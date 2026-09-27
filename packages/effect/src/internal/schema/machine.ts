import type * as Arr from "../../Array.ts"
import type * as Cause from "../../Cause.ts"
import type * as Effect from "../../Effect.ts"
import type * as Exit from "../../Exit.ts"
import type * as SchemaAST from "../../SchemaAST.ts"
import type * as SchemaGetter from "../../SchemaGetter.ts"
import * as SchemaIssue from "../../SchemaIssue.ts"
import type { Parser } from "../../SchemaParser.ts"
import { causeDie, causeEmpty, exitFail, exitFailCause, exitSucceed } from "../core.ts"
import {
  catchCause,
  causeMap,
  effectIsExit,
  exit as exitEffect,
  exitVoid,
  failCauseSync,
  findError,
  flatMap,
  iterateConcurrent,
  mapEager,
  resolveConcurrency,
  suspend
} from "../effect.ts"
import * as InternalRecord from "../record.ts"
import { getSchemaIssue } from "./cause.ts"
import { collectIssues } from "./checks.ts"
import * as InternalParser from "./parser.ts"

type Issue = SchemaIssue.Issue
type Pending = Effect.Effect<unknown, Issue, unknown>
type Issues = Arr.NonEmptyArray<Issue> | undefined

const NONE = Symbol()

const LIMIT = 256

const ISSUE = 1
const CAUSE = 2
const SUSPEND = 3
const DESCEND = 4

const CATCH = 1
const RESTART = 2

const idle: Pending = exitSucceed(undefined)
const unplanned = Symbol()

interface Kind<P> {
  fold(run: Run, node: Node<P>, input: unknown, depth: number): unknown
}

/** @internal */
export class Node<P> {
  readonly kind: Kind<P>
  readonly ast: SchemaAST.AST
  readonly checks: SchemaAST.Checks | undefined
  readonly encodingChecks: SchemaAST.Checks | undefined
  readonly p: P
  constructor(
    kind: Kind<P>,
    ast: SchemaAST.AST,
    checks: SchemaAST.Checks | undefined,
    encodingChecks: SchemaAST.Checks | undefined,
    p: P
  ) {
    this.kind = kind
    this.ast = ast
    this.checks = checks
    this.encodingChecks = encodingChecks
    this.p = p
  }
}

interface FrameKind<P, I, O> {
  resume(run: Run, frame: Frame<P, I, O>, result: unknown): unknown
  copy(out: O): O
}

class Frame<P, I, O> {
  kind: FrameKind<P, I, O>
  node: Node<P>
  input: I
  out: O
  i: number
  j: number
  value: unknown
  acc: Issues
  flags: number
  keys: ReadonlyArray<PropertyKey> | undefined
  lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined
  constructor(
    kind: FrameKind<P, I, O>,
    node: Node<P>,
    input: I,
    out: O,
    i: number,
    j: number,
    value: unknown,
    acc: Issues,
    flags: number
  ) {
    this.kind = kind
    this.node = node
    this.input = input
    this.out = out
    this.i = i
    this.j = j
    this.value = value
    this.acc = acc
    this.flags = flags
    this.keys = undefined
    this.lists = undefined
  }
}

type AnyFrame = Frame<unknown, unknown, unknown>

class Run {
  status: typeof ISSUE | typeof CAUSE | typeof SUSPEND | typeof DESCEND = ISSUE
  issue: Issue | undefined = undefined
  cause: Cause.Cause<Issue> = causeEmpty
  next: Node<unknown> | undefined = undefined
  nextInput: unknown = undefined
  planFailure: unknown = unplanned
  pending: Pending = idle
  result: Exit.Exit<unknown, Issue> | undefined = undefined
  options: SchemaAST.ParseOptions = {}
  readonly stack: Array<AnyFrame> = []
  sp = 0
}

const machine = new Run()

function spill<P, I, O>(
  run: Run,
  kind: FrameKind<P, I, O>,
  node: Node<P>,
  input: I,
  out: O,
  i: number,
  j: number,
  value: unknown,
  acc: Issues,
  flags: number
): Run {
  const frame = run.stack[run.sp]
  if (frame === undefined) {
    run.stack[run.sp] = new Frame(kind, node, input, out, i, j, value, acc, flags)
  } else {
    frame.kind = kind
    frame.node = node
    frame.input = input
    frame.out = out
    frame.i = i
    frame.j = j
    frame.value = value
    frame.acc = acc
    frame.flags = flags
  }
  run.sp++
  return run
}

function pop(run: Run): void {
  const frame = run.stack[--run.sp]
  frame.input = undefined
  frame.out = undefined
  frame.value = undefined
  frame.acc = undefined
  frame.keys = undefined
  frame.lists = undefined
}

function popTo(run: Run, base: number): void {
  while (run.sp > base) pop(run)
}

function reverse(run: Run, from: number, to: number): void {
  for (let a = from, b = to - 1; a < b; a++, b--) {
    const frame = run.stack[a]
    run.stack[a] = run.stack[b]
    run.stack[b] = frame
  }
}

function release<A>(run: Run, settled: A): A {
  run.issue = undefined
  run.cause = causeEmpty
  run.result = undefined
  run.pending = idle
  run.next = undefined
  run.nextInput = undefined
  return settled
}

function failIssue(run: Run, issue: Issue): Run {
  run.status = ISSUE
  run.issue = issue
  return run
}

function failCause(run: Run, cause: Cause.Cause<Issue>): Run {
  run.status = CAUSE
  run.cause = cause
  return run
}

function deliver(run: Run, result: Exit.Exit<unknown, Issue>, input: unknown): unknown {
  if (result._tag === "Failure") return failCause(run, result.cause)
  return result === InternalParser.sameExit ? input : result.value
}

function suspendOn(run: Run, pending: Pending): Run {
  run.pending = pending
  run.status = SUSPEND
  return run
}

function descend(run: Run, node: Node<unknown>, input: unknown): Run {
  run.next = node
  run.nextInput = input
  run.status = DESCEND
  return run
}

function spilled(run: Run, result: unknown): boolean {
  return result === run && run.status >= SUSPEND
}

function schemaIssue(run: Run): Issue | undefined {
  return run.status === ISSUE ? run.issue : getSchemaIssue(run.cause)
}

function failureExit(run: Run): Exit.Exit<never, Issue> {
  return run.status === ISSUE && run.issue !== undefined ? exitFail(run.issue) : exitFailCause(run.cause)
}

function complete(run: Run, node: Node<unknown>, input: unknown, value: unknown): unknown {
  const options = run.options
  if (options.disableChecks) return value
  const encodingChecks = node.encodingChecks
  if (encodingChecks !== undefined && input !== InternalParser.missing && value !== InternalParser.missing) {
    const issues = collectIssues(encodingChecks, input, undefined, node.ast, options)
    if (issues) return failIssue(run, new SchemaIssue.Composite(node.ast, issues, input, options))
  }
  const checks = node.checks
  if (checks !== undefined && value !== InternalParser.missing) {
    const issues = collectIssues(checks, value, undefined, node.ast, options)
    if (issues) return failIssue(run, new SchemaIssue.Composite(node.ast, issues, value, options))
  }
  return value
}

function done(run: Run, node: Node<unknown>, input: unknown): unknown {
  return node.checks === undefined ? input : complete(run, node, input, input)
}

function finish(run: Run, node: Node<unknown>, input: unknown, value: unknown): unknown {
  return node.checks === undefined && node.encodingChecks === undefined ? value : complete(run, node, input, value)
}

function invalidType(run: Run, node: Node<unknown>, input: unknown): Run {
  return failIssue(run, new SchemaIssue.InvalidType(node.ast, input, run.options))
}

function die(run: Run, error: unknown): Run {
  return failCause(run, causeDie(error))
}

function keyIssue(run: Run, node: Node<unknown>, input: unknown, key: PropertyKey): Issue | undefined {
  const options = run.options
  let issue = run.issue
  if (run.status === CAUSE) {
    const cause = run.cause
    if (cause.reasons.length === 0) return undefined
    issue = getSchemaIssue(cause)
    if (issue === undefined) {
      failCause(run, pointCause(cause, node.ast, key, input, options))
      return undefined
    }
  }
  if (issue === undefined) return undefined
  const pointer = new SchemaIssue.Pointer([key], issue)
  if (options.errors === "all") return pointer
  failIssue(run, new SchemaIssue.Composite(node.ast, [pointer], input, options))
  return undefined
}

function pointCause(
  cause: Cause.Cause<Issue>,
  ast: SchemaAST.AST,
  key: PropertyKey,
  input: unknown,
  options: SchemaAST.ParseOptions
): Cause.Cause<Issue> {
  return causeMap(
    cause,
    (issue) => new SchemaIssue.Composite(ast, [new SchemaIssue.Pointer([key], issue)], input, options)
  )
}

function missingKey(
  run: Run,
  node: Node<unknown>,
  input: unknown,
  key: PropertyKey,
  child: SchemaAST.AST
): Issue | undefined {
  const options = run.options
  const issue = new SchemaIssue.Pointer([key], new SchemaIssue.MissingKey(child.context?.annotations))
  if (options.errors === "all") return issue
  failIssue(run, new SchemaIssue.Composite(node.ast, [issue], input, options))
  return undefined
}

function drain(run: Run, base: number, segment: number, result: unknown): unknown {
  while (true) {
    if (result === run && run.status >= SUSPEND) {
      reverse(run, segment, run.sp)
      segment = run.sp
      const next = run.next
      if (run.status === SUSPEND || next === undefined) return run
      const input = run.nextInput
      run.next = undefined
      run.nextInput = undefined
      result = next.kind.fold(run, next, input, 0)
    } else if (run.sp === base) {
      return result
    } else {
      const frame = run.stack[run.sp - 1]
      segment = run.sp - 1
      result = frame.kind.resume(run, frame, result)
    }
  }
}

function drive(
  run: Run,
  base: number,
  segment: number,
  result: unknown,
  previous: SchemaAST.ParseOptions,
  root: boolean
): unknown {
  while (true) {
    try {
      return drain(run, base, segment, result)
    } catch (error) {
      result = unwind(run, base, error, previous, root)
      segment = run.sp
    }
  }
}

function unwind(run: Run, base: number, error: unknown, previous: SchemaAST.ParseOptions, root: boolean): unknown {
  run.result = undefined
  let k = run.sp
  while (k > base) {
    if (run.stack[--k].flags & CATCH) {
      popTo(run, k)
      return die(run, error)
    }
  }
  popTo(run, base)
  if (root) {
    if (error !== run.planFailure) return die(run, error)
    run.planFailure = unplanned
  }
  run.options = previous
  throw error
}

function planned<A>(run: Run, error: unknown): A {
  run.planFailure = error
  throw error
}

function start(
  run: Run,
  node: Node<unknown>,
  input: unknown,
  base: number,
  previous: SchemaAST.ParseOptions,
  root: boolean
): unknown {
  let result: unknown
  try {
    result = node.kind.fold(run, node, input, 0)
  } catch (error) {
    result = unwind(run, base, error, previous, root)
  }
  return result === run ? drive(run, base, base, result, previous, root) : result
}

interface Snapshot {
  readonly frames: ReadonlyArray<AnyFrame>
  readonly restart: number
  readonly options: SchemaAST.ParseOptions
  readonly pending: Pending
}

function snapshot(run: Run, base: number, options: SchemaAST.ParseOptions): Snapshot {
  const frames: Array<AnyFrame> = []
  let restart = -1
  for (let k = base; k < run.sp; k++) {
    const frame = run.stack[k]
    if (restart < 0 && frame.flags & RESTART) restart = k - base
    const copy = new Frame(
      frame.kind,
      frame.node,
      frame.input,
      frame.out,
      frame.i,
      frame.j,
      frame.value,
      frame.acc,
      frame.flags | CATCH
    )
    copy.keys = frame.keys
    copy.lists = frame.lists
    frames.push(copy)
  }
  popTo(run, base)
  return { frames, restart, options, pending: run.pending }
}

function restore(run: Run, frames: ReadonlyArray<AnyFrame>, end: number): void {
  for (let k = 0; k < end; k++) {
    const frame = frames[k]
    spill(
      run,
      frame.kind,
      frame.node,
      frame.input,
      frame.kind.copy(frame.out),
      frame.i,
      frame.j,
      frame.value,
      frame.acc ? [frame.acc[0], ...frame.acc.slice(1)] : undefined,
      frame.flags
    )
    const top = run.stack[run.sp - 1]
    top.keys = frame.keys
    top.lists = frame.lists
  }
}

function settle(run: Run, base: number, result: unknown, options: SchemaAST.ParseOptions): Pending {
  if (result !== run) return exitSucceed(result)
  if (run.status !== SUSPEND) return failureExit(run)
  if (run.sp - base === 1) {
    const frame = run.stack[base]
    if (frame.kind === suspensionFrame && frame.node.checks === undefined && frame.node.encodingChecks === undefined) {
      pop(run)
      return run.pending
    }
  }
  return describe(snapshot(run, base, options))
}

function describe(k: Snapshot): Pending {
  if (k.restart < 0) return flatMap(exitEffect(k.pending), (result) => continueAt(k, result))
  let first = true
  return suspend(() => {
    if (!first) return restart(k)
    first = false
    return flatMap(exitEffect(k.pending), (result) => continueAt(k, result))
  })
}

function continueAt(k: Snapshot, result: Exit.Exit<unknown, Issue>): Pending {
  const run = machine
  const previous = run.options
  run.options = k.options
  const base = run.sp
  restore(run, k.frames, k.frames.length)
  const value = drive(run, base, run.sp, deliver(run, result, undefined), previous, false)
  run.options = previous
  return release(run, settle(run, base, value, k.options))
}

function restart(k: Snapshot): Pending {
  const run = machine
  const previous = run.options
  run.options = k.options
  const base = run.sp
  restore(run, k.frames, k.restart)
  const segment = run.sp
  const frame = k.frames[k.restart]
  const node = frame.node
  let result: unknown
  try {
    result = node.kind.fold(run, node, frame.input, 0)
  } catch (error) {
    result = unwind(run, base, error, previous, false)
  }
  const value = drive(run, base, segment, result, previous, false)
  run.options = previous
  return release(run, settle(run, base, value, k.options))
}

/** @internal */
export function decode(
  node: Node<unknown>,
  input: unknown,
  options: SchemaAST.ParseOptions,
  root: boolean
): Pending {
  const run = machine
  if (root) run.planFailure = unplanned
  const previous = run.options
  run.options = options
  const base = run.sp
  const value = start(run, node, input, base, previous, root)
  run.options = previous
  const result = run.result
  if (result !== undefined) {
    run.result = undefined
    if (node.kind === foreignKind && (value !== run || run.status < SUSPEND)) return release(run, result)
  }
  if (value !== run) {
    return value === input && input !== InternalParser.missing ? InternalParser.sameExit : exitSucceed(value)
  }
  return release(run, settle(run, base, value, options))
}

/** @internal */
export function guard(node: Node<unknown>, input: unknown, options: SchemaAST.ParseOptions): Pending {
  return decode(guardOf(node), input, options, true)
}

const identity = <O>(out: O): O => out

const suspensionFrame: FrameKind<unknown, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    pop(run)
    return result === run ? run : complete(run, node, input, result)
  },
  copy: identity
}

function suspendAt(run: Run, node: Node<unknown>, input: unknown, pending: Pending): Run {
  spill(run, suspensionFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(run, pending)
}

function foldString(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "string" ? done(run, node, input) : invalidType(run, node, input)
}

const stringKind: Kind<undefined> = { fold: foldString }

function foldNumber(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "number" ? done(run, node, input) : invalidType(run, node, input)
}

const numberKind: Kind<undefined> = { fold: foldNumber }

function foldBoolean(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "boolean" ? done(run, node, input) : invalidType(run, node, input)
}

const booleanKind: Kind<undefined> = { fold: foldBoolean }

function foldBigInt(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "bigint" ? done(run, node, input) : invalidType(run, node, input)
}

const bigintKind: Kind<undefined> = { fold: foldBigInt }

function foldSymbol(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "symbol" ? done(run, node, input) : invalidType(run, node, input)
}

const symbolKind: Kind<undefined> = { fold: foldSymbol }

function foldObjectKeyword(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return (typeof input === "object" && input !== null) || typeof input === "function"
    ? done(run, node, input)
    : invalidType(run, node, input)
}

const objectKeywordKind: Kind<undefined> = { fold: foldObjectKeyword }

function foldNotNullish(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return input != null ? done(run, node, input) : invalidType(run, node, input)
}

const notNullishKind: Kind<undefined> = { fold: foldNotNullish }

function foldAny(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return done(run, node, input)
}

const anyKind: Kind<undefined> = { fold: foldAny }

function foldNever(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return invalidType(run, node, input)
}

const neverKind: Kind<undefined> = { fold: foldNever }

function foldConst(run: Run, node: Node<unknown>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  const value = node.p
  if (input !== value) return invalidType(run, node, input)
  return value === 0 ? done(run, node, input) : node.checks === undefined ? value : complete(run, node, input, value)
}

const constKind: Kind<unknown> = { fold: foldConst }

function foldVoid(run: Run, node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return node.checks === undefined ? undefined : complete(run, node, input, undefined)
}

const voidKind: Kind<undefined> = { fold: foldVoid }

function foldEnum(run: Run, node: Node<ReadonlySet<unknown>>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return node.p.has(input) ? done(run, node, input) : invalidType(run, node, input)
}

const enumKind: Kind<ReadonlySet<unknown>> = { fold: foldEnum }

interface ForeignPayload {
  readonly get: () => Parser
  parser: Parser | undefined
}

function foldForeign(run: Run, node: Node<ForeignPayload>, input: unknown, depth: number): unknown {
  const p = node.p
  const parser = p.parser ??= p.get()
  const result = parser(input, run.options)
  if (!effectIsExit(result)) return suspendAt(run, node, input, result)
  if (node.checks === undefined && node.encodingChecks === undefined) {
    if (depth === 0) run.result = result
    return deliver(run, result, input)
  }
  const value = deliver(run, result, input)
  return value === run ? run : complete(run, node, input, value)
}

const foreignKind: Kind<ForeignPayload> = { fold: foldForeign }

/** @internal */
export interface Resolver {
  readonly node: (ast: SchemaAST.AST) => Node<unknown>
  readonly field: (ast: SchemaAST.AST) => Node<unknown>
  readonly make: boolean
}

/** @internal */
export function foreign(ast: SchemaAST.AST, get: () => Parser): Node<unknown> {
  return new Node(foreignKind, ast, undefined, undefined, { get, parser: undefined })
}

/** @internal */
export function checked(ast: SchemaAST.AST, get: () => Parser): Node<unknown> {
  return new Node(foreignKind, ast, ast.checks, "encodingChecks" in ast ? ast.encodingChecks : undefined, {
    get,
    parser: undefined
  })
}

/** @internal */
export function build(ast: SchemaAST.AST, resolver: Resolver): Node<unknown> {
  const encoding = ast.encoding
  return encoding === undefined ? ast.getParser(resolver) : encoding[0].getNode(ast, encoding, resolver)
}

/** @internal */
export function local(ast: SchemaAST.AST, resolver: Resolver): Node<unknown> {
  return ast.getParser(resolver)
}

/** @internal */
export function bare(node: Node<unknown>): Node<unknown> {
  return new Node(node.kind, node.ast, undefined, undefined, node.p)
}

/** @internal */
export function linkOver(
  ast: SchemaAST.AST,
  encoding: SchemaAST.Encoding,
  local: Node<unknown>,
  resolver: Resolver
): Node<unknown> {
  return chain(ast, encoding, local, true, resolver)
}

/** @internal */
export function parser(node: Node<unknown>): Parser {
  return (input, options) => decode(node, input, options, false)
}

function node<P>(kind: Kind<P>, ast: SchemaAST.AST, p: P): Node<unknown> {
  return new Node(kind, ast, ast.checks, undefined, p)
}

/** @internal */
export const stringNode = (ast: SchemaAST.String): Node<unknown> => node(stringKind, ast, undefined)

/** @internal */
export const numberNode = (ast: SchemaAST.Number): Node<unknown> => node(numberKind, ast, undefined)

/** @internal */
export const booleanNode = (ast: SchemaAST.Boolean): Node<unknown> => node(booleanKind, ast, undefined)

/** @internal */
export const bigintNode = (ast: SchemaAST.BigInt): Node<unknown> => node(bigintKind, ast, undefined)

/** @internal */
export const symbolNode = (ast: SchemaAST.Symbol): Node<unknown> => node(symbolKind, ast, undefined)

/** @internal */
export const objectKeywordNode = (ast: SchemaAST.ObjectKeyword): Node<unknown> =>
  node(objectKeywordKind, ast, undefined)

/** @internal */
export const anyNode = (ast: SchemaAST.Any | SchemaAST.Unknown): Node<unknown> => node(anyKind, ast, undefined)

/** @internal */
export const neverNode = (ast: SchemaAST.Never): Node<unknown> => node(neverKind, ast, undefined)

/** @internal */
export const constNode = (ast: SchemaAST.AST, value: unknown): Node<unknown> => node(constKind, ast, value)

/** @internal */
export const voidNode = (ast: SchemaAST.Void): Node<unknown> => node(voidKind, ast, undefined)

/** @internal */
export const enumNode = (ast: SchemaAST.Enum): Node<unknown> =>
  node(enumKind, ast, new Set<unknown>(ast.enums.map(([, v]) => v)))

/** @internal */
export function objectsNode(ast: SchemaAST.Objects, resolver: Resolver): Node<unknown> {
  if (ast.propertySignatures.length === 0) return node(notNullishKind, ast, undefined)
  return new Node(structKind, ast, ast.checks, ast.encodingChecks, structPayload(ast, resolver))
}

function structPayload(ast: SchemaAST.Objects, resolver: Resolver): StructPayload {
  return {
    objects: ast,
    resolver,
    keys: ast.propertySignatures.map((ps) => ps.name),
    expected: new Set(ast.propertySignatures.map((ps) => typeof ps.name === "number" ? String(ps.name) : ps.name)),
    children: undefined
  }
}

/** @internal */
export const arraysNode = (ast: SchemaAST.Arrays, resolver: Resolver): Node<unknown> =>
  new Node(arrayKind, ast, ast.checks, ast.encodingChecks, {
    arrays: ast,
    resolver,
    elements: undefined,
    rest: undefined
  })

/** @internal */
export const unionNode = (
  ast: SchemaAST.Union,
  resolver: Resolver,
  candidates: (types: ReadonlyArray<SchemaAST.AST>) => SchemaAST.CandidateIndex
): Node<unknown> =>
  new Node(unionKind, ast, ast.checks, ast.encodingChecks, {
    union: ast,
    resolver,
    candidates,
    members: [],
    index: undefined,
    oneOf: ast.options?.mode === "oneOf",
    make: resolver.make
  })

/** @internal */
export const suspendNode = (ast: SchemaAST.Suspend, resolver: Resolver): Node<unknown> =>
  node(suspendKind, ast, { thunk: ast.thunk, resolver, target: undefined })

/** @internal */
export function declarationNode(
  ast: SchemaAST.Declaration,
  resolver: Resolver,
  descriptorOf: (ast: SchemaAST.AST) => SchemaAST.ConstructorDescriptor | undefined
): Node<unknown> {
  for (const parameter of ast.typeParameters) resolver.node(parameter)
  const descriptor = resolver.make ? descriptorOf(ast) : undefined
  if (descriptor !== undefined) {
    return new Node(constructorKind, ast, ast.checks, ast.encodingChecks, { descriptor, resolver, source: undefined })
  }
  return new Node(declarationKind, ast, ast.checks, ast.encodingChecks, { declaration: ast, run: undefined })
}

/** @internal */
export const templateNode = (ast: SchemaAST.TemplateLiteral, inner: Node<unknown>): Node<unknown> =>
  node(templateKind, ast, inner)

/** @internal */
export function linkNode(ast: SchemaAST.AST, encoding: SchemaAST.Encoding, resolver: Resolver): Node<unknown> {
  return chain(ast, encoding, ast.getParser(resolver), true, resolver)
}

function chain(
  ast: SchemaAST.AST,
  links: ReadonlyArray<SchemaAST.Link>,
  local: Node<unknown> | undefined,
  wrap: boolean,
  resolver: Resolver
): Node<unknown> {
  const steps: Array<Getter> = []
  for (let i = 0; i < links.length; i++) {
    const transformation = links[i].transformation
    if (transformation._tag === "Middleware") return transformation.getNode(ast, links, i, local, wrap, resolver)
    steps.push(transformation.decode)
  }
  return new Node(linkKind, ast, undefined, undefined, { steps, links, resolver, parsers: undefined, local, wrap })
}

interface StructPayload {
  readonly objects: SchemaAST.Objects
  readonly resolver: Resolver
  readonly keys: ReadonlyArray<PropertyKey>
  readonly expected: ReadonlySet<PropertyKey>
  children: ReadonlyArray<Node<unknown>> | undefined
}

function properties(p: StructPayload): ReadonlyArray<Node<unknown>> {
  return p.children ?? resolveProperties(p)
}

function resolveProperties(p: StructPayload): ReadonlyArray<Node<unknown>> {
  const resolver = p.resolver
  return p.children = p.objects.propertySignatures.map((ps) => resolver.field(ps.type))
}

type Struct = Record<PropertyKey, unknown>

const isStruct = (input: unknown): input is Struct =>
  typeof input === "object" && input !== null && !Array.isArray(input)

function copyStruct(out: Struct): Struct {
  const copy: Struct = {}
  for (const key of Reflect.ownKeys(out)) InternalRecord.assignProperty(copy, key, out[key])
  return copy
}

function propertyValue(input: Struct, key: PropertyKey): unknown {
  return (key === "__proto__" ? Object.hasOwn(input, key) : key in input) ? input[key] : InternalParser.missing
}

function foldStruct(run: Run, node: Node<StructPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  const options = run.options
  if (options.errors !== "all" && options.onExcessProperty === undefined && sequential(options)) {
    if (!isStruct(input)) return invalidType(run, node, input)
    properties(node.p)
    return structLoop(run, node, input, {}, 0, undefined, NONE, depth, CATCH)
  }
  return structAccumulate(run, node, input, depth)
}

function guardStruct(run: Run, node: Node<StructPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  const options = run.options
  if (options.errors !== "all" && options.onExcessProperty === undefined && sequential(options)) {
    if (!isStruct(input)) return invalidType(run, node, input)
    properties(node.p)
    return structGuardLoop(run, node, input, 0, undefined, NONE, depth, CATCH)
  }
  let acc: Issues
  try {
    if (!isStruct(input)) return invalidType(run, node, input)
    properties(node.p)
    if (options.onExcessProperty === "error") {
      const expected = node.p.expected
      const keys = Reflect.ownKeys(input)
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i]
        if (!expected.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)) {
          const issue = new SchemaIssue.Pointer([key], new SchemaIssue.UnexpectedKey(node.ast, input[key], options))
          if (options.errors !== "all") {
            return failIssue(run, new SchemaIssue.Composite(node.ast, [issue], input, options))
          }
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
    }
  } catch (error) {
    return die(run, error)
  }
  if (!sequential(options)) return forkStruct(run, node, input, acc)
  return structGuardLoop(run, node, input, 0, acc, NONE, depth, CATCH | RESTART)
}

function structAccumulate(run: Run, node: Node<StructPayload>, input: unknown, depth: number): unknown {
  let acc: Issues
  try {
    if (!isStruct(input)) return invalidType(run, node, input)
    properties(node.p)
    const options = run.options
    if (options.onExcessProperty === "error") {
      const expected = node.p.expected
      const keys = Reflect.ownKeys(input)
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i]
        if (!expected.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)) {
          const issue = new SchemaIssue.Pointer([key], new SchemaIssue.UnexpectedKey(node.ast, input[key], options))
          if (options.errors !== "all") {
            return failIssue(run, new SchemaIssue.Composite(node.ast, [issue], input, options))
          }
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
    }
  } catch (error) {
    return die(run, error)
  }
  if (!sequential(run.options)) return forkStruct(run, node, input, acc)
  return structLoop(run, node, input, {}, 0, acc, NONE, depth, CATCH | RESTART)
}

function structLoop(
  run: Run,
  node: Node<StructPayload>,
  input: Struct,
  out: Struct,
  i: number,
  acc: Issues,
  result: unknown,
  depth: number,
  flags: number
): unknown {
  const p = node.p
  const keys = p.keys
  const children = properties(p)
  try {
    for (; i < keys.length; i++) {
      const key = keys[i]
      if (result === NONE) {
        const child = children[i]
        result = child.kind.fold(run, child, propertyValue(input, key), depth + 1)
      }
      if (result === run) {
        if (run.status >= SUSPEND) return spill(run, structFrame, node, input, out, i, 0, undefined, acc, flags)
        const issue = keyIssue(run, node, input, key)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        InternalRecord.assignProperty(out, key, result)
      } else if (!children[i].ast.context?.isOptional) {
        const issue = missingKey(run, node, input, key, children[i].ast)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      }
      result = NONE
    }
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, input, run.options))
  return finish(run, node, input, out)
}

function structGuardLoop(
  run: Run,
  node: Node<StructPayload>,
  input: Struct,
  i: number,
  acc: Issues,
  result: unknown,
  depth: number,
  flags: number
): unknown {
  const p = node.p
  const keys = p.keys
  const children = properties(p)
  try {
    for (; i < keys.length; i++) {
      const key = keys[i]
      if (result === NONE) {
        const child = children[i]
        result = child.kind.fold(run, child, propertyValue(input, key), depth + 1)
      }
      if (result === run) {
        if (run.status >= SUSPEND) {
          return spill(run, structGuardFrame, node, input, undefined, i, 0, undefined, acc, flags)
        }
        const issue = keyIssue(run, node, input, key)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result === InternalParser.missing && !children[i].ast.context?.isOptional) {
        const issue = missingKey(run, node, input, key, children[i].ast)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      }
      result = NONE
    }
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, input, run.options))
  return input
}

const structKind: Kind<StructPayload> = { fold: foldStruct }

/** @internal */
export function structResumer(
  ast: SchemaAST.Objects,
  resolver: Resolver
): (input: Struct, out: Struct, from: number, options: SchemaAST.ParseOptions) => Pending {
  const node: Node<StructPayload> = new Node(structKind, ast, undefined, undefined, structPayload(ast, resolver))
  return (input, out, from, options) => {
    const run = machine
    const previous = run.options
    run.options = options
    const base = run.sp
    let result: unknown
    try {
      result = structLoop(run, node, input, out, from, undefined, NONE, 0, CATCH)
    } catch (error) {
      result = unwind(run, base, error, previous, false)
    }
    if (result === run) result = drive(run, base, base, result, previous, false)
    run.options = previous
    return release(run, settle(run, base, result, options))
  }
}

const structFrame: FrameKind<StructPayload, Struct, Struct> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const acc = frame.acc
    const flags = frame.flags
    pop(run)
    return structLoop(run, node, input, out, i, acc, result, 0, flags)
  },
  copy: copyStruct
}

const structGuardFrame: FrameKind<StructPayload, Struct, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    const acc = frame.acc
    const flags = frame.flags
    pop(run)
    return structGuardLoop(run, node, input, i, acc, result, 0, flags)
  },
  copy: identity
}

/** @internal */
export interface RecordSupport {
  readonly key: (parameter: SchemaAST.AST) => SchemaAST.AST
  readonly keys: (
    input: { readonly [x: PropertyKey]: unknown },
    parameter: SchemaAST.IndexSignature["parameter"],
    options: SchemaAST.ParseOptions
  ) => ReadonlyArray<PropertyKey>
  readonly string: SchemaAST.AST
}

interface IndexPlan {
  readonly parameter: SchemaAST.IndexSignature["parameter"]
  readonly key: Node<unknown> | undefined
  readonly value: Node<unknown>
}

interface RecordPayload {
  readonly objects: SchemaAST.Objects
  readonly resolver: Resolver
  readonly support: RecordSupport
  readonly keys: ReadonlyArray<PropertyKey>
  readonly expected: ReadonlySet<PropertyKey>
  children: ReadonlyArray<Node<unknown>> | undefined
  indexes: ReadonlyArray<IndexPlan> | undefined
}

/** @internal */
export function recordNode(ast: SchemaAST.Objects, resolver: Resolver, support: RecordSupport): Node<unknown> {
  return new Node(recordKind, ast, ast.checks, ast.encodingChecks, {
    objects: ast,
    resolver,
    support,
    keys: ast.propertySignatures.map((ps) => ps.name),
    expected: new Set(ast.propertySignatures.map((ps) => typeof ps.name === "number" ? String(ps.name) : ps.name)),
    children: undefined,
    indexes: undefined
  })
}

function resolveRecord(p: RecordPayload): ReadonlyArray<IndexPlan> {
  if (p.indexes !== undefined) return p.indexes
  const resolver = p.resolver
  p.children = p.objects.propertySignatures.map((ps) => resolver.field(ps.type))
  return p.indexes = p.objects.indexSignatures.map((is) => ({
    parameter: is.parameter,
    key: is.parameter === p.support.string ? undefined : resolver.node(p.support.key(is.parameter)),
    value: resolver.field(is.type)
  }))
}

function foldRecord(run: Run, node: Node<RecordPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  const p = node.p
  let acc: Issues
  let lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined
  try {
    if (!isStruct(input)) return invalidType(run, node, input)
    const indexes = resolveRecord(p)
    const options = run.options
    if (options.onExcessProperty === "error") {
      lists = indexes.map((index) => p.support.keys(input, index.parameter, options))
      const covered = new Set(p.expected)
      for (const keys of lists) {
        for (const key of keys) covered.add(key)
      }
      const keys = Reflect.ownKeys(input)
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i]
        if (!covered.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)) {
          const issue = new SchemaIssue.Pointer([key], new SchemaIssue.UnexpectedKey(node.ast, input[key], options))
          if (options.errors !== "all") {
            return failIssue(run, new SchemaIssue.Composite(node.ast, [issue], input, options))
          }
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
    }
  } catch (error) {
    return die(run, error)
  }
  if (!sequential(run.options)) return forkRecord(run, node, input, lists, acc)
  return recordLoop(run, node, input, {}, 0, 0, undefined, lists, NONE, acc, NONE, depth)
}

function recordLoop(
  run: Run,
  node: Node<RecordPayload>,
  input: Struct,
  out: Struct,
  i: number,
  j: number,
  keys: ReadonlyArray<PropertyKey> | undefined,
  lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined,
  k2: unknown,
  acc: Issues,
  result: unknown,
  depth: number
): unknown {
  const p = node.p
  const names = p.keys
  const children = p.children ?? []
  const indexes = p.indexes ?? []
  const n = names.length
  try {
    for (; i < n; i++) {
      const key = names[i]
      if (result === NONE) {
        const child = children[i]
        result = child.kind.fold(run, child, propertyValue(input, key), depth + 1)
      }
      if (result === run) {
        if (run.status >= SUSPEND) return spillRecord(run, recordFrame, node, input, out, i, j, keys, lists, k2, acc)
        const issue = keyIssue(run, node, input, key)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        InternalRecord.assignProperty(out, key, result)
      } else if (!children[i].ast.context?.isOptional) {
        const issue = missingKey(run, node, input, key, children[i].ast)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      }
      result = NONE
    }
    for (; i - n < indexes.length; i++, j = 0, keys = undefined) {
      const index = indexes[i - n]
      if (keys === undefined) {
        keys = lists !== undefined
          ? lists[i - n]
          : index.key === undefined
          ? Object.keys(input)
          : p.support.keys(input, index.parameter, run.options)
      }
      for (; j < keys.length; j++, k2 = NONE) {
        const key = keys[j]
        if (k2 === NONE) {
          const parser = index.key
          if (parser === undefined) {
            k2 = key
          } else {
            if (result === NONE) result = parser.kind.fold(run, parser, key, depth + 1)
            if (result === run) {
              if (run.status >= SUSPEND) {
                return spillRecord(run, recordKeyFrame, node, input, out, i, j, keys, lists, k2, acc)
              }
              const issue = keyIssue(run, node, input, key)
              if (issue === undefined) return run
              if (acc) acc.push(issue)
              else acc = [issue]
              result = NONE
              continue
            }
            k2 = result
            result = NONE
          }
        }
        if (result === NONE) {
          const value = index.value
          result = value.kind.fold(run, value, input[key], depth + 1)
        }
        if (result === run) {
          if (run.status >= SUSPEND) return spillRecord(run, recordFrame, node, input, out, i, j, keys, lists, k2, acc)
          const issue = keyIssue(run, node, input, key)
          if (issue === undefined) return run
          if (acc) acc.push(issue)
          else acc = [issue]
        } else if (k2 !== InternalParser.missing && result !== InternalParser.missing) {
          const name = propertyKey(k2)
          if (!(n > 0 && (p.expected.has(key) || p.expected.has(typeof name === "number" ? String(name) : name)))) {
            InternalRecord.assignProperty(out, name, result)
          }
        }
        result = NONE
      }
    }
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, input, run.options))
  return finish(run, node, input, out)
}

function propertyKey(key: unknown): PropertyKey {
  return typeof key === "string" || typeof key === "number" || typeof key === "symbol" ? key : String(key)
}

function spillRecord(
  run: Run,
  kind: FrameKind<RecordPayload, Struct, Struct>,
  node: Node<RecordPayload>,
  input: Struct,
  out: Struct,
  i: number,
  j: number,
  keys: ReadonlyArray<PropertyKey> | undefined,
  lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined,
  k2: unknown,
  acc: Issues
): Run {
  spill(run, kind, node, input, out, i, j, k2, acc, CATCH | RESTART)
  const top = run.stack[run.sp - 1]
  top.keys = keys
  top.lists = lists
  return run
}

const recordKind: Kind<RecordPayload> = { fold: foldRecord }

function sequential(options: SchemaAST.ParseOptions): boolean {
  return options.concurrency === undefined || resolveConcurrency(options.concurrency) === 1
}

/** @internal */
export interface Accumulator<I> {
  readonly ast: SchemaAST.AST
  readonly input: I
  readonly options: SchemaAST.ParseOptions
  issues: Issues
}

interface Fork extends Accumulator<Struct> {
  readonly out: Struct
  readonly keys: ReadonlyArray<PropertyKey>
  readonly children: ReadonlyArray<Node<unknown>>
  readonly lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined
}

interface RecordFork extends Fork {
  readonly node: Node<RecordPayload>
}

interface ArrayFork extends Accumulator<Elements> {
  readonly node: Node<ArrayPayload>
  readonly out: Array<unknown>
  readonly len: number
}

type Item = Effect.Effect<void, Issue, unknown>

type Terminal = Exit.Exit<void, Issue> | undefined

function stepFailure<I>(s: Accumulator<I>, key: PropertyKey, exit: Exit.Failure<unknown, Issue>): Terminal {
  const cause = exit.cause
  if (cause.reasons.length === 0) return exitFailCause(cause)
  const issue = getSchemaIssue(cause)
  if (issue === undefined) return exitFailCause(pointCause(cause, s.ast, key, s.input, s.options))
  const pointer = new SchemaIssue.Pointer([key], issue)
  if (s.options.errors === "all") {
    if (s.issues) s.issues.push(pointer)
    else s.issues = [pointer]
    return undefined
  }
  return exitFail(new SchemaIssue.Composite(s.ast, [pointer], s.input, s.options))
}

function stepMissing<I>(s: Accumulator<I>, key: PropertyKey, child: SchemaAST.AST): Terminal {
  if (child.context?.isOptional) return undefined
  const issue = new SchemaIssue.Pointer([key], new SchemaIssue.MissingKey(child.context?.annotations))
  if (s.options.errors === "all") {
    if (s.issues) s.issues.push(issue)
    else s.issues = [issue]
    return undefined
  }
  return exitFail(new SchemaIssue.Composite(s.ast, [issue], s.input, s.options))
}

/** @internal */
export function stepKey(
  s: Accumulator<Struct>,
  out: Struct,
  key: PropertyKey,
  child: SchemaAST.AST,
  exit: Exit.Exit<unknown, Issue>
): Terminal {
  if (exit._tag === "Failure") return stepFailure(s, key, exit)
  if (exit === InternalParser.sameExit) return undefined
  const value = exit.value
  if (value !== InternalParser.missing) {
    InternalRecord.assignProperty(out, key, value)
    return undefined
  }
  delete out[key]
  return stepMissing(s, key, child)
}

/** @internal */
export function stepIndex(
  s: Accumulator<Elements>,
  out: Array<unknown>,
  i: number,
  input: unknown,
  child: SchemaAST.AST,
  exit: Exit.Exit<unknown, Issue>
): Terminal {
  if (exit._tag === "Failure") return stepFailure(s, i, exit)
  const value = exit === InternalParser.sameExit ? input : exit.value
  if (value !== InternalParser.missing) {
    out[i] = value
    return undefined
  }
  return stepMissing(s, i, child)
}

function item(result: Pending, absorb: (exit: Exit.Exit<unknown, Issue>) => Item): Item {
  return effectIsExit(result) ? absorb(result) : flatMap(exitEffect(result), absorb)
}

function failed(_: unknown, __: unknown, exit: Exit.Exit<void, Issue>): Exit.Exit<void, Issue> | undefined {
  return exit._tag === "Failure" ? exit : undefined
}

const forkProperties = iterateConcurrent<Fork, PropertyKey>()({
  onItem(s, key, i) {
    const child = s.children[i]
    if (!(key === "__proto__" ? Object.hasOwn(s.input, key) : key in s.input)) {
      return item(decode(child, InternalParser.missing, s.options, false), (exit) => absorbProperty(s, i, key, exit))
    }
    const value = s.input[key]
    InternalRecord.assignProperty(s.out, key, value)
    return item(decode(child, value, s.options, false), (exit) => absorbProperty(s, i, key, exit))
  },
  step: failed
})

function absorbProperty(s: Fork, i: number, key: PropertyKey, exit: Exit.Exit<unknown, Issue>): Item {
  return stepKey(s, s.out, key, s.children[i].ast, exit) ?? exitVoid
}

function join<P, S extends Accumulator<unknown>>(
  run: Run,
  frame: FrameKind<P, unknown, S>,
  node: Node<P>,
  s: S,
  eff: Item | undefined,
  done: (run: Run, node: Node<P>, s: S) => unknown
): unknown {
  if (eff === undefined) return done(run, node, s)
  if (effectIsExit(eff)) return eff._tag === "Failure" ? failCause(run, eff.cause) : done(run, node, s)
  spill(run, frame, node, s.input, s, 0, 0, undefined, undefined, CATCH | RESTART)
  return suspendOn(run, eff)
}

function joined<P, S extends Accumulator<unknown>>(
  done: (run: Run, node: Node<P>, s: S) => unknown
): FrameKind<P, unknown, S> {
  return {
    resume(run, frame, result) {
      const node = frame.node
      const s = frame.out
      pop(run)
      return result === run ? run : done(run, node, s)
    },
    copy: identity
  }
}

function forkDone(run: Run, node: Node<unknown>, s: Fork): unknown {
  if (s.issues) return failIssue(run, new SchemaIssue.Composite(node.ast, s.issues, s.input, s.options))
  return finish(run, node, s.input, s.out)
}

const forkFrame = joined<unknown, Fork>(forkDone)

function forkStruct(run: Run, node: Node<StructPayload>, input: Struct, acc: Issues): unknown {
  const options = run.options
  const p = node.p
  const s: Fork = {
    ast: node.ast,
    input,
    options,
    issues: acc,
    out: {},
    keys: p.keys,
    children: properties(p),
    lists: undefined
  }
  let eff: Item | undefined
  try {
    eff = forkProperties(s, p.keys, { concurrency: resolveConcurrency(options.concurrency) })
  } catch (error) {
    return die(run, error)
  }
  return join(run, forkFrame, node, s, eff, forkDone)
}

function forkRecord(
  run: Run,
  node: Node<RecordPayload>,
  input: Struct,
  lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined,
  acc: Issues
): unknown {
  const options = run.options
  const p = node.p
  const s: RecordFork = {
    ast: node.ast,
    node,
    input,
    options,
    issues: acc,
    out: {},
    keys: p.keys,
    children: p.children ?? [],
    lists
  }
  let eff: Item | undefined
  try {
    if (p.keys.length > 0) eff = forkProperties(s, p.keys, { concurrency: resolveConcurrency(options.concurrency) })
  } catch (error) {
    return die(run, error)
  }
  return join(run, forkRecordFrame, node, s, eff, forkIndexes)
}

function forkIndexes(run: Run, node: Node<RecordPayload>, s: RecordFork): unknown {
  const p = node.p
  const indexes = p.indexes ?? []
  const pairs: Array<readonly [PropertyKey, IndexPlan]> = []
  let eff: Item | undefined
  try {
    for (let i = 0; i < indexes.length; i++) {
      const index = indexes[i]
      const keys = s.lists?.[i] ?? (index.key === undefined
        ? Object.keys(s.input)
        : p.support.keys(s.input, index.parameter, s.options))
      for (let j = 0; j < keys.length; j++) pairs.push([keys[j], index])
    }
    eff = forkEntries(s, pairs, { concurrency: resolveConcurrency(s.options.concurrency) })
  } catch (error) {
    return die(run, error)
  }
  return join(run, forkFrame, node, s, eff, forkDone)
}

const forkRecordFrame = joined<RecordPayload, RecordFork>(forkIndexes)

const forkEntries = iterateConcurrent<RecordFork, readonly [PropertyKey, IndexPlan]>()({
  onItem(s, [key, index]) {
    const parser = index.key
    if (parser === undefined) return forkValue(s, key, key, index)
    return item(decode(parser, key, s.options, false), (exit) => {
      if (exit._tag === "Failure") return stepFailure(s, key, exit) ?? exitVoid
      return forkValue(s, key, exit === InternalParser.sameExit ? key : exit.value, index)
    })
  },
  step: failed
})

function forkValue(s: RecordFork, key: PropertyKey, k2: unknown, index: IndexPlan): Item {
  const input = s.input[key]
  return item(decode(index.value, input, s.options, false), (exit) => {
    if (exit._tag === "Failure") return stepFailure(s, key, exit) ?? exitVoid
    const value = exit === InternalParser.sameExit ? input : exit.value
    if (k2 !== InternalParser.missing && value !== InternalParser.missing) {
      const name = propertyKey(k2)
      const expected = s.node.p.expected
      if (!(s.keys.length > 0 && (expected.has(key) || expected.has(typeof name === "number" ? String(name) : name)))) {
        InternalRecord.assignProperty(s.out, name, value)
      }
    }
    return exitVoid
  })
}

const forkElements = iterateConcurrent<ArrayFork, unknown>()({
  onItem(s, value, i) {
    const child = elementAt(s.node.p, i, s.len)
    return item(
      decode(child, i < s.len ? value : InternalParser.missing, s.options, false),
      (exit) => absorbElement(s, i, value, exit)
    )
  },
  step: failed
})

function absorbElement(s: ArrayFork, i: number, input: unknown, exit: Exit.Exit<unknown, Issue>): Item {
  return stepIndex(s, s.out, i, input, elementAt(s.node.p, i, s.len).ast, exit) ?? exitVoid
}

function forkArray(run: Run, node: Node<ArrayPayload>, input: Elements, len: number): unknown {
  const options = run.options
  const s: ArrayFork = { ast: node.ast, node, input, options, issues: undefined, out: new Array(len), len }
  let eff: Item | undefined
  try {
    eff = forkElements(s, input, {
      concurrency: resolveConcurrency(options.concurrency),
      end: arrayEnd(node.p.arrays, len)
    })
  } catch (error) {
    return die(run, error)
  }
  return join(run, forkArrayFrame, node, s, eff, forkArrayDone)
}

function forkArrayDone(run: Run, node: Node<ArrayPayload>, s: ArrayFork): unknown {
  let acc: Issues
  try {
    const excess = excessElements(run, node, s.input, s.len, s.issues)
    if (excess === false) return run
    acc = excess
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, s.input, s.options))
  return finish(run, node, s.input, s.out)
}

const forkArrayFrame = joined<ArrayPayload, ArrayFork>(forkArrayDone)

const recordFrame: FrameKind<RecordPayload, Struct, Struct> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const j = frame.j
    const keys = frame.keys
    const lists = frame.lists
    const k2 = frame.value
    const acc = frame.acc
    pop(run)
    return recordLoop(run, node, input, out, i, j, keys, lists, k2, acc, result, 0)
  },
  copy: copyStruct
}

const recordKeyFrame: FrameKind<RecordPayload, Struct, Struct> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const j = frame.j
    const keys = frame.keys
    const lists = frame.lists
    const acc = frame.acc
    pop(run)
    return recordLoop(run, node, input, out, i, j, keys, lists, NONE, acc, result, 0)
  },
  copy: copyStruct
}

interface ArrayPayload {
  readonly arrays: SchemaAST.Arrays
  readonly resolver: Resolver
  elements: ReadonlyArray<Node<unknown>> | undefined
  rest: ReadonlyArray<Node<unknown>> | undefined
}

type Elements = ReadonlyArray<unknown>

function resolveElements(p: ArrayPayload): void {
  if (p.elements === undefined) {
    const resolver = p.resolver
    p.elements = p.arrays.elements.map((ast) => resolver.field(ast))
    p.rest = p.arrays.rest.map((ast) => resolver.field(ast))
  }
}

function elementAt(p: ArrayPayload, i: number, len: number): Node<unknown> {
  const elements = p.elements ?? []
  const rest = p.rest ?? []
  const elementLen = elements.length
  if (i < elementLen) return elements[i]
  const tailThreshold = Math.max(elementLen, len - Math.max(0, rest.length - 1))
  return i >= tailThreshold ? rest[i - tailThreshold + 1] : rest[0]
}

function arrayEnd(arrays: SchemaAST.Arrays, len: number): number {
  const elementLen = arrays.elements.length
  const restLen = arrays.rest.length
  return restLen === 0 ? elementLen : Math.max(len, elementLen + Math.max(0, restLen - 1))
}

function foldArray(run: Run, node: Node<ArrayPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  let len: number
  try {
    if (!Array.isArray(input)) return invalidType(run, node, input)
    resolveElements(node.p)
    len = input.length
  } catch (error) {
    return die(run, error)
  }
  if (!sequential(run.options)) return forkArray(run, node, input, len)
  return arrayLoop(run, node, input, new Array(len), 0, len, undefined, NONE, depth, CATCH | RESTART)
}

function guardArray(run: Run, node: Node<ArrayPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  let len: number
  try {
    if (!Array.isArray(input)) return invalidType(run, node, input)
    resolveElements(node.p)
    len = input.length
  } catch (error) {
    return die(run, error)
  }
  if (!sequential(run.options)) return forkArray(run, node, input, len)
  return arrayGuardLoop(run, node, input, 0, len, undefined, NONE, depth, CATCH | RESTART)
}

function arrayLoop(
  run: Run,
  node: Node<ArrayPayload>,
  input: Elements,
  out: Array<unknown>,
  i: number,
  len: number,
  acc: Issues,
  result: unknown,
  depth: number,
  flags: number
): unknown {
  const p = node.p
  const end = arrayEnd(p.arrays, len)
  try {
    for (; i < end; i++) {
      if (result === NONE) {
        const item = input[i]
        const child = elementAt(p, i, len)
        result = child.kind.fold(run, child, i < len ? item : InternalParser.missing, depth + 1)
      }
      if (result === run) {
        if (run.status >= SUSPEND) return spill(run, arrayFrame, node, input, out, i, len, undefined, acc, flags)
        const issue = keyIssue(run, node, input, i)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        out[i] = result
      } else {
        const child = elementAt(p, i, len).ast
        if (!child.context?.isOptional) {
          const issue = missingKey(run, node, input, i, child)
          if (issue === undefined) return run
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
      result = NONE
    }
    const excess = excessElements(run, node, input, len, acc)
    if (excess === false) return run
    acc = excess
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, input, run.options))
  return finish(run, node, input, out)
}

function arrayGuardLoop(
  run: Run,
  node: Node<ArrayPayload>,
  input: Elements,
  i: number,
  len: number,
  acc: Issues,
  result: unknown,
  depth: number,
  flags: number
): unknown {
  const p = node.p
  const end = arrayEnd(p.arrays, len)
  try {
    for (; i < end; i++) {
      if (result === NONE) {
        const item = input[i]
        const child = elementAt(p, i, len)
        result = child.kind.fold(run, child, i < len ? item : InternalParser.missing, depth + 1)
      }
      if (result === run) {
        if (run.status >= SUSPEND) {
          return spill(run, arrayGuardFrame, node, input, undefined, i, len, undefined, acc, flags)
        }
        const issue = keyIssue(run, node, input, i)
        if (issue === undefined) return run
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result === InternalParser.missing) {
        const child = elementAt(p, i, len).ast
        if (!child.context?.isOptional) {
          const issue = missingKey(run, node, input, i, child)
          if (issue === undefined) return run
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
      result = NONE
    }
    const excess = excessElements(run, node, input, len, acc)
    if (excess === false) return run
    acc = excess
  } catch (error) {
    return die(run, error)
  }
  if (acc) return failIssue(run, new SchemaIssue.Composite(node.ast, acc, input, run.options))
  return input
}

function excessElements(
  run: Run,
  node: Node<ArrayPayload>,
  input: Elements,
  len: number,
  acc: Issues
): Issues | false {
  const arrays = node.p.arrays
  const elementLen = arrays.elements.length
  if (arrays.rest.length === 0 && len > elementLen) {
    const options = run.options
    for (let i = elementLen; i < len; i++) {
      const issue = new SchemaIssue.Pointer([i], new SchemaIssue.UnexpectedKey(node.ast, input[i], options))
      if (options.errors !== "all") {
        failIssue(run, new SchemaIssue.Composite(node.ast, [issue], input, options))
        return false
      }
      if (acc) acc.push(issue)
      else acc = [issue]
    }
  }
  return acc
}

const arrayKind: Kind<ArrayPayload> = { fold: foldArray }

const arrayFrame: FrameKind<ArrayPayload, Elements, Array<unknown>> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const len = frame.j
    const acc = frame.acc
    const flags = frame.flags
    pop(run)
    return arrayLoop(run, node, input, out, i, len, acc, result, 0, flags)
  },
  copy: (out) => out.slice()
}

const arrayGuardFrame: FrameKind<ArrayPayload, Elements, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    const len = frame.j
    const acc = frame.acc
    const flags = frame.flags
    pop(run)
    return arrayGuardLoop(run, node, input, i, len, acc, result, 0, flags)
  },
  copy: identity
}

interface UnionPayload {
  readonly union: SchemaAST.Union
  readonly resolver: Resolver
  readonly candidates: (types: ReadonlyArray<SchemaAST.AST>) => SchemaAST.CandidateIndex
  readonly members: Array<Node<unknown>>
  index: SchemaAST.CandidateIndex | undefined
  readonly oneOf: boolean
  readonly make: boolean
}

function member(p: UnionPayload, i: number): Node<unknown> {
  return p.members[i] ??= p.resolver.node(p.union.types[i])
}

function foldUnion(run: Run, node: Node<UnionPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  const p = node.p
  const candidates = (p.index ??= p.candidates(p.union.types))(input, p.make)
  if (candidates.length === 0) return failIssue(run, new SchemaIssue.AnyOf(p.union, [], input, run.options))
  if (candidates.length === 1) {
    const child = member(p, candidates[0])
    return unionSingle(run, node, input, child.kind.fold(run, child, input, depth + 1))
  }
  return unionLoop(run, node, input, candidates, 0, -1, undefined, undefined, NONE, depth)
}

function unionSingle(run: Run, node: Node<UnionPayload>, input: unknown, result: unknown): unknown {
  if (result !== run) return finish(run, node, input, result)
  if (run.status >= SUSPEND) return spill(run, unionSingleFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  const issue = schemaIssue(run)
  if (issue === undefined) return run
  return failIssue(run, new SchemaIssue.AnyOf(node.p.union, [issue], input, run.options))
}

function unionLoop(
  run: Run,
  node: Node<UnionPayload>,
  input: unknown,
  candidates: ReadonlyArray<number>,
  i: number,
  found: number,
  value: unknown,
  acc: Issues,
  result: unknown,
  depth: number
): unknown {
  const p = node.p
  for (; i < candidates.length; i++) {
    if (result === NONE) {
      const child = member(p, candidates[i])
      result = child.kind.fold(run, child, input, depth + 1)
    }
    if (result === run) {
      if (run.status >= SUSPEND) return spill(run, unionFrame, node, input, candidates, i, found, value, acc, 0)
      const issue = schemaIssue(run)
      if (issue === undefined) return run
      if (acc) acc.push(issue)
      else acc = [issue]
    } else {
      if (found >= 0) {
        const types = p.union.types
        return failIssue(run, new SchemaIssue.OneOf(p.union, [types[found], types[candidates[i]]], input, run.options))
      }
      if (!p.oneOf) return finish(run, node, input, result)
      value = result
      found = candidates[i]
    }
    result = NONE
  }
  if (found >= 0) return finish(run, node, input, value)
  return failIssue(run, new SchemaIssue.AnyOf(p.union, acc ?? [], input, run.options))
}

const unionKind: Kind<UnionPayload> = { fold: foldUnion }

const unionSingleFrame: FrameKind<UnionPayload, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    pop(run)
    return unionSingle(run, node, input, result)
  },
  copy: identity
}

const unionFrame: FrameKind<UnionPayload, unknown, ReadonlyArray<number>> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const candidates = frame.out
    const i = frame.i
    const found = frame.j
    const value = frame.value
    const acc = frame.acc
    pop(run)
    return unionLoop(run, node, input, candidates, i, found, value, acc, result, 0)
  },
  copy: identity
}

interface SuspendPayload {
  readonly thunk: () => SchemaAST.AST
  readonly resolver: Resolver
  target: Node<unknown> | undefined
}

const suspendKind: Kind<SuspendPayload> = {
  fold(run, node, input, depth) {
    const p = node.p
    const target = p.target ?? resolveTarget(run, p)
    return target.kind.fold(run, target, input, depth + 1)
  }
}

function resolveTarget(run: Run, p: SuspendPayload): Node<unknown> {
  let target: Node<unknown>
  try {
    target = p.resolver.node(p.thunk())
  } catch (error) {
    return planned(run, error)
  }
  return p.target = target
}

interface DeclarationPayload {
  readonly declaration: SchemaAST.Declaration
  run: ReturnType<SchemaAST.Declaration["run"]> | undefined
}

function foldDeclaration(run: Run, node: Node<DeclarationPayload>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  const p = node.p
  const parse = p.run ?? resolveRun(run, p)
  const result = parse(input, p.declaration, run.options)
  if (!effectIsExit(result)) return suspendAt(run, node, input, result)
  if (result._tag === "Failure") return failCause(run, result.cause)
  return complete(run, node, input, result === InternalParser.sameExit ? input : result.value)
}

function resolveRun(run: Run, p: DeclarationPayload): ReturnType<SchemaAST.Declaration["run"]> {
  let parse: ReturnType<SchemaAST.Declaration["run"]>
  try {
    parse = p.declaration.run(p.declaration.typeParameters)
  } catch (error) {
    return planned(run, error)
  }
  return p.run = parse
}

const declarationKind: Kind<DeclarationPayload> = { fold: foldDeclaration }

interface ConstructorPayload {
  readonly descriptor: SchemaAST.ConstructorDescriptor
  readonly resolver: Resolver
  source: Node<unknown> | undefined
}

function foldConstructor(run: Run, node: Node<ConstructorPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  const p = node.p
  if (p.descriptor.isConstructed(input)) return finish(run, node, input, input)
  const source = p.source ?? resolveSource(p)
  return constructed(run, node, input, source.kind.fold(run, source, input, depth + 1))
}

function resolveSource(p: ConstructorPayload): Node<unknown> {
  const link = p.descriptor.link
  return p.source = chain(link.to, [link], undefined, false, p.resolver)
}

function constructed(run: Run, node: Node<ConstructorPayload>, input: unknown, result: unknown): unknown {
  if (result !== run) return finish(run, node, input, result)
  if (run.status >= SUSPEND) return spill(run, constructorFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return run
}

const constructorKind: Kind<ConstructorPayload> = { fold: foldConstructor }

const constructorFrame: FrameKind<ConstructorPayload, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    pop(run)
    return constructed(run, node, input, result)
  },
  copy: identity
}

interface DefaultPayload {
  readonly value: Pending
  readonly inner: Node<unknown>
}

/** @internal */
export const defaultNode = (ast: SchemaAST.AST, value: Pending, inner: Node<unknown>): Node<unknown> =>
  new Node(defaultKind, ast, undefined, undefined, { value, inner: inner })

function foldDefault(run: Run, node: Node<DefaultPayload>, input: unknown, depth: number): unknown {
  const p = node.p
  const inner = p.inner
  if (input !== InternalParser.missing && input !== undefined) return inner.kind.fold(run, inner, input, depth + 1)
  const value = p.value
  if (effectIsExit(value) && value._tag === "Success") return inner.kind.fold(run, inner, value.value, depth + 1)
  spill(run, defaultFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(run, wrapEncoding(value, node.ast, input, run.options))
}

const defaultKind: Kind<DefaultPayload> = { fold: foldDefault }

const defaultFrame: FrameKind<DefaultPayload, unknown, undefined> = {
  resume(run, frame, result) {
    const inner = frame.node.p.inner
    pop(run)
    return result === run ? run : inner.kind.fold(run, inner, result, 0)
  },
  copy: identity
}

function foldTemplate(run: Run, node: Node<Node<unknown>>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(run, node, input)
  const inner = node.p
  return templateDone(run, node, input, inner.kind.fold(run, inner, input, depth + 1))
}

function templateDone(run: Run, node: Node<Node<unknown>>, input: unknown, result: unknown): unknown {
  if (result !== run) return complete(run, node, input, input)
  if (run.status >= SUSPEND) return spill(run, templateFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  if (run.status === ISSUE && run.issue !== undefined) {
    return failIssue(run, new SchemaIssue.Composite(node.ast, [run.issue], input, run.options))
  }
  const error = findError(run.cause)
  if (error._tag === "Failure") return run
  return failIssue(run, new SchemaIssue.Composite(node.ast, [error.success], input, run.options))
}

const templateKind: Kind<Node<unknown>> = { fold: foldTemplate }

const templateFrame: FrameKind<Node<unknown>, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    pop(run)
    return templateDone(run, node, input, result)
  },
  copy: identity
}

type Getter = SchemaGetter.Getter<unknown, unknown, unknown>

interface LinkPayload {
  readonly steps: ReadonlyArray<Getter>
  readonly links: ReadonlyArray<SchemaAST.Link>
  readonly resolver: Resolver
  parsers: ReadonlyArray<Node<unknown>> | undefined
  readonly local: Node<unknown> | undefined
  readonly wrap: boolean
}

type Middleware = Extract<SchemaAST.Link["transformation"], { readonly _tag: "Middleware" }>

interface MiddlewarePayload extends LinkPayload {
  readonly middleware: Middleware
  readonly at: number
  prefix: Node<unknown> | undefined
}

function linkParsers(p: LinkPayload): ReadonlyArray<Node<unknown>> {
  return p.parsers ?? resolveLinkParsers(p)
}

function resolveLinkParsers(p: LinkPayload): ReadonlyArray<Node<unknown>> {
  const resolver = p.resolver
  return p.parsers = p.links.map((link) => resolver.node(link.to))
}

function foldLink(run: Run, node: Node<LinkPayload>, input: unknown, depth: number): unknown {
  if (depth >= LIMIT) return descend(run, node, input)
  const parsers = linkParsers(node.p)
  const last = parsers.length - 1
  const child = parsers[last]
  return linkParsed(run, node, input, last, child.kind.fold(run, child, input, depth + 1), depth)
}

function linkParsed(
  run: Run,
  node: Node<LinkPayload>,
  input: unknown,
  i: number,
  result: unknown,
  depth: number
): unknown {
  if (spilled(run, result)) return spill(run, linkParseFrame, node, input, undefined, i, 0, undefined, undefined, 0)
  return linkTransform(run, node, input, i, result, depth)
}

function linkTransform(
  run: Run,
  node: Node<LinkPayload>,
  input: unknown,
  i: number,
  result: unknown,
  depth: number
): unknown {
  if (result === run) return linkAfter(run, node, input, i, result, depth)
  const getter = node.p.steps[i]
  switch (getter._tag) {
    case "Passthrough":
      return linkAfter(run, node, input, i, result, depth)
    case "Transform":
      return linkAfter(
        run,
        node,
        input,
        i,
        result === InternalParser.missing ? result : getter.transform(result),
        depth
      )
    case "TransformOptional":
      return linkAfter(
        run,
        node,
        input,
        i,
        deliver(run, InternalParser.fromOptionExit(getter.transform(InternalParser.toOption(result))), result),
        depth
      )
    case "TransformEffect": {
      if (result === InternalParser.missing) return linkAfter(run, node, input, i, result, depth)
      const effect = getter.transform(result, run.options)
      if (effectIsExit(effect)) return linkAfter(run, node, input, i, deliver(run, effect, result), depth)
      spill(run, linkEffectFrame, node, input, undefined, i, 0, undefined, undefined, 0)
      return suspendOn(run, effect)
    }
    case "TransformOptionalEffect": {
      const effect = getter.transform(InternalParser.toOption(result), run.options)
      if (effectIsExit(effect)) {
        return linkAfter(
          run,
          node,
          input,
          i,
          effect._tag === "Failure"
            ? failCause(run, effect.cause)
            : deliver(run, InternalParser.fromOptionExit(effect.value), result),
          depth
        )
      }
      spill(run, linkEffectFrame, node, input, undefined, i, 0, undefined, undefined, 0)
      return suspendOn(run, flatMap(effect, InternalParser.fromOptionExit))
    }
  }
}

function linkAfter(
  run: Run,
  node: Node<LinkPayload>,
  input: unknown,
  i: number,
  result: unknown,
  depth: number
): unknown {
  if (i !== 0) {
    if (result === run) return linkAfter(run, node, input, i - 1, result, depth)
    const child = linkParsers(node.p)[i - 1]
    return linkParsed(run, node, input, i - 1, child.kind.fold(run, child, result, depth + 1), depth)
  }
  if (result !== run) {
    const local = node.p.local
    if (local === undefined) return result
    const value = local.kind.fold(run, local, result, depth + 1)
    if (spilled(run, value)) return spill(run, linkLocalFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
    return value
  }
  if (!node.p.wrap) return run
  const failure = failureExit(run)
  spill(run, linkWrapFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(run, wrapEncoding(failure, node.ast, input, run.options))
}

/** @internal */
export function wrapEncoding(
  failure: Pending,
  ast: SchemaAST.AST,
  input: unknown,
  options: SchemaAST.ParseOptions
): Pending {
  return catchCause(
    failure,
    (cause) => failCauseSync(() => causeMap(cause, (issue) => new SchemaIssue.Encoding(ast, issue, input, options)))
  )
}

const linkKind: Kind<LinkPayload> = { fold: foldLink }

function foldMiddleware(run: Run, node: Node<MiddlewarePayload>, input: unknown, depth: number): unknown {
  if (depth >= LIMIT) return descend(run, node, input)
  const p = node.p
  const options = run.options
  const upstream = decode(p.prefix ?? resolvePrefix(p), input, options, false)
  const transformed = p.middleware.decode(
    upstream === InternalParser.sameExit
      ? exitSucceed(InternalParser.toOption(input))
      : mapEager(upstream, InternalParser.toOption),
    options
  )
  if (effectIsExit(transformed)) {
    const result = transformed._tag === "Success"
      ? deliver(run, InternalParser.fromOptionExit(transformed.value), undefined)
      : failCause(run, transformed.cause)
    return linkAfter(run, node, input, p.at, result, depth)
  }
  spill(run, linkEffectFrame, node, input, undefined, p.at, 0, undefined, undefined, 0)
  return suspendOn(run, flatMap(transformed, InternalParser.fromOptionExit))
}

function resolvePrefix(p: MiddlewarePayload): Node<unknown> {
  const links = p.links
  const at = p.at
  const resolver = p.resolver
  const to = links[at].to
  return p.prefix = at === links.length - 1
    ? resolver.node(to)
    : chain(to, links.slice(at + 1), resolver.node(to), false, resolver)
}

const middlewareKind: Kind<MiddlewarePayload> = { fold: foldMiddleware }

/** @internal */
export function middlewareNode(
  middleware: Middleware,
  ast: SchemaAST.AST,
  links: ReadonlyArray<SchemaAST.Link>,
  at: number,
  local: Node<unknown> | undefined,
  wrap: boolean,
  resolver: Resolver
): Node<unknown> {
  const steps: Array<Getter> = []
  for (let i = 0; i < at; i++) {
    const transformation = links[i].transformation
    if (transformation._tag !== "Middleware") steps.push(transformation.decode)
  }
  return new Node(middlewareKind, ast, undefined, undefined, {
    steps,
    links,
    resolver,
    parsers: undefined,
    local,
    wrap,
    middleware,
    at,
    prefix: undefined
  })
}

const linkParseFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    pop(run)
    return linkTransform(run, node, input, i, result, 0)
  },
  copy: identity
}

const linkEffectFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(run, frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    pop(run)
    return linkAfter(run, node, input, i, result, 0)
  },
  copy: identity
}

const linkLocalFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(run, _, result) {
    pop(run)
    return result
  },
  copy: identity
}

const linkWrapFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(run, _, result) {
    pop(run)
    return result
  },
  copy: identity
}

const structGuardKind: Kind<StructPayload> = { fold: guardStruct }

const arrayGuardKind: Kind<ArrayPayload> = { fold: guardArray }

const guards = new WeakMap<Node<unknown>, Node<unknown>>()

const guardResolvers = new WeakMap<Resolver, Resolver>()

function hasKind<P>(node: Node<unknown>, kind: Kind<P>): node is Node<P> {
  return node.kind === kind
}

function guardResolver(resolver: Resolver): Resolver {
  let guarded = guardResolvers.get(resolver)
  if (guarded === undefined) {
    guarded = {
      node: (ast) => guardOf(resolver.node(ast)),
      field: (ast) => guardOf(resolver.field(ast)),
      make: resolver.make
    }
    guardResolvers.set(resolver, guarded)
  }
  return guarded
}

function guardOf(node: Node<unknown>): Node<unknown> {
  if (node.checks !== undefined || node.encodingChecks !== undefined) return node
  const cached = guards.get(node)
  if (cached !== undefined) return cached
  let guarded: Node<unknown> = node
  if (hasKind(node, structKind)) {
    const p = node.p
    guarded = new Node(structGuardKind, node.ast, undefined, undefined, {
      ...p,
      resolver: guardResolver(p.resolver),
      children: undefined
    })
  } else if (hasKind(node, arrayKind)) {
    const p = node.p
    guarded = new Node(arrayGuardKind, node.ast, undefined, undefined, {
      ...p,
      resolver: guardResolver(p.resolver),
      elements: undefined,
      rest: undefined
    })
  } else if (hasKind(node, unionKind)) {
    const p = node.p
    guarded = new Node(unionKind, node.ast, undefined, undefined, {
      ...p,
      resolver: guardResolver(p.resolver),
      members: []
    })
  } else if (hasKind(node, suspendKind)) {
    const p = node.p
    guarded = new Node(suspendKind, node.ast, undefined, undefined, {
      ...p,
      resolver: guardResolver(p.resolver),
      target: undefined
    })
  }
  guards.set(node, guarded)
  return guarded
}
