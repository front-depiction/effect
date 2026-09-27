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

const HALT = Symbol()
const NONE = Symbol()

const LIMIT = 256

const ISSUE = 1
const CAUSE = 2
const SUSPEND = 3
const DESCEND = 4
const DESCEND_GUARD = 5

const CATCH = 1
const RESTART = 2
const GUARD = 4

let rStatus: typeof ISSUE | typeof CAUSE | typeof SUSPEND | typeof DESCEND | typeof DESCEND_GUARD = ISSUE
let rIssue: Issue | undefined = undefined
let rCause: Cause.Cause<Issue> = causeEmpty
let rNext: Node<unknown> | undefined = undefined
let rNextInput: unknown = undefined
const unplanned = Symbol()
let rPlanFailure: unknown = unplanned
const idle: Pending = exitSucceed(undefined)
let rPending: Pending = idle
let rResult: Exit.Exit<unknown, Issue> | undefined = undefined
let rOptions: SchemaAST.ParseOptions = {}

interface Kind<P> {
  fold(node: Node<P>, input: unknown, depth: number): unknown
  guard(node: Node<P>, input: unknown, depth: number): unknown
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
  resume(frame: Frame<P, I, O>, result: unknown): unknown
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

const stack: Array<AnyFrame> = []
let sp = 0

function spill<P, I, O>(
  kind: FrameKind<P, I, O>,
  node: Node<P>,
  input: I,
  out: O,
  i: number,
  j: number,
  value: unknown,
  acc: Issues,
  flags: number
): typeof HALT {
  const frame = stack[sp]
  if (frame === undefined) {
    stack[sp] = new Frame(kind, node, input, out, i, j, value, acc, flags)
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
  sp++
  return HALT
}

function pop(): void {
  const frame = stack[--sp]
  frame.input = undefined
  frame.out = undefined
  frame.value = undefined
  frame.acc = undefined
  frame.keys = undefined
  frame.lists = undefined
}

function popTo(base: number): void {
  while (sp > base) pop()
}

function reverse(from: number, to: number): void {
  for (let a = from, b = to - 1; a < b; a++, b--) {
    const frame = stack[a]
    stack[a] = stack[b]
    stack[b] = frame
  }
}

function release<A>(settled: A): A {
  rIssue = undefined
  rCause = causeEmpty
  rResult = undefined
  rPending = idle
  rNext = undefined
  rNextInput = undefined
  return settled
}

function failIssue(issue: Issue): typeof HALT {
  rStatus = ISSUE
  rIssue = issue
  return HALT
}

function failCause(cause: Cause.Cause<Issue>): typeof HALT {
  rStatus = CAUSE
  rCause = cause
  return HALT
}

function deliver(result: Exit.Exit<unknown, Issue>, input: unknown): unknown {
  if (result._tag === "Failure") return failCause(result.cause)
  return result === InternalParser.sameExit ? input : result.value
}

function suspendOn(pending: Pending): typeof HALT {
  rPending = pending
  rStatus = SUSPEND
  return HALT
}

function descend(node: Node<unknown>, input: unknown, status: typeof DESCEND | typeof DESCEND_GUARD): typeof HALT {
  rNext = node
  rNextInput = input
  rStatus = status
  return HALT
}

function spilled(result: unknown): boolean {
  return result === HALT && rStatus >= SUSPEND
}

function schemaIssue(): Issue | undefined {
  return rStatus === ISSUE ? rIssue : getSchemaIssue(rCause)
}

function failureExit(): Exit.Exit<never, Issue> {
  return rStatus === ISSUE && rIssue !== undefined ? exitFail(rIssue) : exitFailCause(rCause)
}

function complete(node: Node<unknown>, input: unknown, value: unknown): unknown {
  const options = rOptions
  if (options.disableChecks) return value
  const encodingChecks = node.encodingChecks
  if (encodingChecks !== undefined && input !== InternalParser.missing && value !== InternalParser.missing) {
    const issues = collectIssues(encodingChecks, input, undefined, node.ast, options)
    if (issues) return failIssue(new SchemaIssue.Composite(node.ast, issues, input, options))
  }
  const checks = node.checks
  if (checks !== undefined && value !== InternalParser.missing) {
    const issues = collectIssues(checks, value, undefined, node.ast, options)
    if (issues) return failIssue(new SchemaIssue.Composite(node.ast, issues, value, options))
  }
  return value
}

function done(node: Node<unknown>, input: unknown): unknown {
  return node.checks === undefined ? input : complete(node, input, input)
}

function finish(node: Node<unknown>, input: unknown, value: unknown): unknown {
  return node.checks === undefined && node.encodingChecks === undefined ? value : complete(node, input, value)
}

function invalidType(node: Node<unknown>, input: unknown): typeof HALT {
  return failIssue(new SchemaIssue.InvalidType(node.ast, input, rOptions))
}

function die(error: unknown): typeof HALT {
  return failCause(causeDie(error))
}

function keyIssue(node: Node<unknown>, input: unknown, key: PropertyKey): Issue | typeof HALT {
  const options = rOptions
  let issue = rIssue
  if (rStatus === CAUSE) {
    const cause = rCause
    if (cause.reasons.length === 0) return HALT
    issue = getSchemaIssue(cause)
    if (issue === undefined) return failCause(pointCause(cause, node.ast, key, input, options))
  }
  if (issue === undefined) return HALT
  const pointer = new SchemaIssue.Pointer([key], issue)
  if (options.errors === "all") return pointer
  return failIssue(new SchemaIssue.Composite(node.ast, [pointer], input, options))
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

function missingKey(node: Node<unknown>, input: unknown, key: PropertyKey, child: SchemaAST.AST): Issue | typeof HALT {
  const options = rOptions
  const issue = new SchemaIssue.Pointer([key], new SchemaIssue.MissingKey(child.context?.annotations))
  if (options.errors === "all") return issue
  return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
}

function drain(base: number, segment: number, result: unknown): unknown {
  while (true) {
    if (result === HALT && rStatus >= SUSPEND) {
      reverse(segment, sp)
      segment = sp
      const next = rNext
      if (rStatus === SUSPEND || next === undefined) return HALT
      const input = rNextInput
      rNext = undefined
      rNextInput = undefined
      result = rStatus === DESCEND ? next.kind.fold(next, input, 0) : next.kind.guard(next, input, 0)
    } else if (sp === base) {
      return result
    } else {
      const frame = stack[sp - 1]
      segment = sp - 1
      result = frame.kind.resume(frame, result)
    }
  }
}

function drive(
  base: number,
  segment: number,
  result: unknown,
  previous: SchemaAST.ParseOptions,
  root: boolean
): unknown {
  while (true) {
    try {
      return drain(base, segment, result)
    } catch (error) {
      result = unwind(base, error, previous, root)
      segment = sp
    }
  }
}

function unwind(base: number, error: unknown, previous: SchemaAST.ParseOptions, root: boolean): unknown {
  rResult = undefined
  let k = sp
  while (k > base) {
    if (stack[--k].flags & CATCH) {
      popTo(k)
      return die(error)
    }
  }
  popTo(base)
  if (root) {
    if (error !== rPlanFailure) return die(error)
    rPlanFailure = unplanned
  }
  rOptions = previous
  throw error
}

function planned<A>(error: unknown): A {
  rPlanFailure = error
  throw error
}

function run(
  node: Node<unknown>,
  input: unknown,
  base: number,
  previous: SchemaAST.ParseOptions,
  root: boolean
): unknown {
  let result: unknown
  try {
    result = node.kind.fold(node, input, 0)
  } catch (error) {
    result = unwind(base, error, previous, root)
  }
  return result === HALT ? drive(base, base, result, previous, root) : result
}

function runGuard(node: Node<unknown>, input: unknown, base: number, previous: SchemaAST.ParseOptions): unknown {
  let result: unknown
  try {
    result = node.kind.guard(node, input, 0)
  } catch (error) {
    result = unwind(base, error, previous, true)
  }
  return result === HALT ? drive(base, base, result, previous, true) : result
}

interface Snapshot {
  readonly frames: ReadonlyArray<AnyFrame>
  readonly restart: number
  readonly options: SchemaAST.ParseOptions
  readonly pending: Pending
}

function snapshot(base: number, options: SchemaAST.ParseOptions): Snapshot {
  const frames: Array<AnyFrame> = []
  let restart = -1
  for (let k = base; k < sp; k++) {
    const frame = stack[k]
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
  popTo(base)
  return { frames, restart, options, pending: rPending }
}

function restore(frames: ReadonlyArray<AnyFrame>, end: number): void {
  for (let k = 0; k < end; k++) {
    const frame = frames[k]
    spill(
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
    const top = stack[sp - 1]
    top.keys = frame.keys
    top.lists = frame.lists
  }
}

function settle(base: number, result: unknown, options: SchemaAST.ParseOptions): Pending {
  if (result !== HALT) return exitSucceed(result)
  if (rStatus !== SUSPEND) return failureExit()
  if (sp - base === 1) {
    const frame = stack[base]
    if (frame.kind === suspensionFrame && frame.node.checks === undefined && frame.node.encodingChecks === undefined) {
      pop()
      return rPending
    }
  }
  return describe(snapshot(base, options))
}

function describe(k: Snapshot): Pending {
  if (k.restart < 0) return flatMap(exitEffect(k.pending), (result) => resume(k, result))
  let first = true
  return suspend(() => {
    if (!first) return restart(k)
    first = false
    return flatMap(exitEffect(k.pending), (result) => resume(k, result))
  })
}

function resume(k: Snapshot, result: Exit.Exit<unknown, Issue>): Pending {
  const previous = rOptions
  rOptions = k.options
  const base = sp
  restore(k.frames, k.frames.length)
  const value = drive(base, sp, deliver(result, undefined), previous, false)
  rOptions = previous
  return release(settle(base, value, k.options))
}

function restart(k: Snapshot): Pending {
  const previous = rOptions
  rOptions = k.options
  const base = sp
  restore(k.frames, k.restart)
  const segment = sp
  const frame = k.frames[k.restart]
  const node = frame.node
  let result: unknown
  try {
    result = frame.flags & GUARD ? node.kind.guard(node, frame.input, 0) : node.kind.fold(node, frame.input, 0)
  } catch (error) {
    result = unwind(base, error, previous, false)
  }
  const value = drive(base, segment, result, previous, false)
  rOptions = previous
  return release(settle(base, value, k.options))
}

/** @internal */
export function decode(
  node: Node<unknown>,
  input: unknown,
  options: SchemaAST.ParseOptions,
  root: boolean
): Pending {
  if (root) rPlanFailure = unplanned
  const previous = rOptions
  rOptions = options
  const base = sp
  const value = run(node, input, base, previous, root)
  rOptions = previous
  const result = rResult
  if (result !== undefined) {
    rResult = undefined
    if (node.kind === foreignKind && (value !== HALT || rStatus < SUSPEND)) return release(result)
  }
  if (value !== HALT) {
    return value === input && input !== InternalParser.missing ? InternalParser.sameExit : exitSucceed(value)
  }
  return release(settle(base, value, options))
}

/** @internal */
export function guard(node: Node<unknown>, input: unknown, options: SchemaAST.ParseOptions): Pending {
  rPlanFailure = unplanned
  const previous = rOptions
  rOptions = options
  const base = sp
  const value = runGuard(node, input, base, previous)
  rOptions = previous
  if (value !== HALT) {
    return value === input && input !== InternalParser.missing ? InternalParser.sameExit : exitSucceed(value)
  }
  return release(settle(base, value, options))
}

const identity = <O>(out: O): O => out

const suspensionFrame: FrameKind<unknown, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    pop()
    return result === HALT ? HALT : complete(node, input, result)
  },
  copy: identity
}

function suspendAt(node: Node<unknown>, input: unknown, pending: Pending): typeof HALT {
  spill(suspensionFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(pending)
}

function foldString(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "string" ? done(node, input) : invalidType(node, input)
}

const stringKind: Kind<undefined> = { fold: foldString, guard: foldString }

function foldNumber(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "number" ? done(node, input) : invalidType(node, input)
}

const numberKind: Kind<undefined> = { fold: foldNumber, guard: foldNumber }

function foldBoolean(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "boolean" ? done(node, input) : invalidType(node, input)
}

const booleanKind: Kind<undefined> = { fold: foldBoolean, guard: foldBoolean }

function foldBigInt(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "bigint" ? done(node, input) : invalidType(node, input)
}

const bigintKind: Kind<undefined> = { fold: foldBigInt, guard: foldBigInt }

function foldSymbol(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return typeof input === "symbol" ? done(node, input) : invalidType(node, input)
}

const symbolKind: Kind<undefined> = { fold: foldSymbol, guard: foldSymbol }

function foldObjectKeyword(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return (typeof input === "object" && input !== null) || typeof input === "function"
    ? done(node, input)
    : invalidType(node, input)
}

const objectKeywordKind: Kind<undefined> = { fold: foldObjectKeyword, guard: foldObjectKeyword }

function foldNotNullish(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return input != null ? done(node, input) : invalidType(node, input)
}

const notNullishKind: Kind<undefined> = { fold: foldNotNullish, guard: foldNotNullish }

function foldAny(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return done(node, input)
}

const anyKind: Kind<undefined> = { fold: foldAny, guard: foldAny }

function foldNever(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return invalidType(node, input)
}

const neverKind: Kind<undefined> = { fold: foldNever, guard: foldNever }

function foldConst(node: Node<unknown>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  const value = node.p
  if (input !== value) return invalidType(node, input)
  return value === 0 ? done(node, input) : node.checks === undefined ? value : complete(node, input, value)
}

const constKind: Kind<unknown> = { fold: foldConst, guard: foldConst }

function foldVoid(node: Node<undefined>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return node.checks === undefined ? undefined : complete(node, input, undefined)
}

const voidKind: Kind<undefined> = { fold: foldVoid, guard: foldVoid }

function foldEnum(node: Node<ReadonlySet<unknown>>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  return node.p.has(input) ? done(node, input) : invalidType(node, input)
}

const enumKind: Kind<ReadonlySet<unknown>> = { fold: foldEnum, guard: foldEnum }

interface ForeignPayload {
  readonly get: () => Parser
  parser: Parser | undefined
}

function foldForeign(node: Node<ForeignPayload>, input: unknown, depth: number): unknown {
  const p = node.p
  const parser = p.parser ??= p.get()
  const result = parser(input, rOptions)
  if (!effectIsExit(result)) return suspendAt(node, input, result)
  if (depth === 0) rResult = result
  return deliver(result, input)
}

const foreignKind: Kind<ForeignPayload> = { fold: foldForeign, guard: foldForeign }

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
export function build(ast: SchemaAST.AST, resolver: Resolver): Node<unknown> | undefined {
  const encoding = ast.encoding
  const built = encoding === undefined ? ast.getNode(resolver) : encoding[0].getNode(ast, encoding, resolver)
  return built instanceof Node ? built : undefined
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
  return new Node(structKind, ast, ast.checks, ast.encodingChecks, {
    objects: ast,
    resolver,
    keys: ast.propertySignatures.map((ps) => ps.name),
    expected: new Set(ast.propertySignatures.map((ps) => typeof ps.name === "number" ? String(ps.name) : ps.name)),
    children: undefined
  })
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
  const local = ast.getNode(resolver)
  if (!(local instanceof Node)) return local
  return chain(ast, encoding, local, true, resolver)
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
    if (transformation._tag === "Middleware") {
      return new Node(middlewareKind, ast, undefined, undefined, {
        steps,
        links,
        resolver,
        parsers: undefined,
        local,
        wrap,
        middleware: transformation,
        at: i,
        prefix: undefined
      })
    }
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

function foldStruct(node: Node<StructPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const options = rOptions
  if (options.errors !== "all" && options.onExcessProperty === undefined && sequential(options)) {
    if (!isStruct(input)) return invalidType(node, input)
    properties(node.p)
    return structLoop(node, input, {}, 0, undefined, NONE, depth, CATCH)
  }
  return structAccumulate(node, input, depth, false)
}

function guardStruct(node: Node<StructPayload>, input: unknown, depth: number): unknown {
  if (node.checks !== undefined || node.encodingChecks !== undefined) return foldStruct(node, input, depth)
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND_GUARD)
  const options = rOptions
  if (options.errors !== "all" && options.onExcessProperty === undefined && sequential(options)) {
    if (!isStruct(input)) return invalidType(node, input)
    properties(node.p)
    return structGuardLoop(node, input, 0, undefined, NONE, depth, CATCH | GUARD)
  }
  return structAccumulate(node, input, depth, true)
}

function structAccumulate(node: Node<StructPayload>, input: unknown, depth: number, guard: boolean): unknown {
  let acc: Issues
  try {
    if (!isStruct(input)) return invalidType(node, input)
    properties(node.p)
    const options = rOptions
    if (options.onExcessProperty === "error") {
      const expected = node.p.expected
      const keys = Reflect.ownKeys(input)
      for (let i = 0; i < keys.length; i++) {
        const key = keys[i]
        if (!expected.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)) {
          const issue = new SchemaIssue.Pointer([key], new SchemaIssue.UnexpectedKey(node.ast, input[key], options))
          if (options.errors !== "all") return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
    }
  } catch (error) {
    return die(error)
  }
  if (!sequential(rOptions)) return forkStruct(node, input, acc)
  return guard
    ? structGuardLoop(node, input, 0, acc, NONE, depth, CATCH | RESTART | GUARD)
    : structLoop(node, input, {}, 0, acc, NONE, depth, CATCH | RESTART)
}

function structLoop(
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
        result = child.kind.fold(child, propertyValue(input, key), depth + 1)
      }
      if (result === HALT) {
        if (rStatus >= SUSPEND) return spill(structFrame, node, input, out, i, 0, undefined, acc, flags)
        const issue = keyIssue(node, input, key)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        InternalRecord.assignProperty(out, key, result)
      } else if (!children[i].ast.context?.isOptional) {
        const issue = missingKey(node, input, key, children[i].ast)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      }
      result = NONE
    }
  } catch (error) {
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, input, rOptions))
  return finish(node, input, out)
}

function structGuardLoop(
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
        result = child.kind.guard(child, propertyValue(input, key), depth + 1)
      }
      if (result === HALT) {
        if (rStatus >= SUSPEND) return spill(structGuardFrame, node, input, undefined, i, 0, undefined, acc, flags)
        const issue = keyIssue(node, input, key)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result === InternalParser.missing && !children[i].ast.context?.isOptional) {
        const issue = missingKey(node, input, key, children[i].ast)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      }
      result = NONE
    }
  } catch (error) {
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, input, rOptions))
  return input
}

const structKind: Kind<StructPayload> = { fold: foldStruct, guard: guardStruct }

const structFrame: FrameKind<StructPayload, Struct, Struct> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const acc = frame.acc
    const flags = frame.flags
    pop()
    return structLoop(node, input, out, i, acc, result, 0, flags)
  },
  copy: copyStruct
}

const structGuardFrame: FrameKind<StructPayload, Struct, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    const acc = frame.acc
    const flags = frame.flags
    pop()
    return structGuardLoop(node, input, i, acc, result, 0, flags)
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

function foldRecord(node: Node<RecordPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const p = node.p
  let acc: Issues
  let lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined
  try {
    if (!isStruct(input)) return invalidType(node, input)
    const indexes = resolveRecord(p)
    const options = rOptions
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
          if (options.errors !== "all") return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
    }
  } catch (error) {
    return die(error)
  }
  if (!sequential(rOptions)) return forkRecord(node, input, lists, acc)
  return recordLoop(node, input, {}, 0, 0, undefined, lists, NONE, acc, NONE, depth)
}

function recordLoop(
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
        result = child.kind.fold(child, propertyValue(input, key), depth + 1)
      }
      if (result === HALT) {
        if (rStatus >= SUSPEND) return spillRecord(recordFrame, node, input, out, i, j, keys, lists, k2, acc)
        const issue = keyIssue(node, input, key)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        InternalRecord.assignProperty(out, key, result)
      } else if (!children[i].ast.context?.isOptional) {
        const issue = missingKey(node, input, key, children[i].ast)
        if (issue === HALT) return HALT
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
          : p.support.keys(input, index.parameter, rOptions)
      }
      for (; j < keys.length; j++, k2 = NONE) {
        const key = keys[j]
        if (k2 === NONE) {
          const parser = index.key
          if (parser === undefined) {
            k2 = key
          } else {
            if (result === NONE) result = parser.kind.fold(parser, key, depth + 1)
            if (result === HALT) {
              if (rStatus >= SUSPEND) return spillRecord(recordKeyFrame, node, input, out, i, j, keys, lists, k2, acc)
              const issue = keyIssue(node, input, key)
              if (issue === HALT) return HALT
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
          result = value.kind.fold(value, input[key], depth + 1)
        }
        if (result === HALT) {
          if (rStatus >= SUSPEND) return spillRecord(recordFrame, node, input, out, i, j, keys, lists, k2, acc)
          const issue = keyIssue(node, input, key)
          if (issue === HALT) return HALT
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
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, input, rOptions))
  return finish(node, input, out)
}

function propertyKey(key: unknown): PropertyKey {
  return typeof key === "string" || typeof key === "number" || typeof key === "symbol" ? key : String(key)
}

function spillRecord(
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
): typeof HALT {
  spill(kind, node, input, out, i, j, k2, acc, CATCH | RESTART)
  const top = stack[sp - 1]
  top.keys = keys
  top.lists = lists
  return HALT
}

const recordKind: Kind<RecordPayload> = { fold: foldRecord, guard: foldRecord }

function sequential(options: SchemaAST.ParseOptions): boolean {
  return options.concurrency === undefined || resolveConcurrency(options.concurrency) === 1
}

interface Accumulator<I> {
  readonly node: Node<unknown>
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

function forkIssue<I>(s: Accumulator<I>, key: PropertyKey, exit: Exit.Failure<unknown, Issue>): Item {
  const cause = exit.cause
  if (cause.reasons.length === 0) return exitFailCause(cause)
  const issue = getSchemaIssue(cause)
  if (issue === undefined) return exitFailCause(pointCause(cause, s.node.ast, key, s.input, s.options))
  const pointer = new SchemaIssue.Pointer([key], issue)
  if (s.options.errors === "all") {
    if (s.issues) s.issues.push(pointer)
    else s.issues = [pointer]
    return exitVoid
  }
  return exitFail(new SchemaIssue.Composite(s.node.ast, [pointer], s.input, s.options))
}

function forkMissing<I>(s: Accumulator<I>, key: PropertyKey, child: SchemaAST.AST): Item {
  if (child.context?.isOptional) return exitVoid
  const issue = new SchemaIssue.Pointer([key], new SchemaIssue.MissingKey(child.context?.annotations))
  if (s.options.errors === "all") {
    if (s.issues) s.issues.push(issue)
    else s.issues = [issue]
    return exitVoid
  }
  return exitFail(new SchemaIssue.Composite(s.node.ast, [issue], s.input, s.options))
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
  if (exit._tag === "Failure") return forkIssue(s, key, exit)
  if (exit === InternalParser.sameExit) return exitVoid
  const value = exit.value
  if (value !== InternalParser.missing) {
    InternalRecord.assignProperty(s.out, key, value)
    return exitVoid
  }
  delete s.out[key]
  return forkMissing(s, key, s.children[i].ast)
}

function join<P, S extends Accumulator<unknown>>(
  frame: FrameKind<P, unknown, S>,
  node: Node<P>,
  s: S,
  eff: Item | undefined,
  done: (node: Node<P>, s: S) => unknown
): unknown {
  if (eff === undefined) return done(node, s)
  if (effectIsExit(eff)) return eff._tag === "Failure" ? failCause(eff.cause) : done(node, s)
  spill(frame, node, s.input, s, 0, 0, undefined, undefined, CATCH | RESTART)
  return suspendOn(eff)
}

function joined<P, S extends Accumulator<unknown>>(done: (node: Node<P>, s: S) => unknown): FrameKind<P, unknown, S> {
  return {
    resume(frame, result) {
      const node = frame.node
      const s = frame.out
      pop()
      return result === HALT ? HALT : done(node, s)
    },
    copy: identity
  }
}

function forkDone(node: Node<unknown>, s: Fork): unknown {
  if (s.issues) return failIssue(new SchemaIssue.Composite(node.ast, s.issues, s.input, s.options))
  return finish(node, s.input, s.out)
}

const forkFrame = joined<unknown, Fork>(forkDone)

function forkStruct(node: Node<StructPayload>, input: Struct, acc: Issues): unknown {
  const options = rOptions
  const p = node.p
  const s: Fork = {
    node,
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
    return die(error)
  }
  return join(forkFrame, node, s, eff, forkDone)
}

function forkRecord(
  node: Node<RecordPayload>,
  input: Struct,
  lists: ReadonlyArray<ReadonlyArray<PropertyKey>> | undefined,
  acc: Issues
): unknown {
  const options = rOptions
  const p = node.p
  const s: RecordFork = { node, input, options, issues: acc, out: {}, keys: p.keys, children: p.children ?? [], lists }
  let eff: Item | undefined
  try {
    if (p.keys.length > 0) eff = forkProperties(s, p.keys, { concurrency: resolveConcurrency(options.concurrency) })
  } catch (error) {
    return die(error)
  }
  return join(forkRecordFrame, node, s, eff, forkIndexes)
}

function forkIndexes(node: Node<RecordPayload>, s: RecordFork): unknown {
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
    return die(error)
  }
  return join(forkFrame, node, s, eff, forkDone)
}

const forkRecordFrame = joined<RecordPayload, RecordFork>(forkIndexes)

const forkEntries = iterateConcurrent<RecordFork, readonly [PropertyKey, IndexPlan]>()({
  onItem(s, [key, index]) {
    const parser = index.key
    if (parser === undefined) return forkValue(s, key, key, index)
    return item(decode(parser, key, s.options, false), (exit) => {
      if (exit._tag === "Failure") return forkIssue(s, key, exit)
      return forkValue(s, key, exit === InternalParser.sameExit ? key : exit.value, index)
    })
  },
  step: failed
})

function forkValue(s: RecordFork, key: PropertyKey, k2: unknown, index: IndexPlan): Item {
  const input = s.input[key]
  return item(decode(index.value, input, s.options, false), (exit) => {
    if (exit._tag === "Failure") return forkIssue(s, key, exit)
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
  if (exit._tag === "Failure") return forkIssue(s, i, exit)
  const value = exit === InternalParser.sameExit ? input : exit.value
  if (value !== InternalParser.missing) {
    s.out[i] = value
    return exitVoid
  }
  return forkMissing(s, i, elementAt(s.node.p, i, s.len).ast)
}

function forkArray(node: Node<ArrayPayload>, input: Elements, len: number): unknown {
  const options = rOptions
  const s: ArrayFork = { node, input, options, issues: undefined, out: new Array(len), len }
  let eff: Item | undefined
  try {
    eff = forkElements(s, input, {
      concurrency: resolveConcurrency(options.concurrency),
      end: arrayEnd(node.p.arrays, len)
    })
  } catch (error) {
    return die(error)
  }
  return join(forkArrayFrame, node, s, eff, forkArrayDone)
}

function forkArrayDone(node: Node<ArrayPayload>, s: ArrayFork): unknown {
  let acc: Issues
  try {
    const excess = excessElements(node, s.input, s.len, s.issues)
    if (excess === HALT) return HALT
    acc = excess
  } catch (error) {
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, s.input, s.options))
  return finish(node, s.input, s.out)
}

const forkArrayFrame = joined<ArrayPayload, ArrayFork>(forkArrayDone)

const recordFrame: FrameKind<RecordPayload, Struct, Struct> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const j = frame.j
    const keys = frame.keys
    const lists = frame.lists
    const k2 = frame.value
    const acc = frame.acc
    pop()
    return recordLoop(node, input, out, i, j, keys, lists, k2, acc, result, 0)
  },
  copy: copyStruct
}

const recordKeyFrame: FrameKind<RecordPayload, Struct, Struct> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const j = frame.j
    const keys = frame.keys
    const lists = frame.lists
    const acc = frame.acc
    pop()
    return recordLoop(node, input, out, i, j, keys, lists, NONE, acc, result, 0)
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
    p.elements = p.arrays.elements.map(p.resolver.field)
    p.rest = p.arrays.rest.map(p.resolver.field)
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

function foldArray(node: Node<ArrayPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  let len: number
  try {
    if (!Array.isArray(input)) return invalidType(node, input)
    resolveElements(node.p)
    len = input.length
  } catch (error) {
    return die(error)
  }
  if (!sequential(rOptions)) return forkArray(node, input, len)
  return arrayLoop(node, input, new Array(len), 0, len, undefined, NONE, depth, CATCH | RESTART)
}

function guardArray(node: Node<ArrayPayload>, input: unknown, depth: number): unknown {
  if (node.checks !== undefined || node.encodingChecks !== undefined) return foldArray(node, input, depth)
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND_GUARD)
  let len: number
  try {
    if (!Array.isArray(input)) return invalidType(node, input)
    resolveElements(node.p)
    len = input.length
  } catch (error) {
    return die(error)
  }
  if (!sequential(rOptions)) return forkArray(node, input, len)
  return arrayGuardLoop(node, input, 0, len, undefined, NONE, depth, CATCH | RESTART | GUARD)
}

function arrayLoop(
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
        result = child.kind.fold(child, i < len ? item : InternalParser.missing, depth + 1)
      }
      if (result === HALT) {
        if (rStatus >= SUSPEND) return spill(arrayFrame, node, input, out, i, len, undefined, acc, flags)
        const issue = keyIssue(node, input, i)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result !== InternalParser.missing) {
        out[i] = result
      } else {
        const child = elementAt(p, i, len).ast
        if (!child.context?.isOptional) {
          const issue = missingKey(node, input, i, child)
          if (issue === HALT) return HALT
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
      result = NONE
    }
    const excess = excessElements(node, input, len, acc)
    if (excess === HALT) return HALT
    acc = excess
  } catch (error) {
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, input, rOptions))
  return finish(node, input, out)
}

function arrayGuardLoop(
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
        result = child.kind.guard(child, i < len ? item : InternalParser.missing, depth + 1)
      }
      if (result === HALT) {
        if (rStatus >= SUSPEND) return spill(arrayGuardFrame, node, input, undefined, i, len, undefined, acc, flags)
        const issue = keyIssue(node, input, i)
        if (issue === HALT) return HALT
        if (acc) acc.push(issue)
        else acc = [issue]
      } else if (result === InternalParser.missing) {
        const child = elementAt(p, i, len).ast
        if (!child.context?.isOptional) {
          const issue = missingKey(node, input, i, child)
          if (issue === HALT) return HALT
          if (acc) acc.push(issue)
          else acc = [issue]
        }
      }
      result = NONE
    }
    const excess = excessElements(node, input, len, acc)
    if (excess === HALT) return HALT
    acc = excess
  } catch (error) {
    return die(error)
  }
  if (acc) return failIssue(new SchemaIssue.Composite(node.ast, acc, input, rOptions))
  return input
}

function excessElements(node: Node<ArrayPayload>, input: Elements, len: number, acc: Issues): Issues | typeof HALT {
  const arrays = node.p.arrays
  const elementLen = arrays.elements.length
  if (arrays.rest.length === 0 && len > elementLen) {
    const options = rOptions
    for (let i = elementLen; i < len; i++) {
      const issue = new SchemaIssue.Pointer([i], new SchemaIssue.UnexpectedKey(node.ast, input[i], options))
      if (options.errors !== "all") return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
      if (acc) acc.push(issue)
      else acc = [issue]
    }
  }
  return acc
}

const arrayKind: Kind<ArrayPayload> = { fold: foldArray, guard: guardArray }

const arrayFrame: FrameKind<ArrayPayload, Elements, Array<unknown>> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const out = frame.out
    const i = frame.i
    const len = frame.j
    const acc = frame.acc
    const flags = frame.flags
    pop()
    return arrayLoop(node, input, out, i, len, acc, result, 0, flags)
  },
  copy: (out) => out.slice()
}

const arrayGuardFrame: FrameKind<ArrayPayload, Elements, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    const len = frame.j
    const acc = frame.acc
    const flags = frame.flags
    pop()
    return arrayGuardLoop(node, input, i, len, acc, result, 0, flags)
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

function foldUnion(node: Node<UnionPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const p = node.p
  const candidates = (p.index ??= p.candidates(p.union.types))(input, p.make)
  if (candidates.length === 0) return failIssue(new SchemaIssue.AnyOf(p.union, [], input, rOptions))
  if (candidates.length === 1) {
    const child = member(p, candidates[0])
    return unionSingle(node, input, child.kind.fold(child, input, depth + 1))
  }
  return unionLoop(node, input, candidates, 0, -1, undefined, undefined, NONE, depth)
}

function guardUnion(node: Node<UnionPayload>, input: unknown, depth: number): unknown {
  if (node.checks !== undefined || node.encodingChecks !== undefined) return foldUnion(node, input, depth)
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND_GUARD)
  const p = node.p
  const candidates = (p.index ??= p.candidates(p.union.types))(input, p.make)
  if (candidates.length === 0) return failIssue(new SchemaIssue.AnyOf(p.union, [], input, rOptions))
  if (candidates.length === 1) {
    const child = member(p, candidates[0])
    return unionSingle(node, input, child.kind.guard(child, input, depth + 1))
  }
  return unionGuardLoop(node, input, candidates, 0, -1, undefined, undefined, NONE, depth)
}

function unionSingle(node: Node<UnionPayload>, input: unknown, result: unknown): unknown {
  if (result !== HALT) return finish(node, input, result)
  if (rStatus >= SUSPEND) return spill(unionSingleFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  const issue = schemaIssue()
  if (issue === undefined) return HALT
  return failIssue(new SchemaIssue.AnyOf(node.p.union, [issue], input, rOptions))
}

function unionLoop(
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
      result = child.kind.fold(child, input, depth + 1)
    }
    if (result === HALT) {
      if (rStatus >= SUSPEND) return spill(unionFrame, node, input, candidates, i, found, value, acc, 0)
      const issue = schemaIssue()
      if (issue === undefined) return HALT
      if (acc) acc.push(issue)
      else acc = [issue]
    } else {
      if (found >= 0) {
        const types = p.union.types
        return failIssue(new SchemaIssue.OneOf(p.union, [types[found], types[candidates[i]]], input, rOptions))
      }
      if (!p.oneOf) return finish(node, input, result)
      value = result
      found = candidates[i]
    }
    result = NONE
  }
  if (found >= 0) return finish(node, input, value)
  return failIssue(new SchemaIssue.AnyOf(p.union, acc ?? [], input, rOptions))
}

function unionGuardLoop(
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
      result = child.kind.guard(child, input, depth + 1)
    }
    if (result === HALT) {
      if (rStatus >= SUSPEND) return spill(unionGuardFrame, node, input, candidates, i, found, value, acc, 0)
      const issue = schemaIssue()
      if (issue === undefined) return HALT
      if (acc) acc.push(issue)
      else acc = [issue]
    } else {
      if (found >= 0) {
        const types = p.union.types
        return failIssue(new SchemaIssue.OneOf(p.union, [types[found], types[candidates[i]]], input, rOptions))
      }
      if (!p.oneOf) return finish(node, input, result)
      value = result
      found = candidates[i]
    }
    result = NONE
  }
  if (found >= 0) return finish(node, input, value)
  return failIssue(new SchemaIssue.AnyOf(p.union, acc ?? [], input, rOptions))
}

const unionKind: Kind<UnionPayload> = { fold: foldUnion, guard: guardUnion }

const unionSingleFrame: FrameKind<UnionPayload, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    pop()
    return unionSingle(node, input, result)
  },
  copy: identity
}

const unionFrame: FrameKind<UnionPayload, unknown, ReadonlyArray<number>> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const candidates = frame.out
    const i = frame.i
    const found = frame.j
    const value = frame.value
    const acc = frame.acc
    pop()
    return unionLoop(node, input, candidates, i, found, value, acc, result, 0)
  },
  copy: identity
}

const unionGuardFrame: FrameKind<UnionPayload, unknown, ReadonlyArray<number>> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const candidates = frame.out
    const i = frame.i
    const found = frame.j
    const value = frame.value
    const acc = frame.acc
    pop()
    return unionGuardLoop(node, input, candidates, i, found, value, acc, result, 0)
  },
  copy: identity
}

interface SuspendPayload {
  readonly thunk: () => SchemaAST.AST
  readonly resolver: Resolver
  target: Node<unknown> | undefined
}

const suspendKind: Kind<SuspendPayload> = {
  fold(node, input, depth) {
    const p = node.p
    const target = p.target ?? resolveTarget(p)
    return target.kind.fold(target, input, depth + 1)
  },
  guard(node, input, depth) {
    const p = node.p
    const target = p.target ?? resolveTarget(p)
    return target.kind.guard(target, input, depth + 1)
  }
}

function resolveTarget(p: SuspendPayload): Node<unknown> {
  let target: Node<unknown>
  try {
    target = p.resolver.node(p.thunk())
  } catch (error) {
    return planned(error)
  }
  return p.target = target
}

interface DeclarationPayload {
  readonly declaration: SchemaAST.Declaration
  run: ReturnType<SchemaAST.Declaration["run"]> | undefined
}

function foldDeclaration(node: Node<DeclarationPayload>, input: unknown): unknown {
  if (input === InternalParser.missing) return input
  const p = node.p
  const run = p.run ?? resolveRun(p)
  const result = run(input, p.declaration, rOptions)
  if (!effectIsExit(result)) return suspendAt(node, input, result)
  if (result._tag === "Failure") return failCause(result.cause)
  return complete(node, input, result === InternalParser.sameExit ? input : result.value)
}

function resolveRun(p: DeclarationPayload): ReturnType<SchemaAST.Declaration["run"]> {
  let run: ReturnType<SchemaAST.Declaration["run"]>
  try {
    run = p.declaration.run(p.declaration.typeParameters)
  } catch (error) {
    return planned(error)
  }
  return p.run = run
}

const declarationKind: Kind<DeclarationPayload> = { fold: foldDeclaration, guard: foldDeclaration }

interface ConstructorPayload {
  readonly descriptor: SchemaAST.ConstructorDescriptor
  readonly resolver: Resolver
  source: Node<unknown> | undefined
}

function foldConstructor(node: Node<ConstructorPayload>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  const p = node.p
  if (p.descriptor.isConstructed(input)) return finish(node, input, input)
  const source = p.source ?? resolveSource(p)
  return constructed(node, input, source.kind.fold(source, input, depth + 1))
}

function resolveSource(p: ConstructorPayload): Node<unknown> {
  const link = p.descriptor.link
  return p.source = chain(link.to, [link], undefined, false, p.resolver)
}

function constructed(node: Node<ConstructorPayload>, input: unknown, result: unknown): unknown {
  if (result !== HALT) return finish(node, input, result)
  if (rStatus >= SUSPEND) return spill(constructorFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return HALT
}

const constructorKind: Kind<ConstructorPayload> = { fold: foldConstructor, guard: foldConstructor }

const constructorFrame: FrameKind<ConstructorPayload, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    pop()
    return constructed(node, input, result)
  },
  copy: identity
}

interface DefaultPayload {
  readonly value: Pending
  readonly inner: Node<unknown>
}

/** @internal */
export const defaultNode = (ast: SchemaAST.AST, value: Pending, inner: Node<unknown>): Node<unknown> =>
  new Node(defaultKind, ast, undefined, undefined, { value, inner })

function foldDefault(node: Node<DefaultPayload>, input: unknown, depth: number): unknown {
  const p = node.p
  const inner = p.inner
  if (input !== InternalParser.missing && input !== undefined) return inner.kind.fold(inner, input, depth + 1)
  const value = p.value
  if (effectIsExit(value) && value._tag === "Success") return inner.kind.fold(inner, value.value, depth + 1)
  spill(defaultFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(wrapEncoding(value, node.ast, input, rOptions))
}

const defaultKind: Kind<DefaultPayload> = { fold: foldDefault, guard: foldDefault }

const defaultFrame: FrameKind<DefaultPayload, unknown, undefined> = {
  resume(frame, result) {
    const inner = frame.node.p.inner
    pop()
    return result === HALT ? HALT : inner.kind.fold(inner, result, 0)
  },
  copy: identity
}

function foldTemplate(node: Node<Node<unknown>>, input: unknown, depth: number): unknown {
  if (input === InternalParser.missing) return input
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const inner = node.p
  return templateDone(node, input, inner.kind.fold(inner, input, depth + 1))
}

function templateDone(node: Node<Node<unknown>>, input: unknown, result: unknown): unknown {
  if (result !== HALT) return complete(node, input, input)
  if (rStatus >= SUSPEND) return spill(templateFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  if (rStatus === ISSUE && rIssue !== undefined) {
    return failIssue(new SchemaIssue.Composite(node.ast, [rIssue], input, rOptions))
  }
  const error = findError(rCause)
  if (error._tag === "Failure") return HALT
  return failIssue(new SchemaIssue.Composite(node.ast, [error.success], input, rOptions))
}

const templateKind: Kind<Node<unknown>> = { fold: foldTemplate, guard: foldTemplate }

const templateFrame: FrameKind<Node<unknown>, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    pop()
    return templateDone(node, input, result)
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

function foldLink(node: Node<LinkPayload>, input: unknown, depth: number): unknown {
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const parsers = linkParsers(node.p)
  const last = parsers.length - 1
  const child = parsers[last]
  return linkParsed(node, input, last, child.kind.fold(child, input, depth + 1), depth)
}

function linkParsed(node: Node<LinkPayload>, input: unknown, i: number, result: unknown, depth: number): unknown {
  if (spilled(result)) return spill(linkParseFrame, node, input, undefined, i, 0, undefined, undefined, 0)
  return linkTransform(node, input, i, result, depth)
}

function linkTransform(node: Node<LinkPayload>, input: unknown, i: number, result: unknown, depth: number): unknown {
  if (result === HALT) return linkAfter(node, input, i, result, depth)
  const getter = node.p.steps[i]
  switch (getter._tag) {
    case "Passthrough":
      return linkAfter(node, input, i, result, depth)
    case "Transform":
      return linkAfter(
        node,
        input,
        i,
        result === InternalParser.missing ? result : getter.transform(result),
        depth
      )
    case "TransformOptional":
      return linkAfter(
        node,
        input,
        i,
        deliver(InternalParser.fromOptionExit(getter.transform(InternalParser.toOption(result))), result),
        depth
      )
    case "TransformEffect": {
      if (result === InternalParser.missing) return linkAfter(node, input, i, result, depth)
      const effect = getter.transform(result, rOptions)
      if (effectIsExit(effect)) return linkAfter(node, input, i, deliver(effect, result), depth)
      spill(linkEffectFrame, node, input, undefined, i, 0, undefined, undefined, 0)
      return suspendOn(effect)
    }
    case "TransformOptionalEffect": {
      const effect = getter.transform(InternalParser.toOption(result), rOptions)
      if (effectIsExit(effect)) {
        return linkAfter(
          node,
          input,
          i,
          effect._tag === "Failure"
            ? failCause(effect.cause)
            : deliver(InternalParser.fromOptionExit(effect.value), result),
          depth
        )
      }
      spill(linkEffectFrame, node, input, undefined, i, 0, undefined, undefined, 0)
      return suspendOn(flatMap(effect, InternalParser.fromOptionExit))
    }
  }
}

function linkAfter(node: Node<LinkPayload>, input: unknown, i: number, result: unknown, depth: number): unknown {
  if (i !== 0) {
    if (result === HALT) return linkAfter(node, input, i - 1, result, depth)
    const child = linkParsers(node.p)[i - 1]
    return linkParsed(node, input, i - 1, child.kind.fold(child, result, depth + 1), depth)
  }
  if (result !== HALT) {
    const local = node.p.local
    if (local === undefined) return result
    const value = local.kind.fold(local, result, depth + 1)
    if (spilled(value)) return spill(linkLocalFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
    return value
  }
  if (!node.p.wrap) return HALT
  const failure = failureExit()
  spill(linkWrapFrame, node, input, undefined, 0, 0, undefined, undefined, 0)
  return suspendOn(wrapEncoding(failure, node.ast, input, rOptions))
}

function wrapEncoding(
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

const linkKind: Kind<LinkPayload> = { fold: foldLink, guard: foldLink }

function foldMiddleware(node: Node<MiddlewarePayload>, input: unknown, depth: number): unknown {
  if (depth >= LIMIT) return descend(node, input, DESCEND)
  const p = node.p
  const options = rOptions
  const upstream = decode(p.prefix ?? resolvePrefix(p), input, options, false)
  const transformed = p.middleware.decode(
    upstream === InternalParser.sameExit
      ? exitSucceed(InternalParser.toOption(input))
      : mapEager(upstream, InternalParser.toOption),
    options
  )
  if (effectIsExit(transformed)) {
    const result = transformed._tag === "Success"
      ? deliver(InternalParser.fromOptionExit(transformed.value), undefined)
      : failCause(transformed.cause)
    return linkAfter(node, input, p.at, result, depth)
  }
  spill(linkEffectFrame, node, input, undefined, p.at, 0, undefined, undefined, 0)
  return suspendOn(flatMap(transformed, InternalParser.fromOptionExit))
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

const middlewareKind: Kind<MiddlewarePayload> = { fold: foldMiddleware, guard: foldMiddleware }

const linkParseFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    pop()
    return linkTransform(node, input, i, result, 0)
  },
  copy: identity
}

const linkEffectFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(frame, result) {
    const node = frame.node
    const input = frame.input
    const i = frame.i
    pop()
    return linkAfter(node, input, i, result, 0)
  },
  copy: identity
}

const linkLocalFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(_, result) {
    pop()
    return result
  },
  copy: identity
}

const linkWrapFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(_, result) {
    pop()
    return result
  },
  copy: identity
}
