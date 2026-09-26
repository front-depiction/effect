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
  failCauseSync,
  findError,
  flatMap,
  suspend
} from "../effect.ts"
import * as InternalRecord from "../record.ts"
import { getSchemaIssue } from "./cause.ts"
import { collectIssues } from "./checks.ts"
import * as InternalParser from "./parser.ts"

type Issue = SchemaIssue.Issue
type Pending = Effect.Effect<unknown, Issue, unknown>

const DONE = 0
const SUSPEND = 1
type Signal = typeof DONE | typeof SUSPEND
type Step = Signal | Node<unknown>

const OK = 0
const ISSUE = 1
const CAUSE = 2

const CATCH = 1
const RESTART = 2

let rStatus: typeof OK | typeof ISSUE | typeof CAUSE = OK
let rValue: unknown = undefined
let rIssue: Issue | undefined = undefined
let rCause: Cause.Cause<Issue> = causeEmpty
let rInput: unknown = undefined
const unplanned = Symbol()
let rPlanFailure: unknown = unplanned
const idle: Pending = exitSucceed(undefined)
let rPending: Pending = idle
let rResult: Exit.Exit<unknown, Issue> | undefined = undefined
let rOptions: SchemaAST.ParseOptions = {}

interface Kind<P> {
  enter(node: Node<P>, input: unknown): Step
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
  resume(frame: Frame<P, I, O>): Step
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
  acc: Arr.NonEmptyArray<Issue> | undefined
  flags: number
  constructor(
    kind: FrameKind<P, I, O>,
    node: Node<P>,
    input: I,
    out: O,
    i: number,
    j: number,
    value: unknown,
    acc: Arr.NonEmptyArray<Issue> | undefined,
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
  }
}

type AnyFrame = Frame<unknown, unknown, unknown>

const stack: Array<AnyFrame> = []
let sp = 0

function push<P, I, O>(
  kind: FrameKind<P, I, O>,
  node: Node<P>,
  input: I,
  out: O,
  i: number,
  j: number,
  flags: number
): void {
  const frame = stack[sp]
  if (frame === undefined) {
    stack[sp] = new Frame(kind, node, input, out, i, j, undefined, undefined, flags)
  } else {
    frame.kind = kind
    frame.node = node
    frame.input = input
    frame.out = out
    frame.i = i
    frame.j = j
    frame.value = undefined
    frame.acc = undefined
    frame.flags = flags
  }
  sp++
}

function pop(): void {
  const frame = stack[--sp]
  frame.input = undefined
  frame.out = undefined
  frame.value = undefined
  frame.acc = undefined
}

function popTo(base: number): void {
  while (sp > base) pop()
}

function release<A>(settled: A): A {
  rValue = undefined
  rInput = undefined
  rIssue = undefined
  rCause = causeEmpty
  rResult = undefined
  rPending = idle
  return settled
}

function succeed(value: unknown): Signal {
  rStatus = OK
  rValue = value
  return DONE
}

function failIssue(issue: Issue): Signal {
  rStatus = ISSUE
  rIssue = issue
  return DONE
}

function failCause(cause: Cause.Cause<Issue>): Signal {
  rStatus = CAUSE
  rCause = cause
  return DONE
}

function deliver(result: Exit.Exit<unknown, Issue>, input: unknown): Signal {
  if (result._tag === "Failure") return failCause(result.cause)
  return succeed(result === InternalParser.sameExit ? input : result.value)
}

function suspendOn(pending: Pending): Signal {
  rPending = pending
  return SUSPEND
}

function enterChild(node: Node<unknown>, input: unknown): Step {
  rInput = input
  return node
}

function add<P, I, O>(frame: Frame<P, I, O>, issue: Issue): void {
  if (frame.acc) frame.acc.push(issue)
  else frame.acc = [issue]
}

function schemaIssue(): Issue | undefined {
  return rStatus === ISSUE ? rIssue : getSchemaIssue(rCause)
}

function failureExit(): Exit.Exit<never, Issue> {
  return rStatus === ISSUE && rIssue !== undefined ? exitFail(rIssue) : exitFailCause(rCause)
}

function result(): Exit.Exit<unknown, Issue> {
  return rStatus === OK ? exitSucceed(rValue) : failureExit()
}

function complete(node: Node<unknown>, input: unknown, value: unknown): Signal {
  const options = rOptions
  if (options.disableChecks) return succeed(value)
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
  return succeed(value)
}

function invalidType(node: Node<unknown>, input: unknown): Signal {
  return failIssue(new SchemaIssue.InvalidType(node.ast, input, rOptions))
}

function keyFailure<P, I, O>(frame: Frame<P, I, O>, key: PropertyKey): Signal | undefined {
  const options = rOptions
  let issue = rIssue
  if (rStatus === CAUSE) {
    const cause = rCause
    if (cause.reasons.length === 0) {
      pop()
      return DONE
    }
    issue = getSchemaIssue(cause)
    if (issue === undefined) {
      const ast = frame.node.ast
      const input = frame.input
      pop()
      return failCause(pointCause(cause, ast, key, input, options))
    }
  }
  if (issue === undefined) return undefined
  const pointer = new SchemaIssue.Pointer([key], issue)
  if (options.errors === "all") {
    add(frame, pointer)
    return undefined
  }
  const ast = frame.node.ast
  const input = frame.input
  pop()
  return failIssue(new SchemaIssue.Composite(ast, [pointer], input, options))
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

function missingKey<P, I, O>(frame: Frame<P, I, O>, key: PropertyKey, child: SchemaAST.AST): Signal | undefined {
  const options = rOptions
  const issue = new SchemaIssue.Pointer([key], new SchemaIssue.MissingKey(child.context?.annotations))
  if (options.errors === "all") {
    add(frame, issue)
    return undefined
  }
  const ast = frame.node.ast
  const input = frame.input
  pop()
  return failIssue(new SchemaIssue.Composite(ast, [issue], input, options))
}

function decodeLoop(base: number, step: Step): Signal {
  while (true) {
    if (typeof step !== "number") {
      step = step.kind.enter(step, rInput)
    } else if (step === SUSPEND || sp === base) {
      return step
    } else {
      const frame = stack[sp - 1]
      step = frame.kind.resume(frame)
    }
  }
}

type Loop = (base: number, step: Step) => Signal

function drive(loop: Loop, base: number, step: Step, previous: SchemaAST.ParseOptions, root: boolean): Signal {
  while (true) {
    try {
      return loop(base, step)
    } catch (error) {
      step = unwind(base, error, previous, root)
    }
  }
}

function unwind(base: number, error: unknown, previous: SchemaAST.ParseOptions, root: boolean): Signal {
  rResult = undefined
  let k = sp
  while (k > base) {
    if (stack[--k].flags & CATCH) {
      popTo(k)
      return failCause(causeDie(error))
    }
  }
  popTo(base)
  if (root) {
    if (error !== rPlanFailure) return failCause(causeDie(error))
    rPlanFailure = unplanned
  }
  rOptions = previous
  throw error
}

function planned<A>(error: unknown): A {
  rPlanFailure = error
  throw error
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
    frames.push(
      new Frame(
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
    )
  }
  popTo(base)
  return { frames, restart, options, pending: rPending }
}

function restore(frames: ReadonlyArray<AnyFrame>, end: number): void {
  for (let k = 0; k < end; k++) {
    const frame = frames[k]
    push(frame.kind, frame.node, frame.input, frame.kind.copy(frame.out), frame.i, frame.j, frame.flags)
    const top = stack[sp - 1]
    top.value = frame.value
    if (frame.acc) top.acc = [frame.acc[0], ...frame.acc.slice(1)]
  }
}

function settle(base: number, signal: Signal, options: SchemaAST.ParseOptions): Pending {
  if (signal === DONE) return result()
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
  const signal = drive(decodeLoop, base, deliver(result, undefined), previous, false)
  rOptions = previous
  return release(settle(base, signal, k.options))
}

function restart(k: Snapshot): Pending {
  const previous = rOptions
  rOptions = k.options
  const base = sp
  restore(k.frames, k.restart)
  const frame = k.frames[k.restart]
  const signal = drive(decodeLoop, base, enterChild(frame.node, frame.input), previous, false)
  rOptions = previous
  return release(settle(base, signal, k.options))
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
  const signal = drive(decodeLoop, base, enterChild(node, input), previous, root)
  rOptions = previous
  return release(
    signal === DONE && node.kind === foreignKind && rResult !== undefined
      ? rResult
      : signal === DONE && rStatus === OK && rValue === input && input !== InternalParser.missing
      ? InternalParser.sameExit
      : settle(base, signal, options)
  )
}

const identity = <O>(out: O): O => out

const suspensionFrame: FrameKind<unknown, unknown, undefined> = {
  resume(frame) {
    const node = frame.node
    const input = frame.input
    pop()
    return rStatus === OK ? complete(node, input, rValue) : DONE
  },
  copy: identity
}

function suspendAt(node: Node<unknown>, input: unknown, pending: Pending): Signal {
  push(suspensionFrame, node, input, undefined, 0, 0, 0)
  return suspendOn(pending)
}

function enterString(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return typeof input === "string" ? complete(node, input, input) : invalidType(node, input)
}

const stringKind: Kind<undefined> = { enter: enterString }

function enterNumber(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return typeof input === "number" ? complete(node, input, input) : invalidType(node, input)
}

const numberKind: Kind<undefined> = { enter: enterNumber }

function enterBoolean(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return typeof input === "boolean" ? complete(node, input, input) : invalidType(node, input)
}

const booleanKind: Kind<undefined> = { enter: enterBoolean }

function enterBigInt(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return typeof input === "bigint" ? complete(node, input, input) : invalidType(node, input)
}

const bigintKind: Kind<undefined> = { enter: enterBigInt }

function enterSymbol(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return typeof input === "symbol" ? complete(node, input, input) : invalidType(node, input)
}

const symbolKind: Kind<undefined> = { enter: enterSymbol }

function enterObjectKeyword(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return (typeof input === "object" && input !== null) || typeof input === "function"
    ? complete(node, input, input)
    : invalidType(node, input)
}

const objectKeywordKind: Kind<undefined> = { enter: enterObjectKeyword }

function enterNotNullish(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return input != null ? complete(node, input, input) : invalidType(node, input)
}

const notNullishKind: Kind<undefined> = { enter: enterNotNullish }

function enterAny(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return complete(node, input, input)
}

const anyKind: Kind<undefined> = { enter: enterAny }

function enterNever(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return invalidType(node, input)
}

const neverKind: Kind<undefined> = { enter: enterNever }

function enterConst(node: Node<unknown>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  const value = node.p
  if (input === value) return complete(node, input, value === 0 ? input : value)
  return invalidType(node, input)
}

const constKind: Kind<unknown> = { enter: enterConst }

function enterVoid(node: Node<undefined>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return complete(node, input, undefined)
}

const voidKind: Kind<undefined> = { enter: enterVoid }

function enterEnum(node: Node<ReadonlySet<unknown>>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  return node.p.has(input) ? complete(node, input, input) : invalidType(node, input)
}

const enumKind: Kind<ReadonlySet<unknown>> = { enter: enterEnum }

interface ForeignPayload {
  readonly get: () => Parser
  parser: Parser | undefined
}

function enterForeign(node: Node<ForeignPayload>, input: unknown): Step {
  const p = node.p
  const parser = p.parser ??= p.get()
  const result = parser(input, rOptions)
  if (!effectIsExit(result)) return suspendAt(node, input, result)
  rResult = result
  return deliver(result, input)
}

const foreignKind: Kind<ForeignPayload> = { enter: enterForeign }

/** @internal */
export interface Resolver {
  readonly node: (ast: SchemaAST.AST) => Node<unknown>
  readonly local: (ast: SchemaAST.AST) => Parser
  readonly whole: (ast: SchemaAST.AST) => Parser
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
  if (ast.indexSignatures.length > 0) return foreign(ast, () => resolver.local(ast))
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
    oneOf: ast.options?.mode === "oneOf"
  })

/** @internal */
export const suspendNode = (ast: SchemaAST.Suspend, resolver: Resolver): Node<unknown> =>
  node(suspendKind, ast, { thunk: ast.thunk, resolver, target: undefined })

/** @internal */
export function declarationNode(ast: SchemaAST.Declaration, resolver: Resolver): Node<unknown> {
  for (const parameter of ast.typeParameters) resolver.node(parameter)
  return new Node(declarationKind, ast, ast.checks, ast.encodingChecks, { declaration: ast, run: undefined })
}

/** @internal */
export const templateNode = (ast: SchemaAST.TemplateLiteral, inner: Node<unknown>): Node<unknown> =>
  node(templateKind, ast, inner)

/** @internal */
export function linkNode(ast: SchemaAST.AST, encoding: SchemaAST.Encoding, resolver: Resolver): Node<unknown> {
  const steps: Array<Getter> = []
  for (const link of encoding) {
    const transformation = link.transformation
    if (transformation._tag === "Middleware") return foreign(ast, () => resolver.whole(ast))
    steps.push(transformation.decode)
  }
  const local = ast.getNode(resolver)
  if (!(local instanceof Node)) return local
  return new Node(linkKind, ast, undefined, undefined, { steps, links: encoding, resolver, parsers: undefined, local })
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
  return p.children = p.objects.propertySignatures.map((ps) => resolver.node(ps.type))
}

type Struct = Record<PropertyKey, unknown>

const isStruct = (input: unknown): input is Struct =>
  typeof input === "object" && input !== null && !Array.isArray(input)

function copyStruct(out: Struct | undefined): Struct | undefined {
  if (out === undefined) return out
  const copy: Struct = {}
  for (const key of Reflect.ownKeys(out)) InternalRecord.assignProperty(copy, key, out[key])
  return copy
}

function enterStruct(node: Node<StructPayload>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  const options = rOptions
  if (options.errors !== "all" && options.onExcessProperty === undefined) {
    if (!isStruct(input)) return invalidType(node, input)
    properties(node.p)
    push(structFrame, node, input, {}, 0, 0, CATCH)
    return property(node, input, 0)
  }
  push(structFrame, node, input, undefined, 0, 0, CATCH | RESTART)
  if (!isStruct(input)) {
    pop()
    return invalidType(node, input)
  }
  properties(node.p)
  stack[sp - 1].out = {}
  if (options.onExcessProperty === "error") {
    const expected = node.p.expected
    const keys = Reflect.ownKeys(input)
    for (let i = 0; i < keys.length; i++) {
      const key = keys[i]
      if (!expected.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)) {
        const issue = new SchemaIssue.Pointer([key], new SchemaIssue.UnexpectedKey(node.ast, input[key], options))
        if (options.errors !== "all") {
          pop()
          return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
        }
        add(stack[sp - 1], issue)
      }
    }
  }
  return property(node, input, 0)
}

const structKind: Kind<StructPayload> = { enter: enterStruct }

function property(node: Node<StructPayload>, input: Struct, i: number): Step {
  const keys = node.p.keys
  if (i === keys.length) return finishStruct()
  const key = keys[i]
  const child = properties(node.p)[i]
  const value = (key === "__proto__" ? Object.hasOwn(input, key) : key in input) ? input[key] : InternalParser.missing
  return enterChild(child, value)
}

function finishStruct(): Signal {
  const frame = stack[sp - 1]
  const node = frame.node
  const input = frame.input
  const out = frame.out
  const issues = frame.acc
  pop()
  if (issues) return failIssue(new SchemaIssue.Composite(node.ast, issues, input, rOptions))
  return complete(node, input, out === undefined ? input : out)
}

function resumeStruct(frame: Frame<StructPayload, Struct, Struct | undefined>): Step {
  const node = frame.node
  const i = frame.i
  const key = node.p.keys[i]
  if (rStatus === OK) {
    const value = rValue
    if (value !== InternalParser.missing) {
      if (frame.out !== undefined) InternalRecord.assignProperty(frame.out, key, value)
    } else {
      const child = properties(node.p)[i].ast
      if (!child.context?.isOptional) {
        const terminal = missingKey(frame, key, child)
        if (terminal !== undefined) return terminal
      }
    }
  } else {
    const terminal = keyFailure(frame, key)
    if (terminal !== undefined) return terminal
  }
  frame.i = i + 1
  return property(node, frame.input, i + 1)
}

const structFrame: FrameKind<StructPayload, Struct, Struct | undefined> = {
  resume: resumeStruct,
  copy: copyStruct
}

interface ArrayPayload {
  readonly arrays: SchemaAST.Arrays
  readonly resolver: Resolver
  elements: ReadonlyArray<Node<unknown>> | undefined
  rest: ReadonlyArray<Node<unknown>> | undefined
}

type Elements = ReadonlyArray<unknown>

function enterArray(node: Node<ArrayPayload>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  push(arrayFrame, node, input, undefined, 0, 0, CATCH | RESTART)
  if (!Array.isArray(input)) {
    pop()
    return invalidType(node, input)
  }
  const p = node.p
  if (p.elements === undefined) {
    p.elements = p.arrays.elements.map(p.resolver.node)
    p.rest = p.arrays.rest.map(p.resolver.node)
  }
  const len = input.length
  const top = stack[sp - 1]
  top.out = new Array(len)
  top.j = len
  return element(node, input, 0, len)
}

const arrayKind: Kind<ArrayPayload> = { enter: enterArray }

function element(node: Node<ArrayPayload>, input: Elements, i: number, len: number): Step {
  const arrays = node.p.arrays
  const elementLen = arrays.elements.length
  const restLen = arrays.rest.length
  const end = restLen === 0 ? elementLen : Math.max(len, elementLen + Math.max(0, restLen - 1))
  if (i >= end) return finishArray(node, input, len)
  const item = input[i]
  const child = elementAt(node.p, i, len)
  const value = i < len ? item : InternalParser.missing
  return enterChild(child, value)
}

function elementAt(p: ArrayPayload, i: number, len: number): Node<unknown> {
  const elements = p.elements ?? []
  const rest = p.rest ?? []
  const elementLen = elements.length
  if (i < elementLen) return elements[i]
  const tailThreshold = Math.max(elementLen, len - Math.max(0, rest.length - 1))
  return i >= tailThreshold ? rest[i - tailThreshold + 1] : rest[0]
}

function finishArray(node: Node<ArrayPayload>, input: Elements, len: number): Signal {
  const options = rOptions
  const elementLen = node.p.arrays.elements.length
  const frame = stack[sp - 1]
  if (node.p.arrays.rest.length === 0 && len > elementLen) {
    for (let i = elementLen; i < len; i++) {
      const issue = new SchemaIssue.Pointer([i], new SchemaIssue.UnexpectedKey(node.ast, input[i], options))
      if (options.errors !== "all") {
        pop()
        return failIssue(new SchemaIssue.Composite(node.ast, [issue], input, options))
      }
      add(frame, issue)
    }
  }
  const out = frame.out
  const issues = frame.acc
  pop()
  if (issues) return failIssue(new SchemaIssue.Composite(node.ast, issues, input, options))
  return complete(node, input, out === undefined ? input : out)
}

function resumeArray(frame: Frame<ArrayPayload, Elements, Array<unknown> | undefined>): Step {
  const node = frame.node
  const i = frame.i
  const len = frame.j
  if (rStatus === OK) {
    const value = rValue
    if (value !== InternalParser.missing) {
      if (frame.out !== undefined) frame.out[i] = value
    } else {
      const child = elementAt(node.p, i, len).ast
      if (!child.context?.isOptional) {
        const terminal = missingKey(frame, i, child)
        if (terminal !== undefined) return terminal
      }
    }
  } else {
    const terminal = keyFailure(frame, i)
    if (terminal !== undefined) return terminal
  }
  frame.i = i + 1
  return element(node, frame.input, i + 1, len)
}

const arrayFrame: FrameKind<ArrayPayload, Elements, Array<unknown> | undefined> = {
  resume: resumeArray,
  copy: (out) => out === undefined ? out : out.slice()
}

interface UnionPayload {
  readonly union: SchemaAST.Union
  readonly resolver: Resolver
  readonly candidates: (types: ReadonlyArray<SchemaAST.AST>) => SchemaAST.CandidateIndex
  readonly members: Array<Node<unknown>>
  index: SchemaAST.CandidateIndex | undefined
  readonly oneOf: boolean
}

function member(p: UnionPayload, i: number): Node<unknown> {
  return p.members[i] ??= p.resolver.node(p.union.types[i])
}

function enterUnion(node: Node<UnionPayload>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  const p = node.p
  const candidates = (p.index ??= p.candidates(p.union.types))(input, false)
  if (candidates.length === 0) {
    return failIssue(new SchemaIssue.AnyOf(node.p.union, [], input, rOptions))
  }
  if (candidates.length === 1) {
    push(unionSingleFrame, node, input, undefined, 0, 0, 0)
    return enterChild(member(p, candidates[0]), input)
  }
  push(unionFrame, node, input, candidates, 0, -1, 0)
  return enterChild(member(p, candidates[0]), input)
}

const unionKind: Kind<UnionPayload> = { enter: enterUnion }

const unionSingleFrame: FrameKind<UnionPayload, unknown, undefined> = {
  resume(frame) {
    const node = frame.node
    const input = frame.input
    pop()
    if (rStatus === OK) return complete(node, input, rValue)
    const issue = schemaIssue()
    if (issue === undefined) return DONE
    return failIssue(new SchemaIssue.AnyOf(node.p.union, [issue], input, rOptions))
  },
  copy: identity
}

function resumeUnion(frame: Frame<UnionPayload, unknown, ReadonlyArray<number>>): Step {
  const node = frame.node
  const input = frame.input
  const options = rOptions
  const candidates = frame.out
  const position = candidates[frame.i]
  if (rStatus === OK) {
    if (frame.j >= 0) {
      const types = node.p.union.types
      const successes = [types[frame.j], types[position]]
      pop()
      return failIssue(new SchemaIssue.OneOf(node.p.union, successes, input, options))
    }
    if (!node.p.oneOf) {
      pop()
      return complete(node, input, rValue)
    }
    frame.value = rValue
    frame.j = position
  } else {
    const issue = schemaIssue()
    if (issue === undefined) {
      pop()
      return DONE
    }
    add(frame, issue)
  }
  const next = frame.i + 1
  if (next < candidates.length) {
    frame.i = next
    return enterChild(member(node.p, candidates[next]), input)
  }
  const found = frame.j >= 0
  const value = frame.value
  const issues = frame.acc
  pop()
  if (found) return complete(node, input, value)
  return failIssue(new SchemaIssue.AnyOf(node.p.union, issues ?? [], input, options))
}

const unionFrame: FrameKind<UnionPayload, unknown, ReadonlyArray<number>> = {
  resume: resumeUnion,
  copy: identity
}

interface SuspendPayload {
  readonly thunk: () => SchemaAST.AST
  readonly resolver: Resolver
  target: Node<unknown> | undefined
}

function enterSuspend(node: Node<SuspendPayload>, input: unknown): Step {
  const p = node.p
  return enterChild(p.target ?? resolveTarget(p), input)
}

const suspendKind: Kind<SuspendPayload> = { enter: enterSuspend }

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

function enterDeclaration(node: Node<DeclarationPayload>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
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

const declarationKind: Kind<DeclarationPayload> = { enter: enterDeclaration }

function enterTemplate(node: Node<Node<unknown>>, input: unknown): Step {
  if (input === InternalParser.missing) return succeed(input)
  push(templateFrame, node, input, undefined, 0, 0, 0)
  return enterChild(node.p, input)
}

const templateKind: Kind<Node<unknown>> = { enter: enterTemplate }

const templateFrame: FrameKind<Node<unknown>, unknown, undefined> = {
  resume(frame) {
    const node = frame.node
    const input = frame.input
    pop()
    if (rStatus === OK) return complete(node, input, input)
    if (rStatus === ISSUE && rIssue !== undefined) {
      return failIssue(new SchemaIssue.Composite(node.ast, [rIssue], input, rOptions))
    }
    const error = findError(rCause)
    if (error._tag === "Failure") return DONE
    return failIssue(new SchemaIssue.Composite(node.ast, [error.success], input, rOptions))
  },
  copy: identity
}

type Getter = SchemaGetter.Getter<unknown, unknown, unknown>

interface LinkPayload {
  readonly steps: ReadonlyArray<Getter>
  readonly links: SchemaAST.Encoding
  readonly resolver: Resolver
  parsers: ReadonlyArray<Node<unknown>> | undefined
  readonly local: Node<unknown>
}

function linkParsers(p: LinkPayload): ReadonlyArray<Node<unknown>> {
  return p.parsers ?? resolveLinkParsers(p)
}

function resolveLinkParsers(p: LinkPayload): ReadonlyArray<Node<unknown>> {
  const resolver = p.resolver
  return p.parsers = p.links.map((link) => resolver.node(link.to))
}

function enterLink(node: Node<LinkPayload>, input: unknown): Step {
  const parsers = linkParsers(node.p)
  const last = parsers.length - 1
  push(linkParseFrame, node, input, undefined, last, 0, 0)
  return enterChild(parsers[last], input)
}

const linkKind: Kind<LinkPayload> = { enter: enterLink }

function transformAt(frame: Frame<LinkPayload, unknown, undefined>, i: number): Step {
  if (rStatus !== OK) return afterStep(frame, i)
  const getter = frame.node.p.steps[i]
  const value = rValue
  switch (getter._tag) {
    case "Passthrough":
      return afterStep(frame, i)
    case "Transform":
      if (value !== InternalParser.missing) succeed(getter.transform(value))
      return afterStep(frame, i)
    case "TransformOptional":
      deliver(InternalParser.fromOptionExit(getter.transform(InternalParser.toOption(value))), value)
      return afterStep(frame, i)
    case "TransformEffect": {
      if (value === InternalParser.missing) return afterStep(frame, i)
      const effect = getter.transform(value, rOptions)
      if (effectIsExit(effect)) {
        deliver(effect, value)
        return afterStep(frame, i)
      }
      frame.kind = linkEffectFrame
      return suspendOn(effect)
    }
    case "TransformOptionalEffect": {
      const effect = getter.transform(InternalParser.toOption(value), rOptions)
      if (effectIsExit(effect)) {
        if (effect._tag === "Failure") failCause(effect.cause)
        else deliver(InternalParser.fromOptionExit(effect.value), value)
        return afterStep(frame, i)
      }
      frame.kind = linkEffectFrame
      return suspendOn(flatMap(effect, InternalParser.fromOptionExit))
    }
  }
}

function afterStep(frame: Frame<LinkPayload, unknown, undefined>, i: number): Step {
  const node = frame.node
  if (i !== 0) {
    frame.i = i - 1
    if (rStatus === OK) {
      frame.kind = linkParseFrame
      return enterChild(linkParsers(node.p)[i - 1], rValue)
    }
    return transformAt(frame, i - 1)
  }
  if (rStatus === OK) {
    frame.kind = linkLocalFrame
    return enterChild(node.p.local, rValue)
  }
  frame.kind = linkWrapFrame
  return suspendOn(wrapEncoding(failureExit(), node.ast, frame.input, rOptions))
}

function wrapEncoding(
  failure: Exit.Exit<never, Issue>,
  ast: SchemaAST.AST,
  input: unknown,
  options: SchemaAST.ParseOptions
): Pending {
  return catchCause(
    failure,
    (cause) => failCauseSync(() => causeMap(cause, (issue) => new SchemaIssue.Encoding(ast, issue, input, options)))
  )
}

const linkParseFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(frame) {
    return transformAt(frame, frame.i)
  },
  copy: identity
}

const linkEffectFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume(frame) {
    return afterStep(frame, frame.i)
  },
  copy: identity
}

const linkLocalFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume() {
    pop()
    return DONE
  },
  copy: identity
}

const linkWrapFrame: FrameKind<LinkPayload, unknown, undefined> = {
  resume() {
    pop()
    return DONE
  },
  copy: identity
}
