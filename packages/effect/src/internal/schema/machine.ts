import type * as Arr from "../../Array.ts"
import type * as Cause from "../../Cause.ts"
import type * as Effect from "../../Effect.ts"
import type * as Exit from "../../Exit.ts"
import type * as SchemaAST from "../../SchemaAST.ts"
import * as SchemaIssue from "../../SchemaIssue.ts"
import type { Parser } from "../../SchemaParser.ts"
import { causeDie, causeEmpty, exitFail, exitFailCause, exitSucceed } from "../core.ts"
import { effectIsExit, exit as exitEffect, flatMap, suspend } from "../effect.ts"
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
  const signal = drive(decodeLoop, base, enterChild(node, input), previous, root && node.kind !== foreignKind)
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
  if (ast.indexSignatures.length > 0 || ast.propertySignatures.length > 0) {
    return foreign(ast, () => resolver.whole(ast))
  }
  return node(notNullishKind, ast, undefined)
}

/** @internal */
export function declarationNode(ast: SchemaAST.Declaration, resolver: Resolver): Node<unknown> {
  for (const parameter of ast.typeParameters) resolver.node(parameter)
  return new Node(declarationKind, ast, ast.checks, ast.encodingChecks, { declaration: ast, run: undefined })
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
