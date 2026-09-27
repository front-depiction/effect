/**
 * Runtime helpers used by generated schema modules. This module contains no
 * source generator or dynamic function construction. Generated modules must
 * use the same Effect version as their generator.
 *
 * @stability unstable
 * @since 4.0.0
 */
import * as Effect from "../../Effect.ts"
import type * as Exit from "../../Exit.ts"
import { effectIsExit, exit as exitEffect, flatMap, resolveConcurrency, suspend } from "../../internal/effect.ts"
import { lazyResolver, type Resolve, resolve, setCompiler, withDecode } from "../../internal/schema/compilerRegistry.ts"
import * as Machine from "../../internal/schema/machine.ts"
import * as InternalParser from "../../internal/schema/parser.ts"
import * as SchemaAST from "../../SchemaAST.ts"
import * as SchemaIssue from "../../SchemaIssue.ts"
import type { Parser } from "../../SchemaParser.ts"
import { type Decode, invalid } from "../SchemaCompiler.ts"

type Issue = SchemaIssue.Issue
type Pending = Effect.Effect<unknown, Issue, any>
type ParsedProperty = {
  readonly parser: Parser
  readonly name: PropertyKey
  readonly type: SchemaAST.AST
}
type ObjectParserState = Machine.Accumulator<Record<PropertyKey, unknown>> & {
  readonly ast: SchemaAST.Objects
  readonly out: Record<PropertyKey, unknown>
}
type ArrayParserState = Machine.Accumulator<ReadonlyArray<unknown>> & {
  readonly len: number
  readonly getParser: (tailThreshold: number, index: number) => { readonly ast: SchemaAST.AST; readonly parser: Parser }
  readonly tailThreshold: number
  readonly output: Array<unknown>
}
type StepProperty = (
  state: ObjectParserState,
  property: ParsedProperty,
  exit: Exit.Exit<unknown, Issue>
) => Exit.Exit<void, Issue> | undefined
type StepArray = (
  state: ArrayParserState,
  item: unknown,
  exit: Exit.Exit<unknown, Issue>,
  index: number
) => Exit.Exit<void, Issue> | undefined
type RunArray = (
  state: ArrayParserState,
  input: ReadonlyArray<unknown>,
  index?: number,
  end?: number
) => Effect.Effect<void, Issue, any> | undefined
type GenerateObject = (context: {
  readonly ast: SchemaAST.Objects
  readonly getProperties: () => ReadonlyArray<ParsedProperty>
  readonly fallback: Parser
  readonly resume: (state: ObjectParserState, index: number, pending: Pending) => Pending
  readonly step: StepProperty
}) => Parser
type GenerateArray = (context: {
  readonly getElement: () => Parser
  readonly step: StepArray
  readonly resume: (
    state: ArrayParserState,
    item: unknown,
    index: number,
    pending: Pending,
    end: number
  ) => Effect.Effect<void, Issue, any>
}) => RunArray

const stepProperty: StepProperty = (state, property, exit) =>
  Machine.stepKey(state, state.out, property.name, property.type, exit)

const stepArray: StepArray = (state, item, exit, index) =>
  Machine.stepIndex(state, state.output, index, item, state.getParser(state.tailThreshold, index).ast, exit)

const fieldParser = (plan: Machine.Resolver) => (ast: SchemaAST.AST): Parser => Machine.parser(plan.field(ast))

const makeObjectBase = (
  ast: SchemaAST.Objects,
  plan: Machine.Resolver,
  generate: GenerateObject
): Parser => {
  let properties: Array<ParsedProperty> | undefined
  const field = fieldParser(plan)
  const getProperties = (): Array<ParsedProperty> => {
    if (properties !== undefined) return properties
    const parsers = new Map<SchemaAST.AST, Parser>()
    return properties = ast.propertySignatures.map((property) => {
      let parser = parsers.get(property.type)
      if (parser === undefined) {
        parser = field(property.type)
        parsers.set(property.type, parser)
      }
      return { parser, name: property.name, type: property.type }
    })
  }
  let fallback: Parser | undefined
  const runFallback: Parser = (input, options) =>
    (fallback ??= Machine.parser(Machine.bare(Machine.local(ast, plan))))(input, options)
  let rest: ReturnType<typeof Machine.structResumer> | undefined
  const resume = (state: ObjectParserState, index: number, pending: Pending): Pending => {
    const property = properties![index]
    return flatMap(exitEffect(pending), (exit) => {
      const terminal = stepProperty(state, property, exit)
      if (terminal) return terminal
      return (rest ??= Machine.structResumer(ast, plan))(state.input, state.out, index + 1, state.options)
    })
  }
  return generate({ ast, getProperties, fallback: runFallback, resume, step: stepProperty })
}

const makeArrayBase = (
  ast: SchemaAST.Arrays,
  plan: Machine.Resolver,
  generateArray: GenerateArray
): Parser => {
  let element: { readonly ast: SchemaAST.AST; readonly parser: Parser } | undefined
  const getElement = () => (element ??= {
    ast: ast.rest[0],
    parser: fieldParser(plan)(ast.rest[0])
  })
  let fallback: Parser | undefined
  const runFallback: Parser = (input, options) =>
    (fallback ??= Machine.parser(Machine.bare(Machine.local(ast, plan))))(input, options)
  const run: RunArray = generateArray({
    getElement: () => getElement().parser,
    step: stepArray,
    resume: (state, item, index, pending, end) =>
      flatMap(
        exitEffect(pending),
        (exit) => stepArray(state, item, exit, index) ?? run(state, state.input, index + 1, end) ?? Effect.void
      )
  })
  const finish = (state: ArrayParserState): Pending =>
    state.issues
      ? Effect.fail(new SchemaIssue.Composite(ast, state.issues, state.input, state.options))
      : InternalParser.succeed(state.output)
  const specialized: Parser = (input, options) => {
    try {
      if (input === InternalParser.missing) return InternalParser.succeed(InternalParser.missing)
      if (!Array.isArray(input)) return Effect.fail(new SchemaIssue.InvalidType(ast, input, options))
      const descriptor = getElement()
      const len = input.length
      const state: ArrayParserState = {
        ast,
        getParser: () => descriptor,
        input,
        len,
        tailThreshold: len,
        output: new globalThis.Array(len),
        issues: undefined,
        options
      }
      const effect = run(state, input, 0, len)
      if (effect === undefined) return finish(state)
      if (effectIsExit(effect)) return effect._tag === "Failure" ? effect : finish(state)
      let first = true
      return suspend(() => {
        if (!first) return suspend(() => specialized(input, options))
        first = false
        return flatMap(effect, () => finish(state))
      })
    } catch (error) {
      return Effect.die(error)
    }
  }
  return (input, options) =>
    options.concurrency !== undefined && resolveConcurrency(options.concurrency) !== 1
      ? runFallback(input, options)
      : specialized(input, options)
}

const base = (
  ast: SchemaAST.AST,
  plan: Machine.Resolver,
  generate: GenerateObject | undefined,
  generateArray: GenerateArray | undefined
): Machine.Node<unknown> =>
  ast._tag === "Objects" && generate !== undefined
    ? Machine.checked(ast, () => makeObjectBase(ast, plan, generate))
    : ast._tag === "Arrays" && generateArray !== undefined
    ? Machine.checked(ast, () => makeArrayBase(ast, plan, generateArray))
    : Machine.local(ast, plan)

const hasChecks = (ast: SchemaAST.AST): boolean =>
  ast.checks !== undefined || ("encodingChecks" in ast && ast.encodingChecks !== undefined)

const decode = (
  ast: SchemaAST.AST,
  resolve: Resolve,
  generate?: GenerateObject,
  detailed = false,
  makeDecode?: () => Decode,
  generateArray?: GenerateArray
): Parser => {
  const plan = lazyResolver(resolve, detailed ? "decodeEffect" : "parser", false)
  let local = base(
    ast,
    makeDecode === undefined ? plan : lazyResolver(resolve, "decodeEffect", false),
    generate,
    generateArray
  )
  const links = ast.encoding
  if (makeDecode !== undefined && (links !== undefined || hasChecks(ast))) {
    try {
      const fast = makeDecode()
      const detailedLocal = Machine.parser(local)
      local = Machine.foreign(ast, () => withDecode(fast, () => detailedLocal))
    } catch {
      // Initialization failure selects the local interpreter, without parsing again.
    }
  }
  return Machine.parser(links === undefined ? local : Machine.linkOver(ast, links, local, plan))
}

const make = (
  ast: SchemaAST.AST,
  resolve: Resolve,
  generate?: GenerateObject,
  generateArray?: GenerateArray
): Parser => {
  const plan = lazyResolver(resolve, "makeEffect", true)
  const local = base(ast, plan, generate, generateArray)
  const links = ast.encoding
  return Machine.parser(links === undefined ? local : Machine.linkOver(ast, links, local, plan))
}

const getCheckIssues = (
  ast: SchemaAST.AST,
  value: unknown,
  encoded: boolean,
  options: SchemaAST.ParseOptions
): ReturnType<typeof SchemaAST.collectIssues> => {
  const checks = encoded ? "encodingChecks" in ast ? ast.encodingChecks : undefined : ast.checks
  return !options.disableChecks && checks !== undefined
    ? SchemaAST.collectIssues(checks, value, undefined, ast, options)
    : undefined
}

const check = (
  ast: SchemaAST.AST,
  value: unknown,
  options: SchemaAST.ParseOptions
): Effect.Effect<unknown, SchemaIssue.Issue> => {
  const issues = getCheckIssues(ast, value, false, options)
  return issues === undefined
    ? InternalParser.succeed(value)
    : Effect.fail(new SchemaIssue.Composite(ast, issues, value, options))
}

const hasExcessProperties = (
  ast: SchemaAST.Objects,
  input: Record<PropertyKey, unknown>,
  indexKeys?: ReadonlyArray<ReadonlyArray<PropertyKey>>
): boolean => {
  const covered = new Set<PropertyKey>(
    ast.propertySignatures.map((p) => typeof p.name === "number" ? String(p.name) : p.name)
  )
  if (indexKeys) {
    for (const keys of indexKeys) {
      for (const key of keys) covered.add(key)
    }
  }
  return Reflect.ownKeys(input).some((key) =>
    !covered.has(key) && Object.prototype.propertyIsEnumerable.call(input, key)
  )
}

const invalidType = (ast: SchemaAST.AST, input: unknown, options: SchemaAST.ParseOptions) =>
  Effect.fail(new SchemaIssue.InvalidType(ast, input, options))

const invalidEncoding = (
  ast: SchemaAST.AST & { readonly encoding: SchemaAST.Encoding },
  index: number,
  input: unknown,
  value: unknown,
  options: SchemaAST.ParseOptions
) =>
  index === 0
    ? invalidType(ast, value, options)
    : Machine.wrapEncoding(invalidType(ast.encoding[index - 1].to, value, options), ast, input, options)

/**
 * @internal
 */
export const runtime = {
  decode,
  make,
  resolve,
  setCompiler,
  invalid,
  missing: InternalParser.missing,
  missingExit: InternalParser.missingExit,
  sameExit: InternalParser.sameExit,
  args: InternalParser.args,
  succeed: InternalParser.succeed,
  effectIsExit,
  die: Effect.die,
  invalidType,
  invalidEncoding,
  getCheckIssues,
  check,
  getExpectedKeys: (ast: SchemaAST.Objects) =>
    ast.propertySignatures.map((p) => typeof p.name === "number" ? String(p.name) : p.name),
  hasExcessProperties,
  matchesTemplateLiteral: (ast: SchemaAST.TemplateLiteral, input: unknown, options: SchemaAST.ParseOptions) =>
    typeof input === "string" && ast.matchPart(input, options) !== undefined,
  getCandidateIndex: SchemaAST.getCandidateIndex,
  getIndexSignatureKeys: SchemaAST.getIndexSignatureKeys,
  parameterFromPropertyKey: SchemaAST.parameterFromPropertyKey,
  getConstructorDescriptor: SchemaAST.getConstructorDescriptor,
  defaultParseOptions: SchemaAST.defaultParseOptions
}
