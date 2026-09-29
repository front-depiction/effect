import * as Effect from "../../Effect.ts"
import type { CompiledDecoder, Decode, Is, Make } from "../../schema/SchemaCompiler.ts"
import type * as SchemaAST from "../../SchemaAST.ts"
import type { Parser } from "../../SchemaParser.ts"
import * as Machine from "./machine.ts"
import * as InternalParser from "./parser.ts"

/** @internal */
export const invalid = Symbol()

/** @internal */
export type Resolve = (ast: SchemaAST.AST) => Entry

/** @internal */
export type DecoderSource = Partial<CompiledDecoder>

/** @internal */
export type DecoderOperation = keyof CompiledDecoder

/** @internal */
export type Compile = <K extends DecoderOperation>(
  ast: SchemaAST.AST,
  resolve: Resolve,
  operation: K
) => CompiledDecoder[K] | undefined

/** @internal */
export type CompileSource = (ast: SchemaAST.AST, resolve: Resolve) => DecoderSource | undefined

/** @internal */
export type Compiled = DecoderSource | Compile

const cache = new WeakMap<SchemaAST.AST, Entry>()
let compiler: CompileSource | undefined

/** @internal */
export let compilerAdaptersEnabled = false

function activateCompilerAdapters(): void {
  compilerAdaptersEnabled = true
}

function withDefault(ast: SchemaAST.AST, node: Machine.Node<unknown>): Machine.Node<unknown> {
  const value = ast.context?.constructorDefault
  return value === undefined ? node : Machine.defaultNode(ast, value, node)
}

const resolver: Machine.Resolver = {
  node: (ast) => resolve(ast).node,
  field: (ast) => resolve(ast).node,
  make: false
}

const makeResolver: Machine.Resolver = {
  node: (ast) => resolve(ast).makeNode,
  field: (ast) => withDefault(ast, resolve(ast).makeNode),
  make: true
}

/** @internal */
export function lazyResolver(
  resolve: Resolve,
  operation: "parser" | "decodeEffect" | "makeEffect",
  make: boolean
): Machine.Resolver {
  const node = (ast: SchemaAST.AST) => {
    const parser = lazyParser(resolve, ast, operation)
    return Machine.foreign(ast, () => parser)
  }
  return { node, field: make ? (ast) => withDefault(ast, node(ast)) : node, make }
}

/** @internal */
export interface Entry {
  readonly ast: SchemaAST.AST
  readonly compiled?: Compiled | undefined
  readonly resolve?: Resolve | undefined
  readonly is?: Is | undefined
  readonly decode?: Decode | undefined
  readonly make?: Make | undefined
  readonly decodeEffect: Parser
  readonly parser: Parser
  readonly makeEffect: Parser
  readonly node: Machine.Node<unknown>
  readonly makeNode: Machine.Node<unknown>
  readonly rootEffect: Parser
}

class InterpretedEntry implements Entry {
  readonly ast: SchemaAST.AST
  declare private cachedDecodeEffect: Parser | undefined
  declare private cachedMakeEffect: Parser | undefined
  declare private cachedRootEffect: Parser | undefined
  declare private cachedNode: Machine.Node<unknown> | undefined
  declare private cachedMakeNode: Machine.Node<unknown> | undefined

  constructor(ast: SchemaAST.AST) {
    this.ast = ast
  }

  get node(): Machine.Node<unknown> {
    return this.cachedNode ??= Machine.build(this.ast, resolver)
  }

  get decodeEffect(): Parser {
    return this.cachedDecodeEffect ??= (input, options) => Machine.decode(this.node, input, options, false)
  }

  get rootEffect(): Parser {
    return this.cachedRootEffect ??= (input, options) => Machine.decode(this.node, input, options, true)
  }

  get parser(): Parser {
    return this.decodeEffect
  }

  get makeNode(): Machine.Node<unknown> {
    return this.cachedMakeNode ??= Machine.build(this.ast, makeResolver)
  }

  get makeEffect(): Parser {
    return this.cachedMakeEffect ??= (input, options) => Machine.decode(this.makeNode, input, options, false)
  }
}

class CompilerEntry extends InterpretedEntry {
  readonly compiled: Compiled | undefined
  readonly resolve: Resolve

  constructor(ast: SchemaAST.AST, compiled: Compiled | undefined, resolve: Resolve) {
    super(ast)
    this.compiled = compiled
    this.resolve = resolve
  }

  private save<K extends keyof Entry>(key: K, value: Entry[K]): Entry[K] {
    Object.defineProperty(this, key, { value })
    return value
  }

  private operation<K extends DecoderOperation>(key: K): CompiledDecoder[K] | undefined {
    const compiled = this.compiled
    return typeof compiled === "function" ? compiled(this.ast, this.resolve, key) : compiled?.[key]
  }

  override get node(): Machine.Node<unknown> {
    return this.save("node", Machine.foreign(this.ast, () => this.parser))
  }

  override get makeNode(): Machine.Node<unknown> {
    return this.save("makeNode", Machine.foreign(this.ast, () => this.makeEffect))
  }

  override get rootEffect(): Parser {
    return this.parser
  }

  get is(): Is | undefined {
    return this.save("is", this.operation("is"))
  }

  get decode(): Decode | undefined {
    return this.save("decode", this.operation("decode"))
  }

  get make(): Make | undefined {
    return this.save("make", this.operation("make"))
  }

  override get decodeEffect(): Parser {
    return this.save(
      "decodeEffect",
      this.operation("decodeEffect") ??
        Machine.parser(Machine.build(this.ast, lazyResolver(this.resolve, "parser", false)))
    )
  }

  override get parser(): Parser {
    const decode = this.decode
    return decode === undefined
      ? this.decodeEffect
      : this.save("parser", withDecode(decode, () => this.decodeEffect))
  }

  override get makeEffect(): Parser {
    return this.save(
      "makeEffect",
      this.operation("makeEffect") ??
        Machine.parser(Machine.build(this.ast, lazyResolver(this.resolve, "makeEffect", true)))
    )
  }
}

/** @internal */
export function withDecode(fastDecode: Decode, decodeEffect: () => Parser): Parser {
  let detailed: Parser | undefined
  return (input, options) => {
    if (input !== InternalParser.missing) {
      try {
        const value = fastDecode(input, options)
        if (value !== invalid) return value === input ? InternalParser.sameExit : InternalParser.succeed(value)
      } catch (error) {
        return Effect.die(error)
      }
    }
    return (detailed ??= decodeEffect())(input, options)
  }
}

/** @internal */
export function lazyParser(
  resolve: Resolve,
  ast: SchemaAST.AST,
  operation: "parser" | "decodeEffect" | "makeEffect"
): Parser {
  const entry = resolve(ast)
  if (entry.compiled === undefined || Object.hasOwn(entry, operation)) {
    return entry[operation]
  }
  let parser: Parser | undefined
  return (input, options) => (parser ??= entry[operation])(input, options)
}

/** @internal */
export function resolve(ast: SchemaAST.AST): Entry {
  const cached = cache.get(ast)
  if (cached !== undefined) return cached
  const entry = compiler === undefined
    ? new InterpretedEntry(ast)
    : new CompilerEntry(ast, compiler(ast, resolve), resolve)
  cache.set(ast, entry)
  return entry
}

/** @internal */
export function set(ast: SchemaAST.AST, decoder: DecoderSource | undefined, resolveChild: Resolve = resolve): Entry {
  if (decoder !== undefined) activateCompilerAdapters()
  const entry = new CompilerEntry(ast, decoder, resolveChild)
  cache.set(ast, entry)
  return entry
}

/** @internal */
export function setCompiler(
  ast: SchemaAST.AST,
  compile: Compile,
  resolveChild: Resolve = resolve
): Entry {
  activateCompilerAdapters()
  const entry = new CompilerEntry(ast, compile, resolveChild)
  cache.set(ast, entry)
  return entry
}

/** @internal */
export function install(compile: CompileSource): void {
  activateCompilerAdapters()
  compiler = compile
}

/** @internal */
export function enable(ast: SchemaAST.AST, compile: CompileSource): void {
  activateCompilerAdapters()
  const scoped: Resolve = (child) => {
    const cached = cache.get(child)
    return cached !== undefined && (cached.compiled !== undefined || cached.resolve === scoped)
      ? cached
      : set(child, compile(child, scoped), scoped)
  }
  const decoder = compile(ast, scoped)
  const cached = cache.get(ast)
  if (decoder !== undefined || cached?.compiled === undefined) {
    set(ast, decoder, scoped)
  }
}
