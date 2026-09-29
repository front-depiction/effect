import * as Pipeable from "../../Pipeable.ts"
import type * as Schema from "../../Schema.ts"
import * as SchemaAST from "../../SchemaAST.ts"
import * as SchemaParser from "../../SchemaParser.ts"

/** @internal */
export const TypeId = "~effect/Schema/Schema"

const RebuildOptions = Symbol()

const Kind = Symbol()

interface Rebuildable {
  readonly [Kind]?: object | undefined
  readonly [RebuildOptions]?: object | undefined
}

const SchemaProto = {
  [TypeId]: TypeId,
  get make() {
    const value = SchemaParser.make(this as any)
    Object.defineProperty(this, "make", { value, enumerable: true })
    return value
  },
  get makeEffect() {
    const value = SchemaParser.makeEffect(this as any)
    Object.defineProperty(this, "makeEffect", { value, enumerable: true })
    return value
  },
  get makeOption() {
    const value = SchemaParser.makeOption(this as any)
    Object.defineProperty(this, "makeOption", { value, enumerable: true })
    return value
  },
  pipe() {
    return Pipeable.pipeArguments(this, arguments)
  },
  annotate(this: Schema.Top, annotations: Schema.Annotations.Annotations) {
    return this.rebuild(SchemaAST.annotate(this.ast, annotations))
  },
  annotateKey(this: Schema.Top, annotations: Schema.Annotations.Key<unknown>) {
    return this.rebuild(SchemaAST.annotateKey(this.ast, annotations))
  },
  check(this: Schema.Top, ...checks: readonly [SchemaAST.Check<unknown>, ...Array<SchemaAST.Check<unknown>>]) {
    return this.rebuild(SchemaAST.appendChecks(this.ast, checks))
  },
  rebuild(this: Schema.Top & Rebuildable, ast: SchemaAST.AST) {
    return makeKind(this[Kind] ?? SchemaProto, ast, this[RebuildOptions])
  }
}

/** @internal */
export function kind<Members extends object>(members: Members): Members {
  const proto: Members & { [Kind]?: object } = Object.assign(Object.create(SchemaProto), members)
  proto[Kind] = proto
  return proto
}

/** @internal */
export function make<S extends Schema.Constraint>(ast: S["ast"], options?: object): S {
  return makeKind(SchemaProto, ast, options)
}

/** @internal */
export function makeKind<S extends Schema.Constraint>(proto: object, ast: S["ast"], options?: object): S {
  function Schema() {}
  const self = Object.setPrototypeOf(Schema, proto)
  if (
    options &&
    (Object.hasOwn(options, "name") || Object.hasOwn(options, "length") || Object.hasOwn(options, "__proto__"))
  ) {
    Object.defineProperties(self, Object.getOwnPropertyDescriptors({ ...options }))
  } else {
    Object.assign(self, options)
  }
  self[RebuildOptions] = options
  self.ast = ast
  return self
}
