import { assert, describe, it } from "@effect/vitest"
import { Effect, Exit, Schema, SchemaGetter, SchemaParser } from "effect"

describe("Schema kinds", () => {
  it("Literal.transform keeps the checks of its receiver", () => {
    const schema = Schema.Literal("a").check(Schema.makeFilter((s: string) => s.length > 5 || "too short"))
      .transform("b")
    assert.isTrue(Exit.isFailure(SchemaParser.decodeUnknownExit(schema)("a")))
  })

  it("Literal.transform keeps the annotations of its receiver", () => {
    const schema = Schema.Literal("a").annotate({ description: "letter a" }).transform("b")
    assert.strictEqual(schema.ast.encoding?.[0].to.annotations?.description, "letter a")
  })

  it("rebuilt schemas keep their kind methods", () => {
    const struct = Schema.Struct({ a: Schema.String }).annotate({ title: "t" })
    assert.deepStrictEqual(Object.keys(struct.mapFields((fields) => ({ ...fields, b: Schema.Number })).fields), [
      "a",
      "b"
    ])
    const union = Schema.Union([Schema.String]).check(Schema.makeFilter(() => true))
    assert.strictEqual(union.mapMembers((members) => [...members, Schema.Number]).members.length, 2)
    const literals = Schema.Literals(["a", "b"]).annotate({ title: "t" })
    assert.deepStrictEqual(literals.pick(["a"]).literals, ["a"])
  })

  it("a Class copies a __proto__ field as its own data", () => {
    class A extends Schema.Class<A>("A")({ ["__proto__"]: Schema.String, a: Schema.Number }) {}
    const decoded = SchemaParser.decodeUnknownSync(A)(JSON.parse(`{"__proto__":"x","a":1}`))
    assert.isTrue(Object.hasOwn(decoded, "__proto__"))
    assert.strictEqual(Object.getPrototypeOf(decoded), A.prototype)
    assert.deepStrictEqual(Object.keys(new A(JSON.parse(`{"__proto__":"y","a":2}`))), ["__proto__", "a"])
  })

  it("a user constructor in an extend chain receives the forwarded options", () => {
    const seen: Array<unknown> = []
    class A extends Schema.Class<A>("A")({ a: Schema.String }) {
      constructor(input: { readonly a: string }, options?: Schema.MakeOptions) {
        seen.push(options?.disableChecks)
        super(input, options)
      }
    }
    class B extends A.extend<B>("B")({ b: Schema.Number }) {}
    const b = new B({ a: "a", b: 1 })
    assert.deepStrictEqual(seen, [true])
    assert.deepStrictEqual({ ...b }, { a: "a", b: 1 })
  })

  it("decoding a Class runs its constructor once without validating the struct again", () => {
    let calls = 0
    class A extends Schema.Class<A>("A")({ a: Schema.String.check(Schema.makeFilter(() => (calls++, true))) }) {}
    SchemaParser.decodeUnknownSync(A)({ a: "x" })
    assert.strictEqual(calls, 1)
  })

  it("a struct keeps every own field key in own-key order", () => {
    const sym = Symbol("s")
    const fields = { b: Schema.String, 2: Schema.String, a: Schema.String, [sym]: Schema.String, 1: Schema.String }
    Object.defineProperty(fields, "hidden", { value: Schema.String, enumerable: false })
    const ast = Schema.Struct(fields).ast
    assert.deepStrictEqual(ast.propertySignatures.map((ps) => ps.name), Reflect.ownKeys(fields))
  })

  it("a Class accepts an already validated value only for the class it was issued to", () => {
    let captured: Schema.MakeOptions | undefined
    class A extends Schema.Class<A>("A")({ a: Schema.String }) {
      constructor(input: { readonly a: string }, options?: Schema.MakeOptions) {
        captured ??= options
        super(input, options)
      }
    }
    class B extends Schema.Class<B>("B")({ b: Schema.Number }) {}
    SchemaParser.decodeUnknownSync(A)({ a: "x" })
    assert.deepStrictEqual({ ...new B({ b: 1 }, captured) }, { b: 1 })
  })

  it("a decode nested in a filter leaves the outer run's options unchanged", () => {
    const inner = SchemaParser.decodeUnknownSync(Schema.String)
    const nested = Schema.Number.check(Schema.makeFilter((n: number) => (inner("x"), n > 0) || "not positive"))
    const schema = Schema.Struct({ a: nested, b: Schema.String, c: Schema.String })
    const exit = SchemaParser.decodeUnknownExit(schema)({ a: 1, b: 1, c: 1 }, { errors: "all" })
    assert.isTrue(Exit.isFailure(exit))
    if (Exit.isFailure(exit)) {
      const issue = exit.cause.reasons[0]
      assert.isTrue(issue._tag === "Fail" && issue.error._tag === "Composite" && issue.error.issues.length === 2)
    }
  })

  it.effect("a new run of a suspended decode observes its input again", () =>
    Effect.gen(function*() {
      let reads = 0
      const input = {
        get a() {
          reads++
          return "a"
        },
        b: "b"
      }
      const slow = Schema.String.pipe(
        Schema.decodeTo(Schema.String, {
          decode: SchemaGetter.transformEffect((s: string) => Effect.suspend(() => Effect.succeed(s))),
          encode: SchemaGetter.transform((s: string) => s)
        })
      )
      const decode = SchemaParser.decodeUnknownEffect(Schema.Struct({ a: Schema.String, b: slow }))(input)
      yield* decode
      const afterFirst = reads
      yield* decode
      assert.strictEqual(afterFirst, 1)
      assert.strictEqual(reads, 2)
    }))
})
