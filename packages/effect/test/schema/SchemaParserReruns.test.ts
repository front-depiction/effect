import { describe, it } from "@effect/vitest"
import { assertTrue, deepStrictEqual, strictEqual } from "@effect/vitest/utils"
import { Effect, Exit, Schema, SchemaGetter, SchemaIssue, SchemaParser } from "effect"

const format = (exit: Exit.Exit<unknown, SchemaIssue.Issue>) =>
  Exit.isSuccess(exit)
    ? `ok ${JSON.stringify(exit.value)}`
    : exit.cause.reasons.map((r) =>
      r._tag === "Fail"
        ? SchemaIssue.defaultFormatter(r.error)
        : r._tag === "Die"
        ? `Die ${String((r.defect as Error)?.message)}`
        : r._tag
    ).join("|")

const suspended = (message: string) =>
  Schema.String.pipe(Schema.decodeTo(Schema.String, {
    decode: SchemaGetter.transformEffect((s: string) =>
      Effect.suspend(() =>
        s.startsWith("boom") ? Effect.fail(new SchemaIssue.InvalidValue({ message })) : Effect.succeed(s)
      )
    ),
    encode: SchemaGetter.passthrough()
  }))

const throwingGetter = (base: object, key: string) =>
  Object.defineProperty({ ...base }, key, {
    enumerable: true,
    get() {
      throw new Error(`getter ${key}`)
    }
  })

describe("SchemaParser reruns and root defects", () => {
  it.effect("re-running a decode Effect under errors: all yields the same issues and leaves earlier issues intact", () =>
    Effect.gen(function*() {
      const schema = Schema.Struct({ a: Schema.String, e: suspended("e"), b: Schema.Number })
      const decode = SchemaParser.decodeUnknownEffect(schema)({ a: 1, e: "boom", b: "x" }, { errors: "all" })
      const first = yield* Effect.exit(decode)
      const firstText = format(first)
      const second = yield* Effect.exit(decode)
      strictEqual(format(second), firstText)
      strictEqual(format(first), firstText)
    }))

  it("a throwing discriminant getter in a tagged union is a Die, not a synchronous throw", () => {
    const schema = Schema.Union([
      Schema.Struct({ _tag: Schema.Literal("A"), a: Schema.String }),
      Schema.Struct({ _tag: Schema.Literal("B"), b: Schema.Number })
    ])
    let exit: Exit.Exit<unknown, SchemaIssue.Issue> | undefined
    let thrown: unknown
    try {
      exit = SchemaParser.decodeUnknownExit(schema)(throwingGetter({}, "_tag"))
    } catch (e) {
      thrown = e
    }
    strictEqual(thrown, undefined)
    strictEqual(exit && format(exit), "Die getter _tag")
  })

  it.effect("re-running a oneOf union decode with an effectful member succeeds both times", () =>
    Effect.gen(function*() {
      const schema = Schema.Union([suspended("o"), Schema.String.check(Schema.isMinLength(5))], { mode: "oneOf" })
      const decode = SchemaParser.decodeUnknownEffect(schema)("x")
      strictEqual(format(yield* Effect.exit(decode)), `ok "x"`)
      strictEqual(format(yield* Effect.exit(decode)), `ok "x"`)
    }))

  it.effect("re-running a union decode with effectful candidates does not duplicate or mutate issues", () =>
    Effect.gen(function*() {
      const schema = Schema.Union([suspended("A"), suspended("B")])
      const decode = SchemaParser.decodeUnknownEffect(schema)("boom")
      const first = yield* Effect.exit(decode)
      const firstText = format(first)
      const second = yield* Effect.exit(decode)
      strictEqual(format(second), firstText)
      strictEqual(format(first), firstText)
    }))

  it.effect("re-running a struct decode with a suspending field does not mutate the previously returned value", () =>
    Effect.gen(function*() {
      let n = 0
      const counter = Schema.String.pipe(Schema.decodeTo(Schema.String, {
        decode: SchemaGetter.transformEffect((s: string) => Effect.sync(() => `${s}${++n}`)),
        encode: SchemaGetter.passthrough()
      }))
      const decode = SchemaParser.decodeUnknownEffect(Schema.Struct({ e: counter }))({ e: "v" })
      const first = yield* decode
      deepStrictEqual(first, { e: "v1" })
      const second = yield* decode
      deepStrictEqual(second, { e: "v2" })
      deepStrictEqual(first, { e: "v1" })
      assertTrue(first !== second)
    }))
})
