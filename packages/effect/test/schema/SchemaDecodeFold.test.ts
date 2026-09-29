import { describe, it } from "@effect/vitest"
import { assertTrue, deepStrictEqual, strictEqual } from "@effect/vitest/utils"
import { Effect, Exit, Fiber, Schema, SchemaGetter, SchemaIssue, SchemaParser } from "effect"

const format = (exit: Exit.Exit<unknown, SchemaIssue.Issue>) =>
  Exit.isSuccess(exit)
    ? `ok ${JSON.stringify(exit.value)}`
    : exit.cause.reasons.map((r) =>
      r._tag === "Fail"
        ? SchemaIssue.defaultFormatter(r.error)
        : r._tag === "Die"
        ? `Die ${r.defect instanceof Error ? r.defect.message : String(r.defect)}`
        : r._tag
    ).join("|")

const log: Array<string> = []

const later = (name: string) =>
  Schema.String.pipe(Schema.decodeTo(Schema.String, {
    decode: SchemaGetter.transformEffect((s: string) =>
      Effect.suspend(() => {
        log.push(`${name}:${s}`)
        return s.startsWith("bad")
          ? Effect.fail(new SchemaIssue.InvalidValue(s, { message: name }))
          : Effect.succeed(s + "!")
      })
    ),
    encode: SchemaGetter.passthrough()
  }))

const run = <A>(effect: Effect.Effect<A, SchemaIssue.Issue>) => Effect.runSync(Effect.exit(effect))

describe("spill: a suspension at every position", () => {
  it("first, middle and last key of a struct", () => {
    for (const at of ["a", "b", "c"] as const) {
      const fields = { a: Schema.String, b: Schema.String, c: Schema.String }
      const schema = Schema.Struct({ ...fields, [at]: later(at) })
      const exit = run(SchemaParser.decodeUnknownEffect(schema)({ a: "x", b: "y", c: "z" }))
      assertTrue(Exit.isSuccess(exit))
      deepStrictEqual(Object.keys(exit.value), ["a", "b", "c"])
      strictEqual((exit.value as Record<string, string>)[at].endsWith("!"), true)
    }
  })

  it("an array element, a union candidate and a nested position three deep", () => {
    deepStrictEqual(
      format(run(SchemaParser.decodeUnknownEffect(Schema.Array(later("e")))(["p", "q", "r"]))),
      `ok ["p!","q!","r!"]`
    )
    deepStrictEqual(
      format(run(SchemaParser.decodeUnknownEffect(Schema.Union([Schema.Number, later("u")]))("s"))),
      `ok "s!"`
    )
    const deep = Schema.Struct({
      x: Schema.Array(Schema.Struct({ y: later("d"), z: Schema.Number })),
      w: Schema.String
    })
    deepStrictEqual(
      format(run(SchemaParser.decodeUnknownEffect(deep)({ x: [{ y: "1", z: 1 }, { y: "2", z: 2 }], w: "w" }))),
      `ok {"x":[{"y":"1!","z":1},{"y":"2!","z":2}],"w":"w"}`
    )
  })
})

describe("spill: errors all accumulates across a spill, in order", () => {
  it("issues before and after the suspended key keep key order", () => {
    const schema = Schema.Struct({ a: Schema.Number, b: later("b"), c: Schema.Number, d: later("d") })
    const exit = run(
      SchemaParser.decodeUnknownEffect(schema)({ a: "1", b: "bad1", c: "2", d: "bad2" }, { errors: "all" })
    )
    assertTrue(Exit.isFailure(exit))
    const issue = exit.cause.reasons[0]
    assertTrue(issue._tag === "Fail" && issue.error._tag === "Composite")
    if (issue._tag === "Fail" && issue.error._tag === "Composite") {
      deepStrictEqual(
        issue.error.issues.map((i) => i._tag === "Pointer" ? i.path.join(".") : i._tag),
        ["a", "b", "c", "d"]
      )
    }
  })
})

describe("spill: a suspended description run twice", () => {
  it("gives identical, independent results", () => {
    const schema = Schema.Struct({ a: Schema.String, b: later("b"), c: Schema.Array(later("c")) })
    const effect = SchemaParser.decodeUnknownEffect(schema)({ a: "x", b: "y", c: ["p", "q"] })
    const r1 = run(effect)
    const r2 = run(effect)
    assertTrue(Exit.isSuccess(r1) && Exit.isSuccess(r2))
    if (Exit.isSuccess(r1) && Exit.isSuccess(r2)) {
      deepStrictEqual(r1.value, r2.value)
      assertTrue(r1.value !== r2.value)
      assertTrue(r1.value.c !== r2.value.c)
    }
  })
})

describe("spill: interruption while suspended", () => {
  it.effect("runs the finalizer, and the next run starts clean with its boundary intact", () =>
    Effect.gen(function*() {
      let finalized = 0
      const slow = Schema.String.pipe(Schema.decodeTo(Schema.String, {
        decode: SchemaGetter.transformEffect((s: string) =>
          Effect.sleep("1 hour").pipe(Effect.as(s), Effect.onInterrupt(() => Effect.sync(() => finalized++)))
        ),
        encode: SchemaGetter.passthrough()
      }))
      const schema = Schema.Struct({ a: Schema.String, b: Schema.Array(Schema.Struct({ s: slow })), c: Schema.String })
      const fiber = yield* Effect.forkChild(
        SchemaParser.decodeUnknownEffect(schema)({ a: "x", b: [{ s: "1" }], c: "z" })
      )
      yield* Effect.yieldNow
      yield* Fiber.interrupt(fiber)
      strictEqual(finalized, 1)
      const boom = Schema.Struct({
        a: Schema.String.check(Schema.makeFilter(() => {
          throw new Error("boom")
        }))
      })
      strictEqual(format(SchemaParser.decodeUnknownExit(boom)({ a: "x" })), "Die boom")
      strictEqual(
        format(SchemaParser.decodeUnknownExit(Schema.Struct({ a: Schema.Array(Schema.Number) }))({ a: [1, 2] })),
        `ok {"a":[1,2]}`
      )
    }))
})

describe("spill: the depth budget alone, with no Effect", () => {
  it("decodes chains around the budget and far beyond it", () => {
    for (const depth of [255, 256, 257, 639, 640, 641, 1279, 1280, 1281, 5000]) {
      let schema: Schema.Codec<unknown> = Schema.String
      let value: unknown = "x"
      let tuple: Schema.Codec<unknown> = Schema.Number
      let list: unknown = 1
      for (let i = 0; i < depth; i++) {
        schema = Schema.Struct({ [`k${i}`]: schema, [`n${i}`]: Schema.Literal(i) })
        value = { [`k${i}`]: value, [`n${i}`]: i }
        tuple = Schema.Tuple([tuple, Schema.Literal(i)])
        list = [list, i]
      }
      strictEqual(format(SchemaParser.decodeUnknownExit(schema)(value)), `ok ${JSON.stringify(value)}`)
      strictEqual(format(SchemaParser.decodeUnknownExit(tuple)(list)), `ok ${JSON.stringify(list)}`)
    }
  })

  it("keeps issue paths across a depth spill", () => {
    let schema: Schema.Codec<unknown> = Schema.String
    let value: unknown = 1
    for (let i = 0; i < 600; i++) {
      schema = Schema.Struct({ [`v${i}`]: schema })
      value = { [`v${i}`]: value }
    }
    const exit = SchemaParser.decodeUnknownExit(schema)(value)
    assertTrue(Exit.isFailure(exit))
    const reason = exit.cause.reasons[0]
    let depth = 0
    const path: Array<PropertyKey> = []
    let issue = reason._tag === "Fail" ? reason.error : undefined
    while (issue !== undefined && issue._tag === "Composite") {
      const next = issue.issues[0]
      if (next._tag !== "Pointer") break
      depth++
      path.push(...next.path)
      issue = next.issue
    }
    strictEqual(depth, 600)
    deepStrictEqual(path, Array.from({ length: 600 }, (_, i) => `v${599 - i}`))
    strictEqual(issue?._tag, "InvalidType")
  })
})
