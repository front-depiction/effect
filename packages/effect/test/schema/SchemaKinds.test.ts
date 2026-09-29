import { assert, describe, it } from "@effect/vitest"
import { Exit, Schema, SchemaParser } from "effect"

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
})
