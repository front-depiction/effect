import { describe, it } from "@effect/vitest"
import { strictEqual } from "@effect/vitest/utils"
import { Exit, Schema, SchemaIssue, SchemaParser } from "effect"

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

const throwingGetter = (base: object, key: string) =>
  Object.defineProperty({ ...base }, key, {
    enumerable: true,
    get() {
      throw new Error(`getter ${key}`)
    }
  })

describe("SchemaParser defects under excess-property checks", () => {
  it("a throwing excess-key getter under onExcessProperty: error is a Die", () => {
    const schema = Schema.Struct({ a: Schema.String })
    for (const errors of ["first", "all"] as const) {
      const exit = SchemaParser.decodeUnknownExit(schema)(throwingGetter({ a: "x" }, "extra"), {
        onExcessProperty: "error",
        errors
      })
      strictEqual(format(exit), "Die getter extra")
    }
  })

  it("a throwing ownKeys trap under onExcessProperty: error is a Die", () => {
    const schema = Schema.Struct({ a: Schema.String })
    const input = new Proxy({ a: "x" }, {
      ownKeys() {
        throw new Error("ownKeys")
      }
    })
    strictEqual(format(SchemaParser.decodeUnknownExit(schema)(input, { onExcessProperty: "error" })), "Die ownKeys")
  })
})
