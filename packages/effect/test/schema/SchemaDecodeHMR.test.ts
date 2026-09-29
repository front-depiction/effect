import { describe, expect, it, vi } from "vitest"

const SCHEMA_MODULE_PATH = "../../src/Schema.ts"

describe("HMR: a node built by another module copy", () => {
  it("decodes, fails and suspends through the other copy's kinds", async () => {
    const mod1: any = await vi.importActual(SCHEMA_MODULE_PATH)
    const Effect1: any = await vi.importActual("../../src/Effect.ts")
    const SG1: any = await vi.importActual("../../src/SchemaGetter.ts")
    const inner = mod1.Struct({
      a: mod1.String,
      n: mod1.NumberFromString,
      e: mod1.String.pipe(mod1.decodeTo(mod1.String, {
        decode: SG1.transformEffect((s: string) => Effect1.suspend(() => Effect1.succeed(s + "!"))),
        encode: SG1.passthrough()
      }))
    })
    vi.resetModules()
    const schema: any = await vi.importActual(SCHEMA_MODULE_PATH)
    const Effect2: any = await vi.importActual("../../src/Effect.ts")
    const outer = schema.Struct({ rows: schema.Array(inner), k: schema.Number })
    const ok = await Effect2.runPromise(
      Effect2.exit(schema.decodeUnknownEffect(outer)({ rows: [{ a: "x", n: "1", e: "y" }], k: 1 }))
    )
    expect(String(ok)).toBe(`Success({"rows":[{"a":"x","n":1,"e":"y!"}],"k":1})`)
    const bad = schema.decodeUnknownExit(outer)({ rows: [{ a: 1, n: "1", e: "y" }], k: 1 })
    expect(bad._tag).toBe("Failure")
    expect(String(bad)).toContain(`Expected string\n  at ["rows"][0]["a"]`)
    const all = schema.decodeUnknownExit(outer)({ rows: [{ a: 1, n: "1", e: "y" }], k: "z" }, { errors: "all" })
    expect(String(all)).toContain(`at ["rows"][0]["a"]`)
    expect(String(all)).toContain(`at ["k"]`)
  })
})
