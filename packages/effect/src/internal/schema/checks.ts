import type * as Arr from "../../Array.ts"
import type * as SchemaAST from "../../SchemaAST.ts"
import * as SchemaIssue from "../../SchemaIssue.ts"

/** @internal */
export function collectIssues<T>(
  checks: ReadonlyArray<SchemaAST.Check<T>>,
  value: T,
  issues: Arr.NonEmptyArray<SchemaIssue.Issue> | undefined,
  ast: SchemaAST.AST,
  options: SchemaAST.ParseOptions
): Arr.NonEmptyArray<SchemaIssue.Issue> | undefined {
  for (let i = 0; i < checks.length; i++) {
    const check = checks[i]
    if (check._tag === "FilterGroup") {
      issues = collectIssues(check.checks, value, issues, ast, options)
      if (
        issues &&
        (options.errors !== "all" || (issues[issues.length - 1] as SchemaIssue.Filter).filter.aborted)
      ) {
        return issues
      }
    } else {
      const issue = check.run(value, ast, options)
      if (issue) {
        const filter = new SchemaIssue.Filter(check, issue, value, options)
        if (issues) issues.push(filter)
        else issues = [filter]
        if (options.errors !== "all" || check.aborted) {
          return issues
        }
      }
    }
  }
  return issues
}
