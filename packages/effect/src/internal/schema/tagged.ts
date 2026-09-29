/** @internal */
export function tagged<C extends { readonly prototype: object }>(_tag: string, C: C): C {
  Object.assign(C.prototype, { _tag })
  return C
}
