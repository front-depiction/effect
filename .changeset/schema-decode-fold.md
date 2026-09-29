---
"effect": patch
---

Decode Schema values with one fold over the schema instead of a closure per node. Deeply nested and recursive values no longer overflow the stack, throwing user callbacks become defects instead of escaping a synchronous decode, re-running a decode effect no longer shares state with an earlier run, and decoding allocates less.
