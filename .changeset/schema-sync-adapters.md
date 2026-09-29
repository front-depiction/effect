---
"effect": patch
---

Return decoded values from the synchronous Schema adapters, type guards and constructors without allocating an intermediate `Exit`, and map a failing transformation immediately instead of running it through a fiber.
