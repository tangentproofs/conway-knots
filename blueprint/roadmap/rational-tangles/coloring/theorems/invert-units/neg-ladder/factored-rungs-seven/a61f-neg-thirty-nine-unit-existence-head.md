---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtyNine_existence_head
proof: formalized
---

# Negative thirty-nine-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the thirty-nine-unit
witness coloring `sharpColAddNegThirtyNine`: the `hcs`-list equation
(a single `decide` fixes the thirty-nine switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-37,-36,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~212+ at this rung depth, holding this head here keeps the
existence at ~96 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative thirty-nine-unit invert-add witness coloring](a61c-neg-thirty-nine-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
