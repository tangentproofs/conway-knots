---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtyEight_existence_head
proof: formalized
---

# Negative thirty-eight-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the thirty-eight-unit
witness coloring `sharpColAddNegThirtyEight`: the `hcs`-list equation
(a single `decide` fixes the thirty-eight switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-36,-35,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~207+ at this rung depth, holding this head here keeps the
existence at ~93 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative thirty-eight-unit invert-add witness coloring](a60c-neg-thirty-eight-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
