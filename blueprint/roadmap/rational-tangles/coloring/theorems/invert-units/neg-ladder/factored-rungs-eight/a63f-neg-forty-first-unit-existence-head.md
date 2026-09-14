---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFirst_existence_head
proof: formalized
---

# Negative forty-one-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-one-unit
witness coloring `sharpColAddNegFortyFirst`: the `hcs`-list equation
(a single `decide` fixes the forty-one switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-39,-38,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~222+ at this rung depth, holding this head here keeps the
existence at ~100 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-one-unit invert-add witness coloring](a63c-neg-forty-first-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
