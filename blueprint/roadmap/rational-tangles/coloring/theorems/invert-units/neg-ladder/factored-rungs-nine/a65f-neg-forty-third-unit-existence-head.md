---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyThird_existence_head
proof: formalized
---

# Negative forty-three-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-three-unit
witness coloring `sharpColAddNegFortyThird`: the `hcs`-list equation
(a single `decide` fixes the forty-three switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-41,-40,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~232+ at this rung depth, holding this head here keeps the
existence at ~102 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-three-unit invert-add witness coloring](a65c-neg-forty-third-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
