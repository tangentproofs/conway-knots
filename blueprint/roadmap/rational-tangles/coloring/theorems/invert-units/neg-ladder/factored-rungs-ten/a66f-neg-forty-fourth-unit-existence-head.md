---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFourth_existence_head
proof: formalized
---

# Negative forty-four-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-four-unit
witness coloring `sharpColAddNegFortyFourth`: the `hcs`-list equation
(a single `decide` fixes the forty-four switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-42,-41,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~237+ at this rung depth, holding this head here keeps the
existence at ~102 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-four-unit invert-add witness coloring](a66c-neg-forty-fourth-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
