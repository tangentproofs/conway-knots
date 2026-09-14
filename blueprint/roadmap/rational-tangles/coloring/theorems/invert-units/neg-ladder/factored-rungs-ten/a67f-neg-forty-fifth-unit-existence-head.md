---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFifth_existence_head
proof: formalized
---

# Negative forty-five-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-five-unit
witness coloring `sharpColAddNegFortyFifth`: the `hcs`-list equation
(a single `decide` fixes the forty-five switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-43,-42,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~242+ at this rung depth, holding this head here keeps the
existence at ~104 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-five-unit invert-add witness coloring](a67c-neg-forty-fifth-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
