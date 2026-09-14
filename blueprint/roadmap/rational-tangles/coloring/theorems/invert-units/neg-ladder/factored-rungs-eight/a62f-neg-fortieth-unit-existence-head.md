---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortieth_existence_head
proof: formalized
---

# Negative forty-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-unit
witness coloring `sharpColAddNegFortieth`: the `hcs`-list equation
(a single `decide` fixes the forty switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-38,-37,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~217+ at this rung depth, holding this head here keeps the
existence at ~99 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-unit invert-add witness coloring](a62c-neg-fortieth-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
