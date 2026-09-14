---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortySeventh_existence_head
proof: formalized
---

# Negative forty-seven-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-seven-unit
witness coloring `sharpColAddNegFortySeventh`: the `hcs`-list equation
(a single `decide` fixes the forty-seven switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-45,-44,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~252+ at this rung depth, holding this head here keeps the
existence at ~108 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-seven-unit invert-add witness coloring](a69c-neg-forty-seventh-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
