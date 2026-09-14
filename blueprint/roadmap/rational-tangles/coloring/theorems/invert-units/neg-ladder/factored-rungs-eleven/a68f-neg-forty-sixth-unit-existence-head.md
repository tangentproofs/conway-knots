---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortySixth_existence_head
proof: formalized
---

# Negative forty-six-unit existence-head preliminary

Crossing-list and tangle-to-matrix bridge for the forty-six-unit
witness coloring `sharpColAddNegFortySixth`: the `hcs`-list equation
(a single `decide` fixes the forty-six switched crossings) and the
`hM` `rfl` identifying the witness matrix `⟨-44,-43,2,3⟩`. Factored from
the existence (same witness-value precedent): with the flat existence
projecting ~247+ at this rung depth, holding this head here keeps the
existence at ~106 lines. Carries `set_option maxRecDepth 16384`,
matching the existence (it holds the former existence `rfl`). Proof part
of the parent topic; see that page for the mathematical context.

## Depends on

- [Negative forty-six-unit invert-add witness coloring](a68c-neg-forty-sixth-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
