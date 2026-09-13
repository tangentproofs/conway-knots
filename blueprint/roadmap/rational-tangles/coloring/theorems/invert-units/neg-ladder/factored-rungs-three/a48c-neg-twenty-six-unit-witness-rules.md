---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegTwentySix_witness_rules
proof: formalized
---

# Negative twenty-six-unit witness rule preliminaries

Arc equations for the twenty-six-unit witness coloring
`sharpColAddNegTwentySix`: the conjunction of the twenty-six switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-twenty-six existence
projects to ~201-203 lines (the twenty-six 3-line `show` blocks plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~150
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-six-unit invert-add witness coloring](a48b-neg-twenty-six-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
