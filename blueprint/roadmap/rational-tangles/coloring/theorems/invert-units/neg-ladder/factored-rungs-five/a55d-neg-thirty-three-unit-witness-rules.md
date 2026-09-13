---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtyThree_witness_rules
proof: formalized
---

# Negative thirty-three-unit witness rule preliminaries

Arc equations for the thirty-three-unit witness coloring
`sharpColAddNegThirtyThree`: the conjunction of the thirty-three switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-thirty-three existence
projects past the 200 limit (the thirty-three one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~186
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-three-unit invert-add witness coloring](a55c-neg-thirty-three-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
