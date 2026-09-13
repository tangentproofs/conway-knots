---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtySeven_witness_rules
proof: formalized
---

# Negative thirty-seven-unit witness rule preliminaries

Arc equations for the thirty-seven-unit witness coloring
`sharpColAddNegThirtySeven`: the conjunction of the thirty-seven switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-thirty-seven existence
projects past the 200 limit (the thirty-seven one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~197
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-seven-unit invert-add witness coloring](a59c-neg-thirty-seven-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
