---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtyFive_witness_rules
proof: formalized
---

# Negative thirty-five-unit witness rule preliminaries

Arc equations for the thirty-five-unit witness coloring
`sharpColAddNegThirtyFive`: the conjunction of the thirty-five switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-thirty-five existence
projects past the 200 limit (the thirty-five one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~196
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-five-unit invert-add witness coloring](a57c-neg-thirty-five-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
