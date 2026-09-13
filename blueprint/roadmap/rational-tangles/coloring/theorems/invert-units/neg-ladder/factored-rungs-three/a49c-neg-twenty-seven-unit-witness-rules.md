---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegTwentySeven_witness_rules
proof: formalized
---

# Negative twenty-seven-unit witness rule preliminaries

Arc equations for the twenty-seven-unit witness coloring
`sharpColAddNegTwentySeven`: the conjunction of the twenty-seven switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-twenty-seven existence
projects past the 200 limit (the twenty-seven one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~155
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-seven-unit invert-add witness coloring](a49b-neg-twenty-seven-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
