---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegTwentyNine_witness_rules
proof: formalized
---

# Negative twenty-nine-unit witness rule preliminaries

Arc equations for the twenty-nine-unit witness coloring
`sharpColAddNegTwentyNine`: the conjunction of the twenty-nine switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-twenty-nine existence
projects past the 200 limit (the twenty-nine one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, the existence node keeps only the `hcs`-list `decide`, the `hM`
`rfl`, the `NotMono` `decide`, and the fraction normalization (~166
lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-nine-unit invert-add witness coloring](a51c-neg-twenty-nine-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
