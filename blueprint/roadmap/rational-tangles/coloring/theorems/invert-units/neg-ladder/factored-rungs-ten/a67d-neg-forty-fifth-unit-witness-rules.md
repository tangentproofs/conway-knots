---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFifth_witness_rules
proof: formalized
---

# Negative forty-five-unit witness rule preliminaries

Arc equations for the forty-five-unit witness coloring
`sharpColAddNegFortyFifth`: the conjunction of the forty-five switched-crossing
equations (each `W a = W c ∧ W b + W d = 2 * W a` pair discharged by
`decide`), factored into its own node so the existence computation stays
under the span limit. Without this split the rung-forty-five existence
projects past the 200 limit (the forty-five one-line `exact` steps plus the
`hcs`/`hM`/`NotMono`/fraction parts); with the rule discharges living
here, and the `hcs`/`hM` head plus the matrix-side tail factored into
their own preliminaries, the existence node keeps only the head obtain,
the `w`-obtains, the one-line `exact` steps, and the assembly over both
preliminaries (~106 lines). Carries `set_option maxRecDepth 4096`, matching the crossings
preliminaries. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-five-unit invert-add witness coloring](a67c-neg-forty-fifth-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
