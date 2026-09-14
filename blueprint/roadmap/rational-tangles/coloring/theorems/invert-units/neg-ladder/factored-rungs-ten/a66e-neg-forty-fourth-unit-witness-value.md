---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFourth_witness_value
proof: formalized
---

# Negative forty-four-unit witness-value computation

Matrix-side value computation for the forty-four-unit witness matrix
`⟨-42,-41,2,3⟩` (identified by the existence-head `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/44` (the `-1/44`-to-`-1/44`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~237+, holding this tail here plus the
crossing-list/matrix head in its own preliminary keeps the existence at ~104 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
