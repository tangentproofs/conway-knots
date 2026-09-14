---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtyNine_witness_value
proof: formalized
---

# Negative thirty-nine-unit witness-value computation

Matrix-side value computation for the thirty-nine-unit witness matrix
`⟨-37,-36,2,3⟩` (identified by the existence-head `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/39` (the `1/-39`-to-`-1/39`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~212+, holding this tail here plus the
crossing-list/matrix head in its own preliminary keeps the existence at ~96 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
