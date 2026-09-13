---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegThirtySix_witness_value
proof: formalized
---

# Negative thirty-six-unit witness-value computation

Matrix-side value computation for the thirty-six-unit witness matrix
`⟨-34,-33,2,3⟩` (identified by the existence `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/36` (the `1/-36`-to-`-1/36`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~201, holding this tail here keeps the
existence at ~193 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
