---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyThird_witness_value
proof: formalized
---

# Negative forty-three-unit witness-value computation

Matrix-side value computation for the forty-three-unit witness matrix
`⟨-41,-40,2,3⟩` (identified by the existence-head `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/43` (the `-1/43`-to-`-1/43`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~232+, holding this tail here plus the
crossing-list/matrix head in its own preliminary keeps the existence at ~102 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
