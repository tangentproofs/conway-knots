---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyFifth_witness_value
proof: formalized
---

# Negative forty-five-unit witness-value computation

Matrix-side value computation for the forty-five-unit witness matrix
`⟨-43,-42,2,3⟩` (identified by the existence-head `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/45` (the `-1/45`-to-`-1/45`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~242+, holding this tail here plus the
crossing-list/matrix head in its own preliminary keeps the existence at ~106 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
