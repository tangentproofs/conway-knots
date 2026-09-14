---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortieth_witness_value
proof: formalized
---

# Negative forty-unit witness-value computation

Matrix-side value computation for the forty-unit witness matrix
`⟨-38,-37,2,3⟩` (identified by the existence-head `hM`): non-monochrome
(`NotMono` by `decide`) and fraction `-1/40` (the `1/-40`-to-`-1/40`
normalization). Factored from the existence (same witness-rules precedent):
with the flat existence projecting ~217+, holding this tail here plus the
crossing-list/matrix head in its own preliminary keeps the existence at ~99 lines. Carries no `maxRecDepth` override (small literal
matrix computation). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
