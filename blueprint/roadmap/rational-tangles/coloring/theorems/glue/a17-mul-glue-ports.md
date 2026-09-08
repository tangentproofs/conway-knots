---
declaration: lemma
origin: bridged
statement: formalized
lean: RationalTangles.mulGlue_NW RationalTangles.mulGlue_NE RationalTangles.mulGlue_shift_eq RationalTangles.mulGlue_crossingTangle_congr RationalTangles.mulGlue_shift_unit_le RationalTangles.mul_SE_glue RationalTangles.mul_SW_glue RationalTangles.mul_SE_rename RationalTangles.mul_SW_rename RationalTangles.mul_crossings_append RationalTangles.mul_one_SE RationalTangles.mul_one_SW RationalTangles.mul_one_crossings RationalTangles.mul_negOne_SE RationalTangles.mul_negOne_SW RationalTangles.mul_negOne_crossings RationalTangles.mul_crossingTangle_SE RationalTangles.mul_crossingTangle_SW RationalTangles.mul_crossingTangle_maxArc
proof: formalized
---

# Mul-glue maps, ports, and unit factors

The vertical analogues of the add-side toolkit: the `mulGlue` arc map,
its values on glue ports, endpoint and crossing-list equations for
`T.mul S`, congruence across units, and endpoint/crossing/`maxArc` facts
for products with a unit factor on either side. Pure PD-code facts
backing every glued coloring of a product. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
