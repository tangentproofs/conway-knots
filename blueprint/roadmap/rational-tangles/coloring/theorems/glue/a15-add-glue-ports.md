---
declaration: lemma
origin: bridged
statement: formalized
lean: RationalTangles.addGlue_NW RationalTangles.addGlue_SW RationalTangles.addGlue_shift_eq RationalTangles.addGlue_crossingTangle_congr RationalTangles.addGlue_eq_of_glue_ports RationalTangles.addGlue_shift_fresh RationalTangles.addGlue_shift_unit_le RationalTangles.add_NE RationalTangles.add_SE RationalTangles.add_NW RationalTangles.add_SW RationalTangles.add_NE_rename RationalTangles.add_SE_rename RationalTangles.add_crossings_append
proof: formalized
---

# Add-glue maps and sum ports

The arc maps gluing a right summand onto a sum (`addGlue`, `addShift`),
their values on glue ports and fresh arcs, the resulting endpoint and
crossing-list equations for `T.add S`, and congruence of the glue maps
across units and port-matching summands. Pure PD-code facts backing
every glued coloring of a sum. Proof part of the parent topic; see that
page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
