---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_mul_right_infinity RationalTangles.HasColoringFraction.invert_mul_left_infinity RationalTangles.coloringIsotopy_infinity_invert_add RationalTangles.coloring_invert_infinity_mul RationalTangles.coloring_fraction_invert_infinity_mul RationalTangles.coloring_fraction_invert_infinity_add RationalTangles.coloring_fraction_mul_infinity_invert RationalTangles.coloring_fraction_invert_add_infinity
proof: formalized
---

# Invert-mul with $[\infty]$ and the reindex machinery

Invert-mul with a right factor $[\infty]$ is a PD-code no-op on both
sides (`mul_infinity_eq`, `add_infinity_invert_eq`). Invert-mul with a
left factor $[\infty]$ reindexes $T^{i}$ along `infinityMulReindex`
after `switch`, while $[\infty]^{i}+T^{i}$ is coloring-isotopic to
$T^{i}$ (`coloringIsotopy_infinity_invert_add`). The dummy colorings and
fraction computations backing the invert-add $[\infty]$ nodes live here
too. All on arbitrary diagrams with no hypotheses. Proof part of the
parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
