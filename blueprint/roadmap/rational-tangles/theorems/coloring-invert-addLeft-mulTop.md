---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_mirror_addLeft RationalTangles.coloring_invert_inv_addLeft RationalTangles.coloring_invert_inv_eq_F_addLeft RationalTangles.coloring_invert_inv_eq_F_addLeft_colorFrom RationalTangles.coloring_invert_inv_any_addLeft RationalTangles.coloring_fraction_unique_invert_addLeft RationalTangles.coloring_mirror_any_eq_neg_F_addLeft RationalTangles.coloring_fraction_unique_mirror_addLeft RationalTangles.coloring_mirror_mulTop RationalTangles.coloring_invert_inv_mulTop RationalTangles.coloring_invert_inv_eq_F_mulTop RationalTangles.coloring_invert_inv_eq_F_mulTop_colorFrom RationalTangles.coloring_invert_inv_any_mulTop RationalTangles.coloring_fraction_unique_invert_mulTop RationalTangles.coloring_mirror_any_eq_neg_F_mulTop RationalTangles.coloring_fraction_unique_mirror_mulTop RationalTangles.HasColoringFraction.invert_addLeft RationalTangles.HasColoringFraction.mirror_addLeft RationalTangles.HasColoringFraction.invert_mulTop RationalTangles.HasColoringFraction.mirror_mulTop
proof: formalized
---

# Coloring fraction after invert on addLeft and mulTop

Uniqueness of the coloring fraction on `addLeft` (resp. `mulTop`) of a
right-and-bottom inner expression, under the glue-port hypotheses used to
color those constructors ($NW \neq SW$ / $NW \neq NE$), identifies $f$
with the arithmetical value (resp. the standard-form value). A *fresh*
coloring of the inverted PD-code therefore has fraction $1/F$, dual to
invert uniqueness on `slideReady` diagrams. Independently, a fresh
coloring of the PD-mirror has fraction $-F$.

Colorings are not transported across crossing switch, and `invert_cong`
is not added to `ColoringIsotopy`. Invert coloring without the port
hypotheses is not claimed: those constructors are not `slideReady` when
the glue ports coincide.

This is not Theorem 2, Theorem 3, or Theorem 4. It is uniqueness of $f$
after invert (and after mirror) on these two honest classes.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)

## Proof depends on

- [Uniqueness of the coloring fraction on larger honest classes](coloring-fraction-unique.md)
- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
- [Coloring fraction after mirror on slide-ready diagrams](coloring-mirror-cong-slideReady.md)
