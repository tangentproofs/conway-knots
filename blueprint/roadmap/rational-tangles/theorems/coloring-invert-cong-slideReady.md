---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_inv_eq_F_slideReady RationalTangles.coloring_invert_inv_eq_F_slideReady_colorFrom RationalTangles.coloring_invert_inv_any_slideReady RationalTangles.coloring_fraction_unique_invert_slideReady RationalTangles.coloring_invert_cong_slideReady RationalTangles.TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom
proof: formalized
---

# Coloring fraction after invert on slide-ready diagrams

A non-monochrome coloring of a `slideReady` twist-form diagram has coloring
fraction equal to the standard-form value $F$. A *fresh* coloring of the
inverted PD-code therefore has fraction $1/F$. Inversion is the rotate of
the PD-mirror, so any non-monochrome coloring of the inverted PD-code
likewise has fraction $1/F$: uniqueness of $f$ on $T$ identifies the
PD-mirror fraction as $-F$, and rotation sends that to $1/F$.

If two `slideReady` expressions are related by `ColoringIsotopy`, they share
$F$, so fresh invert colorings share $1/F$. That is the fraction-level
content of invert-congruence on this class. Colorings are not transported
across crossing switch, and `invert_cong` is not added to `ColoringIsotopy`.

This is not Theorem 2, Theorem 3, or Theorem 4. It is uniqueness of $f$ after
invert on a `slideReady` diagram, and agreement of those inverted fractions
along coloring-ready isotopy.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)

## Proof depends on

- [Coloring fraction of a rational tangle](../coloring/theorems/coloring-fraction-properties.md)
- [Standard-form $F$ along coloring isotopy](twist-coloring-isotopy-fraction.md)
