---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.ColorMatrix.NotMono_of_rot180 RationalTangles.coloring_rot180_add_slideReady RationalTangles.coloring_rot180_mul_slideReady
proof: formalized
---

# Coloring fraction of rotated unit sums and products

The leftover generators `Isotopic.rot180_add` and `Isotopic.rot180_mul` are
$(T+S)^{180}\sim S^{180}+T^{180}$ and $(T*S)^{180}\sim S^{180}*T^{180}$.
On a `slideReady` twist, uniqueness of $f=F$ already identifies every
non-monochrome coloring of $T^{180}$. When $S$ is a unit and $T+S$
(resp. $T*S$) is `addRight` (resp. `mulBottom`), a coloring of the
rotated twist glues to a coloring of the swapped rotated PD-code with
the same color matrix, hence the same fraction $F$.

There is no `TwistExpr` for planar $180^\circ$ of a general summand, so
neither comparison is a `SlideReadyIsotopy` constructor, and neither is
added to `ColoringIsotopy`. This is not Theorem 2: arbitrary isotopy,
`rot180_add`/`rot180_mul` of two general (non-unit) diagrams, and
`rot180_cong` of an arbitrary isotopy remain omitted.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Flype](../definitions/flype.md)

## Proof depends on

- [Standard-form $F$ along coloring isotopy](twist-coloring-isotopy-fraction.md)
