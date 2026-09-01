---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_unique_rot180_slideReady RationalTangles.coloring_rot180_cong_slideReady
proof: formalized
---

# Coloring fraction after 180° rotation on slide-ready diagrams

A non-monochrome coloring of the planar $180^\circ$ of a `slideReady`
twist-form diagram has coloring fraction $F$. Uniqueness of $f=F$ on
the original diagram, after restoring disc colors by two $90^\circ$
rotations, identifies that value on every such coloring of $T.rot180$.

If two `slideReady` expressions are related by `ColoringIsotopy`, they
share $F$, so any non-monochrome colorings of the two `rot180` PD-codes
share $F$. That is the fraction-level content of `rot180_cong` on this
class. It is not added to `ColoringIsotopy`.

This is uniqueness of $f$ after planar $180^\circ$ on a `slideReady`
diagram, and agreement of those rotated fractions along coloring-ready
isotopy. It is not invariance of $F$ along arbitrary `Isotopic`.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)

## Proof depends on

- [Standard-form $F$ along coloring isotopy](twist-coloring-isotopy-fraction.md)
- [Coloring fraction of rotated unit sums and products](coloring-rot180-add-units.md)
