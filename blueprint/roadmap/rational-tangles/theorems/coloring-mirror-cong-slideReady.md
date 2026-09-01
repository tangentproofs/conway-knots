---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_mirror_any_eq_neg_F_slideReady RationalTangles.coloring_mirror_cong_slideReady
proof: formalized
---

# Coloring fraction after mirror on slide-ready diagrams

A non-monochrome coloring of the PD-mirror of a `slideReady` twist-form
diagram has coloring fraction $-F$. Uniqueness of $f$ after mirror
(`coloring_mirror_slideReady`) identifies that value on every such
coloring.

If two `slideReady` expressions are related by `ColoringIsotopy`, they
share $F$, so fresh PD-mirror colorings share $-F$. That is the
fraction-level content of `mirror_cong` on this class. Colorings are not
transported across crossing switch, and `mirror_cong` is not added to
`ColoringIsotopy`.

This is not Theorem 2, Theorem 3, or Theorem 4.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)

## Proof depends on

- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
- [Standard-form $F$ along coloring isotopy](twist-coloring-isotopy-fraction.md)
