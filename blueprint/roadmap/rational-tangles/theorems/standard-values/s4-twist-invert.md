---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_inv_rightBottom RationalTangles.coloring_invert_inv_slideReady RationalTangles.coloring_invert_inv_eq_F_rightBottom RationalTangles.coloring_invert_inv_eq_F_rightBottom_colorFrom
proof: formalized
---

# Fresh invert colorings of twists

Fresh colorings of the inverted PD-code of `rightBottom` and
`slideReady` twists carry $1/F$ — via the algebraic mirror and
`rotate180`, reusing uniqueness of $f=F$. Every non-monochrome coloring
of these inverts is identified with that value; the `colorFrom`
existence is recorded. Not transport across `switch` of a given
coloring, and not `invert_cong` on `ColoringIsotopy`. Proof part of the
parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
