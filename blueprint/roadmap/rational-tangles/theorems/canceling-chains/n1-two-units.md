---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.addRight_canceling_units_fraction RationalTangles.TwistExpr.addRight_canceling_units_diagram RationalTangles.coloring_fraction_canceling_units RationalTangles.coloring_fraction_one_add_negOne RationalTangles.coloring_fraction_negOne_add_one RationalTangles.HasColoringFraction.canceling_units RationalTangles.HasColoringFraction.one_add_negOne RationalTangles.HasColoringFraction.negOne_add_one RationalTangles.coloring_invert_add_canceling_units RationalTangles.HasColoringFraction.invert_add_canceling_units
proof: formalized
---

# Two canceling units

The pairs $[+1]+[-1]$ and $[-1]+[+1]$ are `rightBottom` two-unit twists
of fraction $0$. Every non-monochrome coloring has fraction $0$ by
uniqueness (`coloring_fraction_canceling_units`, with the `[1]+[-1]`
spelling-outs). Invert-add of the pair reuses
`coloring_invert_add_units` with invert uniqueness, carrying $\infty$
— not glue of two general summands, so no dummy coloring. Proof part of
the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
