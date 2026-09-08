---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.verticalTwists_NW RationalTangles.verticalTwists_NE RationalTangles.verticalTwists_NW_ne_NE RationalTangles.coloring_fraction_verticalTwists RationalTangles.verticalTwists_diagonal RationalTangles.coloring_fraction_verticalTwists_mul_neg
proof: formalized
---

# Two-block vertical products, fractions

The two-block PD-product `(verticalTwists n).mul (verticalTwists (-n))`
is not a `TwistExpr`. Gluing vertical colorings gives fraction $\infty$
when non-monochrome (`coloring_fraction_verticalTwists_mul_neg`,
via `verticalTwists_diagonal`). Port and diagonal facts for vertical
twists are recorded here. Proof part of the parent topic; see that page
for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
