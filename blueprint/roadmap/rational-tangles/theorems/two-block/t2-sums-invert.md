---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_add_integerTangle_add_neg RationalTangles.HasColoringFraction.invert_add_integerTangle_add_neg RationalTangles.coloring_invert_add_neg_integerTangle_add RationalTangles.HasColoringFraction.invert_add_neg_integerTangle_add
proof: formalized
---

# Invert-add of two-block integer sums

Invert-add of the two-block PD-sum of canceling integer diagrams reuses
`coloring_invert_add_two_rightBottom` when $n \neq 0$ (summands have
finite nonzero $F$) or the `[0]` invert-add lemmas when $n = 0$,
carrying $\infty$ on both sign orders. Proof part of the parent topic;
see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
