---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_integerTangle_add_neg RationalTangles.coloring_exists_integerTangle_add_neg RationalTangles.HasColoringFraction.integerTangle_add_neg RationalTangles.coloring_fraction_neg_integerTangle_add RationalTangles.coloring_exists_neg_integerTangle_add RationalTangles.HasColoringFraction.neg_integerTangle_add
proof: formalized
---

# Two-block integer sums

The two-block PD-sum `(integerTangle n).add (integerTangle (-n))` is not
a `TwistExpr`. Gluing integer colorings gives fraction $0$ when
non-monochrome, on both sign orders, with `HasColoringFraction`
existence. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
