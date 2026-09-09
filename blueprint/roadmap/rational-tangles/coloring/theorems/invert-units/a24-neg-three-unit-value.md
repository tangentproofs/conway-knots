---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative three-unit invert-add value

Every non-monochrome coloring of `([-1]+[-1]+[-1])ⁱ` has fraction
`-1/3` (universal), with a direct witness for the existence: the
three switched rules force numerator `d` and denominator `-3d` for
nonzero `d`, with no `DiagonalSum` or port inputs. The negative units
are mirror-switches of the positive ones, so the arc wirings — and
the sign of the denominator multiple — differ from the `+1/3` case;
the nonzero transfer additionally needs `neg_ne_zero` since the
denominator multiple is negative. Both sides are evaluated directly.
Proof part of the parent topic; see that page for the mathematical
context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
