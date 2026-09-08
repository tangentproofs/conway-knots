---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_four_one RationalTangles.HasColoringFraction.invert_add_four_one
proof: formalized
---

# Unrestricted four-unit invert-add value

Every non-monochrome coloring of `([+1]+[+1]+[+1]+[+1])ⁱ` has fraction
`1/4` (universal), with a direct witness for the existence: the four
switched rules force numerator `d` and denominator `4d` for nonzero
`d`, with no `DiagonalSum` or port inputs. Rung two of the ladder past
two crossings; module build cost rises only modestly over the
three-unit rung, so the direct-computation method keeps scaling.
Proof part of the parent topic; see that page for the mathematical
context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
