---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_one_one_one RationalTangles.HasColoringFraction.invert_add_one_one_one
proof: formalized
---

# Unrestricted three-unit invert-add value

Every non-monochrome coloring of `([+1]+[+1]+[+1])ⁱ` has fraction `1/3`
(universal), with a direct witness for the existence: the three
switched rules force numerator `d` and denominator `3d` for nonzero
`d`, with no `DiagonalSum` or port inputs. This is the first rung past
two crossings for the direct-computation method — `decide` on the
three-crossing PD-code and `linarith` over six rule equations close
with only modest cost, so the machinery scales. Proof part of the
parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
