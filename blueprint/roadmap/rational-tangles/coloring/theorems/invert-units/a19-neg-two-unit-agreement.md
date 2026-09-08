---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne RationalTangles.coloring_fraction_invert_mul_negOne_negOne RationalTangles.coloring_fraction_invert_mul_negOne_negOne_existence RationalTangles.HasColoringFraction.invert_add_mul_agree_negOne_negOne
proof: formalized
---

# Unrestricted negative two-unit invert-add agreement

Fresh colorings of `([-1]+[-1])ⁱ` (witness) and every non-monochrome coloring
of `[-1]ⁱ*[-1]ⁱ` (universal) agree at `-1/2`, with no `DiagonalSum` or port
inputs. The negative unit is the mirror-switch of the positive one, so the
arc wirings — and hence the coloring rules — differ from the `+1/2` case;
both sides are evaluated directly. Proof part of the parent topic; see that
page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
