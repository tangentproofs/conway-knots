---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_mul_one_negOne RationalTangles.HasColoringFraction.invert_mul_one_negOne RationalTangles.coloring_fraction_invert_mul_negOne_one RationalTangles.HasColoringFraction.invert_mul_negOne_one
proof: formalized
---

# Mixed-sign invert-mul products at infinity

On the mixed-sign products `[+1]ⁱ*[-1]ⁱ` and `[-1]ⁱ*[+1]ⁱ`, every coloring
— monochrome or not — has fraction `∞`: the two crossing rules force the
denominator `NE − SE` to vanish identically, so no non-monochrome
hypothesis is needed for the universal. Direct witnesses give the
`HasColoringFraction` existences at `∞` on both products. The agreement
conjunctions pairing these products with the `([1]+[-1])ⁱ` and
`([-1]+[1])ⁱ` sum sides already live in [the spelled-out node](n5-one-negOne.md).
Proof part of the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
