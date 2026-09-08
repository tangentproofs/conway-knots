---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_mul_two_rightBottom RationalTangles.coloring_mirror_mul_two
proof: formalized
---

# Canceling two-block sums and products

The two-block PD-sum `(integerTangle n).add (integerTangle (-n))` is not
a `TwistExpr`; gluing integer colorings gives fraction $0$ when
non-monochrome, and invert-add reuses `coloring_invert_add_two_rightBottom`
for $n \neq 0$ (summands of finite nonzero $F$) or the `[0]` lemmas for
$n = 0$, carrying $\infty$. Dually, the two-block PD-product
`(verticalTwists n).mul (verticalTwists (-n))` carries $\infty$, and
invert-mul carries $0$. The general two-block glue
(`coloring_mul_two_rightBottom`) and mirror (`coloring_mirror_mul_two`)
machines are claimed here.

This is not a `ColoringIsotopy` constructor: invert-add/invert-mul switch
crossings. It is not unrestricted `flype_slide`, not `invert_cong` on
`ColoringIsotopy`, and not Theorem 2.

## Split into pull-request-sized nodes

The remaining results live in:

- [Two-block integer sums](t1-sums.md)
- [Invert-add of two-block integer sums](t2-sums-invert.md)
- [Two-block vertical products, fractions](t3-vertical-fractions.md)
- [Two-block vertical products, existence](t4-vertical-existence.md)
- [Invert-mul of two-block vertical products](t5-vertical-invert-mul.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)

## Proof depends on

- [Coloring fraction after invert on slide-ready diagrams](../coloring-invert-cong-slideReady.md)
