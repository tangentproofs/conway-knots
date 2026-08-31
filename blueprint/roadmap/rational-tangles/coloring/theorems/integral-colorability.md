---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.integrally_colorable_from_initial RationalTangles.StandardExpr.colorFrom_isColored
proof: formalized
---

# Every rational tangle is integrally colorable

A tangle is **integrally colorable** when it admits a coloring by integers
(no reduction modulo $n$ is required). Every rational tangle is integrally
colorable: choose two colors for the initial strands (the starting colors,
e.g. $0$ and $1$) and color the tangle as it is created by successive
twists. Coloring must start from the initial strands, so that it propagates
automatically and uniquely; starting elsewhere may leave an edge with an
undetermined color.

The inductive step is the coloring rule at the new crossing created by
adding or multiplying by $[\pm 1]$.

## Sources

- [Kauffman–Lambropoulou, integral colorability](../../../../sources/kauffman-lambropoulou.md#integral-colorability)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Rational tangle](../../definitions/rational-tangle.md)

## Proof depends on

- [Integer and vertical tangles](../../definitions/integer-tangle.md)
