---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_mul_two_rightBottom RationalTangles.HasColoringFraction.invert_mul_two_rightBottom RationalTangles.coloring_invert_mul_infinity RationalTangles.HasColoringFraction.invert_mul_infinity
proof: formalized
---

# Invert-mul of two right-and-bottom diagrams

For two `rightBottom` / `slideReady` twist diagrams $T,S$ with finite
nonzero standard-form values $F(T)$ and $F(S)$, independent fresh
colorings of $(T*S)^{i}$ and of $T^{i}+S^{i}$ are non-monochrome and
agree at $F(T)^{-1}+F(S)^{-1}$. The comparison uses glue of invert
colorings on the sum side and algebraic-mirror product plus rotation on
the invert-of-product side.

Skip $0$ and $\infty$ on those two-block hypotheses. The degenerate
product $[\infty]*[\infty]$ is a separate dummy coloring: both
$([\infty]*[\infty])^{i}$ and $[\infty]^{i}+[\infty]^{i}$ collapse to
$[\infty]^{i}$ and carry fraction $0$.

Neither identity is a `ColoringIsotopy` (crossings switch). Neither is a
`SlideReadyIsotopy` constructor (`T.mul S` is not a `TwistExpr`). This is
not unrestricted `flype_slide`, and it is not Theorem 2.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../definitions/integer-tangle.md)

## Proof depends on

- [Coloring fraction of inverted unit sums and products](../coloring/theorems/coloring-invert-add-units.md)
- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
