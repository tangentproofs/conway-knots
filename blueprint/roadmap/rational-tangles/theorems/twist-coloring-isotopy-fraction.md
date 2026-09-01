---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.toStandard_fraction_ColoringIsotopy RationalTangles.TwistExpr.fraction_ColoringIsotopy_noMulTop RationalTangles.TwistExpr.fraction_ColoringIsotopy_rightBottom
proof: formalized
---

# Standard-form $F$ along coloring isotopy

If two `slideReady` twist-form expressions are related by `ColoringIsotopy`
and the source admits a non-monochrome coloring that satisfies the diagonal
sum rule, then they have the same standard-form evaluation
`toStandard.fraction`. The coloring fraction of each diagram equals that
value, and coloring fraction is already invariant along `ColoringIsotopy`.

On expressions with no top product the same conclusion holds for algebraic
$F$. On right-and-bottom expressions the coloring is `colorFrom`, so no
extra coloring hypothesis remains.

This is not Theorem 2: `ColoringIsotopy` does not include unrestricted
Figure 14 transfers, flype-slides, or `invert_cong`, and it is not full
diagram isotopy. Assigning $F$ to an arbitrary rational diagram still
requires isotopy invariance of $F$.

## Sources

- [Kauffman–Lambropoulou Definition 8](../../../sources/kauffman-lambropoulou.md#definition-8)
- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Fraction of a rational tangle](../definitions/tangle-fraction.md)
- [Standard form](../definitions/standard-form.md)
- [Coloring fraction](../coloring/definitions/coloring-fraction.md)

## Proof depends on

- [Standard-form value of a twist diagram is well-defined](twist-diagram-fraction.md)
- [Coloring fraction of a rational tangle](../coloring/theorems/coloring-fraction-properties.md)
