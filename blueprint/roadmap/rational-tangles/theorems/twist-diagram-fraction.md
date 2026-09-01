---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.toStandard_fraction_eq_of_diagram_slideReady RationalTangles.TwistExpr.toStandard_fraction_eq_of_diagram_rightBottom RationalTangles.TwistExpr.fraction_eq_of_diagram_rightBottom RationalTangles.TwistExpr.fraction_eq_of_diagram_noMulTop RationalTangles.StandardExpr.fraction_eq_of_diagram RationalTangles.IsTwistForm.toStandard_fraction_unique
proof: formalized
---

# Standard-form value of a twist diagram is well-defined

If two twist-form expressions denote the *same* PD-code, they have the same
standard-form evaluation `toStandard.fraction`, once each expression is
`slideReady` and a non-monochrome coloring of that code satisfies the
diagonal-sum rule. The coloring fraction of the diagram equals each
expression's standard-form value, so that value is a function of the diagram
rather than of the expression tree.

On right-and-bottom expressions the coloring is constructed by propagating
two initial strand colors, so no extra coloring hypothesis remains, and
algebraic $F$ agrees with the standard-form value. On expressions with no
top product the same conclusion for algebraic $F$ still needs a coloring
(left addition is allowed, but `colorFrom` is not).

A diagram that *is* a twist-form PD-code may therefore be assigned this
standard-form value via any right-and-bottom parse. An `IsRational` witness
is an isotopy to a twist diagram, not PD-code equality; assigning $F$ to an
arbitrary rational diagram still requires isotopy invariance (Theorem 2).

This is not Theorem 2, Theorem 3, or Theorem 4.

## Sources

- [Kauffman–Lambropoulou Definition 8](../../../sources/kauffman-lambropoulou.md#definition-8)
- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Fraction of a rational tangle](../definitions/tangle-fraction.md)
- [Standard form](../definitions/standard-form.md)
- [Rational tangle](../definitions/rational-tangle.md)

## Proof depends on

- [Coloring fraction of a rational tangle](../coloring/theorems/coloring-fraction-properties.md)
- [Every rational tangle has a standard form](standard-form-exists.md)
