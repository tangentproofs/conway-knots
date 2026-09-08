---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.toStandard_fraction_eq_of_diagram_slideReady RationalTangles.TwistExpr.toStandard_fraction_eq_of_diagram_rightBottom RationalTangles.TwistExpr.fraction_eq_of_diagram_rightBottom RationalTangles.TwistExpr.fraction_eq_of_diagram_noMulTop RationalTangles.StandardExpr.fraction_eq_of_diagram RationalTangles.IsTwistForm.toStandard_fraction_unique RationalTangles.IsTwistForm.toStandard_fraction_unique_slideReady_colorFrom RationalTangles.TwistExpr.fraction_eq_of_diagram_noMulTop_colorFrom RationalTangles.IsTwistForm.fraction_unique_slideReady_noMulTop RationalTangles.TwistExpr.mulTop_comm_of_unit_fraction RationalTangles.TwistExpr.fraction_eq_toStandard_mulTop_of_unit_fraction RationalTangles.TwistExpr.unitMulTop RationalTangles.TwistExpr.toNoMulTop_fraction_of_unitMulTop RationalTangles.TwistExpr.exists_noMulTop_fraction_isotopic
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
algebraic $F$ agrees with the standard-form value. On `noMulTop`
`slideReady` expressions the coloring hypotheses likewise discharge by
`colorFrom`, for both the standard-form and the algebraic value. The
`mulTop` commutativity hypothesis itself holds when the inner fraction
is `±1` (the fixed points of `inv`: both sides reduce to `s ± 1`),
so `mulTop` over a unit-fraction twist preserves algebraic `F` — and on
the `unitMulTop` subclass (every top product over a `±1` inner) the
`toNoMulTop` normalization preserves algebraic `F` throughout, giving a
`noMulTop` expression with identical `F` for Theorem 3.

A diagram that *is* a twist-form PD-code may therefore be assigned this
standard-form value via any right-and-bottom parse. An `IsRational` witness
is an isotopy to a twist diagram, not PD-code equality; assigning $F$ to an
arbitrary rational diagram still requires isotopy invariance (Theorem 2).

This is not Theorem 2, Theorem 3, or Theorem 4.

## Sources

- [Kauffman–Lambropoulou Definition 8](../../../../sources/kauffman-lambropoulou.md#definition-8)
- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Rational tangle](../../definitions/rational-tangle.md)

## Proof depends on

- [Coloring fraction of a rational tangle](../../coloring/theorems/coloring-fraction-properties.md)
- [Every rational tangle has a standard form](standard-form-exists.md)
