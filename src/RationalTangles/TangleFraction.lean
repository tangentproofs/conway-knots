/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Rational
import RationalTangles.ContinuedFractionForm

/-!
# Fraction of a rational tangle

The fraction `F(T)` is the ordinary-arithmetic evaluation of a twist-form
expression, with tangle product interpreted as `x * y := 1 / (1/x + y)` and
`F([∞]) = ∞ = 1/0` (Kauffman–Lambropoulou Definition 8). By Remark 6, if
`T = [[a₁], …, [aₙ]]` then `F(T) = [a₁, …, aₙ]`, so the same quantity is
the value of the corresponding `ArithmeticCF`.
-/

namespace RationalTangles

/-- Arithmetic value of a crossing sign: `+1` or `-1`. -/
def CrossingSign.cfValue : CrossingSign → CFValue
  | .pos => 1
  | .neg => .ofInt (-1)

namespace TwistExpr

/-- Definition 8: evaluate a twist-form expression in ordinary arithmetic. -/
def fraction : TwistExpr → CFValue
  | zero => 0
  | infinity => .inf
  | one => 1
  | negOne => .ofInt (-1)
  | addRight e s => e.fraction.add s.cfValue
  | addLeft e s => s.cfValue.add e.fraction
  | mulBottom e s => (e.fraction.inv.add s.cfValue).inv
  | mulTop e s => (s.cfValue.inv.add e.fraction).inv

end TwistExpr

/-- Remark 6: the continued-fraction evaluation of `[a₁, …, aₙ]`. -/
def fractionOfCF (cf : ArithmeticCF) : CFValue :=
  cf.value

end RationalTangles
