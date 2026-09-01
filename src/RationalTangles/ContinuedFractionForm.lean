/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.IntegerTangle
import RationalTangles.ContinuedFraction

/-!
# Continued fraction form of a tangle

A continued fraction in integer tangles is the algebraic description
`[[a₁], …, [aₙ]] := [a₁] + 1 / ([a₂] + ⋯ + 1/[aₙ])` (Kauffman–Lambropoulou
Definition 5). The leading term may be zero; later terms are nonzero.
This is the tangle-level counterpart of `ArithmeticCF`.
-/

namespace RationalTangles

/-- Interpret a list of integers as a continued fraction of integer tangles,
    innermost term last. The empty list is `[∞]`. -/
def cfTangle : List Int → TangleDiagram
  | [] => TangleDiagram.infinity
  | [a] => integerTangle a
  | a :: b :: rest => integerTangle a + (cfTangle (b :: rest)).invert

/-- The tangle `[[a₁], …, [aₙ]]` denoted by an arithmetic continued fraction. -/
def ArithmeticCF.tangle (cf : ArithmeticCF) : TangleDiagram :=
  cfTangle cf.terms

/-- A diagram in continued fraction form. -/
def IsContinuedFractionForm (T : TangleDiagram) : Prop :=
  ∃ cf : ArithmeticCF, T = cf.tangle

theorem cfTangle_nil : cfTangle [] = TangleDiagram.infinity := rfl

theorem cfTangle_singleton (a : Int) : cfTangle [a] = integerTangle a := rfl

theorem cfTangle_cons (a : Int) (t : List Int) :
    cfTangle (a :: t) =
      match t with
      | [] => integerTangle a
      | _ => integerTangle a + (cfTangle t).invert := by
  cases t <;> rfl

end RationalTangles
