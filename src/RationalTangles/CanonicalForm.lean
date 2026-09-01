/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.ContinuedFractionForm

/-!
# Canonical form of a rational tangle

A rational tangle `T = [[β₁], …, [βₘ]]` in continued fraction form is in
canonical form when it is alternating (all `βᵢ` positive, or all negative)
and `m` is odd (Kauffman–Lambropoulou Definition 6).
-/

namespace RationalTangles

/-- An arithmetic continued fraction is in canonical form when it has odd
    length and is termwise nonnegative or termwise nonpositive (Definition 7).
    The leading term may be zero; later terms are already nonzero by
    `ArithmeticCF.later_ne_zero`, so a nonzero expansion is termwise positive
    or termwise negative after the (possible) leading zero. -/
def ArithmeticCF.IsCanonical (cf : ArithmeticCF) : Prop :=
  cf.length % 2 = 1 ∧
    ((∀ a ∈ cf.terms, 0 ≤ a) ∨ (∀ a ∈ cf.terms, a ≤ 0))

/-- A diagram in canonical continued-fraction form. -/
def IsCanonicalForm (T : TangleDiagram) : Prop :=
  ∃ cf : ArithmeticCF, cf.IsCanonical ∧ T = cf.tangle

end RationalTangles
