/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.CanonicalFormExists
import RationalTangles.ColoringFractionEq

/-!
# Canonical diagrams of a given fraction

Two continued-fraction diagrams already in canonical form with the same
arithmetic value are the same PD-code (`canonical_tangle_eq_of_value`).
A standard-form expression with finite fraction `q` isotopes to that unique
diagram `(canonicalCF q).tangle` by the value-preserving reduction of
Proposition 2 together with uniqueness of Proposition 3. Two twist
expressions with the same algebraic `F` are isotopic once that value agrees
with `toStandard` (automatic if there is no top product). This does not
claim that `F` is invariant under arbitrary leftover `Isotopic` generators,
and it is not Theorem 3.
-/

namespace RationalTangles

theorem StandardExpr.toCF_value_of_fraction {e : StandardExpr} {q : Rat}
    (h : e.fraction = CFValue.ofRat q) :
    e.toCF.value = CFValue.ofRat q :=
  (StandardExpr.fraction_eq_toCF_value e).symm.trans h

/-- A standard-form diagram of finite fraction `q` isotopes to the unique
    canonical continued-fraction diagram of `q`. -/
theorem StandardExpr.isotopic_canonicalCF {e : StandardExpr} {q : Rat}
    (h : e.fraction = CFValue.ofRat q) :
    Isotopic e.diagram (canonicalCF q).tangle :=
  .trans e.toCF_isotopic
    (ArithmeticCF.isotopic_canonicalCF (StandardExpr.toCF_value_of_fraction h))

/-- Two standard forms of the same finite fraction are isotopic. -/
theorem standard_same_fraction_isotopic {e₁ e₂ : StandardExpr} {q : Rat}
    (h₁ : e₁.fraction = CFValue.ofRat q) (h₂ : e₂.fraction = CFValue.ofRat q) :
    Isotopic e₁.diagram e₂.diagram :=
  (StandardExpr.isotopic_canonicalCF h₁).trans
    (StandardExpr.isotopic_canonicalCF h₂).symm

theorem StandardExpr.toCF_value_of_inf {e : StandardExpr}
    (h : e.fraction = CFValue.inf) :
    e.toCF.value = CFValue.inf :=
  (StandardExpr.fraction_eq_toCF_value e).symm.trans h

theorem StandardExpr.isotopic_infinity_of_fraction {e : StandardExpr}
    (h : e.fraction = CFValue.inf) :
    Isotopic e.diagram TangleDiagram.infinity := by
  have hv := StandardExpr.toCF_value_of_inf h
  rcases cf_to_canonical e.toCF.terms e.toCF.later_ne_zero e.toCF.terms_ne with
    ⟨cf, hcan, _, hval⟩ | ⟨hinf, _⟩
  · exact (isCanonical_value_ne_inf hcan (hval.trans hv)).elim
  · exact e.toCF_isotopic.trans hinf

theorem standard_same_inf_isotopic {e₁ e₂ : StandardExpr}
    (h₁ : e₁.fraction = CFValue.inf) (h₂ : e₂.fraction = CFValue.inf) :
    Isotopic e₁.diagram e₂.diagram :=
  (StandardExpr.isotopic_infinity_of_fraction h₁).trans
    (StandardExpr.isotopic_infinity_of_fraction h₂).symm

/-- Two standard forms of fraction `q` reduce to the same canonical CF. -/
theorem standard_same_fraction_same_canonicalCF {e₁ e₂ : StandardExpr} {q : Rat}
    (h₁ : e₁.fraction = CFValue.ofRat q) (h₂ : e₂.fraction = CFValue.ofRat q)
    {cf₁ cf₂ : ArithmeticCF}
    (hc₁ : cf₁.IsCanonical) (hc₂ : cf₂.IsCanonical)
    (hv₁ : cf₁.value = e₁.toCF.value) (hv₂ : cf₂.value = e₂.toCF.value) :
    cf₁ = cf₂ := by
  have e1 : cf₁ = canonicalCF q :=
    canonicalCF_unique hc₁ (hv₁.trans (StandardExpr.toCF_value_of_fraction h₁))
  have e2 : cf₂ = canonicalCF q :=
    canonicalCF_unique hc₂ (hv₂.trans (StandardExpr.toCF_value_of_fraction h₂))
  exact e1.trans e2.symm

/-- Two standard forms of the same arithmetical value (finite or `∞`) are
    isotopic. -/
theorem standard_same_CFValue_isotopic {e₁ e₂ : StandardExpr}
    (h : e₁.fraction = e₂.fraction) :
    Isotopic e₁.diagram e₂.diagram := by
  cases he : e₁.fraction with
  | inf =>
    exact standard_same_inf_isotopic he (h.symm.trans he)
  | ofRat q =>
    exact standard_same_fraction_isotopic he (h.symm.trans he)

/-- A twist-form diagram isotopes to the unique canonical continued-fraction
    diagram of a finite fraction `q` once the standard-form evaluation of
    `toStandard` equals `q`. -/
theorem TwistExpr.isotopic_canonicalCF {e : TwistExpr} {q : Rat}
    (hs : e.toStandard.fraction = CFValue.ofRat q) :
    Isotopic e.diagram (canonicalCF q).tangle :=
  e.toStandard_isotopic.trans (StandardExpr.isotopic_canonicalCF hs)

theorem TwistExpr.isotopic_infinity_of_fraction {e : TwistExpr}
    (hs : e.toStandard.fraction = CFValue.inf) :
    Isotopic e.diagram TangleDiagram.infinity :=
  e.toStandard_isotopic.trans (StandardExpr.isotopic_infinity_of_fraction hs)

/-- If two twist expressions reduce by `toStandard` to standard forms of the
    same arithmetical value, their diagrams are isotopic. This uses
    `toStandard_isotopic` (flypes / left-add and top-mul slides) and uniqueness
    of canonical form; it does not claim well-definedness of `F` along an
    arbitrary `Isotopic` witness. -/
theorem twist_same_toStandard_fraction_isotopic {e₁ e₂ : TwistExpr}
    (h : e₁.toStandard.fraction = e₂.toStandard.fraction) :
    Isotopic e₁.diagram e₂.diagram :=
  e₁.toStandard_isotopic.trans
    ((standard_same_CFValue_isotopic h).trans e₂.toStandard_isotopic.symm)

/-- Two twist expressions with the same algebraic fraction have isotopic
    diagrams, provided each expression's `F` agrees with the standard-form
    evaluation of `toStandard`. The extra hypothesis is automatic on
    `noMulTop` (and on `rightBottom`); an unrestricted `mulTop` can have a
    different Conway product from the right-and-bottom rewrite. This is not
    Theorem 3: it does not apply to an arbitrary rational diagram. -/
theorem twist_same_fraction_isotopic {e₁ e₂ : TwistExpr}
    (hf : e₁.fraction = e₂.fraction)
    (h₁ : e₁.fraction = e₁.toStandard.fraction)
    (h₂ : e₂.fraction = e₂.toStandard.fraction) :
    Isotopic e₁.diagram e₂.diagram :=
  twist_same_toStandard_fraction_isotopic (h₁.symm.trans (hf.trans h₂))

theorem twist_same_fraction_isotopic_of_noMulTop {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hf : e₁.fraction = e₂.fraction) :
    Isotopic e₁.diagram e₂.diagram :=
  twist_same_fraction_isotopic hf
    (TwistExpr.fraction_eq_toStandard_of_noMulTop e₁ hn₁)
    (TwistExpr.fraction_eq_toStandard_of_noMulTop e₂ hn₂)

theorem twist_same_fraction_isotopic_of_rightBottom {e₁ e₂ : TwistExpr}
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom)
    (hf : e₁.fraction = e₂.fraction) :
    Isotopic e₁.diagram e₂.diagram :=
  twist_same_fraction_isotopic_of_noMulTop
    (TwistExpr.noMulTop_of_rightBottom e₁ hr₁)
    (TwistExpr.noMulTop_of_rightBottom e₂ hr₂) hf

end RationalTangles
