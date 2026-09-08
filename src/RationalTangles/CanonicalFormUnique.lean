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

/-- Two right-and-bottom parses of the same twist-form PD-code agree on the
    standard-form value. `IsRational` witnesses an isotopy, not PD-code
    equality, so this does not assign `F` to an arbitrary rational diagram. -/
theorem IsTwistForm.toStandard_fraction_unique {T : TangleDiagram}
    {e₁ e₂ : TwistExpr}
    (hT₁ : T = e₁.diagram) (hT₂ : T = e₂.diagram)
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom) :
    e₁.toStandard.fraction = e₂.toStandard.fraction :=
  TwistExpr.toStandard_fraction_eq_of_diagram_rightBottom hr₁ hr₂ (hT₁.symm.trans hT₂)

/-- Same as `IsTwistForm.toStandard_fraction_unique`, for algebraic `F`. -/
theorem IsTwistForm.fraction_unique {T : TangleDiagram}
    {e₁ e₂ : TwistExpr}
    (hT₁ : T = e₁.diagram) (hT₂ : T = e₂.diagram)
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom) :
    e₁.fraction = e₂.fraction :=
  TwistExpr.fraction_eq_of_diagram_rightBottom hr₁ hr₂ (hT₁.symm.trans hT₂)

/-- A twist-form PD-code that admits a `slideReady` parse with a
    non-monochrome `DiagonalSum` coloring may be assigned the standard-form
    value of any such parse. -/
theorem IsTwistForm.toStandard_fraction_unique_slideReady {T : TangleDiagram}
    {e₁ e₂ : TwistExpr}
    (hT₁ : T = e₁.diagram) (hT₂ : T = e₂.diagram)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (col : Nat → Int)
    (hc : T.IsColored col)
    (hdiag : (ColorMatrix.of T col).DiagonalSum)
    (hm : (ColorMatrix.of T col).NotMono) :
    e₁.toStandard.fraction = e₂.toStandard.fraction := by
  subst hT₁
  exact TwistExpr.toStandard_fraction_eq_of_diagram_slideReady
    hok₁ hok₂ hT₂ col hc hdiag hm

/-- Same, with every coloring hypothesis discharged by `colorFrom 0 1`:
    `slideReady` parses of one PD-code agree on the standard-form value,
    no coloring input needed. -/
theorem IsTwistForm.toStandard_fraction_unique_slideReady_colorFrom
    {T : TangleDiagram} {e₁ e₂ : TwistExpr}
    (hT₁ : T = e₁.diagram) (hT₂ : T = e₂.diagram)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady) :
    e₁.toStandard.fraction = e₂.toStandard.fraction :=
  TwistExpr.toStandard_fraction_eq_of_diagram_slideReady_colorFrom
    hok₁ hok₂ (hT₁.symm.trans hT₂)

/-- Same as `IsTwistForm.fraction_unique`, for algebraic `F` on `noMulTop`
    `slideReady` parses: the coloring hypotheses discharge by `colorFrom`,
    using `fraction_eq_toStandard_of_noMulTop` on each side. -/
theorem IsTwistForm.fraction_unique_slideReady_noMulTop
    {T : TangleDiagram} {e₁ e₂ : TwistExpr}
    (hT₁ : T = e₁.diagram) (hT₂ : T = e₂.diagram)
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady) :
    e₁.fraction = e₂.fraction :=
  TwistExpr.fraction_eq_of_diagram_noMulTop_colorFrom
    hn₁ hn₂ hok₁ hok₂ (hT₁.symm.trans hT₂)

/-- On rightBottom parses, the arithmetical fraction is a function of the
    PD-code: existence from any parse, uniqueness by `fraction_unique`.
    Relational formulation, so no choice principle is needed. -/
theorem IsTwistForm.exists_unique_fraction_rightBottom {T : TangleDiagram}
    {e : TwistExpr} (hT : T = e.diagram) (hr : e.rightBottom) :
    ∃! v : CFValue, ∃ e' : TwistExpr,
      e'.rightBottom ∧ T = e'.diagram ∧ e'.fraction = v := by
  refine ⟨e.fraction, ⟨e, hr, hT, rfl⟩, ?_⟩
  rintro v ⟨e', hr', hT', hf'⟩
  exact hf'.symm.trans (IsTwistForm.fraction_unique hT hT' hr hr').symm

/-- Diagram-level Theorem 3 for rightBottom-parseable diagrams: same
    fraction implies isotopic. Not Theorem 3 in full (arbitrary rational
    diagrams, arbitrary parses). -/
theorem IsTwistForm.same_fraction_isotopic_rightBottom {T S : TangleDiagram}
    {e₁ e₂ : TwistExpr} (hT : T = e₁.diagram) (hS : S = e₂.diagram)
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom)
    (hf : e₁.fraction = e₂.fraction) : Isotopic T S := by
  subst hT
  subst hS
  exact twist_same_fraction_isotopic_of_rightBottom hr₁ hr₂ hf

/-- On `noMulTop` `slideReady` parses, the arithmetical fraction is a
    function of the PD-code (`colorFrom` discharge needs `slideReady`;
    `noMulTop` aligns algebraic `F` with the standard value). -/
theorem IsTwistForm.exists_unique_fraction_noMulTop {T : TangleDiagram}
    {e : TwistExpr} (hT : T = e.diagram) (hn : e.noMulTop)
    (hok : e.slideReady) :
    ∃! v : CFValue, ∃ e' : TwistExpr,
      e'.noMulTop ∧ e'.slideReady ∧ T = e'.diagram ∧ e'.fraction = v := by
  refine ⟨e.fraction, ⟨e, hn, hok, hT, rfl⟩, ?_⟩
  rintro v ⟨e', hn', hok', hT', hf'⟩
  exact hf'.symm.trans
    (TwistExpr.fraction_eq_of_diagram_noMulTop_colorFrom
      hn hn' hok hok' (hT.symm.trans hT')).symm

/-- Diagram-level Theorem 3 for `noMulTop`-parseable diagrams (needs only
    `noMulTop`; the standard value agrees there unconditionally). -/
theorem IsTwistForm.same_fraction_isotopic_noMulTop {T S : TangleDiagram}
    {e₁ e₂ : TwistExpr} (hT : T = e₁.diagram) (hS : S = e₂.diagram)
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hf : e₁.fraction = e₂.fraction) : Isotopic T S := by
  subst hT
  subst hS
  exact twist_same_fraction_isotopic_of_noMulTop hn₁ hn₂ hf

end RationalTangles
