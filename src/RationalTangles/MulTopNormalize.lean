/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.FlippingLemma
import RationalTangles.TangleFraction
import RationalTangles.ColorFraction
import RationalTangles.ColoringIsotopy
import RationalTangles.ColorFractionUnique
import RationalTangles.CanonicalFormUnique
import RationalTangles.DiagonalSumGeneral
import RationalTangles.ColoringFractionEq

/-!
# Eliminating top products from twist expressions (diagram-level fragment)

For Theorem 3, an arbitrary twist expression must be normalized without
changing its (standard-form) fraction. Addition is commutative, so
`addLeft` is harmless (`fraction_eq_toStandard_addLeft`); the Conway
product is not, so `mulTop` is the obstruction (blocker (b):
`TwistExpr.fraction` of a `mulTop` node need not equal its
`toStandard.fraction`).

This file proves the diagram-level half: every twist expression isotopes
to one with no top product (`toNoMulTop`), via the proved Figure 5 slide
`flype_mul` and the planar half-turn `TwistExpr.isotopic_rot180`. The
standard-form fraction is preserved (`toNoMulTop_toStandard_fraction`).

Residual gaps (not claimed): algebraic `TwistExpr.fraction` is preserved
only under the explicit commutativity hypothesis
`fraction_eq_toStandard_mulTop` (discharged for unit fractions, with a
normalization procedure, in the second half of this file). Coloring
transport along the normalization path is proved for `slideReady`
twists (`coloring_toNoMulTop`, carried fractions in
`HasColoringFraction.toNoMulTop_slideReady`); transport from colorings
of non-`slideReady` diagrams is outstanding.
-/

namespace RationalTangles
namespace TwistExpr

/-- Eliminate every top product, rewriting `mulTop e s` to
    `mulBottom e.toNoMulTop s`. Left addition is kept: it is harmless
    for the fraction. -/
def toNoMulTop : TwistExpr → TwistExpr
  | zero => zero
  | infinity => infinity
  | one => one
  | negOne => negOne
  | addRight e s => addRight e.toNoMulTop s
  | addLeft e s => addLeft e.toNoMulTop s
  | mulBottom e s => mulBottom e.toNoMulTop s
  | mulTop e s => mulBottom e.toNoMulTop s

theorem toNoMulTop_noMulTop (e : TwistExpr) : e.toNoMulTop.noMulTop := by
  induction e with
  | zero => exact trivial
  | infinity => exact trivial
  | one => exact trivial
  | negOne => exact trivial
  | addRight e s ih => exact ih
  | addLeft e s ih => exact ih
  | mulBottom e s ih => exact ih
  | mulTop e s ih => exact ih

/-- The normalization is diagram-isotopic: a `mulTop` node slides via
    `flype_mul`, and the resulting `rot180` of the normalized inner
    expression turns back via `isotopic_rot180`. -/
theorem toNoMulTop_isotopic (e : TwistExpr) :
    Isotopic e.diagram e.toNoMulTop.diagram := by
  induction e with
  | zero => exact .refl _
  | infinity => exact .refl _
  | one => exact .refl _
  | negOne => exact .refl _
  | addRight e s ih =>
    simpa [TwistExpr.toNoMulTop, TwistExpr.diagram, add_eq_add] using
      Isotopic.add_left (S := crossingTangle s) ih
  | addLeft e s ih =>
    simpa [TwistExpr.toNoMulTop, TwistExpr.diagram, add_eq_add] using
      Isotopic.add_right (T := crossingTangle s) ih
  | mulBottom e s ih =>
    simpa [TwistExpr.toNoMulTop, TwistExpr.diagram, mul_eq_mul] using
      Isotopic.mul_left (S := crossingTangle s) ih
  | mulTop e s ih =>
    simp only [TwistExpr.toNoMulTop, TwistExpr.diagram, mul_eq_mul]
    have h1 : Isotopic ((crossingTangle s).mul e.diagram)
        (e.diagram.rot180.mul (crossingTangle s)) :=
      flype_mul s e.diagram
    have h2 : Isotopic (e.diagram.rot180.mul (crossingTangle s))
        (e.toNoMulTop.diagram.rot180.mul (crossingTangle s)) :=
      Isotopic.mul_left (S := crossingTangle s) (.rot180_cong ih)
    have h3 : Isotopic
        (e.toNoMulTop.diagram.rot180.mul (crossingTangle s))
        (e.toNoMulTop.diagram.mul (crossingTangle s)) :=
      Isotopic.mul_left (S := crossingTangle s) e.toNoMulTop.isotopic_rot180
    exact h1.trans (h2.trans h3)

/-- The normalization preserves the standard-form fraction: `toStandard`
    already sends both `mulTop` and `mulBottom` to the right-and-bottom
    product. -/
theorem toNoMulTop_toStandard_fraction (e : TwistExpr) :
    e.toNoMulTop.toStandard.fraction = e.toStandard.fraction := by
  induction e with
  | zero => rfl
  | infinity => rfl
  | one => rfl
  | negOne => rfl
  | addRight e s ih =>
    have hL : (toNoMulTop (TwistExpr.addRight e s)).toStandard =
        StandardExpr.addRight e.toNoMulTop.toStandard s := rfl
    have hR : (TwistExpr.addRight e s).toStandard =
        StandardExpr.addRight e.toStandard s := rfl
    rw [hL, hR]
    cases s <;> simp [StandardExpr.fraction, ih]
  | addLeft e s ih =>
    have hL : (toNoMulTop (TwistExpr.addLeft e s)).toStandard =
        StandardExpr.addRight e.toNoMulTop.toStandard s := rfl
    have hR : (TwistExpr.addLeft e s).toStandard =
        StandardExpr.addRight e.toStandard s := rfl
    rw [hL, hR]
    cases s <;> simp [StandardExpr.fraction, ih]
  | mulBottom e s ih =>
    have hL : (toNoMulTop (TwistExpr.mulBottom e s)).toStandard =
        StandardExpr.mulBottom e.toNoMulTop.toStandard s := rfl
    have hR : (TwistExpr.mulBottom e s).toStandard =
        StandardExpr.mulBottom e.toStandard s := rfl
    rw [hL, hR]
    cases s <;> simp [StandardExpr.fraction, ih]
  | mulTop e s ih =>
    have hL : (toNoMulTop (TwistExpr.mulTop e s)).toStandard =
        StandardExpr.mulBottom e.toNoMulTop.toStandard s := rfl
    have hR : (TwistExpr.mulTop e s).toStandard =
        StandardExpr.mulBottom e.toStandard s := rfl
    rw [hL, hR]
    cases s <;> simp [StandardExpr.fraction, ih]

/-- Every twist expression isotopes to a `noMulTop` one with the same
    standard-form fraction: the diagram-level normal form for Theorem 3.
    Algebraic `TwistExpr.fraction` preservation is not claimed (see the
    file header). -/
theorem exists_noMulTop_isotopic (e : TwistExpr) :
    ∃ e' : TwistExpr, e'.noMulTop ∧ Isotopic e.diagram e'.diagram ∧
      e'.toStandard.fraction = e.toStandard.fraction :=
  ⟨e.toNoMulTop, e.toNoMulTop_noMulTop, e.toNoMulTop_isotopic,
    e.toNoMulTop_toStandard_fraction⟩

end TwistExpr

/-- Twist expressions whose every top product sits over an inner
    expression of fraction ±11 (the fixed points of inv!, where the
    Conway product commutes). On this subclass top products normalize
    without changing algebraic F. -/
def TwistExpr.unitMulTop : TwistExpr → Prop
  | zero | infinity | one | negOne => True
  | addRight e _ | addLeft e _ | mulBottom e _ => e.unitMulTop
  | mulTop e _ =>
      e.unitMulTop ∧ (e.fraction = 1 ∨ e.fraction = CFValue.ofInt (-1))

/-- Normalization preserves algebraic F on unitMulTop expressions:
    every constructor is congruent, and mulTop nodes use
    fraction_eq_toStandard_mulTop_of_unit_fraction via the inner
    ±1 hypothesis. -/
theorem TwistExpr.toNoMulTop_fraction_of_unitMulTop (e : TwistExpr) :
    e.unitMulTop → (toNoMulTop e).fraction = e.fraction := by
  induction e with
  | zero | infinity | one | negOne => intro _; rfl
  | addRight e s ih =>
    intro h
    have ihH := ih h
    simp only [TwistExpr.toNoMulTop, TwistExpr.fraction, ihH]
  | addLeft e s ih =>
    intro h
    have ihH := ih h
    simp only [TwistExpr.toNoMulTop, TwistExpr.fraction, ihH]
  | mulBottom e s ih =>
    intro h
    have ihH := ih h
    simp only [TwistExpr.toNoMulTop, TwistExpr.fraction, ihH]
  | mulTop e s ih =>
    intro h
    obtain ⟨ihu, hF⟩ := h
    have ihH := ih ihu
    calc (TwistExpr.mulBottom e.toNoMulTop s).fraction
        = (e.toNoMulTop.fraction.inv.add s.cfValue).inv := rfl
      _ = (e.fraction.inv.add s.cfValue).inv := by rw [ihH]
      _ = (s.cfValue.inv.add e.fraction).inv :=
          (TwistExpr.mulTop_comm_of_unit_fraction e s hF).symm
      _ = (TwistExpr.mulTop e s).fraction := rfl

/-- Normalization procedure for Theorem 3 on the subclass: every
    unitMulTop expression isotopes to a noMulTop one with identical
    algebraic F (hence isotopic diagrams by
    twist_same_fraction_isotopic_of_noMulTop). -/
theorem TwistExpr.exists_noMulTop_fraction_isotopic (e : TwistExpr)
    (h : e.unitMulTop) :
    ∃ eR : TwistExpr, eR.noMulTop ∧ Isotopic e.diagram eR.diagram ∧
      eR.fraction = e.fraction := by
  refine ⟨e.toNoMulTop, e.toNoMulTop_noMulTop, e.toNoMulTop_isotopic,
    e.toNoMulTop_fraction_of_unitMulTop h⟩


/-- Recolor a slideReady twist along toNoMulTop, preserving the color
    matrix. Congruence cases reuse coloring_add_left/coloring_mul_left;
    addLeft restricts and reglues directly (both sides stay left, the
    glue identification discharging by the port hypothesis); only mulTop
    flips sides, via the Figure 5 slide, recursion under rot180 (there
    and back by the double-rot180 trick), and a final glue. -/
theorem coloring_toNoMulTop (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int) (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum) :
    Exists (fun colR => e.toNoMulTop.diagram.IsColored colR ∧
      SameEndpointColors e.diagram e.toNoMulTop.diagram col colR) := by
  induction e generalizing col with
  | zero => exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | infinity => exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | one => exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | negOne => exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | addRight e s ih =>
    simp only [TwistExpr.toNoMulTop, TwistExpr.diagram, add_eq_add] at hc hdiag ⊢
    have hokR : e.slideReady := hok
    have hL : e.diagram.IsColored col := IsColored_add_left hc
    have hR : (crossingTangle s).IsColored
        (colorAddRight e.diagram (crossingTangle s) col) :=
      IsColored_add_right hc
    have hdiagL : (ColorMatrix.of e.diagram col).DiagonalSum :=
      ColorMatrix.DiagonalSum_left_of_add (crossingTangle_NW_ne_SW s) hdiag
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨colR, hcR, hsR⟩ := ih hokR col hL hdiagL
    obtain ⟨hcol, hsRR⟩ := coloring_add_left hL hR hcR hsR
    exact ⟨_, hcol, hsRR⟩
  | addLeft e s ih =>
    simp only [TwistExpr.toNoMulTop, TwistExpr.diagram, add_eq_add] at hc hdiag ⊢
    obtain ⟨hne, hokR⟩ := hok
    let U := crossingTangle s
    have hL : U.IsColored col := IsColored_add_left hc
    have hR : e.diagram.IsColored (colorAddRight U e.diagram col) :=
      IsColored_add_right hc
    have hdiagU : (ColorMatrix.of U col).DiagonalSum :=
      crossingTangle_diagonal_any s _ hL
    have hdiagR : (ColorMatrix.of e.diagram
        (colorAddRight U e.diagram col)).DiagonalSum :=
      ColorMatrix.DiagonalSum_right_of_add hne hdiag hdiagU
    obtain ⟨colR, hcR, hsR⟩ :=
      ih hokR (colorAddRight U e.diagram col) hR hdiagR
    obtain ⟨hcol, hsRR⟩ := coloring_add_right hL hR hcR hsR
      (fun h => (hne h).elim)
    exact ⟨_, hcol, hsRR⟩
  | mulBottom e s ih =>
    simp only [TwistExpr.toNoMulTop, TwistExpr.diagram, mul_eq_mul] at hc hdiag ⊢
    have hokR : e.slideReady := hok
    have hL : e.diagram.IsColored col := IsColored_mul_top hc
    have hR : (crossingTangle s).IsColored
        (colorMulBottom e.diagram (crossingTangle s) col) :=
      IsColored_mul_bottom hc
    have hdiagL : (ColorMatrix.of e.diagram col).DiagonalSum :=
      ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨colR, hcR, hsR⟩ := ih hokR col hL hdiagL
    obtain ⟨hcol, hsRR⟩ := coloring_mul_left hL hR hcR hsR
    exact ⟨_, hcol, hsRR⟩
  | mulTop e s ih =>
    simp only [TwistExpr.toNoMulTop, TwistExpr.diagram, mul_eq_mul] at hc hdiag ⊢
    obtain ⟨hne, hokR⟩ := hok
    let U := crossingTangle s
    obtain ⟨col1, hc1, hs1⟩ :=
      coloring_flype_slide_mul s e.diagram col hc hne hdiag
    have hdiag1 : (ColorMatrix.of (e.diagram.rot180.mul U) col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs1).symm hdiag
    have hT180 : e.diagram.rot180.IsColored col1 := IsColored_mul_top hc1
    have hU : U.IsColored (colorMulBottom e.diagram.rot180 U col1) :=
      IsColored_mul_bottom hc1
    have hdiagT180 : (ColorMatrix.of e.diagram.rot180 col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag1
        (crossingTangle_diagonal_any s _ hU)
    obtain ⟨col2, hc2, hs2⟩ :=
      coloring_rot180_diagonal e.diagram.rot180 col1 hT180 hdiagT180
    have hdiag2 : (ColorMatrix.of e.diagram.rot180.rot180 col2).DiagonalSum :=
      ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs2).symm
        hdiagT180
    have hc2e : e.diagram.IsColored col2 := by
      simpa [rot180_rot180] using hc2
    have hs2e : SameEndpointColors e.diagram.rot180 e.diagram col1 col2 := by
      simpa [rot180_rot180] using hs2
    have hdiag2e : (ColorMatrix.of e.diagram col2).DiagonalSum := by
      simpa [rot180_rot180] using hdiag2
    obtain ⟨col3, hc3, hs3⟩ := ih hokR col2 hc2e hdiag2e
    have hdiag3 : (ColorMatrix.of e.toNoMulTop.diagram col3).DiagonalSum :=
      ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs3).symm
        hdiag2e
    obtain ⟨col4, hc4, hs4⟩ :=
      coloring_rot180_diagonal e.toNoMulTop.diagram col3 hc3 hdiag3
    have hsame : SameEndpointColors e.diagram.rot180
        e.toNoMulTop.diagram.rot180 col1 col4 :=
      hs2e.trans (hs3.trans hs4)
    obtain ⟨hcol45, hs45⟩ := coloring_mul_left hT180 hU hc4 hsame
    have hdiag45 := ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs45).symm hdiag1
    have hT45 := IsColored_mul_top hcol45
    have hU45 := IsColored_mul_bottom hcol45
    have hdiagT45 := ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag45
        (crossingTangle_diagonal_any s _ hU45)
    obtain ⟨col5, hc5, hs5⟩ := coloring_rot180_diagonal e.toNoMulTop.diagram.rot180 _ hT45 hdiagT45
    have hc5e : e.toNoMulTop.diagram.IsColored col5 := by
      simpa [rot180_rot180] using hc5
    have hs5e := by simpa [rot180_rot180] using hs5
    obtain ⟨hcol6, hs6⟩ := coloring_mul_left hT45 hU45 hc5e hs5e
    exact ⟨_, hcol6, hs1.trans (hs45.trans hs6)⟩

/-- Every coloring fraction of a slideReady twist is a coloring
    fraction of its noMulTop normalization, at the same value. -/
theorem HasColoringFraction.toNoMulTop_slideReady (e : TwistExpr)
    (hok : e.slideReady) {v : CFValue}
    (h : HasColoringFraction e.diagram v) :
    HasColoringFraction e.toNoMulTop.diagram v := by
  obtain ⟨col, hc, hm, hf⟩ := h
  have hd := twist_coloring_diagonal_slideReady e hok col hc
  obtain ⟨colR, hcR, hsR⟩ := coloring_toNoMulTop e hok col hc hd
  have hM := ColorMatrix.of_sameEndpoint hsR
  refine ⟨colR, hcR, ?_, ?_⟩
  · simpa [hM] using hm
  · have hfR : (ColorMatrix.of e.toNoMulTop.diagram colR).fraction =
      (ColorMatrix.of e.diagram col).fraction := by
      rw [hM]
    exact hfR.trans hf


/-- Joint transport-and-value theorem: on slideReady unitMulTop
twists (independent axes — e.g. addLeft infinity pos is unitMulTop
with degenerate ports, so neither hypothesis is dropped), one
recoloring of the normalization preserves the matrix and both the
coloring and the algebraic fraction agree. Packages
coloring_toNoMulTop with toNoMulTop_fraction_of_unitMulTop. -/
theorem coloring_toNoMulTop_joint (e : TwistExpr)
    (hsr : e.slideReady) (hu : e.unitMulTop) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum) :
    Exists (fun colR => e.toNoMulTop.diagram.IsColored colR ∧
      SameEndpointColors e.diagram e.toNoMulTop.diagram col colR ∧
      (ColorMatrix.of e.toNoMulTop.diagram colR).fraction =
        (ColorMatrix.of e.diagram col).fraction ∧
      (TwistExpr.toNoMulTop e).fraction = e.fraction) := by
  obtain ⟨colR, hcR, hsR⟩ := coloring_toNoMulTop e hsr col hc hdiag
  have hM := ColorMatrix.of_sameEndpoint hsR
  have hfR : (ColorMatrix.of e.toNoMulTop.diagram colR).fraction =
      (ColorMatrix.of e.diagram col).fraction := by
    rw [hM]
  exact ⟨colR, hcR, hsR, hfR, e.toNoMulTop_fraction_of_unitMulTop hu⟩

/-- Joint carried-fraction version. -/
theorem HasColoringFraction.toNoMulTop_joint (e : TwistExpr)
    (hsr : e.slideReady) (hu : e.unitMulTop) {v : CFValue}
    (h : HasColoringFraction e.diagram v) :
    HasColoringFraction e.toNoMulTop.diagram v ∧
      (TwistExpr.toNoMulTop e).fraction = e.fraction := by
  obtain ⟨col, hc, hm, hf⟩ := h
  have hd := twist_coloring_diagonal_slideReady e hsr col hc
  obtain ⟨colR, hcR, hsR, hfR, hAlg⟩ :=
    coloring_toNoMulTop_joint e hsr hu col hc hd
  have hM := ColorMatrix.of_sameEndpoint hsR
  have hHCF : HasColoringFraction e.toNoMulTop.diagram v :=
    ⟨colR, hcR, by simpa [hM] using hm, by exact hfR.trans hf⟩
  exact ⟨hHCF, hAlg⟩


/-- Theorem 3 with colorings carried along, on slideReady twists with
    unit fractions: same algebraic fraction gives isotopic diagrams plus
    non-monochrome colorings of both carrying the common standard value
    (via colorFrom and unconditional f = F). The standard values agree
    through the normalized forms (noMulTop on both sides). -/
theorem twist_same_fraction_isotopic_with_colorings {e₁ e₂ : TwistExpr}
    (hsr₁ : e₁.slideReady) (hsr₂ : e₂.slideReady)
    (hu₁ : e₁.unitMulTop) (hu₂ : e₂.unitMulTop)
    (hf : e₁.fraction = e₂.fraction) :
    Exists (fun v => Isotopic e₁.diagram e₂.diagram ∧
      (Exists (fun col1 => e₁.diagram.IsColored col1 ∧
        (ColorMatrix.of e₁.diagram col1).NotMono ∧
        (ColorMatrix.of e₁.diagram col1).fraction = v)) ∧
      (Exists (fun col2 => e₂.diagram.IsColored col2 ∧
        (ColorMatrix.of e₂.diagram col2).NotMono ∧
        (ColorMatrix.of e₂.diagram col2).fraction = v))) := by
  have hfN : (TwistExpr.toNoMulTop e₁).fraction =
      (TwistExpr.toNoMulTop e₂).fraction :=
    (TwistExpr.toNoMulTop_fraction_of_unitMulTop e₁ hu₁).trans
      (hf.trans
        (TwistExpr.toNoMulTop_fraction_of_unitMulTop e₂ hu₂).symm)
  have hIso : Isotopic e₁.diagram e₂.diagram :=
    (TwistExpr.toNoMulTop_isotopic e₁).trans
      ((twist_same_fraction_isotopic_of_noMulTop
        (TwistExpr.toNoMulTop_noMulTop e₁)
        (TwistExpr.toNoMulTop_noMulTop e₂) hfN).trans
        (TwistExpr.toNoMulTop_isotopic e₂).symm)
  have hAgree : e₁.toStandard.fraction = e₂.toStandard.fraction := by
    have a1 := TwistExpr.fraction_eq_toStandard_of_noMulTop _
      (TwistExpr.toNoMulTop_noMulTop e₁)
    have a2 := TwistExpr.fraction_eq_toStandard_of_noMulTop _
      (TwistExpr.toNoMulTop_noMulTop e₂)
    have s1 := TwistExpr.toNoMulTop_toStandard_fraction e₁
    have s2 := TwistExpr.toNoMulTop_toStandard_fraction e₂
    exact s1.symm.trans (a1.symm.trans (hfN.trans (a2.trans s2)))
  refine ⟨e₁.toStandard.fraction, hIso, ?_, ?_⟩
  · refine ⟨e₁.colorFrom 0 1, e₁.colorFrom_isColored_slideReady hsr₁ 0 1,
      e₁.colorFrom_notMono_slideReady hsr₁, ?_⟩
    exact coloring_fraction_eq_F_any_slideReady e₁ hsr₁ _
      (e₁.colorFrom_isColored_slideReady hsr₁ 0 1)
      (e₁.colorFrom_notMono_slideReady hsr₁)
  · refine ⟨e₂.colorFrom 0 1, e₂.colorFrom_isColored_slideReady hsr₂ 0 1,
      e₂.colorFrom_notMono_slideReady hsr₂, ?_⟩
    have hcol := coloring_fraction_eq_F_any_slideReady e₂ hsr₂ _
      (e₂.colorFrom_isColored_slideReady hsr₂ 0 1)
      (e₂.colorFrom_notMono_slideReady hsr₂)
    rw [hAgree]
    exact hcol

end RationalTangles
