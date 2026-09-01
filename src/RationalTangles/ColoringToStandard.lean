/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColoringStandard

/-!
# Coloring the twist-form → standard-form construction

Transport of an integral coloring along the explicit steps of
`TwistExpr.toStandard_isotopic` (planar isotopy, `add`/`mul` congruence,
Figure 5 flype slides under `DiagonalSum`, and `coloring_rot180_diagonal`).
This does **not** color `Isotopic.invert_cong` (so not `lemma4_unit` /
continued-fraction form) and does **not** color `rot180_cong` of an
arbitrary `Isotopic` witness of `IsRational`.

`slideReady` excludes the PD-degenerate flype cases `t.NW = t.SW`
(addLeft of the `[∞]` family) and `t.NW = t.NE` (mulTop of the `[0]`
family), where `coloring_flype_slide_*` does not apply.
-/

namespace RationalTangles

theorem ColorMatrix.eq_of_sameEndpoint {D E : TangleDiagram} {col col' : Nat → Int}
    (h : SameEndpointColors D E col col') :
    ColorMatrix.of E col' = ColorMatrix.of D col :=
  ColorMatrix.of_sameEndpoint h

theorem ColorMatrix.DiagonalSum_of_eq {M N : ColorMatrix} (h : M = N)
    (hM : M.DiagonalSum) : N.DiagonalSum :=
  h ▸ hM

theorem ColorMatrix.NotMono_of_eq {M N : ColorMatrix} (h : M = N)
    (hM : M.NotMono) : N.NotMono :=
  h ▸ hM

/-- The left summand inherits `DiagonalSum` from a right-adjoined unit (or
    any right summand with `NW ≠ SW` that itself satisfies the rule). -/
theorem ColorMatrix.DiagonalSum_left_of_add {T S : TangleDiagram} {col : Nat → Int}
    (hSW : S.NW ≠ S.SW)
    (hSum : (ColorMatrix.of (T.add S) col).DiagonalSum)
    (hS : (ColorMatrix.of S (colorAddRight T S col)).DiagonalSum) :
    (ColorMatrix.of T col).DiagonalSum := by
  have hS' := hS
  rw [ColorMatrix.of_add_right T S col hSW] at hS'
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.add] at hSum hS' ⊢
  omega

/-- The right summand inherits `DiagonalSum` from the sum and the left. -/
theorem ColorMatrix.DiagonalSum_right_of_add {T S : TangleDiagram} {col : Nat → Int}
    (hSW : S.NW ≠ S.SW)
    (hSum : (ColorMatrix.of (T.add S) col).DiagonalSum)
    (hT : (ColorMatrix.of T col).DiagonalSum) :
    (ColorMatrix.of S (colorAddRight T S col)).DiagonalSum := by
  rw [ColorMatrix.of_add_right T S col hSW]
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.add] at hSum hT ⊢
  omega

theorem ColorMatrix.DiagonalSum_top_of_mul {T S : TangleDiagram} {col : Nat → Int}
    (hNE : S.NW ≠ S.NE)
    (hSum : (ColorMatrix.of (T.mul S) col).DiagonalSum)
    (hS : (ColorMatrix.of S (colorMulBottom T S col)).DiagonalSum) :
    (ColorMatrix.of T col).DiagonalSum := by
  have hS' := hS
  rw [ColorMatrix.of_mul_bottom T S col hNE] at hS'
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.mul] at hSum hS' ⊢
  omega

/-- Inner twist diagrams for which every Figure 5 slide in `toStandard`
    meets the `hne` hypothesis of `coloring_flype_slide_*`. -/
def TwistExpr.slideReady : TwistExpr → Prop
  | zero | infinity | one | negOne => True
  | addRight e _ | mulBottom e _ => e.slideReady
  | addLeft e _ => e.diagram.NW ≠ e.diagram.SW ∧ e.slideReady
  | mulTop e _ => e.diagram.NW ≠ e.diagram.NE ∧ e.slideReady

theorem ColorMatrix.DiagonalSum_of_rot180 (T : TangleDiagram) (col : Nat → Int)
    (h : (ColorMatrix.of T col).DiagonalSum) :
    (ColorMatrix.of T.rot180 col).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.rot180] at h ⊢
  omega

/-- Restricted coloring of `T.rot180` for a twist-form diagram, under
    `DiagonalSum` (the coloring-honest content of Lemma 2 (i) on the
    explicit twist PD-code). -/
theorem coloring_twist_rot180 (e : TwistExpr) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum) :
    ∃ col', e.diagram.rot180.IsColored col' ∧
      ColorMatrix.of e.diagram.rot180 col' = ColorMatrix.of e.diagram col ∧
      (ColorMatrix.of e.diagram.rot180 col').fraction =
        (ColorMatrix.of e.diagram col).fraction :=
  coloring_fraction_rot180_diagonal e.diagram col hc hdiag

/-- `[±1]+t` and `t+[±1]` have the same color matrix, via the Figure 5
    slide and `coloring_rot180_diagonal` on `t` (the two steps of
    `toStandard_isotopic` for `addLeft`). -/
theorem coloring_commute_add (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW)
    (hdiag : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum) :
    ∃ col', (t.add (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).add t)
        (t.add (crossingTangle s)) col col' := by
  let U := crossingTangle s
  obtain ⟨col1, hc1, hs1⟩ := coloring_flype_slide_add s t col hc hne hdiag
  have hdiag1 : (ColorMatrix.of (t.rot180.add U) col1).DiagonalSum := by
    exact ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs1).symm hdiag
  have hU : U.IsColored (colorAddRight t.rot180 U col1) := IsColored_add_right hc1
  have hdiagL : (ColorMatrix.of t.rot180 col1).DiagonalSum :=
    ColorMatrix.DiagonalSum_left_of_add (crossingTangle_NW_ne_SW s) hdiag1
      (crossingTangle_diagonal_any s _ hU)
  obtain ⟨col2, hc2, hs2⟩ :=
    coloring_rot180_diagonal t.rot180 col1 (IsColored_add_left hc1) hdiagL
  have hc2t : t.IsColored col2 := by
    simpa [rot180_rot180] using hc2
  have hs2t : SameEndpointColors t.rot180 t col1 col2 := by
    simpa [rot180_rot180] using hs2
  obtain ⟨hcol, hs3⟩ :=
    coloring_add_left (IsColored_add_left hc1) hU hc2t hs2t
  exact ⟨_, hcol, hs1.trans hs3⟩

/-- `[±1]*t` and `t*[±1]` have the same color matrix, via the Figure 5
    slide and `coloring_rot180_diagonal` on `t`. -/
theorem coloring_commute_mul (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE)
    (hdiag : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum) :
    ∃ col', (t.mul (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).mul t)
        (t.mul (crossingTangle s)) col col' := by
  let U := crossingTangle s
  obtain ⟨col1, hc1, hs1⟩ := coloring_flype_slide_mul s t col hc hne hdiag
  have hdiag1 : (ColorMatrix.of (t.rot180.mul U) col1).DiagonalSum := by
    exact ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs1).symm hdiag
  have hU : U.IsColored (colorMulBottom t.rot180 U col1) := IsColored_mul_bottom hc1
  have hdiagL : (ColorMatrix.of t.rot180 col1).DiagonalSum :=
    ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag1
      (crossingTangle_diagonal_any s _ hU)
  obtain ⟨col2, hc2, hs2⟩ :=
    coloring_rot180_diagonal t.rot180 col1 (IsColored_mul_top hc1) hdiagL
  have hc2t : t.IsColored col2 := by
    simpa [rot180_rot180] using hc2
  have hs2t : SameEndpointColors t.rot180 t col1 col2 := by
    simpa [rot180_rot180] using hs2
  obtain ⟨hcol, hs3⟩ :=
    coloring_mul_left (IsColored_mul_top hc1) hU hc2t hs2t
  exact ⟨_, hcol, hs1.trans hs3⟩

theorem coloring_one_toStandard (col : Nat → Int) (hc : one.IsColored col) :
    ∃ col', (StandardExpr.addRight .zero .pos).diagram.IsColored col' ∧
      SameEndpointColors one (StandardExpr.addRight .zero .pos).diagram col col' :=
  coloring_ColoringIsotopy (.isotopy planar_one_zero_add) col hc

theorem coloring_negOne_toStandard (col : Nat → Int) (hc : negOne.IsColored col) :
    ∃ col', (StandardExpr.addRight .zero .neg).diagram.IsColored col' ∧
      SameEndpointColors negOne (StandardExpr.addRight .zero .neg).diagram col col' :=
  coloring_ColoringIsotopy (.isotopy planar_negOne_zero_add) col hc

/-- Recolor a `slideReady` twist-form diagram along `toStandard`, preserving
    the color matrix (hence `f`). -/
theorem coloring_toStandard (e : TwistExpr) (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum) :
    ∃ col', e.toStandard.diagram.IsColored col' ∧
      SameEndpointColors e.diagram e.toStandard.diagram col col' := by
  induction e generalizing col with
  | zero =>
    exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | infinity =>
    exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | one =>
    simpa [TwistExpr.diagram, TwistExpr.toStandard] using coloring_one_toStandard col hc
  | negOne =>
    simpa [TwistExpr.diagram, TwistExpr.toStandard] using coloring_negOne_toStandard col hc
  | addRight e s ih =>
    simp only [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram] at hc hdiag ⊢
    have hok : e.slideReady := hok
    have hL : e.diagram.IsColored col := IsColored_add_left hc
    have hR : (crossingTangle s).IsColored (colorAddRight e.diagram (crossingTangle s) col) :=
      IsColored_add_right hc
    have hdiagL : (ColorMatrix.of e.diagram col).DiagonalSum :=
      ColorMatrix.DiagonalSum_left_of_add (crossingTangle_NW_ne_SW s) hdiag
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨col', hc', hs⟩ := ih hok col hL hdiagL
    obtain ⟨hcol, hs'⟩ := coloring_add_left hL hR hc' hs
    exact ⟨_, hcol, hs'⟩
  | mulBottom e s ih =>
    simp only [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram] at hc hdiag ⊢
    have hok : e.slideReady := hok
    have hL : e.diagram.IsColored col := IsColored_mul_top hc
    have hR : (crossingTangle s).IsColored (colorMulBottom e.diagram (crossingTangle s) col) :=
      IsColored_mul_bottom hc
    have hdiagL : (ColorMatrix.of e.diagram col).DiagonalSum :=
      ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨col', hc', hs⟩ := ih hok col hL hdiagL
    obtain ⟨hcol, hs'⟩ := coloring_mul_left hL hR hc' hs
    exact ⟨_, hcol, hs'⟩
  | addLeft e s ih =>
    simp only [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram] at hc hdiag ⊢
    obtain ⟨hne, hok⟩ := hok
    obtain ⟨col1, hc1, hs1⟩ :=
      coloring_commute_add s e.diagram col hc hne hdiag
    have hL : e.diagram.IsColored col1 := IsColored_add_left hc1
    have hR : (crossingTangle s).IsColored
        (colorAddRight e.diagram (crossingTangle s) col1) :=
      IsColored_add_right hc1
    have hdiag1 : (ColorMatrix.of (e.diagram.add (crossingTangle s)) col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs1).symm hdiag
    have hdiagL : (ColorMatrix.of e.diagram col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_left_of_add (crossingTangle_NW_ne_SW s) hdiag1
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨col', hc', hs⟩ := ih hok col1 hL hdiagL
    obtain ⟨hcol, hs'⟩ := coloring_add_left hL hR hc' hs
    exact ⟨_, hcol, hs1.trans hs'⟩
  | mulTop e s ih =>
    simp only [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram] at hc hdiag ⊢
    obtain ⟨hne, hok⟩ := hok
    obtain ⟨col1, hc1, hs1⟩ :=
      coloring_commute_mul s e.diagram col hc hne hdiag
    have hL : e.diagram.IsColored col1 := IsColored_mul_top hc1
    have hR : (crossingTangle s).IsColored
        (colorMulBottom e.diagram (crossingTangle s) col1) :=
      IsColored_mul_bottom hc1
    have hdiag1 : (ColorMatrix.of (e.diagram.mul (crossingTangle s)) col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_of_eq (ColorMatrix.of_sameEndpoint hs1).symm hdiag
    have hdiagL : (ColorMatrix.of e.diagram col1).DiagonalSum :=
      ColorMatrix.DiagonalSum_top_of_mul (crossingTangle_NW_ne_NE s) hdiag1
        (crossingTangle_diagonal_any s _ hR)
    obtain ⟨col', hc', hs⟩ := ih hok col1 hL hdiagL
    obtain ⟨hcol, hs'⟩ := coloring_mul_left hL hR hc' hs
    exact ⟨_, hcol, hs1.trans hs'⟩

/-- A non-monochrome coloring of a `slideReady` twist-form diagram has the
    same coloring fraction as the arithmetical fraction of its standard
    expression. -/
theorem coloring_fraction_toStandard (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.toStandard.fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_toStandard e hok col hc hdiag
  have hM := ColorMatrix.of_sameEndpoint hs
  have hm' : (ColorMatrix.of e.toStandard.diagram col').NotMono :=
    ColorMatrix.NotMono_of_eq hM.symm hm
  have hf := standard_fraction_any_coloring e.toStandard col' hc' hm'
  exact (hM ▸ rfl : (ColorMatrix.of e.diagram col).fraction =
      (ColorMatrix.of e.toStandard.diagram col').fraction).trans hf

end RationalTangles
