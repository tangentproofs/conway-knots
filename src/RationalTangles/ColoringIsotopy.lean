/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.ColoringFlype
import RationalTangles.ColorFraction

/-!
# Coloring and `f` along `ColoringIsotopy`

Transport of an integral coloring (preserving endpoint colors, hence the
color matrix and coloring fraction) along coloring-ready generators.

This does **not** give invariance of `f` along `Isotopic`.
-/

namespace RationalTangles

theorem ColorMatrix.of_sameEndpoint {D E : TangleDiagram} {col col' : Nat → Int}
    (h : SameEndpointColors D E col col') :
    ColorMatrix.of E col' = ColorMatrix.of D col := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := h
  simp [ColorMatrix.of, hNW, hNE, hSE, hSW]

/-! ## Glue colorings of `add` and `mul` -/

def colorGlueAdd (T : TangleDiagram) (_S : TangleDiagram) (colT colS : Nat → Int)
    (a : Nat) : Int :=
  if T.maxArc < a then colS (a - (T.maxArc + 1)) else colT a

def colorGlueMul (T : TangleDiagram) (_S : TangleDiagram) (colT colS : Nat → Int)
    (a : Nat) : Int :=
  if T.maxArc < a then colS (a - (T.maxArc + 1)) else colT a

theorem colorGlueAdd_of_le (T S : TangleDiagram) (colT colS : Nat → Int) {a : Nat}
    (ha : a ≤ T.maxArc) :
    colorGlueAdd T S colT colS a = colT a := by
  have : ¬ T.maxArc < a := Nat.not_lt.mpr ha
  simp [colorGlueAdd, this]

theorem colorGlueMul_of_le (T S : TangleDiagram) (colT colS : Nat → Int) {a : Nat}
    (ha : a ≤ T.maxArc) :
    colorGlueMul T S colT colS a = colT a := by
  have : ¬ T.maxArc < a := Nat.not_lt.mpr ha
  simp [colorGlueMul, this]

theorem colorGlueAdd_comp_shift (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNE : colT T.NE = colS S.NW)
    (hSE : colT T.SE = colS S.SW ∨ S.NW = S.SW) (b : Nat) :
    colorGlueAdd T S colT colS (addGlue T S (b + (T.maxArc + 1))) = colS b := by
  rw [addGlue_shift_eq]
  by_cases hNW : b = S.NW
  · simp [hNW]
    have hle : T.NE ≤ T.maxArc := maxArc_ge_NE T
    rw [colorGlueAdd_of_le T S colT colS hle, hNE]
  · by_cases hSW : b = S.SW
    · simp [hSW]
      have hle : T.SE ≤ T.maxArc := maxArc_ge_SE T
      have hne : S.NW ≠ S.SW := fun h => hNW (h ▸ hSW)
      have hse' : colT T.SE = colS S.SW := by
        rcases hSE with h | h
        · exact h
        · exact (hne h).elim
      simp [Ne.symm hne]
      rw [colorGlueAdd_of_le T S colT colS hle, hse']
    · have hlt : T.maxArc < b + (T.maxArc + 1) := by omega
      simp [hNW, hSW, colorGlueAdd, hlt]

theorem colorGlueMul_comp_shift (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNW : colT T.SW = colS S.NW)
    (hNE : colT T.SE = colS S.NE ∨ S.NW = S.NE) (b : Nat) :
    colorGlueMul T S colT colS (mulGlue T S (b + (T.maxArc + 1))) = colS b := by
  rw [mulGlue_shift_eq]
  by_cases hNWs : b = S.NW
  · simp [hNWs]
    have hle : T.SW ≤ T.maxArc := maxArc_ge_SW T
    rw [colorGlueMul_of_le T S colT colS hle, hNW]
  · by_cases hNEs : b = S.NE
    · simp [hNEs]
      have hle : T.SE ≤ T.maxArc := maxArc_ge_SE T
      have hne : S.NW ≠ S.NE := fun h => hNWs (h ▸ hNEs)
      have hne' : colT T.SE = colS S.NE := by
        rcases hNE with h | h
        · exact h
        · exact (hne h).elim
      simp [Ne.symm hne]
      rw [colorGlueMul_of_le T S colT colS hle, hne']
    · have hlt : T.maxArc < b + (T.maxArc + 1) := by omega
      simp [hNWs, hNEs, colorGlueMul, hlt]

theorem IsColored_colorGlueAdd (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (hNE : colT T.NE = colS S.NW)
    (hSE : colT T.SE = colS S.SW ∨ S.NW = S.SW) :
    (T.add S).IsColored (colorGlueAdd T S colT colS) := by
  intro C hC
  rw [add_crossings_append, List.mem_append] at hC
  rcases hC with hC | hC
  · have hle := arc_le_maxArc_of_mem T hC
    exact ColoringRule_congr
      (colorGlueAdd_of_le T S colT colS hle.1)
      (colorGlueAdd_of_le T S colT colS hle.2.1)
      (colorGlueAdd_of_le T S colT colS hle.2.2.1)
      (colorGlueAdd_of_le T S colT colS hle.2.2.2)
      (hT C hC)
  · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
    rw [ColoringRule_rename]
    have hfun :
        colorGlueAdd T S colT colS ∘ addGlue T S ∘ addShift T = colS := by
      funext b
      simpa [Function.comp, addShift] using
        colorGlueAdd_comp_shift T S colT colS hNE hSE b
    simpa [hfun] using hS C0 hC0

theorem IsColored_colorGlueMul (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (hSW : colT T.SW = colS S.NW)
    (hSE : colT T.SE = colS S.NE ∨ S.NW = S.NE) :
    (T.mul S).IsColored (colorGlueMul T S colT colS) := by
  intro C hC
  rw [mul_crossings_append, List.mem_append] at hC
  rcases hC with hC | hC
  · have hle := arc_le_maxArc_of_mem T hC
    exact ColoringRule_congr
      (colorGlueMul_of_le T S colT colS hle.1)
      (colorGlueMul_of_le T S colT colS hle.2.1)
      (colorGlueMul_of_le T S colT colS hle.2.2.1)
      (colorGlueMul_of_le T S colT colS hle.2.2.2)
      (hT C hC)
  · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
    rw [ColoringRule_rename]
    have hfun :
        colorGlueMul T S colT colS ∘ mulGlue T S ∘ addShift T = colS := by
      funext b
      simpa [Function.comp, addShift] using
        colorGlueMul_comp_shift T S colT colS hSW hSE b
    simpa [hfun] using hS C0 hC0

theorem add_NE (T S : TangleDiagram) :
    (T.add S).NE = addGlue T S (S.NE + (T.maxArc + 1)) := by
  simp [TangleDiagram.add, TangleDiagram.rename, addGlue]

theorem add_SE (T S : TangleDiagram) :
    (T.add S).SE = addGlue T S (S.SE + (T.maxArc + 1)) := by
  simp [TangleDiagram.add, TangleDiagram.rename, addGlue]

theorem mul_SE_glue (T S : TangleDiagram) :
    (T.mul S).SE = mulGlue T S (S.SE + (T.maxArc + 1)) := by
  simp [TangleDiagram.mul, TangleDiagram.rename, mulGlue]

theorem mul_SW_glue (T S : TangleDiagram) :
    (T.mul S).SW = mulGlue T S (S.SW + (T.maxArc + 1)) := by
  simp [TangleDiagram.mul, TangleDiagram.rename, mulGlue]

theorem colorAddRight_NW (T S : TangleDiagram) (col : Nat → Int) :
    colorAddRight T S col S.NW = col T.NE := by
  simp [colorAddRight, addShift, addGlue_NW]

theorem colorAddRight_SW (T S : TangleDiagram) (col : Nat → Int) :
    colorAddRight T S col S.SW = col T.SE ∨ S.NW = S.SW := by
  by_cases h : S.NW = S.SW
  · exact Or.inr h
  · left
    have hne : ¬ S.SW = S.NW := fun eq => h eq.symm
    simp [colorAddRight, addShift, addGlue_shift_eq, hne]

theorem colorMulBottom_NW (T S : TangleDiagram) (col : Nat → Int) :
    colorMulBottom T S col S.NW = col T.SW := by
  simp [colorMulBottom, addShift, mulGlue_NW]

theorem colorMulBottom_NE (T S : TangleDiagram) (col : Nat → Int) :
    colorMulBottom T S col S.NE = col T.SE ∨ S.NW = S.NE := by
  by_cases h : S.NW = S.NE
  · exact Or.inr h
  · left
    have hne : ¬ S.NE = S.NW := fun eq => h eq.symm
    simp [colorMulBottom, addShift, mulGlue_shift_eq, hne]

theorem colorAddRight_NE (T S : TangleDiagram) (col : Nat → Int) :
    colorAddRight T S col S.NE = col (T.add S).NE := by
  simp [colorAddRight, addShift, add_NE]

theorem colorAddRight_SE (T S : TangleDiagram) (col : Nat → Int) :
    colorAddRight T S col S.SE = col (T.add S).SE := by
  simp [colorAddRight, addShift, add_SE]

theorem colorMulBottom_SE (T S : TangleDiagram) (col : Nat → Int) :
    colorMulBottom T S col S.SE = col (T.mul S).SE := by
  simp [colorMulBottom, addShift, mul_SE_glue]

theorem colorMulBottom_SW (T S : TangleDiagram) (col : Nat → Int) :
    colorMulBottom T S col S.SW = col (T.mul S).SW := by
  simp [colorMulBottom, addShift, mul_SW_glue]

theorem coloring_add_left {T T' S : TangleDiagram} {col colT' : Nat → Int}
    (_hT : T.IsColored col) (hS : S.IsColored (colorAddRight T S col))
    (hT' : T'.IsColored colT')
    (hsame : SameEndpointColors T T' col colT') :
    (T'.add S).IsColored (colorGlueAdd T' S colT' (colorAddRight T S col)) ∧
      SameEndpointColors (T.add S) (T'.add S) col
        (colorGlueAdd T' S colT' (colorAddRight T S col)) := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := hsame
  have glueNE : colT' T'.NE = colorAddRight T S col S.NW := by
    rw [hNE, colorAddRight_NW]
  have glueSE : colT' T'.SE = colorAddRight T S col S.SW ∨ S.NW = S.SW := by
    rcases colorAddRight_SW T S col with h | h
    · exact Or.inl (hSE.trans h.symm)
    · exact Or.inr h
  have hcol :
      (T'.add S).IsColored (colorGlueAdd T' S colT' (colorAddRight T S col)) :=
    IsColored_colorGlueAdd T' S colT' (colorAddRight T S col) hT' hS glueNE glueSE
  refine ⟨hcol, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueAdd T' S colT' (colorAddRight T S col) T'.NW = col T.NW
    rw [colorGlueAdd_of_le T' S colT' (colorAddRight T S col) (maxArc_ge_NW T'), hNW]
  · have h1 : colorGlueAdd T' S colT' (colorAddRight T S col) (T'.add S).NE =
        colorAddRight T S col S.NE := by
      rw [add_NE T']
      exact colorGlueAdd_comp_shift T' S colT' (colorAddRight T S col) glueNE glueSE S.NE
    rw [h1, colorAddRight_NE]
  · have h1 : colorGlueAdd T' S colT' (colorAddRight T S col) (T'.add S).SE =
        colorAddRight T S col S.SE := by
      rw [add_SE T']
      exact colorGlueAdd_comp_shift T' S colT' (colorAddRight T S col) glueNE glueSE S.SE
    rw [h1, colorAddRight_SE]
  · change colorGlueAdd T' S colT' (colorAddRight T S col) T'.SW = col T.SW
    rw [colorGlueAdd_of_le T' S colT' (colorAddRight T S col) (maxArc_ge_SW T'), hSW]

theorem coloring_add_right {T S S' : TangleDiagram} {col colS' : Nat → Int}
    (hT : T.IsColored col) (_hS : S.IsColored (colorAddRight T S col))
    (hS' : S'.IsColored colS')
    (hsame : SameEndpointColors S S' (colorAddRight T S col) colS')
    (hglue : S.NW = S.SW → S'.NW = S'.SW) :
    (T.add S').IsColored (colorGlueAdd T S' col colS') ∧
      SameEndpointColors (T.add S) (T.add S') col
        (colorGlueAdd T S' col colS') := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := hsame
  have glueNE : col T.NE = colS' S'.NW := by
    rw [hNW, colorAddRight_NW]
  have glueSE : col T.SE = colS' S'.SW ∨ S'.NW = S'.SW := by
    by_cases h' : S'.NW = S'.SW
    · exact Or.inr h'
    · left
      have hne : S.NW ≠ S.SW := fun h => h' (hglue h)
      have hEq : colorAddRight T S col S.SW = col T.SE := by
        unfold colorAddRight addShift
        rw [addGlue_shift_eq]
        simp [hne.symm]
      exact (hSW.trans hEq).symm
  have hcol : (T.add S').IsColored (colorGlueAdd T S' col colS') :=
    IsColored_colorGlueAdd T S' col colS' hT hS' glueNE glueSE
  refine ⟨hcol, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueAdd T S' col colS' T.NW = col T.NW
    rw [colorGlueAdd_of_le T S' col colS' (maxArc_ge_NW T)]
  · have h1 : colorGlueAdd T S' col colS' (T.add S').NE = colS' S'.NE := by
      rw [add_NE T S']
      exact colorGlueAdd_comp_shift T S' col colS' glueNE glueSE S'.NE
    rw [h1, hNE, colorAddRight_NE]
  · have h1 : colorGlueAdd T S' col colS' (T.add S').SE = colS' S'.SE := by
      rw [add_SE T S']
      exact colorGlueAdd_comp_shift T S' col colS' glueNE glueSE S'.SE
    rw [h1, hSE, colorAddRight_SE]
  · change colorGlueAdd T S' col colS' T.SW = col T.SW
    rw [colorGlueAdd_of_le T S' col colS' (maxArc_ge_SW T)]

theorem coloring_mul_left {T T' S : TangleDiagram} {col colT' : Nat → Int}
    (_hT : T.IsColored col) (hS : S.IsColored (colorMulBottom T S col))
    (hT' : T'.IsColored colT')
    (hsame : SameEndpointColors T T' col colT') :
    (T'.mul S).IsColored (colorGlueMul T' S colT' (colorMulBottom T S col)) ∧
      SameEndpointColors (T.mul S) (T'.mul S) col
        (colorGlueMul T' S colT' (colorMulBottom T S col)) := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := hsame
  have glueNW : colT' T'.SW = colorMulBottom T S col S.NW := by
    rw [hSW, colorMulBottom_NW]
  have glueNE : colT' T'.SE = colorMulBottom T S col S.NE ∨ S.NW = S.NE := by
    rcases colorMulBottom_NE T S col with h | h
    · exact Or.inl (hSE.trans h.symm)
    · exact Or.inr h
  have hcol :
      (T'.mul S).IsColored (colorGlueMul T' S colT' (colorMulBottom T S col)) :=
    IsColored_colorGlueMul T' S colT' (colorMulBottom T S col) hT' hS glueNW glueNE
  refine ⟨hcol, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueMul T' S colT' (colorMulBottom T S col) T'.NW = col T.NW
    rw [colorGlueMul_of_le T' S colT' (colorMulBottom T S col) (maxArc_ge_NW T'), hNW]
  · change colorGlueMul T' S colT' (colorMulBottom T S col) T'.NE = col T.NE
    rw [colorGlueMul_of_le T' S colT' (colorMulBottom T S col) (maxArc_ge_NE T'), hNE]
  · have h1 : colorGlueMul T' S colT' (colorMulBottom T S col) (T'.mul S).SE =
        colorMulBottom T S col S.SE := by
      rw [mul_SE_glue T']
      exact colorGlueMul_comp_shift T' S colT' (colorMulBottom T S col) glueNW glueNE S.SE
    rw [h1, colorMulBottom_SE]
  · have h1 : colorGlueMul T' S colT' (colorMulBottom T S col) (T'.mul S).SW =
        colorMulBottom T S col S.SW := by
      rw [mul_SW_glue T']
      exact colorGlueMul_comp_shift T' S colT' (colorMulBottom T S col) glueNW glueNE S.SW
    rw [h1, colorMulBottom_SW]

theorem coloring_mul_right {T S S' : TangleDiagram} {col colS' : Nat → Int}
    (hT : T.IsColored col) (_hS : S.IsColored (colorMulBottom T S col))
    (hS' : S'.IsColored colS')
    (hsame : SameEndpointColors S S' (colorMulBottom T S col) colS')
    (hglue : S.NW = S.NE → S'.NW = S'.NE) :
    (T.mul S').IsColored (colorGlueMul T S' col colS') ∧
      SameEndpointColors (T.mul S) (T.mul S') col
        (colorGlueMul T S' col colS') := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := hsame
  have glueNW : col T.SW = colS' S'.NW := by
    rw [hNW, colorMulBottom_NW]
  have glueNE : col T.SE = colS' S'.NE ∨ S'.NW = S'.NE := by
    by_cases h' : S'.NW = S'.NE
    · exact Or.inr h'
    · left
      have hne : S.NW ≠ S.NE := fun h => h' (hglue h)
      have hEq : colorMulBottom T S col S.NE = col T.SE := by
        unfold colorMulBottom addShift
        rw [mulGlue_shift_eq]
        simp [hne.symm]
      exact (hNE.trans hEq).symm
  have hcol : (T.mul S').IsColored (colorGlueMul T S' col colS') :=
    IsColored_colorGlueMul T S' col colS' hT hS' glueNW glueNE
  refine ⟨hcol, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueMul T S' col colS' T.NW = col T.NW
    rw [colorGlueMul_of_le T S' col colS' (maxArc_ge_NW T)]
  · change colorGlueMul T S' col colS' T.NE = col T.NE
    rw [colorGlueMul_of_le T S' col colS' (maxArc_ge_NE T)]
  · have h1 : colorGlueMul T S' col colS' (T.mul S').SE = colS' S'.SE := by
      rw [mul_SE_glue T S']
      exact colorGlueMul_comp_shift T S' col colS' glueNW glueNE S'.SE
    rw [h1, hSE, colorMulBottom_SE]
  · have h1 : colorGlueMul T S' col colS' (T.mul S').SW = colS' S'.SW := by
      rw [mul_SW_glue T S']
      exact colorGlueMul_comp_shift T S' col colS' glueNW glueNE S'.SW
    rw [h1, hSW, colorMulBottom_SW]

/-- Recolor after a coloring-ready isotopy so that endpoint colors (hence
    the color matrix and coloring fraction) are unchanged. -/
theorem coloring_ColoringIsotopy {D E : TangleDiagram}
    (h : ColoringIsotopy D E) (col : Nat → Int) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  induction h generalizing col with
  | refl D => exact ⟨col, hc, rfl, rfl, rfl, rfl⟩
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨col1, hc1, hs1⟩ := ih1 col hc
    obtain ⟨col2, hc2, hs2⟩ := ih2 col1 hc1
    exact ⟨col2, hc2, hs1.trans hs2⟩
  | r1 hrm hwD hwE =>
    exact coloring_IsReidemeisterI _ _ col hrm hc hwD hwE
  | r2 hrm hwD hwE =>
    exact coloring_IsReidemeisterII _ _ col hrm hc hwD hwE
  | r3Local hrm =>
    exact coloring_IsReidemeisterIIILocal _ _ col hrm hc
  | localFlype hrm =>
    exact coloring_IsLocalFlype _ _ col hrm hc
  | isotopy hrm =>
    exact coloring_planar_isotopy _ _ col hrm hc
  | add_left h ih =>
    obtain ⟨colT', hT', hs⟩ := ih col (IsColored_add_left hc)
    obtain ⟨hcol, hs'⟩ :=
      coloring_add_left (IsColored_add_left hc) (IsColored_add_right hc) hT' hs
    exact ⟨_, hcol, hs'⟩
  | add_right h hglue ih =>
    obtain ⟨colS', hS', hs⟩ := ih (colorAddRight _ _ col) (IsColored_add_right hc)
    obtain ⟨hcol, hs'⟩ :=
      coloring_add_right (IsColored_add_left hc) (IsColored_add_right hc) hS' hs hglue
    exact ⟨_, hcol, hs'⟩
  | mul_left h ih =>
    obtain ⟨colT', hT', hs⟩ := ih col (IsColored_mul_top hc)
    obtain ⟨hcol, hs'⟩ :=
      coloring_mul_left (IsColored_mul_top hc) (IsColored_mul_bottom hc) hT' hs
    exact ⟨_, hcol, hs'⟩
  | mul_right h hglue ih =>
    obtain ⟨colS', hS', hs⟩ := ih (colorMulBottom _ _ col) (IsColored_mul_bottom hc)
    obtain ⟨hcol, hs'⟩ :=
      coloring_mul_right (IsColored_mul_top hc) (IsColored_mul_bottom hc) hS' hs hglue
    exact ⟨_, hcol, hs'⟩

/-- Indexed Reidemeister III is a coloring-ready move, via the local model. -/
theorem ColoringIsotopy.of_IsReidemeisterIII {D E : TangleDiagram}
    (h : IsReidemeisterIII D E) : ColoringIsotopy D E :=
  .r3Local h.toLocal

/-- The color matrix (hence `f`) is unchanged along `ColoringIsotopy`. -/
theorem coloring_fraction_ColoringIsotopy {D E : TangleDiagram}
    (h : ColoringIsotopy D E) (col : Nat → Int) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧
      ColorMatrix.of E col' = ColorMatrix.of D col ∧
      (ColorMatrix.of E col').fraction = (ColorMatrix.of D col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_ColoringIsotopy h col hc
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

end RationalTangles
