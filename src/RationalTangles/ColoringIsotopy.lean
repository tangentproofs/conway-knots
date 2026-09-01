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

/-- Restriction of a glue coloring of `T.add S` recovers the right-hand coloring. -/
theorem colorAddRight_colorGlueAdd (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNE : colT T.NE = colS S.NW)
    (hSE : colT T.SE = colS S.SW ∨ S.NW = S.SW) :
    colorAddRight T S (colorGlueAdd T S colT colS) = colS := by
  funext b
  simpa [colorAddRight, addShift] using
    colorGlueAdd_comp_shift T S colT colS hNE hSE b

/-- Restriction of a glue coloring of `T.mul S` recovers the bottom coloring. -/
theorem colorMulBottom_colorGlueMul (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNW : colT T.SW = colS S.NW)
    (hNE : colT T.SE = colS S.NE ∨ S.NW = S.NE) :
    colorMulBottom T S (colorGlueMul T S colT colS) = colS := by
  funext b
  simpa [colorMulBottom, addShift] using
    colorGlueMul_comp_shift T S colT colS hNW hNE b

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

/-- Reverse of `coloring_add_right`. Restriction `colorAddRight` recovers the
    right-hand coloring of `T.add S'`. Gluing a matching coloring of `S`
    back onto `T` needs the converse identification
    `S'.NW = S'.SW → S.NW = S.SW`. Without it, `S'.NW = S'.SW` and
    `S.NW ≠ S.SW` would force `col T.SE = col T.NE`, which is false in
    general. -/
theorem coloring_add_right_rev {T S S' : TangleDiagram} {col colS : Nat → Int}
    (hT : T.IsColored col) (hS' : S'.IsColored (colorAddRight T S' col))
    (hS : S.IsColored colS)
    (hsame : SameEndpointColors S' S (colorAddRight T S' col) colS)
    (hglue : S'.NW = S'.SW → S.NW = S.SW) :
    (T.add S).IsColored (colorGlueAdd T S col colS) ∧
      SameEndpointColors (T.add S') (T.add S) col
        (colorGlueAdd T S col colS) :=
  coloring_add_right hT hS' hS hsame hglue

/-- Reverse of `coloring_mul_right`. Restriction `colorMulBottom` recovers the
    bottom coloring of `T.mul S'`. Gluing a matching coloring of `S` back
    onto `T` needs the converse identification
    `S'.NW = S'.NE → S.NW = S.NE`. Without it, `S'.NW = S'.NE` and
    `S.NW ≠ S.NE` would force `col T.SE = col T.SW`, which is false in
    general. -/
theorem coloring_mul_right_rev {T S S' : TangleDiagram} {col colS : Nat → Int}
    (hT : T.IsColored col) (hS' : S'.IsColored (colorMulBottom T S' col))
    (hS : S.IsColored colS)
    (hsame : SameEndpointColors S' S (colorMulBottom T S' col) colS)
    (hglue : S'.NW = S'.NE → S.NW = S.NE) :
    (T.mul S).IsColored (colorGlueMul T S col colS) ∧
      SameEndpointColors (T.mul S') (T.mul S) col
        (colorGlueMul T S col colS) :=
  coloring_mul_right hT hS' hS hsame hglue

/-- Recolor `[±1]` after inversion so endpoint colors (as a 2-tangle) agree. -/
def colorInvertUnit (col : Nat → Int) (a : Nat) : Int :=
  if a = 0 then col 3
  else if a = 1 then col 0
  else if a = 2 then col 1
  else if a = 3 then col 2
  else col a

theorem colorInvertUnit_vals (col : Nat → Int) :
    colorInvertUnit col 0 = col 3 ∧
    colorInvertUnit col 1 = col 0 ∧
    colorInvertUnit col 2 = col 1 ∧
    colorInvertUnit col 3 = col 2 := by
  simp [colorInvertUnit]

theorem coloring_invert_unit (s : CrossingSign) (col : Nat → Int)
    (hc : (crossingTangle s).IsColored col) :
    ∃ col', ((crossingTangle s).invert).IsColored col' ∧
      SameEndpointColors (crossingTangle s) (crossingTangle s).invert col col' := by
  refine ⟨colorInvertUnit col, ?_, ?_⟩
  · cases s with
    | pos =>
      intro C hC
      simp [crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, Crossing.switch, one] at hC
      subst hC
      obtain ⟨hβ, hr⟩ := hc ⟨0, 1, 2, 3, CrossingSign.pos⟩ (by simp [one, crossingTangle])
      constructor
      · simp [Crossing.switch, colorInvertUnit, hβ]
      · simp [Crossing.switch, colorInvertUnit]; linarith
    | neg =>
      intro C hC
      simp [crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, Crossing.switch, one, negOne] at hC
      subst hC
      have hmem : { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
          negOne.crossings := by
        simp [negOne, one, TangleDiagram.mirror, Crossing.switch, CrossingSign.flip]
      obtain ⟨hβ, hr⟩ := hc _ hmem
      constructor
      · simp [Crossing.switch, colorInvertUnit] at hβ ⊢
        linarith
      · simp [Crossing.switch, colorInvertUnit] at hr ⊢
        linarith
  · cases s with
    | pos =>
      simp [SameEndpointColors, crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, one, colorInvertUnit]
    | neg =>
      simp [SameEndpointColors, crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, negOne, one, colorInvertUnit]

/-- Inverse cycle of `colorInvertUnit`: pull a coloring of `[±1]ⁱ` back to `[±1]`. -/
def colorInvertUnitInv (col : Nat → Int) (a : Nat) : Int :=
  if a = 0 then col 1
  else if a = 1 then col 2
  else if a = 2 then col 3
  else if a = 3 then col 0
  else col a

theorem coloring_invert_unit_rev (s : CrossingSign) (col : Nat → Int)
    (hc : ((crossingTangle s).invert).IsColored col) :
    ∃ col', (crossingTangle s).IsColored col' ∧
      SameEndpointColors (crossingTangle s).invert (crossingTangle s) col col' := by
  refine ⟨colorInvertUnitInv col, ?_, ?_⟩
  · cases s with
    | pos =>
      intro C hC
      simp [crossingTangle, one] at hC
      subst hC
      have hmem : { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
          (one.invert).crossings := by
        simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
          Crossing.switch, CrossingSign.flip, one]
      obtain ⟨hβ, hr⟩ := hc _ hmem
      constructor
      · simp [colorInvertUnitInv] at hβ ⊢
        linarith
      · simp [colorInvertUnitInv] at hr ⊢
        linarith
    | neg =>
      intro C hC
      simp [crossingTangle, negOne, one, TangleDiagram.mirror, Crossing.switch] at hC
      subst hC
      have hmem : { a0 := 2, a1 := 3, a2 := 0, a3 := 1, sign := CrossingSign.pos } ∈
          (negOne.invert).crossings := by
        simp [negOne, one, TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
          Crossing.switch, CrossingSign.flip]
      obtain ⟨hβ, hr⟩ := hc _ hmem
      constructor
      · simp [colorInvertUnitInv] at hβ ⊢
        linarith
      · simp [colorInvertUnitInv] at hr ⊢
        linarith
  · cases s with
    | pos =>
      simp [SameEndpointColors, crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, one, colorInvertUnitInv]
    | neg =>
      simp [SameEndpointColors, crossingTangle, TangleDiagram.invert, TangleDiagram.rotate,
        TangleDiagram.mirror, negOne, one, colorInvertUnitInv]

/-! ## Left-add of `[0]` as a planar reindexing -/

theorem zero_maxArc : TangleDiagram.zero.maxArc = 1 := by
  unfold TangleDiagram.maxArc TangleDiagram.zero
  simp

/-- Arc map sending `T` onto the PD-code of `[0]+T`. Glues `T.NW` to `[0]`'s
    top strand `0` and `T.SW` to the bottom strand `1`. -/
def zeroAddReindex (T : TangleDiagram) (a : Nat) : Nat :=
  if a = T.NW then 0
  else if a = T.SW then 1
  else a + 2

theorem zeroAddReindex_eq_glue (T : TangleDiagram) (a : Nat) :
    addGlue TangleDiagram.zero T (a + (TangleDiagram.zero.maxArc + 1)) =
      zeroAddReindex T a := by
  rw [addGlue_shift_eq, zero_maxArc]
  simp [TangleDiagram.zero, zeroAddReindex]

theorem zeroAddReindex_injective (T : TangleDiagram) :
    Function.Injective (zeroAddReindex T) := by
  intro a b h
  unfold zeroAddReindex at h
  split_ifs at h <;> omega

theorem pairRel_sameUpToRotation_rfl :
    ∀ cs : List Crossing, pairRel Crossing.sameUpToRotation cs cs
  | [] => trivial
  | _C :: cs => ⟨Or.inl rfl, pairRel_sameUpToRotation_rfl cs⟩

theorem zero_add_crossings_reindex (T : TangleDiagram) :
    (TangleDiagram.zero.add T).crossings =
      T.crossings.map (Crossing.rename (zeroAddReindex T)) := by
  have hfun :
      addGlue TangleDiagram.zero T ∘ addShift TangleDiagram.zero =
        zeroAddReindex T := by
    funext a
    simpa [addShift, zero_maxArc] using zeroAddReindex_eq_glue T a
  rw [add_crossings_append, hfun]
  simp [TangleDiagram.zero]

theorem zero_add_NE_reindex (T : TangleDiagram) :
    (TangleDiagram.zero.add T).NE = zeroAddReindex T T.NE := by
  rw [add_NE_rename, zero_maxArc]
  simp [TangleDiagram.zero, zeroAddReindex]

theorem zero_add_SE_reindex (T : TangleDiagram) :
    (TangleDiagram.zero.add T).SE = zeroAddReindex T T.SE := by
  rw [add_SE_rename, zero_maxArc]
  simp [TangleDiagram.zero, zeroAddReindex]

/-- `[0]+T` is `T` with arcs renamed by `zeroAddReindex`. When `T.NW ≠ T.SW`
    the four endpoints match this reindexing, so the diagrams are planar
    isotopic. (If `T.NW = T.SW` then `[0]+T` records an unused SW name `1`
    while the reindex sends that arc to `0`; coloring still transports.) -/
theorem planar_zero_add (T : TangleDiagram) (h : T.NW ≠ T.SW) :
    PlanarIsotopy T (TangleDiagram.zero.add T) := by
  refine ⟨zeroAddReindex T, zeroAddReindex_injective T, ?_, ?_, ?_, ?_,
    (TangleDiagram.zero.add T).crossings, ?_, List.Perm.rfl⟩
  · simp [TangleDiagram.add, TangleDiagram.zero, zeroAddReindex]
  · exact zero_add_NE_reindex T
  · exact zero_add_SE_reindex T
  · simp [TangleDiagram.add, TangleDiagram.zero, zeroAddReindex, h.symm]
  · rw [zero_add_crossings_reindex]
    exact pairRel_sameUpToRotation_rfl _

/-- Recolor after the left-add of `[0]`: pull colors back along the
    reindex, sending the dummy bottom strand `1` of `[0]` to `T.SW`. -/
def colorZeroAdd (T : TangleDiagram) (col : Nat → Int) (b : Nat) : Int :=
  if b = 0 then col T.NW
  else if b = 1 then col T.SW
  else col (b - 2)

theorem colorZeroAdd_reindex (T : TangleDiagram) (col : Nat → Int) (a : Nat) :
    colorZeroAdd T col (zeroAddReindex T a) = col a := by
  unfold zeroAddReindex
  split_ifs with hNW hSW
  · simp [colorZeroAdd, hNW]
  · simp [colorZeroAdd, hSW]
  · have hne1 : a + 2 ≠ 1 := by omega
    simp [colorZeroAdd, hne1]

theorem IsColored_colorZeroAdd (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col) :
    (TangleDiagram.zero.add T).IsColored (colorZeroAdd T col) := by
  intro C hC
  rw [zero_add_crossings_reindex] at hC
  obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
  rw [ColoringRule_rename]
  have hfun : colorZeroAdd T col ∘ zeroAddReindex T = col :=
    funext (colorZeroAdd_reindex T col)
  simpa [hfun] using hc C0 hC0

theorem coloring_zero_add (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col) :
    ∃ col', (TangleDiagram.zero.add T).IsColored col' ∧
      SameEndpointColors T (TangleDiagram.zero.add T) col col' := by
  refine ⟨colorZeroAdd T col, IsColored_colorZeroAdd T col hc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [colorZeroAdd, TangleDiagram.add, TangleDiagram.zero]
  · rw [zero_add_NE_reindex, colorZeroAdd_reindex]
  · rw [zero_add_SE_reindex, colorZeroAdd_reindex]
  · simp [colorZeroAdd, TangleDiagram.add, TangleDiagram.zero]

/-- Reverse of `coloring_zero_add` when `T.NW ≠ T.SW`. Restriction
    `colorAddRight` recovers the summand coloring. The dummy-strand case
    `NW = SW` is omitted: `[0]+T` then records unused SW name `1` while the
    reindex sends that arc to `0`. -/
theorem coloring_zero_add_rev (T : TangleDiagram) (hne : T.NW ≠ T.SW)
    (col : Nat → Int) (hc : (TangleDiagram.zero.add T).IsColored col) :
    ∃ col', T.IsColored col' ∧
      SameEndpointColors (TangleDiagram.zero.add T) T col col' := by
  refine ⟨colorAddRight TangleDiagram.zero T col, IsColored_add_right hc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [colorAddRight_NW]
    simp [TangleDiagram.add, TangleDiagram.zero]
  · exact colorAddRight_NE TangleDiagram.zero T col
  · exact colorAddRight_SE TangleDiagram.zero T col
  · have hsw :=
        (colorAddRight_SW TangleDiagram.zero T col).resolve_right hne
    rw [hsw]
    simp [TangleDiagram.add, TangleDiagram.zero]

/-! ## Left-mul of infinity as a planar reindexing

Degenerate flype-slide case (b): left-multiply by the vertical trivial
tangle. This is `T` with arcs renamed. When `T.NW ≠ T.NE` the four
endpoints match this reindexing (planar isotopy). If `T.NW = T.NE` then
the product records an unused NE name `1` while the reindex sends that
arc to `0`; coloring still transports.
-/

theorem infinity_maxArc : TangleDiagram.infinity.maxArc = 1 := by
  unfold TangleDiagram.maxArc TangleDiagram.infinity
  simp

/-- Arc map sending `T` onto the PD-code of `infinity.mul T`. Glues `T.NW`
    to the left strand `0` and `T.NE` to the right strand `1`. -/
def infinityMulReindex (T : TangleDiagram) (a : Nat) : Nat :=
  if a = T.NW then 0
  else if a = T.NE then 1
  else a + 2

theorem infinityMulReindex_eq_glue (T : TangleDiagram) (a : Nat) :
    mulGlue TangleDiagram.infinity T
      (a + (TangleDiagram.infinity.maxArc + 1)) =
      infinityMulReindex T a := by
  rw [mulGlue_shift_eq, infinity_maxArc]
  simp [TangleDiagram.infinity, infinityMulReindex]

theorem infinityMulReindex_injective (T : TangleDiagram) :
    Function.Injective (infinityMulReindex T) := by
  intro a b h
  unfold infinityMulReindex at h
  split_ifs at h <;> omega

theorem infinity_mul_crossings_reindex (T : TangleDiagram) :
    (TangleDiagram.infinity.mul T).crossings =
      T.crossings.map (Crossing.rename (infinityMulReindex T)) := by
  have hfun :
      mulGlue TangleDiagram.infinity T ∘ addShift TangleDiagram.infinity =
        infinityMulReindex T := by
    funext a
    simpa [addShift, infinity_maxArc] using infinityMulReindex_eq_glue T a
  rw [mul_crossings_append, hfun]
  simp [TangleDiagram.infinity]

theorem infinity_mul_SE_reindex (T : TangleDiagram) :
    (TangleDiagram.infinity.mul T).SE = infinityMulReindex T T.SE := by
  rw [mul_SE_glue, infinity_maxArc]
  exact infinityMulReindex_eq_glue T T.SE

theorem infinity_mul_SW_reindex (T : TangleDiagram) :
    (TangleDiagram.infinity.mul T).SW = infinityMulReindex T T.SW := by
  rw [mul_SW_glue, infinity_maxArc]
  exact infinityMulReindex_eq_glue T T.SW

/-- `infinity.mul T` is `T` with arcs renamed by `infinityMulReindex`. When
    `T.NW ≠ T.NE` the four endpoints match this reindexing, so the diagrams
    are planar isotopic. -/
theorem planar_infinity_mul (T : TangleDiagram) (h : T.NW ≠ T.NE) :
    PlanarIsotopy T (TangleDiagram.infinity.mul T) := by
  refine ⟨infinityMulReindex T, infinityMulReindex_injective T, ?_, ?_, ?_, ?_,
    (TangleDiagram.infinity.mul T).crossings, ?_, List.Perm.rfl⟩
  · simp [TangleDiagram.mul, TangleDiagram.infinity, infinityMulReindex]
  · simp [TangleDiagram.mul, TangleDiagram.infinity, infinityMulReindex, h.symm]
  · exact infinity_mul_SE_reindex T
  · exact infinity_mul_SW_reindex T
  · rw [infinity_mul_crossings_reindex]
    exact pairRel_sameUpToRotation_rfl _

/-- Recolor after left-mul by `infinity`: pull colors back along the
    reindex, sending the dummy right strand `1` to `T.NE`. -/
def colorInfinityMul (T : TangleDiagram) (col : Nat → Int) (b : Nat) : Int :=
  if b = 0 then col T.NW
  else if b = 1 then col T.NE
  else col (b - 2)

theorem colorInfinityMul_reindex (T : TangleDiagram) (col : Nat → Int) (a : Nat) :
    colorInfinityMul T col (infinityMulReindex T a) = col a := by
  unfold infinityMulReindex
  split_ifs with hNW hNE
  · simp [colorInfinityMul, hNW]
  · simp [colorInfinityMul, hNE]
  · have hne1 : a + 2 ≠ 1 := by omega
    simp [colorInfinityMul, hne1]

theorem IsColored_colorInfinityMul (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col) :
    (TangleDiagram.infinity.mul T).IsColored (colorInfinityMul T col) := by
  intro C hC
  rw [infinity_mul_crossings_reindex] at hC
  obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
  rw [ColoringRule_rename]
  have hfun : colorInfinityMul T col ∘ infinityMulReindex T = col :=
    funext (colorInfinityMul_reindex T col)
  simpa [hfun] using hc C0 hC0

theorem coloring_infinity_mul (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col) :
    ∃ col', (TangleDiagram.infinity.mul T).IsColored col' ∧
      SameEndpointColors T (TangleDiagram.infinity.mul T) col col' := by
  refine ⟨colorInfinityMul T col, IsColored_colorInfinityMul T col hc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [colorInfinityMul, TangleDiagram.mul, TangleDiagram.infinity]
  · simp [colorInfinityMul, TangleDiagram.mul, TangleDiagram.infinity]
  · rw [infinity_mul_SE_reindex, colorInfinityMul_reindex]
  · rw [infinity_mul_SW_reindex, colorInfinityMul_reindex]

theorem coloring_fraction_infinity_mul (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col) :
    ∃ col', (TangleDiagram.infinity.mul T).IsColored col' ∧
      ColorMatrix.of (TangleDiagram.infinity.mul T) col' =
        ColorMatrix.of T col ∧
      (ColorMatrix.of (TangleDiagram.infinity.mul T) col').fraction =
        (ColorMatrix.of T col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_infinity_mul T col hc
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

/-! ## Nested unit chains vs two-block PD-sums

`T` followed by `n` right-adds of `[±1]` is the same projection as
`T.add (integerTangle (±n))` after a `+2` arc reindex: the two-block
right summand is built from `[0]`, whose dummy arcs bump `maxArc` by
`zero.maxArc + 1 = 2`. This is planar isotopy (no flype).
-/

/-- Arc map sending a nested right-add of units onto the two-block sum
    with an integer tangle (the extra `+2` is the dummy `[0]` in the
    right block). -/
def addZeroBlockReindex (T : TangleDiagram) (a : Nat) : Nat :=
  if a ≤ T.maxArc then a else a + 2

theorem addZeroBlockReindex_injective (T : TangleDiagram) :
    Function.Injective (addZeroBlockReindex T) := by
  intro a b h
  unfold addZeroBlockReindex at h
  split_ifs at h <;> omega

theorem addZeroBlockReindex_le (T : TangleDiagram) {a : Nat}
    (ha : a ≤ T.maxArc) : addZeroBlockReindex T a = a := by
  simp [addZeroBlockReindex, ha]

theorem addZeroBlockReindex_gt (T : TangleDiagram) {a : Nat}
    (ha : T.maxArc < a) : addZeroBlockReindex T a = a + 2 := by
  have : ¬ a ≤ T.maxArc := Nat.not_le.mpr ha
  simp [addZeroBlockReindex, this]

theorem Crossing.rename_eq_of_ports {f : Nat → Nat} {C : Crossing}
    (h0 : f C.a0 = C.a0) (h1 : f C.a1 = C.a1) (h2 : f C.a2 = C.a2)
    (h3 : f C.a3 = C.a3) : C.rename f = C := by
  cases C
  simp [Crossing.rename, h0, h1, h2, h3]

theorem foldl_maxArc_le (cs : List Crossing) (b M : Nat)
    (hb : b ≤ M) (h : ∀ C ∈ cs, C.maxArc ≤ M) :
    cs.foldl (fun m C => max m C.maxArc) b ≤ M := by
  induction cs generalizing b with
  | nil => simpa [List.foldl] using hb
  | cons C cs ih =>
    simp [List.foldl]
    apply ih
    · exact Nat.max_le.mpr ⟨hb, h C (List.mem_cons.2 (Or.inl rfl))⟩
    · intro X hX
      exact h X (List.mem_cons.2 (Or.inr hX))

theorem maxArc_add_one (T : TangleDiagram) :
    (T.add one).maxArc = T.maxArc + 3 := by
  have hNW := maxArc_ge_NW T
  have hNE := maxArc_ge_NE T
  have hSE := maxArc_ge_SE T
  have hSW := maxArc_ge_SW T
  have hb :
      max T.NW (max (T.maxArc + 2) (max (T.maxArc + 3) T.SW)) =
        T.maxArc + 3 := by omega
  have hT :
      T.crossings.foldl (fun m C => max m C.maxArc) (T.maxArc + 3) =
        T.maxArc + 3 := by
    apply Nat.le_antisymm
    · exact foldl_maxArc_le _ _ _ (by omega)
        (fun C hC => le_trans (maxArc_ge_of_mem T hC) (by omega))
    · exact foldl_maxArc_ge _ _
  conv => lhs; unfold TangleDiagram.maxArc
  rw [add_one_crossings, add_one_NW, add_one_NE, add_one_SW, add_one_SE, hb,
    List.foldl_append, hT]
  simp [List.foldl, Crossing.maxArc]
  omega

theorem maxArc_add_negOne (T : TangleDiagram) :
    (T.add negOne).maxArc = T.maxArc + 3 := by
  have hNW := maxArc_ge_NW T
  have hNE := maxArc_ge_NE T
  have hSE := maxArc_ge_SE T
  have hSW := maxArc_ge_SW T
  have hb :
      max T.NW (max (T.maxArc + 2) (max (T.maxArc + 3) T.SW)) =
        T.maxArc + 3 := by omega
  have hT :
      T.crossings.foldl (fun m C => max m C.maxArc) (T.maxArc + 3) =
        T.maxArc + 3 := by
    apply Nat.le_antisymm
    · exact foldl_maxArc_le _ _ _ (by omega)
        (fun C hC => le_trans (maxArc_ge_of_mem T hC) (by omega))
    · exact foldl_maxArc_ge _ _
  conv => lhs; unfold TangleDiagram.maxArc
  rw [add_negOne_crossings, add_negOne_NW, add_negOne_NE, add_negOne_SW,
    add_negOne_SE, hb, List.foldl_append, hT]
  simp [List.foldl, Crossing.maxArc]
  omega

theorem addGlue_eq_of_glue_ports (T S S' : TangleDiagram)
    (hNW : S'.NW = S.NW) (hSW : S'.SW = S.SW) :
    addGlue T S' = addGlue T S := by
  funext a
  simp [addGlue, hNW, hSW]

theorem add_crossings_add_one (T S : TangleDiagram) :
    (T.add (S.add one)).crossings =
      (T.add S).crossings ++
        [Crossing.rename (addGlue T S ∘ addShift T)
          ⟨S.NE, S.maxArc + 2, S.maxArc + 3, S.SE, CrossingSign.pos⟩] := by
  have hglue : addGlue T (S.add one) = addGlue T S :=
    addGlue_eq_of_glue_ports T S (S.add one) (add_one_NW S) (add_one_SW S)
  rw [add_crossings_append, add_one_crossings, List.map_append,
    add_crossings_append, hglue]
  simp [List.map]

theorem add_crossings_add_negOne (T S : TangleDiagram) :
    (T.add (S.add negOne)).crossings =
      (T.add S).crossings ++
        [Crossing.rename (addGlue T S ∘ addShift T)
          ⟨S.maxArc + 2, S.maxArc + 3, S.SE, S.NE, CrossingSign.neg⟩] := by
  have hglue : addGlue T (S.add negOne) = addGlue T S :=
    addGlue_eq_of_glue_ports T S (S.add negOne) (add_negOne_NW S)
      (add_negOne_SW S)
  rw [add_crossings_append, add_negOne_crossings, List.map_append,
    add_crossings_append, hglue]
  simp [List.map]

theorem addGlue_shift_fresh (T S : TangleDiagram) {k : Nat}
    (hk : S.maxArc < k) :
    addGlue T S (k + (T.maxArc + 1)) = k + (T.maxArc + 1) := by
  have hNW : k ≠ S.NW := by
    have := maxArc_ge_NW S
    omega
  have hSW : k ≠ S.SW := by
    have := maxArc_ge_SW S
    omega
  simp [addGlue, hNW, hSW]

/-- A PD-code rename with matching endpoints is a planar isotopy. -/
theorem planar_of_rename {D E : TangleDiagram} {f : Nat → Nat}
    (hinj : Function.Injective f)
    (hNW : E.NW = f D.NW) (hNE : E.NE = f D.NE) (hSE : E.SE = f D.SE)
    (hSW : E.SW = f D.SW)
    (hcs : E.crossings = D.crossings.map (Crossing.rename f)) :
    PlanarIsotopy D E := by
  refine ⟨f, hinj, hNW, hNE, hSE, hSW, E.crossings, ?_, List.Perm.rfl⟩
  rw [hcs]
  exact pairRel_sameUpToRotation_rfl _

/-- Inversion preserves a rename planar isotopy (`switch` commutes with
    `rename`; endpoints cycle). -/
theorem planar_invert_of_rename {D E : TangleDiagram} {f : Nat → Nat}
    (hinj : Function.Injective f)
    (hNW : E.NW = f D.NW) (hNE : E.NE = f D.NE) (hSE : E.SE = f D.SE)
    (hSW : E.SW = f D.SW)
    (hcs : E.crossings = D.crossings.map (Crossing.rename f)) :
    PlanarIsotopy D.invert E.invert := by
  have hcsI :
      E.invert.crossings = D.invert.crossings.map (Crossing.rename f) := by
    simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
      hcs, List.map_map, Function.comp, Crossing.switch_rename]
  refine planar_of_rename hinj ?_ ?_ ?_ ?_ hcsI
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror, hNE]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror, hSE]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror, hSW]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror, hNW]

theorem foldAddUnits_replicate_snoc (n : Nat) (s : CrossingSign) :
    List.replicate (n + 1) (crossingTangle s) =
      List.replicate n (crossingTangle s) ++ [crossingTangle s] := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih =>
    calc List.replicate (n + 1 + 1) (crossingTangle s)
        = crossingTangle s :: List.replicate (n + 1) (crossingTangle s) := rfl
      _ = crossingTangle s ::
          (List.replicate n (crossingTangle s) ++ [crossingTangle s]) := by
            rw [ih]
      _ = (crossingTangle s :: List.replicate n (crossingTangle s)) ++
          [crossingTangle s] := by simp [List.cons_append]
      _ = List.replicate (n + 1) (crossingTangle s) ++ [crossingTangle s] := rfl

/-- Nested right-adds of `n` copies of `[s]` onto `T`. -/
def foldAddUnits (T : TangleDiagram) (n : Nat) (s : CrossingSign) :
    TangleDiagram :=
  (List.replicate n (crossingTangle s)).foldl TangleDiagram.add T

/-- Two-block integer summand: `[s]` nested onto `[0]` (dummy arcs `0,1`). -/
def integerBlock (n : Nat) (s : CrossingSign) : TangleDiagram :=
  foldAddUnits TangleDiagram.zero n s

theorem foldAddUnits_zero (T : TangleDiagram) (s : CrossingSign) :
    foldAddUnits T 0 s = T :=
  rfl

theorem integerBlock_zero (s : CrossingSign) :
    integerBlock 0 s = TangleDiagram.zero :=
  rfl

theorem foldAddUnits_succ (T : TangleDiagram) (n : Nat) (s : CrossingSign) :
    foldAddUnits T (n + 1) s =
      (foldAddUnits T n s).add (crossingTangle s) := by
  unfold foldAddUnits
  rw [foldAddUnits_replicate_snoc, List.foldl_append]
  simp [List.foldl]

theorem integerBlock_succ (n : Nat) (s : CrossingSign) :
    integerBlock (n + 1) s =
      (integerBlock n s).add (crossingTangle s) :=
  foldAddUnits_succ TangleDiagram.zero n s

theorem foldAddUnits_maxArc (T : TangleDiagram) (n : Nat) (s : CrossingSign) :
    (foldAddUnits T n s).maxArc = T.maxArc + 3 * n := by
  induction n with
  | zero => simp [foldAddUnits]
  | succ n ih =>
    rw [foldAddUnits_succ]
    cases s with
    | pos =>
      rw [show crossingTangle CrossingSign.pos = one from rfl, maxArc_add_one, ih]
      omega
    | neg =>
      rw [show crossingTangle CrossingSign.neg = negOne from rfl, maxArc_add_negOne, ih]
      omega

theorem integerBlock_maxArc (n : Nat) (s : CrossingSign) :
    (integerBlock n s).maxArc = 1 + 3 * n := by
  simpa [integerBlock, zero_maxArc, Nat.add_comm] using
    foldAddUnits_maxArc TangleDiagram.zero n s

theorem foldAddUnits_NW (T : TangleDiagram) (n : Nat) (s : CrossingSign) :
    (foldAddUnits T n s).NW = T.NW := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldAddUnits_succ]
    cases s with
    | pos =>
      rw [show crossingTangle CrossingSign.pos = one from rfl, add_one_NW, ih]
    | neg =>
      rw [show crossingTangle CrossingSign.neg = negOne from rfl, add_negOne_NW, ih]

theorem foldAddUnits_SW (T : TangleDiagram) (n : Nat) (s : CrossingSign) :
    (foldAddUnits T n s).SW = T.SW := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldAddUnits_succ]
    cases s with
    | pos =>
      rw [show crossingTangle CrossingSign.pos = one from rfl, add_one_SW, ih]
    | neg =>
      rw [show crossingTangle CrossingSign.neg = negOne from rfl, add_negOne_SW, ih]

theorem addZeroBlockReindex_NW (T : TangleDiagram) :
    addZeroBlockReindex T T.NW = T.NW :=
  addZeroBlockReindex_le T (maxArc_ge_NW T)

theorem addZeroBlockReindex_NE (T : TangleDiagram) :
    addZeroBlockReindex T T.NE = T.NE :=
  addZeroBlockReindex_le T (maxArc_ge_NE T)

theorem addZeroBlockReindex_SE (T : TangleDiagram) :
    addZeroBlockReindex T T.SE = T.SE :=
  addZeroBlockReindex_le T (maxArc_ge_SE T)

theorem addZeroBlockReindex_SW (T : TangleDiagram) :
    addZeroBlockReindex T T.SW = T.SW :=
  addZeroBlockReindex_le T (maxArc_ge_SW T)

theorem crossings_rename_addZeroBlockReindex (T : TangleDiagram) :
    T.crossings.map (Crossing.rename (addZeroBlockReindex T)) = T.crossings := by
  refine
    (show ∀ cs, (∀ C ∈ cs, C ∈ T.crossings) →
        cs.map (Crossing.rename (addZeroBlockReindex T)) = cs from ?_)
      T.crossings (fun _ h => h)
  intro cs hcs
  induction cs with
  | nil => rfl
  | cons C cs ih =>
    simp [List.map]
    constructor
    · have h := arc_le_maxArc_of_mem T (hcs C (List.mem_cons.2 (Or.inl rfl)))
      exact Crossing.rename_eq_of_ports
        (addZeroBlockReindex_le T h.1) (addZeroBlockReindex_le T h.2.1)
        (addZeroBlockReindex_le T h.2.2.1) (addZeroBlockReindex_le T h.2.2.2)
    · exact ih (fun X hX => hcs X (List.mem_cons.2 (Or.inr hX)))

theorem add_NW (T S : TangleDiagram) : (T.add S).NW = T.NW := rfl

theorem add_SW (T S : TangleDiagram) : (T.add S).SW = T.SW := rfl

theorem foldAddUnits_integerBlock_rename (T : TangleDiagram) (n : Nat)
    (s : CrossingSign) :
    (T.add (integerBlock n s)).NW =
        addZeroBlockReindex T (foldAddUnits T n s).NW ∧
      (T.add (integerBlock n s)).NE =
        addZeroBlockReindex T (foldAddUnits T n s).NE ∧
      (T.add (integerBlock n s)).SE =
        addZeroBlockReindex T (foldAddUnits T n s).SE ∧
      (T.add (integerBlock n s)).SW =
        addZeroBlockReindex T (foldAddUnits T n s).SW ∧
      (T.add (integerBlock n s)).crossings =
        (foldAddUnits T n s).crossings.map
          (Crossing.rename (addZeroBlockReindex T)) := by
  induction n with
  | zero =>
    rw [foldAddUnits_zero, integerBlock_zero, add_zero_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [addZeroBlockReindex_NW]
    · rw [addZeroBlockReindex_NE]
    · rw [addZeroBlockReindex_SE]
    · rw [addZeroBlockReindex_SW]
    · exact (crossings_rename_addZeroBlockReindex T).symm
  | succ n ih =>
    cases s with
    | pos =>
      rw [foldAddUnits_succ, integerBlock_succ,
        show crossingTangle CrossingSign.pos = one from rfl]
      obtain ⟨_ihNW, ihNE, ihSE, _ihSW, ihcs⟩ := ih
      have hglue :
          addGlue T ((integerBlock n CrossingSign.pos).add one) =
            addGlue T (integerBlock n CrossingSign.pos) :=
        addGlue_eq_of_glue_ports T (integerBlock n CrossingSign.pos)
          ((integerBlock n CrossingSign.pos).add one)
          (add_one_NW _) (add_one_SW _)
      have hmaxD := foldAddUnits_maxArc T n CrossingSign.pos
      have hmaxS := integerBlock_maxArc n CrossingSign.pos
      have hf2 : addZeroBlockReindex T
          ((foldAddUnits T n CrossingSign.pos).maxArc + 2) =
          (foldAddUnits T n CrossingSign.pos).maxArc + 4 := by
        apply addZeroBlockReindex_gt; omega
      have hf3 : addZeroBlockReindex T
          ((foldAddUnits T n CrossingSign.pos).maxArc + 3) =
          (foldAddUnits T n CrossingSign.pos).maxArc + 5 := by
        apply addZeroBlockReindex_gt; omega
      have hfresh2 :
          addGlue T (integerBlock n CrossingSign.pos)
            ((integerBlock n CrossingSign.pos).maxArc + 2 + (T.maxArc + 1)) =
            (integerBlock n CrossingSign.pos).maxArc + 2 + (T.maxArc + 1) :=
        addGlue_shift_fresh T (integerBlock n CrossingSign.pos) (by omega)
      have hfresh3 :
          addGlue T (integerBlock n CrossingSign.pos)
            ((integerBlock n CrossingSign.pos).maxArc + 3 + (T.maxArc + 1)) =
            (integerBlock n CrossingSign.pos).maxArc + 3 + (T.maxArc + 1) :=
        addGlue_shift_fresh T (integerBlock n CrossingSign.pos) (by omega)
      have hport2 :
          addGlue T (integerBlock n CrossingSign.pos)
            ((integerBlock n CrossingSign.pos).maxArc + 2 + (T.maxArc + 1)) =
            addZeroBlockReindex T
              ((foldAddUnits T n CrossingSign.pos).maxArc + 2) := by
        rw [hfresh2, hf2, hmaxD, hmaxS]; omega
      have hport3 :
          addGlue T (integerBlock n CrossingSign.pos)
            ((integerBlock n CrossingSign.pos).maxArc + 3 + (T.maxArc + 1)) =
            addZeroBlockReindex T
              ((foldAddUnits T n CrossingSign.pos).maxArc + 3) := by
        rw [hfresh3, hf3, hmaxD, hmaxS]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [add_NW, add_one_NW, foldAddUnits_NW, addZeroBlockReindex_NW]
      · rw [add_NE, add_one_NE, hglue, add_one_NE]
        exact hport2
      · rw [add_SE, add_one_SE, hglue, add_one_SE]
        exact hport3
      · rw [add_SW, add_one_SW, foldAddUnits_SW, addZeroBlockReindex_SW]
      · rw [add_crossings_add_one, add_one_crossings, ihcs, List.map_append]
        simp [List.map, Crossing.rename, addShift, Function.comp, hport2, hport3]
        constructor
        · simpa [add_NE] using ihNE
        · simpa [add_SE] using ihSE
    | neg =>
      rw [foldAddUnits_succ, integerBlock_succ,
        show crossingTangle CrossingSign.neg = negOne from rfl]
      obtain ⟨_ihNW, ihNE, ihSE, _ihSW, ihcs⟩ := ih
      have hglue :
          addGlue T ((integerBlock n CrossingSign.neg).add negOne) =
            addGlue T (integerBlock n CrossingSign.neg) :=
        addGlue_eq_of_glue_ports T (integerBlock n CrossingSign.neg)
          ((integerBlock n CrossingSign.neg).add negOne)
          (add_negOne_NW _) (add_negOne_SW _)
      have hmaxD := foldAddUnits_maxArc T n CrossingSign.neg
      have hmaxS := integerBlock_maxArc n CrossingSign.neg
      have hf2 : addZeroBlockReindex T
          ((foldAddUnits T n CrossingSign.neg).maxArc + 2) =
          (foldAddUnits T n CrossingSign.neg).maxArc + 4 := by
        apply addZeroBlockReindex_gt; omega
      have hf3 : addZeroBlockReindex T
          ((foldAddUnits T n CrossingSign.neg).maxArc + 3) =
          (foldAddUnits T n CrossingSign.neg).maxArc + 5 := by
        apply addZeroBlockReindex_gt; omega
      have hfresh2 :
          addGlue T (integerBlock n CrossingSign.neg)
            ((integerBlock n CrossingSign.neg).maxArc + 2 + (T.maxArc + 1)) =
            (integerBlock n CrossingSign.neg).maxArc + 2 + (T.maxArc + 1) :=
        addGlue_shift_fresh T (integerBlock n CrossingSign.neg) (by omega)
      have hfresh3 :
          addGlue T (integerBlock n CrossingSign.neg)
            ((integerBlock n CrossingSign.neg).maxArc + 3 + (T.maxArc + 1)) =
            (integerBlock n CrossingSign.neg).maxArc + 3 + (T.maxArc + 1) :=
        addGlue_shift_fresh T (integerBlock n CrossingSign.neg) (by omega)
      have hport2 :
          addGlue T (integerBlock n CrossingSign.neg)
            ((integerBlock n CrossingSign.neg).maxArc + 2 + (T.maxArc + 1)) =
            addZeroBlockReindex T
              ((foldAddUnits T n CrossingSign.neg).maxArc + 2) := by
        rw [hfresh2, hf2, hmaxD, hmaxS]; omega
      have hport3 :
          addGlue T (integerBlock n CrossingSign.neg)
            ((integerBlock n CrossingSign.neg).maxArc + 3 + (T.maxArc + 1)) =
            addZeroBlockReindex T
              ((foldAddUnits T n CrossingSign.neg).maxArc + 3) := by
        rw [hfresh3, hf3, hmaxD, hmaxS]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [add_NW, add_negOne_NW, foldAddUnits_NW, addZeroBlockReindex_NW]
      · rw [add_NE, add_negOne_NE, hglue, add_negOne_NE]
        exact hport2
      · rw [add_SE, add_negOne_SE, hglue, add_negOne_SE]
        exact hport3
      · rw [add_SW, add_negOne_SW, foldAddUnits_SW, addZeroBlockReindex_SW]
      · rw [add_crossings_add_negOne, add_negOne_crossings, ihcs, List.map_append]
        simp [List.map, Crossing.rename, addShift, Function.comp, hport2, hport3]
        constructor
        · simpa [add_SE] using ihSE
        · simpa [add_NE] using ihNE

/-- Nested right-adds of `n` copies of `[s]` onto `T` is a planar reindexing
    of the two-block PD-sum `T.add (integerBlock n s)`. Not a flype. -/
theorem planar_foldAddUnits_integerBlock (T : TangleDiagram) (n : Nat)
    (s : CrossingSign) :
    PlanarIsotopy (foldAddUnits T n s) (T.add (integerBlock n s)) := by
  obtain ⟨hNW, hNE, hSE, hSW, hcs⟩ := foldAddUnits_integerBlock_rename T n s
  exact planar_of_rename (addZeroBlockReindex_injective T) hNW hNE hSE hSW hcs

/-- Invert of both sides of `planar_foldAddUnits_integerBlock` is the same
    rename after `Crossing.switch`. Not `invert_cong` on `ColoringIsotopy`. -/
theorem planar_foldAddUnits_integerBlock_invert (T : TangleDiagram) (n : Nat)
    (s : CrossingSign) :
    PlanarIsotopy (foldAddUnits T n s).invert
      (T.add (integerBlock n s)).invert := by
  obtain ⟨hNW, hNE, hSE, hSW, hcs⟩ := foldAddUnits_integerBlock_rename T n s
  exact planar_invert_of_rename (addZeroBlockReindex_injective T)
    hNW hNE hSE hSW hcs

/-- Invert of `[0]+T` is the invert of `T` after `zeroAddReindex`.
    Same port hypothesis as `planar_zero_add`. Not `invert_cong`. -/
theorem planar_zero_add_invert (T : TangleDiagram) (h : T.NW ≠ T.SW) :
    PlanarIsotopy T.invert (TangleDiagram.zero.add T).invert :=
  planar_invert_of_rename (zeroAddReindex_injective T)
    (by simp [TangleDiagram.add, TangleDiagram.zero, zeroAddReindex])
    (zero_add_NE_reindex T) (zero_add_SE_reindex T)
    (by simp [TangleDiagram.add, TangleDiagram.zero, zeroAddReindex, h.symm])
    (zero_add_crossings_reindex T)

/-- Invert of `[∞]*T` is the invert of `T` after `infinityMulReindex`.
    Same port hypothesis as `planar_infinity_mul`. Not `invert_cong`. -/
theorem planar_infinity_mul_invert (T : TangleDiagram) (h : T.NW ≠ T.NE) :
    PlanarIsotopy T.invert (TangleDiagram.infinity.mul T).invert :=
  planar_invert_of_rename (infinityMulReindex_injective T)
    (by simp [TangleDiagram.mul, TangleDiagram.infinity, infinityMulReindex])
    (by simp [TangleDiagram.mul, TangleDiagram.infinity, infinityMulReindex, h.symm])
    (infinity_mul_SE_reindex T) (infinity_mul_SW_reindex T)
    (infinity_mul_crossings_reindex T)


/-! ## Sign-preserving `[±1]` slide (algebraic Figure 5)

`t.rot180` cycles the box endpoints (`NW = t.SE`), so `colorAddRight` on
`t.rot180` does not preserve the four disc colors of `[±1]+t`. The PD-code of
`t.rot180+[±1]` is a planar reindexing of `([±1]+t).rot180`. Pulling `col`
along that reindexing yields the 180°-rotated color matrix. When the original
matrix satisfies `DiagonalSum`, the affine map `α ↦ (NW+SE) - α` restores the
four disc colors.

This is **not** an `IsLocalFlype` witness: an injective `f` cannot both fix
disc endpoints and implement `rotate180` on `t` (`t.NE` would have to map to
both `E.NE` and `t.NE`). It is also not `hflip`/`Crossing.switch` or
`(-T).vflip`.

`SameEndpointColors` for the unrotated diagrams is **false** in general (a
crossingless diagonal `t` with `NW=SE`, `NE=SW` gives a well-formed
`[±1]+t` whose non-monochrome colorings do not extend to `t.rot180+[±1]`
with the same positional colors). Hence no `ColoringIsotopy` constructor is
added in this slice.
-/

theorem Crossing.rotate180_maxArc (C : Crossing) :
    C.rotate180.maxArc = C.maxArc := by
  simp [Crossing.rotate180, Crossing.maxArc]
  omega

theorem foldl_maxArc_map_rotate180 (cs : List Crossing) (b : Nat) :
    (cs.map Crossing.rotate180).foldl (fun m C => max m C.maxArc) b =
      cs.foldl (fun m C => max m C.maxArc) b := by
  induction cs generalizing b with
  | nil => rfl
  | cons C cs ih =>
    simp [List.foldl]
    rw [Crossing.rotate180_maxArc, ih]

theorem maxArc_rot180 (T : TangleDiagram) : T.rot180.maxArc = T.maxArc := by
  unfold TangleDiagram.rot180 TangleDiagram.maxArc
  simp [foldl_maxArc_map_rotate180]
  ac_rfl

theorem IsColored_rot180 (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) : T.rot180.IsColored col := by
  intro C hC
  simp [TangleDiagram.rot180, List.mem_map] at hC
  obtain ⟨C0, hC0, rfl⟩ := hC
  exact ColoringRule_rotate180 C0 col (h C0 hC0)

theorem one_maxArc : one.maxArc = 3 := by
  unfold one TangleDiagram.maxArc Crossing.maxArc
  simp

theorem crossingTangle_maxArc (s : CrossingSign) :
    (crossingTangle s).maxArc = 3 := by
  cases s with
  | pos => simp [crossingTangle, one_maxArc]
  | neg =>
    simp [crossingTangle, negOne, maxArc_mirror, one_maxArc]

theorem crossingTangle_NW (s : CrossingSign) : (crossingTangle s).NW = 0 := by
  cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]

theorem crossingTangle_NE (s : CrossingSign) : (crossingTangle s).NE = 1 := by
  cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]

theorem crossingTangle_SE (s : CrossingSign) : (crossingTangle s).SE = 2 := by
  cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]

theorem crossingTangle_SW (s : CrossingSign) : (crossingTangle s).SW = 3 := by
  cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]

/-- Arc map identifying `([±1]+t).rot180` with `t.rot180+[±1]`. On the unit,
    ports are 180-cycled then glued; on the shifted copy of `t` it is unshift. -/
def flypeSlideAddFun (s : CrossingSign) (t : TangleDiagram) (a : Nat) : Nat :=
  let U := crossingTangle s
  let m := t.maxArc
  if a = U.NW then U.SE + (m + 1)
  else if a = U.NE then t.NW
  else if a = U.SE then t.SW
  else if a = U.SW then U.NE + (m + 1)
  else
    let b := a - (U.maxArc + 1)
    if b = t.NW ∨ b = t.SW ∨ t.maxArc < b then a + m + 8
    else b

theorem flypeSlideAddFun_unit_NW (s : CrossingSign) (t : TangleDiagram) :
    flypeSlideAddFun s t (crossingTangle s).NW =
      (crossingTangle s).SE + (t.maxArc + 1) := by
  simp [flypeSlideAddFun]

theorem flypeSlideAddFun_unit_NE (s : CrossingSign) (t : TangleDiagram) :
    flypeSlideAddFun s t (crossingTangle s).NE = t.NW := by
  have hne : (crossingTangle s).NE ≠ (crossingTangle s).NW :=
    (crossingTangle_NW_ne_NE s).symm
  simp [flypeSlideAddFun, hne]

theorem flypeSlideAddFun_unit_SE (s : CrossingSign) (t : TangleDiagram) :
    flypeSlideAddFun s t (crossingTangle s).SE = t.SW := by
  have hNW : (crossingTangle s).SE ≠ (crossingTangle s).NW := by
    cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]
  have hNE : (crossingTangle s).SE ≠ (crossingTangle s).NE := by
    cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]
  simp [flypeSlideAddFun, hNW, hNE]

theorem flypeSlideAddFun_unit_SW (s : CrossingSign) (t : TangleDiagram) :
    flypeSlideAddFun s t (crossingTangle s).SW =
      (crossingTangle s).NE + (t.maxArc + 1) := by
  have hNW : (crossingTangle s).SW ≠ (crossingTangle s).NW :=
    (crossingTangle_NW_ne_SW s).symm
  have hNE : (crossingTangle s).SW ≠ (crossingTangle s).NE := by
    cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]
  have hSE : (crossingTangle s).SW ≠ (crossingTangle s).SE := by
    cases s <;> simp [crossingTangle, one, negOne, TangleDiagram.mirror]
  simp [flypeSlideAddFun, hNW, hNE, hSE]

theorem flypeSlideAddFun_eq (s : CrossingSign) (t : TangleDiagram) (a : Nat) :
    flypeSlideAddFun s t a =
      if a = 0 then t.maxArc + 3
      else if a = 1 then t.NW
      else if a = 2 then t.SW
      else if a = 3 then t.maxArc + 2
      else if a - 4 = t.NW ∨ a - 4 = t.SW ∨ t.maxArc < a - 4 then a + t.maxArc + 8
      else a - 4 := by
  have hNW : (crossingTangle s).NW = 0 := crossingTangle_NW s
  have hNE : (crossingTangle s).NE = 1 := crossingTangle_NE s
  have hSE : (crossingTangle s).SE = 2 := crossingTangle_SE s
  have hSW : (crossingTangle s).SW = 3 := crossingTangle_SW s
  have hU : (crossingTangle s).maxArc = 3 := crossingTangle_maxArc s
  unfold flypeSlideAddFun
  simp [hNW, hNE, hSE, hSW, hU]
  split_ifs <;> omega

theorem flypeSlideAddFun_shift (s : CrossingSign) (t : TangleDiagram) {b : Nat}
    (hNW : b ≠ t.NW) (hSW : b ≠ t.SW) (hle : b ≤ t.maxArc) :
    flypeSlideAddFun s t (b + ((crossingTangle s).maxArc + 1)) = b := by
  rw [crossingTangle_maxArc, flypeSlideAddFun_eq]
  have : b + (3 + 1) ≠ 0 := by omega
  have : b + (3 + 1) ≠ 1 := by omega
  have : b + (3 + 1) ≠ 2 := by omega
  have : b + (3 + 1) ≠ 3 := by omega
  have : ¬ t.maxArc < b := Nat.not_lt.mpr hle
  simp [this, hNW, hSW]

theorem flypeSlideAddFun_injective (s : CrossingSign) (t : TangleDiagram)
    (hne : t.NW ≠ t.SW) :
    Function.Injective (flypeSlideAddFun s t) := by
  intro a b h
  have hNWle : t.NW ≤ t.maxArc := maxArc_ge_NW t
  have hSWle : t.SW ≤ t.maxArc := maxArc_ge_SW t
  simp [flypeSlideAddFun_eq] at h
  split_ifs at h <;> omega

theorem flypeSlideAddFun_comp_glue (s : CrossingSign) (t : TangleDiagram)
    (a : Nat) (hle : a ≤ t.maxArc) :
    flypeSlideAddFun s t
      (addGlue (crossingTangle s) t
        (a + ((crossingTangle s).maxArc + 1))) = a := by
  rw [addGlue_shift_eq, crossingTangle_maxArc]
  by_cases hNW : a = t.NW
  · rw [if_pos hNW, flypeSlideAddFun_eq]
    simp [crossingTangle_NE, hNW]
  · rw [if_neg hNW]
    by_cases hSW : a = t.SW
    · rw [if_pos hSW, flypeSlideAddFun_eq]
      simp [crossingTangle_SE, hSW]
    · rw [if_neg hSW, flypeSlideAddFun_eq]
      have : ¬ t.maxArc < a := Nat.not_lt.mpr hle
      simp [hNW, hSW, this]

theorem flypeSlideAdd_map_t (s : CrossingSign) (t : TangleDiagram)
    {C : Crossing} (hC : C ∈ t.crossings) :
    (C.rename (addGlue (crossingTangle s) t ∘ addShift (crossingTangle s))).rotate180.rename
        (flypeSlideAddFun s t) =
      C.rotate180 := by
  have hb := arc_le_maxArc_of_mem t hC
  simp [Crossing.rename, Crossing.rotate180, Function.comp, addShift]
  rw [flypeSlideAddFun_comp_glue s t _ hb.2.2.1,
      flypeSlideAddFun_comp_glue s t _ hb.2.2.2,
      flypeSlideAddFun_comp_glue s t _ hb.1,
      flypeSlideAddFun_comp_glue s t _ hb.2.1]
  simp

/-- Recolor the four ports of `[±1]` by a planar 180°: NW↔SE, NE↔SW. -/
def colorRot180Arc (col : Nat → Int) (a : Nat) : Int :=
  if a = 0 then col 2
  else if a = 1 then col 3
  else if a = 2 then col 0
  else if a = 3 then col 1
  else col a

theorem colorRot180Arc_vals (col : Nat → Int) :
    colorRot180Arc col 0 = col 2 ∧
    colorRot180Arc col 1 = col 3 ∧
    colorRot180Arc col 2 = col 0 ∧
    colorRot180Arc col 3 = col 1 := by
  simp [colorRot180Arc]

theorem IsColored_colorRot180Arc (s : CrossingSign) (col : Nat → Int)
    (hc : (crossingTangle s).IsColored col) :
    (crossingTangle s).IsColored (colorRot180Arc col) := by
  cases s with
  | pos =>
    intro C hC
    simp [crossingTangle, one] at hC
    subst hC
    obtain ⟨hβ, hr⟩ := hc ⟨0, 1, 2, 3, CrossingSign.pos⟩ (by simp [one, crossingTangle])
    constructor
    · simp [colorRot180Arc, hβ]
    · simp [colorRot180Arc]; linarith
  | neg =>
    intro C hC
    simp [crossingTangle, negOne, one, TangleDiagram.mirror, Crossing.switch] at hC
    subst hC
    have hmem : { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
        negOne.crossings := by
      simp [negOne, one, TangleDiagram.mirror, Crossing.switch, CrossingSign.flip]
    obtain ⟨hβ, hr⟩ := hc _ hmem
    constructor
    · simp [colorRot180Arc] at hβ ⊢
      linarith
    · simp [colorRot180Arc] at hr ⊢
      linarith

/-- Affine involution `x ↦ (NW+SE) - x` restoring the 180°-rotated matrix
    when `DiagonalSum` holds. -/
def colorDiagInvol (D : TangleDiagram) (col : Nat → Int) (colG : Nat → Int)
    (a : Nat) : Int :=
  (col D.NW + col D.SE) - colG a

theorem IsColored_colorDiagInvol (E D : TangleDiagram) (col colG : Nat → Int)
    (h : E.IsColored colG) :
    E.IsColored (colorDiagInvol D col colG) := by
  have h' := coloring_affine E colG (-1) (col D.NW + col D.SE) h
  convert h' using 1
  funext a
  simp [colorDiagInvol]
  ring

theorem colorRot180Arc_NW (s : CrossingSign) (col : Nat → Int) :
    colorRot180Arc col (crossingTangle s).NW = col (crossingTangle s).SE := by
  simp [colorRot180Arc, crossingTangle_NW, crossingTangle_SE]

theorem colorRot180Arc_NE (s : CrossingSign) (col : Nat → Int) :
    colorRot180Arc col (crossingTangle s).NE = col (crossingTangle s).SW := by
  simp [colorRot180Arc, crossingTangle_NE, crossingTangle_SW]

theorem colorRot180Arc_SE (s : CrossingSign) (col : Nat → Int) :
    colorRot180Arc col (crossingTangle s).SE = col (crossingTangle s).NW := by
  simp [colorRot180Arc, crossingTangle_SE, crossingTangle_NW]

theorem colorRot180Arc_SW (s : CrossingSign) (col : Nat → Int) :
    colorRot180Arc col (crossingTangle s).SW = col (crossingTangle s).NE := by
  simp [colorRot180Arc, crossingTangle_SW, crossingTangle_NE]

/-- Restricted Figure 5 slide on a sum: if `[±1]+t` is integrally colored and
    the color matrix satisfies `DiagonalSum` (as on rational standard form),
    the affine involution `x ↦ (NW+SE)-x` transports the coloring across
    `t.rot180+[±1]` with unchanged disc colors. Not a `ColoringIsotopy`
    constructor: without `DiagonalSum` the statement is false. -/
theorem coloring_flype_slide_add (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW)
    (hdiag : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum) :
    ∃ col', (t.rot180.add (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).add t)
        (t.rot180.add (crossingTangle s)) col col' := by
  let U := crossingTangle s
  let colT := colorAddRight U t col
  let colU := colorRot180Arc col
  let colG := colorGlueAdd t.rot180 U colT colU
  have hT : t.IsColored colT := IsColored_add_right hc
  have hU : U.IsColored col := IsColored_add_left hc
  have hT180 : t.rot180.IsColored colT := IsColored_rot180 t colT hT
  have hU180 : U.IsColored colU := IsColored_colorRot180Arc s col hU
  have glueNE : colT t.rot180.NE = colU U.NW := by
    change colT t.SW = colorRot180Arc col U.NW
    rw [colorRot180Arc_NW s col]
    exact (colorAddRight_SW U t col).resolve_right hne
  have glueSE : colT t.rot180.SE = colU U.SW ∨ U.NW = U.SW := by
    left
    change colT t.NW = colorRot180Arc col U.SW
    rw [colorRot180Arc_SW s col]
    dsimp [colT]
    rw [colorAddRight_NW]
  have hG : (t.rot180.add U).IsColored colG :=
    IsColored_colorGlueAdd t.rot180 U colT colU hT180 hU180 glueNE glueSE
  refine ⟨colorDiagInvol (U.add t) col colG,
    IsColored_colorDiagInvol _ _ col colG hG, ?_⟩
  have hsum :
      col (U.add t).NW + col (U.add t).SE =
        col (U.add t).NE + col (U.add t).SW := by
    simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiag
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hGnw : colG (t.rot180.add U).NW = colT t.SE :=
      colorGlueAdd_of_le t.rot180 U colT colU (maxArc_ge_NW t.rot180)
    have hSE : colT t.SE = col (U.add t).SE := by
      dsimp [colT]; rw [colorAddRight_SE]
    change col (U.add t).NW + col (U.add t).SE - colG (t.rot180.add U).NW =
      col (U.add t).NW
    rw [hGnw, hSE]; ring
  · have h1 : colG (t.rot180.add U).NE = colU U.NE := by
      dsimp [colG]
      rw [add_NE t.rot180 U]
      exact colorGlueAdd_comp_shift t.rot180 U colT colU glueNE glueSE U.NE
    have h2 : colU U.NE = col (U.add t).SW := by
      dsimp [colU]
      rw [colorRot180Arc_NE s col]
      rfl
    change col (U.add t).NW + col (U.add t).SE - colG (t.rot180.add U).NE =
      col (U.add t).NE
    rw [h1, h2]; linarith [hsum]
  · have h1 : colG (t.rot180.add U).SE = colU U.SE := by
      dsimp [colG]
      rw [add_SE t.rot180 U]
      exact colorGlueAdd_comp_shift t.rot180 U colT colU glueNE glueSE U.SE
    have h2 : colU U.SE = col (U.add t).NW := by
      dsimp [colU]
      rw [colorRot180Arc_SE s col]
      rfl
    change col (U.add t).NW + col (U.add t).SE - colG (t.rot180.add U).SE =
      col (U.add t).SE
    rw [h1, h2]; ring
  · have hGsw : colG (t.rot180.add U).SW = colT t.NE :=
      colorGlueAdd_of_le t.rot180 U colT colU (maxArc_ge_SW t.rot180)
    have hNE : colT t.NE = col (U.add t).NE := by
      dsimp [colT]; rw [colorAddRight_NE]
    change col (U.add t).NW + col (U.add t).SE - colG (t.rot180.add U).SW =
      col (U.add t).SW
    rw [hGsw, hNE]; linarith [hsum]

theorem coloring_fraction_flype_slide_add (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW)
    (hdiag : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum) :
    ∃ col', (t.rot180.add (crossingTangle s)).IsColored col' ∧
      ColorMatrix.of (t.rot180.add (crossingTangle s)) col' =
        ColorMatrix.of ((crossingTangle s).add t) col ∧
      (ColorMatrix.of (t.rot180.add (crossingTangle s)) col').fraction =
        (ColorMatrix.of ((crossingTangle s).add t) col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_flype_slide_add s t col hc hne hdiag
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

theorem coloring_flype_slide_mul (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE)
    (hdiag : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum) :
    ∃ col', (t.rot180.mul (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).mul t)
        (t.rot180.mul (crossingTangle s)) col col' := by
  let U := crossingTangle s
  let colT := colorMulBottom U t col
  let colU := colorRot180Arc col
  let colG := colorGlueMul t.rot180 U colT colU
  have hT : t.IsColored colT := IsColored_mul_bottom hc
  have hU : U.IsColored col := IsColored_mul_top hc
  have hT180 : t.rot180.IsColored colT := IsColored_rot180 t colT hT
  have hU180 : U.IsColored colU := IsColored_colorRot180Arc s col hU
  have glueNW : colT t.rot180.SW = colU U.NW := by
    change colT t.NE = colorRot180Arc col U.NW
    rw [colorRot180Arc_NW s col]
    exact (colorMulBottom_NE U t col).resolve_right hne
  have glueNE : colT t.rot180.SE = colU U.NE ∨ U.NW = U.NE := by
    left
    change colT t.NW = colorRot180Arc col U.NE
    rw [colorRot180Arc_NE s col]
    dsimp [colT]
    rw [colorMulBottom_NW]
  have hG : (t.rot180.mul U).IsColored colG :=
    IsColored_colorGlueMul t.rot180 U colT colU hT180 hU180 glueNW glueNE
  refine ⟨colorDiagInvol (U.mul t) col colG,
    IsColored_colorDiagInvol _ _ col colG hG, ?_⟩
  have hsum :
      col (U.mul t).NW + col (U.mul t).SE =
        col (U.mul t).NE + col (U.mul t).SW := by
    simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiag
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hGnw : colG (t.rot180.mul U).NW = colT t.SE :=
      colorGlueMul_of_le t.rot180 U colT colU (maxArc_ge_NW t.rot180)
    have hSE : colT t.SE = col (U.mul t).SE := by
      dsimp [colT]; rw [colorMulBottom_SE]
    change col (U.mul t).NW + col (U.mul t).SE - colG (t.rot180.mul U).NW =
      col (U.mul t).NW
    rw [hGnw, hSE]; ring
  · have hGne : colG (t.rot180.mul U).NE = colT t.SW :=
      colorGlueMul_of_le t.rot180 U colT colU (maxArc_ge_NE t.rot180)
    have hSW : colT t.SW = col (U.mul t).SW := by
      dsimp [colT]; rw [colorMulBottom_SW]
    change col (U.mul t).NW + col (U.mul t).SE - colG (t.rot180.mul U).NE =
      col (U.mul t).NE
    rw [hGne, hSW]; linarith [hsum]
  · have h1 : colG (t.rot180.mul U).SE = colU U.SE := by
      dsimp [colG]
      rw [mul_SE_glue t.rot180 U]
      exact colorGlueMul_comp_shift t.rot180 U colT colU glueNW glueNE U.SE
    have h2 : colU U.SE = col (U.mul t).NW := by
      dsimp [colU]
      rw [colorRot180Arc_SE s col]
      rfl
    change col (U.mul t).NW + col (U.mul t).SE - colG (t.rot180.mul U).SE =
      col (U.mul t).SE
    rw [h1, h2]; ring
  · have h1 : colG (t.rot180.mul U).SW = colU U.SW := by
      dsimp [colG]
      rw [mul_SW_glue t.rot180 U]
      exact colorGlueMul_comp_shift t.rot180 U colT colU glueNW glueNE U.SW
    have h2 : colU U.SW = col (U.mul t).NE := by
      dsimp [colU]
      rw [colorRot180Arc_SW s col]
      rfl
    change col (U.mul t).NW + col (U.mul t).SE - colG (t.rot180.mul U).SW =
      col (U.mul t).SW
    rw [h1, h2]; linarith [hsum]

theorem coloring_fraction_flype_slide_mul (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE)
    (hdiag : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum) :
    ∃ col', (t.rot180.mul (crossingTangle s)).IsColored col' ∧
      ColorMatrix.of (t.rot180.mul (crossingTangle s)) col' =
        ColorMatrix.of ((crossingTangle s).mul t) col ∧
      (ColorMatrix.of (t.rot180.mul (crossingTangle s)) col').fraction =
        (ColorMatrix.of ((crossingTangle s).mul t) col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_flype_slide_mul s t col hc hne hdiag
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

/-! ## Restricted coloring of planar `rot180`

`T.rot180` cycles endpoints (`NW↔SE`, `NE↔SW`), so the same coloring `col`
satisfies `ColoringRule` on the rotated crossings but not `SameEndpointColors`.
Under `DiagonalSum`, the affine involution `x ↦ (NW+SE)-x` restores the four
disc colors. This is false without `DiagonalSum` (same crossingless diagonal
counterexample as the flype slide), so it is not a `ColoringIsotopy`
constructor.
-/

/-- Restricted planar 180°: if `T` is integrally colored and the color matrix
    satisfies `DiagonalSum`, `x ↦ (NW+SE)-x` transports the coloring to
    `T.rot180` with unchanged disc colors. -/
theorem coloring_rot180_diagonal (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col)
    (hdiag : (ColorMatrix.of T col).DiagonalSum) :
    ∃ col', T.rot180.IsColored col' ∧
      SameEndpointColors T T.rot180 col col' := by
  have h180 : T.rot180.IsColored col := IsColored_rot180 T col hc
  refine ⟨colorDiagInvol T col col,
    IsColored_colorDiagInvol T.rot180 T col col h180, ?_⟩
  have hsum : col T.NW + col T.SE = col T.NE + col T.SW := by
    simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiag
  refine ⟨?_, ?_, ?_, ?_⟩
  · change col T.NW + col T.SE - col T.SE = col T.NW
    ring
  · change col T.NW + col T.SE - col T.SW = col T.NE
    linarith [hsum]
  · change col T.NW + col T.SE - col T.NW = col T.SE
    ring
  · change col T.NW + col T.SE - col T.NE = col T.SW
    linarith [hsum]

theorem coloring_fraction_rot180_diagonal (T : TangleDiagram) (col : Nat → Int)
    (hc : T.IsColored col)
    (hdiag : (ColorMatrix.of T col).DiagonalSum) :
    ∃ col', T.rot180.IsColored col' ∧
      ColorMatrix.of T.rot180 col' = ColorMatrix.of T col ∧
      (ColorMatrix.of T.rot180 col').fraction =
        (ColorMatrix.of T col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_rot180_diagonal T col hc hdiag
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

/-- Reverse of `coloring_flype_slide_add`, for `Isotopic.symm` on a slide. -/
theorem coloring_flype_slide_add_rev (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : (t.rot180.add (crossingTangle s)).IsColored col)
    (_hne : t.NW ≠ t.SW)
    (hdiag : (ColorMatrix.of (t.rot180.add (crossingTangle s)) col).DiagonalSum) :
    ∃ col', ((crossingTangle s).add t).IsColored col' ∧
      SameEndpointColors (t.rot180.add (crossingTangle s))
        ((crossingTangle s).add t) col col' := by
  let U := crossingTangle s
  let colU0 := colorAddRight t.rot180 U col
  let colU := colorRot180Arc colU0
  let colG := colorGlueAdd U t colU col
  have hT180 : t.rot180.IsColored col := IsColored_add_left hc
  have hT : t.IsColored col := by
    simpa [rot180_rot180] using IsColored_rot180 t.rot180 col hT180
  have hU0 : U.IsColored colU0 := IsColored_add_right hc
  have hU : U.IsColored colU := IsColored_colorRot180Arc s colU0 hU0
  have glueNE : colU U.NE = col t.NW := by
    change colorRot180Arc colU0 U.NE = col t.NW
    rw [colorRot180Arc_NE s colU0]
    exact (colorAddRight_SW t.rot180 U col).resolve_right (crossingTangle_NW_ne_SW s)
  have glueSE : colU U.SE = col t.SW ∨ t.NW = t.SW := by
    left
    change colorRot180Arc colU0 U.SE = col t.SW
    rw [colorRot180Arc_SE s colU0]
    dsimp [colU0, U]
    rw [colorAddRight_NW t.rot180 U col]
    rfl
  have hG : (U.add t).IsColored colG :=
    IsColored_colorGlueAdd U t colU col hU hT glueNE glueSE
  refine ⟨colorDiagInvol (t.rot180.add U) col colG,
    IsColored_colorDiagInvol _ _ col colG hG, ?_⟩
  have hsum :
      col (t.rot180.add U).NW + col (t.rot180.add U).SE =
        col (t.rot180.add U).NE + col (t.rot180.add U).SW := by
    simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiag
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hGnw : colG (U.add t).NW = colU U.NW :=
      colorGlueAdd_of_le U t colU col (maxArc_ge_NW U)
    have h2 : colU U.NW = col (t.rot180.add U).SE := by
      change colorRot180Arc colU0 U.NW = col (t.rot180.add U).SE
      rw [colorRot180Arc_NW s colU0]
      change colorAddRight t.rot180 U col U.SE = col (t.rot180.add U).SE
      simpa [U] using colorAddRight_SE t.rot180 U col
    change col (t.rot180.add U).NW + col (t.rot180.add U).SE - colG (U.add t).NW =
      col (t.rot180.add U).NW
    rw [hGnw, h2]; ring
  · have h1 : colG (U.add t).NE = col t.NE := by
      dsimp [colG]
      rw [add_NE U t]
      exact colorGlueAdd_comp_shift U t colU col glueNE glueSE t.NE
    have h2 : col t.NE = col (t.rot180.add U).SW := rfl
    change col (t.rot180.add U).NW + col (t.rot180.add U).SE - colG (U.add t).NE =
      col (t.rot180.add U).NE
    rw [h1, h2]; linarith [hsum]
  · have h1 : colG (U.add t).SE = col t.SE := by
      dsimp [colG]
      rw [add_SE U t]
      exact colorGlueAdd_comp_shift U t colU col glueNE glueSE t.SE
    have h2 : col t.SE = col (t.rot180.add U).NW := rfl
    change col (t.rot180.add U).NW + col (t.rot180.add U).SE - colG (U.add t).SE =
      col (t.rot180.add U).SE
    rw [h1, h2]; ring
  · have hGsw : colG (U.add t).SW = colU U.SW :=
      colorGlueAdd_of_le U t colU col (maxArc_ge_SW U)
    have h2 : colU U.SW = col (t.rot180.add U).NE := by
      change colorRot180Arc colU0 U.SW = col (t.rot180.add U).NE
      rw [colorRot180Arc_SW s colU0]
      change colorAddRight t.rot180 U col U.NE = col (t.rot180.add U).NE
      simpa [U] using colorAddRight_NE t.rot180 U col
    change col (t.rot180.add U).NW + col (t.rot180.add U).SE - colG (U.add t).SW =
      col (t.rot180.add U).SW
    rw [hGsw, h2]; linarith [hsum]

theorem coloring_fraction_flype_slide_add_rev (s : CrossingSign) (t : TangleDiagram)
    (col : Nat → Int)
    (hc : (t.rot180.add (crossingTangle s)).IsColored col)
    (_hne : t.NW ≠ t.SW)
    (hdiag : (ColorMatrix.of (t.rot180.add (crossingTangle s)) col).DiagonalSum) :
    ∃ col', ((crossingTangle s).add t).IsColored col' ∧
      ColorMatrix.of ((crossingTangle s).add t) col' =
        ColorMatrix.of (t.rot180.add (crossingTangle s)) col ∧
      (ColorMatrix.of ((crossingTangle s).add t) col').fraction =
        (ColorMatrix.of (t.rot180.add (crossingTangle s)) col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_flype_slide_add_rev s t col hc _hne hdiag
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

/-! ## Associativity of `add` as reindexing -/

theorem coloring_add_assoc (T S R : TangleDiagram) (col : Nat → Int)
    (hc : ((T.add S).add R).IsColored col) :
    ∃ col', (T.add (S.add R)).IsColored col' ∧
      SameEndpointColors ((T.add S).add R) (T.add (S.add R)) col col' := by
  set colS := colorAddRight T S col
  set colR := colorAddRight (T.add S) R col
  have hT : T.IsColored col := IsColored_add_left (IsColored_add_left hc)
  have hS : S.IsColored colS := IsColored_add_right (IsColored_add_left hc)
  have hR : R.IsColored colR := IsColored_add_right hc
  have glueSR_NE : colS S.NE = colR R.NW := by
    dsimp [colS, colR]
    rw [colorAddRight_NE, colorAddRight_NW]
  have glueSR_SE : colS S.SE = colR R.SW ∨ R.NW = R.SW := by
    rcases colorAddRight_SW (T.add S) R col with h | h
    · exact Or.inl ((colorAddRight_SE T S col).trans h.symm)
    · exact Or.inr h
  have hSR : (S.add R).IsColored (colorGlueAdd S R colS colR) :=
    IsColored_colorGlueAdd S R colS colR hS hR glueSR_NE glueSR_SE
  have glueT_NE : col T.NE = colorGlueAdd S R colS colR (S.add R).NW := by
    change col T.NE = colorGlueAdd S R colS colR S.NW
    rw [colorGlueAdd_of_le S R colS colR (maxArc_ge_NW S)]
    dsimp [colS]
    rw [colorAddRight_NW]
  have glueT_SE :
      col T.SE = colorGlueAdd S R colS colR (S.add R).SW ∨
        (S.add R).NW = (S.add R).SW := by
    change col T.SE = colorGlueAdd S R colS colR S.SW ∨ S.NW = S.SW
    rw [colorGlueAdd_of_le S R colS colR (maxArc_ge_SW S)]
    rcases colorAddRight_SW T S col with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hE : (T.add (S.add R)).IsColored
      (colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR)) :=
    IsColored_colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR)
      hT hSR glueT_NE glueT_SE
  refine ⟨colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR), hE, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR) T.NW = col T.NW
    rw [colorGlueAdd_of_le T (S.add R) col (colorGlueAdd S R colS colR)
      (maxArc_ge_NW T)]
  · have h1 :
        colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR)
          (T.add (S.add R)).NE =
        colorGlueAdd S R colS colR (S.add R).NE := by
      rw [add_NE T (S.add R)]
      exact colorGlueAdd_comp_shift T (S.add R) col (colorGlueAdd S R colS colR)
        glueT_NE glueT_SE (S.add R).NE
    have h2 : colorGlueAdd S R colS colR (S.add R).NE = colR R.NE := by
      rw [add_NE S R]
      exact colorGlueAdd_comp_shift S R colS colR glueSR_NE glueSR_SE R.NE
    rw [h1, h2]
    dsimp [colR]
    rw [colorAddRight_NE]
  · have h1 :
        colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR)
          (T.add (S.add R)).SE =
        colorGlueAdd S R colS colR (S.add R).SE := by
      rw [add_SE T (S.add R)]
      exact colorGlueAdd_comp_shift T (S.add R) col (colorGlueAdd S R colS colR)
        glueT_NE glueT_SE (S.add R).SE
    have h2 : colorGlueAdd S R colS colR (S.add R).SE = colR R.SE := by
      rw [add_SE S R]
      exact colorGlueAdd_comp_shift S R colS colR glueSR_NE glueSR_SE R.SE
    rw [h1, h2]
    dsimp [colR]
    rw [colorAddRight_SE]
  · change colorGlueAdd T (S.add R) col (colorGlueAdd S R colS colR) T.SW = col T.SW
    rw [colorGlueAdd_of_le T (S.add R) col (colorGlueAdd S R colS colR)
      (maxArc_ge_SW T)]

theorem coloring_add_assoc_rev (T S R : TangleDiagram) (col : Nat → Int)
    (hc : (T.add (S.add R)).IsColored col) :
    ∃ col', ((T.add S).add R).IsColored col' ∧
      SameEndpointColors (T.add (S.add R)) ((T.add S).add R) col col' := by
  set colSR := colorAddRight T (S.add R) col
  set colR := colorAddRight S R colSR
  have hT : T.IsColored col := IsColored_add_left hc
  have hSR : (S.add R).IsColored colSR := IsColored_add_right hc
  have hS : S.IsColored colSR := IsColored_add_left hSR
  have hR : R.IsColored colR := IsColored_add_right hSR
  have glueTS_NE : col T.NE = colSR S.NW := by
    dsimp [colSR]
    rw [show S.NW = (S.add R).NW from (add_NW S R).symm, colorAddRight_NW]
  have glueTS_SE : col T.SE = colSR S.SW ∨ S.NW = S.SW := by
    change col T.SE = colSR (S.add R).SW ∨ (S.add R).NW = (S.add R).SW
    rcases colorAddRight_SW T (S.add R) col with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hTS : (T.add S).IsColored (colorGlueAdd T S col colSR) :=
    IsColored_colorGlueAdd T S col colSR hT hS glueTS_NE glueTS_SE
  have glueR_NE :
      colorGlueAdd T S col colSR (T.add S).NE = colR R.NW := by
    have h1 : colorGlueAdd T S col colSR (T.add S).NE = colSR S.NE := by
      rw [add_NE T S]
      exact colorGlueAdd_comp_shift T S col colSR glueTS_NE glueTS_SE S.NE
    rw [h1]
    dsimp [colR]
    rw [colorAddRight_NW]
  have glueR_SE :
      colorGlueAdd T S col colSR (T.add S).SE = colR R.SW ∨ R.NW = R.SW := by
    have h1 : colorGlueAdd T S col colSR (T.add S).SE = colSR S.SE := by
      rw [add_SE T S]
      exact colorGlueAdd_comp_shift T S col colSR glueTS_NE glueTS_SE S.SE
    rw [h1]
    rcases colorAddRight_SW S R colSR with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hE : ((T.add S).add R).IsColored
      (colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR) :=
    IsColored_colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR
      hTS hR glueR_NE glueR_SE
  refine ⟨colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR, hE, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR
        (T.add S).NW = col T.NW
    rw [colorGlueAdd_of_le (T.add S) R (colorGlueAdd T S col colSR) colR
      (maxArc_ge_NW (T.add S))]
    change colorGlueAdd T S col colSR T.NW = col T.NW
    rw [colorGlueAdd_of_le T S col colSR (maxArc_ge_NW T)]
  · have h1 :
        colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR
          ((T.add S).add R).NE = colR R.NE := by
      rw [add_NE (T.add S) R]
      exact colorGlueAdd_comp_shift (T.add S) R (colorGlueAdd T S col colSR)
        colR glueR_NE glueR_SE R.NE
    rw [h1]
    dsimp [colR, colSR]
    rw [colorAddRight_NE, colorAddRight_NE]
  · have h1 :
        colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR
          ((T.add S).add R).SE = colR R.SE := by
      rw [add_SE (T.add S) R]
      exact colorGlueAdd_comp_shift (T.add S) R (colorGlueAdd T S col colSR)
        colR glueR_NE glueR_SE R.SE
    rw [h1]
    dsimp [colR, colSR]
    rw [colorAddRight_SE, colorAddRight_SE]
  · change colorGlueAdd (T.add S) R (colorGlueAdd T S col colSR) colR
        (T.add S).SW = col T.SW
    rw [colorGlueAdd_of_le (T.add S) R (colorGlueAdd T S col colSR) colR
      (maxArc_ge_SW (T.add S))]
    change colorGlueAdd T S col colSR T.SW = col T.SW
    rw [colorGlueAdd_of_le T S col colSR (maxArc_ge_SW T)]

/-! ## Associativity of `mul` as reindexing -/

theorem coloring_mul_assoc (T S R : TangleDiagram) (col : Nat → Int)
    (hc : ((T.mul S).mul R).IsColored col) :
    ∃ col', (T.mul (S.mul R)).IsColored col' ∧
      SameEndpointColors ((T.mul S).mul R) (T.mul (S.mul R)) col col' := by
  set colS := colorMulBottom T S col
  set colR := colorMulBottom (T.mul S) R col
  have hT : T.IsColored col := IsColored_mul_top (IsColored_mul_top hc)
  have hS : S.IsColored colS := IsColored_mul_bottom (IsColored_mul_top hc)
  have hR : R.IsColored colR := IsColored_mul_bottom hc
  have glueSR_NW : colS S.SW = colR R.NW := by
    dsimp [colS, colR]
    rw [colorMulBottom_SW, colorMulBottom_NW]
  have glueSR_NE : colS S.SE = colR R.NE ∨ R.NW = R.NE := by
    rcases colorMulBottom_NE (T.mul S) R col with h | h
    · exact Or.inl ((colorMulBottom_SE T S col).trans h.symm)
    · exact Or.inr h
  have hSR : (S.mul R).IsColored (colorGlueMul S R colS colR) :=
    IsColored_colorGlueMul S R colS colR hS hR glueSR_NW glueSR_NE
  have glueT_NW : col T.SW = colorGlueMul S R colS colR (S.mul R).NW := by
    change col T.SW = colorGlueMul S R colS colR S.NW
    rw [colorGlueMul_of_le S R colS colR (maxArc_ge_NW S)]
    dsimp [colS]
    rw [colorMulBottom_NW]
  have glueT_NE :
      col T.SE = colorGlueMul S R colS colR (S.mul R).NE ∨
        (S.mul R).NW = (S.mul R).NE := by
    change col T.SE = colorGlueMul S R colS colR S.NE ∨ S.NW = S.NE
    rw [colorGlueMul_of_le S R colS colR (maxArc_ge_NE S)]
    rcases colorMulBottom_NE T S col with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hE : (T.mul (S.mul R)).IsColored
      (colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR)) :=
    IsColored_colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR)
      hT hSR glueT_NW glueT_NE
  refine ⟨colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR), hE, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR) T.NW = col T.NW
    rw [colorGlueMul_of_le T (S.mul R) col (colorGlueMul S R colS colR)
      (maxArc_ge_NW T)]
  · change colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR) T.NE = col T.NE
    rw [colorGlueMul_of_le T (S.mul R) col (colorGlueMul S R colS colR)
      (maxArc_ge_NE T)]
  · have h1 :
        colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR)
          (T.mul (S.mul R)).SE =
        colorGlueMul S R colS colR (S.mul R).SE := by
      rw [mul_SE_glue T (S.mul R)]
      exact colorGlueMul_comp_shift T (S.mul R) col (colorGlueMul S R colS colR)
        glueT_NW glueT_NE (S.mul R).SE
    have h2 : colorGlueMul S R colS colR (S.mul R).SE = colR R.SE := by
      rw [mul_SE_glue S R]
      exact colorGlueMul_comp_shift S R colS colR glueSR_NW glueSR_NE R.SE
    rw [h1, h2]
    dsimp [colR]
    rw [colorMulBottom_SE]
  · have h1 :
        colorGlueMul T (S.mul R) col (colorGlueMul S R colS colR)
          (T.mul (S.mul R)).SW =
        colorGlueMul S R colS colR (S.mul R).SW := by
      rw [mul_SW_glue T (S.mul R)]
      exact colorGlueMul_comp_shift T (S.mul R) col (colorGlueMul S R colS colR)
        glueT_NW glueT_NE (S.mul R).SW
    have h2 : colorGlueMul S R colS colR (S.mul R).SW = colR R.SW := by
      rw [mul_SW_glue S R]
      exact colorGlueMul_comp_shift S R colS colR glueSR_NW glueSR_NE R.SW
    rw [h1, h2]
    dsimp [colR]
    rw [colorMulBottom_SW]

theorem coloring_mul_assoc_rev (T S R : TangleDiagram) (col : Nat → Int)
    (hc : (T.mul (S.mul R)).IsColored col) :
    ∃ col', ((T.mul S).mul R).IsColored col' ∧
      SameEndpointColors (T.mul (S.mul R)) ((T.mul S).mul R) col col' := by
  set colSR := colorMulBottom T (S.mul R) col
  set colR := colorMulBottom S R colSR
  have hT : T.IsColored col := IsColored_mul_top hc
  have hSR : (S.mul R).IsColored colSR := IsColored_mul_bottom hc
  have hS : S.IsColored colSR := IsColored_mul_top hSR
  have hR : R.IsColored colR := IsColored_mul_bottom hSR
  have glueTS_NW : col T.SW = colSR S.NW := by
    dsimp [colSR]
    -- `S.mul R` has the same NW as `S`.
    change col T.SW = colorMulBottom T (S.mul R) col (S.mul R).NW
    rw [colorMulBottom_NW]
  have glueTS_NE : col T.SE = colSR S.NE ∨ S.NW = S.NE := by
    change col T.SE = colSR (S.mul R).NE ∨ (S.mul R).NW = (S.mul R).NE
    rcases colorMulBottom_NE T (S.mul R) col with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hTS : (T.mul S).IsColored (colorGlueMul T S col colSR) :=
    IsColored_colorGlueMul T S col colSR hT hS glueTS_NW glueTS_NE
  have glueR_NW :
      colorGlueMul T S col colSR (T.mul S).SW = colR R.NW := by
    have h1 : colorGlueMul T S col colSR (T.mul S).SW = colSR S.SW := by
      rw [mul_SW_glue T S]
      exact colorGlueMul_comp_shift T S col colSR glueTS_NW glueTS_NE S.SW
    rw [h1]
    dsimp [colR]
    rw [colorMulBottom_NW]
  have glueR_NE :
      colorGlueMul T S col colSR (T.mul S).SE = colR R.NE ∨ R.NW = R.NE := by
    have h1 : colorGlueMul T S col colSR (T.mul S).SE = colSR S.SE := by
      rw [mul_SE_glue T S]
      exact colorGlueMul_comp_shift T S col colSR glueTS_NW glueTS_NE S.SE
    rw [h1]
    rcases colorMulBottom_NE S R colSR with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hE : ((T.mul S).mul R).IsColored
      (colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR) :=
    IsColored_colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR
      hTS hR glueR_NW glueR_NE
  refine ⟨colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR, hE, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR
        (T.mul S).NW = col T.NW
    rw [colorGlueMul_of_le (T.mul S) R (colorGlueMul T S col colSR) colR
      (maxArc_ge_NW (T.mul S))]
    change colorGlueMul T S col colSR T.NW = col T.NW
    rw [colorGlueMul_of_le T S col colSR (maxArc_ge_NW T)]
  · change colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR
        (T.mul S).NE = col T.NE
    rw [colorGlueMul_of_le (T.mul S) R (colorGlueMul T S col colSR) colR
      (maxArc_ge_NE (T.mul S))]
    change colorGlueMul T S col colSR T.NE = col T.NE
    rw [colorGlueMul_of_le T S col colSR (maxArc_ge_NE T)]
  · have h1 :
        colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR
          ((T.mul S).mul R).SE = colR R.SE := by
      rw [mul_SE_glue (T.mul S) R]
      exact colorGlueMul_comp_shift (T.mul S) R (colorGlueMul T S col colSR)
        colR glueR_NW glueR_NE R.SE
    rw [h1]
    dsimp [colR, colSR]
    rw [colorMulBottom_SE, colorMulBottom_SE]
  · have h1 :
        colorGlueMul (T.mul S) R (colorGlueMul T S col colSR) colR
          ((T.mul S).mul R).SW = colR R.SW := by
      rw [mul_SW_glue (T.mul S) R]
      exact colorGlueMul_comp_shift (T.mul S) R (colorGlueMul T S col colSR)
        colR glueR_NW glueR_NE R.SW
    rw [h1]
    dsimp [colR, colSR]
    rw [colorMulBottom_SW, colorMulBottom_SW]

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
  | add_zero T =>
    refine ⟨col, ?_, ?_⟩
    · simpa [add_zero_eq] using hc
    · simp [add_zero_eq, SameEndpointColors]
  | zero_add T =>
    exact coloring_zero_add T col hc
  | invert_unit s =>
    exact coloring_invert_unit s col hc
  | invert_unit_rev s =>
    exact coloring_invert_unit_rev s col hc
  | add_assoc T S R =>
    exact coloring_add_assoc T S R col hc
  | mul_assoc T S R =>
    exact coloring_mul_assoc T S R col hc
  | add_assoc_rev T S R =>
    exact coloring_add_assoc_rev T S R col hc
  | mul_assoc_rev T S R =>
    exact coloring_mul_assoc_rev T S R col hc

/-- Indexed Reidemeister III is a coloring-ready move, via the local model. -/
theorem ColoringIsotopy.of_IsReidemeisterIII {D E : TangleDiagram}
    (h : IsReidemeisterIII D E) : ColoringIsotopy D E :=
  .r3Local h.toLocal

/-- A Reidemeister generator is coloring-ready when both diagrams are
    well-formed (needed for R1/R2 coloring transport). Not a leftover
    `Isotopic` constructor. -/
theorem ColoringIsotopy.of_ReidemeisterMove {D E : TangleDiagram}
    (h : ReidemeisterMove D E) (hwD : D.WellFormed) (hwE : E.WellFormed) :
    ColoringIsotopy D E := by
  cases h with
  | r1 h => exact .r1 h hwD hwE
  | r2 h => exact .r2 h hwD hwE
  | r3 h => exact .of_IsReidemeisterIII h
  | isotopy h => exact .isotopy h

/-- The color matrix (hence `f`) is unchanged along `ColoringIsotopy`. -/
theorem coloring_fraction_ColoringIsotopy {D E : TangleDiagram}
    (h : ColoringIsotopy D E) (col : Nat → Int) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧
      ColorMatrix.of E col' = ColorMatrix.of D col ∧
      (ColorMatrix.of E col').fraction = (ColorMatrix.of D col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_ColoringIsotopy h col hc
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

theorem ColoringIsotopy.isotopy_symm {D E : TangleDiagram}
    (h : PlanarIsotopy D E) : ColoringIsotopy E D :=
  .isotopy h.symm

theorem ColoringIsotopy.localFlype_rev {D E : TangleDiagram}
    (h : IsLocalFlype D E) : ColoringIsotopy E D :=
  .localFlype h.symm

theorem ColoringIsotopy.r3Local_rev {D E : TangleDiagram}
    (h : IsReidemeisterIIILocal D E) : ColoringIsotopy E D :=
  .r3Local h.symm

/-- Reverse of `zero_add` when `T.NW ≠ T.SW`. Dummy-strand `NW = SW` is
    omitted: `[0]+T` then records unused SW name `1` while the reindex
    sends that arc to `0`. Not a fake reverse of unrestricted `zero_add`. -/
theorem ColoringIsotopy.zero_add_rev (T : TangleDiagram) (hne : T.NW ≠ T.SW) :
    ColoringIsotopy (TangleDiagram.zero.add T) T :=
  .isotopy (planar_zero_add T hne).symm

/-- Reverse a reversible coloring isotopy. Not `ColoringIsotopy.symm`:
    unrestricted `zero_add` (`NW = SW`) is omitted from
    `ReversibleColoringIsotopy`. `r3Local`, two-way-glue
    `add_right`/`mul_right`, `zero_add` when `NW ≠ SW`, and local flype
    are included. -/
theorem ReversibleColoringIsotopy.symm {D E : TangleDiagram}
    (h : ReversibleColoringIsotopy D E) : ReversibleColoringIsotopy E D := by
  induction h with
  | refl D => exact .refl D
  | trans h1 h2 ih1 ih2 => exact .trans ih2 ih1
  | r1 h hwD hwE => exact .r1 h.symm hwE hwD
  | r2 h hwD hwE => exact .r2 h.symm hwE hwD
  | r3Local h => exact .r3Local h.symm
  | localFlype h => exact .localFlype h.symm
  | isotopy h => exact .isotopy h.symm
  | add_left h ih => exact .add_left ih
  | add_right h hglue ih => exact .add_right ih hglue.symm
  | mul_left h ih => exact .mul_left ih
  | mul_right h hglue ih => exact .mul_right ih hglue.symm
  | add_zero T =>
    exact (congrArg (fun X => ReversibleColoringIsotopy X
      (T.add TangleDiagram.zero)) (add_zero_eq T)).mp (.refl _)
  | zero_add T hne => exact .isotopy (planar_zero_add T hne).symm
  | invert_unit s => exact .invert_unit_rev s
  | invert_unit_rev s => exact .invert_unit s
  | add_assoc T S R => exact .add_assoc_rev T S R
  | add_assoc_rev T S R => exact .add_assoc T S R
  | mul_assoc T S R => exact .mul_assoc_rev T S R
  | mul_assoc_rev T S R => exact .mul_assoc T S R

/-- Every `ColoringIsotopy` constructor has a reverse except unrestricted
    `zero_add` when `NW = SW` (dummy strand) and one-way
    `add_right`/`mul_right` glue without the converse identification.
    On the two-way-glue / `NW ≠ SW` fragment this is
    `ReversibleColoringIsotopy.symm`; a full `ColoringIsotopy.symm` by
    induction is therefore not proved. -/
theorem ColoringIsotopy.symm_of_reversible {D E : TangleDiagram}
    (h : ReversibleColoringIsotopy D E) : ColoringIsotopy E D :=
  h.symm.toColoringIsotopy

theorem coloring_ReversibleColoringIsotopy {D E : TangleDiagram}
    (h : ReversibleColoringIsotopy D E) (col : Nat → Int)
    (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' :=
  coloring_ColoringIsotopy h.toColoringIsotopy col hc

end RationalTangles
