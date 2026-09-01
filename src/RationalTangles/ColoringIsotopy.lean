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

theorem Crossing.rotate180_rename (f : Nat → Nat) (C : Crossing) :
    (C.rename f).rotate180 = C.rotate180.rename f :=
  rfl

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

-- Slice 2 blocker: t.rot180+[±1] is a planar reindexing of ([±1]+t).rot180
-- (flypeSlideAddFun, flypeSlideAdd_map_t). An injective f identifies rotated
-- disc endpoints, so planar/colorFlype transport gives the 180-degree color
-- matrix, not SameEndpointColors of the unrotated diagrams. The affine map
-- sending a color x to (NW+SE)-x restores the matrix iff DiagonalSum holds;
-- that fails for some well-formed t (crossingless diagonal NW=SE, NE=SW), so
-- the un-hypothesized coloring theorem is false and no ColoringIsotopy
-- constructor is added. The vertical flype_slide_mul case is the same.

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
