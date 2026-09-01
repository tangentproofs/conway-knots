/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Init.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RationalTangles.ColoringInvariance
import RationalTangles.TangleFraction

/-!
# Coloring-fraction identities (Kauffman–Lambropoulou Theorem 4)

Without Reidemeister III or flype coloring, so without isotopy invariance
of `f`.
-/

namespace RationalTangles

def ColorMatrix.NotMono (M : ColorMatrix) : Prop :=
  ¬ (M.NW = M.NE ∧ M.NE = M.SE)

lemma divInt_add_one (n d : Int) (hd : d ≠ 0) :
    Rat.divInt n d + 1 = Rat.divInt (n + d) d := by
  have hdR : (d : Rat) ≠ 0 := Int.cast_ne_zero.mpr hd
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div, Int.cast_add]
  field_simp

lemma divInt_sub_one (n d : Int) (hd : d ≠ 0) :
    Rat.divInt n d + (-1 : Rat) = Rat.divInt (n - d) d := by
  have hdR : (d : Rat) ≠ 0 := Int.cast_ne_zero.mpr hd
  rw [Rat.divInt_eq_div, Rat.divInt_eq_div, Int.cast_sub]
  field_simp
  simp [sub_eq_add_neg]

namespace ColorMatrix

theorem fraction_hswap {M : ColorMatrix} (h : M.DiagonalSum) :
    M.hswap.fraction = M.fraction.neg := by
  unfold fraction hswap
  have hden : M.NW - M.SW = M.NE - M.SE := by
    simp [DiagonalSum] at h; omega
  have hnum : M.NW - M.NE = -(M.NE - M.NW) := by ring
  by_cases hd : M.NE - M.SE = 0
  · simp [hd, hden, CFValue.neg]
  · have hd' : M.NW - M.SW ≠ 0 := by intro hz; apply hd; omega
    simp [hd, hd', CFValue.neg]
    rw [hden, hnum]
    try simp [Rat.divInt_neg]

theorem fraction_rotate {M : ColorMatrix} (h : M.DiagonalSum) (hm : M.NotMono) :
    M.rotate.fraction = M.fraction.negInv := by
  unfold fraction rotate CFValue.negInv
  have hden : M.SE - M.SW = M.NE - M.NW := by
    simp [DiagonalSum] at h; omega
  have hnum : M.SE - M.NE = -(M.NE - M.SE) := by ring
  by_cases hd : M.NE - M.SE = 0
  · have hne : M.NE ≠ M.NW := by
      intro heq; exact hm ⟨heq.symm, by omega⟩
    have hd' : M.SE - M.SW ≠ 0 := by intro hz; apply hne; omega
    simp [hd, hd', CFValue.inv, CFValue.neg]
    have hnum0 : M.SE - M.NE = 0 := by omega
    simp [hnum0]
  · by_cases hn : M.NE - M.NW = 0
    · have hd' : M.SE - M.SW = 0 := by omega
      simp [hd, hn, hd', CFValue.inv, CFValue.neg]
    · have hd' : M.SE - M.SW ≠ 0 := by intro hz; apply hn; omega
      simp [hd, hd', hn, CFValue.inv, CFValue.neg]
      rw [hden, hnum]
      try simp [Rat.divInt_neg, Rat.inv_divInt]

theorem fraction_add_one {a b c d : Int} (_h : a + d = b + c) :
    (mk a (2 * b - d) c b).fraction = (mk a b c d).fraction.add 1 := by
  unfold fraction
  dsimp
  have hdenEq : (2 * b - d) - b = b - d := by ring
  have hnumEq : (2 * b - d) - a = (b - a) + (b - d) := by ring
  by_cases hd : b - d = 0
  · simp [hd, hdenEq, CFValue.add]
  · have hd' : (2 * b - d) - b ≠ 0 := by rwa [hdenEq]
    simp [hd, hd', CFValue.add]
    rw [hdenEq, hnumEq, ← divInt_add_one (b - a) (b - d) hd]

theorem fraction_add_negOne {a b c d : Int} (_h : a + d = b + c) :
    (mk a d c (2 * d - b)).fraction =
      (mk a b c d).fraction.add (.ofInt (-1)) := by
  unfold fraction
  dsimp
  have hdenEq : d - (2 * d - b) = b - d := by ring
  have hnumEq : d - a = (b - a) - (b - d) := by ring
  by_cases hd : b - d = 0
  · simp [hd, hdenEq, CFValue.add]
  · have hd' : d - (2 * d - b) ≠ 0 := by rwa [hdenEq]
    simp [hd, hd', CFValue.add, CFValue.ofInt]
    rw [hdenEq, hnumEq, ← divInt_sub_one (b - a) (b - d) hd]

end ColorMatrix

/-! ## Restriction of a coloring of `T.add S` / `T.mul S` -/

def addShift (T : TangleDiagram) : Nat → Nat :=
  (· + (T.maxArc + 1))

def addGlue (T S : TangleDiagram) : Nat → Nat :=
  fun a =>
    if a = S.NW + (T.maxArc + 1) then T.NE
    else if a = S.SW + (T.maxArc + 1) then T.SE
    else a

def colorAddRight (T S : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun a => col (addGlue T S (addShift T a))

def mulGlue (T S : TangleDiagram) : Nat → Nat :=
  fun a =>
    if a = S.NW + (T.maxArc + 1) then T.SW
    else if a = S.NE + (T.maxArc + 1) then T.SE
    else a

def colorMulBottom (T S : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun a => col (mulGlue T S (addShift T a))

theorem Crossing.rename_comp (f g : Nat → Nat) (C : Crossing) :
    (C.rename f).rename g = C.rename (g ∘ f) :=
  rfl

theorem add_crossings_append (T S : TangleDiagram) :
    (T.add S).crossings =
      T.crossings ++
        S.crossings.map (Crossing.rename (addGlue T S ∘ addShift T)) := by
  unfold TangleDiagram.add addGlue addShift
  simp [TangleDiagram.rename, List.map_map, Crossing.rename_comp]
  intro a ha; rfl

theorem mul_crossings_append (T S : TangleDiagram) :
    (T.mul S).crossings =
      T.crossings ++
        S.crossings.map (Crossing.rename (mulGlue T S ∘ addShift T)) := by
  unfold TangleDiagram.mul mulGlue addShift
  simp [TangleDiagram.rename, List.map_map, Crossing.rename_comp]
  intro a ha; rfl

theorem IsColored_add_left {T S : TangleDiagram} {col : Nat → Int}
    (h : (T.add S).IsColored col) : T.IsColored col := by
  intro C hC
  exact h C (by simp [add_crossings_append, hC])

theorem IsColored_add_right {T S : TangleDiagram} {col : Nat → Int}
    (h : (T.add S).IsColored col) :
    S.IsColored (colorAddRight T S col) := by
  intro C hC
  have hmem : Crossing.rename (addGlue T S ∘ addShift T) C ∈ (T.add S).crossings := by
    rw [add_crossings_append]
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))
  have hr := h _ hmem
  change ColoringRule C (col ∘ addGlue T S ∘ addShift T)
  simpa [ColoringRule_rename] using hr

theorem IsColored_mul_top {T S : TangleDiagram} {col : Nat → Int}
    (h : (T.mul S).IsColored col) : T.IsColored col := by
  intro C hC
  exact h C (by simp [mul_crossings_append, hC])

theorem IsColored_mul_bottom {T S : TangleDiagram} {col : Nat → Int}
    (h : (T.mul S).IsColored col) :
    S.IsColored (colorMulBottom T S col) := by
  intro C hC
  have hmem : Crossing.rename (mulGlue T S ∘ addShift T) C ∈ (T.mul S).crossings := by
    rw [mul_crossings_append]
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))
  have hr := h _ hmem
  change ColoringRule C (col ∘ mulGlue T S ∘ addShift T)
  simpa [ColoringRule_rename] using hr

theorem addGlue_NW (T S : TangleDiagram) :
    addGlue T S (S.NW + (T.maxArc + 1)) = T.NE := by
  simp [addGlue]

theorem addGlue_SW (T S : TangleDiagram) (h : S.NW ≠ S.SW) :
    addGlue T S (S.SW + (T.maxArc + 1)) = T.SE := by
  unfold addGlue
  have hne : S.SW + (T.maxArc + 1) ≠ S.NW + (T.maxArc + 1) := by
    intro h'; exact h (Nat.add_right_cancel h').symm
  rw [if_neg hne, if_pos rfl]

theorem mulGlue_NW (T S : TangleDiagram) :
    mulGlue T S (S.NW + (T.maxArc + 1)) = T.SW := by
  simp [mulGlue]

theorem mulGlue_NE (T S : TangleDiagram) (h : S.NW ≠ S.NE) :
    mulGlue T S (S.NE + (T.maxArc + 1)) = T.SE := by
  unfold mulGlue
  have hne : S.NE + (T.maxArc + 1) ≠ S.NW + (T.maxArc + 1) := by
    intro h'; exact h (Nat.add_right_cancel h').symm
  rw [if_neg hne, if_pos rfl]

theorem one_NW_ne_SW : one.NW ≠ one.SW := by decide
theorem one_NW_ne_NE : one.NW ≠ one.NE := by decide
theorem negOne_NW_ne_SW : negOne.NW ≠ negOne.SW := by
  simp [negOne, one, TangleDiagram.mirror]
theorem negOne_NW_ne_NE : negOne.NW ≠ negOne.NE := by
  simp [negOne, one, TangleDiagram.mirror]
theorem crossingTangle_NW_ne_SW (s : CrossingSign) :
    (crossingTangle s).NW ≠ (crossingTangle s).SW := by
  cases s with
  | pos => exact one_NW_ne_SW
  | neg => exact negOne_NW_ne_SW
theorem crossingTangle_NW_ne_NE (s : CrossingSign) :
    (crossingTangle s).NW ≠ (crossingTangle s).NE := by
  cases s with
  | pos => exact one_NW_ne_NE
  | neg => exact negOne_NW_ne_NE

theorem addGlue_shift_eq (T S : TangleDiagram) (a : Nat) :
    addGlue T S (a + (T.maxArc + 1)) =
      if a = S.NW then T.NE else if a = S.SW then T.SE else a + (T.maxArc + 1) := by
  unfold addGlue
  have hNW : a + (T.maxArc + 1) = S.NW + (T.maxArc + 1) ↔ a = S.NW :=
    ⟨fun h => Nat.add_right_cancel h, fun h => h ▸ rfl⟩
  have hSW : a + (T.maxArc + 1) = S.SW + (T.maxArc + 1) ↔ a = S.SW :=
    ⟨fun h => Nat.add_right_cancel h, fun h => h ▸ rfl⟩
  simp [hNW, hSW]

theorem ColorMatrix.of_add_right (T S : TangleDiagram) (col : Nat → Int)
    (h : S.NW ≠ S.SW) :
    ColorMatrix.of S (colorAddRight T S col) =
      { NW := col T.NE
        NE := col (T.add S).NE
        SW := col T.SE
        SE := col (T.add S).SE } := by
  simp only [ColorMatrix.of, colorAddRight, addShift, addGlue_shift_eq]
  simp [TangleDiagram.add, TangleDiagram.rename, h.symm]

theorem mulGlue_shift_eq (T S : TangleDiagram) (a : Nat) :
    mulGlue T S (a + (T.maxArc + 1)) =
      if a = S.NW then T.SW else if a = S.NE then T.SE else a + (T.maxArc + 1) := by
  unfold mulGlue
  have hNW : a + (T.maxArc + 1) = S.NW + (T.maxArc + 1) ↔ a = S.NW :=
    ⟨fun h => Nat.add_right_cancel h, fun h => h ▸ rfl⟩
  have hNE : a + (T.maxArc + 1) = S.NE + (T.maxArc + 1) ↔ a = S.NE :=
    ⟨fun h => Nat.add_right_cancel h, fun h => h ▸ rfl⟩
  simp [hNW, hNE]

theorem ColorMatrix.of_mul_bottom (T S : TangleDiagram) (col : Nat → Int)
    (h : S.NW ≠ S.NE) :
    ColorMatrix.of S (colorMulBottom T S col) =
      { NW := col T.SW
        NE := col T.SE
        SW := col (T.mul S).SW
        SE := col (T.mul S).SE } := by
  simp only [ColorMatrix.of, colorMulBottom, addShift, mulGlue_shift_eq]
  simp [TangleDiagram.mul, TangleDiagram.rename, h.symm]

/-! ## Diagonal sum -/

theorem zero_diagonal_any (col : Nat → Int) :
    (ColorMatrix.of TangleDiagram.zero col).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.zero]

theorem infinity_diagonal_any (col : Nat → Int) :
    (ColorMatrix.of TangleDiagram.infinity col).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.infinity]
  omega

theorem one_diagonal_any (col : Nat → Int) (h : one.IsColored col) :
    (ColorMatrix.of one col).DiagonalSum := by
  obtain ⟨hβ, hrule⟩ := h ⟨0, 1, 2, 3, CrossingSign.pos⟩ (by simp [one])
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, one, hβ, hrule]
  omega

theorem negOne_diagonal_any (col : Nat → Int) (h : negOne.IsColored col) :
    (ColorMatrix.of negOne col).DiagonalSum := by
  have hmem : { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
      negOne.crossings := by
    simp [negOne, one, TangleDiagram.mirror, Crossing.switch, CrossingSign.flip]
  obtain ⟨hβ, hrule⟩ := h _ hmem
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, negOne, one, TangleDiagram.mirror,
    Crossing.switch] at hβ hrule ⊢
  omega

theorem crossingTangle_diagonal_any (s : CrossingSign) (col : Nat → Int)
    (h : (crossingTangle s).IsColored col) :
    (ColorMatrix.of (crossingTangle s) col).DiagonalSum := by
  cases s with
  | pos => exact one_diagonal_any col h
  | neg => exact negOne_diagonal_any col h

theorem ColorMatrix.DiagonalSum_of_add {T S : TangleDiagram} {col : Nat → Int}
    (hSW : S.NW ≠ S.SW)
    (hT : (ColorMatrix.of T col).DiagonalSum)
    (hS : (ColorMatrix.of S (colorAddRight T S col)).DiagonalSum) :
    (ColorMatrix.of (T.add S) col).DiagonalSum := by
  have hS' := hS
  rw [ColorMatrix.of_add_right T S col hSW] at hS'
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.add] at hT hS' ⊢
  omega

theorem ColorMatrix.DiagonalSum_of_mul {T S : TangleDiagram} {col : Nat → Int}
    (hNE : S.NW ≠ S.NE)
    (hT : (ColorMatrix.of T col).DiagonalSum)
    (hS : (ColorMatrix.of S (colorMulBottom T S col)).DiagonalSum) :
    (ColorMatrix.of (T.mul S) col).DiagonalSum := by
  have hS' := hS
  rw [ColorMatrix.of_mul_bottom T S col hNE] at hS'
  simp [ColorMatrix.DiagonalSum, ColorMatrix.of, TangleDiagram.mul] at hT hS' ⊢
  omega

theorem standard_coloring_diagonal (e : StandardExpr) (col : Nat → Int)
    (h : e.diagram.IsColored col) :
    (ColorMatrix.of e.diagram col).DiagonalSum := by
  induction e generalizing col with
  | zero => simpa [StandardExpr.diagram] using zero_diagonal_any col
  | infinity => simpa [StandardExpr.diagram] using infinity_diagonal_any col
  | addRight e s ih =>
    simp [StandardExpr.diagram] at h ⊢
    exact ColorMatrix.DiagonalSum_of_add (crossingTangle_NW_ne_SW s)
      (ih col (IsColored_add_left h))
      (crossingTangle_diagonal_any s _ (IsColored_add_right h))
  | mulBottom e s ih =>
    simp [StandardExpr.diagram] at h ⊢
    exact ColorMatrix.DiagonalSum_of_mul (crossingTangle_NW_ne_NE s)
      (ih col (IsColored_mul_top h))
      (crossingTangle_diagonal_any s _ (IsColored_mul_bottom h))

theorem standardForm_coloring_diagonal {T : TangleDiagram} (hT : IsStandardForm T)
    (col : Nat → Int) (h : T.IsColored col) :
    (ColorMatrix.of T col).DiagonalSum := by
  obtain ⟨e, rfl⟩ := hT
  exact standard_coloring_diagonal e col h

/-! ## Additivity (Theorem 4.3) -/

theorem coloring_fraction_add (T S : TangleDiagram) (col : Nat → Int)
    (hSW : S.NW ≠ S.SW)
    (hS : (ColorMatrix.of S (colorAddRight T S col)).DiagonalSum) :
    (ColorMatrix.of T col).fraction.add
        (ColorMatrix.of S (colorAddRight T S col)).fraction =
      (ColorMatrix.of (T.add S) col).fraction := by
  rw [ColorMatrix.of_add_right T S col hSW]
  have hdiag : col T.NE - col T.SE =
      col (T.add S).NE - col (T.add S).SE := by
    have hS' := hS
    rw [ColorMatrix.of_add_right T S col hSW] at hS'
    simp [ColorMatrix.DiagonalSum] at hS'
    omega
  simpa [ColorMatrix.of, TangleDiagram.add] using
    ColorMatrix.fraction_add_glue (col T.NW) (col T.NE) (col T.SW) (col T.SE)
      (col (T.add S).NE) (col (T.add S).SE) hdiag

theorem coloring_fraction_add_crossing (T : TangleDiagram) (s : CrossingSign)
    (col : Nat → Int) (hcol : (T.add (crossingTangle s)).IsColored col) :
    (ColorMatrix.of T col).fraction.add
        (ColorMatrix.of (crossingTangle s)
          (colorAddRight T (crossingTangle s) col)).fraction =
      (ColorMatrix.of (T.add (crossingTangle s)) col).fraction :=
  coloring_fraction_add T (crossingTangle s) col (crossingTangle_NW_ne_SW s)
    (crossingTangle_diagonal_any s _ (IsColored_add_right hcol))

/-! ## Rotation and vertical reflect -/

theorem coloring_fraction_rotate (T : TangleDiagram) (col : Nat → Int)
    (h : (ColorMatrix.of T col).DiagonalSum)
    (hm : (ColorMatrix.of T col).NotMono) :
    (ColorMatrix.of T.rotate col).fraction =
      (ColorMatrix.of T col).fraction.negInv := by
  rw [ColorMatrix.of_rotate]
  exact ColorMatrix.fraction_rotate h hm

theorem coloring_fraction_vflip_neg (T : TangleDiagram) (col : Nat → Int)
    (h : (ColorMatrix.of T col).DiagonalSum) :
    (ColorMatrix.of (-T).vflip col).fraction =
      (ColorMatrix.of T col).fraction.neg := by
  rw [vertical_reflect_matrix]
  exact ColorMatrix.fraction_hswap h

/-! ## Color matrices after adjoining `[±1]` -/

theorem colorAddOne_old_arc (T : TangleDiagram) (col : Nat → Int) {x : Nat}
    (hx : x ≤ T.maxArc) : colorAddOne T col x = col x :=
  colorAddOne_old (by omega) (by omega)

theorem ColorMatrix.of_add_one (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of (T.add one) (colorAddOne T col) =
      { NW := col T.NW
        NE := 2 * col T.NE - col T.SE
        SW := col T.SW
        SE := col T.NE } := by
  have hNW := colorAddOne_old_arc T col (maxArc_ge_NW T)
  have hSW := colorAddOne_old_arc T col (maxArc_ge_SW T)
  have hNE : colorAddOne T col (T.maxArc + 2) = 2 * col T.NE - col T.SE := by
    simp [colorAddOne]
  have hSE' : colorAddOne T col (T.maxArc + 3) = col T.NE := by
    have : T.maxArc + 3 ≠ T.maxArc + 2 := by omega
    simp [colorAddOne, this]
  simp [ColorMatrix.of, add_one_NW, add_one_SW, add_one_NE, add_one_SE, hNW, hSW, hNE, hSE']

theorem colorAddNegOne_old_arc (T : TangleDiagram) (col : Nat → Int) {x : Nat}
    (hx : x ≤ T.maxArc) : colorAddNegOne T col x = col x :=
  colorAddNegOne_old (by omega) (by omega)

theorem add_negOne_NE (T : TangleDiagram) : (T.add negOne).NE = T.maxArc + 2 := by
  unfold TangleDiagram.add
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename]

theorem add_negOne_SE (T : TangleDiagram) : (T.add negOne).SE = T.maxArc + 3 := by
  unfold TangleDiagram.add
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename]

theorem ColorMatrix.of_add_negOne (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of (T.add negOne) (colorAddNegOne T col) =
      { NW := col T.NW
        NE := col T.SE
        SW := col T.SW
        SE := 2 * col T.SE - col T.NE } := by
  have hNW := colorAddNegOne_old_arc T col (maxArc_ge_NW T)
  have hSW := colorAddNegOne_old_arc T col (maxArc_ge_SW T)
  have hNE : colorAddNegOne T col (T.maxArc + 2) = col T.SE := by
    simp [colorAddNegOne]
  have hSE : colorAddNegOne T col (T.maxArc + 3) = 2 * col T.SE - col T.NE := by
    have : T.maxArc + 3 ≠ T.maxArc + 2 := by omega
    simp [colorAddNegOne, this]
  simp only [ColorMatrix.of]
  rw [show (T.add negOne).NW = T.NW from rfl,
      show (T.add negOne).SW = T.SW from rfl,
      add_negOne_NE, add_negOne_SE, hNW, hSW, hNE, hSE]

theorem colorMulOne_old_arc (T : TangleDiagram) (col : Nat → Int) {x : Nat}
    (hx : x ≤ T.maxArc) : colorMulOne T col x = col x :=
  colorMulOne_old (by omega) (by omega)

theorem mul_one_SE (T : TangleDiagram) : (T.mul one).SE = T.maxArc + 3 := by
  unfold TangleDiagram.mul
  rw [one_rename_shift]
  simp [TangleDiagram.rename]

theorem mul_one_SW (T : TangleDiagram) : (T.mul one).SW = T.maxArc + 4 := by
  unfold TangleDiagram.mul
  rw [one_rename_shift]
  simp [TangleDiagram.rename]

theorem ColorMatrix.of_mul_one (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of (T.mul one) (colorMulOne T col) =
      { NW := col T.NW
        NE := col T.NE
        SW := 2 * col T.SW - col T.SE
        SE := col T.SW } := by
  have hNW := colorMulOne_old_arc T col (maxArc_ge_NW T)
  have hNE := colorMulOne_old_arc T col (maxArc_ge_NE T)
  have hSE : colorMulOne T col (T.maxArc + 3) = col T.SW := by
    simp [colorMulOne]
  have hSW : colorMulOne T col (T.maxArc + 4) = 2 * col T.SW - col T.SE := by
    have : T.maxArc + 4 ≠ T.maxArc + 3 := by omega
    simp [colorMulOne, this]
  simp only [ColorMatrix.of]
  rw [show (T.mul one).NW = T.NW from rfl,
      show (T.mul one).NE = T.NE from rfl,
      mul_one_SE, mul_one_SW, hNW, hNE, hSE, hSW]

theorem colorMulNegOne_old_arc (T : TangleDiagram) (col : Nat → Int) {x : Nat}
    (hx : x ≤ T.maxArc) : colorMulNegOne T col x = col x :=
  colorMulNegOne_old (by omega) (by omega)

theorem mul_negOne_SE (T : TangleDiagram) : (T.mul negOne).SE = T.maxArc + 3 := by
  unfold TangleDiagram.mul
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename]

theorem mul_negOne_SW (T : TangleDiagram) : (T.mul negOne).SW = T.maxArc + 4 := by
  unfold TangleDiagram.mul
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename]

theorem ColorMatrix.of_mul_negOne (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of (T.mul negOne) (colorMulNegOne T col) =
      { NW := col T.NW
        NE := col T.NE
        SW := col T.SE
        SE := 2 * col T.SE - col T.SW } := by
  have hNW := colorMulNegOne_old_arc T col (maxArc_ge_NW T)
  have hNE := colorMulNegOne_old_arc T col (maxArc_ge_NE T)
  have hSE : colorMulNegOne T col (T.maxArc + 3) = 2 * col T.SE - col T.SW := by
    simp [colorMulNegOne]
  have hSW : colorMulNegOne T col (T.maxArc + 4) = col T.SE := by
    have : T.maxArc + 4 ≠ T.maxArc + 3 := by omega
    simp [colorMulNegOne, this]
  simp only [ColorMatrix.of]
  rw [show (T.mul negOne).NW = T.NW from rfl,
      show (T.mul negOne).NE = T.NE from rfl,
      mul_negOne_SE, mul_negOne_SW, hNW, hNE, hSE, hSW]

namespace ColorMatrix

theorem fraction_mul_one {a b c d : Int} (h : a + d = b + c)
    (hm : ¬ (a = b ∧ b = d)) :
    (mk a b (2 * c - d) c).fraction =
      ((mk a b c d).fraction.inv.add 1).inv := by
  unfold fraction
  dsimp
  by_cases hd : b - d = 0
  · have hab : a ≠ b := by intro hab; exact hm ⟨hab, by omega⟩
    have hac : a = c := by omega
    have hbc : b - c ≠ 0 := by omega
    simp [hd, hbc, CFValue.inv, CFValue.add, hac, show b - c = b - a by omega]
    have ha : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hz : (b : Rat) - a ≠ 0 := by exact_mod_cast ha
    rw [Rat.divInt_eq_div]
    field_simp
    simp [ha]
  · by_cases hb : b - c = 0
    · have ha : b - a ≠ 0 := by intro hz; omega
      have hsum : (b - d) + (b - a) = 0 := by omega
      simp [hd, hb, ha, CFValue.inv, CFValue.add]
      rw [divInt_add_one _ _ ha, hsum]
      simp [Rat.divInt_eq_zero ha]
    · by_cases ha : b - a = 0
      · simp [hd, hb, ha, CFValue.inv, CFValue.add]
      · have hsum : (b - d) + (b - a) = b - c := by omega
        simp [hd, hb, ha, CFValue.inv, CFValue.add]
        rw [divInt_add_one _ _ ha, hsum]
        have hnz : Rat.divInt (b - c) (b - a) ≠ 0 := (Rat.divInt_ne_zero ha).mpr hb
        rw [if_neg hnz, Rat.inv_divInt]

theorem fraction_mul_negOne {a b c d : Int} (h : a + d = b + c)
    (hm : ¬ (a = b ∧ b = d)) :
    (mk a b d (2 * d - c)).fraction =
      ((mk a b c d).fraction.inv.add (.ofInt (-1))).inv := by
  unfold fraction
  dsimp
  by_cases hd : b - d = 0
  · have hab : a ≠ b := by intro hab; exact hm ⟨hab, by omega⟩
    have hac : a = c := by omega
    have hden : b - (2 * d - c) ≠ 0 := by omega
    have hz : (b : Rat) - (2 * d - c) ≠ 0 := by exact_mod_cast hden
    simp [hd, hden, hac, CFValue.inv, CFValue.add, CFValue.ofInt]
    have hden' : b - (2 * d - c) = -(b - a) := by omega
    rw [hden', Rat.divInt_neg]
    have ha : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    simp [Rat.divInt_eq_div, ha]
    have hz' : (b : Rat) - a ≠ 0 := by exact_mod_cast ha
    have hcab : (c : Rat) ≠ b := by
      intro hcb
      have : c = b := by exact_mod_cast hcb
      exact hab (hac.trans this)
    field_simp
    rw [hac]
    ring
  · by_cases hb : b - (2 * d - c) = 0
    · have ha : b - a ≠ 0 := by intro hz; omega
      have hsum : (b - d) - (b - a) = 0 := by omega
      simp [hd, hb, ha, CFValue.inv, CFValue.add, CFValue.ofInt]
      rw [divInt_sub_one _ _ ha, hsum]
      simp [Rat.divInt_eq_zero ha]
    · by_cases ha : b - a = 0
      · simp [hd, hb, ha, CFValue.inv, CFValue.add, CFValue.ofInt]
      · have hsum : (b - d) - (b - a) = b - (2 * d - c) := by omega
        simp [hd, hb, ha, hsum, CFValue.inv, CFValue.add, CFValue.ofInt]
        rw [divInt_sub_one _ _ ha, hsum]
        have hnz : Rat.divInt (b - (2 * d - c)) (b - a) ≠ 0 :=
          (Rat.divInt_ne_zero ha).mpr hb
        simp [hnz]

end ColorMatrix

/-! ## `f = F` on standard-form expressions -/

def StandardExpr.fraction : StandardExpr → CFValue
  | zero => 0
  | infinity => .inf
  | addRight e .pos => e.fraction.add 1
  | addRight e .neg => e.fraction.add (.ofInt (-1))
  | mulBottom e .pos => (e.fraction.inv.add 1).inv
  | mulBottom e .neg => (e.fraction.inv.add (.ofInt (-1))).inv

theorem StandardExpr.colorFrom_diagonal (e : StandardExpr) (a c : Int) :
    (ColorMatrix.of e.diagram (e.colorFrom a c)).DiagonalSum :=
  standard_coloring_diagonal e (e.colorFrom a c) (e.colorFrom_isColored a c)

theorem StandardExpr.colorFrom_notMono (e : StandardExpr) :
    (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NotMono := by
  induction e with
  | zero =>
    simp [StandardExpr.diagram, StandardExpr.colorFrom, ColorMatrix.NotMono,
      ColorMatrix.of, TangleDiagram.zero, colorZero]
  | infinity =>
    simp [StandardExpr.diagram, StandardExpr.colorFrom, ColorMatrix.NotMono,
      ColorMatrix.of, TangleDiagram.infinity, colorInfinity]
  | addRight e s ih =>
    have hd := e.colorFrom_diagonal 0 1
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_add_one]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih hd ⊢
      omega
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_add_negOne]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih hd ⊢
      omega
  | mulBottom e s ih =>
    have hd := e.colorFrom_diagonal 0 1
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_mul_one]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih hd ⊢
      omega
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_mul_negOne]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih hd ⊢
      omega

theorem StandardExpr.colorFrom_eq_fraction (e : StandardExpr) :
    (ColorMatrix.of e.diagram (e.colorFrom 0 1)).fraction = e.fraction := by
  induction e with
  | zero =>
    have h : (0 : Int) ≠ 1 := by decide
    simpa [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction]
      using zero_fraction (a := (0 : Int)) (c := (1 : Int)) h
  | infinity =>
    have h : (0 : Int) ≠ 1 := by decide
    simpa [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction]
      using infinity_fraction (a := (0 : Int)) (b := (1 : Int)) h
  | addRight e s ih =>
    have hd := e.colorFrom_diagonal 0 1
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction,
        crossingTangle]
      erw [ColorMatrix.of_add_one]
      have h := ColorMatrix.fraction_add_one
        (a := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW)
        (b := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE)
        (c := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SW)
        (d := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) hd
      simp [ColorMatrix.of] at h
      simp [ColorMatrix.of] at ih
      exact h.trans (by rw [ih])
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction,
        crossingTangle]
      erw [ColorMatrix.of_add_negOne]
      have h := ColorMatrix.fraction_add_negOne
        (a := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW)
        (b := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE)
        (c := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SW)
        (d := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) hd
      simp [ColorMatrix.of] at h
      simp [ColorMatrix.of] at ih
      exact h.trans (by rw [ih])
  | mulBottom e s ih =>
    have hd := e.colorFrom_diagonal 0 1
    have hm := e.colorFrom_notMono
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction,
        crossingTangle]
      erw [ColorMatrix.of_mul_one]
      have hne : ¬ ((ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW =
          (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE ∧
          (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE =
            (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) := hm
      have h := ColorMatrix.fraction_mul_one
        (a := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW)
        (b := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE)
        (c := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SW)
        (d := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) hd hne
      simp [ColorMatrix.of] at h
      simp [ColorMatrix.of] at ih
      exact h.trans (by rw [ih])
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, StandardExpr.fraction,
        crossingTangle]
      erw [ColorMatrix.of_mul_negOne]
      have hne : ¬ ((ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW =
          (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE ∧
          (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE =
            (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) := hm
      have h := ColorMatrix.fraction_mul_negOne
        (a := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW)
        (b := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE)
        (c := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SW)
        (d := (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE) hd hne
      simp [ColorMatrix.of] at h
      simp [ColorMatrix.of] at ih
      exact h.trans (by rw [ih])

/-- On a standard-form diagram, the propagated coloring with initial
    colors `0, 1` has coloring fraction equal to the arithmetical
    fraction of the expression. -/
theorem standard_coloring_eq_fraction (e : StandardExpr) :
    ∃ col, e.diagram.IsColored col ∧
      (ColorMatrix.of e.diagram col).DiagonalSum ∧
      (ColorMatrix.of e.diagram col).NotMono ∧
      (ColorMatrix.of e.diagram col).fraction = e.fraction :=
  ⟨e.colorFrom 0 1, e.colorFrom_isColored 0 1, e.colorFrom_diagonal 0 1,
    e.colorFrom_notMono, e.colorFrom_eq_fraction⟩

end RationalTangles
