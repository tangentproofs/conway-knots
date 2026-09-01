/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Init.Data.Rat.Lemmas
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RationalTangles.Tangle
import RationalTangles.IntegerTangle
import RationalTangles.Flip
import RationalTangles.Rational
import RationalTangles.ContinuedFraction

/-!
# Integral coloring

Colors are integers. At a crossing, the two under-arcs `α`, `γ` and the
over-arc `β` satisfy `α + γ = 2β` (Kauffman–Lambropoulou §5, Figure 20).
The overstrand occupies ports `0` and `2` of the PD-code, so those two
ports carry the same color `β`.

`τ β α := 2β - α` produces the remaining under-arc color. An integral
coloring of a diagram is an assignment of an integer to every arc
identifier that satisfies the rule at every crossing.

The color matrix records the four boundary colors, and the coloring
fraction is the extended rational `(NE - NW) / (NE - SE)`. Affine
recoloring `n· + k` preserves the coloring rule and, for `n ≠ 0`, the
coloring fraction.
-/

namespace RationalTangles

/-- The remaining under-arc color: `τ_β(α) = 2β - α`. -/
def tau (β α : Int) : Int :=
  2 * β - α

/-- The coloring rule at a crossing: overstrand ports share a color `β`,
    and the two under-arc colors `α`, `γ` satisfy `α + γ = 2β`. -/
def ColoringRule (C : Crossing) (col : Nat → Int) : Prop :=
  col C.a0 = col C.a2 ∧ col C.a1 + col C.a3 = 2 * col C.a0

/-- An integral coloring of a 2-tangle diagram. -/
def TangleDiagram.IsColored (D : TangleDiagram) (col : Nat → Int) : Prop :=
  ∀ C ∈ D.crossings, ColoringRule C col

/-- The 2×2 matrix of boundary colors
    `[[NW, NE], [SW, SE]]`. -/
structure ColorMatrix where
  NW : Int
  NE : Int
  SW : Int
  SE : Int
  deriving DecidableEq, Repr

namespace ColorMatrix

/-- Boundary colors of a diagram under an arc coloring. -/
def of (D : TangleDiagram) (col : Nat → Int) : ColorMatrix where
  NW := col D.NW
  NE := col D.NE
  SW := col D.SW
  SE := col D.SE

/-- Affine recoloring of a color matrix: `M ↦ nM + k`. -/
def affine (M : ColorMatrix) (n k : Int) : ColorMatrix where
  NW := n * M.NW + k
  NE := n * M.NE + k
  SW := n * M.SW + k
  SE := n * M.SE + k

/-- The coloring fraction `f = (NE - NW) / (NE - SE)`, with
    `∞ = 1/0` when the denominator vanishes. -/
def fraction (M : ColorMatrix) : CFValue :=
  if M.NE - M.SE = 0 then .inf
  else .ofRat (Rat.divInt (M.NE - M.NW) (M.NE - M.SE))

end ColorMatrix

/-- Recoloring every arc by `α ↦ nα + k` preserves the coloring rule. -/
theorem coloring_affine (D : TangleDiagram) (col : Nat → Int) (n k : Int)
    (h : D.IsColored col) :
    D.IsColored (fun a => n * col a + k) := by
  intro C hC
  obtain ⟨hβ, hrule⟩ := h C hC
  constructor
  · simp [hβ]
  · calc
      (n * col C.a1 + k) + (n * col C.a3 + k)
          = n * (col C.a1 + col C.a3) + (k + k) := by ring
      _ = n * (2 * col C.a0) + (k + k) := by rw [hrule]
      _ = 2 * (n * col C.a0 + k) := by ring

/-- For `n ≠ 0`, affine recoloring does not change the coloring fraction. -/
theorem ColorMatrix.fraction_affine (M : ColorMatrix) (n k : Int) (hn : n ≠ 0) :
    (M.affine n k).fraction = M.fraction := by
  unfold ColorMatrix.affine ColorMatrix.fraction
  have hnum : n * M.NE + k - (n * M.NW + k) = n * (M.NE - M.NW) := by ring
  have hden : n * M.NE + k - (n * M.SE + k) = n * (M.NE - M.SE) := by ring
  rw [hnum, hden]
  by_cases hd : M.NE - M.SE = 0
  · simp [hd]
  · have hd' : n * (M.NE - M.SE) ≠ 0 := mul_ne_zero hn hd
    simp [hd, hd']
    rw [mul_comm n (M.NE - M.NW), mul_comm n (M.NE - M.SE)]
    exact Rat.divInt_mul_right hn

theorem ColorMatrix.of_affineMap (D : TangleDiagram) (col : Nat → Int) (n k : Int) :
    ColorMatrix.of D (fun a => n * col a + k) = (ColorMatrix.of D col).affine n k :=
  rfl

/-! ## Algebra of `τ` and the coloring rule -/

@[simp] theorem tau_apply (β α : Int) : tau β α = 2 * β - α := rfl

theorem tau_involutive (β α : Int) : tau β (tau β α) = α := by
  unfold tau; ring

theorem tau_fixed (α : Int) : tau α α = α := by
  unfold tau; ring

/-- Self-distributivity of `τ`, the local identity of Reidemeister III. -/
theorem tau_self_distrib (β γ α : Int) :
    tau (tau β γ) (tau β α) = tau β (tau γ α) := by
  unfold tau; ring

/-- Recolor after switching over/under at `C`: the four incident arcs all
    receive the old over-color `β`. The switched crossing is then monochrome,
    so `ColoringRule` holds. -/
def recolorSwitch (C : Crossing) (col : Nat → Int) (a : Nat) : Int :=
  if a = C.a0 ∨ a = C.a1 ∨ a = C.a2 ∨ a = C.a3 then col C.a0 else col a

theorem recolorSwitch_mem (C : Crossing) (col : Nat → Int) {a : Nat}
    (h : a = C.a0 ∨ a = C.a1 ∨ a = C.a2 ∨ a = C.a3) :
    recolorSwitch C col a = col C.a0 := by
  simp [recolorSwitch, h]

theorem ColoringRule_switch_recolor (C : Crossing) (col : Nat → Int)
    (h : ColoringRule C col) :
    ColoringRule C.switch (recolorSwitch C col) := by
  obtain ⟨hβ, hr⟩ := h
  constructor
  · simp [Crossing.switch, recolorSwitch]
  · simp [Crossing.switch, recolorSwitch]; ring

/-- Recolor `C.switch` by swapping each over-arc with the adjacent under-arc
    (`a0↔a1`, `a2↔a3`). Locally the new overstrand is monochrome with the old
    over-color, so `ColoringRule` holds. This is not a global map on a whole
    diagram: shared arcs of adjacent crossings need not agree. -/
def colorSwitchPorts (C : Crossing) (col : Nat → Int) (a : Nat) : Int :=
  if a = C.a0 then col C.a1
  else if a = C.a1 then col C.a0
  else if a = C.a2 then col C.a3
  else if a = C.a3 then col C.a2
  else col a

/-- Port permutation `0↔1`, `2↔3` used to color `[±1]` after a switch. -/
def colorMirrorUnit (col : Nat → Int) (a : Nat) : Int :=
  if a = 0 then col 1
  else if a = 1 then col 0
  else if a = 2 then col 3
  else if a = 3 then col 2
  else col a

theorem ColoringRule_rotate180 (C : Crossing) (col : Nat → Int)
    (h : ColoringRule C col) : ColoringRule C.rotate180 col := by
  obtain ⟨hβ, hr⟩ := h
  constructor
  · simpa [Crossing.rotate180] using hβ.symm
  · simp [Crossing.rotate180]
    linarith

theorem ColoringRule_reverseUnders (C : Crossing) (col : Nat → Int)
    (h : ColoringRule C col) : ColoringRule C.reverseUnders col := by
  obtain ⟨hβ, hr⟩ := h
  constructor
  · simpa [Crossing.reverseUnders] using hβ
  · simp [Crossing.reverseUnders]; linarith

theorem ColoringRule_sameUpToRotation {C D : Crossing} (col : Nat → Int)
    (h : C.sameUpToRotation D) (hc : ColoringRule C col) :
    ColoringRule D col := by
  rcases h with rfl | hrot | hrev | hrr
  · exact hc
  · have hD : D = C.rotate180 := by
      rw [hrot, Crossing.rotate180_involutive]
    rw [hD]
    exact ColoringRule_rotate180 C col hc
  · have hD : D = C.reverseUnders := by
      rw [hrev, Crossing.reverseUnders_involutive]
    rw [hD]
    exact ColoringRule_reverseUnders C col hc
  · have hD : D = C.rotate180.reverseUnders := by
      rw [hrr, Crossing.rotate180_involutive, Crossing.reverseUnders_involutive]
    rw [hD]
    exact ColoringRule_reverseUnders _ col (ColoringRule_rotate180 C col hc)

@[simp] theorem ColoringRule_rename (f : Nat → Nat) (C : Crossing) (col : Nat → Int) :
    ColoringRule (C.rename f) col ↔ ColoringRule C (col ∘ f) :=
  Iff.rfl

theorem IsColored_rename (D : TangleDiagram) (f : Nat → Nat) (col : Nat → Int) :
    (D.rename f).IsColored col ↔ D.IsColored (col ∘ f) := by
  constructor
  · intro h C hC
    have : C.rename f ∈ (D.rename f).crossings := by
      simp [TangleDiagram.rename, List.mem_map]
      exact ⟨C, hC, rfl⟩
    exact h _ this
  · intro h C hC
    simp [TangleDiagram.rename, List.mem_map] at hC
    obtain ⟨C0, hC0, rfl⟩ := hC
    exact h C0 hC0

theorem IsColored_rename_injective (D : TangleDiagram) (f : Nat → Nat)
    (hf : Function.Injective f) (col : Nat → Int) (h : D.IsColored col) :
    (D.rename f).IsColored (fun b => col (Function.invFun f b)) := by
  rw [IsColored_rename]
  have : (fun b => col (Function.invFun f b)) ∘ f = col := by
    funext a
    simp [Function.leftInverse_invFun hf a]
  simpa [this] using h

/-- The constant coloring (the degenerate affine case `n = 0`). -/
theorem isColored_const (D : TangleDiagram) (k : Int) :
    D.IsColored (fun _ => k) := by
  intro C _
  constructor
  · rfl
  · ring

/-- Endpoint colors of two diagrams under (possibly different) colorings. -/
def SameEndpointColors (D E : TangleDiagram) (col col' : Nat → Int) : Prop :=
  col' E.NW = col D.NW ∧ col' E.NE = col D.NE ∧
    col' E.SE = col D.SE ∧ col' E.SW = col D.SW

/-! ## Color-matrix arithmetic -/

namespace ColorMatrix

/-- The diagonal sum rule `NW + SE = NE + SW`. -/
def DiagonalSum (M : ColorMatrix) : Prop :=
  M.NW + M.SE = M.NE + M.SW

/-- Counterclockwise 90° rotation of the matrix, matching `T.rotate`. -/
def rotate (M : ColorMatrix) : ColorMatrix where
  NW := M.NE
  NE := M.SE
  SE := M.SW
  SW := M.NW

/-- Left-right swap of the matrix, matching the vertical reflect `(-T).vflip`. -/
def hswap (M : ColorMatrix) : ColorMatrix where
  NW := M.NE
  NE := M.NW
  SW := M.SE
  SE := M.SW

@[simp] theorem rotate_NW (M : ColorMatrix) : M.rotate.NW = M.NE := rfl
@[simp] theorem rotate_NE (M : ColorMatrix) : M.rotate.NE = M.SE := rfl
@[simp] theorem rotate_SW (M : ColorMatrix) : M.rotate.SW = M.NW := rfl
@[simp] theorem rotate_SE (M : ColorMatrix) : M.rotate.SE = M.SW := rfl
@[simp] theorem hswap_NW (M : ColorMatrix) : M.hswap.NW = M.NE := rfl
@[simp] theorem hswap_NE (M : ColorMatrix) : M.hswap.NE = M.NW := rfl
@[simp] theorem hswap_SW (M : ColorMatrix) : M.hswap.SW = M.SE := rfl
@[simp] theorem hswap_SE (M : ColorMatrix) : M.hswap.SE = M.SW := rfl

theorem of_rotate (T : TangleDiagram) (col : Nat → Int) :
    of T.rotate col = (of T col).rotate :=
  rfl

theorem DiagonalSum.rotate {M : ColorMatrix} (h : M.DiagonalSum) :
    M.rotate.DiagonalSum := by
  simp [DiagonalSum] at h ⊢
  omega

theorem DiagonalSum.hswap {M : ColorMatrix} (h : M.DiagonalSum) :
    M.hswap.DiagonalSum := by
  simp [DiagonalSum] at h ⊢
  omega

/-- Glue-compatible additivity of the coloring fraction
    (Kauffman–Lambropoulou Theorem 4.3). -/
theorem fraction_add_glue (a b c d e f : Int)
    (hdiag : b - d = e - f) :
    (mk a b c d).fraction.add (mk b e d f).fraction = (mk a e c f).fraction := by
  unfold fraction
  dsimp
  by_cases hden : e - f = 0
  · have hb : b - d = 0 := by omega
    simp [hb, hden, CFValue.add]
  · have hb : b - d ≠ 0 := by intro h; apply hden; omega
    simp [hb, hden, CFValue.add]
    -- both sides ofRat
    have : b - d = e - f := hdiag
    simp [this]
    simp [Rat.divInt_eq_div]
    have hz : (e : Rat) - f ≠ 0 := by exact_mod_cast hden
    field_simp
    ring

end ColorMatrix

/-! ## Integral colorability -/

/-- Every diagram admits the constant integral coloring. -/
theorem integrally_colorable (T : TangleDiagram) :
    ∃ col : Nat → Int, T.IsColored col :=
  ⟨fun _ => 0, isColored_const T 0⟩

/-- Every rational tangle is integrally colorable. -/
theorem rational_integrally_colorable (T : TangleDiagram) (_h : IsRational T) :
    ∃ col : Nat → Int, T.IsColored col :=
  integrally_colorable T

/-! ## Colorings of the elementary tangles -/

def colorZero (a c : Int) : Nat → Int :=
  fun x => if x = 0 then a else c

theorem zero_isColored (a c : Int) :
    TangleDiagram.zero.IsColored (colorZero a c) := by
  intro C hC
  cases hC

theorem zero_matrix (a c : Int) :
    ColorMatrix.of TangleDiagram.zero (colorZero a c) =
      { NW := a, NE := a, SW := c, SE := c } := by
  simp [ColorMatrix.of, TangleDiagram.zero, colorZero]

theorem zero_diagonal (a c : Int) :
    (ColorMatrix.of TangleDiagram.zero (colorZero a c)).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, zero_matrix]

theorem zero_fraction {a c : Int} (h : a ≠ c) :
    (ColorMatrix.of TangleDiagram.zero (colorZero a c)).fraction = (0 : CFValue) := by
  simp [ColorMatrix.fraction, zero_matrix, sub_ne_zero.mpr h]
  rfl

def colorInfinity (a b : Int) : Nat → Int :=
  fun x => if x = 0 then a else b

theorem infinity_isColored (a b : Int) :
    TangleDiagram.infinity.IsColored (colorInfinity a b) := by
  intro C hC
  cases hC

theorem infinity_matrix (a b : Int) :
    ColorMatrix.of TangleDiagram.infinity (colorInfinity a b) =
      { NW := a, NE := b, SW := a, SE := b } := by
  simp [ColorMatrix.of, TangleDiagram.infinity, colorInfinity]

theorem infinity_diagonal (a b : Int) :
    (ColorMatrix.of TangleDiagram.infinity (colorInfinity a b)).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, infinity_matrix]
  ring

theorem infinity_fraction {a b : Int} (_h : a ≠ b) :
    (ColorMatrix.of TangleDiagram.infinity (colorInfinity a b)).fraction = .inf := by
  simp [ColorMatrix.fraction, infinity_matrix]

/-- Color `[+1]` with overstrand color `β` and NE color `α`. -/
def colorOne (β α : Int) : Nat → Int :=
  fun x => if x = 0 ∨ x = 2 then β else if x = 1 then α else 2 * β - α

theorem colorOne_0 (β α : Int) : colorOne β α 0 = β := by simp [colorOne]
theorem colorOne_1 (β α : Int) : colorOne β α 1 = α := by simp [colorOne]
theorem colorOne_2 (β α : Int) : colorOne β α 2 = β := by simp [colorOne]
theorem colorOne_3 (β α : Int) : colorOne β α 3 = 2 * β - α := by simp [colorOne]

theorem one_isColored (β α : Int) :
    one.IsColored (colorOne β α) := by
  intro C hC
  simp [one] at hC
  rcases hC with rfl
  simp [ColoringRule, colorOne_0, colorOne_1, colorOne_2, colorOne_3]
  try ring

theorem one_matrix (β α : Int) :
    ColorMatrix.of one (colorOne β α) =
      { NW := β, NE := α, SW := 2 * β - α, SE := β } := by
  simp [ColorMatrix.of, one, colorOne_0, colorOne_1, colorOne_2, colorOne_3]

theorem one_diagonal (β α : Int) :
    (ColorMatrix.of one (colorOne β α)).DiagonalSum := by
  simp [ColorMatrix.DiagonalSum, one_matrix]
  ring

theorem one_fraction {β α : Int} (h : α ≠ β) :
    (ColorMatrix.of one (colorOne β α)).fraction = (1 : CFValue) := by
  simp [ColorMatrix.fraction, one_matrix, sub_ne_zero.mpr h, Rat.divInt_eq_div]
  have : (α : Rat) - β ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr h)
  field_simp
  rfl

/-- Color `[-1]` so the overstrand (NE–SW after the switch) has color `β`. -/
def colorNegOne (β α : Int) : Nat → Int :=
  fun x => if x = 1 ∨ x = 3 then β else if x = 0 then α else 2 * β - α

theorem colorNegOne_0 (β α : Int) : colorNegOne β α 0 = α := by simp [colorNegOne]
theorem colorNegOne_1 (β α : Int) : colorNegOne β α 1 = β := by simp [colorNegOne]
theorem colorNegOne_2 (β α : Int) : colorNegOne β α 2 = 2 * β - α := by simp [colorNegOne]
theorem colorNegOne_3 (β α : Int) : colorNegOne β α 3 = β := by simp [colorNegOne]

theorem negOne_isColored (β α : Int) :
    negOne.IsColored (colorNegOne β α) := by
  intro C hC
  simp [negOne, one, TangleDiagram.mirror, Crossing.switch] at hC
  rcases hC with rfl
  simp [ColoringRule, colorNegOne_0, colorNegOne_1, colorNegOne_2, colorNegOne_3]
  try ring

theorem negOne_matrix (β α : Int) :
    ColorMatrix.of negOne (colorNegOne β α) =
      { NW := α, NE := β, SW := β, SE := 2 * β - α } := by
  simp [ColorMatrix.of, negOne, one, TangleDiagram.mirror, Crossing.switch,
    colorNegOne_0, colorNegOne_1, colorNegOne_2, colorNegOne_3]

theorem negOne_fraction {β α : Int} (h : α ≠ β) :
    (ColorMatrix.of negOne (colorNegOne β α)).fraction = CFValue.ofInt (-1) := by
  rw [negOne_matrix]
  unfold ColorMatrix.fraction
  have hne : α - β ≠ 0 := sub_ne_zero.mpr h
  have hden : β - (2 * β - α) = α - β := by ring
  simp [hden, hne, Rat.divInt_eq_div, CFValue.ofInt]
  have hz : (α : Rat) - β ≠ 0 := by exact_mod_cast hne
  field_simp
  ring

/-! ## Mirror of elementary diagrams

`SameEndpointColors` after `T.mirror` is false for a non-monochrome `[+1]`:
the four endpoints are the four arcs, and `ColoringRule` on the switched
crossing with those colors forces the two under-colors to agree. The working
transport is `colorMirrorUnit`, whose color matrix is `hswap` of the original
(so `f(-T)=-f(T)` under `DiagonalSum`). -/

theorem coloring_mirror_one_sameEndpoint_mono (col col' : Nat → Int)
    (hc : one.IsColored col) (hc' : one.mirror.IsColored col')
    (hs : SameEndpointColors one one.mirror col col') :
    col 0 = col 1 := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := hs
  have hmem :
      { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
        one.mirror.crossings := by
    simp [one, TangleDiagram.mirror, Crossing.switch, CrossingSign.flip]
  obtain ⟨hβ, _hr⟩ := hc' _ hmem
  have hC := hc ⟨0, 1, 2, 3, CrossingSign.pos⟩ (by simp [one])
  simp [SameEndpointColors, one, TangleDiagram.mirror] at hNW hNE hSE hSW
  have h13 : col 1 = col 3 := by
    simp [Crossing.switch] at hβ
    linarith
  linarith [hC.2]

theorem coloring_mirror_one (col : Nat → Int) (hc : one.IsColored col) :
    one.mirror.IsColored (colorMirrorUnit col) ∧
      ColorMatrix.of one.mirror (colorMirrorUnit col) =
        (ColorMatrix.of one col).hswap := by
  constructor
  · intro C hC
    simp [one, TangleDiagram.mirror, Crossing.switch] at hC
    subst hC
    obtain ⟨hβ, hr⟩ := hc ⟨0, 1, 2, 3, CrossingSign.pos⟩ (by simp [one])
    constructor
    · simp [Crossing.switch, colorMirrorUnit, hβ]
    · simp [Crossing.switch, colorMirrorUnit]; linarith
  · simp [ColorMatrix.of, ColorMatrix.hswap, one, TangleDiagram.mirror,
      colorMirrorUnit]

theorem coloring_mirror_negOne (col : Nat → Int) (hc : negOne.IsColored col) :
    negOne.mirror.IsColored (colorMirrorUnit col) ∧
      ColorMatrix.of negOne.mirror (colorMirrorUnit col) =
        (ColorMatrix.of negOne col).hswap := by
  have hmem :
      { a0 := 1, a1 := 2, a2 := 3, a3 := 0, sign := CrossingSign.neg } ∈
        negOne.crossings := by
    simp [negOne, one, TangleDiagram.mirror, Crossing.switch, CrossingSign.flip]
  obtain ⟨hβ, hr⟩ := hc _ hmem
  constructor
  · intro C hC
    simp [negOne, one, TangleDiagram.mirror, List.map_map, Function.comp,
      Crossing.switch, Crossing.switch_switch] at hC
    subst hC
    constructor
    · simp [colorMirrorUnit] at hβ ⊢
      linarith
    · simp [colorMirrorUnit] at hr ⊢
      linarith
  · simp [ColorMatrix.of, ColorMatrix.hswap, negOne, one, TangleDiagram.mirror,
      colorMirrorUnit]

theorem coloring_mirror_zero (col : Nat → Int) :
    TangleDiagram.zero.mirror.IsColored col ∧
      ColorMatrix.of TangleDiagram.zero.mirror col =
        (ColorMatrix.of TangleDiagram.zero col).hswap := by
  constructor
  · intro C hC; cases hC
  · simp [ColorMatrix.of, ColorMatrix.hswap, TangleDiagram.zero, TangleDiagram.mirror]

theorem coloring_mirror_infinity (col : Nat → Int) :
    TangleDiagram.infinity.mirror.IsColored (colorMirrorUnit col) ∧
      ColorMatrix.of TangleDiagram.infinity.mirror (colorMirrorUnit col) =
        (ColorMatrix.of TangleDiagram.infinity col).hswap := by
  constructor
  · intro C hC; cases hC
  · simp [ColorMatrix.of, ColorMatrix.hswap, TangleDiagram.infinity,
      TangleDiagram.mirror, colorMirrorUnit]

theorem coloring_mirror_crossingTangle (s : CrossingSign) (col : Nat → Int)
    (hc : (crossingTangle s).IsColored col) :
    (crossingTangle s).mirror.IsColored (colorMirrorUnit col) ∧
      ColorMatrix.of (crossingTangle s).mirror (colorMirrorUnit col) =
        (ColorMatrix.of (crossingTangle s) col).hswap := by
  cases s with
  | pos => simpa [crossingTangle] using coloring_mirror_one col hc
  | neg => simpa [crossingTangle] using coloring_mirror_negOne col hc

/-! ## Vertical reflect -/

theorem coloring_rotate (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) : T.rotate.IsColored col :=
  h

theorem vertical_reflect_isColored (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) : ((-T).vflip).IsColored col := by
  intro C hC
  change C ∈ (T.mirror.vflip).crossings at hC
  have hC' : C ∈ T.mirror.mirror.crossings := by
    simpa [TangleDiagram.vflip] using hC
  have hmap : T.mirror.mirror.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch]
  rw [hmap, List.mem_map] at hC'
  obtain ⟨C0, hC0, rfl⟩ := hC'
  exact ColoringRule_rotate180 C0 col (h C0 hC0)

theorem vertical_reflect_matrix (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of (-T).vflip col = (ColorMatrix.of T col).hswap := by
  simp [ColorMatrix.of, ColorMatrix.hswap, Neg.neg, TangleDiagram.vflip,
    TangleDiagram.mirror]

theorem SameEndpointColors.vertical_reflect {T T' : TangleDiagram}
    {col col' : Nat → Int} (h : SameEndpointColors T T' col col') :
    SameEndpointColors (-T).vflip (-T').vflip col col' := by
  obtain ⟨hNW, hNE, hSE, hSW⟩ := h
  simp [SameEndpointColors, Neg.neg, TangleDiagram.vflip, TangleDiagram.mirror]
  exact ⟨hNE, hNW, hSW, hSE⟩

/-! ## Uniqueness of `f` for a fixed elementary diagram -/

/-- Any non-monochrome coloring of `[0]` has coloring fraction `0`. -/
theorem zero_fraction_of_colored {col : Nat → Int} (h : col 0 ≠ col 1) :
    (ColorMatrix.of TangleDiagram.zero col).fraction = (0 : CFValue) := by
  simp [ColorMatrix.of, TangleDiagram.zero, ColorMatrix.fraction, sub_ne_zero.mpr h]
  rfl

/-- Any coloring of `[∞]` has coloring fraction `∞`. -/
theorem infinity_fraction_of_colored (col : Nat → Int) :
    (ColorMatrix.of TangleDiagram.infinity col).fraction = .inf := by
  simp [ColorMatrix.of, TangleDiagram.infinity, ColorMatrix.fraction]

/-- Any non-monochrome coloring of `[+1]` has coloring fraction `1`. -/
theorem one_fraction_of_colored {col : Nat → Int} (hc : one.IsColored col)
    (h : col 1 ≠ col 0) :
    (ColorMatrix.of one col).fraction = (1 : CFValue) := by
  have hC := hc ⟨0, 1, 2, 3, .pos⟩ (by simp [one])
  have hβ : col 0 = col 2 := hC.1
  have hmat : ColorMatrix.of one col = ColorMatrix.of one (colorOne (col 0) (col 1)) := by
    have h3 : col 3 = 2 * col 0 - col 1 := by linarith [hC.2]
    simp [ColorMatrix.of, one, colorOne_0, colorOne_1, colorOne_2, colorOne_3, hβ, h3]
  rw [hmat]
  exact one_fraction h

end RationalTangles
