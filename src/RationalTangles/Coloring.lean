/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Init.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import RationalTangles.Tangle
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

end RationalTangles
