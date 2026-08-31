/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import RationalTangles.Coloring
import RationalTangles.Flype

/-!
# Coloring invariance under Reidemeister moves and flypes

The paper's "easy to verify" checks: `τ` is an involution (R2), is
self-distributive (R3), and fixes the diagonal (R1 kink). Combined with
transport of colorings along planar isotopy, this yields invariance of
external strand colors.
-/

namespace RationalTangles

theorem pairRel_coloring {R : Crossing → Crossing → Prop}
    (hR : ∀ C₁ C₂, R C₁ C₂ → ∀ col, ColoringRule C₁ col → ColoringRule C₂ col)
    {Cs Ds : List Crossing} (h : pairRel R Cs Ds) (col : Nat → Int)
    (hCs : ∀ C ∈ Cs, ColoringRule C col) :
    ∀ X ∈ Ds, ColoringRule X col := by
  induction Cs generalizing Ds with
  | nil =>
    cases Ds with
    | nil => intro X hX; cases hX
    | cons _ _ => cases h
  | cons C Cs ih =>
    cases Ds with
    | nil => cases h
    | cons Y Ds =>
      obtain ⟨hCY, hrest⟩ := h
      intro X hX
      rw [List.mem_cons] at hX
      cases hX with
      | inl hEq =>
        rw [hEq]
        exact hR C Y hCY col (hCs C (by simp))
      | inr hX =>
        exact ih hrest (fun Z hZ => hCs Z (by simp [hZ])) X hX

theorem coloring_planar_isotopy (D E : TangleDiagram) (col : Nat → Int)
    (h : PlanarIsotopy D E) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨f, hf, hNW, hNE, hSE, hSW, Cs, hpair, hperm⟩ := h
  let col' : Nat → Int := fun b => col (Function.invFun f b)
  have hrename : (D.rename f).IsColored col' :=
    IsColored_rename_injective D f hf col hc
  have hCs : ∀ C ∈ Cs, ColoringRule C col' :=
    pairRel_coloring (fun C₁ C₂ hCD col₀ hC0 =>
      ColoringRule_sameUpToRotation col₀ hCD hC0) hpair col'
      (fun C hC => hrename C (by simpa [TangleDiagram.rename] using hC))
  refine ⟨col', ?_, ?_⟩
  · intro C hC
    exact hCs C ((List.Perm.mem_iff hperm).2 hC)
  · have hpt : ∀ a, col' (f a) = col a := by
      intro a
      dsimp [col']
      rw [Function.leftInverse_invFun hf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hNW]; exact hpt D.NW
    · rw [hNE]; exact hpt D.NE
    · rw [hSE]; exact hpt D.SE
    · rw [hSW]; exact hpt D.SW

/-- Reidemeister I locally: a kink is monochrome, `τ_α(α) = α`. -/
theorem coloring_reidemeister_I (α : Int) : tau α α = α :=
  tau_fixed α

/-- Reidemeister II locally: `τ` is an involution. -/
theorem coloring_reidemeister_II (β α : Int) : tau β (tau β α) = α :=
  tau_involutive β α

/-- Reidemeister III locally: `τ` is self-distributive. -/
theorem coloring_reidemeister_III (β γ α : Int) :
    tau (tau β γ) (tau β α) = tau β (tau γ α) :=
  tau_self_distrib β γ α

/-- Flype locally: the vertical reflect (the spatial flip used in a flype)
    inherits a coloring with left-right swapped color matrix. -/
theorem coloring_flype (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) :
    ((-T).vflip).IsColored col ∧
      ColorMatrix.of (-T).vflip col = (ColorMatrix.of T col).hswap :=
  ⟨vertical_reflect_isColored T col h, vertical_reflect_matrix T col⟩

end RationalTangles
