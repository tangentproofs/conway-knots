/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColoringFractionEq

/-!
# Uniqueness of the coloring fraction on a slideReady diagram

Any two non-monochrome integral colorings of a `slideReady` twist-form
diagram have the same coloring fraction `f`, because each equals
`e.toStandard.fraction` (`coloring_fraction_eq_F`). Affine identities for
`colorFrom` are recorded here but uniqueness does not need them.
This is not Theorem 2: it is uniqueness on a fixed PD-code, not along
arbitrary `Isotopic` generators.

The algebraic mirror of `negOne` is `one`, while PD-mirror is `Crossing.switch`
(double switch is `rotate180`), so `maxArc_mirror` does not identify
`e.mirror.diagram.maxArc` with `e.diagram.maxArc`. Same `appears` implies
same `maxArc`; on `unit.add S` the appearing arcs are determined by
`S.appears` and the glue ports. That gives `TwistExpr.mirror_maxArc`, port
lemmas, `slideReady_mirror`, and a `ColoringIsotopy` between `e.diagram.mirror`
and `e.mirror.diagram` for `slideReady` expressions (extending
`coloring_mirror_diagram_rightBottom`). Invert uniqueness on this class
reuses `colorFrom_isColored_slideReady`.
-/

namespace RationalTangles


theorem colorZero_affine (a c n k : Int) :
    colorZero (n * a + k) (n * c + k) = fun x => n * colorZero a c x + k := by
  funext x
  simp [colorZero]
  split_ifs <;> rfl

theorem colorInfinity_affine (a b n k : Int) :
    colorInfinity (n * a + k) (n * b + k) = fun x => n * colorInfinity a b x + k := by
  funext x
  simp [colorInfinity]
  split_ifs <;> rfl

theorem colorOne_affine (beta alpha n k : Int) :
    colorOne (n * beta + k) (n * alpha + k) = fun x => n * colorOne beta alpha x + k := by
  funext x
  simp [colorOne]
  split_ifs <;> ring

theorem colorNegOne_affine (beta alpha n k : Int) :
    colorNegOne (n * beta + k) (n * alpha + k) =
      fun x => n * colorNegOne beta alpha x + k := by
  funext x
  simp [colorNegOne]
  split_ifs <;> ring

theorem colorAddOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorAddOne T (fun a => n * col a + k) = fun a => n * colorAddOne T col a + k := by
  funext a
  simp [colorAddOne]
  split_ifs <;> ring

theorem colorAddNegOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorAddNegOne T (fun a => n * col a + k) =
      fun a => n * colorAddNegOne T col a + k := by
  funext a
  simp [colorAddNegOne]
  split_ifs <;> ring

theorem colorMulOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorMulOne T (fun a => n * col a + k) = fun a => n * colorMulOne T col a + k := by
  funext a
  simp [colorMulOne]
  split_ifs <;> ring

theorem colorMulNegOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorMulNegOne T (fun a => n * col a + k) =
      fun a => n * colorMulNegOne T col a + k := by
  funext a
  simp [colorMulNegOne]
  split_ifs <;> ring

theorem colorGlueAdd_affine (T S : TangleDiagram) (colT colS : Nat → Int) (n k : Int) :
    colorGlueAdd T S (fun a => n * colT a + k) (fun a => n * colS a + k) =
      fun a => n * colorGlueAdd T S colT colS a + k := by
  funext a
  by_cases h : T.maxArc < a
  · simp [colorGlueAdd, h]
  · simp [colorGlueAdd, h]

theorem colorGlueMul_affine (T S : TangleDiagram) (colT colS : Nat → Int) (n k : Int) :
    colorGlueMul T S (fun a => n * colT a + k) (fun a => n * colS a + k) =
      fun a => n * colorGlueMul T S colT colS a + k := by
  funext a
  by_cases h : T.maxArc < a
  · simp [colorGlueMul, h]
  · simp [colorGlueMul, h]

theorem colorAddLeftOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorAddLeftOne S (fun a => n * colS a + k) =
      fun a => n * colorAddLeftOne S colS a + k := by
  have hU := colorOne_affine (colS S.SW) (colS S.NW) n k
  have hG := colorGlueAdd_affine one S (colorOne (colS S.SW) (colS S.NW)) colS n k
  simp [colorAddLeftOne]
  rw [hU, hG]

theorem colorAddLeftNegOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorAddLeftNegOne S (fun a => n * colS a + k) =
      fun a => n * colorAddLeftNegOne S colS a + k := by
  have hbeta : n * (2 * colS S.NW - colS S.SW) + k =
      2 * (n * colS S.NW + k) - (n * colS S.SW + k) := by ring
  have hU := colorNegOne_affine (colS S.NW) (2 * colS S.NW - colS S.SW) n k
  have hG := colorGlueAdd_affine negOne S
    (colorNegOne (colS S.NW) (2 * colS S.NW - colS S.SW)) colS n k
  simp [colorAddLeftNegOne]
  rw [← hbeta, hU]
  exact hG

theorem colorMulTopOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorMulTopOne S (fun a => n * colS a + k) =
      fun a => n * colorMulTopOne S colS a + k := by
  have halpha : n * (2 * colS S.NE - colS S.NW) + k =
      2 * (n * colS S.NE + k) - (n * colS S.NW + k) := by ring
  have hU := colorOne_affine (colS S.NE) (2 * colS S.NE - colS S.NW) n k
  have hG := colorGlueMul_affine one S
    (colorOne (colS S.NE) (2 * colS S.NE - colS S.NW)) colS n k
  simp [colorMulTopOne]
  rw [← halpha, hU]
  exact hG

theorem colorMulTopNegOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorMulTopNegOne S (fun a => n * colS a + k) =
      fun a => n * colorMulTopNegOne S colS a + k := by
  have halpha : n * (2 * colS S.NW - colS S.NE) + k =
      2 * (n * colS S.NW + k) - (n * colS S.NE + k) := by ring
  have hU := colorNegOne_affine (colS S.NW) (2 * colS S.NW - colS S.NE) n k
  have hG := colorGlueMul_affine negOne S
    (colorNegOne (colS S.NW) (2 * colS S.NW - colS S.NE)) colS n k
  simp [colorMulTopNegOne]
  rw [← halpha, hU]
  exact hG

theorem TwistExpr.colorFrom_affine (e : TwistExpr) (a c n k : Int) :
    e.colorFrom (n * a + k) (n * c + k) = fun x => n * e.colorFrom a c x + k := by
  induction e generalizing a c with
  | zero => exact colorZero_affine a c n k
  | infinity => exact colorInfinity_affine a c n k
  | one => exact colorOne_affine a c n k
  | negOne => exact colorNegOne_affine a c n k
  | addRight e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorAddOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorAddNegOne_affine]
  | mulBottom e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorMulOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorMulNegOne_affine]
  | addLeft e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorAddLeftOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorAddLeftNegOne_affine]
  | mulTop e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorMulTopOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorMulTopNegOne_affine]

theorem TwistExpr.colorFrom_eq_affine_01 (e : TwistExpr) (a c : Int) :
    e.colorFrom a c = fun x => (c - a) * e.colorFrom 0 1 x + a := by
  have h := e.colorFrom_affine 0 1 (c - a) a
  have ha : (c - a) * 0 + a = a := by ring
  have hc : (c - a) * 1 + a = c := by ring
  simpa [ha, hc] using h

theorem ColorMatrix.NotMono_of_eq_affine {M N : ColorMatrix} {p q : Int}
    (h : N = M.affine p q) (hN : N.NotMono) : p ≠ 0 := by
  intro hp
  subst h
  simp [ColorMatrix.affine, ColorMatrix.NotMono, hp] at hN

/-- Uniqueness of `f` on a `slideReady` diagram: every non-monochrome coloring
    has `f = e.toStandard.fraction`, so any two agree. `DiagonalSum` is
    discharged by `twist_coloring_diagonal_slideReady`. -/
theorem coloring_fraction_unique_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col col' : Nat → Int)
    (hc : e.diagram.IsColored col) (hc' : e.diagram.IsColored col')
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hm' : (ColorMatrix.of e.diagram col').NotMono) :
    (ColorMatrix.of e.diagram col).fraction =
      (ColorMatrix.of e.diagram col').fraction :=
  (coloring_fraction_eq_F e hok col hc
      (twist_coloring_diagonal_slideReady e hok col hc) hm).trans
    (coloring_fraction_eq_F e hok col' hc'
      (twist_coloring_diagonal_slideReady e hok col' hc') hm').symm


theorem ColorMatrix.of_colorFrom_affine_01 (e : TwistExpr) (a c : Int) :
    ColorMatrix.of e.diagram (e.colorFrom a c) =
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).affine (c - a) a := by
  have hfun := e.colorFrom_eq_affine_01 a c
  calc
    ColorMatrix.of e.diagram (e.colorFrom a c)
        = ColorMatrix.of e.diagram (fun x => (c - a) * e.colorFrom 0 1 x + a) := by
          simp [hfun]
    _ = (ColorMatrix.of e.diagram (e.colorFrom 0 1)).affine (c - a) a :=
          ColorMatrix.of_affineMap _ _ _ _


/-! ## Appearing arcs and algebraic-mirror PD-codes -/

theorem Crossing.memArc_rename (f : Nat → Nat) (C : Crossing) {b : Nat} :
    (C.rename f).memArc b ↔ ∃ a, C.memArc a ∧ f a = b := by
  simp only [Crossing.rename, Crossing.memArc]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨C.a0, Or.inl rfl, rfl⟩
    · exact ⟨C.a1, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨C.a2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨C.a3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨a, ha, hfa⟩
    rcases ha with h0 | h1 | h2 | h3
    · exact Or.inl (h0 ▸ hfa).symm
    · exact Or.inr (Or.inl (h1 ▸ hfa).symm)
    · exact Or.inr (Or.inr (Or.inl (h2 ▸ hfa).symm))
    · exact Or.inr (Or.inr (Or.inr (h3 ▸ hfa).symm))

theorem foldl_maxArc_eq_start_or_mem (cs : List Crossing) (b : Nat) :
    cs.foldl (fun m C => max m C.maxArc) b = b ∨
      ∃ C ∈ cs, cs.foldl (fun m C => max m C.maxArc) b = C.maxArc := by
  induction cs generalizing b with
  | nil => exact Or.inl rfl
  | cons C cs ih =>
    simp only [List.foldl]
    rcases ih (max b C.maxArc) with h | ⟨C', hC', hmax⟩
    · rw [h]
      by_cases hb : C.maxArc ≤ b
      · exact Or.inl (Nat.max_eq_left hb)
      · exact Or.inr ⟨C, List.mem_cons_self, Nat.max_eq_right (Nat.le_of_not_ge hb)⟩
    · exact Or.inr ⟨C', List.mem_cons_of_mem _ hC', hmax⟩

theorem foldl_maxArc_le (cs : List Crossing) (b M : Nat)
    (hb : b ≤ M) (hC : ∀ C ∈ cs, C.maxArc ≤ M) :
    cs.foldl (fun m C => max m C.maxArc) b ≤ M := by
  induction cs generalizing b with
  | nil => simpa
  | cons C cs ih =>
    simp [List.foldl]
    apply ih
    · exact Nat.max_le.mpr ⟨hb, hC C List.mem_cons_self⟩
    · intro C' hC'
      exact hC C' (List.mem_cons_of_mem _ hC')

theorem max4_eq_or (w x y z : Nat) :
    max w (max x (max y z)) = w ∨ max w (max x (max y z)) = x ∨
      max w (max x (max y z)) = y ∨ max w (max x (max y z)) = z := by
  omega

theorem TangleDiagram.maxArc_appears (T : TangleDiagram) : T.appears T.maxArc := by
  unfold TangleDiagram.maxArc TangleDiagram.appears
  set b := max T.NW (max T.NE (max T.SE T.SW))
  have hb : b = T.NW ∨ b = T.NE ∨ b = T.SE ∨ b = T.SW :=
    max4_eq_or T.NW T.NE T.SE T.SW
  rcases foldl_maxArc_eq_start_or_mem T.crossings b with h | ⟨C, hC, hmax⟩
  · rcases hb with hNW | hNE | hSE | hSW
    · left; exact h.trans hNW
    · right; left; exact h.trans hNE
    · right; right; left; exact h.trans hSE
    · right; right; right; left; exact h.trans hSW
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmax ▸ Crossing.maxArc_memArc C⟩)))

theorem TangleDiagram.appears_le_maxArc (T : TangleDiagram) {a : Nat}
    (h : T.appears a) : a ≤ T.maxArc := by
  rcases h with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
  · exact maxArc_ge_NW T
  · exact maxArc_ge_NE T
  · exact maxArc_ge_SE T
  · exact maxArc_ge_SW T
  · have hm := maxArc_ge_of_mem T hC
    have ha : a ≤ C.maxArc := by
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Crossing.a0_le_maxArc C
      · exact Crossing.a1_le_maxArc C
      · exact Crossing.a2_le_maxArc C
      · exact Crossing.a3_le_maxArc C
    exact le_trans ha hm

theorem TangleDiagram.maxArc_eq_of_appears {T S : TangleDiagram}
    (h : ∀ a, T.appears a ↔ S.appears a) : T.maxArc = S.maxArc := by
  apply Nat.le_antisymm
  · exact S.appears_le_maxArc ((h T.maxArc).mp T.maxArc_appears)
  · exact T.appears_le_maxArc ((h S.maxArc).mpr S.maxArc_appears)

theorem Crossing.rename_maxArc_le (f : Nat → Nat) (C : Crossing) (M : Nat)
    (h : ∀ a, C.memArc a → f a ≤ M) : (C.rename f).maxArc ≤ M := by
  have h0 : f C.a0 ≤ M := h C.a0 (Or.inl rfl)
  have h1 : f C.a1 ≤ M := h C.a1 (Or.inr (Or.inl rfl))
  have h2 : f C.a2 ≤ M := h C.a2 (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : f C.a3 ≤ M := h C.a3 (Or.inr (Or.inr (Or.inr rfl)))
  simp [Crossing.rename, Crossing.maxArc]
  omega

theorem one_appears (a : Nat) : one.appears a ↔ a ≤ 3 := by
  constructor
  · intro h
    simp [TangleDiagram.appears, one, Crossing.memArc] at h
    omega
  · intro h
    simp [TangleDiagram.appears, one, Crossing.memArc]
    omega

theorem negOne_appears (a : Nat) : negOne.appears a ↔ a ≤ 3 := by
  simp [negOne, TangleDiagram.appears, TangleDiagram.mirror, one,
    Crossing.switch, Crossing.memArc]
  omega

theorem crossingTangle_appears (s : CrossingSign) (a : Nat) :
    (crossingTangle s).appears a ↔ a ≤ 3 := by
  cases s with
  | pos => simpa [crossingTangle] using one_appears a
  | neg =>
    constructor
    · intro h
      simp [crossingTangle, negOne, TangleDiagram.appears, TangleDiagram.mirror,
        Crossing.switch, one, Crossing.memArc] at h
      omega
    · intro h
      simp [crossingTangle, negOne, TangleDiagram.appears, TangleDiagram.mirror,
        Crossing.switch, one, Crossing.memArc]
      omega

theorem crossingTangle_memArc_le (s : CrossingSign) {C : Crossing}
    (hC : C ∈ (crossingTangle s).crossings) {a : Nat} (ha : C.memArc a) :
    a ≤ 3 :=
  (crossingTangle_appears s a).1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, ha⟩))))

theorem crossingTangle_exists_memArc (s : CrossingSign) {a : Nat} (ha : a ≤ 3) :
    ∃ C ∈ (crossingTangle s).crossings, C.memArc a := by
  cases s with
  | pos =>
    refine ⟨⟨0, 1, 2, 3, .pos⟩, ?_, ?_⟩
    · simp [crossingTangle, one]
    · simp [Crossing.memArc]; omega
  | neg =>
    refine ⟨Crossing.switch ⟨0, 1, 2, 3, .pos⟩, ?_, ?_⟩
    · simp [crossingTangle, negOne, one, TangleDiagram.mirror]
    · simp [Crossing.switch, Crossing.memArc]; omega

theorem addGlue_shift_unit_le (T : TangleDiagram) (s : CrossingSign) {a : Nat}
    (ha : a ≤ 3) :
    addGlue T (crossingTangle s) (a + (T.maxArc + 1)) ≤ T.maxArc + 3 := by
  rw [addGlue_shift_eq]
  simp [crossingTangle_NW, crossingTangle_SW]
  split_ifs
  · exact le_trans (maxArc_ge_NE T) (by omega)
  · exact le_trans (maxArc_ge_SE T) (by omega)
  · omega

theorem add_crossingTangle_NE (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).NE = T.maxArc + 2 := by
  cases s <;> (simp [add_NE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem add_crossingTangle_SE (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).SE = T.maxArc + 3 := by
  cases s <;> (simp [add_SE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem add_crossingTangle_maxArc (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).maxArc = T.maxArc + 3 := by
  let U := crossingTangle s
  have hNE := add_crossingTangle_NE T s
  have hSE := add_crossingTangle_SE T s
  apply Nat.le_antisymm
  · unfold TangleDiagram.maxArc
    rw [add_crossings_append]
    refine foldl_maxArc_le _ _ (T.maxArc + 3) ?_ ?_
    · change max T.NW (max (T.add (crossingTangle s)).NE
          (max (T.add (crossingTangle s)).SE T.SW)) ≤ T.maxArc + 3
      rw [hNE, hSE]
      have := maxArc_ge_NW T
      have := maxArc_ge_SW T
      omega
    · intro C hC
      rw [List.mem_append] at hC
      rcases hC with hC | hC
      · exact le_trans (maxArc_ge_of_mem T hC) (by omega)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        refine Crossing.rename_maxArc_le _ _ _ ?_
        intro a ha
        simpa [Function.comp, addShift] using
          addGlue_shift_unit_le T s (crossingTangle_memArc_le s hC0 ha)
  · rw [← hSE]
    exact maxArc_ge_SE _

theorem mulGlue_shift_unit_le (T : TangleDiagram) (s : CrossingSign) {a : Nat}
    (ha : a ≤ 3) :
    mulGlue T (crossingTangle s) (a + (T.maxArc + 1)) ≤ T.maxArc + 4 := by
  rw [mulGlue_shift_eq]
  simp [crossingTangle_NW, crossingTangle_NE]
  split_ifs
  · exact le_trans (maxArc_ge_SW T) (by omega)
  · exact le_trans (maxArc_ge_SE T) (by omega)
  · omega

theorem mul_SE_rename (T S : TangleDiagram) :
    (T.mul S).SE =
      if S.SE = S.NW then T.SW
      else if S.SE = S.NE then T.SE
      else S.SE + (T.maxArc + 1) := by
  simp [TangleDiagram.mul, TangleDiagram.rename]

theorem mul_SW_rename (T S : TangleDiagram) :
    (T.mul S).SW =
      if S.SW = S.NW then T.SW
      else if S.SW = S.NE then T.SE
      else S.SW + (T.maxArc + 1) := by
  simp [TangleDiagram.mul, TangleDiagram.rename]

theorem mul_crossingTangle_SE (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).SE = T.maxArc + 3 := by
  cases s <;> (simp [mul_SE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem mul_crossingTangle_SW (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).SW = T.maxArc + 4 := by
  cases s <;> (simp [mul_SW_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem mul_crossingTangle_maxArc (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).maxArc = T.maxArc + 4 := by
  have hSE := mul_crossingTangle_SE T s
  have hSW := mul_crossingTangle_SW T s
  apply Nat.le_antisymm
  · unfold TangleDiagram.maxArc
    rw [mul_crossings_append]
    refine foldl_maxArc_le _ _ (T.maxArc + 4) ?_ ?_
    · change max T.NW (max T.NE (max (T.mul (crossingTangle s)).SE
          (T.mul (crossingTangle s)).SW)) ≤ T.maxArc + 4
      rw [hSE, hSW]
      have := maxArc_ge_NW T
      have := maxArc_ge_NE T
      omega
    · intro C hC
      rw [List.mem_append] at hC
      rcases hC with hC | hC
      · exact le_trans (maxArc_ge_of_mem T hC) (by omega)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        refine Crossing.rename_maxArc_le _ _ _ ?_
        intro a ha
        simpa [Function.comp, addShift] using
          mulGlue_shift_unit_le T s (crossingTangle_memArc_le s hC0 ha)
  · rw [← hSW]
    exact maxArc_ge_SW _

theorem mem_add_mapped {T S : TangleDiagram} {C : Crossing}
    (hC : C ∈ S.crossings) :
    C.rename (addGlue T S ∘ addShift T) ∈ (T.add S).crossings := by
  rw [add_crossings_append]
  exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))

theorem mem_mul_mapped {T S : TangleDiagram} {C : Crossing}
    (hC : C ∈ S.crossings) :
    C.rename (mulGlue T S ∘ addShift T) ∈ (T.mul S).crossings := by
  rw [mul_crossings_append]
  exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))

theorem appears_add_crossingTangle (T : TangleDiagram) (s : CrossingSign) (a : Nat) :
    (T.add (crossingTangle s)).appears a ↔
      T.appears a ∨ a = T.maxArc + 2 ∨ a = T.maxArc + 3 := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · exact Or.inl (Or.inl (by simpa [TangleDiagram.add] using hNW))
    · rw [add_crossingTangle_NE] at hNE; exact Or.inr (Or.inl hNE)
    · rw [add_crossingTangle_SE] at hSE; exact Or.inr (Or.inr hSE)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [TangleDiagram.add] using hSW)))))
    · rw [add_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩))))
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        have hb3 := crossingTangle_memArc_le s hC0 hb
        have hf := addGlue_shift_eq T (crossingTangle s) b
        simp [crossingTangle_NW, crossingTangle_SW, Function.comp, addShift, U] at hba hf
        rw [hf] at hba
        split_ifs at hba with hNW hSW
        · exact Or.inl (Or.inr (Or.inl hba.symm))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hba.symm)))
        · have hb02 : b ≠ 0 ∧ b ≠ 3 := ⟨hNW, hSW⟩
          have : b = 1 ∨ b = 2 := by omega
          rcases this with rfl | rfl
          · apply Or.inr; apply Or.inl; omega
          · apply Or.inr; apply Or.inr; omega
  · intro h
    rcases h with hT | rfl | rfl
    · rcases hT with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · left; simp [TangleDiagram.add]
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NW] : (crossingTangle s).NW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NW, hmem0, by
          simpa [Function.comp, addShift] using addGlue_NW T (crossingTangle s)⟩
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_SW] : (crossingTangle s).SW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).SW, hmem0, by
          simpa [Function.comp, addShift] using
            addGlue_SW T (crossingTangle s) (crossingTangle_NW_ne_SW s)⟩
      · right; right; right; left; simp [TangleDiagram.add]
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, by simp [add_crossings_append, hC], hmem⟩)))
    · exact Or.inr (Or.inl (add_crossingTangle_NE T s).symm)
    · exact Or.inr (Or.inr (Or.inl (add_crossingTangle_SE T s).symm))

theorem appears_mul_crossingTangle (T : TangleDiagram) (s : CrossingSign) (a : Nat) :
    (T.mul (crossingTangle s)).appears a ↔
      T.appears a ∨ a = T.maxArc + 3 ∨ a = T.maxArc + 4 := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · exact Or.inl (Or.inl (by simpa [TangleDiagram.mul] using hNW))
    · exact Or.inl (Or.inr (Or.inl (by simpa [TangleDiagram.mul] using hNE)))
    · rw [mul_crossingTangle_SE] at hSE; exact Or.inr (Or.inl hSE)
    · rw [mul_crossingTangle_SW] at hSW; exact Or.inr (Or.inr hSW)
    · rw [mul_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩))))
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        have hb3 := crossingTangle_memArc_le s hC0 hb
        have hf := mulGlue_shift_eq T (crossingTangle s) b
        simp [crossingTangle_NW, crossingTangle_NE, Function.comp, addShift, U] at hba hf
        rw [hf] at hba
        split_ifs at hba with hNW hNE
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hba.symm))))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hba.symm)))
        · have hb01 : b ≠ 0 ∧ b ≠ 1 := ⟨hNW, hNE⟩
          have : b = 2 ∨ b = 3 := by omega
          rcases this with rfl | rfl
          · apply Or.inr; apply Or.inl; omega
          · apply Or.inr; apply Or.inr; omega
  · intro h
    rcases h with hT | rfl | rfl
    · rcases hT with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · left; simp [TangleDiagram.mul]
      · right; left; simp [TangleDiagram.mul]
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NE] : (crossingTangle s).NE ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NE, hmem0, by
          simpa [Function.comp, addShift] using
            mulGlue_NE T (crossingTangle s) (crossingTangle_NW_ne_NE s)⟩
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NW] : (crossingTangle s).NW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NW, hmem0, by
          simpa [Function.comp, addShift] using mulGlue_NW T (crossingTangle s)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, by simp [mul_crossings_append, hC], hmem⟩)))
    · exact Or.inr (Or.inr (Or.inl (mul_crossingTangle_SE T s).symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_crossingTangle_SW T s).symm)))

theorem appears_add_left_unit (s : CrossingSign) (S : TangleDiagram) (a : Nat) :
    ((crossingTangle s).add S).appears a ↔
      a ≤ 3 ∨ ∃ b, S.appears b ∧
        addGlue (crossingTangle s) S
          (b + ((crossingTangle s).maxArc + 1)) = a := by
  let U := crossingTangle s
  have hUmax : U.maxArc = 3 := crossingTangle_maxArc s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · have : a = 0 := by simpa [TangleDiagram.add, crossingTangle_NW] using hNW
      omega
    · refine Or.inr ⟨S.NE, Or.inr (Or.inl rfl),
        (add_NE (crossingTangle s) S).symm.trans hNE.symm⟩
    · refine Or.inr ⟨S.SE, Or.inr (Or.inr (Or.inl rfl)),
        (add_SE (crossingTangle s) S).symm.trans hSE.symm⟩
    · have : a = 3 := by simpa [TangleDiagram.add, crossingTangle_SW] using hSW
      omega
    · rw [add_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · have : U.appears a := Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩)))
        exact Or.inl ((crossingTangle_appears s a).1 this)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        refine Or.inr ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, hC0, hb⟩))), ?_⟩
        simpa [Function.comp, addShift] using hba
  · intro h
    rcases h with ha | ⟨b, hbS, hglue⟩
    · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s ha
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, ?_, hmem0⟩)))
      rw [add_crossings_append]
      exact List.mem_append.2 (Or.inl hC0)
    · rcases hbS with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · have : a = (crossingTangle s).NE :=
          hglue.symm.trans (addGlue_NW (crossingTangle s) S)
        obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (le_trans (le_of_eq (crossingTangle_NE s)) (by decide : (1 : Nat) ≤ 3))
        rw [this]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
      · exact Or.inr (Or.inl (hglue.symm.trans (add_NE (crossingTangle s) S).symm))
      · exact Or.inr (Or.inr (Or.inl (hglue.symm.trans (add_SE (crossingTangle s) S).symm)))
      · have hba := hglue
        rw [addGlue_shift_eq] at hba
        split_ifs at hba with hNW hSW
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_NE s)) (by decide : (1 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_SE s)) (by decide : (2 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
        · exact (hSW rfl).elim
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨b, hmem, by simpa [Function.comp, addShift] using hglue⟩

theorem appears_mul_top_unit (s : CrossingSign) (S : TangleDiagram) (a : Nat) :
    ((crossingTangle s).mul S).appears a ↔
      a ≤ 3 ∨ ∃ b, S.appears b ∧
        mulGlue (crossingTangle s) S
          (b + ((crossingTangle s).maxArc + 1)) = a := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · have : a = 0 := by simpa [TangleDiagram.mul, crossingTangle_NW] using hNW
      omega
    · have : a = 1 := by simpa [TangleDiagram.mul, crossingTangle_NE] using hNE
      omega
    · refine Or.inr ⟨S.SE, Or.inr (Or.inr (Or.inl rfl)),
        (mul_SE_glue (crossingTangle s) S).symm.trans hSE.symm⟩
    · refine Or.inr ⟨S.SW, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        (mul_SW_glue (crossingTangle s) S).symm.trans hSW.symm⟩
    · rw [mul_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · have : U.appears a := Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩)))
        exact Or.inl ((crossingTangle_appears s a).1 this)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        refine Or.inr ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, hC0, hb⟩))), ?_⟩
        simpa [Function.comp, addShift] using hba
  · intro h
    rcases h with ha | ⟨b, hbS, hglue⟩
    · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s ha
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, ?_, hmem0⟩)))
      rw [mul_crossings_append]
      exact List.mem_append.2 (Or.inl hC0)
    · rcases hbS with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · have : a = (crossingTangle s).SW :=
          hglue.symm.trans (mulGlue_NW (crossingTangle s) S)
        obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (le_of_eq (crossingTangle_SW s))
        rw [this]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
      · have hba := hglue
        rw [mulGlue_shift_eq] at hba
        split_ifs at hba with hNW hNE
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_of_eq (crossingTangle_SW s))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_SE s)) (by decide : (2 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
        · exact (hNE rfl).elim
      · rw [← mul_SE_glue] at hglue
        rw [← hglue]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [← mul_SW_glue] at hglue
        rw [← hglue]
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨b, hmem, by simpa [Function.comp, addShift] using hglue⟩

theorem addGlue_crossingTangle_congr (s t : CrossingSign) {S S' : TangleDiagram}
    (hNW : S.NW = S'.NW) (hSW : S.SW = S'.SW) (b : Nat) :
    addGlue (crossingTangle s) S (b + ((crossingTangle s).maxArc + 1)) =
      addGlue (crossingTangle t) S' (b + ((crossingTangle t).maxArc + 1)) := by
  rw [addGlue_shift_eq, addGlue_shift_eq]
  simp [crossingTangle_NE, crossingTangle_SE, crossingTangle_maxArc, hNW, hSW]

theorem mulGlue_crossingTangle_congr (s t : CrossingSign) {S S' : TangleDiagram}
    (hNW : S.NW = S'.NW) (hNE : S.NE = S'.NE) (b : Nat) :
    mulGlue (crossingTangle s) S (b + ((crossingTangle s).maxArc + 1)) =
      mulGlue (crossingTangle t) S' (b + ((crossingTangle t).maxArc + 1)) := by
  rw [mulGlue_shift_eq, mulGlue_shift_eq]
  simp [crossingTangle_SW, crossingTangle_SE, crossingTangle_maxArc, hNW, hNE]

theorem TwistExpr.mirror_diagram_core (e : TwistExpr) :
    e.mirror.diagram.NW = e.diagram.NW ∧
    e.mirror.diagram.NE = e.diagram.NE ∧
    e.mirror.diagram.SE = e.diagram.SE ∧
    e.mirror.diagram.SW = e.diagram.SW ∧
    (∀ a, e.mirror.diagram.appears a ↔ e.diagram.appears a) ∧
    e.mirror.diagram.maxArc = e.diagram.maxArc := by
  induction e with
  | zero =>
    simp [TwistExpr.mirror, TwistExpr.diagram]
  | infinity =>
    simp [TwistExpr.mirror, TwistExpr.diagram]
  | one =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro a
      simpa [TwistExpr.mirror, TwistExpr.diagram] using
        (negOne_appears a).trans (one_appears a).symm
    · simpa [TwistExpr.mirror, TwistExpr.diagram, Neg.neg] using
        maxArc_mirror RationalTangles.one
  | negOne =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro a
      simpa [TwistExpr.mirror, TwistExpr.diagram] using
        (one_appears a).trans (negOne_appears a).symm
    · simpa [TwistExpr.mirror, TwistExpr.diagram, Neg.neg] using
        (maxArc_mirror RationalTangles.one).symm
  | addRight e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hNEsum :
        (e.mirror.diagram.add (crossingTangle s.flip)).NE =
          (e.diagram.add (crossingTangle s)).NE := by
      rw [add_crossingTangle_NE, add_crossingTangle_NE, hmax]
    have hSEsum :
        (e.mirror.diagram.add (crossingTangle s.flip)).SE =
          (e.diagram.add (crossingTangle s)).SE := by
      rw [add_crossingTangle_SE, add_crossingTangle_SE, hmax]
    refine ⟨?_, hNEsum, hSEsum, ?_, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, hNW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, hSW]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_crossingTangle, appears_add_crossingTangle, happ, hmax]
    · simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [add_crossingTangle_maxArc, add_crossingTangle_maxArc, hmax]
  | mulBottom e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hSEsum :
        (e.mirror.diagram.mul (crossingTangle s.flip)).SE =
          (e.diagram.mul (crossingTangle s)).SE := by
      rw [mul_crossingTangle_SE, mul_crossingTangle_SE, hmax]
    have hSWsum :
        (e.mirror.diagram.mul (crossingTangle s.flip)).SW =
          (e.diagram.mul (crossingTangle s)).SW := by
      rw [mul_crossingTangle_SW, mul_crossingTangle_SW, hmax]
    refine ⟨?_, ?_, hSEsum, hSWsum, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, hNW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, hNE]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_crossingTangle, appears_mul_crossingTangle, happ, hmax]
    · simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [mul_crossingTangle_maxArc, mul_crossingTangle_maxArc, hmax]
  | addLeft e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hNEsum :
        ((crossingTangle s.flip).add e.mirror.diagram).NE =
          ((crossingTangle s).add e.diagram).NE := by
      rw [add_NE, add_NE, hNE]
      exact addGlue_crossingTangle_congr s.flip s hNW hSW _
    have hSEsum :
        ((crossingTangle s.flip).add e.mirror.diagram).SE =
          ((crossingTangle s).add e.diagram).SE := by
      rw [add_SE, add_SE, hSE]
      exact addGlue_crossingTangle_congr s.flip s hNW hSW _
    refine ⟨?_, hNEsum, hSEsum, ?_, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, crossingTangle_NW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, crossingTangle_SW]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_left_unit, appears_add_left_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (addGlue_crossingTangle_congr s.flip s hNW hSW b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (addGlue_crossingTangle_congr s s.flip hNW.symm hSW.symm b).symm.trans hglue
    · apply TangleDiagram.maxArc_eq_of_appears
      intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_left_unit, appears_add_left_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (addGlue_crossingTangle_congr s.flip s hNW hSW b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (addGlue_crossingTangle_congr s s.flip hNW.symm hSW.symm b).symm.trans hglue
  | mulTop e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hSEsum :
        ((crossingTangle s.flip).mul e.mirror.diagram).SE =
          ((crossingTangle s).mul e.diagram).SE := by
      rw [mul_SE_glue, mul_SE_glue, hSE]
      exact mulGlue_crossingTangle_congr s.flip s hNW hNE _
    have hSWsum :
        ((crossingTangle s.flip).mul e.mirror.diagram).SW =
          ((crossingTangle s).mul e.diagram).SW := by
      rw [mul_SW_glue, mul_SW_glue, hSW]
      exact mulGlue_crossingTangle_congr s.flip s hNW hNE _
    refine ⟨?_, ?_, hSEsum, hSWsum, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, crossingTangle_NW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, crossingTangle_NE]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_top_unit, appears_mul_top_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s.flip s hNW hNE b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s s.flip hNW.symm hNE.symm b).symm.trans hglue
    · apply TangleDiagram.maxArc_eq_of_appears
      intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_top_unit, appears_mul_top_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s.flip s hNW hNE b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s s.flip hNW.symm hNE.symm b).symm.trans hglue

theorem TwistExpr.mirror_NW (e : TwistExpr) : e.mirror.diagram.NW = e.diagram.NW :=
  (e.mirror_diagram_core).1

theorem TwistExpr.mirror_NE (e : TwistExpr) : e.mirror.diagram.NE = e.diagram.NE :=
  (e.mirror_diagram_core).2.1

theorem TwistExpr.mirror_SE (e : TwistExpr) : e.mirror.diagram.SE = e.diagram.SE :=
  (e.mirror_diagram_core).2.2.1

theorem TwistExpr.mirror_SW (e : TwistExpr) : e.mirror.diagram.SW = e.diagram.SW :=
  (e.mirror_diagram_core).2.2.2.1

theorem TwistExpr.mirror_appears (e : TwistExpr) (a : Nat) :
    e.mirror.diagram.appears a ↔ e.diagram.appears a :=
  (e.mirror_diagram_core).2.2.2.2.1 a

theorem TwistExpr.mirror_maxArc (e : TwistExpr) :
    e.mirror.diagram.maxArc = e.diagram.maxArc :=
  (e.mirror_diagram_core).2.2.2.2.2

theorem TwistExpr.slideReady_mirror (e : TwistExpr) (hok : e.slideReady) :
    e.mirror.slideReady := by
  induction e with
  | zero | infinity | one | negOne => simp [TwistExpr.mirror, TwistExpr.slideReady]
  | addRight e s ih =>
    simpa [TwistExpr.mirror, TwistExpr.slideReady] using ih hok
  | mulBottom e s ih =>
    simpa [TwistExpr.mirror, TwistExpr.slideReady] using ih hok
  | addLeft e s ih =>
    obtain ⟨hne, hok'⟩ := hok
    refine ⟨?_, ih hok'⟩
    simpa [TwistExpr.mirror, TwistExpr.slideReady, e.mirror_NW, e.mirror_SW] using hne
  | mulTop e s ih =>
    obtain ⟨hne, hok'⟩ := hok
    refine ⟨?_, ih hok'⟩
    simpa [TwistExpr.mirror, TwistExpr.slideReady, e.mirror_NW, e.mirror_NE] using hne

theorem TwistExpr.toStandard_mirror (e : TwistExpr) :
    e.mirror.toStandard = e.toStandard.mirror := by
  induction e with
  | zero | infinity => rfl
  | one | negOne =>
    simp [TwistExpr.mirror, TwistExpr.toStandard, StandardExpr.mirror, CrossingSign.flip]
  | addRight e s ih | addLeft e s ih | mulBottom e s ih | mulTop e s ih =>
    simp [TwistExpr.mirror, TwistExpr.toStandard, StandardExpr.mirror, ih]

theorem coloring_mirror_diagram_slideReady (e : TwistExpr) (hok : e.slideReady) :
    ColoringIsotopy e.diagram.mirror e.mirror.diagram := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | infinity =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | one =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | negOne =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .isotopy (planar_mirror_mirror one)
  | addRight e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).SW := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).SW :=
        crossingTangle_NW_ne_SW s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := (crossingTangle s).mirror) (ih hok'))
        (.add_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).NE := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).NE :=
        crossingTangle_NW_ne_NE s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := (crossingTangle s).mirror) (ih hok'))
        (.mul_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_mul] using hstep
  | addLeft e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.diagram.mirror.NW = e.diagram.mirror.SW →
        e.mirror.diagram.NW = e.mirror.diagram.SW := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_SW] using h
    have hstep :=
      ColoringIsotopy.trans
        (.add_right (T := (crossingTangle s).mirror) (ih hok') hglue)
        (.add_left (S := e.mirror.diagram) (coloring_crossingTangle_mirror s))
    simpa [mirror_add] using hstep
  | mulTop e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.diagram.mirror.NW = e.diagram.mirror.NE →
        e.mirror.diagram.NW = e.mirror.diagram.NE := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_NE] using h
    have hstep :=
      ColoringIsotopy.trans
        (.mul_right (T := (crossingTangle s).mirror) (ih hok') hglue)
        (.mul_left (S := e.mirror.diagram) (coloring_crossingTangle_mirror s))
    simpa [mirror_mul] using hstep

theorem coloring_mirror_diagram_rev_slideReady (e : TwistExpr) (hok : e.slideReady) :
    ColoringIsotopy e.mirror.diagram e.diagram.mirror := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | infinity =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | one =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | negOne =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .isotopy (planar_mirror_mirror_rev one)
  | addRight e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).SW →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).SW :=
        crossingTangle_NW_ne_SW s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := crossingTangle s.flip) (ih hok'))
        (.add_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).NE →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).NE :=
        crossingTangle_NW_ne_NE s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := crossingTangle s.flip) (ih hok'))
        (.mul_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_mul] using hstep
  | addLeft e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.mirror.diagram.NW = e.mirror.diagram.SW →
        e.diagram.mirror.NW = e.diagram.mirror.SW := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_SW] using h
    have hstep :=
      ColoringIsotopy.trans
        (.add_right (T := crossingTangle s.flip) (ih hok') hglue)
        (.add_left (S := e.diagram.mirror) (coloring_crossingTangle_mirror_rev s))
    simpa [mirror_add] using hstep
  | mulTop e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.mirror.diagram.NW = e.mirror.diagram.NE →
        e.diagram.mirror.NW = e.diagram.mirror.NE := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_NE] using h
    have hstep :=
      ColoringIsotopy.trans
        (.mul_right (T := crossingTangle s.flip) (ih hok') hglue)
        (.mul_left (S := e.diagram.mirror) (coloring_crossingTangle_mirror_rev s))
    simpa [mirror_mul] using hstep

/-- A non-monochrome coloring of the PD-mirror of a `slideReady` diagram has
    coloring fraction `-f(T)`. Fresh coloring of the algebraic mirror, via
    `ColoringIsotopy` to `e.diagram.mirror`. -/
theorem coloring_mirror_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col col' : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hc' : e.diagram.mirror.IsColored col')
    (hm' : (ColorMatrix.of e.diagram.mirror col').NotMono) :
    (ColorMatrix.of e.diagram.mirror col').fraction =
      (ColorMatrix.of e.diagram col).fraction.neg := by
  obtain ⟨colM, hcM, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_slideReady e hok) col' hc'
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono := by
    simpa [hMat] using hm'
  have hdiag := twist_coloring_diagonal_slideReady e hok col hc
  have hokM := TwistExpr.slideReady_mirror e hok
  have hdiagM := twist_coloring_diagonal_slideReady e.mirror hokM colM hcM
  have hfT := coloring_fraction_eq_F e hok col hc hdiag hm
  have hfM := coloring_fraction_eq_F e.mirror hokM colM hcM hdiagM hmM
  rw [hfrac.symm, hfM, TwistExpr.toStandard_mirror, StandardExpr.fraction_mirror, hfT]

/-- `f(Tⁱ) = 1/f(T)` on a `slideReady` twist diagram, via a fresh coloring of
    the algebraic mirror transported along `coloring_mirror_diagram_rev_slideReady`. -/
theorem coloring_invert_inv_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction =
        (ColorMatrix.of e.diagram col).fraction.inv := by
  have hokM : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  let colM := e.mirror.colorFrom 0 1
  have hcM : e.mirror.diagram.IsColored colM :=
    e.mirror.colorFrom_isColored_slideReady hokM 0 1
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono :=
    e.mirror.colorFrom_notMono_slideReady hokM
  have hdM : (ColorMatrix.of e.mirror.diagram colM).DiagonalSum :=
    e.mirror.colorFrom_diagonal_slideReady hokM 0 1
  obtain ⟨col', hc', hMat, _hfrac⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_rev_slideReady e hok) colM hcM
  have hm' : (ColorMatrix.of e.diagram.mirror col').NotMono := by
    simpa [hMat] using hmM
  have hd' : (ColorMatrix.of e.diagram.mirror col').DiagonalSum := by
    simpa [hMat] using hdM
  have hcI : e.diagram.invert.IsColored col' := by
    simpa [invert_eq_mirror_rotate] using coloring_rotate _ col' hc'
  refine ⟨col', hcI, ?_, ?_⟩
  · have hrot :
        ColorMatrix.of e.diagram.invert col' =
          (ColorMatrix.of e.diagram.mirror col').rotate := by
      simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
    simpa [hrot] using ColorMatrix.NotMono_rotate hd' hm'
  · have hrot :
        (ColorMatrix.of e.diagram.invert col').fraction =
          (ColorMatrix.of e.diagram.mirror col').fraction.negInv := by
      simpa [invert_eq_mirror_rotate] using
        coloring_fraction_rotate e.diagram.mirror col' hd' hm'
    have hfM := coloring_mirror_slideReady e hok col col' hc hm hc' hm'
    rw [hrot, hfM, CFValue.negInv, ← CFValue.neg_inv, CFValue.neg_neg]


end RationalTangles
