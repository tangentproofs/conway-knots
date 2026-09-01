/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.ColoringR3
import RationalTangles.Flype

/-!
# Coloring invariance under a local flype

`IsLocalFlype` slides one crossing over a neighboring subtangle whose
crossings are turned 180°. Recoloring special-cases the two distinguished
legs of the sliding crossing and pulls the rest back along `f`, including
the rotated subtangle.
-/

namespace RationalTangles

noncomputable def colorFlype (f : Nat → Nat) (uD wD uE wE : Nat)
    (col : Nat → Int) (a : Nat) : Int :=
  if a = uE then col uD
  else if a = wE then col wD
  else col (Function.invFun f a)

theorem colorFlype_uE (f : Nat → Nat) (uD wD uE wE : Nat) (col : Nat → Int) :
    colorFlype f uD wD uE wE col uE = col uD := by
  simp [colorFlype]

theorem colorFlype_wE (f : Nat → Nat) (uD wD uE wE : Nat) (col : Nat → Int)
    (huw : uE ≠ wE) :
    colorFlype f uD wD uE wE col wE = col wD := by
  simp [colorFlype, huw.symm]

theorem colorFlype_of_ne (f : Nat → Nat) (uD wD uE wE : Nat)
    (col : Nat → Int) {a : Nat} (hu : a ≠ uE) (hw : a ≠ wE) :
    colorFlype f uD wD uE wE col a = col (Function.invFun f a) := by
  simp [colorFlype, hu, hw]

theorem colorFlype_f (f : Nat → Nat) (uD wD uE wE : Nat)
    (col : Nat → Int) (hf : Function.Injective f) {a : Nat}
    (hu : f a ≠ uE) (hw : f a ≠ wE) :
    colorFlype f uD wD uE wE col (f a) = col a := by
  rw [colorFlype_of_ne f uD wD uE wE col hu hw, Function.leftInverse_invFun hf]

theorem flype_extOver_not_uw {FD FE : Crossing} {f : Nat → Nat}
    {uD wD uE wE : Nat} (h : IsFlypeCrossingSlide f FD FE uD wD uE wE) :
    FE.extOverArc uE ≠ uE ∧ FE.extOverArc uE ≠ wE :=
  ⟨Crossing.extOverArc_ne_self h.overE h.portsE.2.1,
    Crossing.isOver_ne_isUnder (Crossing.extOverArc_isOver h.overE) h.underE
      h.portsE⟩

theorem flype_otherUnder_not_uw {FD FE : Crossing} {f : Nat → Nat}
    {uD wD uE wE : Nat} (h : IsFlypeCrossingSlide f FD FE uD wD uE wE) :
    FE.otherUnderArc wE ≠ uE ∧ FE.otherUnderArc wE ≠ wE :=
  ⟨(Crossing.isOver_ne_isUnder h.overE (Crossing.otherUnderArc_isUnder FE wE)
      h.portsE).symm,
    Crossing.otherUnderArc_ne_self h.underE h.portsE.2.2.2.2.1⟩

theorem colorFlype_ColoringRule_FE (f : Nat → Nat)
    {FD FE : Crossing} {uD wD uE wE : Nat}
    (col : Nat → Int) (hf : Function.Injective f)
    (h : IsFlypeCrossingSlide f FD FE uD wD uE wE)
    (hFD : ColoringRule FD col) :
    ColoringRule FE (colorFlype f uD wD uE wE col) := by
  let col' := colorFlype f uD wD uE wE col
  have hcu : col' uE = col uD := colorFlype_uE f uD wD uE wE col
  have hcw : col' wE = col wD := colorFlype_wE f uD wD uE wE col h.huwE
  have hPext := flype_extOver_not_uw (FD := FD) h
  have hPund := flype_otherUnder_not_uw (FD := FD) h
  have hcExt : col' (FE.extOverArc uE) = col (FD.extOverArc uD) := by
    rw [h.ext_match]
    exact colorFlype_f f uD wD uE wE col hf (h.ext_match ▸ hPext.1)
      (h.ext_match ▸ hPext.2)
  have hcUnd : col' (FE.otherUnderArc wE) = col (FD.otherUnderArc wD) := by
    rw [h.und_match]
    exact colorFlype_f f uD wD uE wE col hf (h.und_match ▸ hPund.1)
      (h.und_match ▸ hPund.2)
  have hoverD := Crossing.extOverArc_color hFD h.overD
  have hsumD :=
    Crossing.otherUnderArc_sum_over hFD h.overD h.underD h.portsD.2.2.2.2.1
  refine ColoringRule_of_slide FE col' uE wE h.overE h.underE h.portsE ?_ ?_
  · exact hcExt.trans (hoverD.trans hcu.symm)
  · rw [hcw, hcUnd, hcu]; exact hsumD

theorem ColoringRule_colorFlype_rest (f : Nat → Nat)
    (uD wD uE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f) {X : Crossing}
    (hX : ColoringRule X col)
    {Y : Crossing} (hXY : (X.rename f).sameUpToRotation Y)
    (hY : ¬ Y.memArc uE ∧ ¬ Y.memArc wE) :
    ColoringRule Y (colorFlype f uD wD uE wE col) := by
  have hmem : ∀ a, Y.memArc a ↔ (X.rename f).memArc a :=
    fun a => (sameUpToRotation_memArc hXY).symm
  have hy0 : Y.memArc (f X.a0) :=
    (hmem _).2 (by simp [Crossing.memArc, Crossing.rename])
  have hy1 : Y.memArc (f X.a1) :=
    (hmem _).2 (by simp [Crossing.memArc, Crossing.rename])
  have hy2 : Y.memArc (f X.a2) :=
    (hmem _).2 (by simp [Crossing.memArc, Crossing.rename])
  have hy3 : Y.memArc (f X.a3) :=
    (hmem _).2 (by simp [Crossing.memArc, Crossing.rename])
  have hrename : ColoringRule (X.rename f)
      (colorFlype f uD wD uE wE col) := by
    rw [ColoringRule_rename]
    refine ColoringRule_congr
      (colorFlype_f f uD wD uE wE col hf
        (ne_of_mem_not_mem hy0 hY.1) (ne_of_mem_not_mem hy0 hY.2))
      (colorFlype_f f uD wD uE wE col hf
        (ne_of_mem_not_mem hy1 hY.1) (ne_of_mem_not_mem hy1 hY.2))
      (colorFlype_f f uD wD uE wE col hf
        (ne_of_mem_not_mem hy2 hY.1) (ne_of_mem_not_mem hy2 hY.2))
      (colorFlype_f f uD wD uE wE col hf
        (ne_of_mem_not_mem hy3 hY.1) (ne_of_mem_not_mem hy3 hY.2))
      hX
  exact ColoringRule_sameUpToRotation (colorFlype f uD wD uE wE col) hXY hrename

theorem ColoringRule_colorFlype_t (f : Nat → Nat)
    (uD wD uE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f) {X : Crossing}
    (hX : ColoringRule X col)
    {Y : Crossing} (hXY : (X.rotate180.rename f).sameUpToRotation Y)
    (hY : ¬ Y.memArc uE ∧ ¬ Y.memArc wE) :
    ColoringRule Y (colorFlype f uD wD uE wE col) :=
  ColoringRule_colorFlype_rest (X := X.rotate180) f uD wD uE wE col hf
    (ColoringRule_rotate180 X col hX) hXY hY

theorem pairRel_colorFlype_rest (f : Nat → Nat)
    (uD wD uE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f)
    {restD restE : List Crossing}
    (hpair : pairRel Crossing.sameUpToRotation
      (restD.map (Crossing.rename f)) restE)
    (hrestD : ∀ C ∈ restD, ColoringRule C col)
    (hrestE : ∀ C ∈ restE, ¬ C.memArc uE ∧ ¬ C.memArc wE) :
    ∀ C ∈ restE, ColoringRule C (colorFlype f uD wD uE wE col) := by
  induction restD generalizing restE with
  | nil =>
    cases restE with
    | nil => intro C hC; cases hC
    | cons _ _ => cases hpair
  | cons X xs ih =>
    cases restE with
    | nil => cases hpair
    | cons Y ys =>
      obtain ⟨hXY, hrest⟩ := hpair
      intro Z hZ
      rw [List.mem_cons] at hZ
      cases hZ with
      | inl hEq =>
        rw [hEq]
        exact ColoringRule_colorFlype_rest f uD wD uE wE col hf
          (hrestD X (by simp)) hXY (hrestE Y (by simp))
      | inr hZ =>
        exact ih hrest (fun W hW => hrestD W (by simp [hW]))
          (fun W hW => hrestE W (by simp [hW])) Z hZ

theorem pairRel_colorFlype_t (f : Nat → Nat)
    (uD wD uE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f)
    {tD tE : List Crossing}
    (hpair : pairRel (fun C Y => (C.rotate180.rename f).sameUpToRotation Y)
      tD tE)
    (htD : ∀ C ∈ tD, ColoringRule C col)
    (htE : ∀ C ∈ tE, ¬ C.memArc uE ∧ ¬ C.memArc wE) :
    ∀ C ∈ tE, ColoringRule C (colorFlype f uD wD uE wE col) := by
  induction tD generalizing tE with
  | nil =>
    cases tE with
    | nil => intro C hC; cases hC
    | cons _ _ => cases hpair
  | cons X xs ih =>
    cases tE with
    | nil => cases hpair
    | cons Y ys =>
      obtain ⟨hXY, hrest⟩ := hpair
      intro Z hZ
      rw [List.mem_cons] at hZ
      cases hZ with
      | inl hEq =>
        rw [hEq]
        exact ColoringRule_colorFlype_t f uD wD uE wE col hf
          (htD X (by simp)) hXY (htE Y (by simp))
      | inr hZ =>
        exact ih hrest (fun W hW => htD W (by simp [hW]))
          (fun W hW => htE W (by simp [hW])) Z hZ

theorem colorFlype_endpoint (f : Nat → Nat) (uD wD uE wE : Nat)
    (col : Nat → Int) (hf : Function.Injective f) (a : Nat)
    (hu : f a ≠ uE) (hw : f a ≠ wE) :
    colorFlype f uD wD uE wE col (f a) = col a :=
  colorFlype_f f uD wD uE wE col hf hu hw

/-- Given a coloring of a 2-tangle, there is a way to recolor after a local
flype so that the colors on the external strands are unchanged and the
coloring rule still holds at every crossing. -/
theorem coloring_IsLocalFlype (D E : TangleDiagram) (col : Nat → Int)
    (h : IsLocalFlype D E) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨f, FD, FE, tD, tE, restD, restE, uD, wD, uE, wE,
    hf, hslide, hNW, hNE, hSE, hSW, hpermD, hpermE, hpairRest, hpairT,
    hrestE, htE⟩ := h
  let col' := colorFlype f uD wD uE wE col
  have hFD : ColoringRule FD col :=
    hc FD ((List.Perm.mem_iff hpermD).2 (by simp))
  have htD : ∀ C ∈ tD, ColoringRule C col :=
    fun C hC => hc C ((List.Perm.mem_iff hpermD).2 (by
      simp [List.mem_cons, List.mem_append, hC]))
  have hrestD : ∀ C ∈ restD, ColoringRule C col :=
    fun C hC => hc C ((List.Perm.mem_iff hpermD).2 (by
      simp [List.mem_cons, List.mem_append, hC]))
  have hFE := colorFlype_ColoringRule_FE f col hf hslide hFD
  have ht := pairRel_colorFlype_t f uD wD uE wE col hf hpairT htD htE
  have hrest := pairRel_colorFlype_rest f uD wD uE wE col hf hpairRest hrestD
    hrestE
  refine ⟨col', ?_, ?_⟩
  · intro C hC
    have : C = FE ∨ C ∈ tE ∨ C ∈ restE := by
      have := (List.Perm.mem_iff hpermE).1 hC
      simp [List.mem_cons, List.mem_append] at this
      tauto
    rcases this with hC' | hC' | hC'
    · subst hC'; exact hFE
    · exact ht C hC'
    · exact hrest C hC'
  · have hbnd (a : Nat) : col' (f a) = col a := by
      by_cases hu : f a = uE
      · have ha : a = uD := hf (hu.trans hslide.u_map)
        calc
          col' (f a) = col' uE := by rw [hu]
          _ = col uD := colorFlype_uE f uD wD uE wE col
          _ = col a := by rw [ha]
      · by_cases hw : f a = wE
        · have ha : a = wD := hf (hw.trans hslide.w_map)
          calc
            col' (f a) = col' wE := by rw [hw]
            _ = col wD := colorFlype_wE f uD wD uE wE col hslide.huwE
            _ = col a := by rw [ha]
        · exact colorFlype_f f uD wD uE wE col hf hu hw
    exact ⟨by rw [hNW]; exact hbnd D.NW,
      by rw [hNE]; exact hbnd D.NE,
      by rw [hSE]; exact hbnd D.SE,
      by rw [hSW]; exact hbnd D.SW⟩

end RationalTangles
