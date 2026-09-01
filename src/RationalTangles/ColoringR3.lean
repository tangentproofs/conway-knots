/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.List.Perm.Basic
import RationalTangles.ColoringInvariance

/-!
# Coloring invariance under a local Reidemeister III over-slide

`IsReidemeisterIIILocal` replaces a triangular triple by another over-slide
triple with matching external legs, identifying the rest of the diagram by
permutation (no `dropIdxs`). Rest and boundary constraints hold on both
diagrams. Recoloring keeps the six external-leg colors and copies the three
internal colors onto the new internal arcs. Reverse uses `planarInvFun` on
appearing arcs of `D` (`IsReidemeisterIIILocal.symm`).
-/

namespace RationalTangles

/-! ## Port lemmas -/

theorem Crossing.extOverArc_mem (C : Crossing) (u : Nat) :
    C.memArc (C.extOverArc u) := by
  unfold Crossing.extOverArc Crossing.memArc
  split_ifs <;> simp

theorem Crossing.otherUnderArc_mem (C : Crossing) (w : Nat) :
    C.memArc (C.otherUnderArc w) := by
  unfold Crossing.otherUnderArc Crossing.memArc
  split_ifs <;> simp

theorem Crossing.otherUnderArc_isUnder (C : Crossing) (w : Nat) :
    C.isUnderArc (C.otherUnderArc w) := by
  unfold Crossing.otherUnderArc Crossing.isUnderArc
  split_ifs <;> simp

theorem Crossing.isOverArc.color {C : Crossing} {col : Nat → Int} {a : Nat}
    (h : ColoringRule C col) (ho : C.isOverArc a) :
    col a = col C.a0 := by
  rcases ho with h0 | h2
  · simp [h0]
  · simp [h2, h.1]

theorem Crossing.extOverArc_isOver {C : Crossing} {u : Nat}
    (ho : C.isOverArc u) : C.isOverArc (C.extOverArc u) := by
  unfold Crossing.extOverArc Crossing.isOverArc at *
  rcases ho with h0 | h2
  · simp [h0]
  · split_ifs <;> simp [h2]

theorem Crossing.extOverArc_ne_self {C : Crossing} {u : Nat}
    (ho : C.isOverArc u) (hd : C.a0 ≠ C.a2) :
    C.extOverArc u ≠ u := by
  unfold Crossing.extOverArc
  rcases ho with h0 | h2
  · simp [h0]
    intro heq
    exact hd heq.symm
  · intro heq
    split_ifs at heq with h0'
    · exact hd (h0'.trans h2)
    · exact h0' heq

theorem Crossing.otherUnderArc_ne_self {C : Crossing} {w : Nat}
    (hu : C.isUnderArc w) (hd : C.a1 ≠ C.a3) :
    C.otherUnderArc w ≠ w := by
  unfold Crossing.otherUnderArc
  rcases hu with h1 | h3
  · simp [h1]
    intro heq
    exact hd heq.symm
  · intro heq
    split_ifs at heq with h1'
    · exact hd (h1'.trans h3)
    · exact h1' heq

theorem Crossing.isOver_ne_isUnder {C : Crossing} {u w : Nat}
    (ho : C.isOverArc u) (hu : C.isUnderArc w) (hd : C.portsDistinct) :
    u ≠ w := by
  intro h
  rcases ho with h0 | h2 <;> rcases hu with h1 | h3
  · exact hd.1 (h0.symm.trans (h.trans h1))
  · exact hd.2.2.1 (h0.symm.trans (h.trans h3))
  · exact hd.2.2.2.1 (h1.symm.trans (h.symm.trans h2))
  · exact hd.2.2.2.2.2 (h2.symm.trans (h.trans h3))

theorem Crossing.extOverArc_color {C : Crossing} {col : Nat → Int} {u : Nat}
    (h : ColoringRule C col) (ho : C.isOverArc u) :
    col (C.extOverArc u) = col u := by
  unfold Crossing.extOverArc
  rcases ho with h0 | h2
  · simpa [h0] using h.1.symm
  · split_ifs with h0'
    · simp [h2]
    · simp [h2, h.1]

theorem Crossing.otherUnderArc_sum {C : Crossing} {col : Nat → Int} {w : Nat}
    (h : ColoringRule C col) (hu : C.isUnderArc w) (hd : C.a1 ≠ C.a3) :
    col w + col (C.otherUnderArc w) = 2 * col C.a0 := by
  unfold Crossing.otherUnderArc
  rcases hu with h1 | h3
  · simp [h1, h.2]
  · have hif : (if C.a1 = C.a3 then C.a3 else C.a1) = C.a1 := by simp [hd]
    simp [h3, hif]
    linarith [h.2]

theorem Crossing.otherUnderArc_sum_over {C : Crossing} {col : Nat → Int}
    {u w : Nat} (h : ColoringRule C col)
    (ho : C.isOverArc u) (hu : C.isUnderArc w) (hd : C.a1 ≠ C.a3) :
    col w + col (C.otherUnderArc w) = 2 * col u := by
  have hs := Crossing.otherUnderArc_sum h hu hd
  have hu0 : col u = col C.a0 := Crossing.isOverArc.color h ho
  linarith

theorem ne_of_mem_not_mem {C : Crossing} {x y : Nat}
    (hx : C.memArc x) (hy : ¬ C.memArc y) : x ≠ y :=
  fun h => hy (h ▸ hx)

theorem Crossing.extOverArc_eq_a2 {C : Crossing} {u : Nat}
    (h0 : u = C.a0) : C.extOverArc u = C.a2 := by
  unfold Crossing.extOverArc; simp [h0]

theorem Crossing.extOverArc_eq_a0 {C : Crossing} {u : Nat}
    (h2 : u = C.a2) (hd : C.a0 ≠ C.a2) : C.extOverArc u = C.a0 := by
  unfold Crossing.extOverArc
  split_ifs with h0'
  · exact (hd (h0'.trans h2)).elim
  · rfl

theorem Crossing.otherUnderArc_eq_a3 {C : Crossing} {w : Nat}
    (h1 : w = C.a1) : C.otherUnderArc w = C.a3 := by
  unfold Crossing.otherUnderArc; simp [h1]

theorem Crossing.otherUnderArc_eq_a1 {C : Crossing} {w : Nat}
    (h3 : w = C.a3) (hd : C.a1 ≠ C.a3) : C.otherUnderArc w = C.a1 := by
  unfold Crossing.otherUnderArc
  split_ifs with h1'
  · exact (hd (h1'.trans h3)).elim
  · rfl

theorem ColoringRule_of_slide (C : Crossing) (col : Nat → Int) (u w : Nat)
    (ho : C.isOverArc u) (hu : C.isUnderArc w) (hd : C.portsDistinct)
    (hover : col (C.extOverArc u) = col u)
    (hunder : col w + col (C.otherUnderArc w) = 2 * col u) :
    ColoringRule C col := by
  have ha0 : col C.a0 = col u := by
    rcases ho with h0 | h2
    · rw [h0]
    · rw [← Crossing.extOverArc_eq_a0 h2 hd.2.1, hover]
  constructor
  · rcases ho with h0 | h2
    · have ha2 := Crossing.extOverArc_eq_a2 (C := C) h0
      calc
        col C.a0 = col u := by rw [h0]
        _ = col (C.extOverArc u) := hover.symm
        _ = col C.a2 := by rw [ha2]
    · calc
        col C.a0 = col u := ha0
        _ = col C.a2 := by rw [h2]
  · rcases hu with h1 | h3
    · have ho3 := Crossing.otherUnderArc_eq_a3 (C := C) h1
      rw [ho3, h1] at hunder
      linarith
    · have ho1 := Crossing.otherUnderArc_eq_a1 (C := C) h3 hd.2.2.2.2.1
      rw [ho1, h3] at hunder
      linarith

/-! ## Recoloring map -/

noncomputable def colorR3 (f : Nat → Nat) (uD vD wD uE vE wE : Nat)
    (col : Nat → Int) (a : Nat) : Int :=
  if a = uE then col uD
  else if a = vE then col vD
  else if a = wE then col wD
  else col (Function.invFun f a)

theorem colorR3_uE (f : Nat → Nat) (uD vD wD uE vE wE : Nat) (col : Nat → Int) :
    colorR3 f uD vD wD uE vE wE col uE = col uD := by
  simp [colorR3]

theorem colorR3_vE (f : Nat → Nat) (uD vD wD uE vE wE : Nat) (col : Nat → Int)
    (huv : uE ≠ vE) :
    colorR3 f uD vD wD uE vE wE col vE = col vD := by
  simp [colorR3, huv.symm]

theorem colorR3_wE (f : Nat → Nat) (uD vD wD uE vE wE : Nat) (col : Nat → Int)
    (huw : uE ≠ wE) (hvw : vE ≠ wE) :
    colorR3 f uD vD wD uE vE wE col wE = col wD := by
  simp [colorR3, huw.symm, hvw.symm]

theorem colorR3_of_ne (f : Nat → Nat) (uD vD wD uE vE wE : Nat)
    (col : Nat → Int) {a : Nat} (hu : a ≠ uE) (hv : a ≠ vE) (hw : a ≠ wE) :
    colorR3 f uD vD wD uE vE wE col a = col (Function.invFun f a) := by
  simp [colorR3, hu, hv, hw]

theorem colorR3_f (f : Nat → Nat) (uD vD wD uE vE wE : Nat)
    (col : Nat → Int) (hf : Function.Injective f) {a : Nat}
    (hu : f a ≠ uE) (hv : f a ≠ vE) (hw : f a ≠ wE) :
    colorR3 f uD vD wD uE vE wE col (f a) = col a := by
  rw [colorR3_of_ne f uD vD wD uE vE wE col hu hv hw,
    Function.leftInverse_invFun hf]

/-! ## Internals vs external legs -/

theorem r3_P_extOver_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    P.extOverArc u ≠ u ∧ P.extOverArc u ≠ v ∧ P.extOverArc u ≠ w := by
  obtain ⟨_, _, _, portsP, _, _, _, _, _, Po, _, _, _, _, Pnv, Pu, _, _⟩ := h
  exact ⟨Crossing.extOverArc_ne_self Po portsP.2.1,
    ne_of_mem_not_mem (Crossing.extOverArc_mem P u) Pnv,
    Crossing.isOver_ne_isUnder (Crossing.extOverArc_isOver Po) Pu portsP⟩

theorem r3_P_otherUnder_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    P.otherUnderArc w ≠ u ∧ P.otherUnderArc w ≠ v ∧ P.otherUnderArc w ≠ w := by
  obtain ⟨_, _, _, portsP, _, _, _, _, _, Po, _, _, _, _, Pnv, Pu, _, _⟩ := h
  exact ⟨(Crossing.isOver_ne_isUnder Po (Crossing.otherUnderArc_isUnder P w) portsP).symm,
    ne_of_mem_not_mem (Crossing.otherUnderArc_mem P w) Pnv,
    Crossing.otherUnderArc_ne_self Pu portsP.2.2.2.2.1⟩

theorem r3_Q_extOver_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    Q.extOverArc u ≠ u ∧ Q.extOverArc u ≠ v ∧ Q.extOverArc u ≠ w := by
  obtain ⟨_, _, _, _, portsQ, _, _, _, _, _, Qo, _, Qu, _, _, _, _, Qnw⟩ := h
  exact ⟨Crossing.extOverArc_ne_self Qo portsQ.2.1,
    Crossing.isOver_ne_isUnder (Crossing.extOverArc_isOver Qo) Qu portsQ,
    ne_of_mem_not_mem (Crossing.extOverArc_mem Q u) Qnw⟩

theorem r3_Q_otherUnder_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    Q.otherUnderArc v ≠ u ∧ Q.otherUnderArc v ≠ v ∧ Q.otherUnderArc v ≠ w := by
  obtain ⟨_, _, _, _, portsQ, _, _, _, _, _, Qo, _, Qu, _, _, _, _, Qnw⟩ := h
  exact ⟨(Crossing.isOver_ne_isUnder Qo (Crossing.otherUnderArc_isUnder Q v) portsQ).symm,
    Crossing.otherUnderArc_ne_self Qu portsQ.2.2.2.2.1,
    ne_of_mem_not_mem (Crossing.otherUnderArc_mem Q v) Qnw⟩

theorem r3_R_extOver_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    R.extOverArc v ≠ u ∧ R.extOverArc v ≠ v ∧ R.extOverArc v ≠ w := by
  obtain ⟨_, _, _, _, _, portsR, _, _, _, _, _, Rnu, _, Ro, _, _, Ru, _⟩ := h
  exact ⟨ne_of_mem_not_mem (Crossing.extOverArc_mem R v) Rnu,
    Crossing.extOverArc_ne_self Ro portsR.2.1,
    Crossing.isOver_ne_isUnder (Crossing.extOverArc_isOver Ro) Ru portsR⟩

theorem r3_R_otherUnder_not_internal {P Q R : Crossing} {u v w : Nat}
    (h : IsR3OverSlide P Q R u v w) :
    R.otherUnderArc w ≠ u ∧ R.otherUnderArc w ≠ v ∧ R.otherUnderArc w ≠ w := by
  obtain ⟨_, _, _, _, _, portsR, _, _, _, _, _, Rnu, _, Ro, _, _, Ru, _⟩ := h
  exact ⟨ne_of_mem_not_mem (Crossing.otherUnderArc_mem R w) Rnu,
    (Crossing.isOver_ne_isUnder Ro (Crossing.otherUnderArc_isUnder R w) portsR).symm,
    Crossing.otherUnderArc_ne_self Ru portsR.2.2.2.2.1⟩

/-! ## Triple coloring -/

theorem colorR3_ColoringRule_P (f : Nat → Nat)
    {PD QD RD PE QE RE : Crossing} {uD vD wD uE vE wE : Nat}
    (col : Nat → Int) (hf : Function.Injective f)
    (hD : IsR3OverSlide PD QD RD uD vD wD)
    (hE : IsR3OverSlide PE QE RE uE vE wE)
    (hm : r3ExtMatch f PD QD RD PE QE RE uD vD wD uE vE wE)
    (hPD : ColoringRule PD col) :
    ColoringRule PE (colorR3 f uD vD wD uE vE wE col) := by
  have hE0 := hE
  have hD0 := hD
  obtain ⟨_, _, _, portsPD, _, _, _, _, hwuD, PoD, _, _, _, _, _, PuD, _, _⟩ := hD
  obtain ⟨_, _, _, portsPE, _, _, huvE, hvwE, hwuE, PoE, _, _, _, _, _, PuE, _, _⟩ :=
    hE
  let col' := colorR3 f uD vD wD uE vE wE col
  have hPext := r3_P_extOver_not_internal hE0
  have hPund := r3_P_otherUnder_not_internal hE0
  have hcu : col' uE = col uD := colorR3_uE f uD vD wD uE vE wE col
  have hcw : col' wE = col wD :=
    colorR3_wE f uD vD wD uE vE wE col hwuE.symm hvwE
  have hcExt : col' (PE.extOverArc uE) = col (PD.extOverArc uD) := by
    have heq : PE.extOverArc uE = f (PD.extOverArc uD) := hm.1
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hPext.1) (heq ▸ hPext.2.1) (heq ▸ hPext.2.2)
  have hcUnd : col' (PE.otherUnderArc wE) = col (PD.otherUnderArc wD) := by
    have heq : PE.otherUnderArc wE = f (PD.otherUnderArc wD) := hm.2.2.1
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hPund.1) (heq ▸ hPund.2.1) (heq ▸ hPund.2.2)
  have hoverD := Crossing.extOverArc_color hPD PoD
  have hsumD :=
    Crossing.otherUnderArc_sum_over hPD PoD PuD portsPD.2.2.2.2.1
  refine ColoringRule_of_slide PE col' uE wE PoE PuE portsPE ?_ ?_
  · exact hcExt.trans (hoverD.trans hcu.symm)
  · rw [hcw, hcUnd, hcu]; exact hsumD

theorem colorR3_ColoringRule_Q (f : Nat → Nat)
    {PD QD RD PE QE RE : Crossing} {uD vD wD uE vE wE : Nat}
    (col : Nat → Int) (hf : Function.Injective f)
    (hD : IsR3OverSlide PD QD RD uD vD wD)
    (hE : IsR3OverSlide PE QE RE uE vE wE)
    (hm : r3ExtMatch f PD QD RD PE QE RE uD vD wD uE vE wE)
    (hQD : ColoringRule QD col) :
    ColoringRule QE (colorR3 f uD vD wD uE vE wE col) := by
  have hE0 := hE
  have hD0 := hD
  obtain ⟨_, _, _, _, portsQD, _, huvD, _, _, _, QoD, _, QuD, _, _, _, _, _⟩ := hD
  obtain ⟨_, _, _, _, portsQE, _, huvE, hvwE, hwuE, _, QoE, _, QuE, _, _, _, _, _⟩ :=
    hE
  let col' := colorR3 f uD vD wD uE vE wE col
  have hQext := r3_Q_extOver_not_internal hE0
  have hQund := r3_Q_otherUnder_not_internal hE0
  have hcu : col' uE = col uD := colorR3_uE f uD vD wD uE vE wE col
  have hcv : col' vE = col vD := colorR3_vE f uD vD wD uE vE wE col huvE
  have hcExt : col' (QE.extOverArc uE) = col (QD.extOverArc uD) := by
    have heq : QE.extOverArc uE = f (QD.extOverArc uD) := hm.2.1
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hQext.1) (heq ▸ hQext.2.1) (heq ▸ hQext.2.2)
  have hcUnd : col' (QE.otherUnderArc vE) = col (QD.otherUnderArc vD) := by
    have heq : QE.otherUnderArc vE = f (QD.otherUnderArc vD) := hm.2.2.2.1
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hQund.1) (heq ▸ hQund.2.1) (heq ▸ hQund.2.2)
  have hoverD := Crossing.extOverArc_color hQD QoD
  have hsumD :=
    Crossing.otherUnderArc_sum_over hQD QoD QuD portsQD.2.2.2.2.1
  refine ColoringRule_of_slide QE col' uE vE QoE QuE portsQE ?_ ?_
  · exact hcExt.trans (hoverD.trans hcu.symm)
  · rw [hcv, hcUnd, hcu]; exact hsumD

theorem colorR3_ColoringRule_R (f : Nat → Nat)
    {PD QD RD PE QE RE : Crossing} {uD vD wD uE vE wE : Nat}
    (col : Nat → Int) (hf : Function.Injective f)
    (hD : IsR3OverSlide PD QD RD uD vD wD)
    (hE : IsR3OverSlide PE QE RE uE vE wE)
    (hm : r3ExtMatch f PD QD RD PE QE RE uD vD wD uE vE wE)
    (hRD : ColoringRule RD col) :
    ColoringRule RE (colorR3 f uD vD wD uE vE wE col) := by
  have hE0 := hE
  have hD0 := hD
  obtain ⟨_, _, _, _, _, portsRD, _, _, _, _, _, _, _, RoD, _, _, RuD, _⟩ := hD
  obtain ⟨_, _, _, _, _, portsRE, huvE, hvwE, hwuE, _, _, _, _, RoE, _, _, RuE, _⟩ :=
    hE
  let col' := colorR3 f uD vD wD uE vE wE col
  have hRext := r3_R_extOver_not_internal hE0
  have hRund := r3_R_otherUnder_not_internal hE0
  have hcv : col' vE = col vD := colorR3_vE f uD vD wD uE vE wE col huvE
  have hcw : col' wE = col wD :=
    colorR3_wE f uD vD wD uE vE wE col hwuE.symm hvwE
  have hcExt : col' (RE.extOverArc vE) = col (RD.extOverArc vD) := by
    have heq : RE.extOverArc vE = f (RD.extOverArc vD) := hm.2.2.2.2.1
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hRext.1) (heq ▸ hRext.2.1) (heq ▸ hRext.2.2)
  have hcUnd : col' (RE.otherUnderArc wE) = col (RD.otherUnderArc wD) := by
    have heq : RE.otherUnderArc wE = f (RD.otherUnderArc wD) := hm.2.2.2.2.2
    rw [heq]
    exact colorR3_f f uD vD wD uE vE wE col hf
      (heq ▸ hRund.1) (heq ▸ hRund.2.1) (heq ▸ hRund.2.2)
  have hoverD := Crossing.extOverArc_color hRD RoD
  have hsumD :=
    Crossing.otherUnderArc_sum_over hRD RoD RuD portsRD.2.2.2.2.1
  refine ColoringRule_of_slide RE col' vE wE RoE RuE portsRE ?_ ?_
  · exact hcExt.trans (hoverD.trans hcv.symm)
  · rw [hcw, hcUnd, hcv]; exact hsumD

/-! ## Rest of the diagram -/

theorem sameUpToRotation_memArc {C D : Crossing}
    (h : C.sameUpToRotation D) {a : Nat} : C.memArc a ↔ D.memArc a := by
  rcases h with rfl | hrot | hrev | hrr
  · exact Iff.rfl
  · have hD : D = C.rotate180 := by
      rw [hrot, Crossing.rotate180_involutive]
    subst hD
    simp [Crossing.memArc, Crossing.rotate180]
    tauto
  · have hD : D = C.reverseUnders := by
      rw [hrev, Crossing.reverseUnders_involutive]
    subst hD
    simp [Crossing.memArc, Crossing.reverseUnders]
    tauto
  · have hD : D = C.rotate180.reverseUnders := by
      rw [hrr, Crossing.rotate180_involutive, Crossing.reverseUnders_involutive]
    subst hD
    simp [Crossing.memArc, Crossing.rotate180, Crossing.reverseUnders]
    tauto

theorem ColoringRule_colorR3_rest (f : Nat → Nat)
    (uD vD wD uE vE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f) {X : Crossing}
    (hX : ColoringRule X col)
    {Y : Crossing} (hXY : (X.rename f).sameUpToRotation Y)
    (hY : ¬ Y.memArc uE ∧ ¬ Y.memArc vE ∧ ¬ Y.memArc wE) :
    ColoringRule Y (colorR3 f uD vD wD uE vE wE col) := by
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
      (colorR3 f uD vD wD uE vE wE col) := by
    rw [ColoringRule_rename]
    refine ColoringRule_congr
      (colorR3_f f uD vD wD uE vE wE col hf
        (ne_of_mem_not_mem hy0 hY.1) (ne_of_mem_not_mem hy0 hY.2.1)
        (ne_of_mem_not_mem hy0 hY.2.2))
      (colorR3_f f uD vD wD uE vE wE col hf
        (ne_of_mem_not_mem hy1 hY.1) (ne_of_mem_not_mem hy1 hY.2.1)
        (ne_of_mem_not_mem hy1 hY.2.2))
      (colorR3_f f uD vD wD uE vE wE col hf
        (ne_of_mem_not_mem hy2 hY.1) (ne_of_mem_not_mem hy2 hY.2.1)
        (ne_of_mem_not_mem hy2 hY.2.2))
      (colorR3_f f uD vD wD uE vE wE col hf
        (ne_of_mem_not_mem hy3 hY.1) (ne_of_mem_not_mem hy3 hY.2.1)
        (ne_of_mem_not_mem hy3 hY.2.2))
      hX
  exact ColoringRule_sameUpToRotation (colorR3 f uD vD wD uE vE wE col) hXY
    hrename

theorem pairRel_colorR3_rest (f : Nat → Nat)
    (uD vD wD uE vE wE : Nat) (col : Nat → Int)
    (hf : Function.Injective f)
    {restD restE : List Crossing}
    (hpair : pairRel Crossing.sameUpToRotation
      (restD.map (Crossing.rename f)) restE)
    (hrestD : ∀ C ∈ restD, ColoringRule C col)
    (hrestE : ∀ C ∈ restE, ¬ C.memArc uE ∧ ¬ C.memArc vE ∧ ¬ C.memArc wE) :
    ∀ C ∈ restE, ColoringRule C (colorR3 f uD vD wD uE vE wE col) := by
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
        exact ColoringRule_colorR3_rest f uD vD wD uE vE wE col hf
          (hrestD X (by simp)) hXY (hrestE Y (by simp))
      | inr hZ =>
        exact ih hrest (fun W hW => hrestD W (by simp [hW]))
          (fun W hW => hrestE W (by simp [hW])) Z hZ

/-! ## Main theorem -/

theorem coloring_IsReidemeisterIIILocal (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIIILocal D E) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨f, PD, QD, RD, PE, QE, RE, uD, vD, wD, uE, vE, wE, restD, restE,
    hf, hD, hE, _sP, _sQ, _sR, hm, hNW, hNE, hSE, hSW,
    huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
    hrestE, _huDNW, _huDNE, _huDSE, _huDSW, _hvDNW, _hvDNE, _hvDSE, _hvDSW,
    _hwDNW, _hwDNE, _hwDSE, _hwDSW, _hrestD, hpermD, hpermE, hpair⟩ := h
  let col' := colorR3 f uD vD wD uE vE wE col
  have hPD : ColoringRule PD col := hc PD ((List.Perm.mem_iff hpermD).2 (by simp))
  have hQD : ColoringRule QD col := hc QD ((List.Perm.mem_iff hpermD).2 (by simp))
  have hRD : ColoringRule RD col := hc RD ((List.Perm.mem_iff hpermD).2 (by simp))
  have hrestD : ∀ C ∈ restD, ColoringRule C col :=
    fun C hC => hc C ((List.Perm.mem_iff hpermD).2 (by simp [hC]))
  have hPE := colorR3_ColoringRule_P f col hf hD hE hm hPD
  have hQE := colorR3_ColoringRule_Q f col hf hD hE hm hQD
  have hRE := colorR3_ColoringRule_R f col hf hD hE hm hRD
  have hrest := pairRel_colorR3_rest f uD vD wD uE vE wE col hf hpair hrestD
    hrestE
  refine ⟨col', ?_, ?_⟩
  · intro C hC
    have : C = PE ∨ C = QE ∨ C = RE ∨ C ∈ restE := by
      have := (List.Perm.mem_iff hpermE).1 hC
      simp [List.mem_cons] at this
      tauto
    rcases this with hC' | hC' | hC' | hC'
    · subst hC'; exact hPE
    · subst hC'; exact hQE
    · subst hC'; exact hRE
    · exact hrest C hC'
  · have hbnd (a : Nat) (ha_u : f a ≠ uE) (ha_v : f a ≠ vE) (ha_w : f a ≠ wE) :
        col' (f a) = col a :=
      colorR3_f f uD vD wD uE vE wE col hf ha_u ha_v ha_w
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hNW]; exact hbnd D.NW (hNW ▸ huNW.symm) (hNW ▸ hvNW.symm) (hNW ▸ hwNW.symm)
    · rw [hNE]; exact hbnd D.NE (hNE ▸ huNE.symm) (hNE ▸ hvNE.symm) (hNE ▸ hwNE.symm)
    · rw [hSE]; exact hbnd D.SE (hSE ▸ huSE.symm) (hSE ▸ hvSE.symm) (hSE ▸ hwSE.symm)
    · rw [hSW]; exact hbnd D.SW (hSW ▸ huSW.symm) (hSW ▸ hvSW.symm) (hSW ▸ hwSW.symm)

/-! ## Reverse local R3

Triangle internals are not `f`-images, so reverse uses `planarInvFun` on
appearing arcs of `D` for the six external legs and the endpoints. Rest
and boundary constraints are two-sided on `IsReidemeisterIIILocal`, so the
reverse witness is again a local over-slide.
-/

theorem Crossing.extOverArc_le {C : Crossing} {u M : Nat}
    (h0 : C.a0 ≤ M) (h2 : C.a2 ≤ M) : C.extOverArc u ≤ M := by
  unfold Crossing.extOverArc
  split_ifs <;> assumption

theorem Crossing.otherUnderArc_le {C : Crossing} {w M : Nat}
    (h1 : C.a1 ≤ M) (h3 : C.a3 ≤ M) : C.otherUnderArc w ≤ M := by
  unfold Crossing.otherUnderArc
  split_ifs <;> assumption

theorem r3ExtMatch_planarInvFun {f : Nat → Nat} {M : Nat}
    {PD QD RD PE QE RE : Crossing} {uD vD wD uE vE wE : Nat}
    (hf : Function.Injective f)
    (hP0 : PD.a0 ≤ M) (hP1 : PD.a1 ≤ M) (hP2 : PD.a2 ≤ M) (hP3 : PD.a3 ≤ M)
    (hQ0 : QD.a0 ≤ M) (hQ1 : QD.a1 ≤ M) (hQ2 : QD.a2 ≤ M) (hQ3 : QD.a3 ≤ M)
    (hR0 : RD.a0 ≤ M) (hR1 : RD.a1 ≤ M) (hR2 : RD.a2 ≤ M) (hR3 : RD.a3 ≤ M)
    (hm : r3ExtMatch f PD QD RD PE QE RE uD vD wD uE vE wE) :
    r3ExtMatch (planarInvFun f M) PE QE RE PD QD RD uE vE wE uD vD wD := by
  have hPext := Crossing.extOverArc_le (u := uD) hP0 hP2
  have hQext := Crossing.extOverArc_le (u := uD) hQ0 hQ2
  have hRext := Crossing.extOverArc_le (u := vD) hR0 hR2
  have hPund := Crossing.otherUnderArc_le (w := wD) hP1 hP3
  have hQund := Crossing.otherUnderArc_le (w := vD) hQ1 hQ3
  have hRund := Crossing.otherUnderArc_le (w := wD) hR1 hR3
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm
  exact ⟨by simp [h1, planarInvFun_of_le f hf M hPext],
    by simp [h2, planarInvFun_of_le f hf M hQext],
    by simp [h3, planarInvFun_of_le f hf M hPund],
    by simp [h4, planarInvFun_of_le f hf M hQund],
    by simp [h5, planarInvFun_of_le f hf M hRext],
    by simp [h6, planarInvFun_of_le f hf M hRund]⟩

theorem IsReidemeisterIIILocal.symm {D E : TangleDiagram}
    (h : IsReidemeisterIIILocal D E) : IsReidemeisterIIILocal E D := by
  obtain ⟨f, PD, QD, RD, PE, QE, RE, uD, vD, wD, uE, vE, wE, restD, restE,
    hf, hD, hE, sP, sQ, sR, hm, hNW, hNE, hSE, hSW,
    huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
    hrestE, huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
    hwDNW, hwDNE, hwDSE, hwDSW, hrestD, hpermD, hpermE, hpair⟩ := h
  let g := planarInvFun f D.maxArc
  have hg : Function.Injective g := planarInvFun_injective f D.maxArc
  have hid {a : Nat} (ha : a ≤ D.maxArc) : g (f a) = a :=
    planarInvFun_of_le f hf D.maxArc ha
  have memD_of {C : Crossing}
      (hC : C = PD ∨ C = QD ∨ C = RD ∨ C ∈ restD) : C ∈ D.crossings :=
    (List.Perm.mem_iff hpermD).2 (by
      simp [List.mem_cons] at hC ⊢
      tauto)
  have hrename (C : Crossing) (hC : C ∈ D.crossings) :
      C.rename (g ∘ f) = C := by
    have hp := arc_le_maxArc_of_mem D hC
    cases C
    simp [Crossing.rename, Function.comp, hid hp.1, hid hp.2.1, hid hp.2.2.1,
      hid hp.2.2.2]
  have hpP := arc_le_maxArc_of_mem D (memD_of (Or.inl rfl))
  have hpQ := arc_le_maxArc_of_mem D (memD_of (Or.inr (Or.inl rfl)))
  have hpR := arc_le_maxArc_of_mem D (memD_of (Or.inr (Or.inr (Or.inl rfl))))
  have hm' :=
    r3ExtMatch_planarInvFun hf hpP.1 hpP.2.1 hpP.2.2.1 hpP.2.2.2
      hpQ.1 hpQ.2.1 hpQ.2.2.1 hpQ.2.2.2
      hpR.1 hpR.2.1 hpR.2.2.1 hpR.2.2.2 hm
  have hmap_rest : restD.map (Crossing.rename (g ∘ f)) = restD :=
    List.map_eq_of_id fun C hC =>
      hrename C (memD_of (Or.inr (Or.inr (Or.inr hC))))
  have hpair' :
      pairRel Crossing.sameUpToRotation (restE.map (Crossing.rename g)) restD := by
    have h1 :=
      pairRel_map (Crossing.rename g)
        (fun _ _ => Crossing.sameUpToRotation_rename g) hpair
    have hmap :
        (restD.map (Crossing.rename f)).map (Crossing.rename g) = restD := by
      rw [List.map_map]
      exact hmap_rest
    rw [hmap] at h1
    exact pairRel_symm (fun _ _ => Crossing.sameUpToRotation.symm) h1
  refine ⟨g, PE, QE, RE, PD, QD, RD, uE, vE, wE, uD, vD, wD, restE, restD,
    hg, hE, hD, sP.symm, sQ.symm, sR.symm, hm', ?_, ?_, ?_, ?_,
    huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
    hwDNW, hwDNE, hwDSE, hwDSW, hrestD,
    huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
    hrestE, hpermE, hpermD, hpair'⟩
  · simp [g, hNW, hid (maxArc_ge_NW D)]
  · simp [g, hNE, hid (maxArc_ge_NE D)]
  · simp [g, hSE, hid (maxArc_ge_SE D)]
  · simp [g, hSW, hid (maxArc_ge_SW D)]

/-- Reverse coloring along a local R3 over-slide: rest and boundary
    constraints are two-sided, and `planarInvFun` inverts `f` on appearing
    arcs of `D`. -/
theorem coloring_IsReidemeisterIIILocal_rev (D E : TangleDiagram)
    (col : Nat → Int) (h : IsReidemeisterIIILocal D E)
    (hc : E.IsColored col) :
    ∃ col', D.IsColored col' ∧ SameEndpointColors E D col col' :=
  coloring_IsReidemeisterIIILocal E D col h.symm hc

/-! ## Indexed R3 is local R3 -/

theorem dropIdxs_shift {α} (i j k n : Nat) (xs : List α) :
    dropIdxs (i + 1) (j + 1) (k + 1) (n + 1) xs = dropIdxs i j k n xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [dropIdxs]
    by_cases h : n = i ∨ n = j ∨ n = k
    · have h' : n + 1 = i + 1 ∨ n + 1 = j + 1 ∨ n + 1 = k + 1 := by omega
      simp [h, h', ih]
    · have h' : ¬ (n + 1 = i + 1 ∨ n + 1 = j + 1 ∨ n + 1 = k + 1) := by omega
      simp [h, h', ih]

theorem dropIdxs_id_of_lt {α} (i j k n : Nat) (xs : List α)
    (hi : i < n) (hj : j < n) (hk : k < n) :
    dropIdxs i j k n xs = xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    have hne : ¬ (n = i ∨ n = j ∨ n = k) := by omega
    simp [dropIdxs, hne, ih (n + 1) (by omega) (by omega) (by omega)]

theorem dropIdxs_irrel_lt {α} (i j k n : Nat) (xs : List α) (hi : i < n) :
    dropIdxs i j k n xs = dropIdxs j k j n xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [dropIdxs]
    by_cases h : n = j ∨ n = k
    · have h₁ : n = i ∨ n = j ∨ n = k := by tauto
      have h₂ : n = j ∨ n = k ∨ n = j := by tauto
      rw [if_pos h₁, if_pos h₂, ih (n + 1) (Nat.lt_succ_of_lt hi)]
    · have h₁ : ¬ (n = i ∨ n = j ∨ n = k) := by
        have : n ≠ i := Nat.ne_of_gt hi
        tauto
      have h₂ : ¬ (n = j ∨ n = k ∨ n = j) := by tauto
      rw [if_neg h₁, if_neg h₂, ih (n + 1) (Nat.lt_succ_of_lt hi)]

theorem dropIdxs_eraseIdx {α} (i : Nat) (xs : List α) :
    dropIdxs i i i 0 xs = xs.eraseIdx i := by
  induction xs generalizing i with
  | nil => simp [dropIdxs]
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [dropIdxs]
      exact dropIdxs_id_of_lt 0 0 0 1 xs (by omega) (by omega) (by omega)
    | succ i =>
      simp only [dropIdxs, List.eraseIdx_cons_succ]
      have hne : ¬ (0 = i + 1 ∨ 0 = i + 1 ∨ 0 = i + 1) := by omega
      rw [if_neg hne, dropIdxs_shift i i i 0 xs, ih]

theorem dropIdxs_comm_swap_ij {α} (i j k n : Nat) (xs : List α) :
    dropIdxs i j k n xs = dropIdxs j i k n xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [dropIdxs]
    by_cases h : n = i ∨ n = j ∨ n = k
    · have h' : n = j ∨ n = i ∨ n = k := by tauto
      rw [if_pos h, if_pos h', ih]
    · have h' : ¬ (n = j ∨ n = i ∨ n = k) := by tauto
      rw [if_neg h, if_neg h']
      simp [ih]

theorem dropIdxs_comm_swap_jk {α} (i j k n : Nat) (xs : List α) :
    dropIdxs i j k n xs = dropIdxs i k j n xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    simp only [dropIdxs]
    by_cases h : n = i ∨ n = j ∨ n = k
    · have h' : n = i ∨ n = k ∨ n = j := by tauto
      rw [if_pos h, if_pos h', ih]
    · have h' : ¬ (n = i ∨ n = k ∨ n = j) := by tauto
      rw [if_neg h, if_neg h']
      simp [ih]

theorem dropIdxs_eraseIdx_two {α} (a b : Nat) (xs : List α)
    (hab : a < b) (hb : b < xs.length) :
    dropIdxs a b a 0 xs = (xs.eraseIdx b).eraseIdx a := by
  induction xs generalizing a b with
  | nil => cases hb
  | cons x xs ih =>
    cases a with
    | zero =>
      cases b with
      | zero => cases hab
      | succ b =>
        simp only [dropIdxs, true_or, ite_true]
        rw [dropIdxs_irrel_lt 0 (b + 1) 0 1 xs (by omega)]
        rw [dropIdxs_comm_swap_ij]
        rw [dropIdxs_irrel_lt 0 (b + 1) (b + 1) 1 xs (by omega)]
        rw [dropIdxs_shift b b b 0 xs, dropIdxs_eraseIdx]
        simp [List.eraseIdx]
    | succ a =>
      cases b with
      | zero => cases hab
      | succ b =>
        have hab' : a < b := by omega
        have hb' : b < xs.length := by simpa using hb
        simp only [dropIdxs]
        have hne : ¬ (0 = a + 1 ∨ 0 = b + 1 ∨ 0 = a + 1) := by omega
        rw [if_neg hne, dropIdxs_shift a b a 0 xs, ih a b hab' hb']
        simp [List.eraseIdx]

theorem dropIdxs_eraseIdx_three {α} (a b c : Nat) (xs : List α)
    (hab : a < b) (hbc : b < c) (hc : c < xs.length) :
    dropIdxs a b c 0 xs = ((xs.eraseIdx c).eraseIdx b).eraseIdx a := by
  induction xs generalizing a b c with
  | nil => cases hc
  | cons x xs ih =>
    cases a with
    | zero =>
      cases b with
      | zero => cases hab
      | succ b =>
        cases c with
        | zero => cases hbc
        | succ c =>
          have hbc' : b < c := by omega
          have hc' : c < xs.length := by simpa using hc
          simp only [dropIdxs, true_or, ite_true]
          rw [dropIdxs_irrel_lt 0 (b + 1) (c + 1) 1 xs (by omega)]
          rw [dropIdxs_shift b c b 0 xs, dropIdxs_eraseIdx_two b c xs hbc' hc']
          simp [List.eraseIdx]
    | succ a =>
      cases b with
      | zero => cases hab
      | succ b =>
        cases c with
        | zero => cases hbc
        | succ c =>
          have hab' : a < b := by omega
          have hbc' : b < c := by omega
          have hc' : c < xs.length := by simpa using hc
          simp only [dropIdxs]
          have hne : ¬ (0 = a + 1 ∨ 0 = b + 1 ∨ 0 = c + 1) := by omega
          rw [if_neg hne, dropIdxs_shift a b c 0 xs, ih a b c hab' hbc' hc']
          simp [List.eraseIdx]

theorem dropIdxs_of_iff {α} (i j k i' j' k' n : Nat) (xs : List α)
    (h : ∀ x, (x = i ∨ x = j ∨ x = k) ↔ (x = i' ∨ x = j' ∨ x = k')) :
    dropIdxs i j k n xs = dropIdxs i' j' k' n xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons _ xs ih =>
    simp only [dropIdxs]
    have hiff : (n = i ∨ n = j ∨ n = k) ↔ (n = i' ∨ n = j' ∨ n = k') := h n
    by_cases hn : n = i ∨ n = j ∨ n = k
    · rw [if_pos hn, if_pos (hiff.mp hn), ih]
    · rw [if_neg hn, if_neg (mt hiff.mpr hn), ih]

theorem getElem_eraseIdx_of_lt {α} (xs : List α) {j k : Nat}
    (hjk : j < k) (hk : k < xs.length) :
    (xs.eraseIdx k)[j]'(by rw [List.length_eraseIdx_of_lt hk]; omega) =
      xs[j]'(Nat.lt_trans hjk hk) := by
  induction xs generalizing j k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => cases hjk
    | succ k =>
      cases j with
      | zero => simp [List.eraseIdx]
      | succ j =>
        have hjk' : j < k := by omega
        have hk' : k < xs.length := by simpa using hk
        simpa [List.eraseIdx] using ih hjk' hk'

theorem perm_swap_heads {α} (a b : α) (l : List α) :
    (a :: b :: l).Perm (b :: a :: l) :=
  List.Perm.swap b a l

theorem perm_triple {α} (a b c : α) (l : List α) :
    (a :: b :: c :: l).Perm (b :: c :: a :: l) :=
  (perm_swap_heads a b (c :: l)).trans (List.Perm.cons b (perm_swap_heads a c l))

theorem perm_cons3_dropIdxs_sorted {α} (xs : List α) (i j k : Nat)
    (hij : i < j) (hjk : j < k) (hk : k < xs.length) :
    xs.Perm (xs[i]'(Nat.lt_trans hij (Nat.lt_trans hjk hk)) ::
      xs[j]'(Nat.lt_trans hjk hk) :: xs[k] :: dropIdxs i j k 0 xs) := by
  have hi : i < xs.length := Nat.lt_trans hij (Nat.lt_trans hjk hk)
  have hj : j < xs.length := Nat.lt_trans hjk hk
  rw [dropIdxs_eraseIdx_three i j k xs hij hjk hk]
  have h₁ := (List.getElem_cons_eraseIdx_perm (l := xs) hk).symm
  have hlenk : (xs.eraseIdx k).length = xs.length - 1 := List.length_eraseIdx_of_lt hk
  have hj' : j < (xs.eraseIdx k).length := by rw [hlenk]; omega
  have h₂ := (List.getElem_cons_eraseIdx_perm (l := xs.eraseIdx k) hj').symm
  have hlenj : ((xs.eraseIdx k).eraseIdx j).length = (xs.eraseIdx k).length - 1 :=
    List.length_eraseIdx_of_lt hj'
  have hi' : i < ((xs.eraseIdx k).eraseIdx j).length := by rw [hlenj, hlenk]; omega
  have h₃ := (List.getElem_cons_eraseIdx_perm
    (l := (xs.eraseIdx k).eraseIdx j) hi').symm
  have heqj : (xs.eraseIdx k)[j] = xs[j] := getElem_eraseIdx_of_lt xs hjk hk
  have heqi₁ : ((xs.eraseIdx k).eraseIdx j)[i] = (xs.eraseIdx k)[i] :=
    getElem_eraseIdx_of_lt (xs.eraseIdx k) hij hj'
  have heqi₀ : (xs.eraseIdx k)[i] = xs[i] :=
    getElem_eraseIdx_of_lt xs (Nat.lt_trans hij hjk) hk
  let rest := ((xs.eraseIdx k).eraseIdx j).eraseIdx i
  have h₂' : (xs.eraseIdx k).Perm (xs[j] :: (xs.eraseIdx k).eraseIdx j) := by
    rw [heqj] at h₂; exact h₂
  have h₃' : ((xs.eraseIdx k).eraseIdx j).Perm (xs[i] :: rest) := by
    rw [heqi₁, heqi₀] at h₃; exact h₃
  have hperm : xs.Perm (xs[k] :: xs[j] :: xs[i] :: rest) :=
    h₁.trans <| List.Perm.cons _ <| h₂'.trans <| List.Perm.cons _ h₃'
  exact hperm.trans <|
    (perm_triple xs[k] xs[j] xs[i] rest).trans
      (perm_swap_heads xs[j] xs[i] (xs[k] :: rest))

theorem perm_cons3_dropIdxs {α} (xs : List α) (i j k : Nat)
    (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    xs.Perm (xs[i] :: xs[j] :: xs[k] :: dropIdxs i j k 0 xs) := by
  rcases lt_trichotomy i j with (hij' : i < j) | (rfl : i = j) | (hji : j < i)
  · rcases lt_trichotomy j k with (hjk' : j < k) | (rfl : j = k) | (hkj : k < j)
    · exact perm_cons3_dropIdxs_sorted xs i j k hij' hjk' hk
    · exact (hjk rfl).elim
    · rcases lt_trichotomy i k with (hik' : i < k) | (rfl : i = k) | (hki : k < i)
      · have h := perm_cons3_dropIdxs_sorted xs i k j hik' hkj hj
        rw [dropIdxs_comm_swap_jk] at h
        exact h.trans (List.Perm.cons xs[i] (perm_swap_heads xs[k] xs[j] (dropIdxs i j k 0 xs)))
      · exact (hik rfl).elim
      · have h := perm_cons3_dropIdxs_sorted xs k i j hki hij' hj
        have hd : dropIdxs k i j 0 xs = dropIdxs i j k 0 xs :=
          dropIdxs_of_iff k i j i j k 0 xs (fun x => by tauto)
        rw [hd] at h
        exact h.trans (perm_triple xs[k] xs[i] xs[j] (dropIdxs i j k 0 xs))
  · exact (hij rfl).elim
  · rcases lt_trichotomy i k with (hik' : i < k) | (rfl : i = k) | (hki : k < i)
    · have h := perm_cons3_dropIdxs_sorted xs j i k hji hik' hk
      rw [dropIdxs_comm_swap_ij] at h
      exact h.trans (perm_swap_heads xs[j] xs[i] (xs[k] :: dropIdxs i j k 0 xs))
    · exact (hik rfl).elim
    · rcases lt_trichotomy j k with (hjk' : j < k) | (rfl : j = k) | (hkj : k < j)
      · have h := perm_cons3_dropIdxs_sorted xs j k i hjk' hki hi
        have hd : dropIdxs j k i 0 xs = dropIdxs i j k 0 xs :=
          dropIdxs_of_iff j k i i j k 0 xs (fun x => by tauto)
        rw [hd] at h
        exact h.trans <|
          (perm_triple xs[j] xs[k] xs[i] (dropIdxs i j k 0 xs)).trans
            (perm_triple xs[k] xs[i] xs[j] (dropIdxs i j k 0 xs))
      · exact (hjk rfl).elim
      · have h := perm_cons3_dropIdxs_sorted xs k j i hkj hji hi
        have hd : dropIdxs k j i 0 xs = dropIdxs i j k 0 xs :=
          dropIdxs_of_iff k j i i j k 0 xs (fun x => by tauto)
        rw [hd] at h
        exact h.trans <|
          (perm_triple xs[k] xs[j] xs[i] (dropIdxs i j k 0 xs)).trans
            (perm_swap_heads xs[j] xs[i] (xs[k] :: dropIdxs i j k 0 xs))

theorem IsReidemeisterIII.toLocal {D E : TangleDiagram}
    (h : IsReidemeisterIII D E) : IsReidemeisterIIILocal D E := by
  obtain ⟨hlen, f, i, j, k, uD, vD, wD, uE, vE, wE, hf, hij, hjk, hik,
    hNW, hNE, hSE, hSW,
    huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
    hrestE, huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
    hwDNW, hwDNE, hwDSE, hwDSW, hrestD, hsP, hsQ, hsR, hslide, hex⟩ := h
  have iE : i.val < E.crossings.length := hlen ▸ i.isLt
  have jE : j.val < E.crossings.length := hlen ▸ j.isLt
  have kE : k.val < E.crossings.length := hlen ▸ k.isLt
  have hijN : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjkN : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hikN : i.val ≠ k.val := fun h => hik (Fin.ext h)
  have hpermD := perm_cons3_dropIdxs D.crossings i.val j.val k.val
    i.isLt j.isLt k.isLt hijN hjkN hikN
  have hpermE0 := perm_cons3_dropIdxs E.crossings i.val j.val k.val
    iE jE kE hijN hjkN hikN
  obtain ⟨_, _, _, _, Cs, hpair, hpermCs⟩ := hex
  have hrestCs : ∀ C ∈ Cs, ¬ C.memArc uE ∧ ¬ C.memArc vE ∧ ¬ C.memArc wE := by
    intro C hC
    exact hrestE C ((List.Perm.mem_iff hpermCs).1 hC)
  have hpermE : E.crossings.Perm
      (E.crossings[i.val] :: E.crossings[j.val] :: E.crossings[k.val] :: Cs) :=
    hpermE0.trans (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ hpermCs.symm)))
  rcases hslide with ⟨hD, hE, hm⟩ | ⟨hD, hE, hm⟩ | ⟨hD, hE, hm⟩
  · exact ⟨f, D.crossings[i], D.crossings[j], D.crossings[k],
      E.crossings[i.val], E.crossings[j.val], E.crossings[k.val],
      uD, vD, wD, uE, vE, wE,
      dropIdxs i.val j.val k.val 0 D.crossings, Cs,
      hf, hD, hE, hsP, hsQ, hsR, hm,
      hNW, hNE, hSE, hSW,
      huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
      hrestCs, huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
      hwDNW, hwDNE, hwDSE, hwDSW, hrestD, hpermD, hpermE, hpair⟩
  · have hpermD' : D.crossings.Perm
        (D.crossings[j] :: D.crossings[k] :: D.crossings[i] ::
          dropIdxs i.val j.val k.val 0 D.crossings) :=
      hpermD.trans
        (perm_triple D.crossings[i] D.crossings[j] D.crossings[k]
          (dropIdxs i.val j.val k.val 0 D.crossings))
    have hpermE' : E.crossings.Perm
        (E.crossings[j.val] :: E.crossings[k.val] :: E.crossings[i.val] :: Cs) :=
      hpermE.trans
        (perm_triple E.crossings[i.val] E.crossings[j.val] E.crossings[k.val] Cs)
    exact ⟨f, D.crossings[j], D.crossings[k], D.crossings[i],
      E.crossings[j.val], E.crossings[k.val], E.crossings[i.val],
      uD, vD, wD, uE, vE, wE,
      dropIdxs i.val j.val k.val 0 D.crossings, Cs,
      hf, hD, hE, hsQ, hsR, hsP, hm,
      hNW, hNE, hSE, hSW,
      huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
      hrestCs, huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
      hwDNW, hwDNE, hwDSE, hwDSW, hrestD, hpermD', hpermE', hpair⟩
  · have hpermD' : D.crossings.Perm
        (D.crossings[k] :: D.crossings[i] :: D.crossings[j] ::
          dropIdxs i.val j.val k.val 0 D.crossings) :=
      hpermD.trans <|
        (perm_triple D.crossings[i] D.crossings[j] D.crossings[k]
          (dropIdxs i.val j.val k.val 0 D.crossings)).trans
        (perm_triple D.crossings[j] D.crossings[k] D.crossings[i]
          (dropIdxs i.val j.val k.val 0 D.crossings))
    have hpermE' : E.crossings.Perm
        (E.crossings[k.val] :: E.crossings[i.val] :: E.crossings[j.val] :: Cs) :=
      hpermE.trans <|
        (perm_triple E.crossings[i.val] E.crossings[j.val] E.crossings[k.val] Cs).trans
        (perm_triple E.crossings[j.val] E.crossings[k.val] E.crossings[i.val] Cs)
    exact ⟨f, D.crossings[k], D.crossings[i], D.crossings[j],
      E.crossings[k.val], E.crossings[i.val], E.crossings[j.val],
      uD, vD, wD, uE, vE, wE,
      dropIdxs i.val j.val k.val 0 D.crossings, Cs,
      hf, hD, hE, hsR, hsP, hsQ, hm,
      hNW, hNE, hSE, hSW,
      huNW, huNE, huSE, huSW, hvNW, hvNE, hvSE, hvSW, hwNW, hwNE, hwSE, hwSW,
      hrestCs, huDNW, huDNE, huDSE, huDSW, hvDNW, hvDNE, hvDSE, hvDSW,
      hwDNW, hwDNE, hwDSE, hwDSW, hrestD, hpermD', hpermE', hpair⟩

/-- Indexed Reidemeister III has coloring transport, via the local model. -/
theorem coloring_IsReidemeisterIII (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIII D E) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' :=
  coloring_IsReidemeisterIIILocal D E col h.toLocal hc

end RationalTangles
