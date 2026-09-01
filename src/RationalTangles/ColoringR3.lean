/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.ColoringInvariance

/-!
# Coloring invariance under a local Reidemeister III over-slide

`IsReidemeisterIIILocal` replaces a triangular triple by another over-slide
triple with matching external legs, identifying the rest of the diagram by
permutation (no `dropIdxs`). Recoloring keeps the six external-leg colors
and copies the three internal colors onto the new internal arcs.
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
    hrestE, hpermD, hpermE, hpair⟩ := h
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

end RationalTangles
