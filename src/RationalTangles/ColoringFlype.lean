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

/-! ## Reverse local flype

The distinguished legs of a local flype are in the image of `f`
(`uE = f uD`, `wE = f wD`), so the rename is two-sided: `planarInvFun`
inverts `f` on appearing arcs of `D`, the 180° box reverses because
`rotate180` is an involution, and rest/`t` disjointness pulls back along
`f`. Local R3 internals are not `f`-images either; reverse there uses the
two-sided rest/boundary fields of `IsReidemeisterIIILocal` together with
`planarInvFun` on the external legs.
-/

theorem pairRel_flip {α} {R S : α → α → Prop}
    (hRS : ∀ x y, R x y → S y x) :
    ∀ {xs ys : List α}, pairRel R xs ys → pairRel S ys xs
  | [], [] => id
  | _ :: _, [] => by intro h; cases h
  | [], _ :: _ => by intro h; cases h
  | x :: xs, y :: ys => by
    intro h
    exact ⟨hRS x y h.1, pairRel_flip hRS h.2⟩

theorem pairRel_exists_of_mem {α} {R : α → α → Prop} :
    ∀ {xs ys : List α}, pairRel R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | [], [], h, x, hx => by cases hx
  | _ :: _, [], h, x, hx => by cases h
  | [], _ :: _, h, x, hx => by cases h
  | x0 :: xs, y0 :: ys, h, x, hx => by
    obtain ⟨h0, hrest⟩ := h
    rw [List.mem_cons] at hx
    cases hx with
    | inl heq => exact ⟨y0, List.mem_cons.2 (Or.inl rfl), heq ▸ h0⟩
    | inr hx =>
      obtain ⟨y, hy, hr⟩ := pairRel_exists_of_mem hrest x hx
      exact ⟨y, List.mem_cons.2 (Or.inr hy), hr⟩

theorem Crossing.memArc_of_rename (f : Nat → Nat) {C : Crossing} {a : Nat}
    (h : C.memArc a) : (C.rename f).memArc (f a) := by
  simp [Crossing.memArc, Crossing.rename] at h ⊢
  tauto

theorem Crossing.memArc_rotate180 (C : Crossing) (a : Nat) :
    C.rotate180.memArc a ↔ C.memArc a := by
  simp [Crossing.memArc, Crossing.rotate180]
  tauto

theorem Crossing.rotate180_rename (f : Nat → Nat) (C : Crossing) :
    (C.rename f).rotate180 = C.rotate180.rename f :=
  rfl

theorem Crossing.sameUpToRotation_rotate180_congr {C D : Crossing}
    (h : C.sameUpToRotation D) :
    C.rotate180.sameUpToRotation D.rotate180 := by
  rcases h with rfl | hrot | hrev | hrr
  · exact Or.inl rfl
  · have hD : D = C.rotate180 := by
      rw [hrot, Crossing.rotate180_involutive]
    subst hD
    exact (Crossing.sameUpToRotation_rotate180 C).symm
  · have hD : D = C.reverseUnders := by
      rw [hrev, Crossing.reverseUnders_involutive]
    subst hD
    rw [Crossing.reverseUnders_rotate180]
    exact Or.inr (Or.inr (Or.inl (Crossing.reverseUnders_involutive C.rotate180).symm))
  · have hD : D = C.rotate180.reverseUnders := by
      rw [hrr, Crossing.rotate180_involutive, Crossing.reverseUnders_involutive]
    subst hD
    rw [Crossing.reverseUnders_rotate180, Crossing.rotate180_involutive]
    exact Or.inr (Or.inr (Or.inr (show C.rotate180 =
        C.reverseUnders.reverseUnders.rotate180 by
      rw [Crossing.reverseUnders_involutive])))

theorem pairRel_flype_t_rev (f g : Nat → Nat) {tD tE : List Crossing}
    (hpair : pairRel (fun C Y => (C.rotate180.rename f).sameUpToRotation Y)
      tD tE)
    (hid : ∀ C ∈ tD, C.rename (g ∘ f) = C) :
    pairRel (fun Y C => (Y.rotate180.rename g).sameUpToRotation C) tE tD := by
  induction tD generalizing tE with
  | nil =>
    cases tE with
    | nil => trivial
    | cons _ _ => cases hpair
  | cons C cs ih =>
    cases tE with
    | nil => cases hpair
    | cons Y ys =>
      obtain ⟨hCY, hrest⟩ := hpair
      constructor
      · have hren : C.rotate180.rename (g ∘ f) = C.rotate180 := by
          rw [← Crossing.rotate180_rename, hid C (by simp)]
        have h1 : Y.sameUpToRotation (C.rotate180.rename f) := hCY.symm
        have h2 :
            (Y.rename g).sameUpToRotation ((C.rotate180.rename f).rename g) :=
          Crossing.sameUpToRotation_rename g h1
        have h3 : (Y.rename g).sameUpToRotation (C.rotate180.rename (g ∘ f)) :=
          h2
        have h4 : (Y.rename g).sameUpToRotation C.rotate180 := by
          simpa [hren] using h3
        have h5 :
            (Y.rename g).rotate180.sameUpToRotation C.rotate180.rotate180 :=
          Crossing.sameUpToRotation_rotate180_congr h4
        simpa [Crossing.rotate180_rename, Crossing.rotate180_involutive] using h5
      · exact ih hrest (fun W hW => hid W (by simp [hW]))

/-- Reverse a local flype by inverting the rename on appearing arcs of `D`. -/
theorem IsLocalFlype.symm {D E : TangleDiagram} (h : IsLocalFlype D E) :
    IsLocalFlype E D := by
  obtain ⟨f, FD, FE, tD, tE, restD, restE, uD, wD, uE, wE,
    hf, hslide, hNW, hNE, hSE, hSW, hpermD, hpermE, hpairRest, hpairT,
    hrestE, htE⟩ := h
  let g := planarInvFun f D.maxArc
  have hg : Function.Injective g := planarInvFun_injective f D.maxArc
  have hid {a : Nat} (ha : a ≤ D.maxArc) : g (f a) = a :=
    planarInvFun_of_le f hf D.maxArc ha
  have memD_of {C : Crossing}
      (hC : C = FD ∨ C ∈ tD ∨ C ∈ restD) : C ∈ D.crossings :=
    (List.Perm.mem_iff hpermD).2 (by
      simp [List.mem_cons, List.mem_append] at hC ⊢
      tauto)
  have hrename (C : Crossing) (hC : C ∈ D.crossings) :
      C.rename (g ∘ f) = C := by
    have hp := arc_le_maxArc_of_mem D hC
    cases C
    simp [Crossing.rename, Function.comp, hid hp.1, hid hp.2.1, hid hp.2.2.1,
      hid hp.2.2.2]
  have hpFD := arc_le_maxArc_of_mem D (memD_of (Or.inl rfl))
  have huD_le : uD ≤ D.maxArc := by
    rcases hslide.overD with h0 | h2
    · exact h0 ▸ hpFD.1
    · exact h2 ▸ hpFD.2.2.1
  have hwD_le : wD ≤ D.maxArc := by
    rcases hslide.underD with h1 | h3
    · exact h1 ▸ hpFD.2.1
    · exact h3 ▸ hpFD.2.2.2
  have hext_le : FD.extOverArc uD ≤ D.maxArc := by
    unfold Crossing.extOverArc
    split_ifs
    · exact hpFD.2.2.1
    · exact hpFD.1
  have hund_le : FD.otherUnderArc wD ≤ D.maxArc := by
    unfold Crossing.otherUnderArc
    split_ifs
    · exact hpFD.2.2.2
    · exact hpFD.2.1
  have hslide' : IsFlypeCrossingSlide g FE FD uE wE uD wD :=
    { adjD := hslide.adjE
      adjE := hslide.adjD
      portsD := hslide.portsE
      portsE := hslide.portsD
      sign := hslide.sign.symm
      huwD := hslide.huwE
      huwE := hslide.huwD
      overD := hslide.overE
      underD := hslide.underE
      overE := hslide.overD
      underE := hslide.underD
      u_map := by simp [g, hslide.u_map, hid huD_le]
      w_map := by simp [g, hslide.w_map, hid hwD_le]
      ext_match := by simp [g, hslide.ext_match, hid hext_le]
      und_match := by simp [g, hslide.und_match, hid hund_le] }
  have hmap_rest : restD.map (Crossing.rename (g ∘ f)) = restD :=
    List.map_eq_of_id fun C hC => hrename C (memD_of (Or.inr (Or.inr hC)))
  have hpairRest' :
      pairRel Crossing.sameUpToRotation (restE.map (Crossing.rename g)) restD := by
    have h1 :=
      pairRel_map (Crossing.rename g)
        (fun _ _ => Crossing.sameUpToRotation_rename g) hpairRest
    have hmap :
        (restD.map (Crossing.rename f)).map (Crossing.rename g) = restD := by
      rw [List.map_map]
      exact hmap_rest
    rw [hmap] at h1
    exact pairRel_symm (fun _ _ => Crossing.sameUpToRotation.symm) h1
  have hpairT' :
      pairRel (fun Y C => (Y.rotate180.rename g).sameUpToRotation C) tE tD :=
    pairRel_flype_t_rev f g hpairT fun C hC =>
      hrename C (memD_of (Or.inr (Or.inl hC)))
  have hrestD : ∀ C ∈ restD, ¬ C.memArc uD ∧ ¬ C.memArc wD := by
    intro C hC
    have hCf : C.rename f ∈ restD.map (Crossing.rename f) :=
      List.mem_map_of_mem hC
    obtain ⟨Y, hY, hCY⟩ := pairRel_exists_of_mem hpairRest (C.rename f) hCf
    constructor
    · intro hu
      have : Y.memArc uE :=
        (sameUpToRotation_memArc hCY).1
          (by simpa [hslide.u_map] using Crossing.memArc_of_rename f hu)
      exact (hrestE Y hY).1 this
    · intro hw
      have : Y.memArc wE :=
        (sameUpToRotation_memArc hCY).1
          (by simpa [hslide.w_map] using Crossing.memArc_of_rename f hw)
      exact (hrestE Y hY).2 this
  have htD : ∀ C ∈ tD, ¬ C.memArc uD ∧ ¬ C.memArc wD := by
    intro C hC
    obtain ⟨Y, hY, hCY⟩ := pairRel_exists_of_mem hpairT C hC
    constructor
    · intro hu
      have : Y.memArc uE :=
        (sameUpToRotation_memArc hCY).1 (by
          simpa [hslide.u_map, Crossing.memArc_rotate180] using
            Crossing.memArc_of_rename f ((Crossing.memArc_rotate180 C uD).2 hu))
      exact (htE Y hY).1 this
    · intro hw
      have : Y.memArc wE :=
        (sameUpToRotation_memArc hCY).1 (by
          simpa [hslide.w_map, Crossing.memArc_rotate180] using
            Crossing.memArc_of_rename f ((Crossing.memArc_rotate180 C wD).2 hw))
      exact (htE Y hY).2 this
  refine ⟨g, FE, FD, tE, tD, restE, restD, uE, wE, uD, wD,
    hg, hslide', ?_, ?_, ?_, ?_, hpermE, hpermD, hpairRest', hpairT',
    hrestD, htD⟩
  · simp [g, hNW, hid (maxArc_ge_NW D)]
  · simp [g, hNE, hid (maxArc_ge_NE D)]
  · simp [g, hSE, hid (maxArc_ge_SE D)]
  · simp [g, hSW, hid (maxArc_ge_SW D)]

/-- Reverse coloring along a local flype: distinguished legs lie on `f`,
    so the reverse move is again a local flype. -/
theorem coloring_IsLocalFlype_rev (D E : TangleDiagram) (col : Nat → Int)
    (h : IsLocalFlype D E) (hc : E.IsColored col) :
    ∃ col', D.IsColored col' ∧ SameEndpointColors E D col col' :=
  coloring_IsLocalFlype E D col h.symm hc

end RationalTangles
