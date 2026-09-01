/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RationalTangles.ColoringMoves
import RationalTangles.StandardForm

/-!
# Reidemeister/flype coloring invariance and twist-form integral colorability
-/

namespace RationalTangles

/-! ## Crossing ports -/

@[simp] theorem Crossing.arcs_zero (C : Crossing) : C.arcs 0 = C.a0 := rfl
@[simp] theorem Crossing.arcs_one (C : Crossing) : C.arcs 1 = C.a1 := rfl
@[simp] theorem Crossing.arcs_two (C : Crossing) : C.arcs 2 = C.a2 := rfl
@[simp] theorem Crossing.arcs_three (C : Crossing) : C.arcs 3 = C.a3 := rfl

/-! ## SameEndpointColors -/

theorem SameEndpointColors.refl (D : TangleDiagram) (col : Nat → Int) :
    SameEndpointColors D D col col :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem SameEndpointColors.trans {D E F : TangleDiagram} {col col' col'' : Nat → Int}
    (h₁ : SameEndpointColors D E col col') (h₂ : SameEndpointColors E F col' col'') :
    SameEndpointColors D F col col'' := by
  obtain ⟨a, b, c, d⟩ := h₁
  obtain ⟨a', b', c', d'⟩ := h₂
  exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d⟩

/-! ## Planar isotopy, reverse transport -/

theorem Crossing.sameUpToRotation.symm {C D : Crossing}
    (h : C.sameUpToRotation D) : D.sameUpToRotation C := by
  rcases h with rfl | hrot | hrev | hrr
  · exact Or.inl rfl
  · have : D = C.rotate180 := by
      rw [hrot, Crossing.rotate180_involutive]
    exact Or.inr (Or.inl this)
  · have : D = C.reverseUnders := by
      rw [hrev, Crossing.reverseUnders_involutive]
    exact Or.inr (Or.inr (Or.inl this))
  · have : D = C.rotate180.reverseUnders := by
      rw [hrr, Crossing.rotate180_involutive, Crossing.reverseUnders_involutive]
    refine Or.inr (Or.inr (Or.inr ?_))
    rw [this, ← Crossing.reverseUnders_rotate180]

theorem pairRel_symm {α} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) :
    ∀ {xs ys : List α}, pairRel R xs ys → pairRel R ys xs
  | [], [] => id
  | _ :: _, [] => by intro h; cases h
  | [], _ :: _ => by intro h; cases h
  | x :: xs, y :: ys => by
    intro h
    exact ⟨hR x y h.1, pairRel_symm hR h.2⟩

theorem coloring_planar_isotopy_backward (D E : TangleDiagram) (col : Nat → Int)
    (h : PlanarIsotopy D E) (hc : E.IsColored col) :
    ∃ col', D.IsColored col' ∧ SameEndpointColors D E col' col := by
  obtain ⟨f, _hf, hNW, hNE, hSE, hSW, Cs, hpair, hperm⟩ := h
  let col' : Nat → Int := col ∘ f
  have hCs : ∀ C ∈ Cs, ColoringRule C col :=
    fun C hC => hc C ((List.Perm.mem_iff hperm).1 hC)
  have hpair' :
      pairRel Crossing.sameUpToRotation Cs (D.crossings.map (Crossing.rename f)) :=
    pairRel_symm (fun _x _y => Crossing.sameUpToRotation.symm) hpair
  have hmap : ∀ C ∈ D.crossings.map (Crossing.rename f), ColoringRule C col :=
    pairRel_coloring (fun C₁ C₂ hCD col₀ hC0 =>
      ColoringRule_sameUpToRotation col₀ hCD hC0) hpair' col hCs
  refine ⟨col', ?_, ?_⟩
  · intro C hC
    have : C.rename f ∈ D.crossings.map (Crossing.rename f) := by
      simp [List.mem_map]
      exact ⟨C, hC, rfl⟩
    simpa [ColoringRule_rename] using hmap _ this
  · exact ⟨by simp [col', hNW], by simp [col', hNE], by simp [col', hSE],
      by simp [col', hSW]⟩

/-! ## mergeArc -/

@[simp] theorem mergeArc_src (src tgt : Nat) : mergeArc src tgt src = tgt := by
  simp [mergeArc]

theorem mergeArc_of_ne {src tgt a : Nat} (h : a ≠ src) : mergeArc src tgt a = a := by
  simp [mergeArc, h]

theorem mergeArc_color_eq (col : Nat → Int) (src tgt : Nat) (h : col src = col tgt) :
    col ∘ mergeArc src tgt = col := by
  funext a
  by_cases ha : a = src
  · subst ha; simp [mergeArc, h]
  · simp [mergeArc, ha]

theorem IsColored_eraseCrossing (D : TangleDiagram) (k : Nat) (col : Nat → Int)
    (h : D.IsColored col) : (D.eraseCrossing k).IsColored col :=
  fun C hC => h C (List.mem_of_mem_eraseIdx hC)

theorem getD_eq_getElem {α} [Inhabited α] (l : List α) (k : Fin l.length) :
    l.getD k.val default = l[k] := by
  simp [List.getD, k.isLt]

/-! ## Kinks are monochrome -/

theorem ColoringRule_kink_mono (C : Crossing) (col : Nat → Int) (p : Fin 4)
    (hk : C.IsKink p) (h : ColoringRule C col) :
    col (C.arcs p) = col (C.arcs (p + 2)) ∧
      col (C.arcs p) = col (C.arcs (p + 3)) := by
  obtain ⟨hβ, hr⟩ := h
  have hloop := hk.1
  fin_cases p <;> simp [Crossing.arcs] at hloop hβ hr ⊢ <;> (
    have hcol := congrArg col hloop
    constructor <;> linarith)

theorem ColoringRule_kink_of_mono (C : Crossing) (col : Nat → Int) (p : Fin 4)
    (hk : C.IsKink p)
    (h : col (C.arcs p) = col (C.arcs (p + 2)) ∧
      col (C.arcs p) = col (C.arcs (p + 3))) :
    ColoringRule C col := by
  have hloop := hk.1
  fin_cases p <;> simp [Crossing.arcs, ColoringRule] at hloop h ⊢ <;> (
    have hcol := congrArg col hloop
    constructor <;> linarith)

/-! ## Well-formed kinks: the loop is not used outside the kink crossing -/

theorem length_ge_two_of_distinct_mem {α} {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : 2 ≤ l.length := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
    · exact (hab rfl).elim
    · exact Nat.succ_le_succ (Nat.succ_le_of_lt (List.length_pos_of_mem hb'))
    · exact Nat.succ_le_succ (Nat.succ_le_of_lt (List.length_pos_of_mem ha'))
    · exact Nat.le_trans (ih ha' hb') (Nat.le_succ _)

theorem length_ge_three_of_distinct_mem {α} {l : List α} {a b c : α}
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : 3 ≤ l.length := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hb hc
    rcases ha with rfl | ha' <;> rcases hb with rfl | hb' <;> rcases hc with rfl | hc'
    · exact (hab rfl).elim
    · exact (hab rfl).elim
    · exact (hac rfl).elim
    · exact Nat.succ_le_succ (length_ge_two_of_distinct_mem hb' hc' hbc)
    · exact (hbc rfl).elim
    · exact Nat.succ_le_succ (length_ge_two_of_distinct_mem ha' hc' hac)
    · exact Nat.succ_le_succ (length_ge_two_of_distinct_mem ha' hb' hab)
    · exact Nat.le_trans (ih ha' hb' hc') (Nat.le_succ _)

theorem crossing_end_mem_endsOf (D : TangleDiagram) (i : Fin D.crossings.length)
    (p : Fin 4) :
    TangleDiagram.ArcEnd.crossing i.val p ∈ D.endsOf (D.crossings[i].arcs p) := by
  unfold TangleDiagram.endsOf
  simp [List.mem_append, List.mem_flatMap]
  exact ⟨i, rfl, rfl⟩

theorem kink_loop_ends (D : TangleDiagram) (k : Fin D.crossings.length) (p : Fin 4)
    (hk : (D.crossings[k]).IsKink p) :
    TangleDiagram.ArcEnd.crossing k.val p ∈ D.endsOf ((D.crossings[k]).arcs p) ∧
      TangleDiagram.ArcEnd.crossing k.val (p + 1) ∈ D.endsOf ((D.crossings[k]).arcs p) := by
  have hloop : (D.crossings[k]).arcs p = (D.crossings[k]).arcs (p + 1) := hk.1
  refine ⟨crossing_end_mem_endsOf D k p, ?_⟩
  rw [hloop]
  exact crossing_end_mem_endsOf D k (p + 1)

theorem Fin.succ_ne_self (p : Fin 4) : p ≠ p + 1 := by
  intro h
  have hv : p.val = (p.val + 1) % 4 := by
    simpa [Fin.val_add] using congrArg Fin.val h
  have : p.val < 4 := p.isLt
  omega

theorem memArc_port (C : Crossing) {a : Nat} (h : C.memArc a) :
    ∃ q : Fin 4, C.arcs q = a := by
  rcases h with h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩

theorem kink_loop_not_mem_erase (D : TangleDiagram) (k : Fin D.crossings.length)
    (p : Fin 4) (hk : (D.crossings[k]).IsKink p) (hw : D.WellFormed)
    {C : Crossing} (hC : C ∈ (D.eraseCrossing k.val).crossings) :
    ¬ C.memArc ((D.crossings[k]).arcs p) := by
  intro hmem
  let loop := (D.crossings[k]).arcs p
  obtain ⟨he1, he2⟩ := kink_loop_ends D k p hk
  have hlen2 : (D.endsOf loop).length = 2 := by
    have hwf := hw loop
    have hpos : 0 < (D.endsOf loop).length := List.length_pos_of_mem he1
    cases hwf with
    | inl h0 => omega
    | inr h2 => exact h2
  have hne12 : TangleDiagram.ArcEnd.crossing k.val p ≠ TangleDiagram.ArcEnd.crossing k.val (p + 1) := by
    intro h
    injection h with _ hp
    exact (Fin.succ_ne_self p) hp
  obtain ⟨j, hjlen, hjk, hCeq⟩ := (List.mem_eraseIdx_iff_getElem (l := D.crossings) (k := k.val)).1 hC
  obtain ⟨q, hq⟩ := memArc_port C hmem
  have he3 : TangleDiagram.ArcEnd.crossing j q ∈ D.endsOf loop := by
    have := crossing_end_mem_endsOf D ⟨j, hjlen⟩ q
    simpa [loop, hCeq, hq] using this
  have hne13 : TangleDiagram.ArcEnd.crossing k.val p ≠ TangleDiagram.ArcEnd.crossing j q := by
    intro h; injection h with hji _; exact hjk hji.symm
  have hne23 : TangleDiagram.ArcEnd.crossing k.val (p + 1) ≠ TangleDiagram.ArcEnd.crossing j q := by
    intro h; injection h with hji _; exact hjk hji.symm
  have : 3 ≤ (D.endsOf loop).length :=
    length_ge_three_of_distinct_mem he1 he2 he3 hne12 hne23 hne13
  omega


theorem boundary_end_mem_endsOf (D : TangleDiagram) (e : Endpoint) :
    TangleDiagram.ArcEnd.boundary e ∈ D.endsOf (D.boundary e) := by
  unfold TangleDiagram.endsOf
  simp [List.mem_append, List.mem_flatMap, TangleDiagram.boundary]
  match e with
  | .NW => simp
  | .NE => simp
  | .SE => simp
  | .SW => simp

theorem kink_loop_not_boundary (D : TangleDiagram) (k : Fin D.crossings.length)
    (p : Fin 4) (hk : (D.crossings[k]).IsKink p) (hw : D.WellFormed)
    (e : Endpoint) :
    D.boundary e ≠ (D.crossings[k]).arcs p := by
  intro heq
  let loop := (D.crossings[k]).arcs p
  obtain ⟨he1, he2⟩ := kink_loop_ends D k p hk
  have hlen2 : (D.endsOf loop).length = 2 := by
    have hwf := hw loop
    have hpos : 0 < (D.endsOf loop).length := List.length_pos_of_mem he1
    cases hwf with
    | inl h0 => omega
    | inr h2 => exact h2
  have hne12 : TangleDiagram.ArcEnd.crossing k.val p ≠
      TangleDiagram.ArcEnd.crossing k.val (p + 1) := by
    intro h; injection h with _ hp; exact (Fin.succ_ne_self p) hp
  have he3 : TangleDiagram.ArcEnd.boundary e ∈ D.endsOf loop := by
    simpa [loop, heq] using boundary_end_mem_endsOf D e
  have hne13 : TangleDiagram.ArcEnd.crossing k.val p ≠
      TangleDiagram.ArcEnd.boundary e := by intro h; cases h
  have hne23 : TangleDiagram.ArcEnd.crossing k.val (p + 1) ≠
      TangleDiagram.ArcEnd.boundary e := by intro h; cases h
  have : 3 ≤ (D.endsOf loop).length :=
    length_ge_three_of_distinct_mem he1 he2 he3 hne12 hne23 hne13
  omega

theorem ColoringRule_congr {C : Crossing} {col col' : Nat → Int}
    (h0 : col' C.a0 = col C.a0) (h1 : col' C.a1 = col C.a1)
    (h2 : col' C.a2 = col C.a2) (h3 : col' C.a3 = col C.a3)
    (hc : ColoringRule C col) : ColoringRule C col' := by
  obtain ⟨hβ, hr⟩ := hc
  constructor
  · simp [h0, h2, hβ]
  · simp [h1, h3, h0]; linarith

theorem collapseKink_eq (D : TangleDiagram) (k : Fin D.crossings.length) (p : Fin 4) :
    collapseKink D k.val p =
      (D.eraseCrossing k.val).rename
        (mergeArc ((D.crossings[k]).arcs (p + 3))
          ((D.crossings[k]).arcs (p + 2))) := by
  unfold collapseKink
  rw [getD_eq_getElem]

theorem IsColored_collapseKink (D : TangleDiagram) (k : Fin D.crossings.length)
    (p : Fin 4) (col : Nat → Int)
    (hk : (D.crossings[k]).IsKink p) (hc : D.IsColored col) :
    (collapseKink D k.val p).IsColored col ∧
      SameEndpointColors D (collapseKink D k.val p) col col := by
  have hmono := ColoringRule_kink_mono (D.crossings[k]) col p hk
    (hc _ (by simp [List.getElem_mem]))
  let thru0 := (D.crossings[k]).arcs (p + 2)
  let thru1 := (D.crossings[k]).arcs (p + 3)
  have hcolors : col thru1 = col thru0 := (hmono.2).symm.trans hmono.1
  have hfun : col ∘ mergeArc thru1 thru0 = col :=
    mergeArc_color_eq col thru1 thru0 hcolors
  have herase : (D.eraseCrossing k.val).IsColored col :=
    IsColored_eraseCrossing D k.val col hc
  have hrename :
      ((D.eraseCrossing k.val).rename (mergeArc thru1 thru0)).IsColored col := by
    rw [IsColored_rename]
    simpa [hfun] using herase
  have hEq : collapseKink D k.val p =
      (D.eraseCrossing k.val).rename (mergeArc thru1 thru0) := collapseKink_eq D k p
  refine ⟨hEq ▸ hrename, ?_⟩
  have hb (a : Nat) : col (mergeArc thru1 thru0 a) = col a := congrFun hfun a
  rw [hEq]
  exact ⟨hb _, hb _, hb _, hb _⟩

def colorAddKink (E : TangleDiagram) (k : Fin E.crossings.length) (p : Fin 4)
    (col' : Nat → Int) (a : Nat) : Int :=
  if a = (E.crossings[k]).arcs p then col' ((E.crossings[k]).arcs (p + 2))
  else col' (mergeArc ((E.crossings[k]).arcs (p + 3))
    ((E.crossings[k]).arcs (p + 2)) a)

theorem colorAddKink_ne {E : TangleDiagram} {k : Fin E.crossings.length} {p : Fin 4}
    {col' : Nat → Int} {a : Nat} (h : a ≠ (E.crossings[k]).arcs p) :
    colorAddKink E k p col' a =
      col' (mergeArc ((E.crossings[k]).arcs (p + 3))
        ((E.crossings[k]).arcs (p + 2)) a) := by
  unfold colorAddKink
  rw [if_neg h]

theorem IsColored_colorAddKink (E : TangleDiagram) (k : Fin E.crossings.length)
    (p : Fin 4) (col' : Nat → Int)
    (hk : (E.crossings[k]).IsKink p) (hw : E.WellFormed)
    (hc : (collapseKink E k.val p).IsColored col') :
    E.IsColored (colorAddKink E k p col') ∧
      SameEndpointColors (collapseKink E k.val p) E col'
        (colorAddKink E k p col') := by
  let loop := (E.crossings[k]).arcs p
  let thru0 := (E.crossings[k]).arcs (p + 2)
  let thru1 := (E.crossings[k]).arcs (p + 3)
  have hloop_ne_thru0 : loop ≠ thru0 := hk.2.1
  have hloop_ne_thru1 : loop ≠ thru1 := hk.2.2.1
  have hEq : collapseKink E k.val p =
      (E.eraseCrossing k.val).rename (mergeArc thru1 thru0) := collapseKink_eq E k p
  have herase_col :
      (E.eraseCrossing k.val).IsColored (col' ∘ mergeArc thru1 thru0) := by
    have : ((E.eraseCrossing k.val).rename (mergeArc thru1 thru0)).IsColored col' :=
      hEq ▸ hc
    exact (IsColored_rename _ _ _).1 this
  constructor
  · intro X hX
    by_cases hXk : X = E.crossings[k]
    · subst hXk
      refine ColoringRule_kink_of_mono (E.crossings[k]) (colorAddKink E k p col') p hk ?_
      have hL : colorAddKink E k p col' loop = col' thru0 := by
        unfold colorAddKink loop thru0; simp
      have h0 : colorAddKink E k p col' thru0 = col' thru0 := by
        unfold colorAddKink
        rw [if_neg (Ne.symm hloop_ne_thru0)]
        simp [mergeArc, thru0]
      have h1 : colorAddKink E k p col' thru1 = col' thru0 := by
        unfold colorAddKink
        rw [if_neg (Ne.symm hloop_ne_thru1)]
        simp [mergeArc, thru0, thru1]
      exact ⟨by simp [Crossing.arcs]; exact hL.trans h0.symm,
        by simp [Crossing.arcs]; exact hL.trans h1.symm⟩
    · have hXin : X ∈ (E.eraseCrossing k.val).crossings := by
        obtain ⟨j, hjlen, hXeq⟩ := List.mem_iff_getElem.mp hX
        have hjk : j ≠ k.val := by
          intro hj
          exact hXk (hXeq.symm.trans (by simp [hj]))
        exact (List.mem_eraseIdx_iff_getElem).2 ⟨j, hjlen, hjk, hXeq⟩
      have hnot : ¬ X.memArc loop := kink_loop_not_mem_erase E k p hk hw hXin
      have hr : ColoringRule X (col' ∘ mergeArc thru1 thru0) := herase_col X hXin
      have hport {a : Nat} (ha : a ≠ loop) :
          colorAddKink E k p col' a = (col' ∘ mergeArc thru1 thru0) a :=
        colorAddKink_ne ha
      exact ColoringRule_congr
        (hport (fun h => hnot (Or.inl h.symm)))
        (hport (fun h => hnot (Or.inr (Or.inl h.symm))))
        (hport (fun h => hnot (Or.inr (Or.inr (Or.inl h.symm)))))
        (hport (fun h => hnot (Or.inr (Or.inr (Or.inr h.symm)))))
        hr
  · have hbnd (e : Endpoint) : E.boundary e ≠ loop :=
      kink_loop_not_boundary E k p hk hw e
    rw [hEq]
    have hap (a : Nat) (hne : a ≠ loop) :
        colorAddKink E k p col' a = col' (mergeArc thru1 thru0 a) :=
      colorAddKink_ne hne
    constructor
    · exact hap _ (by simpa [TangleDiagram.boundary] using hbnd .NW)
    constructor
    · exact hap _ (by simpa [TangleDiagram.boundary] using hbnd .NE)
    constructor
    · exact hap _ (by simpa [TangleDiagram.boundary] using hbnd .SE)
    · exact hap _ (by simpa [TangleDiagram.boundary] using hbnd .SW)

theorem coloring_reidemeister_I_add (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIAdd D E) (hc : D.IsColored col) (hwE : E.WellFormed) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨k, p, hk, hiso⟩ := h
  obtain ⟨col₁, hcol₁, hsame₁⟩ :=
    coloring_planar_isotopy D (collapseKink E k.val p) col hiso hc
  obtain ⟨hE, hsame₂⟩ := IsColored_colorAddKink E k p col₁ hk hwE hcol₁
  exact ⟨colorAddKink E k p col₁, hE, hsame₁.trans hsame₂⟩

/-- After Reidemeister I (removing a kink), recolor so external colors are unchanged. -/
theorem coloring_reidemeister_I_remove (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIAdd E D) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨k, p, hk, hiso⟩ := h
  obtain ⟨hcol, hsame₁⟩ := IsColored_collapseKink D k p col hk hc
  obtain ⟨col', hE, hsame₂⟩ :=
    coloring_planar_isotopy_backward E (collapseKink D k.val p) col hiso hcol
  refine ⟨col', hE, ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := hsame₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := hsame₂
  exact ⟨a₂.symm.trans a₁, b₂.symm.trans b₁, c₂.symm.trans c₁, d₂.symm.trans d₁⟩

/-- Given a coloring of a 2-tangle, there is a way to recolor after a
Reidemeister I move so that the colors on the external strands are unchanged
and the coloring rule still holds at every crossing. -/
theorem coloring_IsReidemeisterI (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterI D E) (hc : D.IsColored col)
    (_hwD : D.WellFormed) (hwE : E.WellFormed) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  rcases h with h | h
  · exact coloring_reidemeister_I_add D E col h hc hwE
  · exact coloring_reidemeister_I_remove D E col h hc


/-! ## maxArc bounds -/

theorem foldl_maxArc_ge (l : List Crossing) (b : Nat) :
    b ≤ l.foldl (fun m C => max m C.maxArc) b := by
  induction l generalizing b with
  | nil => simp
  | cons C Cs ih =>
    simp [List.foldl]
    exact le_trans (Nat.le_max_left b C.maxArc) (ih _)

theorem foldl_maxArc_ge_mem (l : List Crossing) (b : Nat) {C : Crossing}
    (h : C ∈ l) :
    C.maxArc ≤ l.foldl (fun m (X : Crossing) => max m X.maxArc) b := by
  induction l generalizing b with
  | nil => cases h
  | cons C' Cs ih =>
    rw [List.foldl]
    simp [List.mem_cons] at h
    rcases h with hC | hCs
    · subst hC
      exact le_trans (Nat.le_max_right b C.maxArc) (foldl_maxArc_ge Cs _)
    · exact ih (max b C'.maxArc) hCs

theorem maxArc_ge_NW (T : TangleDiagram) : T.NW ≤ T.maxArc := by
  unfold TangleDiagram.maxArc
  exact le_trans (Nat.le_max_left _ _) (foldl_maxArc_ge _ _)

theorem maxArc_ge_NE (T : TangleDiagram) : T.NE ≤ T.maxArc := by
  unfold TangleDiagram.maxArc
  have h1 : T.NE ≤ max T.NE (max T.SE T.SW) := Nat.le_max_left _ _
  have h2 : T.NE ≤ max T.NW (max T.NE (max T.SE T.SW)) :=
    le_trans h1 (Nat.le_max_right _ _)
  exact le_trans h2 (foldl_maxArc_ge _ _)

theorem maxArc_ge_SE (T : TangleDiagram) : T.SE ≤ T.maxArc := by
  unfold TangleDiagram.maxArc
  have h1 : T.SE ≤ max T.SE T.SW := Nat.le_max_left _ _
  have h2 : T.SE ≤ max T.NE (max T.SE T.SW) := le_trans h1 (Nat.le_max_right _ _)
  have h3 : T.SE ≤ max T.NW (max T.NE (max T.SE T.SW)) :=
    le_trans h2 (Nat.le_max_right _ _)
  exact le_trans h3 (foldl_maxArc_ge _ _)

theorem maxArc_ge_SW (T : TangleDiagram) : T.SW ≤ T.maxArc := by
  unfold TangleDiagram.maxArc
  have h1 : T.SW ≤ max T.SE T.SW := Nat.le_max_right _ _
  have h2 : T.SW ≤ max T.NE (max T.SE T.SW) := le_trans h1 (Nat.le_max_right _ _)
  have h3 : T.SW ≤ max T.NW (max T.NE (max T.SE T.SW)) :=
    le_trans h2 (Nat.le_max_right _ _)
  exact le_trans h3 (foldl_maxArc_ge _ _)

theorem Crossing.a0_le_maxArc (C : Crossing) : C.a0 ≤ C.maxArc :=
  Nat.le_max_left _ _

theorem Crossing.a1_le_maxArc (C : Crossing) : C.a1 ≤ C.maxArc :=
  le_trans (Nat.le_max_left C.a1 (max C.a2 C.a3)) (Nat.le_max_right _ _)

theorem Crossing.a2_le_maxArc (C : Crossing) : C.a2 ≤ C.maxArc :=
  le_trans (Nat.le_max_left C.a2 C.a3)
    (le_trans (Nat.le_max_right C.a1 _) (Nat.le_max_right C.a0 _))

theorem Crossing.a3_le_maxArc (C : Crossing) : C.a3 ≤ C.maxArc :=
  le_trans (Nat.le_max_right C.a2 C.a3)
    (le_trans (Nat.le_max_right C.a1 _) (Nat.le_max_right C.a0 _))

theorem maxArc_ge_of_mem (T : TangleDiagram) {C : Crossing}
    (h : C ∈ T.crossings) : C.maxArc ≤ T.maxArc := by
  unfold TangleDiagram.maxArc
  exact le_trans (foldl_maxArc_ge_mem T.crossings
    (max T.NW (max T.NE (max T.SE T.SW))) h) (le_refl _)

theorem arc_le_maxArc_of_mem (T : TangleDiagram) {C : Crossing}
    (h : C ∈ T.crossings) :
    C.a0 ≤ T.maxArc ∧ C.a1 ≤ T.maxArc ∧ C.a2 ≤ T.maxArc ∧ C.a3 ≤ T.maxArc := by
  have hm := maxArc_ge_of_mem T h
  exact ⟨le_trans C.a0_le_maxArc hm, le_trans C.a1_le_maxArc hm,
    le_trans C.a2_le_maxArc hm, le_trans C.a3_le_maxArc hm⟩

/-! ## Reverse planar isotopy

`PlanarIsotopy` uses an injective arc rename `f`. A global left inverse of
`f` need not be injective, so reverse uses `planarInvFun f D.maxArc`, which
inverts `f` on `{a | a ≤ D.maxArc}` (all appearing arcs of `D`) and shifts
the remaining names. This is not a coloring lemma: reverse coloring along
`PlanarIsotopy` is `coloring_planar_isotopy_backward`.
-/

/-- Inverse of an injective rename on `{a | a ≤ M}`; names outside that
    image are shifted past `M`, so the result is globally injective. -/
def planarInvFun (f : Nat → Nat) (M b : Nat) : Nat :=
  match (List.range (M + 1)).find? (fun a => f a == b) with
  | some a => a
  | none => b + M + 1

theorem planarInvFun_of_le (f : Nat → Nat) (hf : Function.Injective f)
    (M : Nat) {a : Nat} (ha : a ≤ M) :
    planarInvFun f M (f a) = a := by
  unfold planarInvFun
  cases h : (List.range (M + 1)).find? (fun k => f k == f a) with
  | none =>
    have : a ∈ List.range (M + 1) := List.mem_range.2 (Nat.lt_succ_of_le ha)
    have hnone := List.find?_eq_none.1 h
    exact (hnone a this (by simp)).elim
  | some k =>
    have hk : f k = f a := by
      have := List.find?_some (p := fun k => f k == f a) h
      simpa using this
    exact hf hk

theorem mem_of_find?_eq_some {α} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  obtain ⟨_, as, bs, rfl, _⟩ := List.find?_eq_some_iff_append.1 h
  simp

theorem planarInvFun_injective (f : Nat → Nat) (M : Nat) :
    Function.Injective (planarInvFun f M) := by
  intro x y hxy
  unfold planarInvFun at hxy
  cases hx : (List.range (M + 1)).find? (fun a => f a == x) with
  | none =>
    cases hy : (List.range (M + 1)).find? (fun a => f a == y) with
    | none => simp [hx, hy] at hxy; omega
    | some b =>
      simp [hx, hy] at hxy
      have : b < M + 1 := List.mem_range.1 (mem_of_find?_eq_some hy)
      omega
  | some a =>
    cases hy : (List.range (M + 1)).find? (fun a => f a == y) with
    | none =>
      simp [hx, hy] at hxy
      have : a < M + 1 := List.mem_range.1 (mem_of_find?_eq_some hx)
      omega
    | some b =>
      simp [hx, hy] at hxy
      have ha : f a = x := by
        have := List.find?_some (p := fun k => f k == x) hx
        simpa using this
      have hb : f b = y := by
        have := List.find?_some (p := fun k => f k == y) hy
        simpa using this
      exact ha.symm.trans (hxy ▸ hb)

theorem pairRel_map {α β} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hRS : ∀ x y, R x y → S (f x) (f y)) :
    ∀ {xs ys : List α}, pairRel R xs ys → pairRel S (xs.map f) (ys.map f)
  | [], [] => id
  | _ :: _, [] => by intro h; cases h
  | [], _ :: _ => by intro h; cases h
  | _ :: _, _ :: _ => by
    intro h
    exact ⟨hRS _ _ h.1, pairRel_map f hRS h.2⟩

theorem pairRel_perm_left {α} {R : α → α → Prop}
    {xs ys : List α} (hpair : pairRel R xs ys) {xs'} (hperm : xs.Perm xs') :
    ∃ ys', ys.Perm ys' ∧ pairRel R xs' ys' := by
  induction hperm generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨[], .nil, trivial⟩
    | cons _ _ => cases hpair
  | cons x h ih =>
    cases ys with
    | nil => cases hpair
    | cons y ys =>
      obtain ⟨hxy, hrest⟩ := hpair
      obtain ⟨ys', hp, hr⟩ := ih hrest
      exact ⟨y :: ys', hp.cons y, ⟨hxy, hr⟩⟩
  | swap x y l =>
    cases ys with
    | nil => cases hpair
    | cons y0 ys =>
      cases ys with
      | nil => cases hpair.2
      | cons x0 ys =>
        obtain ⟨hy, hxrest⟩ := hpair
        obtain ⟨hx, hrest⟩ := hxrest
        exact ⟨x0 :: y0 :: ys, .swap x0 y0 ys, ⟨hx, hy, hrest⟩⟩
  | trans h1 h2 ih1 ih2 =>
    obtain ⟨ys1, hp1, hr1⟩ := ih1 hpair
    obtain ⟨ys2, hp2, hr2⟩ := ih2 hr1
    exact ⟨ys2, hp1.trans hp2, hr2⟩

theorem Crossing.sameUpToRotation_rename (g : Nat → Nat) {C D : Crossing}
    (h : C.sameUpToRotation D) :
    (C.rename g).sameUpToRotation (D.rename g) := by
  rcases h with rfl | hrot | hrev | hrr
  · exact Or.inl rfl
  · rw [hrot]; exact Or.inr (Or.inl rfl)
  · rw [hrev]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [hrr]; exact Or.inr (Or.inr (Or.inr rfl))

theorem List.map_eq_of_id {α} {f : α → α} {l : List α}
    (h : ∀ x ∈ l, f x = x) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [h x (List.mem_cons.2 (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))]

/-- Reverse a planar isotopy by inverting the rename on appearing arcs. -/
theorem PlanarIsotopy.symm {D E : TangleDiagram} (h : PlanarIsotopy D E) :
    PlanarIsotopy E D := by
  obtain ⟨f, hf, hNW, hNE, hSE, hSW, Cs, hpair, hperm⟩ := h
  let g := planarInvFun f D.maxArc
  have hg : Function.Injective g := planarInvFun_injective f D.maxArc
  have hid {a : Nat} (ha : a ≤ D.maxArc) : g (f a) = a :=
    planarInvFun_of_le f hf D.maxArc ha
  have hrename {C : Crossing} (hC : C ∈ D.crossings) :
      C.rename (g ∘ f) = C := by
    have hp := arc_le_maxArc_of_mem D hC
    cases C
    simp [Crossing.rename, Function.comp, hid hp.1, hid hp.2.1, hid hp.2.2.1,
      hid hp.2.2.2]
  have hmapD :
      D.crossings.map (Crossing.rename (g ∘ f)) = D.crossings :=
    List.map_eq_of_id fun C hC => hrename hC
  have hpairg :
      pairRel Crossing.sameUpToRotation
        (Cs.map (Crossing.rename g)) D.crossings := by
    have h1 :=
      pairRel_map (Crossing.rename g) (fun _ _ =>
        Crossing.sameUpToRotation_rename g) hpair
    have hmap :
        (D.crossings.map (Crossing.rename f)).map (Crossing.rename g) =
          D.crossings := by
      rw [List.map_map]
      exact hmapD
    rw [hmap] at h1
    exact pairRel_symm (fun _ _ => Crossing.sameUpToRotation.symm) h1
  have hperm' : (Cs.map (Crossing.rename g)).Perm
      (E.crossings.map (Crossing.rename g)) := hperm.map _
  obtain ⟨Cs', hCs', hpair'⟩ := pairRel_perm_left hpairg hperm'
  refine ⟨g, hg, ?_, ?_, ?_, ?_, Cs', hpair', hCs'.symm⟩
  · simp [g, hNW, hid (maxArc_ge_NW D)]
  · simp [g, hNE, hid (maxArc_ge_NE D)]
  · simp [g, hSE, hid (maxArc_ge_SE D)]
  · simp [g, hSW, hid (maxArc_ge_SW D)]

/-! ## Extending colorings across `[±1]` twists -/

def colorAddOne (T : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun x =>
    if x = T.maxArc + 2 then 2 * col T.NE - col T.SE
    else if x = T.maxArc + 3 then col T.NE
    else col x

def colorAddNegOne (T : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun x =>
    if x = T.maxArc + 2 then col T.SE
    else if x = T.maxArc + 3 then 2 * col T.SE - col T.NE
    else col x

def colorMulOne (T : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun x =>
    if x = T.maxArc + 3 then col T.SW
    else if x = T.maxArc + 4 then 2 * col T.SW - col T.SE
    else col x

def colorMulNegOne (T : TangleDiagram) (col : Nat → Int) : Nat → Int :=
  fun x =>
    if x = T.maxArc + 3 then 2 * col T.SE - col T.SW
    else if x = T.maxArc + 4 then col T.SE
    else col x

theorem colorAddOne_old {T : TangleDiagram} {col : Nat → Int} {x : Nat}
    (h2 : x ≠ T.maxArc + 2) (h3 : x ≠ T.maxArc + 3) :
    colorAddOne T col x = col x := by
  simp [colorAddOne, h2, h3]

theorem colorAddNegOne_old {T : TangleDiagram} {col : Nat → Int} {x : Nat}
    (h2 : x ≠ T.maxArc + 2) (h3 : x ≠ T.maxArc + 3) :
    colorAddNegOne T col x = col x := by
  simp [colorAddNegOne, h2, h3]

theorem colorMulOne_old {T : TangleDiagram} {col : Nat → Int} {x : Nat}
    (h3 : x ≠ T.maxArc + 3) (h4 : x ≠ T.maxArc + 4) :
    colorMulOne T col x = col x := by
  simp [colorMulOne, h3, h4]

theorem colorMulNegOne_old {T : TangleDiagram} {col : Nat → Int} {x : Nat}
    (h3 : x ≠ T.maxArc + 3) (h4 : x ≠ T.maxArc + 4) :
    colorMulNegOne T col x = col x := by
  simp [colorMulNegOne, h3, h4]

theorem one_rename_shift (s : Nat) :
    one.rename (fun x => x + s) =
      { crossings := [⟨s, s + 1, s + 2, s + 3, CrossingSign.pos⟩]
        NW := s, NE := s + 1, SE := s + 2, SW := s + 3 } := by
  simp [one, TangleDiagram.rename, Crossing.rename]
  omega

theorem add_one_crossings (T : TangleDiagram) :
    (T.add one).crossings =
      T.crossings ++
        [⟨T.NE, T.maxArc + 2, T.maxArc + 3, T.SE, CrossingSign.pos⟩] := by
  unfold TangleDiagram.add
  rw [one_rename_shift]
  simp [TangleDiagram.rename, Crossing.rename]


theorem add_one_NW (T : TangleDiagram) : (T.add one).NW = T.NW := by
  unfold TangleDiagram.add
  rfl

theorem add_one_SW (T : TangleDiagram) : (T.add one).SW = T.SW := by
  unfold TangleDiagram.add
  rfl

theorem add_one_NE (T : TangleDiagram) : (T.add one).NE = T.maxArc + 2 := by
  unfold TangleDiagram.add
  rw [one_rename_shift]
  simp [TangleDiagram.rename]

theorem add_one_SE (T : TangleDiagram) : (T.add one).SE = T.maxArc + 3 := by
  unfold TangleDiagram.add
  rw [one_rename_shift]
  simp [TangleDiagram.rename]

theorem IsColored_add_one (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) :
    (T.add one).IsColored (colorAddOne T col) := by
  intro C hC
  rw [add_one_crossings, List.mem_append] at hC
  rcases hC with hT | hNew
  · have hr := h C hT
    have hb := arc_le_maxArc_of_mem T hT
    have h2 : C.a0 ≠ T.maxArc + 2 ∧ C.a1 ≠ T.maxArc + 2 ∧
        C.a2 ≠ T.maxArc + 2 ∧ C.a3 ≠ T.maxArc + 2 := by omega
    have h3 : C.a0 ≠ T.maxArc + 3 ∧ C.a1 ≠ T.maxArc + 3 ∧
        C.a2 ≠ T.maxArc + 3 ∧ C.a3 ≠ T.maxArc + 3 := by omega
    exact ColoringRule_congr
      (colorAddOne_old h2.1 h3.1)
      (colorAddOne_old h2.2.1 h3.2.1)
      (colorAddOne_old h2.2.2.1 h3.2.2.1)
      (colorAddOne_old h2.2.2.2 h3.2.2.2)
      hr
  · simp at hNew
    subst hNew
    have hNEle : T.NE ≤ T.maxArc := maxArc_ge_NE T
    have hSEle : T.SE ≤ T.maxArc := maxArc_ge_SE T
    have hNE2 : T.NE ≠ T.maxArc + 2 := by omega
    have hNE3 : T.NE ≠ T.maxArc + 3 := by omega
    have hSE2 : T.SE ≠ T.maxArc + 2 := by omega
    have hSE3 : T.SE ≠ T.maxArc + 3 := by omega
    constructor
    · simp [colorAddOne, hNE2, hNE3]
    · simp [colorAddOne, hNE2, hNE3, hSE2, hSE3]

/-! ## Standard-form coloring from two initial strand colors -/

def StandardExpr.colorFrom : StandardExpr → Int → Int → (Nat → Int)
  | .zero, a, c => colorZero a c
  | .infinity, a, b => colorInfinity a b
  | .addRight e .pos, a, c => colorAddOne e.diagram (e.colorFrom a c)
  | .addRight e .neg, a, c => colorAddNegOne e.diagram (e.colorFrom a c)
  | .mulBottom e .pos, a, c => colorMulOne e.diagram (e.colorFrom a c)
  | .mulBottom e .neg, a, c => colorMulNegOne e.diagram (e.colorFrom a c)


theorem negOne_rename_shift (s : Nat) :
    negOne.rename (fun x => x + s) =
      { crossings := [⟨s + 1, s + 2, s + 3, s, CrossingSign.neg⟩]
        NW := s, NE := s + 1, SE := s + 2, SW := s + 3 } := by
  simp [negOne, one, TangleDiagram.mirror, TangleDiagram.rename, Crossing.rename,
    Crossing.switch, CrossingSign.flip, Nat.add_comm]

theorem add_negOne_crossings (T : TangleDiagram) :
    (T.add negOne).crossings =
      T.crossings ++
        [⟨T.maxArc + 2, T.maxArc + 3, T.SE, T.NE, CrossingSign.neg⟩] := by
  unfold TangleDiagram.add
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename, Crossing.rename]

theorem add_negOne_NW (T : TangleDiagram) : (T.add negOne).NW = T.NW := by
  unfold TangleDiagram.add
  rfl

theorem add_negOne_SW (T : TangleDiagram) : (T.add negOne).SW = T.SW := by
  unfold TangleDiagram.add
  rfl

theorem IsColored_add_negOne (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) :
    (T.add negOne).IsColored (colorAddNegOne T col) := by
  intro C hC
  rw [add_negOne_crossings, List.mem_append] at hC
  rcases hC with hT | hNew
  · have hr := h C hT
    have hb := arc_le_maxArc_of_mem T hT
    have h2 : C.a0 ≠ T.maxArc + 2 ∧ C.a1 ≠ T.maxArc + 2 ∧
        C.a2 ≠ T.maxArc + 2 ∧ C.a3 ≠ T.maxArc + 2 := by omega
    have h3 : C.a0 ≠ T.maxArc + 3 ∧ C.a1 ≠ T.maxArc + 3 ∧
        C.a2 ≠ T.maxArc + 3 ∧ C.a3 ≠ T.maxArc + 3 := by omega
    exact ColoringRule_congr
      (colorAddNegOne_old h2.1 h3.1)
      (colorAddNegOne_old h2.2.1 h3.2.1)
      (colorAddNegOne_old h2.2.2.1 h3.2.2.1)
      (colorAddNegOne_old h2.2.2.2 h3.2.2.2)
      hr
  · simp at hNew
    subst hNew
    have hNEle : T.NE ≤ T.maxArc := maxArc_ge_NE T
    have hSEle : T.SE ≤ T.maxArc := maxArc_ge_SE T
    have hNE2 : T.NE ≠ T.maxArc + 2 := by omega
    have hNE3 : T.NE ≠ T.maxArc + 3 := by omega
    have hSE2 : T.SE ≠ T.maxArc + 2 := by omega
    have hSE3 : T.SE ≠ T.maxArc + 3 := by omega
    constructor
    · simp [colorAddNegOne, hSE2, hSE3]
    · simp [colorAddNegOne, hNE2, hNE3]

theorem mul_one_crossings (T : TangleDiagram) :
    (T.mul one).crossings =
      T.crossings ++
        [⟨T.SW, T.SE, T.maxArc + 3, T.maxArc + 4, CrossingSign.pos⟩] := by
  unfold TangleDiagram.mul
  rw [one_rename_shift]
  simp [TangleDiagram.rename, Crossing.rename]

theorem IsColored_mul_one (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) :
    (T.mul one).IsColored (colorMulOne T col) := by
  intro C hC
  rw [mul_one_crossings, List.mem_append] at hC
  rcases hC with hT | hNew
  · have hr := h C hT
    have hb := arc_le_maxArc_of_mem T hT
    have h3 : C.a0 ≠ T.maxArc + 3 ∧ C.a1 ≠ T.maxArc + 3 ∧
        C.a2 ≠ T.maxArc + 3 ∧ C.a3 ≠ T.maxArc + 3 := by omega
    have h4 : C.a0 ≠ T.maxArc + 4 ∧ C.a1 ≠ T.maxArc + 4 ∧
        C.a2 ≠ T.maxArc + 4 ∧ C.a3 ≠ T.maxArc + 4 := by omega
    exact ColoringRule_congr
      (colorMulOne_old h3.1 h4.1)
      (colorMulOne_old h3.2.1 h4.2.1)
      (colorMulOne_old h3.2.2.1 h4.2.2.1)
      (colorMulOne_old h3.2.2.2 h4.2.2.2)
      hr
  · simp at hNew
    subst hNew
    have hSWle : T.SW ≤ T.maxArc := maxArc_ge_SW T
    have hSEle : T.SE ≤ T.maxArc := maxArc_ge_SE T
    have hSW3 : T.SW ≠ T.maxArc + 3 := by omega
    have hSW4 : T.SW ≠ T.maxArc + 4 := by omega
    have hSE3 : T.SE ≠ T.maxArc + 3 := by omega
    have hSE4 : T.SE ≠ T.maxArc + 4 := by omega
    constructor
    · simp [colorMulOne, hSW3, hSW4]
    · simp [colorMulOne, hSW3, hSW4, hSE3, hSE4]

theorem mul_negOne_crossings (T : TangleDiagram) :
    (T.mul negOne).crossings =
      T.crossings ++
        [⟨T.SE, T.maxArc + 3, T.maxArc + 4, T.SW, CrossingSign.neg⟩] := by
  unfold TangleDiagram.mul
  rw [negOne_rename_shift]
  simp [TangleDiagram.rename, Crossing.rename]

theorem IsColored_mul_negOne (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) :
    (T.mul negOne).IsColored (colorMulNegOne T col) := by
  intro C hC
  rw [mul_negOne_crossings, List.mem_append] at hC
  rcases hC with hT | hNew
  · have hr := h C hT
    have hb := arc_le_maxArc_of_mem T hT
    have h3 : C.a0 ≠ T.maxArc + 3 ∧ C.a1 ≠ T.maxArc + 3 ∧
        C.a2 ≠ T.maxArc + 3 ∧ C.a3 ≠ T.maxArc + 3 := by omega
    have h4 : C.a0 ≠ T.maxArc + 4 ∧ C.a1 ≠ T.maxArc + 4 ∧
        C.a2 ≠ T.maxArc + 4 ∧ C.a3 ≠ T.maxArc + 4 := by omega
    exact ColoringRule_congr
      (colorMulNegOne_old h3.1 h4.1)
      (colorMulNegOne_old h3.2.1 h4.2.1)
      (colorMulNegOne_old h3.2.2.1 h4.2.2.1)
      (colorMulNegOne_old h3.2.2.2 h4.2.2.2)
      hr
  · simp at hNew
    subst hNew
    have hSWle : T.SW ≤ T.maxArc := maxArc_ge_SW T
    have hSEle : T.SE ≤ T.maxArc := maxArc_ge_SE T
    have hSW3 : T.SW ≠ T.maxArc + 3 := by omega
    have hSW4 : T.SW ≠ T.maxArc + 4 := by omega
    have hSE3 : T.SE ≠ T.maxArc + 3 := by omega
    have hSE4 : T.SE ≠ T.maxArc + 4 := by omega
    constructor
    · simp [colorMulNegOne, hSE3, hSE4]
    · simp [colorMulNegOne, hSW3, hSW4, hSE3, hSE4]

theorem StandardExpr.colorFrom_isColored (e : StandardExpr) (a c : Int) :
    e.diagram.IsColored (e.colorFrom a c) := by
  induction e with
  | zero => exact zero_isColored a c
  | infinity => exact infinity_isColored a c
  | addRight e s ih =>
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      exact IsColored_add_one e.diagram (e.colorFrom a c) ih
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      exact IsColored_add_negOne e.diagram (e.colorFrom a c) ih
  | mulBottom e s ih =>
    cases s with
    | pos =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      exact IsColored_mul_one e.diagram (e.colorFrom a c) ih
    | neg =>
      simp [StandardExpr.diagram, StandardExpr.colorFrom, crossingTangle]
      exact IsColored_mul_negOne e.diagram (e.colorFrom a c) ih

/-- Every standard-form (hence twist-form) rational tangle is integrally
colorable by propagating two initial strand colors through successive
`[±1]` twists. This is not the constant coloring. -/
theorem integrally_colorable_from_initial (T : TangleDiagram)
    (h : IsStandardForm T) :
    ∃ col : Nat → Int, T.IsColored col := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.colorFrom 0 1, e.colorFrom_isColored 0 1⟩


/-! ## Reidemeister II -/

theorem memArcB_iff (C : Crossing) (a : Nat) :
    memArcB C a = true ↔ C.memArc a := by
  unfold memArcB Crossing.memArc
  simp [beq_iff_eq, Bool.or_eq_true]
  tauto

theorem IsColored_eraseTwo (D : TangleDiagram) (i j : Nat) (col : Nat → Int)
    (hc : D.IsColored col) :
    (eraseTwo D i j).IsColored col := by
  intro C hC
  unfold eraseTwo at hC
  split_ifs at hC with hlt hgt
  · exact IsColored_eraseCrossing (D.eraseCrossing j) i col
      (IsColored_eraseCrossing D j col hc) C hC
  · exact IsColored_eraseCrossing (D.eraseCrossing i) j col
      (IsColored_eraseCrossing D i col hc) C hC
  · exact IsColored_eraseCrossing D i col hc C hC

theorem ColoringRule.opposite_color {C : Crossing} {col : Nat → Int}
    (h : ColoringRule C col) (p : Fin 4) :
    col (C.arcs (p + 2)) = 2 * col C.a0 - col (C.arcs p) := by
  obtain ⟨hβ, hr⟩ := h
  fin_cases p <;> simp [Crossing.arcs] at * <;> linarith

theorem portOf_eq_some (C : Crossing) {a : Nat} (ha : C.memArc a) :
    ∃ p : Fin 4, C.portOf a = some p := by
  unfold Crossing.portOf
  split_ifs with h0 h1 h2 h3
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩
  · exact ⟨⟨2, by decide⟩, rfl⟩
  · exact ⟨⟨3, by decide⟩, rfl⟩
  · rcases ha with h | h | h | h
    · exact (h0 h.symm).elim
    · exact (h1 h.symm).elim
    · exact (h2 h.symm).elim
    · exact (h3 h.symm).elim

theorem portOf_arcs (C : Crossing) {a : Nat} {p : Fin 4}
    (hp : C.portOf a = some p) : C.arcs p = a := by
  unfold Crossing.portOf at hp
  split_ifs at hp with h0 h1 h2 h3
  · injection hp with hp; subst hp; simpa [Crossing.arcs] using h0
  · injection hp with hp; subst hp; simpa [Crossing.arcs] using h1
  · injection hp with hp; subst hp; simpa [Crossing.arcs] using h2
  · injection hp with hp; subst hp; simpa [Crossing.arcs] using h3

theorem ColoringRule.oppositeArc_color {C : Crossing} {col : Nat → Int}
    (h : ColoringRule C col) {a : Nat} (ha : C.memArc a) :
    col (C.oppositeArc a) = 2 * col C.a0 - col a := by
  obtain ⟨p, hp⟩ := portOf_eq_some C ha
  have hpa := portOf_arcs C hp
  unfold Crossing.oppositeArc
  rw [hp]
  have := h.opposite_color p
  rwa [hpa] at this

theorem r2Merge_color_of_over_eq (C D : Crossing) (col : Nat → Int)
    (hC : ColoringRule C col) (hD : ColoringRule D col)
    (hβ : col C.a0 = col D.a0) (a : Nat) :
    col (r2Merge C D a) = col a := by
  unfold r2Merge
  dsimp
  split_ifs with hB
  · have haC : C.memArc a := (memArcB_iff C a).1 (by
      simp [Bool.and_eq_true] at hB; exact hB.1.1)
    have hOpp : D.memArc (C.oppositeArc a) :=
      (memArcB_iff D (C.oppositeArc a)).1 (by
        simp [Bool.and_eq_true] at hB; exact hB.2)
    have h1 := hC.oppositeArc_color haC
    have h2 := hD.oppositeArc_color hOpp
    linarith
  · rfl

theorem collapseR2_eq (D : TangleDiagram) (i j : Fin D.crossings.length) :
    collapseR2 D i.val j.val =
      (eraseTwo D i.val j.val).rename
        (r2Merge D.crossings[i] D.crossings[j]) := by
  unfold collapseR2
  rw [getD_eq_getElem, getD_eq_getElem]

theorem IsColored_collapseR2 (D : TangleDiagram) (i j : Fin D.crossings.length)
    (col : Nat → Int) (hc : D.IsColored col)
    (hβ : col D.crossings[i].a0 = col D.crossings[j].a0) :
    (collapseR2 D i.val j.val).IsColored col ∧
      SameEndpointColors D (collapseR2 D i.val j.val) col col := by
  have hC : ColoringRule D.crossings[i] col := hc _ (List.getElem_mem _)
  have hD : ColoringRule D.crossings[j] col := hc _ (List.getElem_mem _)
  have hfun : col ∘ r2Merge D.crossings[i] D.crossings[j] = col := by
    funext a
    exact r2Merge_color_of_over_eq _ _ col hC hD hβ a
  have herase : (eraseTwo D i.val j.val).IsColored col :=
    IsColored_eraseTwo D i.val j.val col hc
  have hrename :
      ((eraseTwo D i.val j.val).rename
        (r2Merge D.crossings[i] D.crossings[j])).IsColored col := by
    rw [IsColored_rename, hfun]
    exact herase
  have hEq := collapseR2_eq D i j
  refine ⟨hEq ▸ hrename, ?_⟩
  have hb (a : Nat) : col (r2Merge D.crossings[i] D.crossings[j] a) = col a :=
    congrFun hfun a
  rw [hEq]
  have hbd :
      (eraseTwo D i.val j.val).NW = D.NW ∧
      (eraseTwo D i.val j.val).NE = D.NE ∧
      (eraseTwo D i.val j.val).SE = D.SE ∧
      (eraseTwo D i.val j.val).SW = D.SW := by
    unfold eraseTwo TangleDiagram.eraseCrossing
    split_ifs <;> simp
  dsimp [TangleDiagram.rename]
  rw [hbd.1, hbd.2.1, hbd.2.2.1, hbd.2.2.2]
  exact ⟨hb D.NW, hb D.NE, hb D.SE, hb D.SW⟩

theorem ColoringRule.over_of_mem {C : Crossing} {col : Nat → Int}
    (h : ColoringRule C col) {a : Nat} (ha0 : a = C.a0 ∨ a = C.a2) :
    col a = col C.a0 := by
  rcases ha0 with h0 | h2
  · simp [h0]
  · simp [h2, h.1]

theorem r2_over_eq_of_shared_over (C D : Crossing) (col : Nat → Int)
    (hC : ColoringRule C col) (hD : ColoringRule D col) {p : Nat}
    (hpC : p = C.a0 ∨ p = C.a2) (hpD : p = D.a0 ∨ p = D.a2) :
    col C.a0 = col D.a0 := by
  have h1 := hC.over_of_mem hpC
  have h2 := hD.over_of_mem hpD
  linarith

theorem IsR2Pair.over_color_eq {C D : Crossing} {col : Nat → Int}
    (h : IsR2Pair C D) (hC : ColoringRule C col) (hD : ColoringRule D col) :
    col C.a0 = col D.a0 := by
  obtain ⟨_, _, _, p, q, hpq, hpC, hqC, hpD, hqD, _, hcompat⟩ := h
  rcases hcompat with hp | hq
  · exact r2_over_eq_of_shared_over C D col hC hD hp.1 hp.2.1
  · exact r2_over_eq_of_shared_over C D col hC hD hq.1 hq.2.1

theorem coloring_reidemeister_II_remove (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIIAdd E D) (hc : D.IsColored col) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨i, j, hij, hpair, hiso⟩ := h
  have hCi : ColoringRule D.crossings[i] col := hc _ (List.getElem_mem _)
  have hCj : ColoringRule D.crossings[j] col := hc _ (List.getElem_mem _)
  have hβ := hpair.over_color_eq hCi hCj
  obtain ⟨hcol, hsame₁⟩ := IsColored_collapseR2 D i j col hc hβ
  obtain ⟨col', hE, hsame₂⟩ :=
    coloring_planar_isotopy_backward E (collapseR2 D i.val j.val) col hiso hcol
  refine ⟨col', hE, ?_⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := hsame₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := hsame₂
  exact ⟨a₂.symm.trans a₁, b₂.symm.trans b₁, c₂.symm.trans c₁, d₂.symm.trans d₁⟩


/-! ## oppositeArc -/

theorem oppositeArc_a0 (C : Crossing) : C.oppositeArc C.a0 = C.a2 := by
  simp [Crossing.oppositeArc, Crossing.portOf]

theorem Fin.add_two_ne_self (p : Fin 4) : p ≠ p + 2 := by
  intro h
  have hv : p.val = (p.val + 2) % 4 := by
    simpa [Fin.val_add] using congrArg Fin.val h
  have : p.val < 4 := p.isLt
  omega

/-! ## R2 pair: shared over / shared under -/

theorem IsR2Pair.shared_over_under {C D : Crossing} (h : IsR2Pair C D) :
    ∃ p q : Nat, p ≠ q ∧
      C.memArc p ∧ D.memArc p ∧ C.memArc q ∧ D.memArc q ∧
      C.isOverArc p ∧ D.isOverArc p ∧ C.isUnderArc q ∧ D.isUnderArc q ∧
      (∀ a : Nat, (C.memArc a ∧ D.memArc a) → a = p ∨ a = q) := by
  obtain ⟨_, _, _, p, q, hpq, hpC, hqC, hpD, hqD, honly, hcompat⟩ := h
  rcases hcompat with h | h
  · exact ⟨p, q, hpq, hpC, hpD, hqC, hqD, h.1, h.2.1, h.2.2.1, h.2.2.2, honly⟩
  · refine ⟨q, p, hpq.symm, hqC, hqD, hpC, hpD, h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
    intro a ha
    rcases honly a ha with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

theorem crossing_end_mem_endsOf_eq (D : TangleDiagram) (i : Fin D.crossings.length)
    (p : Fin 4) {a : Nat} (h : D.crossings[i].arcs p = a) :
    TangleDiagram.ArcEnd.crossing i.val p ∈ D.endsOf a := by
  have := crossing_end_mem_endsOf D i p
  rwa [h] at this

theorem r2_shared_two_ends (D : TangleDiagram) (i j : Fin D.crossings.length)
    (hij : i ≠ j) {p : Nat}
    (hpC : D.crossings[i].memArc p) (hpD : D.crossings[j].memArc p) :
    ∃ (pi pj : Fin 4),
      TangleDiagram.ArcEnd.crossing i.val pi ∈ D.endsOf p ∧
      TangleDiagram.ArcEnd.crossing j.val pj ∈ D.endsOf p ∧
      TangleDiagram.ArcEnd.crossing i.val pi ≠
        TangleDiagram.ArcEnd.crossing j.val pj := by
  obtain ⟨pi, hpi⟩ := memArc_port D.crossings[i] hpC
  obtain ⟨pj, hpj⟩ := memArc_port D.crossings[j] hpD
  refine ⟨pi, pj, crossing_end_mem_endsOf_eq D i pi hpi,
    crossing_end_mem_endsOf_eq D j pj hpj, ?_⟩
  intro h
  injection h with hij' _
  exact hij (Fin.eq_of_val_eq hij')

theorem r2_three_ends_false (D : TangleDiagram) {p : Nat}
    {e1 e2 e3 : TangleDiagram.ArcEnd}
    (he1 : e1 ∈ D.endsOf p) (he2 : e2 ∈ D.endsOf p) (he3 : e3 ∈ D.endsOf p)
    (h12 : e1 ≠ e2) (h23 : e2 ≠ e3) (h13 : e1 ≠ e3)
    (h2 : (D.endsOf p).length = 2) : False := by
  have : 3 ≤ (D.endsOf p).length :=
    length_ge_three_of_distinct_mem he1 he2 he3 h12 h23 h13
  omega

theorem r2_wf_len2 (D : TangleDiagram) (i j : Fin D.crossings.length)
    (hij : i ≠ j) {p : Nat} (hw : D.WellFormed)
    (hpC : D.crossings[i].memArc p) (hpD : D.crossings[j].memArc p) :
    (D.endsOf p).length = 2 := by
  obtain ⟨pi, pj, he1, he2, _⟩ := r2_shared_two_ends D i j hij hpC hpD
  have hpos : 0 < (D.endsOf p).length := List.length_pos_of_mem he1
  have hwf := hw p
  cases hwf with
  | inl h0 => omega
  | inr h2 => exact h2

theorem r2_not_two_ports_and_other (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) {p : Nat}
    (h2 : (E.endsOf p).length = 2)
    {p1 p2 : Fin 4} (hne : p1 ≠ p2)
    (he1 : TangleDiagram.ArcEnd.crossing i.val p1 ∈ E.endsOf p)
    (he2 : TangleDiagram.ArcEnd.crossing i.val p2 ∈ E.endsOf p)
    (hpD : E.crossings[j].memArc p) : False := by
  obtain ⟨pj, hpj⟩ := memArc_port E.crossings[j] hpD
  have he3 := crossing_end_mem_endsOf_eq E j pj hpj
  have h12 : TangleDiagram.ArcEnd.crossing i.val p1 ≠
      TangleDiagram.ArcEnd.crossing i.val p2 := by
    intro h; injection h with _ hp; exact hne hp
  have h13 : TangleDiagram.ArcEnd.crossing i.val p1 ≠
      TangleDiagram.ArcEnd.crossing j.val pj := by
    intro h; injection h with hji _; exact hij (Fin.eq_of_val_eq hji)
  have h23 : TangleDiagram.ArcEnd.crossing i.val p2 ≠
      TangleDiagram.ArcEnd.crossing j.val pj := by
    intro h; injection h with hji _; exact hij (Fin.eq_of_val_eq hji)
  exact r2_three_ends_false E he1 he2 he3 h12 h23 h13 h2

/-- The overstrand of an R2 pair occupies exactly one port at `C`; the
    opposite over-port is external. -/
theorem r2_other_over_not_shared (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q) :
    (E.crossings[i].a0 = p ∧ ¬ E.crossings[j].memArc E.crossings[i].a2) ∨
      (E.crossings[i].a2 = p ∧ ¬ E.crossings[j].memArc E.crossings[i].a0) := by
  have hlenp := r2_wf_len2 E i j hij hw hpC hpD
  have hlenq := r2_wf_len2 E i j hij hw hqC hqD
  have hnot_both : ¬ (E.crossings[i].a0 = p ∧ E.crossings[i].a2 = p) := by
    intro ⟨h0, h2⟩
    exact r2_not_two_ports_and_other E i j hij hlenp
      (by decide : (0 : Fin 4) ≠ 2)
      (crossing_end_mem_endsOf_eq E i 0 h0)
      (crossing_end_mem_endsOf_eq E i 2 h2)
      hpD
  rcases hover with h0 | h2
  · refine Or.inl ⟨h0.symm, ?_⟩
    intro hmem
    have hx := honly E.crossings[i].a2 ⟨Or.inr (Or.inr (Or.inl rfl)), hmem⟩
    rcases hx with h2p | h2q
    · exact hnot_both ⟨h0.symm, h2p⟩
    · rcases hunder with hq1 | hq3
      · exact r2_not_two_ports_and_other E i j hij hlenq
          (by decide : (1 : Fin 4) ≠ 2)
          (crossing_end_mem_endsOf_eq E i 1 hq1.symm)
          (crossing_end_mem_endsOf_eq E i 2 h2q)
          hqD
      · exact r2_not_two_ports_and_other E i j hij hlenq
          (by decide : (2 : Fin 4) ≠ 3)
          (crossing_end_mem_endsOf_eq E i 2 h2q)
          (crossing_end_mem_endsOf_eq E i 3 hq3.symm)
          hqD
  · refine Or.inr ⟨h2.symm, ?_⟩
    intro hmem
    have hx := honly E.crossings[i].a0 ⟨Or.inl rfl, hmem⟩
    rcases hx with h0p | h0q
    · exact hnot_both ⟨h0p, h2.symm⟩
    · rcases hunder with hq1 | hq3
      · exact r2_not_two_ports_and_other E i j hij hlenq
          (by decide : (0 : Fin 4) ≠ 1)
          (crossing_end_mem_endsOf_eq E i 0 h0q)
          (crossing_end_mem_endsOf_eq E i 1 hq1.symm)
          hqD
      · exact r2_not_two_ports_and_other E i j hij hlenq
          (by decide : (0 : Fin 4) ≠ 3)
          (crossing_end_mem_endsOf_eq E i 0 h0q)
          (crossing_end_mem_endsOf_eq E i 3 hq3.symm)
          hqD

def r2OverColor (C D : Crossing) (col' : Nat → Int) : Int :=
  if memArcB D C.a0 then col' (r2Merge C D C.a2) else col' (r2Merge C D C.a0)

def colorAddR2CD (C D : Crossing) (col' : Nat → Int) (a : Nat) : Int :=
  if memArcB C a && memArcB D a then
    if a = C.a0 ∨ a = C.a2 then
      r2OverColor C D col'
    else
      2 * r2OverColor C D col' -
        col' (r2Merge C D (if a = C.a1 then C.a3 else C.a1))
  else
    col' (r2Merge C D a)

def colorAddR2 (E : TangleDiagram) (i j : Fin E.crossings.length)
    (col' : Nat → Int) (a : Nat) : Int :=
  colorAddR2CD E.crossings[i] E.crossings[j] col' a

theorem colorAddR2CD_unshared {C D : Crossing} {col' : Nat → Int} {a : Nat}
    (h : ¬ (C.memArc a ∧ D.memArc a)) :
    colorAddR2CD C D col' a = col' (r2Merge C D a) := by
  simp [colorAddR2CD]
  intro hC hD
  simp [memArcB_iff] at hC hD
  exact (h ⟨hC, hD⟩).elim

theorem colorAddR2_unshared {E : TangleDiagram} {i j : Fin E.crossings.length}
    {col' : Nat → Int} {a : Nat}
    (h : ¬ (E.crossings[i].memArc a ∧ E.crossings[j].memArc a)) :
    colorAddR2 E i j col' a =
      col' (r2Merge E.crossings[i] E.crossings[j] a) :=
  colorAddR2CD_unshared h

theorem oppositeArc_a2_of_ne (C : Crossing) (h0 : C.a0 ≠ C.a2) (h1 : C.a1 ≠ C.a2) :
    C.oppositeArc C.a2 = C.a0 := by
  unfold Crossing.oppositeArc Crossing.portOf
  split_ifs <;> (try contradiction)
  rfl

theorem oppositeArc_a1_of_ne (C : Crossing)
    (h0 : C.a0 ≠ C.a1) (h2 : C.a2 ≠ C.a1) :
    C.oppositeArc C.a1 = C.a3 := by
  unfold Crossing.oppositeArc Crossing.portOf
  split_ifs <;> (try contradiction)
  rfl

theorem oppositeArc_a3_of_ne (C : Crossing)
    (h0 : C.a0 ≠ C.a3) (h1 : C.a1 ≠ C.a3) (h2 : C.a2 ≠ C.a3) :
    C.oppositeArc C.a3 = C.a1 := by
  unfold Crossing.oppositeArc Crossing.portOf
  split_ifs <;> (try contradiction)
  rfl

theorem IsR2Pair.adjC {C D : Crossing} (h : IsR2Pair C D) : C.adjacentDistinct :=
  h.2.1

theorem IsR2Pair.adjD {C D : Crossing} (h : IsR2Pair C D) : D.adjacentDistinct :=
  h.2.2.1

theorem colorAddR2_of_shared {E : TangleDiagram} {i j : Fin E.crossings.length}
    {a : Nat}
    (h : E.crossings[i].memArc a ∧ E.crossings[j].memArc a) :
    memArcB E.crossings[i] a = true ∧ memArcB E.crossings[j] a = true :=
  ⟨(memArcB_iff _ _).2 h.1, (memArcB_iff _ _).2 h.2⟩

theorem colorAddR2CD_shared_over {C D : Crossing} {col' : Nat → Int} {a : Nat}
    (h : C.memArc a ∧ D.memArc a)
    (hover : a = C.a0 ∨ a = C.a2) :
    colorAddR2CD C D col' a = r2OverColor C D col' := by
  have hi : memArcB C a = true := (memArcB_iff _ _).2 h.1
  have hj : memArcB D a = true := (memArcB_iff _ _).2 h.2
  simp [colorAddR2CD, hi, hj, hover]

theorem colorAddR2_shared_over {E : TangleDiagram} {i j : Fin E.crossings.length}
    {col' : Nat → Int} {a : Nat}
    (h : E.crossings[i].memArc a ∧ E.crossings[j].memArc a)
    (hover : a = E.crossings[i].a0 ∨ a = E.crossings[i].a2) :
    colorAddR2 E i j col' a =
      r2OverColor E.crossings[i] E.crossings[j] col' :=
  colorAddR2CD_shared_over h hover

theorem colorAddR2CD_shared_under {C D : Crossing} {col' : Nat → Int} {a : Nat}
    (h : C.memArc a ∧ D.memArc a)
    (h0 : a ≠ C.a0) (h2 : a ≠ C.a2) :
    colorAddR2CD C D col' a =
      2 * r2OverColor C D col' -
        col' (r2Merge C D (if a = C.a1 then C.a3 else C.a1)) := by
  have hi : memArcB C a = true := (memArcB_iff _ _).2 h.1
  have hj : memArcB D a = true := (memArcB_iff _ _).2 h.2
  have hover : ¬ (a = C.a0 ∨ a = C.a2) := by
    intro h; rcases h with h | h <;> contradiction
  simp [colorAddR2CD, hi, hj, hover]

theorem colorAddR2_shared_under {E : TangleDiagram} {i j : Fin E.crossings.length}
    {col' : Nat → Int} {a : Nat}
    (h : E.crossings[i].memArc a ∧ E.crossings[j].memArc a)
    (h0 : a ≠ E.crossings[i].a0) (h2 : a ≠ E.crossings[i].a2) :
    colorAddR2 E i j col' a =
      2 * r2OverColor E.crossings[i] E.crossings[j] col' -
        col' (r2Merge E.crossings[i] E.crossings[j]
          (if a = E.crossings[i].a1 then E.crossings[i].a3
            else E.crossings[i].a1)) :=
  colorAddR2CD_shared_under h h0 h2

theorem r2_not_mem_third (E : TangleDiagram) (i j : Fin E.crossings.length)
    (hij : i ≠ j) {p : Nat} (hw : E.WellFormed)
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    {k : Fin E.crossings.length} (hki : k ≠ i) (hkj : k ≠ j) :
    ¬ E.crossings[k].memArc p := by
  intro hmem
  have hlen := r2_wf_len2 E i j hij hw hpC hpD
  obtain ⟨pi, pj, he1, he2, hne12⟩ := r2_shared_two_ends E i j hij hpC hpD
  obtain ⟨pk, hpk⟩ := memArc_port E.crossings[k] hmem
  have he3 := crossing_end_mem_endsOf_eq E k pk hpk
  have h13 : TangleDiagram.ArcEnd.crossing i.val pi ≠
      TangleDiagram.ArcEnd.crossing k.val pk := by
    intro h; injection h with hki' _; exact hki (Fin.eq_of_val_eq hki'.symm)
  have h23 : TangleDiagram.ArcEnd.crossing j.val pj ≠
      TangleDiagram.ArcEnd.crossing k.val pk := by
    intro h; injection h with hkj' _; exact hkj (Fin.eq_of_val_eq hkj'.symm)
  exact r2_three_ends_false E he1 he2 he3 hne12 h23 h13 hlen

theorem r2_shared_not_boundary (E : TangleDiagram) (i j : Fin E.crossings.length)
    (hij : i ≠ j) {p : Nat} (hw : E.WellFormed)
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (e : Endpoint) : E.boundary e ≠ p := by
  intro heq
  have hlen := r2_wf_len2 E i j hij hw hpC hpD
  obtain ⟨pi, pj, he1, he2, hne12⟩ := r2_shared_two_ends E i j hij hpC hpD
  have he3 : TangleDiagram.ArcEnd.boundary e ∈ E.endsOf p := by
    simpa [heq] using boundary_end_mem_endsOf E e
  have h13 : TangleDiagram.ArcEnd.crossing i.val pi ≠
      TangleDiagram.ArcEnd.boundary e := by intro h; cases h
  have h23 : TangleDiagram.ArcEnd.crossing j.val pj ≠
      TangleDiagram.ArcEnd.boundary e := by intro h; cases h
  exact r2_three_ends_false E he1 he2 he3 hne12 h23 h13 hlen


theorem mem_eraseTwo_of_ne {D : TangleDiagram} (i j : Fin D.crossings.length)
    {X : Crossing} (hX : X ∈ D.crossings)
    (hXi : X ≠ D.crossings[i]) (hXj : X ≠ D.crossings[j]) :
    X ∈ (eraseTwo D i.val j.val).crossings := by
  unfold eraseTwo TangleDiagram.eraseCrossing
  have hjlt := j.isLt
  have hilt := i.isLt
  split_ifs with hlt hgt
  · have hmemj : X ∈ D.crossings.eraseIdx j.val := by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hX
      refine (List.mem_eraseIdx_iff_getElem (l := D.crossings)).2
        ⟨k, hk, ?_, rfl⟩
      intro hkj
      apply hXj
      simp [hkj]
    obtain ⟨k2, hk2, hget⟩ := List.mem_iff_getElem.mp hmemj
    refine (List.mem_eraseIdx_iff_getElem (l := D.crossings.eraseIdx j.val)).2
      ⟨k2, hk2, ?_, hget⟩
    intro hki
    subst hki
    apply hXi
    have hi_lt : i.val < (D.crossings.eraseIdx j.val).length := hk2
    have hgeti : (D.crossings.eraseIdx j.val)[i.val]'(hi_lt) = D.crossings[i] := by
      simp [List.getElem_eraseIdx, hlt]
    exact hget.symm.trans hgeti
  · have hmemi : X ∈ D.crossings.eraseIdx i.val := by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hX
      refine (List.mem_eraseIdx_iff_getElem (l := D.crossings)).2
        ⟨k, hk, ?_, rfl⟩
      intro hki
      apply hXi
      simp [hki]
    obtain ⟨k2, hk2, hget⟩ := List.mem_iff_getElem.mp hmemi
    refine (List.mem_eraseIdx_iff_getElem (l := D.crossings.eraseIdx i.val)).2
      ⟨k2, hk2, ?_, hget⟩
    intro hkj
    subst hkj
    apply hXj
    have hj_lt : j.val < (D.crossings.eraseIdx i.val).length := hk2
    have hgetj : (D.crossings.eraseIdx i.val)[j.val]'(hj_lt) = D.crossings[j] := by
      simp [List.getElem_eraseIdx, hgt]
    exact hget.symm.trans hgetj
  · have heq : i.val = j.val := by omega
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hX
    refine (List.mem_eraseIdx_iff_getElem (l := D.crossings)).2
      ⟨k, hk, ?_, rfl⟩
    intro hki
    apply hXi
    simp [hki]


theorem r2OverColor_a0_shared {C D : Crossing} (col' : Nat → Int)
    (h : D.memArc C.a0) :
    r2OverColor C D col' = col' (r2Merge C D C.a2) := by
  unfold r2OverColor
  simp [memArcB_iff, h]

theorem r2OverColor_a0_unshared {C D : Crossing} (col' : Nat → Int)
    (h : ¬ D.memArc C.a0) :
    r2OverColor C D col' = col' (r2Merge C D C.a0) := by
  unfold r2OverColor
  simp [memArcB_iff, h]

theorem r2Merge_id_not_C {C D : Crossing} {a : Nat} (hC : ¬ C.memArc a) :
    r2Merge C D a = a := by
  unfold r2Merge
  simp [memArcB_iff, hC]

theorem r2Merge_external {C D : Crossing} {a : Nat}
    (hC : C.memArc a) (hD : ¬ D.memArc a)
    (hOpp : D.memArc (C.oppositeArc a)) :
    r2Merge C D a = D.oppositeArc (C.oppositeArc a) := by
  unfold r2Merge
  simp [memArcB_iff, hC, hD, hOpp]

theorem r2_ne_ports_of_shared (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    {s : Nat}
    (hsC : E.crossings[i].memArc s) (hsD : E.crossings[j].memArc s)
    (p1 p2 : Fin 4)
    (h1 : E.crossings[i].arcs p1 = s) (h2 : E.crossings[i].arcs p2 = s) :
    p1 = p2 := by
  by_contra hne
  have hlen := r2_wf_len2 E i j hij hw hsC hsD
  exact r2_not_two_ports_and_other E i j hij hlen hne
    (crossing_end_mem_endsOf_eq E i p1 h1)
    (crossing_end_mem_endsOf_eq E i p2 h2)
    hsD

theorem colorAddR2_overs_of_a0_shared {E : TangleDiagram}
    (i j : Fin E.crossings.length) (col' : Nat → Int) {p : Nat}
    (hp : E.crossings[i].a0 = p)
    (hpD : E.crossings[j].memArc p)
    (ha2 : ¬ E.crossings[j].memArc E.crossings[i].a2) :
    colorAddR2 E i j col' E.crossings[i].a0 =
      r2OverColor E.crossings[i] E.crossings[j] col' ∧
    colorAddR2 E i j col' E.crossings[i].a2 =
      r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hpD0 : E.crossings[j].memArc E.crossings[i].a0 := by
    rw [hp]; exact hpD
  have h0s : E.crossings[i].memArc E.crossings[i].a0 ∧
      E.crossings[j].memArc E.crossings[i].a0 :=
    ⟨Or.inl rfl, hpD0⟩
  have h2u : ¬ (E.crossings[i].memArc E.crossings[i].a2 ∧
      E.crossings[j].memArc E.crossings[i].a2) := fun h => ha2 h.2
  have c0 := colorAddR2_shared_over (E := E) (i := i) (j := j) (col' := col')
    (a := E.crossings[i].a0) h0s (Or.inl rfl)
  have c2 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
    (a := E.crossings[i].a2) h2u
  have hβ := r2OverColor_a0_shared (C := E.crossings[i]) (D := E.crossings[j])
    col' hpD0
  exact ⟨c0, c2.trans hβ.symm⟩

theorem colorAddR2_overs_of_a2_shared {E : TangleDiagram}
    (i j : Fin E.crossings.length) (col' : Nat → Int) {p : Nat}
    (hp : E.crossings[i].a2 = p)
    (hpD : E.crossings[j].memArc p)
    (ha0 : ¬ E.crossings[j].memArc E.crossings[i].a0) :
    colorAddR2 E i j col' E.crossings[i].a0 =
      r2OverColor E.crossings[i] E.crossings[j] col' ∧
    colorAddR2 E i j col' E.crossings[i].a2 =
      r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hpD2 : E.crossings[j].memArc E.crossings[i].a2 := by
    rw [hp]; exact hpD
  have h0u : ¬ (E.crossings[i].memArc E.crossings[i].a0 ∧
      E.crossings[j].memArc E.crossings[i].a0) := fun h => ha0 h.2
  have h2s : E.crossings[i].memArc E.crossings[i].a2 ∧
      E.crossings[j].memArc E.crossings[i].a2 :=
    ⟨Or.inr (Or.inr (Or.inl rfl)), hpD2⟩
  have c0 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
    (a := E.crossings[i].a0) h0u
  have c2 := colorAddR2_shared_over (E := E) (i := i) (j := j) (col' := col')
    (a := E.crossings[i].a2) h2s (Or.inr rfl)
  have hβ := r2OverColor_a0_unshared (C := E.crossings[i]) (D := E.crossings[j])
    col' ha0
  exact ⟨c0.trans hβ.symm, c2⟩

theorem r2_other_under_not_shared (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q) :
    (E.crossings[i].a1 = q ∧ ¬ E.crossings[j].memArc E.crossings[i].a3) ∨
      (E.crossings[i].a3 = q ∧ ¬ E.crossings[j].memArc E.crossings[i].a1) := by
  have hlenp := r2_wf_len2 E i j hij hw hpC hpD
  have hlenq := r2_wf_len2 E i j hij hw hqC hqD
  have hnot_both : ¬ (E.crossings[i].a1 = q ∧ E.crossings[i].a3 = q) := by
    intro ⟨h1, h3⟩
    exact r2_not_two_ports_and_other E i j hij hlenq
      (by decide : (1 : Fin 4) ≠ 3)
      (crossing_end_mem_endsOf_eq E i 1 h1)
      (crossing_end_mem_endsOf_eq E i 3 h3)
      hqD
  rcases hunder with h1 | h3
  · refine Or.inl ⟨h1.symm, ?_⟩
    intro hmem
    have hx := honly E.crossings[i].a3 ⟨Or.inr (Or.inr (Or.inr rfl)), hmem⟩
    rcases hx with h3p | h3q
    · rcases hover with hp0 | hp2
      · exact r2_not_two_ports_and_other E i j hij hlenp
          (by decide : (0 : Fin 4) ≠ 3)
          (crossing_end_mem_endsOf_eq E i 0 hp0.symm)
          (crossing_end_mem_endsOf_eq E i 3 h3p)
          hpD
      · exact r2_not_two_ports_and_other E i j hij hlenp
          (by decide : (2 : Fin 4) ≠ 3)
          (crossing_end_mem_endsOf_eq E i 2 hp2.symm)
          (crossing_end_mem_endsOf_eq E i 3 h3p)
          hpD
    · exact hnot_both ⟨h1.symm, h3q⟩
  · refine Or.inr ⟨h3.symm, ?_⟩
    intro hmem
    have hx := honly E.crossings[i].a1 ⟨Or.inr (Or.inl rfl), hmem⟩
    rcases hx with h1p | h1q
    · rcases hover with hp0 | hp2
      · exact r2_not_two_ports_and_other E i j hij hlenp
          (by decide : (0 : Fin 4) ≠ 1)
          (crossing_end_mem_endsOf_eq E i 0 hp0.symm)
          (crossing_end_mem_endsOf_eq E i 1 h1p)
          hpD
      · exact r2_not_two_ports_and_other E i j hij hlenp
          (by decide : (1 : Fin 4) ≠ 2)
          (crossing_end_mem_endsOf_eq E i 1 h1p)
          (crossing_end_mem_endsOf_eq E i 2 hp2.symm)
          hpD
    · exact hnot_both ⟨h1q, h3.symm⟩

theorem r2_over_ports_color (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q) :
    colorAddR2 E i j col' E.crossings[i].a0 =
      r2OverColor E.crossings[i] E.crossings[j] col' ∧
    colorAddR2 E i j col' E.crossings[i].a2 =
      r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hover' := r2_other_over_not_shared E i j hij hw hpC hpD hqC hqD
    hover hunder honly
  rcases hover' with ⟨h0, ha2⟩ | ⟨h2, ha0⟩
  · exact colorAddR2_overs_of_a0_shared i j col' h0 hpD ha2
  · exact colorAddR2_overs_of_a2_shared i j col' h2 hpD ha0

theorem r2_q_not_over (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (hpq : p ≠ q) :
    q ≠ E.crossings[i].a0 ∧ q ≠ E.crossings[i].a2 := by
  constructor
  · intro h
    rcases hunder with hu1 | hu3
    · exact (by decide : (0 : Fin 4) ≠ 1) (r2_ne_ports_of_shared E i j hij hw hqC hqD 0 1
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using hu1.symm))
    · exact (by decide : (0 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 0 3
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using hu3.symm))
  · intro h
    rcases hunder with hu1 | hu3
    · exact (by decide : (2 : Fin 4) ≠ 1) (r2_ne_ports_of_shared E i j hij hw hqC hqD 2 1
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using hu1.symm))
    · exact (by decide : (2 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 2 3
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using hu3.symm))

theorem r2_under_ports_sum (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q)
    (hpq : p ≠ q) :
    colorAddR2 E i j col' E.crossings[i].a1 +
      colorAddR2 E i j col' E.crossings[i].a3 =
      2 * r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hunder' := r2_other_under_not_shared E i j hij hw hpC hpD hqC hqD
    hover hunder honly
  have qno := r2_q_not_over E i j hij hw hpC hpD hqC hqD hover hunder hpq
  have hqs : E.crossings[i].memArc q ∧ E.crossings[j].memArc q := ⟨hqC, hqD⟩
  rcases hunder' with ⟨h1q, ha3⟩ | ⟨h3q, ha1⟩
  · have cq := colorAddR2_shared_under (E := E) (i := i) (j := j) (col' := col')
      (a := q) hqs qno.1 qno.2
    have h3u : ¬ (E.crossings[i].memArc E.crossings[i].a3 ∧
        E.crossings[j].memArc E.crossings[i].a3) := fun h => ha3 h.2
    have c3 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[i].a3) h3u
    have hif : (if q = E.crossings[i].a1 then E.crossings[i].a3
        else E.crossings[i].a1) = E.crossings[i].a3 := if_pos h1q.symm
    rw [hif] at cq
    rw [← h1q] at cq
    rw [cq, c3]
    ring
  · have cq := colorAddR2_shared_under (E := E) (i := i) (j := j) (col' := col')
      (a := q) hqs qno.1 qno.2
    have h1u : ¬ (E.crossings[i].memArc E.crossings[i].a1 ∧
        E.crossings[j].memArc E.crossings[i].a1) := fun h => ha1 h.2
    have c1 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[i].a1) h1u
    have hne : q ≠ E.crossings[i].a1 := by
      intro h
      exact (by decide : (1 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 1 3
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using h3q))
    have hif : (if q = E.crossings[i].a1 then E.crossings[i].a3
        else E.crossings[i].a1) = E.crossings[i].a1 := if_neg hne
    rw [hif] at cq
    rw [← h3q] at cq
    rw [cq, c1]
    ring

theorem colorAddR2_ColoringRule_first (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) (hpair : IsR2Pair E.crossings[i] E.crossings[j]) :
    ColoringRule E.crossings[i] (colorAddR2 E i j col') := by
  obtain ⟨p, q, hpq, hpC, hpD, hqC, hqD, hoverC, hoverD, hunderC, hunderD, honly⟩ :=
    hpair.shared_over_under
  have hovers := r2_over_ports_color E i j hij hw col' hpC hpD hqC hqD
    hoverC hunderC honly
  have hunders := r2_under_ports_sum E i j hij hw col' hpC hpD hqC hqD
    hoverC hunderC honly hpq
  constructor
  · exact hovers.1.trans hovers.2.symm
  · rwa [hovers.1]

theorem r2_shared_over_color (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hover : E.crossings[i].isOverArc p) (hunder : E.crossings[i].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q) :
    colorAddR2 E i j col' p =
      r2OverColor E.crossings[i] E.crossings[j] col' := by
  exact colorAddR2_shared_over ⟨hpC, hpD⟩ hover

theorem r2_C_a0_ne_a2 (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    {p : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (h0 : E.crossings[i].a0 = p)
    (ha2 : ¬ E.crossings[j].memArc E.crossings[i].a2) :
    E.crossings[i].a0 ≠ E.crossings[i].a2 := by
  intro h
  exact ha2 (by rwa [← h, h0])

set_option maxHeartbeats 800000 in
theorem r2_D_over_ports_color (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) (hpair : IsR2Pair E.crossings[i] E.crossings[j])
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hoverC : E.crossings[i].isOverArc p) (hoverD : E.crossings[j].isOverArc p)
    (hunderC : E.crossings[i].isUnderArc q) (hunderD : E.crossings[j].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q) :
    colorAddR2 E i j col' E.crossings[j].a0 =
      r2OverColor E.crossings[i] E.crossings[j] col' ∧
    colorAddR2 E i j col' E.crossings[j].a2 =
      r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hadjC := hpair.adjC
  have hadjD := hpair.adjD
  have hij' : j ≠ i := hij.symm
  have honly' : ∀ a : Nat,
      (E.crossings[j].memArc a ∧ E.crossings[i].memArc a) → a = p ∨ a = q := by
    intro a ha; exact honly a ⟨ha.2, ha.1⟩
  have hoverD' := r2_other_over_not_shared E j i hij' hw hpD hpC hqD hqC
    hoverD hunderD honly'
  have hoverC' := r2_other_over_not_shared E i j hij hw hpC hpD hqC hqD
    hoverC hunderC honly
  have hpcol := r2_shared_over_color E i j hij hw col' hpC hpD hqC hqD
    hoverC hunderC honly
  have hC0ne2 : E.crossings[i].a0 ≠ E.crossings[i].a2 := by
    rcases hoverC' with ⟨h0, ha2⟩ | ⟨h2, ha0⟩
    · intro h; exact ha2 (by rwa [← h, h0])
    · intro h; exact ha0 (by rwa [h, h2])
  have hD0ne2 : E.crossings[j].a0 ≠ E.crossings[j].a2 := by
    rcases hoverD' with ⟨h0, ha2⟩ | ⟨h2, ha0⟩
    · intro h; exact ha2 (by rwa [← h, h0])
    · intro h; exact ha0 (by rwa [h, h2])
  rcases hoverD' with ⟨hD0, hCnot2⟩ | ⟨hD2, hCnot0⟩
  · -- D.a0 = p, D.a2 external
    have h2u : ¬ (E.crossings[i].memArc E.crossings[j].a2 ∧
        E.crossings[j].memArc E.crossings[j].a2) := fun h => hCnot2 h.1
    have c2 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[j].a2) h2u
    have hmerge2 : r2Merge E.crossings[i] E.crossings[j] E.crossings[j].a2 =
        E.crossings[j].a2 := r2Merge_id_not_C hCnot2
    have hβ : r2OverColor E.crossings[i] E.crossings[j] col' =
        col' E.crossings[j].a2 := by
      rcases hoverC' with ⟨hC0, hDnot2⟩ | ⟨hC2, hDnot0⟩
      · have hβ0 := r2OverColor_a0_shared (C := E.crossings[i])
          (D := E.crossings[j]) col' (by rwa [hC0])
        have hopp := oppositeArc_a2_of_ne E.crossings[i] (by
          intro h; exact hDnot2 (by rwa [← h, hC0])) hadjC.2.1
        have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
          (a := E.crossings[i].a2) (Or.inr (Or.inr (Or.inl rfl))) hDnot2
          (by rw [hopp, hC0]; exact hpD)
        have hoppD := oppositeArc_a0 E.crossings[j]
        calc
          r2OverColor E.crossings[i] E.crossings[j] col'
              = col' (r2Merge E.crossings[i] E.crossings[j]
                  E.crossings[i].a2) := hβ0
          _ = col' (E.crossings[j].oppositeArc
                (E.crossings[i].oppositeArc E.crossings[i].a2)) := by rw [hm]
          _ = col' (E.crossings[j].oppositeArc E.crossings[i].a0) := by rw [hopp]
          _ = col' (E.crossings[j].oppositeArc p) := by rw [hC0]
          _ = col' (E.crossings[j].oppositeArc E.crossings[j].a0) := by rw [hD0]
          _ = col' E.crossings[j].a2 := by rw [hoppD]
      · have hβ0 := r2OverColor_a0_unshared (C := E.crossings[i])
          (D := E.crossings[j]) col' hDnot0
        have hopp := oppositeArc_a0 E.crossings[i]
        have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
          (a := E.crossings[i].a0) (Or.inl rfl) hDnot0
          (by rw [hopp, hC2]; exact hpD)
        have hoppD := oppositeArc_a0 E.crossings[j]
        calc
          r2OverColor E.crossings[i] E.crossings[j] col'
              = col' (r2Merge E.crossings[i] E.crossings[j]
                  E.crossings[i].a0) := hβ0
          _ = col' (E.crossings[j].oppositeArc
                (E.crossings[i].oppositeArc E.crossings[i].a0)) := by rw [hm]
          _ = col' (E.crossings[j].oppositeArc E.crossings[i].a2) := by rw [hopp]
          _ = col' (E.crossings[j].oppositeArc p) := by rw [hC2]
          _ = col' (E.crossings[j].oppositeArc E.crossings[j].a0) := by rw [hD0]
          _ = col' E.crossings[j].a2 := by rw [hoppD]
    constructor
    · simpa [hD0.symm] using hpcol
    · exact c2.trans (by rw [hmerge2, hβ])
  · -- D.a2 = p, D.a0 external
    have h0u : ¬ (E.crossings[i].memArc E.crossings[j].a0 ∧
        E.crossings[j].memArc E.crossings[j].a0) := fun h => hCnot0 h.1
    have c0 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[j].a0) h0u
    have hmerge0 : r2Merge E.crossings[i] E.crossings[j] E.crossings[j].a0 =
        E.crossings[j].a0 := r2Merge_id_not_C hCnot0
    have hoppD := oppositeArc_a2_of_ne E.crossings[j] hD0ne2 hadjD.2.1
    have hβ : r2OverColor E.crossings[i] E.crossings[j] col' =
        col' E.crossings[j].a0 := by
      rcases hoverC' with ⟨hC0, hDnot2⟩ | ⟨hC2, hDnot0⟩
      · have hβ0 := r2OverColor_a0_shared (C := E.crossings[i])
          (D := E.crossings[j]) col' (by rwa [hC0])
        have hopp := oppositeArc_a2_of_ne E.crossings[i] (by
          intro h; exact hDnot2 (by rwa [← h, hC0])) hadjC.2.1
        have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
          (a := E.crossings[i].a2) (Or.inr (Or.inr (Or.inl rfl))) hDnot2
          (by rw [hopp, hC0]; exact hpD)
        calc
          r2OverColor E.crossings[i] E.crossings[j] col'
              = col' (r2Merge E.crossings[i] E.crossings[j]
                  E.crossings[i].a2) := hβ0
          _ = col' (E.crossings[j].oppositeArc
                (E.crossings[i].oppositeArc E.crossings[i].a2)) := by rw [hm]
          _ = col' (E.crossings[j].oppositeArc E.crossings[i].a0) := by rw [hopp]
          _ = col' (E.crossings[j].oppositeArc p) := by rw [hC0]
          _ = col' (E.crossings[j].oppositeArc E.crossings[j].a2) := by rw [hD2]
          _ = col' E.crossings[j].a0 := by rw [hoppD]
      · have hβ0 := r2OverColor_a0_unshared (C := E.crossings[i])
          (D := E.crossings[j]) col' hDnot0
        have hopp := oppositeArc_a0 E.crossings[i]
        have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
          (a := E.crossings[i].a0) (Or.inl rfl) hDnot0
          (by rw [hopp, hC2]; exact hpD)
        calc
          r2OverColor E.crossings[i] E.crossings[j] col'
              = col' (r2Merge E.crossings[i] E.crossings[j]
                  E.crossings[i].a0) := hβ0
          _ = col' (E.crossings[j].oppositeArc
                (E.crossings[i].oppositeArc E.crossings[i].a0)) := by rw [hm]
          _ = col' (E.crossings[j].oppositeArc E.crossings[i].a2) := by rw [hopp]
          _ = col' (E.crossings[j].oppositeArc p) := by rw [hC2]
          _ = col' (E.crossings[j].oppositeArc E.crossings[j].a2) := by rw [hD2]
          _ = col' E.crossings[j].a0 := by rw [hoppD]
    constructor
    · exact c0.trans (by rw [hmerge0, hβ])
    · simpa [hD2.symm] using hpcol

theorem r2_merge_C_other_under (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (hpair : IsR2Pair E.crossings[i] E.crossings[j])
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hoverC : E.crossings[i].isOverArc p) (hunderC : E.crossings[i].isUnderArc q)
    (hunderD : E.crossings[j].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q)
    (hpq : p ≠ q) :
    r2Merge E.crossings[i] E.crossings[j]
        (if q = E.crossings[i].a1 then E.crossings[i].a3 else E.crossings[i].a1) =
      E.crossings[j].oppositeArc q := by
  have hadjC := hpair.adjC
  have hadjD := hpair.adjD
  have hij' : j ≠ i := hij.symm
  have honly' : ∀ a : Nat,
      (E.crossings[j].memArc a ∧ E.crossings[i].memArc a) → a = p ∨ a = q := by
    intro a ha; exact honly a ⟨ha.2, ha.1⟩
  have hunderC' := r2_other_under_not_shared E i j hij hw hpC hpD hqC hqD
    hoverC hunderC honly
  have hC1ne3 : E.crossings[i].a1 ≠ E.crossings[i].a3 := by
    intro h
    rcases hunderC' with ⟨h1q, _⟩ | ⟨h3q, _⟩
    · exact (by decide : (1 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 1 3
        (by simpa [Crossing.arcs] using h1q)
        (by simpa [Crossing.arcs] using h.symm.trans h1q))
    · exact (by decide : (1 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 1 3
        (by simpa [Crossing.arcs] using h.trans h3q)
        (by simpa [Crossing.arcs] using h3q))
  rcases hunderC' with ⟨hC1, hDnot3⟩ | ⟨hC3, hDnot1⟩
  · rw [if_pos hC1.symm]
    have hopp := oppositeArc_a3_of_ne E.crossings[i]
      hadjC.2.2.2.symm hC1ne3 hadjC.2.2.1
    have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
      (a := E.crossings[i].a3) (Or.inr (Or.inr (Or.inr rfl))) hDnot3
      (by rw [hopp, hC1]; exact hqD)
    exact hm.trans (congrArg (E.crossings[j].oppositeArc) (hopp.trans hC1))
  · have hne : q ≠ E.crossings[i].a1 := by
      intro h
      exact (by decide : (1 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E i j hij hw hqC hqD 1 3
        (by simpa [Crossing.arcs] using h.symm)
        (by simpa [Crossing.arcs] using hC3))
    rw [if_neg hne]
    have hopp := oppositeArc_a1_of_ne E.crossings[i] hadjC.1 hadjC.2.1.symm
    have hm := r2Merge_external (C := E.crossings[i]) (D := E.crossings[j])
      (a := E.crossings[i].a1) (Or.inr (Or.inl rfl)) hDnot1
      (by rw [hopp, hC3]; exact hqD)
    exact hm.trans (congrArg (E.crossings[j].oppositeArc) (hopp.trans hC3))

theorem r2_D_under_ports_sum (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) (hpair : IsR2Pair E.crossings[i] E.crossings[j])
    {p q : Nat}
    (hpC : E.crossings[i].memArc p) (hpD : E.crossings[j].memArc p)
    (hqC : E.crossings[i].memArc q) (hqD : E.crossings[j].memArc q)
    (hoverC : E.crossings[i].isOverArc p) (hoverD : E.crossings[j].isOverArc p)
    (hunderC : E.crossings[i].isUnderArc q) (hunderD : E.crossings[j].isUnderArc q)
    (honly : ∀ a : Nat, (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) →
      a = p ∨ a = q)
    (hpq : p ≠ q) :
    colorAddR2 E i j col' E.crossings[j].a1 +
      colorAddR2 E i j col' E.crossings[j].a3 =
      2 * r2OverColor E.crossings[i] E.crossings[j] col' := by
  have hadjD := hpair.adjD
  have hij' : j ≠ i := hij.symm
  have honly' : ∀ a : Nat,
      (E.crossings[j].memArc a ∧ E.crossings[i].memArc a) → a = p ∨ a = q := by
    intro a ha; exact honly a ⟨ha.2, ha.1⟩
  have hunderD' := r2_other_under_not_shared E j i hij' hw hpD hpC hqD hqC
    hoverD hunderD honly'
  have qno := r2_q_not_over E i j hij hw hpC hpD hqC hqD hoverC hunderC hpq
  have hqs : E.crossings[i].memArc q ∧ E.crossings[j].memArc q := ⟨hqC, hqD⟩
  have cq := colorAddR2_shared_under (E := E) (i := i) (j := j) (col' := col')
    (a := q) hqs qno.1 qno.2
  have hm := r2_merge_C_other_under E i j hij hw hpair hpC hpD hqC hqD
    hoverC hunderC hunderD honly hpq
  rw [hm] at cq
  rcases hunderD' with ⟨hD1, hCnot3⟩ | ⟨hD3, hCnot1⟩
  · have hoppD := oppositeArc_a1_of_ne E.crossings[j] hadjD.1 hadjD.2.1.symm
    have h3u : ¬ (E.crossings[i].memArc E.crossings[j].a3 ∧
        E.crossings[j].memArc E.crossings[j].a3) := fun h => hCnot3 h.1
    have c3 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[j].a3) h3u
    have hmerge3 : r2Merge E.crossings[i] E.crossings[j] E.crossings[j].a3 =
        E.crossings[j].a3 := r2Merge_id_not_C hCnot3
    rw [← hD1, hoppD] at cq
    rw [cq, c3, hmerge3]
    ring
  · have hoppD := oppositeArc_a3_of_ne E.crossings[j]
      hadjD.2.2.2.symm (by
        intro h
        exact (by decide : (1 : Fin 4) ≠ 3) (r2_ne_ports_of_shared E j i hij' hw hqD hqC 1 3
          (by simpa [Crossing.arcs] using h.trans hD3)
          (by simpa [Crossing.arcs] using hD3)))
      hadjD.2.2.1
    have h1u : ¬ (E.crossings[i].memArc E.crossings[j].a1 ∧
        E.crossings[j].memArc E.crossings[j].a1) := fun h => hCnot1 h.1
    have c1 := colorAddR2_unshared (E := E) (i := i) (j := j) (col' := col')
      (a := E.crossings[j].a1) h1u
    have hmerge1 : r2Merge E.crossings[i] E.crossings[j] E.crossings[j].a1 =
        E.crossings[j].a1 := r2Merge_id_not_C hCnot1
    rw [← hD3, hoppD] at cq
    rw [cq, c1, hmerge1]
    ring

theorem colorAddR2_ColoringRule_second (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) (hpair : IsR2Pair E.crossings[i] E.crossings[j]) :
    ColoringRule E.crossings[j] (colorAddR2 E i j col') := by
  obtain ⟨p, q, hpq, hpC, hpD, hqC, hqD, hoverC, hoverD, hunderC, hunderD, honly⟩ :=
    hpair.shared_over_under
  have hovers := r2_D_over_ports_color E i j hij hw col' hpair hpC hpD hqC hqD
    hoverC hoverD hunderC hunderD honly
  have hunders := r2_D_under_ports_sum E i j hij hw col' hpair hpC hpD hqC hqD
    hoverC hoverD hunderC hunderD honly hpq
  constructor
  · exact hovers.1.trans hovers.2.symm
  · rwa [hovers.1]

theorem colorAddR2_ColoringRule_other (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (col' : Nat → Int) (hpair : IsR2Pair E.crossings[i] E.crossings[j])
    (hc : (collapseR2 E i.val j.val).IsColored col')
    {X : Crossing} (hX : X ∈ E.crossings)
    (hXi : X ≠ E.crossings[i]) (hXj : X ≠ E.crossings[j]) :
    ColoringRule X (colorAddR2 E i j col') := by
  obtain ⟨p, q, hpq, hpC, hpD, hqC, hqD, hoverC, hoverD, hunderC, hunderD, honly⟩ :=
    hpair.shared_over_under
  have hXin := mem_eraseTwo_of_ne i j hX hXi hXj
  have hEq := collapseR2_eq E i j
  have herase :
      (eraseTwo E i.val j.val).IsColored
        (col' ∘ r2Merge E.crossings[i] E.crossings[j]) := by
    have : ((eraseTwo E i.val j.val).rename
        (r2Merge E.crossings[i] E.crossings[j])).IsColored col' := hEq ▸ hc
    exact (IsColored_rename _ _ _).1 this
  have hr := herase X hXin
  obtain ⟨k, hk, hXeq⟩ := List.mem_iff_getElem.mp hX
  have hki : (⟨k, hk⟩ : Fin E.crossings.length) ≠ i := by
    intro hk'
    apply hXi
    rw [← hXeq]
    cases hk'
    rfl
  have hkj : (⟨k, hk⟩ : Fin E.crossings.length) ≠ j := by
    intro hk'
    apply hXj
    rw [← hXeq]
    cases hk'
    rfl
  have hnp : ¬ X.memArc p := by
    intro hmem
    apply r2_not_mem_third (E := E) (i := i) (j := j) hij hw hpC hpD hki hkj
    simpa [hXeq] using hmem
  have hnq : ¬ X.memArc q := by
    intro hmem
    apply r2_not_mem_third (E := E) (i := i) (j := j) hij hw hqC hqD hki hkj
    simpa [hXeq] using hmem
  have hunsh {a : Nat} (ha : X.memArc a) :
      ¬ (E.crossings[i].memArc a ∧ E.crossings[j].memArc a) := by
    intro hCD
    rcases honly a hCD with hp | hq
    · subst hp; exact hnp ha
    · subst hq; exact hnq ha
  exact ColoringRule_congr
    (colorAddR2_unshared (hunsh (Or.inl rfl)))
    (colorAddR2_unshared (hunsh (Or.inr (Or.inl rfl))))
    (colorAddR2_unshared (hunsh (Or.inr (Or.inr (Or.inl rfl)))))
    (colorAddR2_unshared (hunsh (Or.inr (Or.inr (Or.inr rfl)))))
    hr

theorem IsColored_colorAddR2 (E : TangleDiagram)
    (i j : Fin E.crossings.length) (hij : i ≠ j) (hw : E.WellFormed)
    (hpair : IsR2Pair E.crossings[i] E.crossings[j])
    (col' : Nat → Int)
    (hc : (collapseR2 E i.val j.val).IsColored col') :
    E.IsColored (colorAddR2 E i j col') ∧
      SameEndpointColors (collapseR2 E i.val j.val) E col'
        (colorAddR2 E i j col') := by
  obtain ⟨p, q, hpq, hpC, hpD, hqC, hqD, hoverC, hoverD, hunderC, hunderD, honly⟩ :=
    hpair.shared_over_under
  constructor
  · intro X hX
    by_cases hXi : X = E.crossings[i]
    · subst hXi
      exact colorAddR2_ColoringRule_first E i j hij hw col' hpair
    · by_cases hXj : X = E.crossings[j]
      · subst hXj
        exact colorAddR2_ColoringRule_second E i j hij hw col' hpair
      · exact colorAddR2_ColoringRule_other E i j hij hw col' hpair hc hX hXi hXj
  · have hEq := collapseR2_eq E i j
    have hunsh_b (e : Endpoint) :
        ¬ (E.crossings[i].memArc (E.boundary e) ∧
            E.crossings[j].memArc (E.boundary e)) := by
      intro h
      rcases honly (E.boundary e) h with hp | hq
      · exact r2_shared_not_boundary E i j hij hw hpC hpD e hp
      · exact r2_shared_not_boundary E i j hij hw hqC hqD e hq
    have hb (a : Nat)
        (hne : ¬ (E.crossings[i].memArc a ∧ E.crossings[j].memArc a)) :
        colorAddR2 E i j col' a =
          col' (r2Merge E.crossings[i] E.crossings[j] a) :=
      colorAddR2_unshared hne
    have hbd :
        (eraseTwo E i.val j.val).NW = E.NW ∧
        (eraseTwo E i.val j.val).NE = E.NE ∧
        (eraseTwo E i.val j.val).SE = E.SE ∧
        (eraseTwo E i.val j.val).SW = E.SW := by
      unfold eraseTwo TangleDiagram.eraseCrossing
      split_ifs <;> simp
    rw [hEq]
    dsimp [TangleDiagram.rename]
    rw [hbd.1, hbd.2.1, hbd.2.2.1, hbd.2.2.2]
    exact ⟨hb E.NW (hunsh_b .NW), hb E.NE (hunsh_b .NE),
      hb E.SE (hunsh_b .SE), hb E.SW (hunsh_b .SW)⟩

theorem coloring_reidemeister_II_add (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterIIAdd D E) (hc : D.IsColored col) (hwE : E.WellFormed) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  obtain ⟨i, j, hij, hpair, hiso⟩ := h
  obtain ⟨col₁, hcol₁, hsame₁⟩ :=
    coloring_planar_isotopy D (collapseR2 E i.val j.val) col hiso hc
  obtain ⟨hE, hsame₂⟩ := IsColored_colorAddR2 E i j hij hwE hpair col₁ hcol₁
  exact ⟨colorAddR2 E i j col₁, hE, hsame₁.trans hsame₂⟩

/-- Given a coloring of a 2-tangle, there is a way to recolor after a
Reidemeister II move so that the colors on the external strands are unchanged
and the coloring rule still holds at every crossing. -/
theorem coloring_IsReidemeisterII (D E : TangleDiagram) (col : Nat → Int)
    (h : IsReidemeisterII D E) (hc : D.IsColored col)
    (_hwD : D.WellFormed) (hwE : E.WellFormed) :
    ∃ col', E.IsColored col' ∧ SameEndpointColors D E col col' := by
  rcases h with h | h
  · exact coloring_reidemeister_II_add D E col h hc hwE
  · exact coloring_reidemeister_II_remove D E col h hc


end RationalTangles
