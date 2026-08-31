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
  rcases h with rfl | hrot
  · exact Or.inl rfl
  · have : D = C.rotate180 := by
      rw [hrot, Crossing.rotate180_involutive]
    exact Or.inr this

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

end RationalTangles
