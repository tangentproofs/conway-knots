/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import RationalTangles.FlippingLemma
import RationalTangles.ContinuedFractionForm

/-!
# Existence of continued fraction form (Proposition 1)
-/

namespace RationalTangles

open Function

def swap05_16 (n : Nat) : Nat :=
  if n = 0 then 5 else if n = 5 then 0 else if n = 1 then 6 else if n = 6 then 1 else n

theorem swap05_16_injective : Injective swap05_16 := by
  intro a b h
  unfold swap05_16 at h
  split_ifs at h <;> omega

theorem one_add_negOne_crossings :
    (one.add negOne).crossings =
      [{ a0 := 0, a1 := 1, a2 := 2, a3 := 3, sign := .pos },
       { a0 := 5, a1 := 6, a2 := 2, a3 := 1, sign := .neg }] := by
  native_decide

theorem collapseR2_one_negOne_eq :
    collapseR2 (one.add negOne) 0 1 =
      { crossings := [], NW := 5, NE := 5, SE := 6, SW := 6 } := by
  native_decide

theorem planar_zero_collapseR2_one_negOne :
    PlanarIsotopy TangleDiagram.zero (collapseR2 (one.add negOne) 0 1) := by
  rw [collapseR2_one_negOne_eq]
  refine ⟨swap05_16, swap05_16_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem isR2_one_negOne :
    IsR2Pair
      { a0 := 0, a1 := 1, a2 := 2, a3 := 3, sign := .pos }
      { a0 := 5, a1 := 6, a2 := 2, a3 := 1, sign := .neg } := by
  refine ⟨by decide, ?_, ?_, 2, 1, ?_⟩
  · simp [Crossing.adjacentDistinct]
  · simp [Crossing.adjacentDistinct]
  · refine ⟨by decide, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl, Or.inr rfl⟩⟩
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · intro a ⟨hCa, hDa⟩
      simp [Crossing.memArc] at hCa hDa
      omega

theorem isotopic_one_add_negOne_zero :
    Isotopic (one.add negOne) TangleDiagram.zero := by
  have hlen : (one.add negOne).crossings.length = 2 := by
    rw [one_add_negOne_crossings]; rfl
  have h0 : 0 < (one.add negOne).crossings.length := by omega
  have h1 : 1 < (one.add negOne).crossings.length := by omega
  refine .step (.r2 (Or.inr ?_))
  simp only [one_add_negOne_crossings] at h0 h1 ⊢
  refine ⟨⟨0, h0⟩, ⟨1, h1⟩, Fin.ne_of_val_ne Nat.zero_ne_one, isR2_one_negOne,
    planar_zero_collapseR2_one_negOne⟩

theorem isotopic_negOne_add_one_zero :
    Isotopic (negOne.add one) TangleDiagram.zero :=
  .trans (flype_add .neg one) <|
    .trans (.add_left isotopic_one_hflip.symm) isotopic_one_add_negOne_zero

/-! ## Inversion of twist-form expressions -/

def TwistExpr.inverted : TwistExpr → TwistExpr
  | zero => infinity
  | infinity => zero
  | one => one
  | negOne => negOne
  | addRight e s => .mulTop e.inverted s
  | addLeft e s => .mulBottom e.inverted s
  | mulBottom e s => .addRight e.inverted s
  | mulTop e s => .addLeft e.inverted s

theorem planar_infinity_invert :
    PlanarIsotopy TangleDiagram.infinity.invert TangleDiagram.zero := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem isotopic_infinity_invert :
    Isotopic TangleDiagram.infinity.invert TangleDiagram.zero :=
  isotopic_planar planar_infinity_invert

theorem TwistExpr.inverted_isotopic (e : TwistExpr) :
    Isotopic e.diagram.invert e.inverted.diagram := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.inverted, invert_zero]
    exact .refl _
  | infinity =>
    simpa [TwistExpr.diagram, TwistExpr.inverted] using isotopic_infinity_invert
  | one =>
    simpa [TwistExpr.diagram, TwistExpr.inverted, crossingTangle] using
      (Isotopic.invert_unit CrossingSign.pos).symm
  | negOne =>
    simpa [TwistExpr.diagram, TwistExpr.inverted, crossingTangle] using
      (Isotopic.invert_unit CrossingSign.neg).symm
  | addRight e s ih =>
    refine .trans (Isotopic.invert_add e.diagram (crossingTangle s)) ?_
    refine .trans (.mul_left (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.mul_right ih
  | addLeft e s ih =>
    refine .trans (Isotopic.invert_add (crossingTangle s) e.diagram) ?_
    refine .trans (.mul_right (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.mul_left ih
  | mulBottom e s ih =>
    refine .trans (Isotopic.invert_mul e.diagram (crossingTangle s)) ?_
    refine .trans (.add_right (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.add_left ih
  | mulTop e s ih =>
    refine .trans (Isotopic.invert_mul (crossingTangle s) e.diagram) ?_
    refine .trans (.add_left (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.add_right ih

theorem isRational_invert {T : TangleDiagram} (h : IsRational T) :
    IsRational T.invert := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.inverted, .trans (.invert_cong he) e.inverted_isotopic⟩

def StandardExpr.toTwist : StandardExpr → TwistExpr
  | zero => .zero
  | infinity => .infinity
  | addRight e s => .addRight e.toTwist s
  | mulBottom e s => .mulBottom e.toTwist s

theorem StandardExpr.toTwist_diagram (e : StandardExpr) :
    e.toTwist.diagram = e.diagram := by
  induction e <;> simp [StandardExpr.toTwist, StandardExpr.diagram, TwistExpr.diagram, *]

theorem StandardExpr.isRational (e : StandardExpr) : IsRational e.diagram :=
  ⟨e.toTwist, by simpa [e.toTwist_diagram] using Isotopic.refl _⟩

theorem lemma4_unit (T : TangleDiagram) (h : IsRational T) (s : CrossingSign) :
    Isotopic (T.mul (crossingTangle s))
      ((crossingTangle s).add T.invert).invert := by
  obtain ⟨e, he⟩ := h
  have hmul : Isotopic (T.mul (crossingTangle s)) (e.diagram.mul (crossingTangle s)) :=
    Isotopic.mul_left he
  have hR : IsRational (T.mul (crossingTangle s)) :=
    ⟨.mulBottom e s, by simpa [TwistExpr.diagram] using hmul⟩
  obtain ⟨_, _, hii, _⟩ := flipping_lemma _ hR
  have hstep : Isotopic (T.mul (crossingTangle s)).invert.invert
      (T.invert.add (crossingTangle s).invert).invert :=
    .invert_cong (Isotopic.invert_mul T (crossingTangle s))
  have hunit : Isotopic (T.invert.add (crossingTangle s).invert).invert
      (T.invert.add (crossingTangle s)).invert :=
    .invert_cong (.add_right (Isotopic.invert_unit s).symm)
  have hTinv : IsRational T.invert := isRational_invert ⟨e, he⟩
  obtain ⟨hTh, _, _, _⟩ := flipping_lemma T.invert hTinv
  have hcomm : Isotopic (T.invert.add (crossingTangle s))
      ((crossingTangle s).add T.invert) :=
    .trans (.add_left hTh) (.symm (flype_add s T.invert))
  exact .trans hii <| .trans hstep <| .trans hunit (.invert_cong hcomm)

theorem isotopic_crossing_integer (s : CrossingSign) :
    Isotopic (crossingTangle s) (integerTangle s.toInt) := by
  cases s <;> simp [crossingTangle, CrossingSign.toInt, integerTangle]
  · exact .symm (Isotopic.zero_add one)
  · exact .symm (Isotopic.zero_add negOne)


/-! ## Rationality of integer and continued-fraction tangles -/

theorem isRational_of_isotopic {T S : TangleDiagram} (h : Isotopic T S)
    (hS : IsRational S) : IsRational T := by
  obtain ⟨e, he⟩ := hS
  exact ⟨e, .trans h he⟩

theorem isRational_zero : IsRational TangleDiagram.zero :=
  ⟨.zero, .refl _⟩

theorem isRational_infinity : IsRational TangleDiagram.infinity :=
  ⟨.infinity, .refl _⟩

theorem isRational_add_crossing {T : TangleDiagram} (h : IsRational T)
    (s : CrossingSign) : IsRational (T.add (crossingTangle s)) := by
  obtain ⟨e, he⟩ := h
  exact ⟨.addRight e s, by simpa [TwistExpr.diagram] using Isotopic.add_left he⟩

theorem isRational_crossing_add {T : TangleDiagram} (h : IsRational T)
    (s : CrossingSign) : IsRational ((crossingTangle s).add T) := by
  obtain ⟨e, he⟩ := h
  exact ⟨.addLeft e s, by simpa [TwistExpr.diagram] using Isotopic.add_right he⟩

theorem replicate_succ_snoc {α} (n : Nat) (a : α) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih =>
    calc List.replicate (n + 1 + 1) a
        = a :: List.replicate (n + 1) a := rfl
      _ = a :: (List.replicate n a ++ [a]) := by rw [ih]
      _ = (a :: List.replicate n a) ++ [a] := by simp [List.cons_append]
      _ = List.replicate (n + 1) a ++ [a] := rfl

theorem integerTangle_ofNat (n : Nat) :
    integerTangle n =
      (List.replicate n one).foldl TangleDiagram.add TangleDiagram.zero := by
  simp [integerTangle]

theorem integerTangle_negOfNat (n : Nat) :
    integerTangle (-n) =
      (List.replicate n negOne).foldl TangleDiagram.add TangleDiagram.zero := by
  simp [integerTangle]
  split_ifs with h
  · have : n = 0 := by omega
    simp [this]
  · rfl

theorem integerTangle_nat_succ (n : Nat) :
    integerTangle (n + 1 : Nat) = integerTangle n + one := by
  rw [integerTangle_ofNat, integerTangle_ofNat, replicate_succ_snoc,
    List.foldl_append]
  simp [List.foldl, add_eq_add]

theorem integerTangle_neg_succ (n : Nat) :
    integerTangle (-(n + 1 : Nat)) = integerTangle (-n) + negOne := by
  rw [integerTangle_negOfNat, integerTangle_negOfNat, replicate_succ_snoc,
    List.foldl_append]
  simp [List.foldl, add_eq_add]

theorem isRational_add_integer_left (n : Int) {T : TangleDiagram}
    (hT : IsRational T) : IsRational ((integerTangle n).add T) := by
  rcases le_or_gt 0 n with hn | hn
  · have heq : n = n.natAbs := Int.eq_natAbs_of_nonneg hn
    rw [heq]
    have go : ∀ k (S : TangleDiagram), IsRational S →
        IsRational ((integerTangle (k : Nat)).add S) := by
      intro k
      induction k with
      | zero =>
        intro S hS
        exact isRational_of_isotopic (Isotopic.zero_add S) hS
      | succ k ih =>
        intro S hS
        rw [integerTangle_nat_succ]
        simp only [add_eq_add]
        have honeS : IsRational (one.add S) := isRational_crossing_add hS .pos
        exact isRational_of_isotopic
          (Isotopic.add_assoc (integerTangle k) one S) (ih _ honeS)
    exact go n.natAbs T hT
  · have heq : n = -n.natAbs := by omega
    rw [heq]
    have go : ∀ k (S : TangleDiagram), IsRational S →
        IsRational ((integerTangle (-(k : Nat))).add S) := by
      intro k
      induction k with
      | zero =>
        intro S hS
        exact isRational_of_isotopic (Isotopic.zero_add S) hS
      | succ k ih =>
        intro S hS
        rw [integerTangle_neg_succ]
        simp only [add_eq_add]
        have honeS : IsRational (negOne.add S) := isRational_crossing_add hS .neg
        exact isRational_of_isotopic
          (Isotopic.add_assoc (integerTangle (-(k : Nat))) negOne S) (ih _ honeS)
    exact go n.natAbs T hT

theorem isRational_integer (n : Int) : IsRational (integerTangle n) :=
  isRational_of_isotopic (Isotopic.add_zero (integerTangle n)).symm
    (isRational_add_integer_left n isRational_zero)

theorem isotopic_add_crossing_comm {T : TangleDiagram} (h : IsRational T)
    (s : CrossingSign) :
    Isotopic (T.add (crossingTangle s)) ((crossingTangle s).add T) := by
  obtain ⟨hTh, _, _, _⟩ := flipping_lemma T h
  exact .trans (.add_left hTh) (.symm (flype_add s T))

theorem isotopic_add_crossing_right_assoc (T U : TangleDiagram) (s : CrossingSign)
    (hU : IsRational U) :
    Isotopic ((T.add U).add (crossingTangle s))
      ((T.add (crossingTangle s)).add U) :=
  .trans (Isotopic.add_assoc T U (crossingTangle s)) <|
    .trans (.add_right (isotopic_add_crossing_comm hU s)) <|
      .symm (Isotopic.add_assoc T (crossingTangle s) U)

theorem isotopic_integer_add_one (n : Int) :
    Isotopic (integerTangle n + one) (integerTangle (n + 1)) := by
  rcases le_or_gt 0 n with h | h
  · have hn : n = n.natAbs := Int.eq_natAbs_of_nonneg h
    have hsucc : n + 1 = ((n.natAbs + 1 : Nat) : Int) := by omega
    rw [hsucc, hn, integerTangle_nat_succ]
    exact .refl _
  · set k := n.natAbs - 1
    have hn : n = -((k + 1 : Nat) : Int) := by omega
    have hnp1 : n + 1 = -((k : Nat) : Int) := by omega
    rw [hnp1, hn, integerTangle_neg_succ]
    refine .trans (Isotopic.add_assoc (integerTangle (-(k : Nat))) negOne one) ?_
    refine .trans (.add_right isotopic_negOne_add_one_zero) ?_
    exact Isotopic.add_zero _

theorem isotopic_integer_add_negOne (n : Int) :
    Isotopic (integerTangle n + negOne) (integerTangle (n + (-1))) := by
  rcases le_or_gt 0 (n + (-1)) with h | h
  · have hn0 : 0 ≤ n := by omega
    have hnp : n + (-1) = ((n.natAbs - 1 : Nat) : Int) := by omega
    have hn' : n = ((n.natAbs - 1 + 1 : Nat) : Int) := by omega
    rw [hnp, hn', integerTangle_nat_succ]
    refine .trans (Isotopic.add_assoc (integerTangle ((n.natAbs - 1 : Nat) : Int)) one negOne) ?_
    refine .trans (.add_right isotopic_one_add_negOne_zero) ?_
    exact Isotopic.add_zero _
  · set m := (n + (-1)).natAbs
    have hm : 1 ≤ m := by omega
    have hn : n + (-1) = - (m : Int) := by
      have hnn : 0 ≤ -(n + (-1)) := by omega
      have heq := Int.eq_natAbs_of_nonneg hnn
      omega
    have hns : n = - ((m - 1 : Nat) : Int) := by omega
    rw [hn, hns]
    have h1 : integerTangle (- ((m - 1 + 1 : Nat) : Int)) =
        integerTangle (- ((m - 1 : Nat) : Int)) + negOne :=
      integerTangle_neg_succ (m - 1)
    have h2 : ((m - 1 + 1 : Nat) : Int) = m := by omega
    rw [h2] at h1
    rw [← h1]
    exact .refl _

theorem isotopic_integer_add_crossing (n : Int) (s : CrossingSign) :
    Isotopic (integerTangle n + crossingTangle s)
      (integerTangle (n + s.toInt)) := by
  cases s <;> simp [crossingTangle, CrossingSign.toInt]
  · exact isotopic_integer_add_one n
  · exact isotopic_integer_add_negOne n

/-! ## Reidemeister I: `[∞] + [±1] ∼ [∞]` -/

def swap13 (n : Nat) : Nat :=
  if n = 1 then 3 else if n = 3 then 1 else n

theorem swap13_injective : Injective swap13 := by
  intro a b h
  unfold swap13 at h
  split_ifs at h <;> omega

theorem infinity_add_one_crossings :
    (TangleDiagram.infinity.add one).crossings =
      [{ a0 := 1, a1 := 3, a2 := 4, a3 := 1, sign := .pos }] := by
  native_decide

theorem infinity_add_negOne_crossings :
    (TangleDiagram.infinity.add negOne).crossings =
      [{ a0 := 3, a1 := 4, a2 := 1, a3 := 1, sign := .neg }] := by
  native_decide

theorem collapseKink_infinity_add_one :
    collapseKink (TangleDiagram.infinity.add one) 0 ⟨3, by decide⟩ =
      { crossings := [], NW := 0, NE := 3, SE := 3, SW := 0 } := by
  native_decide

theorem collapseKink_infinity_add_negOne :
    collapseKink (TangleDiagram.infinity.add negOne) 0 ⟨2, by decide⟩ =
      { crossings := [], NW := 0, NE := 3, SE := 3, SW := 0 } := by
  native_decide

theorem planar_infinity_collapseKink_add_one :
    PlanarIsotopy TangleDiagram.infinity
      (collapseKink (TangleDiagram.infinity.add one) 0 ⟨3, by decide⟩) := by
  rw [collapseKink_infinity_add_one]
  refine ⟨swap13, swap13_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem planar_infinity_collapseKink_add_negOne :
    PlanarIsotopy TangleDiagram.infinity
      (collapseKink (TangleDiagram.infinity.add negOne) 0 ⟨2, by decide⟩) := by
  rw [collapseKink_infinity_add_negOne]
  refine ⟨swap13, swap13_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem isKink_infinity_add_one :
    Crossing.IsKink
      { a0 := 1, a1 := 3, a2 := 4, a3 := 1, sign := .pos } ⟨3, by decide⟩ := by
  simp [Crossing.IsKink, Crossing.arcs]

theorem isKink_infinity_add_negOne :
    Crossing.IsKink
      { a0 := 3, a1 := 4, a2 := 1, a3 := 1, sign := .neg } ⟨2, by decide⟩ := by
  simp [Crossing.IsKink, Crossing.arcs]

theorem isotopic_infinity_add_one :
    Isotopic (TangleDiagram.infinity.add one) TangleDiagram.infinity := by
  have hlen : (TangleDiagram.infinity.add one).crossings.length = 1 := by
    rw [infinity_add_one_crossings]; rfl
  have h0 : 0 < (TangleDiagram.infinity.add one).crossings.length := by omega
  refine .step (.r1 (Or.inr ?_))
  refine ⟨⟨0, h0⟩, ⟨3, by decide⟩, ?_, planar_infinity_collapseKink_add_one⟩
  simp only [infinity_add_one_crossings]
  exact isKink_infinity_add_one

theorem isotopic_infinity_add_negOne :
    Isotopic (TangleDiagram.infinity.add negOne) TangleDiagram.infinity := by
  have hlen : (TangleDiagram.infinity.add negOne).crossings.length = 1 := by
    rw [infinity_add_negOne_crossings]; rfl
  have h0 : 0 < (TangleDiagram.infinity.add negOne).crossings.length := by omega
  refine .step (.r1 (Or.inr ?_))
  refine ⟨⟨0, h0⟩, ⟨2, by decide⟩, ?_, planar_infinity_collapseKink_add_negOne⟩
  simp only [infinity_add_negOne_crossings]
  exact isKink_infinity_add_negOne

theorem isotopic_infinity_add_crossing (s : CrossingSign) :
    Isotopic (TangleDiagram.infinity.add (crossingTangle s))
      TangleDiagram.infinity := by
  cases s <;> simp [crossingTangle]
  · exact isotopic_infinity_add_one
  · exact isotopic_infinity_add_negOne

/-! ## Standard form → continued-fraction terms -/

def IsCFList (t : List Int) : Prop :=
  ∀ a ∈ t.tail, a ≠ 0

def bumpHead (s : Int) : List Int → List Int
  | [] => []
  | a :: t => (a + s) :: t

def invertTerms : List Int → List Int
  | [] => [0]
  | a :: t => if a = 0 then t else 0 :: a :: t

theorem bumpHead_isCFList (s : Int) {t : List Int} (h : IsCFList t) :
    IsCFList (bumpHead s t) := by
  cases t with
  | nil => intro a ha; cases ha
  | cons a rest =>
    intro b hb
    simpa [bumpHead, IsCFList] using h b hb

theorem invertTerms_isCFList {t : List Int} (h : IsCFList t) :
    IsCFList (invertTerms t) := by
  cases t with
  | nil =>
    intro a ha
    simp [invertTerms] at ha
  | cons a rest =>
    simp only [invertTerms]
    split_ifs with ha0
    · intro b hb
      subst ha0
      apply h
      cases rest with
      | nil => cases hb
      | cons _ xs => exact List.mem_cons_of_mem _ hb
    · intro b hb
      simp at hb
      rcases hb with rfl | hb
      · exact ha0
      · exact h b hb

def StandardExpr.toTerms : StandardExpr → List Int
  | zero => [0]
  | infinity => []
  | addRight e s => bumpHead s.toInt e.toTerms
  | mulBottom e s => invertTerms (bumpHead s.toInt (invertTerms e.toTerms))

theorem StandardExpr.toTerms_isCFList (e : StandardExpr) : IsCFList e.toTerms := by
  induction e with
  | zero => intro a ha; simp [StandardExpr.toTerms] at ha
  | infinity => intro a ha; simp [StandardExpr.toTerms] at ha
  | addRight e s ih =>
    simpa [StandardExpr.toTerms] using bumpHead_isCFList s.toInt ih
  | mulBottom e s ih =>
    simpa [StandardExpr.toTerms] using
      invertTerms_isCFList (bumpHead_isCFList s.toInt (invertTerms_isCFList ih))

theorem isCFList_tail {a b : Int} {rest : List Int}
    (h : IsCFList (a :: b :: rest)) : IsCFList (b :: rest) := by
  intro x hx
  exact h x (List.mem_cons_of_mem _ hx)

theorem isRational_cfTangle : ∀ t : List Int, IsCFList t → IsRational (cfTangle t)
  | [], _ => isRational_infinity
  | [a], _ => isRational_integer a
  | a :: b :: rest, h =>
    isRational_add_integer_left a
      (isRational_invert (isRational_cfTangle (b :: rest) (isCFList_tail h)))

theorem isotopic_invert_invert {T : TangleDiagram} (h : IsRational T) :
    Isotopic T.invert.invert T :=
  (flipping_lemma T h).2.2.1.symm

theorem isotopic_cfTangle_zero_cons {t : List Int} (ht : t ≠ []) :
    Isotopic (cfTangle (0 :: t)) (cfTangle t).invert := by
  cases t with
  | nil => exact (ht rfl).elim
  | cons b rest =>
    simpa [cfTangle, integerTangle_zero] using
      Isotopic.zero_add (cfTangle (b :: rest)).invert

theorem isotopic_cfTangle_invert :
    ∀ t : List Int, IsCFList t →
      Isotopic (cfTangle t).invert (cfTangle (invertTerms t))
  | [], _ => isotopic_infinity_invert
  | [0], _ => by
    simp [invertTerms, cfTangle, integerTangle_zero, invert_zero]
    exact .refl _
  | a :: t, h => by
    have ha0 : a = 0 ∨ a ≠ 0 := Classical.em (a = 0)
    rcases ha0 with rfl | ha0
    · -- invertTerms (0 :: t) = t
      cases t with
      | nil =>
        simp [invertTerms, cfTangle, integerTangle_zero, invert_zero]
        exact .refl _
      | cons b rest =>
        simp only [invertTerms, ↓reduceIte]
        refine .trans (.invert_cong (isotopic_cfTangle_zero_cons (List.cons_ne_nil _ _))) ?_
        exact isotopic_invert_invert (isRational_cfTangle (b :: rest) (isCFList_tail h))
    · -- invertTerms (a :: t) = 0 :: a :: t
      have hif : invertTerms (a :: t) = 0 :: a :: t := by simp [invertTerms, ha0]
      rw [hif]
      exact .symm (isotopic_cfTangle_zero_cons (List.cons_ne_nil _ _))

theorem isotopic_cfTangle_add_crossing :
    ∀ t : List Int, IsCFList t → ∀ s : CrossingSign,
      Isotopic (cfTangle t + crossingTangle s) (cfTangle (bumpHead s.toInt t))
  | [], _, s => by
    simpa [cfTangle, bumpHead] using isotopic_infinity_add_crossing s
  | [a], _, s => by
    simpa [cfTangle, bumpHead] using isotopic_integer_add_crossing a s
  | a :: b :: rest, h, s => by
    have ht : IsCFList (b :: rest) := isCFList_tail h
    have hU : IsRational (cfTangle (b :: rest)).invert :=
      isRational_invert (isRational_cfTangle (b :: rest) ht)
    have hassoc :
        Isotopic
          ((integerTangle a + (cfTangle (b :: rest)).invert) + crossingTangle s)
          ((integerTangle a + crossingTangle s) + (cfTangle (b :: rest)).invert) :=
      isotopic_add_crossing_right_assoc (integerTangle a)
        (cfTangle (b :: rest)).invert s hU
    change Isotopic
        ((integerTangle a + (cfTangle (b :: rest)).invert) + crossingTangle s)
        (integerTangle (a + s.toInt) + (cfTangle (b :: rest)).invert)
    refine .trans hassoc ?_
    refine .trans (.add_left (isotopic_integer_add_crossing a s)) ?_
    exact .refl _

theorem StandardExpr.toTerms_isotopic (e : StandardExpr) :
    Isotopic e.diagram (cfTangle e.toTerms) := by
  induction e with
  | zero =>
    simp [StandardExpr.diagram, StandardExpr.toTerms, cfTangle]
    exact .refl _
  | infinity =>
    simp [StandardExpr.diagram, StandardExpr.toTerms, cfTangle]
    exact .refl _
  | addRight e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.toTerms, add_eq_add]
    refine .trans (.add_left ih) ?_
    exact isotopic_cfTangle_add_crossing e.toTerms e.toTerms_isCFList s
  | mulBottom e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.toTerms, mul_eq_mul]
    have hR : IsRational e.diagram := e.isRational
    refine .trans (lemma4_unit e.diagram hR s) ?_
    have hinv :
        Isotopic e.diagram.invert (cfTangle (invertTerms e.toTerms)) :=
      .trans (.invert_cong ih)
        (isotopic_cfTangle_invert e.toTerms e.toTerms_isCFList)
    have hadd :
        Isotopic ((crossingTangle s).add e.diagram.invert)
          (cfTangle (bumpHead s.toInt (invertTerms e.toTerms))) := by
      refine .trans (.add_right hinv) ?_
      -- crossing + cf ~ cf + crossing ~ bump, via commute
      have hcf : IsRational (cfTangle (invertTerms e.toTerms)) :=
        isRational_cfTangle _ (invertTerms_isCFList e.toTerms_isCFList)
      refine .trans (isotopic_add_crossing_comm hcf s).symm ?_
      exact isotopic_cfTangle_add_crossing _ (invertTerms_isCFList e.toTerms_isCFList) s
    refine .trans (.invert_cong hadd) ?_
    exact isotopic_cfTangle_invert _
      (bumpHead_isCFList s.toInt (invertTerms_isCFList e.toTerms_isCFList))

def StandardExpr.cfTerms (e : StandardExpr) : List Int :=
  match e.toTerms with
  | [] => [0, 1, -1]
  | t => t

theorem StandardExpr.cfTerms_ne (e : StandardExpr) : e.cfTerms ≠ [] := by
  simp [StandardExpr.cfTerms]
  cases h : e.toTerms <;> simp

theorem StandardExpr.cfTerms_isCFList (e : StandardExpr) : IsCFList e.cfTerms := by
  simp [StandardExpr.cfTerms]
  cases h : e.toTerms with
  | nil =>
    intro a ha
    simp at ha
    rcases ha with rfl | rfl <;> decide
  | cons a t =>
    simpa [IsCFList, h] using e.toTerms_isCFList

def StandardExpr.toCF (e : StandardExpr) : ArithmeticCF where
  terms := e.cfTerms
  terms_ne := e.cfTerms_ne
  later_ne_zero := e.cfTerms_isCFList

theorem isotopic_infinity_cfTangle_cancel :
    Isotopic TangleDiagram.infinity (cfTangle [0, 1, -1]) := by
  have h11 : Isotopic (cfTangle [1, -1]) TangleDiagram.zero := by
    simp only [cfTangle]
    refine .trans (.add_left (isotopic_crossing_integer .pos).symm) ?_
    refine .trans (.add_right (.invert_cong (isotopic_crossing_integer .neg).symm)) ?_
    refine .trans (.add_right (Isotopic.invert_unit .neg).symm) ?_
    exact isotopic_one_add_negOne_zero
  have h0 : Isotopic (cfTangle [0, 1, -1]) (cfTangle [1, -1]).invert :=
    isotopic_cfTangle_zero_cons (by decide : [1, -1] ≠ [])
  refine .trans ?_ h0.symm
  have : Isotopic TangleDiagram.infinity (cfTangle [1, -1]).invert := by
    simpa [invert_zero] using (Isotopic.invert_cong h11).symm
  exact this

theorem StandardExpr.toCF_isotopic (e : StandardExpr) :
    Isotopic e.diagram e.toCF.tangle := by
  simp [StandardExpr.toCF, ArithmeticCF.tangle, StandardExpr.cfTerms]
  cases h : e.toTerms with
  | nil =>
    have : Isotopic e.diagram TangleDiagram.infinity := by
      simpa [StandardExpr.toTerms, h, cfTangle] using e.toTerms_isotopic
    exact .trans this isotopic_infinity_cfTangle_cancel
  | cons a t =>
    simpa [h] using e.toTerms_isotopic

/-- Proposition 1: every rational tangle can be written in continued fraction form. -/
theorem continued_fraction_form_exists (T : TangleDiagram) (h : IsRational T) :
    ∃ cf : ArithmeticCF, Isotopic T cf.tangle := by
  obtain ⟨e, he⟩ := standard_form_exists T h
  exact ⟨e.toCF, .trans he e.toCF_isotopic⟩

end RationalTangles
