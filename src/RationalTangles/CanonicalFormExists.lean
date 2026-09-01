/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Tactic.Linarith
import RationalTangles.ContinuedFractionFormExists
import RationalTangles.CanonicalForm

/-!
# Every rational tangle isotopes to canonical form (Proposition 2)
-/

namespace RationalTangles

open Int Function

theorem foldl_add_mirror (acc : TangleDiagram) :
    ∀ cs : List TangleDiagram,
      (cs.foldl TangleDiagram.add acc).mirror =
        (cs.map TangleDiagram.mirror).foldl TangleDiagram.add acc.mirror
  | [] => rfl
  | c :: cs => by
    simp [List.foldl]
    rw [foldl_add_mirror (acc.add c), mirror_add]

theorem planar_mirror_mirror (T : TangleDiagram) :
    PlanarIsotopy T.mirror.mirror T := by
  have hmap : T.mirror.mirror.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch]
  refine ⟨id, injective_id, rfl, rfl, rfl, rfl, T.crossings, ?_, List.Perm.rfl⟩
  have hren : Crossing.rename id = id := funext rename_id
  have : T.mirror.mirror.crossings.map (Crossing.rename id) =
      T.crossings.map Crossing.rotate180 := by
    simp [hmap, hren]
  simpa [this] using pairRel_rotate180 T.crossings

theorem isotopic_mirror_mirror (T : TangleDiagram) :
    Isotopic T.mirror.mirror T :=
  isotopic_planar (planar_mirror_mirror T)

theorem isotopic_replicate_foldl (k : Nat) {X Y : TangleDiagram} (h : Isotopic X Y) :
    Isotopic ((List.replicate k X).foldl TangleDiagram.add TangleDiagram.zero)
      ((List.replicate k Y).foldl TangleDiagram.add TangleDiagram.zero) := by
  induction k with
  | zero => simp; exact .refl _
  | succ k ih =>
    rw [replicate_succ_snoc, replicate_succ_snoc, List.foldl_append, List.foldl_append]
    simp [List.foldl]
    exact .trans (.add_left ih) (.add_right h)

theorem map_replicate_one_mirror (k : Nat) :
    (List.replicate k one).map TangleDiagram.mirror = List.replicate k negOne := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, negOne]

theorem map_replicate_negOne_mirror (k : Nat) :
    (List.replicate k negOne).map TangleDiagram.mirror =
      List.replicate k (one.mirror.mirror) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, negOne]

theorem isotopic_integer_mirror : ∀ n : Int,
    Isotopic (integerTangle n).mirror (integerTangle (-n))
  | Int.ofNat k => by
    simp [integerTangle]
    rw [foldl_add_mirror, map_replicate_one_mirror, mirror_zero]
    cases k with
    | zero => simp; exact .refl _
    | succ k =>
      simp [integerTangle]
      exact .refl _
  | Int.negSucc k => by
    simp [integerTangle, negOne]
    rw [foldl_add_mirror, List.map_replicate, mirror_zero]
    refine .trans (isotopic_replicate_foldl (k + 1) (isotopic_mirror_mirror one)) ?_
    exact .refl _

theorem isotopic_integer_add (n m : Int) :
    Isotopic (integerTangle n + integerTangle m) (integerTangle (n + m)) := by
  rcases le_or_gt 0 m with hm | hm
  · have hm' : m = m.natAbs := Int.eq_natAbs_of_nonneg hm
    rw [hm']
    have go : ∀ k,
        Isotopic (integerTangle n + integerTangle (k : Nat))
          (integerTangle (n + k)) := by
      intro k
      induction k with
      | zero =>
        simp [integerTangle_zero]
        exact Isotopic.add_zero _
      | succ k ih =>
        rw [integerTangle_nat_succ]
        simp only [add_eq_add]
        refine .trans (Isotopic.add_assoc (integerTangle n) (integerTangle k) one).symm ?_
        refine .trans (.add_left ih) ?_
        have : n + (k + 1 : Nat) = n + k + 1 := by omega
        rw [this]
        simpa [add_eq_add] using isotopic_integer_add_one (n + k)
    simpa using go m.natAbs
  · have hm' : m = - (m.natAbs : Int) := by omega
    rw [hm']
    have go : ∀ k,
        Isotopic (integerTangle n + integerTangle (-(k : Nat)))
          (integerTangle (n + (-k : Int))) := by
      intro k
      induction k with
      | zero =>
        simp [integerTangle_zero]
        exact Isotopic.add_zero _
      | succ k ih =>
        rw [integerTangle_neg_succ]
        simp only [add_eq_add]
        refine .trans
          (Isotopic.add_assoc (integerTangle n) (integerTangle (-(k : Nat))) negOne).symm ?_
        refine .trans (.add_left ih) ?_
        have : n + (-((k + 1 : Nat) : Int)) = n + -k + -1 := by omega
        rw [this]
        simpa [add_eq_add] using isotopic_integer_add_negOne (n + (-k : Int))
    simpa using go m.natAbs

theorem cfTangle_mirror : ∀ t : List Int,
    Isotopic (cfTangle t).mirror (cfTangle (t.map (fun n => -n)))
  | [] => by simp [cfTangle]; exact .refl _
  | [a] => by simpa [cfTangle] using isotopic_integer_mirror a
  | a :: b :: rest => by
    simp only [cfTangle, List.map_cons, add_eq_add]
    rw [mirror_add, mirror_invert]
    refine .trans (.add_left (isotopic_integer_mirror a)) ?_
    exact .add_right (.invert_cong (cfTangle_mirror (b :: rest)))

theorem isotopic_one_integer :
    Isotopic (integerTangle 1) one := by
  simpa [integerTangle_one] using Isotopic.zero_add one

/-- Head transfer for `a > 0`, `b < 0` (Figure 14). -/
theorem isotopic_transfer_pos (a b : Int) (rest : List Int)
    (ha : 0 < a) (hb : b < 0) (hcf : IsCFList (a :: b :: rest)) :
    Isotopic (cfTangle (a :: b :: rest))
      (cfTangle ((a - 1) :: 1 :: (-(b + 1)) :: rest.map (fun n => -n))) := by
  have ht : IsCFList (b :: rest) := isCFList_tail hcf
  have hTlist : IsCFList ((b + 1) :: rest) := fun x hx => ht x hx
  set T := cfTangle ((b + 1) :: rest) with hTdef
  have hT : IsRational T := isRational_cfTangle _ hTlist
  have hU_eq : Isotopic (cfTangle (b :: rest)) (T.add negOne) := by
    have := isotopic_cfTangle_add_crossing ((b + 1) :: rest) hTlist CrossingSign.neg
    simpa [bumpHead, T, hTdef, crossingTangle] using this.symm
  have hsplit : Isotopic (integerTangle a) (integerTangle (a - 1) + one) := by
    have := isotopic_integer_add (a - 1) 1
    refine .trans ?_ (.add_right isotopic_one_integer)
    simpa using this.symm
  have ha_cf : cfTangle (a :: b :: rest) =
      integerTangle a + (cfTangle (b :: rest)).invert := by
    cases rest <;> rfl
  rw [ha_cf]
  refine .trans (.add_left hsplit) ?_
  refine .trans (Isotopic.add_assoc _ _ _) ?_
  have hsum :
      Isotopic (one.add (cfTangle (b :: rest)).invert)
        ((T.add negOne).mul one).invert := by
    refine .trans (.add_right (.invert_cong hU_eq)) ?_
    refine .trans (.add_left (Isotopic.invert_unit CrossingSign.pos)) ?_
    have hcomm : Isotopic
        ((crossingTangle CrossingSign.pos).invert.add (T.add negOne).invert)
        ((T.add negOne).invert.add one.invert) := by
      have hR : IsRational (T.add negOne).invert :=
        isRational_invert (isRational_add_crossing hT CrossingSign.neg)
      refine .trans (.add_left (Isotopic.invert_unit CrossingSign.pos).symm) ?_
      refine .trans (isotopic_add_crossing_comm hR CrossingSign.pos).symm ?_
      exact .add_right (Isotopic.invert_unit CrossingSign.pos)
    refine .trans hcomm ?_
    exact (Isotopic.invert_mul (T.add negOne) one).symm
  refine .trans (.add_right hsum) ?_
  have htr : Isotopic ((T.add negOne).mul one) (one.add T.mirror.invert) :=
    Isotopic.transfer_odd T
  refine .trans (.add_right (.invert_cong htr)) ?_
  have hnegT : Isotopic T.mirror
      (cfTangle (((b + 1) :: rest).map (fun n => -n))) := by
    simpa [hTdef] using cfTangle_mirror ((b + 1) :: rest)
  have hrhs :
      Isotopic (one.add T.mirror.invert)
        (cfTangle (1 :: (-(b + 1)) :: rest.map (fun n => -n))) := by
    refine .trans (.add_left isotopic_one_integer.symm) ?_
    refine .trans (.add_right (.invert_cong hnegT)) ?_
    simp [cfTangle, List.map_cons]
    exact .refl _
  refine .trans (.add_right (.invert_cong hrhs)) ?_
  simp [cfTangle]
  exact .refl _

theorem isotopic_transfer_neg (a b : Int) (rest : List Int)
    (ha : a < 0) (hb : 0 < b) (hcf : IsCFList (a :: b :: rest)) :
    Isotopic (cfTangle (a :: b :: rest))
      (cfTangle
        (((-a - 1) :: 1 :: (-(-b + 1)) ::
            (rest.map (fun n => -n)).map (fun n => -n)).map (fun n => -n))) := by
  have hcf' : IsCFList ((-a) :: (-b) :: rest.map (fun n => -n)) := by
    intro x hx
    simp only [List.tail_cons, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact neg_ne_zero.mpr (ne_of_gt hb)
    · have : y ≠ 0 := hcf y (by simp [hy])
      exact neg_ne_zero.mpr this
  have hpos := isotopic_transfer_pos (-a) (-b) (rest.map (fun n => -n))
    (neg_pos.mpr ha) (neg_neg_iff_pos.mpr hb) hcf'
  refine .trans (isotopic_mirror_mirror (cfTangle (a :: b :: rest))).symm ?_
  refine .trans (Isotopic.mirror_cong (cfTangle_mirror (a :: b :: rest))) ?_
  refine .trans (Isotopic.mirror_cong hpos) ?_
  exact cfTangle_mirror _

theorem pack_alternating (t : List Int) (hne : t ≠ []) (hl : IsCFList t)
    (hodd : t.length % 2 = 1) (halt : IsAlternating t) :
    ∃ cf : ArithmeticCF, cf.IsCanonical ∧ cfTangle t = cf.tangle :=
  ⟨⟨t, hne, hl⟩, ⟨hodd, halt⟩, rfl⟩

theorem isRational_cfTangle_any : ∀ t : List Int, IsRational (cfTangle t)
  | [] => isRational_infinity
  | [a] => isRational_integer a
  | a :: b :: rest =>
    isRational_add_integer_left a
      (isRational_invert (isRational_cfTangle_any (b :: rest)))

theorem isotopic_one_add_infinity :
    Isotopic (one.add TangleDiagram.infinity) TangleDiagram.infinity :=
  .trans (isotopic_add_crossing_comm isRational_infinity CrossingSign.pos).symm
    isotopic_infinity_add_one

theorem isotopic_negOne_add_infinity :
    Isotopic (negOne.add TangleDiagram.infinity) TangleDiagram.infinity :=
  .trans (isotopic_add_crossing_comm isRational_infinity CrossingSign.neg).symm
    isotopic_infinity_add_negOne

theorem isotopic_integer_add_infinity : ∀ n : Int,
    Isotopic (integerTangle n + TangleDiagram.infinity) TangleDiagram.infinity := by
  intro n
  have go_pos : ∀ k : Nat,
      Isotopic (integerTangle (k : Int) + TangleDiagram.infinity)
        TangleDiagram.infinity := by
    intro k
    induction k with
    | zero =>
      simp [integerTangle_zero]
      exact Isotopic.zero_add _
    | succ k ih =>
      rw [integerTangle_nat_succ]
      refine .trans (Isotopic.add_assoc (integerTangle k) one TangleDiagram.infinity) ?_
      refine .trans (.add_right isotopic_one_add_infinity) ?_
      exact ih
  have go_neg : ∀ k : Nat,
      Isotopic (integerTangle (-(k : Int)) + TangleDiagram.infinity)
        TangleDiagram.infinity := by
    intro k
    induction k with
    | zero =>
      simp [integerTangle_zero]
      exact Isotopic.zero_add _
    | succ k ih =>
      rw [show integerTangle (-((k + 1 : Nat) : Int)) =
          integerTangle (-(k : Nat)) + negOne from integerTangle_neg_succ k]
      refine .trans
        (Isotopic.add_assoc (integerTangle (-(k : Nat))) negOne TangleDiagram.infinity) ?_
      refine .trans (.add_right isotopic_negOne_add_infinity) ?_
      exact ih
  rcases le_or_gt 0 n with hn | hn
  · have heq : n = n.natAbs := Int.eq_natAbs_of_nonneg hn
    rw [heq]
    exact go_pos n.natAbs
  · have heq : n = -(n.natAbs : Int) := by omega
    rw [heq]
    exact go_neg n.natAbs

theorem isotopic_cfTangle_snoc_zero (x : Int) :
    Isotopic (cfTangle [x, 0]) TangleDiagram.infinity := by
  simp [cfTangle, integerTangle_zero, invert_zero]
  exact isotopic_integer_add_infinity x

theorem isotopic_cfTangle_cons_zero (x y : Int) (ys : List Int) :
    Isotopic (cfTangle (x :: 0 :: y :: ys)) (cfTangle ((x + y) :: ys)) := by
  have hx :
      cfTangle (x :: 0 :: y :: ys) =
        integerTangle x + (cfTangle (0 :: y :: ys)).invert := rfl
  rw [hx]
  have h0 : Isotopic (cfTangle (0 :: y :: ys)) (cfTangle (y :: ys)).invert :=
    isotopic_cfTangle_zero_cons (List.cons_ne_nil _ _)
  refine .trans (.add_right (.invert_cong h0)) ?_
  have hr : IsRational (cfTangle (y :: ys)) := isRational_cfTangle_any _
  refine .trans (.add_right (isotopic_invert_invert hr)) ?_
  cases ys with
  | nil =>
    simp [cfTangle]
    exact isotopic_integer_add x y
  | cons z zs =>
    change Isotopic
      (integerTangle x + (integerTangle y + (cfTangle (z :: zs)).invert))
      (cfTangle ((x + y) :: z :: zs))
    refine .trans
      (Isotopic.add_assoc (integerTangle x) (integerTangle y)
        (cfTangle (z :: zs)).invert).symm ?_
    refine .trans (.add_left (isotopic_integer_add x y)) ?_
    simp [cfTangle]
    exact .refl _

theorem isotopic_cfTangle_cons (a : Int) {s t : List Int}
    (hs : s ≠ []) (ht : t ≠ [])
    (h : Isotopic (cfTangle s) (cfTangle t)) :
    Isotopic (cfTangle (a :: s)) (cfTangle (a :: t)) := by
  cases s with
  | nil => cases hs rfl
  | cons _ _ =>
    cases t with
    | nil => cases ht rfl
    | cons _ _ =>
      simp [cfTangle]
      exact .add_right (.invert_cong h)

theorem isotopic_integer_negOne :
    Isotopic (integerTangle (-1)) negOne := by
  simpa [integerTangle_negOne] using Isotopic.zero_add negOne

theorem isotopic_cfTangle_join_one :
    ∀ t : List Int, ∀ a : Int,
      Isotopic (cfTangle (t ++ [a, 1])) (cfTangle (t ++ [a + 1]))
  | [], a => by
    change Isotopic (integerTangle a + (integerTangle 1).invert) (integerTangle (a + 1))
    have h1 : Isotopic (integerTangle 1) one := isotopic_one_integer
    refine .trans (.add_right (.invert_cong h1)) ?_
    refine .trans (.add_right (Isotopic.invert_unit CrossingSign.pos).symm) ?_
    refine .trans (.add_right h1.symm) ?_
    exact isotopic_integer_add a 1
  | x :: xs, a => by
    have htail := isotopic_cfTangle_join_one xs a
    have hs : xs ++ [a, 1] ≠ [] := by simp
    have ht : xs ++ [a + 1] ≠ [] := by simp
    simpa [List.cons_append] using isotopic_cfTangle_cons x hs ht htail

theorem isotopic_cfTangle_join_negOne :
    ∀ t : List Int, ∀ a : Int,
      Isotopic (cfTangle (t ++ [a, -1])) (cfTangle (t ++ [a - 1]))
  | [], a => by
    change Isotopic (integerTangle a + (integerTangle (-1)).invert) (integerTangle (a - 1))
    have h1 : Isotopic (integerTangle (-1)) negOne := isotopic_integer_negOne
    refine .trans (.add_right (.invert_cong h1)) ?_
    refine .trans (.add_right (Isotopic.invert_unit CrossingSign.neg).symm) ?_
    refine .trans (.add_right h1.symm) ?_
    have : a + (-1) = a - 1 := by omega
    simpa [this] using isotopic_integer_add a (-1)
  | x :: xs, a => by
    have htail := isotopic_cfTangle_join_negOne xs a
    have hs : xs ++ [a, -1] ≠ [] := by simp
    have ht : xs ++ [a - 1] ≠ [] := by simp
    simpa [List.cons_append] using isotopic_cfTangle_cons x hs ht htail

theorem isotopic_cfTangle_split_one (t : List Int) (a : Int) :
    Isotopic (cfTangle (t ++ [a])) (cfTangle (t ++ [a - 1, 1])) := by
  have h := (isotopic_cfTangle_join_one t (a - 1)).symm
  have : a - 1 + 1 = a := by omega
  simpa [this] using h

theorem isotopic_cfTangle_split_negOne (t : List Int) (a : Int) :
    Isotopic (cfTangle (t ++ [a])) (cfTangle (t ++ [a + 1, -1])) := by
  have h := (isotopic_cfTangle_join_negOne t (a + 1)).symm
  have : a + 1 - 1 = a := by omega
  simpa [this] using h

theorem transferHead_neg_eq (a b : Int) (rest : List Int) (ha : ¬ 0 < a) :
    transferHead a b rest =
      (a + 1) :: (-1) :: (1 - b) :: rest.map (fun n => -n) := by
  simp [transferHead, ha]

theorem transfer_neg_list_eq (a b : Int) (rest : List Int) :
    (((-a - 1) :: 1 :: (-(-b + 1)) ::
        (rest.map (fun n => -n)).map (fun n => -n)).map (fun n => -n)) =
      (a + 1) :: (-1) :: (1 - b) :: rest.map (fun n => -n) := by
  simp [List.map_map, neg_neg, add_comm, sub_eq_add_neg]

theorem applyFirstTransfer_isotopic :
    ∀ t : List Int, IsCFList t →
      Isotopic (cfTangle t) (cfTangle (applyFirstTransfer t))
  | [], _ => .refl _
  | [_a], _ => by simp [applyFirstTransfer]; exact .refl _
  | a :: b :: rest, hcf => by
    simp only [applyFirstTransfer]
    split_ifs with hmix
    · rcases hmix with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hpos := isotopic_transfer_pos a b rest ha hb hcf
        simp [transferHead, ha]
        rw [show (-1 + -b) = -(b + 1) from by omega]
        exact hpos
      · have hif : ¬ 0 < a := by omega
        have hneg := isotopic_transfer_neg a b rest ha hb hcf
        rw [transferHead_neg_eq a b rest hif]
        convert hneg
        exact (transfer_neg_list_eq a b rest).symm
    · have ht : IsCFList (b :: rest) := isCFList_tail hcf
      have ih := applyFirstTransfer_isotopic (b :: rest) ht
      have hne : applyFirstTransfer (b :: rest) ≠ [] :=
        applyFirstTransfer_ne (b :: rest) (List.cons_ne_nil _ _)
      exact isotopic_cfTangle_cons a (List.cons_ne_nil _ _) hne ih

theorem not_alternating_tail {a b : Int} {rest : List Int}
    (hb0 : b ≠ 0)
    (hna : ¬ IsAlternating (a :: b :: rest))
    (hnmix : ¬ ((0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b))) :
    ¬ IsAlternating (b :: rest) := by
  intro halt
  apply hna
  unfold IsAlternating at halt ⊢
  rcases halt with hp | hn
  · have hb : 0 < b := lt_of_le_of_ne (hp b (by simp)) hb0.symm
    have ha' : 0 ≤ a := by
      have : ¬ a < 0 := by
        intro ha; exact hnmix (Or.inr ⟨ha, hb⟩)
      omega
    refine Or.inl ?_
    intro x hx
    simp at hx
    rcases hx with rfl | hx
    · exact ha'
    · exact hp x (by simp [hx])
  · have hb : b < 0 := lt_of_le_of_ne (hn b (by simp)) hb0
    have ha' : a ≤ 0 := by
      have : ¬ 0 < a := by
        intro ha; exact hnmix (Or.inl ⟨ha, hb⟩)
      omega
    refine Or.inr ?_
    intro x hx
    simp at hx
    rcases hx with rfl | hx
    · exact ha'
    · exact hn x (by simp [hx])

theorem absSum_applyFirstTransfer_lt :
    ∀ t, IsCFList t → ¬ IsAlternating t →
      absSum (applyFirstTransfer t) < absSum t
  | [], _, hna => by
    have : IsAlternating ([] : List Int) := Or.inl (by intro a ha; cases ha)
    exact (hna this).elim
  | [a], _, hna => (hna (isAlternating_singleton a)).elim
  | a :: b :: rest, hcf, hna => by
    simp only [applyFirstTransfer]
    split_ifs with hmix
    · have := absSum_transferHead a b rest hmix
      simpa [absSum, Nat.add_assoc] using this
    · have hb0 : b ≠ 0 := hcf b (by simp)
      have hna' := not_alternating_tail hb0 hna hmix
      have ht := isCFList_tail hcf
      have ih := absSum_applyFirstTransfer_lt (b :: rest) ht hna'
      change a.natAbs + absSum (applyFirstTransfer (b :: rest)) <
        a.natAbs + absSum (b :: rest)
      exact Nat.add_lt_add_left ih _

theorem isCFList_singleton (x : Int) : IsCFList [x] := by
  intro a ha
  simp at ha

theorem isCFList_cons_of {a : Int} {t : List Int} (hne : t ≠ [])
    (hall : ∀ x ∈ t, x ≠ 0) (ht : IsCFList t) : IsCFList (a :: t) := by
  intro x hx
  simp [List.tail_cons] at hx
  exact hall x hx

theorem isCFList_cons_nonzero_head {a z : Int} {zs : List Int}
    (hz : z ≠ 0) (h : IsCFList (z :: zs)) : IsCFList (a :: z :: zs) := by
  intro x hx
  simp at hx
  rcases hx with rfl | hx
  · exact hz
  · exact h x hx

theorem cfTangle_reduce :
    ∀ t : List Int,
      (∃ t' : List Int, IsCFList t' ∧ t' ≠ [] ∧ absSum t' ≤ absSum t ∧
          t'.length ≤ t.length ∧ Isotopic (cfTangle t) (cfTangle t')) ∨
      Isotopic (cfTangle t) TangleDiagram.infinity := by
  intro t
  induction hn : t.length using Nat.strongRecOn generalizing t with
  | ind n ih =>
    match t with
    | [] =>
      refine Or.inr ?_
      simpa [cfTangle] using Isotopic.refl TangleDiagram.infinity
    | [x] =>
      have hlen1 : ([x] : List Int).length ≤ n := by
        simp at hn ⊢
        omega
      refine Or.inl ⟨[x], isCFList_singleton x, by simp, by simp [absSum], hlen1, .refl _⟩
    | x :: y :: ys =>
      if hy : y = 0 then
        subst hy
        match ys with
        | [] =>
          exact Or.inr (isotopic_cfTangle_snoc_zero x)
        | z :: zs =>
          have hlen : ((x + z) :: zs).length < n := by
            subst hn; simp
          have hred := ih _ hlen ((x + z) :: zs) rfl
          have hiso := isotopic_cfTangle_cons_zero x z zs
          have hsum : absSum ((x + z) :: zs) ≤ absSum (x :: 0 :: z :: zs) := by
            simp [absSum]
            have := Int.natAbs_add_le x z
            omega
          have hlenle : ((x + z) :: zs).length ≤ (x :: 0 :: z :: zs).length := by
            simp
          rcases hred with ⟨t', hcf, hne, hle, hll, hiso'⟩ | hinf
          · exact Or.inl ⟨t', hcf, hne, le_trans hle hsum,
              le_trans hll (le_of_lt hlen), .trans hiso hiso'⟩
          · exact Or.inr (.trans hiso hinf)
      else
        have hlen : (y :: ys).length < n := by subst hn; simp
        have hred := ih _ hlen (y :: ys) rfl
        rcases hred with ⟨t', hcf, hne, hle, hll, hiso'⟩ | hinf
        · match t' with
          | [] => exact (hne rfl).elim
          | z :: zs =>
            if hz : z = 0 then
              subst hz
              match zs with
              | [] =>
                have hcons : Isotopic (cfTangle (x :: y :: ys)) (cfTangle [x, 0]) :=
                  isotopic_cfTangle_cons x (List.cons_ne_nil _ _) (by simp) hiso'
                exact Or.inr (.trans hcons (isotopic_cfTangle_snoc_zero x))
              | w :: ws =>
                have hcons : Isotopic (cfTangle (x :: y :: ys))
                    (cfTangle (x :: 0 :: w :: ws)) :=
                  isotopic_cfTangle_cons x (List.cons_ne_nil _ _) (by simp) hiso'
                have hcol := isotopic_cfTangle_cons_zero x w ws
                have hlen2 : ((x + w) :: ws).length < n := by
                  subst hn
                  have : (0 :: w :: ws).length ≤ (y :: ys).length := hll
                  simp at this ⊢
                  omega
                have hred2 := ih _ hlen2 ((x + w) :: ws) rfl
                have hsum : absSum ((x + w) :: ws) ≤ absSum (x :: y :: ys) := by
                  simp [absSum] at hle ⊢
                  have := Int.natAbs_add_le x w
                  omega
                have hlenle : ((x + w) :: ws).length ≤ (x :: y :: ys).length := by
                  subst hn
                  have : (0 :: w :: ws).length ≤ (y :: ys).length := hll
                  simp at this ⊢
                  omega
                rcases hred2 with ⟨t2, hcf2, hne2, hle2, hll2, hiso2⟩ | hinf2
                · exact Or.inl ⟨t2, hcf2, hne2, le_trans hle2 hsum,
                    le_trans hll2 (le_of_lt hlen2), .trans hcons (.trans hcol hiso2)⟩
                · exact Or.inr (.trans hcons (.trans hcol hinf2))
            else
              refine Or.inl ⟨x :: z :: zs, isCFList_cons_nonzero_head hz hcf,
                List.cons_ne_nil _ _, ?_, ?_,
                isotopic_cfTangle_cons x (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hiso'⟩
              · simp [absSum] at hle ⊢; omega
              · subst hn
                have : (z :: zs).length ≤ (y :: ys).length := hll
                simp at this ⊢
                omega
        · have hcons' : Isotopic (cfTangle (x :: y :: ys))
              (integerTangle x + TangleDiagram.infinity.invert) := by
            cases ys with
            | nil =>
              simp [cfTangle]
              exact .add_right (.invert_cong hinf)
            | cons _ _ =>
              simp [cfTangle]
              exact .add_right (.invert_cong hinf)
          refine Or.inl ⟨[x], isCFList_singleton x, by simp, ?_, ?_, ?_⟩
          · simp [absSum]
          · simp at hn ⊢; omega
          · refine .trans hcons' ?_
            refine .trans (.add_right isotopic_infinity_invert) ?_
            simpa [cfTangle] using Isotopic.add_zero (integerTangle x)

theorem getLast_mem_tail {α} {t : List α} (hne : t ≠ []) (h2 : 1 < t.length) :
    t.getLast hne ∈ t.tail := by
  cases t with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    have hxs : xs ≠ [] := by
      intro h; subst h; simp at h2
    simpa [List.getLast_cons hxs] using List.getLast_mem hxs

theorem mem_tail_of_mem_dropLast {α} {t : List α} {x : α}
    (h : x ∈ t.dropLast) : x ∈ t :=
  (List.dropLast_sublist t).mem h

theorem oddify_alternating (t : List Int) (ht : IsCFList t) (hne : t ≠ [])
    (halt : IsAlternating t) (heven : t.length % 2 = 0) :
    ∃ cf : ArithmeticCF, cf.IsCanonical ∧ Isotopic (cfTangle t) cf.tangle := by
  have hlen2 : 1 < t.length := by
    cases t with
    | nil => exact (hne rfl).elim
    | cons _ xs =>
      cases xs with
      | nil => simp at heven
      | cons _ _ => simp
  let a := t.getLast hne
  let u := t.dropLast
  have eqt : t = u ++ [a] := (List.dropLast_concat_getLast hne).symm
  have hu : u ≠ [] := by
    intro hdl
    have hlen := congrArg List.length eqt
    simp [hdl] at hlen
    omega
  have ha0 : a ≠ 0 := by
    apply ht
    exact getLast_mem_tail hne hlen2
  rw [eqt]
  rcases halt with hp | hnneg
  · have hapos : 0 < a := by
      have : 0 ≤ a := hp a (by rw [eqt]; simp)
      exact lt_of_le_of_ne this ha0.symm
    if h1 : a = 1 then
      rw [h1]
      obtain ⟨v, p, hpj⟩ : ∃ v p, u = v ++ [p] :=
        ⟨u.dropLast, u.getLast hu, (List.dropLast_concat_getLast hu).symm⟩
      rw [hpj]
      have hiso := isotopic_cfTangle_join_one v p
      have ht_eq : t = v ++ [p, 1] := by
        rw [eqt, h1, hpj]; simp
      have hcf' : IsCFList (v ++ [p + 1]) := by
        intro x hx
        cases v with
        | nil =>
          cases hx
        | cons q qs =>
          simp [List.mem_append, List.mem_cons] at hx
          rcases hx with hmem | hpeq
          · exact ht x (by
              rw [ht_eq]
              exact List.mem_append.mpr (Or.inl hmem))
          · rw [hpeq]
            have hpnn : 0 ≤ p := hp p (by rw [ht_eq]; simp)
            omega
      have halt' : IsAlternating (v ++ [p + 1]) := by
        refine Or.inl ?_
        intro x hx
        cases v with
        | nil =>
          simp at hx
          rw [hx]
          have hpnn : 0 ≤ p := hp p (by rw [ht_eq]; simp)
          omega
        | cons q qs =>
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hmem | hpeq
          · exact hp x (by
              rw [ht_eq]
              exact List.mem_append.mpr (Or.inl hmem))
          · rw [hpeq]
            have hpnn : 0 ≤ p := hp p (by rw [ht_eq]; simp)
            omega
      have hodd' : (v ++ [p + 1]).length % 2 = 1 := by
        have hlen := congrArg List.length eqt
        simp [h1, hpj] at hlen
        simp
        omega
      obtain ⟨cf, hcan, heq⟩ :=
        pack_alternating (v ++ [p + 1]) (by simp) hcf' hodd' halt'
      have hassoc : v ++ [p] ++ [1] = v ++ [p, 1] := by simp
      rw [hassoc]
      refine ⟨cf, hcan, hiso.trans ?_⟩
      rw [heq]
      exact Isotopic.refl _
    else
      have ha2 : 1 < a := by omega
      have hiso := isotopic_cfTangle_split_one u a
      cases hU : u with
      | nil => exact (hu hU).elim
      | cons q qs =>
        rw [hU] at hiso eqt hu
        have hcf' : IsCFList (q :: qs ++ [a - 1, 1]) := by
          intro x hx
          -- later of q :: (qs ++ [a-1, 1]) is qs ++ [a-1, 1]
          simp [List.mem_append, List.mem_cons] at hx
          rcases hx with hmem | rfl | rfl
          · exact ht x (by rw [eqt]; simp [List.mem_append, hmem])
          · omega
          · decide
        have halt' : IsAlternating (q :: qs ++ [a - 1, 1]) := by
          refine Or.inl ?_
          intro x hx
          simp [List.mem_cons, List.mem_append] at hx
          rcases hx with rfl | hmem | rfl | rfl
          · exact hp x (by rw [eqt]; simp)
          · exact hp x (by rw [eqt]; simp [List.mem_append, List.mem_cons, hmem])
          · omega
          · decide
        have hodd' : (q :: qs ++ [a - 1, 1]).length % 2 = 1 := by
          have hlen := congrArg List.length eqt
          simp at hlen
          simp
          omega
        obtain ⟨cf, hcan, heq⟩ :=
          pack_alternating (q :: qs ++ [a - 1, 1]) (by simp) hcf' hodd' halt'
        refine ⟨cf, hcan, hiso.trans ?_⟩
        rw [heq]
        exact Isotopic.refl _
  · have haneg : a < 0 := by
      have : a ≤ 0 := hnneg a (by rw [eqt]; simp)
      exact lt_of_le_of_ne this ha0
    if h1 : a = -1 then
      rw [h1]
      obtain ⟨v, p, hpj⟩ : ∃ v p, u = v ++ [p] :=
        ⟨u.dropLast, u.getLast hu, (List.dropLast_concat_getLast hu).symm⟩
      rw [hpj]
      have hiso := isotopic_cfTangle_join_negOne v p
      have ht_eq : t = v ++ [p, -1] := by
        rw [eqt, h1, hpj]; simp
      have hcf' : IsCFList (v ++ [p - 1]) := by
        intro x hx
        cases v with
        | nil =>
          cases hx
        | cons q qs =>
          simp [List.mem_append, List.mem_cons] at hx
          rcases hx with hmem | hpeq
          · exact ht x (by
              rw [ht_eq]
              exact List.mem_append.mpr (Or.inl hmem))
          · rw [hpeq]
            have hpnp : p ≤ 0 := hnneg p (by rw [ht_eq]; simp)
            omega
      have halt' : IsAlternating (v ++ [p - 1]) := by
        refine Or.inr ?_
        intro x hx
        cases v with
        | nil =>
          simp at hx
          rw [hx]
          have hpnp : p ≤ 0 := hnneg p (by rw [ht_eq]; simp)
          omega
        | cons q qs =>
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hmem | hpeq
          · exact hnneg x (by
              rw [ht_eq]
              exact List.mem_append.mpr (Or.inl hmem))
          · rw [hpeq]
            have hpnp : p ≤ 0 := hnneg p (by rw [ht_eq]; simp)
            omega
      have hodd' : (v ++ [p - 1]).length % 2 = 1 := by
        have hlen := congrArg List.length eqt
        simp [h1, hpj] at hlen
        simp
        omega
      obtain ⟨cf, hcan, heq⟩ :=
        pack_alternating (v ++ [p - 1]) (by simp) hcf' hodd' halt'
      have hassoc : v ++ [p] ++ [-1] = v ++ [p, -1] := by simp
      rw [hassoc]
      refine ⟨cf, hcan, hiso.trans ?_⟩
      rw [heq]
      exact Isotopic.refl _
    else
      have ha2 : a < -1 := by omega
      have hiso := isotopic_cfTangle_split_negOne u a
      cases hU : u with
      | nil => exact (hu hU).elim
      | cons q qs =>
        rw [hU] at hiso eqt
        have hcf' : IsCFList (q :: qs ++ [a + 1, -1]) := by
          intro x hx
          simp [List.mem_append, List.mem_cons] at hx
          rcases hx with hmem | rfl | rfl
          · exact ht x (by rw [eqt]; simp [List.mem_append, hmem])
          · omega
          · decide
        have halt' : IsAlternating (q :: qs ++ [a + 1, -1]) := by
          refine Or.inr ?_
          intro x hx
          simp [List.mem_cons, List.mem_append] at hx
          rcases hx with rfl | hmem | rfl | rfl
          · exact hnneg x (by rw [eqt]; simp)
          · exact hnneg x (by rw [eqt]; simp [List.mem_append, List.mem_cons, hmem])
          · omega
          · decide
        have hodd' : (q :: qs ++ [a + 1, -1]).length % 2 = 1 := by
          have hlen := congrArg List.length eqt
          simp at hlen
          simp
          omega
        obtain ⟨cf, hcan, heq⟩ :=
          pack_alternating (q :: qs ++ [a + 1, -1]) (by simp) hcf' hodd' halt'
        refine ⟨cf, hcan, hiso.trans ?_⟩
        rw [heq]
        exact Isotopic.refl _

/-- Recursively eliminate mixed signs, then force odd length. -/
theorem cf_to_canonical :
    ∀ t : List Int, IsCFList t → t ≠ [] →
      (∃ cf : ArithmeticCF, cf.IsCanonical ∧ Isotopic (cfTangle t) cf.tangle) ∨
        Isotopic (cfTangle t) TangleDiagram.infinity := by
  intro t ht hne
  induction hn : absSum t using Nat.strongRecOn generalizing t with
  | ind n ih =>
    by_cases halt : IsAlternating t
    · by_cases hodd : t.length % 2 = 1
      · obtain ⟨cf, hcan, heq⟩ := pack_alternating t hne ht hodd halt
        exact Or.inl ⟨cf, hcan, by simpa [heq] using Isotopic.refl (cfTangle t)⟩
      · have heven : t.length % 2 = 0 := by omega
        exact Or.inl (oddify_alternating t ht hne halt heven)
    · have htr := applyFirstTransfer_isotopic t ht
      have hlt := absSum_applyFirstTransfer_lt t ht halt
      have hred := cfTangle_reduce (applyFirstTransfer t)
      rcases hred with ⟨t', hcf, hne', hle, _, hiso⟩ | hinf
      · have hsum : absSum t' < n := by
          subst hn; omega
        have hrec := ih (absSum t') hsum t' hcf hne' rfl
        have hchain : Isotopic (cfTangle t) (cfTangle t') := .trans htr hiso
        rcases hrec with ⟨cf, hcan, hiso'⟩ | hinf'
        · exact Or.inl ⟨cf, hcan, .trans hchain hiso'⟩
        · exact Or.inr (.trans hchain hinf')
      · exact Or.inr (.trans htr hinf)

/-- Proposition 2. -/
theorem canonical_form_exists (T : TangleDiagram) (h : IsRational T) :
    ∃ S : TangleDiagram, IsCanonicalForm S ∧ Isotopic T S := by
  obtain ⟨cf, hcf⟩ := continued_fraction_form_exists T h
  rcases cf_to_canonical cf.terms cf.later_ne_zero cf.terms_ne with
    ⟨cf', hcan, hiso⟩ | hinf
  · exact ⟨cf'.tangle, Or.inr ⟨cf', hcan, rfl⟩, .trans hcf hiso⟩
  · exact ⟨TangleDiagram.infinity, Or.inl rfl, .trans hcf hinf⟩

end RationalTangles
