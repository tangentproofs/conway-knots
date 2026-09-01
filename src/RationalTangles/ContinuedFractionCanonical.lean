/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import RationalTangles.CanonicalForm

/-!
# Unique canonical continued fraction (Proposition 3)

Existence and uniqueness of an odd-length one-sign expansion for every
finite continued-fraction value, via Euclid's algorithm and the last-term
identities of Remark 5. The value `∞` has no same-sign finite expansion.
-/

namespace RationalTangles

theorem value_singleton (n : Int) :
    valueOfList [n] = CFValue.ofInt n := by
  simp [valueOfList, CFValue.ofInt, CFValue.add, CFValue.inv]

theorem ofInt_inj {a b : Int} (h : CFValue.ofInt a = CFValue.ofInt b) : a = b := by
  simp [CFValue.ofInt] at h
  exact_mod_cast h

theorem ArithmeticCF.ext {c₁ c₂ : ArithmeticCF} (h : c₁.terms = c₂.terms) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases h
  rfl

theorem valueOfList_concat_one :
    ∀ t : List Int, ∀ a : Int,
      valueOfList (t ++ [a, 1]) = valueOfList (t ++ [a + 1])
  | [], a => by
    have h1 : (1 : Rat) ≠ 0 := by norm_num
    simp [valueOfList, CFValue.ofInt, CFValue.add, CFValue.inv, h1]
  | x :: xs, a => by
    simp [valueOfList, valueOfList_concat_one xs a]

theorem valueOfList_concat_negOne :
    ∀ t : List Int, ∀ a : Int,
      valueOfList (t ++ [a, -1]) = valueOfList (t ++ [a - 1])
  | [], a => by
    have h1 : (-1 : Rat) ≠ 0 := by norm_num
    simp [valueOfList, CFValue.ofInt, CFValue.add, CFValue.inv, h1]
    ring
  | x :: xs, a => by
    simp [valueOfList, valueOfList_concat_negOne xs a]

theorem valueOfList_split_one (t : List Int) (a : Int) :
    valueOfList (t ++ [a]) = valueOfList (t ++ [a - 1, 1]) := by
  have h := (valueOfList_concat_one t (a - 1)).symm
  simpa [sub_add_cancel] using h

theorem valueOfList_split_negOne (t : List Int) (a : Int) :
    valueOfList (t ++ [a]) = valueOfList (t ++ [a + 1, -1]) := by
  have h := (valueOfList_concat_negOne t (a + 1)).symm
  have : a + 1 - 1 = a := by omega
  simpa [this] using h

/-- Euclidean simple continued fraction of the nonnegative rational `n / d`. -/
noncomputable def euclidPos (n d : Nat) : List Int :=
  d.strongRecOn
    (fun d ih n =>
      if h : d = 0 then []
      else
        if n % d = 0 then [((n / d : Nat) : Int)]
        else
          ((n / d : Nat) : Int) ::
            ih (n % d) (Nat.mod_lt n (Nat.pos_of_ne_zero h)) d)
    n

theorem euclidPos_eq (n d : Nat) (hd : d ≠ 0) :
    euclidPos n d =
      if n % d = 0 then [((n / d : Nat) : Int)]
      else ((n / d : Nat) : Int) :: euclidPos d (n % d) := by
  unfold euclidPos
  rw [Nat.strongRecOn, WellFounded.fix_eq]
  simp [hd, Nat.strongRecOn]

theorem euclidPos_ne_nil (n d : Nat) (hd : d ≠ 0) : euclidPos n d ≠ [] := by
  rw [euclidPos_eq n d hd]
  split_ifs <;> simp

theorem nat_cast_eq_div_mod (n d : Nat) :
    (n : Rat) = (d : Rat) * (n / d : Nat) + (n % d : Nat) := by
  have h := Nat.div_add_mod n d
  have h' : n = d * (n / d) + n % d := by
    simpa [Nat.mul_comm] using h.symm
  refine (congrArg (fun k : Nat => (k : Rat)) h').trans ?_
  push_cast
  rfl

theorem nat_rat_div_mod (n d : Nat) (hd : d ≠ 0) :
    (n : Rat) / (d : Rat) = (n / d : Nat) + (n % d : Nat) / (d : Rat) := by
  have hd0 : (d : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have h := nat_cast_eq_div_mod n d
  calc
    (n : Rat) / (d : Rat)
        = ((d : Rat) * (n / d : Nat) + (n % d : Nat)) / (d : Rat) := by rw [h]
    _ = ((d : Rat) * (n / d : Nat)) / (d : Rat) + (n % d : Nat) / (d : Rat) := by
        simp [add_div]
    _ = (n / d : Nat) + (n % d : Nat) / (d : Rat) := by
        field_simp [hd0]

theorem value_euclidPos (n d : Nat) (hd : d ≠ 0) :
    valueOfList (euclidPos n d) = CFValue.ofRat ((n : Rat) / (d : Rat)) := by
  revert n hd
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n hd
    rw [euclidPos_eq n d hd]
    have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdiv := nat_rat_div_mod n d hd
    by_cases hr : n % d = 0
    · rw [if_pos hr, value_singleton]
      simp [CFValue.ofInt]
      norm_cast
      simpa [hr] using hdiv.symm
    · rw [if_neg hr, valueOfList_cons]
      have hrlt : n % d < d := Nat.mod_lt n hpos
      have hrne : n % d ≠ 0 := hr
      have hval := ih (n % d) hrlt d hrne
      rw [hval]
      have hd0 : (d : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hd
      have hr0 : ((n % d) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hrne
      have hfrac : ((d : Rat) / (n % d : Rat)) ≠ 0 := div_ne_zero hd0 hr0
      rw [CFValue.inv_ofRat hfrac]
      simp [CFValue.ofInt]
      convert hdiv.symm
      rw [← Int.natCast_div n d]
      rfl

theorem num_div_den_eq (q : Rat) : (q.num : Rat) / (q.den : Rat) = q := by
  have : (q.den : Rat) = (q.den : Int) := by simp
  rw [this, Rat.intCast_div_eq_divInt, Rat.num_divInt_den]

/-- Euclid expansion of an arbitrary rational. -/
noncomputable def euclidRat (q : Rat) : List Int :=
  if q < 0 then (euclidPos q.num.natAbs q.den).map (fun n => -n)
  else euclidPos q.num.natAbs q.den

theorem value_euclidRat (q : Rat) :
    valueOfList (euclidRat q) = CFValue.ofRat q := by
  unfold euclidRat
  have hd : q.den ≠ 0 := q.den_nz
  by_cases hq : q < 0
  · rw [if_pos hq, valueOfList_neg, value_euclidPos q.num.natAbs q.den hd]
    have hneg : q.num < 0 := by
      have : ¬ 0 ≤ q := not_le.mpr hq
      have : ¬ 0 ≤ q.num := fun h => this (Rat.num_nonneg.mp h)
      omega
    have habs : (q.num.natAbs : Int) = -q.num := by
      have : 0 ≤ -q.num := by omega
      simpa using (Int.eq_natAbs_of_nonneg this).symm
    have hcast : (q.num.natAbs : Rat) = - (q.num : Rat) := by
      rw [← Rat.intCast_neg]
      exact congrArg (fun k : Int => (k : Rat)) habs
    have hval : (q.num.natAbs : Rat) / (q.den : Rat) = -q := by
      rw [hcast, neg_div, num_div_den_eq]
    rw [CFValue.neg_ofRat, hval, neg_neg]
  · rw [if_neg hq, value_euclidPos q.num.natAbs q.den hd]
    have hnn : 0 ≤ q := le_of_not_gt hq
    have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr hnn
    have habs : (q.num.natAbs : Int) = q.num :=
      (Int.eq_natAbs_of_nonneg hn0).symm
    have hcast : (q.num.natAbs : Rat) = (q.num : Rat) :=
      congrArg (fun k : Int => (k : Rat)) habs
    have : (q.num.natAbs : Rat) / (q.den : Rat) = q := by
      rw [hcast, num_div_den_eq]
    simpa [this]



/-- Remark 5, Euclid case: even length has last ≥ 2, so split the last term. -/
def oddify (t : List Int) : List Int :=
  if t.length % 2 = 1 then t
  else t.dropLast ++ [t.getLastD 0 - 1, 1]

theorem oddify_of_odd {t : List Int} (h : t.length % 2 = 1) : oddify t = t := by
  simp [oddify, h]

theorem dropLast_concat_getLast_eq {t : List Int} (hne : t ≠ []) :
    t = t.dropLast ++ [t.getLast hne] :=
  (List.dropLast_concat_getLast hne).symm

theorem getLastD_eq_getLast {t : List Int} (hne : t ≠ []) :
    t.getLastD 0 = t.getLast hne := by
  simp [List.getLastD_eq_getLast?]
  rw [List.getLast?_eq_some_getLast hne]
  rfl

theorem value_oddify (t : List Int) (hne : t ≠ []) :
    valueOfList (oddify t) = valueOfList t := by
  by_cases hodd : t.length % 2 = 1
  · simp [oddify, hodd]
  · simp [oddify, hodd]
    rw [← List.getLastD_eq_getLast?, getLastD_eq_getLast hne]
    have ht := dropLast_concat_getLast_eq hne
    have hs := valueOfList_split_one t.dropLast (t.getLast hne)
    calc
      valueOfList (t.dropLast ++ [t.getLast hne - 1, 1])
          = valueOfList (t.dropLast ++ [t.getLast hne]) := hs.symm
      _ = valueOfList t := congrArg valueOfList ht.symm

theorem oddify_length_odd (t : List Int) (hne : t ≠ []) :
    (oddify t).length % 2 = 1 := by
  by_cases hodd : t.length % 2 = 1
  · simp [oddify, hodd]
  · have heven : t.length % 2 = 0 := by omega
    have hdl : t.dropLast.length = t.length - 1 := List.length_dropLast
    have hpos : 1 ≤ t.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil hne)
    rw [oddify, if_neg hodd]
    have hlen2 :
        (t.dropLast ++ [t.getLastD 0 - 1, (1 : Int)]).length = t.dropLast.length + 2 := by
      simp [List.length_append]
    rw [hlen2, hdl]
    have : t.length - 1 + 2 = t.length + 1 := by omega
    rw [this, Nat.add_mod, heven]

theorem oddify_ne_nil {t : List Int} (hne : t ≠ []) : oddify t ≠ [] := by
  intro h
  have := oddify_length_odd t hne
  simp [h] at this

theorem euclidPos_nonneg (n d : Nat) (hd : d ≠ 0) :
    ∀ a ∈ euclidPos n d, 0 ≤ a := by
  revert n hd
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n hd a ha
    rw [euclidPos_eq n d hd] at ha
    by_cases hr : n % d = 0
    · simp [hr] at ha; subst ha; exact Int.natCast_nonneg _
    · simp [hr] at ha
      rcases ha with rfl | ha
      · exact Int.natCast_nonneg _
      · exact ih (n % d) (Nat.mod_lt n (Nat.pos_of_ne_zero hd)) d hr a ha

theorem euclidPos_tail_pos (n d : Nat) (hd : d ≠ 0) :
    ∀ a ∈ (euclidPos n d).tail, 0 < a := by
  revert n hd
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n hd a ha
    rw [euclidPos_eq n d hd] at ha
    by_cases hr : n % d = 0
    · simp [hr] at ha
    · simp [hr] at ha
      have hrlt := Nat.mod_lt n (Nat.pos_of_ne_zero hd)
      have hdivpos : 0 < d / (n % d) :=
        Nat.div_pos (Nat.le_of_lt hrlt) (Nat.pos_of_ne_zero hr)
      cases hL : euclidPos d (n % d) with
      | nil => exact (euclidPos_ne_nil d (n % d) hr hL).elim
      | cons x xs =>
          simp [hL] at ha
          rcases ha with rfl | hxs
          · have heq := euclidPos_eq d (n % d) hr
            rw [hL] at heq
            split_ifs at heq with hr2
            · injection heq with hx _; subst hx; exact_mod_cast hdivpos
            · injection heq with hx _; subst hx; exact_mod_cast hdivpos
          · exact ih (n % d) hrlt d hr a (by simp [hL, hxs])

theorem euclidPos_last_ge_two (n d : Nat) (hd : d ≠ 0)
    (hlen : 1 < (euclidPos n d).length) : 2 ≤ (euclidPos n d).getLastD 0 := by
  revert n hd hlen
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n hd hlen
    rw [euclidPos_eq n d hd] at hlen ⊢
    by_cases hr : n % d = 0
    · simp [hr] at hlen
    · simp [hr] at hlen ⊢
      have hrne : n % d ≠ 0 := hr
      have hrlt := Nat.mod_lt n (Nat.pos_of_ne_zero hd)
      have hinner := euclidPos_eq d (n % d) hrne
      by_cases hr2 : d % (n % d) = 0
      · rw [hinner, if_pos hr2] at hlen ⊢
        simp at hlen ⊢
        have hdvd : n % d ∣ d := Nat.dvd_of_mod_eq_zero hr2
        have hge : 1 ≤ d / (n % d) :=
          Nat.div_pos (Nat.le_of_lt hrlt) (Nat.pos_of_ne_zero hrne)
        have hne1 : d / (n % d) ≠ 1 := by
          intro heq
          have : n % d * (d / (n % d)) = d := Nat.mul_div_cancel' hdvd
          rw [heq, Nat.mul_one] at this
          exact (Nat.ne_of_gt hrlt this.symm).elim
        have : 2 ≤ d / (n % d) := Nat.succ_le_of_lt (lt_of_le_of_ne hge hne1.symm)
        exact_mod_cast this
      · rw [hinner, if_neg hr2] at hlen ⊢
        have hlen' : 1 < (euclidPos d (n % d)).length := by
          rw [hinner, if_neg hr2]
          have hne2 := euclidPos_ne_nil (n % d) (d % (n % d)) hr2
          exact Nat.succ_lt_succ (List.length_pos_of_ne_nil hne2)
        have := ih (n % d) hrlt d hrne hlen'
        simpa [hinner, hr2] using this

def IsStandard (t : List Int) : Prop :=
  t ≠ [] ∧
    (∀ a ∈ t, 0 ≤ a) ∧
    (∀ a ∈ t.tail, 0 < a) ∧
    (t.length = 1 ∨ 2 ≤ t.getLastD 0)

theorem isStandard_euclidPos (n d : Nat) (hd : d ≠ 0) :
    IsStandard (euclidPos n d) := by
  refine ⟨euclidPos_ne_nil n d hd, euclidPos_nonneg n d hd, euclidPos_tail_pos n d hd, ?_⟩
  by_cases h1 : (euclidPos n d).length = 1
  · exact Or.inl h1
  · exact Or.inr (euclidPos_last_ge_two n d hd (by
      have : 0 < (euclidPos n d).length := List.length_pos_of_ne_nil (euclidPos_ne_nil n d hd)
      omega))

theorem oddify_euclid_nonneg (n d : Nat) (hd : d ≠ 0) :
    ∀ a ∈ oddify (euclidPos n d), 0 ≤ a := by
  intro a ha
  by_cases hodd : (euclidPos n d).length % 2 = 1
  · simp [oddify, hodd] at ha
    exact euclidPos_nonneg n d hd a ha
  · simp [oddify, hodd, List.mem_append, List.mem_cons] at ha
    rcases ha with hmem | rfl | rfl
    · exact euclidPos_nonneg n d hd a ((List.dropLast_sublist _).mem hmem)
    · have hne := euclidPos_ne_nil n d hd
      have hlen : 1 < (euclidPos n d).length := by
        have : 0 < (euclidPos n d).length := List.length_pos_of_ne_nil hne
        omega
      have hge := euclidPos_last_ge_two n d hd hlen
      rw [List.getLastD_eq_getLast?] at hge
      omega
    · decide

theorem oddify_euclid_later_ne_zero (n d : Nat) (hd : d ≠ 0) :
    ∀ a ∈ (oddify (euclidPos n d)).tail, a ≠ 0 := by
  intro a ha
  have hne := euclidPos_ne_nil n d hd
  by_cases hodd : (euclidPos n d).length % 2 = 1
  · simp [oddify, hodd] at ha
    exact ne_of_gt (euclidPos_tail_pos n d hd a ha)
  · have hlen : 1 < (euclidPos n d).length := by
      have : 0 < (euclidPos n d).length := List.length_pos_of_ne_nil hne
      omega
    have hge := euclidPos_last_ge_two n d hd hlen
    cases hE : euclidPos n d with
    | nil => exact (hne hE).elim
    | cons x xs =>
        have hxs : xs ≠ [] := by
          intro hx; subst hx; simp [hE] at hlen
        have hodd' : ¬ (x :: xs).length % 2 = 1 := by simpa [hE] using hodd
        have hoddify :
            oddify (x :: xs) =
              (x :: xs.dropLast) ++ [(x :: xs).getLastD 0 - 1, 1] := by
          rw [oddify, if_neg hodd']
          simp [List.dropLast]
        rw [hE, hoddify] at ha
        simp [List.mem_append, List.mem_cons] at ha
        rcases ha with hmem | rfl | rfl
        · have : a ∈ xs := (List.dropLast_sublist xs).mem hmem
          exact ne_of_gt (euclidPos_tail_pos n d hd a (by simp [hE, this]))
        · have hlast :
              (x :: xs).getLastD 0 = (euclidPos n d).getLastD 0 := by
            rw [hE]
          simp [List.getLastD_eq_getLast?] at hge hlast ⊢
          omega
        · decide


theorem oddify_euclid_value (n d : Nat) (hd : d ≠ 0) :
    valueOfList (oddify (euclidPos n d)) = CFValue.ofRat ((n : Rat) / (d : Rat)) := by
  rw [value_oddify _ (euclidPos_ne_nil n d hd), value_euclidPos n d hd]

theorem later_map_neg {t : List Int} (h : ∀ a ∈ t.tail, a ≠ 0) :
    ∀ a ∈ (t.map fun n => -n).tail, a ≠ 0 := by
  intro a ha
  cases t with
  | nil => simp at ha
  | cons x xs =>
      simp at ha
      exact neg_ne_zero.mp (h (-a) (by simpa using ha))

noncomputable def canonicalTerms (q : Rat) : List Int :=
  if q < 0 then (oddify (euclidPos q.num.natAbs q.den)).map fun n => -n
  else oddify (euclidPos q.num.natAbs q.den)

theorem canonicalTerms_ne (q : Rat) : canonicalTerms q ≠ [] := by
  unfold canonicalTerms
  have hd : q.den ≠ 0 := q.den_nz
  split_ifs <;> simp [oddify_ne_nil (euclidPos_ne_nil _ _ hd)]

theorem canonicalTerms_later_ne_zero (q : Rat) :
    ∀ a ∈ (canonicalTerms q).tail, a ≠ 0 := by
  unfold canonicalTerms
  have hd : q.den ≠ 0 := q.den_nz
  split_ifs
  · exact later_map_neg (oddify_euclid_later_ne_zero q.num.natAbs q.den hd)
  · exact oddify_euclid_later_ne_zero q.num.natAbs q.den hd

theorem canonicalTerms_odd (q : Rat) : (canonicalTerms q).length % 2 = 1 := by
  unfold canonicalTerms
  have hd : q.den ≠ 0 := q.den_nz
  have h := oddify_length_odd (euclidPos q.num.natAbs q.den) (euclidPos_ne_nil _ _ hd)
  split_ifs <;> simp [List.length_map, h]

theorem canonicalTerms_alternating (q : Rat) :
    (∀ a ∈ canonicalTerms q, 0 ≤ a) ∨ (∀ a ∈ canonicalTerms q, a ≤ 0) := by
  unfold canonicalTerms
  have hd : q.den ≠ 0 := q.den_nz
  by_cases hq : q < 0
  · refine Or.inr ?_
    intro a ha
    rw [if_pos hq] at ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    have := oddify_euclid_nonneg q.num.natAbs q.den hd b hb
    omega
  · refine Or.inl ?_
    intro a ha
    rw [if_neg hq] at ha
    exact oddify_euclid_nonneg q.num.natAbs q.den hd a ha

noncomputable def canonicalCF (q : Rat) : ArithmeticCF where
  terms := canonicalTerms q
  terms_ne := canonicalTerms_ne q
  later_ne_zero := canonicalTerms_later_ne_zero q

theorem canonicalCF_isCanonical (q : Rat) : (canonicalCF q).IsCanonical :=
  ⟨canonicalTerms_odd q, canonicalTerms_alternating q⟩

theorem canonicalCF_value (q : Rat) : (canonicalCF q).value = CFValue.ofRat q := by
  change valueOfList (canonicalTerms q) = CFValue.ofRat q
  have hd : q.den ≠ 0 := q.den_nz
  rw [canonicalTerms]
  split_ifs with hq
  · rw [valueOfList_neg, oddify_euclid_value _ _ hd]
    have hneg : q.num < 0 := by
      have : ¬ 0 ≤ q := not_le.mpr hq
      have : ¬ 0 ≤ q.num := fun h => this (Rat.num_nonneg.mp h)
      omega
    have habs : (q.num.natAbs : Int) = -q.num := by
      have : 0 ≤ -q.num := by omega
      simpa using (Int.eq_natAbs_of_nonneg this).symm
    have hcast : (q.num.natAbs : Rat) = - (q.num : Rat) := by
      rw [← Rat.intCast_neg]
      exact congrArg (fun k : Int => (k : Rat)) habs
    have : (q.num.natAbs : Rat) / (q.den : Rat) = -q := by
      rw [hcast, neg_div, num_div_den_eq]
    rw [CFValue.neg_ofRat, this, neg_neg]
  · rw [oddify_euclid_value _ _ hd]
    have hnn : 0 ≤ q := le_of_not_gt hq
    have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr hnn
    have habs : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg hn0
    have hcast : (q.num.natAbs : Rat) = (q.num : Rat) :=
      congrArg (fun k : Int => (k : Rat)) habs
    have : (q.num.natAbs : Rat) / (q.den : Rat) = q := by
      rw [hcast, num_div_den_eq]
    simpa [this]

/-- Proposition 3, existence. Every continued fraction of finite value has a
    canonical form (Euclid + Remark 5). The constructed form of a rational `q`
    is `canonicalCF q`. Uniqueness is `continued_fraction_canonical_unique`. -/
theorem continued_fraction_canonical (cf : ArithmeticCF) :
    (∃ cf' : ArithmeticCF, cf'.IsCanonical ∧ cf'.value = cf.value) ∨
      cf.value = CFValue.inf := by
  cases hv : cf.value with
  | inf => exact Or.inr rfl
  | ofRat q =>
      refine Or.inl ⟨canonicalCF q, canonicalCF_isCanonical q, ?_⟩
      rw [canonicalCF_value]


theorem valueOfList_cons_ofRat {a : Int} {t : List Int} {r : Rat}
    (hv : valueOfList t = CFValue.ofRat r) (hr : r ≠ 0) :
    valueOfList (a :: t) = CFValue.ofRat ((a : Rat) + r⁻¹) := by
  rw [valueOfList_cons, hv, CFValue.inv_ofRat hr, CFValue.ofInt, CFValue.add_ofRat]

theorem exists_valueOfList_all_pos :
    ∀ t : List Int, t ≠ [] → (∀ a ∈ t, 0 < a) →
      ∃ q : Rat, 1 ≤ q ∧ valueOfList t = CFValue.ofRat q ∧ (q = 1 ↔ t = [1])
  | [], hne, _ => (hne rfl).elim
  | [a], _, hpos => by
      have ha : 0 < a := hpos a (by simp)
      have ha1 : 1 ≤ a := by omega
      refine ⟨(a : Rat), Int.cast_le.mpr ha1, ?_, ?_⟩
      · simp [value_singleton, CFValue.ofInt]
      · constructor
        · intro hq
          have : a = 1 := by exact_mod_cast hq
          simp [this]
        · intro ht
          simp at ht
          simp [ht]
  | a :: b :: rest, _, hpos => by
      have hposr : ∀ x ∈ b :: rest, 0 < x := fun x hx => hpos x (by simp [hx])
      obtain ⟨r, hr1, hv, _⟩ :=
        exists_valueOfList_all_pos (b :: rest) (by simp) hposr
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1)
      have ha1 : 1 ≤ a := by
        have : 0 < a := hpos a (by simp)
        omega
      refine ⟨(a : Rat) + r⁻¹, ?_, valueOfList_cons_ofRat hv hr0, ?_⟩
      · have : (1 : Rat) ≤ a := Int.cast_le.mpr ha1
        have : 0 < r⁻¹ := inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1)
        linarith
      · constructor
        · intro hq
          have : (1 : Rat) ≤ a := Int.cast_le.mpr ha1
          have : 0 < r⁻¹ := inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1)
          linarith
        · intro ht
          simp at ht

theorem exists_valueOfList_nonneg :
    ∀ t : List Int, t ≠ [] → (∀ a ∈ t, 0 ≤ a) → (∀ a ∈ t.tail, 0 < a) →
      ∃ q : Rat, 0 ≤ q ∧ valueOfList t = CFValue.ofRat q
  | [], hne, _, _ => (hne rfl).elim
  | [a], _, hnn, _ => by
      have ha : 0 ≤ a := hnn a (by simp)
      exact ⟨(a : Rat), by exact_mod_cast ha, by simp [value_singleton, CFValue.ofInt]⟩
  | a :: b :: rest, _, hnn, hpos => by
      have hposr : ∀ x ∈ b :: rest, 0 < x := fun x hx => hpos x (by simp [hx])
      obtain ⟨r, hr1, hv, _⟩ :=
        exists_valueOfList_all_pos (b :: rest) (by simp) hposr
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1)
      have ha : 0 ≤ a := hnn a (by simp)
      refine ⟨(a : Rat) + r⁻¹, ?_, valueOfList_cons_ofRat hv hr0⟩
      have : 0 ≤ (a : Rat) := by exact_mod_cast ha
      have : 0 < r⁻¹ := inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1)
      linarith

theorem later_pos_of_nonneg {t : List Int}
    (hnn : ∀ a ∈ t, 0 ≤ a) (hne0 : ∀ a ∈ t.tail, a ≠ 0) :
    ∀ a ∈ t.tail, 0 < a := by
  intro a ha
  exact lt_of_le_of_ne (hnn a (List.mem_of_mem_tail ha)) (hne0 a ha).symm

theorem isStandard_cons_tail {a : Int} {rest : List Int}
    (hs : IsStandard (a :: rest)) (hrest : rest ≠ []) : IsStandard rest := by
  rcases hs with ⟨_, _hnn, hpos, hlast⟩
  refine ⟨hrest, ?_, ?_, Or.inr ?_⟩
  · intro x hx
    exact le_of_lt (hpos x (by simp [hx]))
  · intro x hx
    exact hpos x (List.mem_of_mem_tail hx)
  · have hlen : ¬ (a :: rest).length = 1 := by simp [hrest]
    have hge : 2 ≤ (a :: rest).getLastD 0 := by
      cases hlast with
      | inl h => exact (hlen h).elim
      | inr h => exact h
    have : (a :: rest).getLastD 0 = rest.getLastD 0 := by
      cases rest with
      | nil => exact (hrest rfl).elim
      | cons _ _ => simp [List.getLastD]
    omega

theorem isStandard_eq_euclidPos (d : Nat) (hd : d ≠ 0) :
    ∀ n : Nat, ∀ t : List Int, IsStandard t →
      valueOfList t = CFValue.ofRat ((n : Rat) / (d : Rat)) →
      t = euclidPos n d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n t hs hv
    rcases hs with ⟨hne, hnn, hpos, hlast⟩
    match t with
    | [] => exact (hne rfl).elim
    | a :: rest =>
        have hd0 : (d : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hd
        have ha0 : 0 ≤ a := hnn a (by simp)
        cases rest with
        | nil =>
            have hq : (a : Rat) = (n : Rat) / d := by
              simpa [value_singleton, CFValue.ofInt] using hv
            have hmul : (n : Rat) = a * (d : Rat) := by
              have hq' := hq.symm
              exact (div_eq_iff hd0).mp hq'
            have hndi : (n : Int) = a * (d : Int) := by exact_mod_cast hmul
            have habs : (a.natAbs : Int) = a := Int.natAbs_of_nonneg ha0
            have hnN : n = a.natAbs * d := by
              have : (n : Int) = (a.natAbs : Int) * (d : Int) := by
                rw [habs]; exact hndi
              exact_mod_cast this
            have hmod : n % d = 0 := by
              rw [hnN, Nat.mul_comm]
              exact Nat.mul_mod_right d a.natAbs
            have hdiv : n / d = a.natAbs := by
              rw [hnN, Nat.mul_comm, Nat.mul_div_right _ (Nat.pos_of_ne_zero hd)]
            rw [euclidPos_eq n d hd, if_pos hmod, hdiv]
            simp [abs_of_nonneg ha0]
        | cons b rs =>
            obtain ⟨r, hr1, hvrest, hriff⟩ :=
              exists_valueOfList_all_pos (b :: rs) (by simp)
                (fun x hx => hpos x (by simp [hx]))
            have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : Rat) < 1) hr1
            have hr0 : r ≠ 0 := ne_of_gt hrpos
            have hlast2 : 2 ≤ (a :: b :: rs).getLastD 0 := by
              have hlen : ¬ (a :: b :: rs).length = 1 := by simp
              cases hlast with
              | inl h => exact (hlen h).elim
              | inr h => exact h
            have hne1 : b :: rs ≠ [1] := by
              intro h1
              have : (a :: b :: rs).getLastD 0 = 1 := by simp [h1]
              omega
            have rne : r ≠ 1 := fun h => hne1 (hriff.mp h)
            have rgt : 1 < r := lt_of_le_of_ne hr1 (Ne.symm rne)
            have hvt : valueOfList (a :: b :: rs) =
                CFValue.ofRat ((a : Rat) + r⁻¹) :=
              valueOfList_cons_ofRat hvrest hr0
            have hq : (n : Rat) / d = (a : Rat) + r⁻¹ :=
              CFValue.ofRat_injective (hv.symm.trans hvt)
            have hinvpos : 0 < r⁻¹ := inv_pos.mpr hrpos
            have hinvlt : r⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr rgt
            have hfloor : ⌊(n : Rat) / d⌋ = a := by
              rw [Int.floor_eq_iff]
              constructor <;> linarith
            have haeq : a = ((n / d : Nat) : Int) := by
              rw [← hfloor]
              exact Rat.floor_natCast_div_natCast n d
            have hnmod : n % d ≠ 0 := by
              intro hz
              have hdiv := nat_rat_div_mod n d hd
              have hint : (n : Rat) / d = ((n / d : Nat) : Rat) := by simpa [hz] using hdiv
              have : r⁻¹ = 0 := by
                have ha' : (a : Rat) = ((n / d : Nat) : Rat) := by
                  rw [haeq]
                  exact Int.cast_natCast (n / d)
                linarith [hq, hint, ha']
              exact (ne_of_gt hinvpos this).elim
            have hsub : r⁻¹ = (n % d : Rat) / d := by
              have hfrac := nat_rat_div_mod n d hd
              have hq' := hq
              rw [hfrac, haeq] at hq'
              exact (add_left_cancel hq').symm
            have hrval : r = (d : Rat) / (n % d : Rat) := by
              rw [← inv_inv r, hsub, inv_div]
            have hvrest' : valueOfList (b :: rs) =
                CFValue.ofRat ((d : Rat) / (n % d : Rat)) := by
              rw [hvrest, hrval]
            have hsrest : IsStandard (b :: rs) :=
              isStandard_cons_tail ⟨hne, hnn, hpos, hlast⟩ (by simp)
            have hrestEq :=
              ih (n % d) (Nat.mod_lt n (Nat.pos_of_ne_zero hd)) hnmod d
                (b :: rs) hsrest hvrest'
            rw [euclidPos_eq n d hd, if_neg hnmod, haeq, hrestEq]


theorem eq_append_last {t : List Int} (hne : t ≠ []) :
    ∃ pref a, t = pref ++ [a] :=
  ⟨t.dropLast, t.getLast hne, (List.dropLast_concat_getLast hne).symm⟩

theorem eq_append_two {t : List Int} (h : 2 ≤ t.length) :
    ∃ pref b c, t = pref ++ [b, c] := by
  have hne : t ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨pref1, c, hc⟩ := eq_append_last hne
  have hpref : pref1 ≠ [] := by
    intro hp
    subst hp
    simp [hc] at h
  obtain ⟨pref, b, hb⟩ := eq_append_last hpref
  refine ⟨pref, b, c, ?_⟩
  rw [hc, hb]
  simp

theorem getLast?_append_singleton (pref : List Int) (a : Int) :
    (pref ++ [a]).getLast? = some a := by
  simp

theorem isStandard_singleton_nonneg {a : Int} (ha : 0 ≤ a) : IsStandard [a] :=
  ⟨by simp, by intro x hx; simp at hx; subst hx; exact ha, by simp, Or.inl rfl⟩

theorem isStandard_append_ge_two {pref : List Int} {b : Int}
    (hnn : ∀ x ∈ pref ++ [b], 0 ≤ x) (hpos : ∀ x ∈ (pref ++ [b]).tail, 0 < x)
    (hb : 2 ≤ b) : IsStandard (pref ++ [b]) := by
  refine ⟨by simp, hnn, hpos, Or.inr ?_⟩
  simp
  -- getLastD (pref ++ [b]) = b
  have : (pref ++ [b]).getLastD 0 = b := by simp
  omega

theorem oddify_append_succ {pref : List Int} {b : Int}
    (heven : (pref ++ [b]).length % 2 = 0) :
    oddify (pref ++ [b]) = pref ++ [b - 1, 1] := by
  have hodd : ¬ (pref ++ [b]).length % 2 = 1 := by omega
  unfold oddify
  rw [if_neg hodd]
  have hdrop : (pref ++ [b]).dropLast = pref := by simp
  have hlast : (pref ++ [b]).getLastD 0 = b := by simp
  simp [hdrop]

theorem value_nonneg_of_nonneg_terms {t : List Int} {q : Rat}
    (hne : t ≠ []) (hnn : ∀ a ∈ t, 0 ≤ a) (hpos : ∀ a ∈ t.tail, 0 < a)
    (hv : valueOfList t = CFValue.ofRat q) : 0 ≤ q := by
  obtain ⟨q', hq', hv'⟩ := exists_valueOfList_nonneg t hne hnn hpos
  have : q = q' := CFValue.ofRat_injective (hv.symm.trans hv')
  linarith

theorem nonneg_eq_num_div_den {q : Rat} (h : 0 ≤ q) :
    (q.num.natAbs : Rat) / (q.den : Rat) = q := by
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr h
  have habs : (q.num.natAbs : Int) = q.num := Int.natAbs_of_nonneg hn0
  have hcast : (q.num.natAbs : Rat) = (q.num : Rat) :=
    congrArg (fun k : Int => (k : Rat)) habs
  rw [hcast, num_div_den_eq]

/-- Nonnegative odd-length one-sign expansions are `canonicalTerms q`. -/
theorem nonneg_odd_eq_canonicalTerms {t : List Int} (hne : t ≠ [])
    (hodd : t.length % 2 = 1) (hnn : ∀ a ∈ t, 0 ≤ a)
    (hpos : ∀ a ∈ t.tail, 0 < a) {q : Rat}
    (hv : valueOfList t = CFValue.ofRat q) :
    t = canonicalTerms q := by
  have hq : 0 ≤ q := value_nonneg_of_nonneg_terms hne hnn hpos hv
  have hcan : canonicalTerms q = oddify (euclidPos q.num.natAbs q.den) := by
    unfold canonicalTerms
    simp [not_lt.mpr hq]
  by_cases hlen : t.length = 1
  · obtain ⟨a, ha⟩ : ∃ a, t = [a] := by
      cases t with
      | nil => exact (hne rfl).elim
      | cons a rest =>
          cases rest with
          | nil => exact ⟨a, rfl⟩
          | cons _ _ => simp at hlen
    subst ha
    have hs : IsStandard [a] := isStandard_singleton_nonneg (hnn a (by simp))
    have hv' : valueOfList [a] = CFValue.ofRat ((q.num.natAbs : Rat) / q.den) := by
      rw [hv, nonneg_eq_num_div_den hq]
    have heq : [a] = euclidPos q.num.natAbs q.den :=
      isStandard_eq_euclidPos q.den q.den_nz q.num.natAbs [a] hs hv'
    have hodd1 : ([a] : List Int).length % 2 = 1 := by simp
    rw [hcan, ← heq, oddify_of_odd hodd1]
  · have hge : 3 ≤ t.length := by omega
    obtain ⟨pref, b, c, ht⟩ := eq_append_two (by omega : 2 ≤ t.length)
    have hpref_ne : pref ≠ [] := by
      intro hp; subst hp; simp [ht] at hge
    subst ht
    have hcpos : 0 < c := by
      have : c ∈ (pref ++ [b, c]).tail := by
        cases pref with
        | nil => exact (hpref_ne rfl).elim
        | cons _ _ => simp
      exact hpos c this
    have hbpos : 0 < b := by
      have : b ∈ (pref ++ [b, c]).tail := by
        cases pref with
        | nil => exact (hpref_ne rfl).elim
        | cons _ _ => simp
      exact hpos b this
    by_cases hc1 : c = 1
    · subst hc1
      have hval : valueOfList (pref ++ [b + 1]) = CFValue.ofRat q := by
        rw [← valueOfList_concat_one, hv]
      have hb1 : 2 ≤ b + 1 := by omega
      have hnn' : ∀ x ∈ pref ++ [b + 1], 0 ≤ x := by
        intro x hx
        simp [List.mem_append, List.mem_cons] at hx
        rcases hx with hmem | rfl
        · exact hnn x (by simp [hmem])
        · omega
      have hpos' : ∀ x ∈ (pref ++ [b + 1]).tail, 0 < x := by
        intro x hx
        cases pref with
        | nil => exact (hpref_ne rfl).elim
        | cons p ps =>
            simp [List.mem_append, List.mem_cons] at hx
            rcases hx with hmem | rfl
            · exact hpos x (by simp [hmem])
            · omega
      have hs : IsStandard (pref ++ [b + 1]) :=
        isStandard_append_ge_two hnn' hpos' hb1
      have hv' : valueOfList (pref ++ [b + 1]) =
          CFValue.ofRat ((q.num.natAbs : Rat) / q.den) := by
        rw [hval, nonneg_eq_num_div_den hq]
      have heq : pref ++ [b + 1] = euclidPos q.num.natAbs q.den :=
        isStandard_eq_euclidPos q.den q.den_nz q.num.natAbs _ hs hv'
      have heven : (pref ++ [b + 1]).length % 2 = 0 := by
        have : (pref ++ [b, 1]).length % 2 = 1 := hodd
        simp at this ⊢
        omega
      rw [hcan, ← heq, oddify_append_succ heven]
      simp
    · have hcge : 2 ≤ c := by omega
      have hs : IsStandard (pref ++ [b, c]) := by
        refine ⟨by simp, hnn, hpos, Or.inr ?_⟩
        have : (pref ++ [b, c]).getLastD 0 = c := by simp
        omega
      have hv' : valueOfList (pref ++ [b, c]) =
          CFValue.ofRat ((q.num.natAbs : Rat) / q.den) := by
        rw [hv, nonneg_eq_num_div_den hq]
      have heq : pref ++ [b, c] = euclidPos q.num.natAbs q.den :=
        isStandard_eq_euclidPos q.den q.den_nz q.num.natAbs _ hs hv'
      rw [hcan, ← heq]
      exact (oddify_of_odd hodd).symm

theorem map_neg_map_neg (t : List Int) :
    (t.map fun n => -n).map (fun n => -n) = t := by
  simp [List.map_map]

theorem canonicalTerms_neg {q : Rat} (hq : q < 0) :
    canonicalTerms q = (canonicalTerms (-q)).map fun n => -n := by
  have hnn : ¬ (-q) < 0 := by linarith
  have hnum : (-q).num.natAbs = q.num.natAbs := by
    rw [Rat.num_neg_eq_neg_num, Int.natAbs_neg]
  have hden : (-q).den = q.den := Rat.den_neg_eq_den q
  unfold canonicalTerms
  rw [if_pos hq, if_neg hnn, hnum, hden]

/-- Any odd-length one-sign expansion of a rational equals `canonicalTerms q`. -/
theorem canonicalTerms_unique {t : List Int} (hne : t ≠ [])
    (hodd : t.length % 2 = 1) (hlt : ∀ a ∈ t.tail, a ≠ 0)
    (halt : (∀ a ∈ t, 0 ≤ a) ∨ (∀ a ∈ t, a ≤ 0)) {q : Rat}
    (hv : valueOfList t = CFValue.ofRat q) : t = canonicalTerms q := by
  rcases halt with hnn | hnp
  · exact nonneg_odd_eq_canonicalTerms hne hodd hnn
      (later_pos_of_nonneg hnn hlt) hv
  · set t' := t.map fun n => -n
    have hne' : t' ≠ [] := by simp [t', hne]
    have hodd' : t'.length % 2 = 1 := by simp [t', hodd]
    have hnn' : ∀ a ∈ t', 0 ≤ a := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
      have := hnp b hb
      omega
    have hpos' : ∀ a ∈ t'.tail, 0 < a := by
      intro a ha
      have hne0 := later_map_neg hlt a ha
      have : 0 ≤ a := hnn' a (List.mem_of_mem_tail ha)
      omega
    have hv' : valueOfList t' = CFValue.ofRat (-q) := by
      rw [valueOfList_neg, hv, CFValue.neg_ofRat]
    have ht' : t' = canonicalTerms (-q) :=
      nonneg_odd_eq_canonicalTerms hne' hodd' hnn' hpos' hv'
    have hqle : q ≤ 0 := by
      have : 0 ≤ -q := value_nonneg_of_nonneg_terms hne' hnn' hpos' hv'
      linarith
    by_cases hneg : q < 0
    · rw [canonicalTerms_neg hneg, ← ht', map_neg_map_neg]
    · have hq0 : q = 0 := le_antisymm hqle (le_of_not_gt hneg)
      subst hq0
      have htneg : t = t'.map fun n => -n := (map_neg_map_neg t).symm
      rw [htneg, ht']
      have heu : euclidPos 0 1 = [0] := by
        rw [euclidPos_eq 0 1 (by decide)]
        simp
      simp [canonicalTerms, heu, oddify]

/-- A canonical expansion of `q` is definitionally `canonicalCF q`. -/
theorem canonicalCF_unique {cf : ArithmeticCF} (hc : cf.IsCanonical) {q : Rat}
    (hv : cf.value = CFValue.ofRat q) : cf = canonicalCF q :=
  ArithmeticCF.ext <|
    canonicalTerms_unique cf.terms_ne hc.1 cf.later_ne_zero hc.2 hv

theorem isCanonical_value_ne_inf {cf : ArithmeticCF} (hc : cf.IsCanonical) :
    cf.value ≠ CFValue.inf := by
  rcases hc with ⟨_hodd, hsign⟩
  rcases hsign with hnn | hnp
  · obtain ⟨q, _, hv⟩ :=
      exists_valueOfList_nonneg cf.terms cf.terms_ne hnn
        (later_pos_of_nonneg hnn cf.later_ne_zero)
    simp [ArithmeticCF.value, hv]
  · set t' := cf.terms.map fun n => -n
    have hnn' : ∀ a ∈ t', 0 ≤ a := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
      have := hnp b hb
      omega
    have hpos' : ∀ a ∈ t'.tail, 0 < a := by
      intro a ha
      have hne0 := later_map_neg cf.later_ne_zero a ha
      have : 0 ≤ a := hnn' a (List.mem_of_mem_tail ha)
      omega
    obtain ⟨q, _, hv⟩ :=
      exists_valueOfList_nonneg t' (by simp [t', cf.terms_ne]) hnn' hpos'
    have hneg : (valueOfList cf.terms).neg = CFValue.ofRat q := by
      rw [← valueOfList_neg, hv]
    intro hinf
    have hinf' : valueOfList cf.terms = CFValue.inf := hinf
    rw [hinf', CFValue.neg_inf] at hneg
    cases hneg

/-- Proposition 3, uniqueness: a finite continued-fraction value has at most
    one odd-length one-sign expansion. The infinity value has none. -/
theorem continued_fraction_canonical_unique {cf₁ cf₂ : ArithmeticCF}
    (h₁ : cf₁.IsCanonical) (h₂ : cf₂.IsCanonical)
    (hv : cf₁.value = cf₂.value) : cf₁ = cf₂ := by
  cases hv₁ : cf₁.value with
  | inf => exact (isCanonical_value_ne_inf h₁ hv₁).elim
  | ofRat q =>
      have e1 : cf₁ = canonicalCF q := canonicalCF_unique h₁ hv₁
      have e2 : cf₂ = canonicalCF q := canonicalCF_unique h₂ (hv.symm.trans hv₁)
      exact e1.trans e2.symm

end RationalTangles
