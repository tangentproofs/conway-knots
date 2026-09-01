/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith

/-!
# Arithmetic continued fractions

Kauffman–Lambropoulou §3 write every rational as a finite simple continued
fraction
$$
[a_1,a_2,\ldots,a_n]
:= a_1 + \cfrac{1}{a_2+\cdots+\cfrac{1}{a_n}}
$$
with `a₁ ∈ Int` (possibly zero) and `a₂, …, aₙ ∈ Int \ {0}`. The value lives in
`Rat` together with a formal infinity `∞ = 1/0`, matching `F([∞])`.

Mathlib's `Algebra.ContinuedFractions` develops generalised, simple, and
regular continued fractions as (possibly infinite) sequences of partial
numerator/denominator pairs. Regular CFs require *positive* partial
denominators, and evaluation takes values in a field (no formal `∞`). That
does not match the finite signed expansions used for tangle fractions, so
this file does not reuse it. Canonical form (termwise positive or negative,
odd length) is left to a later article.
-/

namespace RationalTangles

/-- Values of arithmetic continued fractions: a rational, or formal infinity
    `1/0`. -/
inductive CFValue where
  | ofRat : Rat → CFValue
  | inf : CFValue
  deriving DecidableEq, Repr

namespace CFValue

/-- The integer `n`, viewed as a continued-fraction value. -/
def ofInt (n : Int) : CFValue :=
  .ofRat (n : Rat)

/-- Reciprocal, with the formal rules `1/0 = ∞` and `1/∞ = 0`. -/
def inv : CFValue → CFValue
  | ofRat q => if q = 0 then inf else ofRat q⁻¹
  | inf => ofRat 0

/-- Addition, with `∞ + x = x + ∞ = ∞`. -/
def add : CFValue → CFValue → CFValue
  | ofRat a, ofRat b => ofRat (a + b)
  | inf, _ => inf
  | _, inf => inf

/-- Negation, with `-∞ = ∞` (the single point at infinity on `ℝP¹`). -/
def neg : CFValue → CFValue
  | ofRat q => ofRat (-q)
  | inf => inf

instance : Zero CFValue := ⟨ofRat 0⟩
instance : One CFValue := ⟨ofRat 1⟩
instance : Coe Rat CFValue := ⟨ofRat⟩
instance : Neg CFValue := ⟨neg⟩

@[simp] theorem neg_ofRat (q : Rat) : neg (ofRat q) = ofRat (-q) := rfl
@[simp] theorem neg_inf : neg inf = inf := rfl
@[simp] theorem neg_neg (x : CFValue) : neg (neg x) = x := by
  cases x <;> simp [neg]

theorem add_inf_left (x : CFValue) : inf.add x = inf := rfl
theorem add_ofRat_inf (q : Rat) : (ofRat q).add inf = inf := rfl

@[simp] theorem inv_inf : inv inf = (0 : CFValue) := rfl

theorem inv_ofRat {q : Rat} (hq : q ≠ 0) : inv (ofRat q) = ofRat q⁻¹ := by
  simp [inv, hq]

@[simp] theorem add_ofRat (a b : Rat) : (ofRat a).add (ofRat b) = ofRat (a + b) := rfl

theorem add_assoc (x y z : CFValue) : (x.add y).add z = x.add (y.add z) := by
  cases x <;> cases y <;> cases z <;> simp [add, Rat.add_assoc]

theorem add_comm (x y : CFValue) : x.add y = y.add x := by
  cases x <;> cases y <;> simp [add, Rat.add_comm]

theorem add_zero (x : CFValue) : x.add (ofRat 0) = x := by
  cases x <;> simp [add]

theorem zero_add (x : CFValue) : (ofRat 0).add x = x := by
  cases x <;> simp [add]

@[simp] theorem inv_inv (x : CFValue) : x.inv.inv = x := by
  cases x with
  | inf => rfl
  | ofRat q =>
    by_cases h : q = 0
    · simp [inv, h]
    · simp [inv, h]

/-- `-1/x`. -/
def negInv (x : CFValue) : CFValue := (inv x).neg

@[simp] theorem ofInt_add (a b : Int) :
    (ofInt a).add (ofInt b) = ofInt (a + b) := by
  simp [ofInt]

theorem ofInt_zero : ofInt 0 = ofRat 0 := rfl

theorem inv_ofInt_zero : (ofInt 0).inv = inf := by
  simp [ofInt, inv]

theorem ofRat_injective {p q : Rat} (h : ofRat p = ofRat q) : p = q := by
  cases h; rfl

theorem neg_add (x y : CFValue) : (x.add y).neg = x.neg.add y.neg := by
  cases x <;> cases y <;> simp [add, neg]
  linarith

theorem neg_inv (x : CFValue) : x.inv.neg = x.neg.inv := by
  cases x with
  | inf => simp [inv, neg]
  | ofRat q =>
    by_cases hq : q = 0
    · simp [inv, neg, hq]
    · have hnq : -q ≠ 0 := by intro h; apply hq; linarith
      simp [inv, neg, hq, hnq, inv_neg]

@[simp] theorem ofInt_neg (n : Int) : ofInt (-n) = (ofInt n).neg := by
  simp [ofInt, neg]

end CFValue

/-- Continuants `(A, B)` of a finite simple continued fraction. The empty
    expansion is `(1, 0)`, i.e. formal infinity. For `[a₁, …, aₙ]` the pair
    satisfies `[a₁, …, aₙ] = A/B`, with `B = 0` representing `∞`.

    Recurrence: `A₋₁ = 1`, `B₋₁ = 0`, `A₀ = a₁`, `B₀ = 1`, and
    `Aₖ = aₖ₊₁ Aₖ₋₁ + Aₖ₋₂`, `Bₖ = aₖ₊₁ Bₖ₋₁ + Bₖ₋₂`. -/
def continuants : List Int → Int × Int
  | [] => (1, 0)
  | a :: rest =>
    let rec go : List Int → Int → Int → Int → Int → Int × Int
      | [], A, B, _, _ => (A, B)
      | x :: xs, A, B, Ap, Bp => go xs (x * A + Ap) (x * B + Bp) A B
    go rest a 1 1 0

/-- Evaluate a (possibly empty) integer list as a simple continued fraction,
    taking values in `Rat ∪ {∞}`. The empty list evaluates to `∞`. This is the
    recursive rule `[a] + 1/[tail]`. -/
def valueOfList : List Int → CFValue
  | [] => .inf
  | a :: t => (CFValue.ofInt a).add (valueOfList t).inv

theorem valueOfList_nil : valueOfList [] = .inf := rfl

theorem valueOfList_cons (a : Int) (t : List Int) :
    valueOfList (a :: t) = (CFValue.ofInt a).add (valueOfList t).inv := rfl

theorem valueOfList_neg : ∀ t : List Int,
    valueOfList (t.map (fun n => -n)) = (valueOfList t).neg
  | [] => rfl
  | a :: t => by
    rw [List.map_cons, valueOfList_cons, valueOfList_cons, valueOfList_neg t]
    simp [CFValue.ofInt_neg, CFValue.neg_add, CFValue.neg_inv]

def absSum : List Int → Nat
  | [] => 0
  | a :: t => a.natAbs + absSum t

theorem absSum_cons (a : Int) (t : List Int) :
    absSum (a :: t) = a.natAbs + absSum t := rfl

theorem absSum_map_neg : ∀ t : List Int, absSum (t.map (fun n => -n)) = absSum t
  | [] => rfl
  | a :: t => by simp [absSum, absSum_map_neg t]

def IsAlternating (t : List Int) : Prop :=
  (∀ a ∈ t, 0 ≤ a) ∨ (∀ a ∈ t, a ≤ 0)

def oppSign (a b : Int) : Prop :=
  (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b)

theorem isAlternating_singleton (a : Int) : IsAlternating [a] := by
  unfold IsAlternating
  by_cases h : 0 ≤ a
  · exact Or.inl (by intro x hx; simp at hx; subst hx; exact h)
  · exact Or.inr (by intro x hx; simp at hx; subst hx; omega)

theorem absSum_append : ∀ s t : List Int, absSum (s ++ t) = absSum s + absSum t
  | [], t => by simp [absSum]
  | a :: s, t => by simp [absSum, absSum_append s t, Nat.add_assoc]

/-- Head transfer of a mixed-sign pair, matching Figure 14 / Proposition 3. -/
def transferHead (a b : Int) (rest : List Int) : List Int :=
  if 0 < a then
    (a - 1) :: 1 :: (-(b + 1)) :: rest.map (fun n => -n)
  else
    (a + 1) :: (-1) :: (1 - b) :: rest.map (fun n => -n)

theorem natAbs_sub_one_of_pos {a : Int} (h : 0 < a) :
    (a - 1).natAbs = a.natAbs - 1 := by
  have h0 : 0 ≤ a := le_of_lt h
  have h1 : 0 ≤ a - 1 := by omega
  have ea := Int.eq_natAbs_of_nonneg h0
  have e1 := Int.eq_natAbs_of_nonneg h1
  have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (ne_of_gt h)
  exact_mod_cast (by omega : ((a - 1).natAbs : Int) = (a.natAbs : Int) - 1)

theorem natAbs_add_one_of_neg {a : Int} (h : a < 0) :
    (a + 1).natAbs = a.natAbs - 1 := by
  have hneg : 0 ≤ -a := by omega
  have hneg1 : 0 ≤ -(a + 1) := by omega
  have ea : (a.natAbs : Int) = -a := by
    have := Int.eq_natAbs_of_nonneg hneg
    simp at this
    omega
  have ea1 : ((a + 1).natAbs : Int) = -(a + 1) := by
    have := Int.eq_natAbs_of_nonneg hneg1
    simp at this
    omega
  have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (ne_of_lt h)
  exact_mod_cast (by omega : ((a + 1).natAbs : Int) = (a.natAbs : Int) - 1)

theorem absSum_transferHead (a b : Int) (rest : List Int)
    (h : oppSign a b) :
    absSum (transferHead a b rest) < a.natAbs + b.natAbs + absSum rest := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hif : 0 < a := ha
    unfold transferHead
    rw [if_pos hif]
    simp only [absSum, absSum_map_neg]
    rw [Int.natAbs_neg, natAbs_sub_one_of_pos ha, natAbs_add_one_of_neg hb]
    have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
    have : 1 ≤ b.natAbs := Int.natAbs_pos.mpr (ne_of_lt hb)
    omega
  · have hif : ¬ 0 < a := by omega
    unfold transferHead
    rw [if_neg hif]
    simp only [absSum, absSum_map_neg]
    have h1 : (a + 1).natAbs = a.natAbs - 1 := natAbs_add_one_of_neg ha
    have h2 : (1 - b).natAbs = b.natAbs - 1 := by
      have : 1 - b = -(b - 1) := by omega
      rw [this, Int.natAbs_neg, natAbs_sub_one_of_pos hb]
    rw [h1, h2]
    have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr (ne_of_lt ha)
    have : 1 ≤ b.natAbs := Int.natAbs_pos.mpr (ne_of_gt hb)
    omega

/-- Rewrite the first mixed-sign adjacent pair. -/
def applyFirstTransfer : List Int → List Int
  | [] => []
  | [_a] => [_a]
  | a :: b :: rest =>
      if (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b) then
        transferHead a b rest
      else
        a :: applyFirstTransfer (b :: rest)

theorem applyFirstTransfer_ne : ∀ t : List Int, t ≠ [] → applyFirstTransfer t ≠ []
  | [], h => (h rfl).elim
  | [_a], _ => by simp [applyFirstTransfer]
  | a :: b :: rest, _ => by
      simp only [applyFirstTransfer]
      split_ifs
      · unfold transferHead; split_ifs <;> simp
      · simp

/-- Drop later zeros via `[x, 0, y, …] = [x + y, …]` and `[x, 0] = ∞`. -/
def contract : List Int → List Int
  | [] => []
  | [x] => [x]
  | _x :: 0 :: [] => []
  | x :: 0 :: y :: ys => contract ((x + y) :: ys)
  | x :: y :: ys =>
      let t' := contract (y :: ys)
      if t' = [] then [x] else x :: t'
termination_by
  t => t.length
decreasing_by
  all_goals (simp [List.length]; try omega)

theorem absSum_contract (t : List Int) : absSum (contract t) ≤ absSum t := by
  generalize hn : t.length = n
  induction n using Nat.strongRecOn generalizing t with
  | ind n ih =>
    match t with
    | [] => simp [contract, absSum]
    | [x] => simp [contract, absSum]
    | x :: y :: ys =>
        by_cases hy : y = 0
        · subst hy
          match ys with
          | [] => simp [contract, absSum]
          | z :: zs =>
              have hlen : ((x + z) :: zs).length < n := by
                subst hn; simp
              have ih' := ih _ hlen ((x + z) :: zs) rfl
              have hle := Int.natAbs_add_le x z
              simp [contract, absSum] at ih' ⊢
              omega
        · have hlen : (y :: ys).length < n := by
            subst hn; simp
          have ih' := ih _ hlen (y :: ys) rfl
          have hc : contract (x :: y :: ys) =
              if contract (y :: ys) = [] then [x] else x :: contract (y :: ys) := by
            simp [contract, hy]
          rw [hc]
          split_ifs with hempty
          · simp [absSum]
          · simp [absSum] at ih' ⊢
            omega

/-- A finite simple continued fraction `[a₁, …, aₙ]` as in
    Kauffman–Lambropoulou §3: nonempty, with every term after the first
    nonzero. The leading term may be zero. The value `∞` is not a separate
    expansion; it arises from evaluation (for example `[1, -1, 1]`). -/
structure ArithmeticCF where
  /-- The terms `a₁, …, aₙ`. -/
  terms : List Int
  /-- The expansion is nonempty (`n ≥ 1`). -/
  terms_ne : terms ≠ []
  /-- Later terms `a₂, …, aₙ` are nonzero. -/
  later_ne_zero : ∀ a ∈ terms.tail, a ≠ 0

namespace ArithmeticCF

/-- Integer continued fraction `[a]`. -/
def ofInteger (a : Int) : ArithmeticCF where
  terms := [a]
  terms_ne := by simp
  later_ne_zero := by simp

/-- `[head] ++ later`, with a proof that every later term is nonzero. -/
def ofTerms (head : Int) (later : List Int) (h : ∀ a ∈ later, a ≠ 0) : ArithmeticCF where
  terms := head :: later
  terms_ne := by simp
  later_ne_zero := h

/-- The length `n` of `[a₁, …, aₙ]`. -/
def length (cf : ArithmeticCF) : Nat :=
  cf.terms.length

/-- The value `[a₁, …, aₙ] ∈ Rat ∪ {∞}`. -/
def value (cf : ArithmeticCF) : CFValue :=
  valueOfList cf.terms

end ArithmeticCF

end RationalTangles
