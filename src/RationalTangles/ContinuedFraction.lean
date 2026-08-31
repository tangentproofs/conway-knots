/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Data.Rat.Init

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

/-- `-1/x`. -/
def negInv (x : CFValue) : CFValue := (inv x).neg

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

/-- Evaluate a (possibly empty, possibly with internal zeros) integer list as
    a simple continued fraction, taking values in `Rat ∪ {∞}`. The empty list
    evaluates to `∞`. -/
def valueOfList (terms : List Int) : CFValue :=
  let AB := continuants terms
  if AB.2 = 0 then .inf else .ofRat (Rat.divInt AB.1 AB.2)

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
