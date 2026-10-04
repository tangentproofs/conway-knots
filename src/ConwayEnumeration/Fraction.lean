/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

/-!
# Integer fractions for Conway rational tangles

Computational `num/den` pairs. Invariant (maintained by constructors, not
enforced in the type): `den > 0` and `Nat.gcd num.natAbs den = 1`.
No Mathlib — enumeration only.
-/

namespace ConwayEnumeration

/-- A reduced fraction `num/den` with positive denominator. -/
structure Frac where
  num : Int
  den : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Frac

/-- Reduce `n/d`. Returns `none` when `d = 0`. -/
def ofInts (n d : Int) : Option Frac :=
  if d = 0 then none
  else
    let g : Int := Int.gcd n d
    let n' := n / g
    let d' := d / g
    if d' < 0 then
      some { num := -n', den := (-d').toNat }
    else
      some { num := n', den := d'.toNat }

/-- Reduce `n / d` for a positive `Nat` denominator. -/
def ofIntNat (n : Int) (d : Nat) : Frac :=
  if d = 0 then { num := 0, den := 1 }
  else
    let g := Nat.gcd n.natAbs d
    { num := n / (g : Int), den := d / g }

/-- Reciprocal. `none` when the numerator is zero. -/
def inv? (f : Frac) : Option Frac :=
  if f.num = 0 then none
  else ofInts (f.den : Int) f.num

/-- Addition. -/
def add (a b : Frac) : Frac :=
  ofIntNat (a.num * (b.den : Int) + b.num * (a.den : Int)) (a.den * b.den)

/-- Absolute value of the numerator. -/
def numAbs (f : Frac) : Nat := f.num.natAbs

/-- Evaluate continued fraction `[a₀; a₁, …]` (Conway integer twists). -/
def ofContinuedFraction : List Int → Option Frac
  | [] => some (ofIntNat 0 1)
  | [a] => some (ofIntNat a 1)
  | a :: rest =>
      match ofContinuedFraction rest with
      | none => none
      | some t =>
          match t.inv? with
          | none => none
          | some invt => some ((ofIntNat a 1).add invt)

/-- Decimal-ish string `num/den`. -/
def toString (f : Frac) : String :=
  s!"{f.num}/{f.den}"

instance : ToString Frac where
  toString := Frac.toString

end Frac

end ConwayEnumeration
