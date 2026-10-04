/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import ConwayEnumeration.Fraction

/-!
# Rational (2-bridge) prime knots via Conway continued-fraction notation

Conway (1970) builds knots by substituting algebraic tangles into basic
polyhedra. The **rational** (2-bridge) fragment is the special case of the
numerator closure of a rational tangle. Every prime knot through **7**
crossings is rational; beyond that, non-rational algebraic and polyhedral
knots appear (first at 8 crossings).

## Method implemented

1. Generate all positive continued-fraction sequences summing to `n`
   (regular form: last partial quotient ≥ 2 when length > 1).
2. Evaluate to a reduced fraction `p/q`.
3. Keep 2-bridge **knots** only: after clearing content, `|p|` odd and `> 1`.
4. Identify mirror images and Schubert equivalences
   `q ~ ±q⁻¹ (mod p)` to a single key `(p, q*)`.
5. Crossing number := minimum sequence-sum over expansions of that knot.

## Known gaps (honest)

* **Not** a full Conway census through 11: basic polyhedra (`6*`, `8*`, …)
  and non-rational algebraic tangles are **not** enumerated here.
* Flype / polyhedral symmetry reduction for non-rational diagrams: **out of
  scope** on this path (matches the repo's rational-tangle theorem track).
* Notation strings are one minimal-crossing positive CF for each Schubert
  class; they need not match Conway's printed spelling order (e.g. `23`
  vs `32` for `5₂`).

Expected 2-bridge prime counts by crossing number `3..11`:
`1, 1, 2, 3, 7, 12, 24, 45, 91`.
Total prime knots `3..7` coincide; at `8+` this enumerator undercounts
the full prime-knot census (`21, 49, …`).
-/

namespace ConwayEnumeration

/-- Schubert key for a rational knot up to mirror: `(p, q)` with `p` odd `> 1`
    and `1 ≤ q ≤ p/2`, after identifying modular inverses. -/
abbrev SchubertKey := Nat × Nat

/-- Extended gcd on `Nat`, returning `(g, s, t)` with `s*a + t*b = g`. -/
partial def natEgcd (a b : Nat) : Nat × Int × Int :=
  if b = 0 then (a, 1, 0)
  else
    let (g, s, t) := natEgcd b (a % b)
    (g, t, s - t * (a / b : Int))

/-- Modular inverse of `a` modulo `p`, or `none`. -/
def natModInv (a p : Nat) : Option Nat :=
  if p = 0 then none
  else
    let (g, s, _) := natEgcd (a % p) p
    if g ≠ 1 then none
    else
      let m := s % (p : Int)
      some (if m < 0 then (m + (p : Int)).toNat else m.toNat)

/-- Canonical Schubert key for fraction `num/den`, or `none` if not a
    nontrivial 2-bridge knot (link, unknot, or degenerate). -/
def schubertKey (num : Int) (den : Nat) : Option SchubertKey :=
  if den = 0 then none
  else
    let g := Nat.gcd num.natAbs den
    let p := num.natAbs / g
    let q0 := den / g
    if p ≤ 1 then none
    else if p % 2 = 0 then none
    else if q0 = 0 then none
    else
      let q := q0 % p
      if q = 0 then none
      else
        let invs : List Nat :=
          match natModInv q p with
          | none => []
          | some i => [i, p - i]
        let candidates := ([q, p - q] ++ invs).filter (fun c => decide (1 ≤ c ∧ c < p))
        match candidates.min? with
        | none => none
        | some qmin => some (p, qmin)

/-- Conway-style string of a twist sequence, e.g. `[3, 2] ↦ "32"`. -/
def twistsToString (twists : List Nat) : String :=
  String.join (twists.map ToString.toString)

/-- One enumerated rational prime knot. -/
structure RationalPrimeKnot where
  /-- Crossing number (minimal positive-CF length sum). -/
  crossingNumber : Nat
  /-- Schubert key `(p, q)`. -/
  key : SchubertKey
  /-- One positive continued-fraction notation of that crossing number. -/
  twists : List Nat
  deriving Repr

namespace RationalPrimeKnot

def conwayNotation (k : RationalPrimeKnot) : String :=
  twistsToString k.twists

def toString (k : RationalPrimeKnot) : String :=
  s!"cr={k.crossingNumber}  Conway {k.conwayNotation}  Schubert {k.key.1}/{k.key.2}"

instance : ToString RationalPrimeKnot where
  toString := RationalPrimeKnot.toString

end RationalPrimeKnot

/-- Append one part `x` onto every sequence that finishes `remaining`. -/
partial def compositionsFrom (remaining : Nat) (acc : List Nat) : List (List Nat) :=
  if remaining = 0 then
    [acc.reverse]
  else
    Id.run do
      let mut out : List (List Nat) := []
      for i in [1:remaining+1] do
        out := out ++ compositionsFrom (remaining - i) (i :: acc)
      return out

/-- All positive compositions of `n`; if length > 1, require last entry ≥ 2. -/
def positiveCFSequences (n : Nat) : List (List Nat) :=
  if n = 0 then []
  else
    (compositionsFrom n []).filter fun seq =>
      match seq with
      | [] => false
      | [_] => true
      | _ => seq.getLast! ≥ 2

/-- Evaluate a positive CF sequence to a `Frac`. -/
def evalPositiveCF (twists : List Nat) : Option Frac :=
  Frac.ofContinuedFraction (twists.map Int.ofNat)

/-- Collect Schubert keys reached by diagrams of exactly `n` crossings. -/
def diagramsAt (n : Nat) : List (SchubertKey × List Nat) :=
  (positiveCFSequences n).filterMap fun seq =>
    match evalPositiveCF seq with
    | none => none
    | some f =>
        match schubertKey f.num f.den with
        | none => none
        | some key => some (key, seq)

/-- Lexicographic ≤ on `Nat` lists. -/
def listNatLE : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true
      else if x > y then false
      else listNatLE xs ys

/-- Prefer shorter sequences, then lexicographically smaller. -/
def betterNotation (a b : List Nat) : Bool :=
  if a.length < b.length then true
  else if a.length > b.length then false
  else listNatLE a b

/-- Replace or insert a knot record for `key` at crossing number `n`. -/
def upsertKnot (acc : List (SchubertKey × Nat × List Nat))
    (key : SchubertKey) (n : Nat) (seq : List Nat) :
    List (SchubertKey × Nat × List Nat) :=
  match acc.findIdx? (fun t => t.1 == key) with
  | none => (key, n, seq) :: acc
  | some i =>
      let (k, cr, old) := acc[i]!
      let (cr', seq') :=
        if n < cr then (n, seq)
        else if n > cr then (cr, old)
        else if betterNotation seq old then (cr, seq)
        else (cr, old)
      acc.set i (k, cr', seq')

/-- Fold diagrams at crossing number `n` into the accumulator. -/
def mergeKnots (acc : List (SchubertKey × Nat × List Nat))
    (n : Nat) (diags : List (SchubertKey × List Nat)) :
    List (SchubertKey × Nat × List Nat) :=
  diags.foldl (fun acc pair => upsertKnot acc pair.1 n pair.2) acc

/-- Enumerate distinct rational prime knots with crossing number ≤ `maxN`. -/
def enumerateRationalPrimes (maxN : Nat) : List RationalPrimeKnot :=
  let merged : List (SchubertKey × Nat × List Nat) :=
    (List.range maxN).foldl (fun acc i =>
      let n := i + 1
      mergeKnots acc n (diagramsAt n)) []
  let knots := merged.map fun (key, cr, seq) =>
    ({ crossingNumber := cr, key := key, twists := seq } : RationalPrimeKnot)
  knots.toArray.qsort (fun a b =>
      a.crossingNumber < b.crossingNumber ||
      (a.crossingNumber == b.crossingNumber && listNatLE a.twists b.twists))
    |>.toList

/-- Count rational primes by crossing number for `cr ∈ [lo, hi]`. -/
def countsByCrossing (knots : List RationalPrimeKnot) (lo hi : Nat) :
    List (Nat × Nat) :=
  (List.range (hi + 1 - lo)).map fun i =>
    let cr := lo + i
    (cr, (knots.filter (·.crossingNumber == cr)).length)

/-- Classical 2-bridge prime counts for crossing numbers 3 through 11. -/
def expectedTwoBridgeCounts : List (Nat × Nat) :=
  [(3, 1), (4, 1), (5, 2), (6, 3), (7, 7), (8, 12), (9, 24), (10, 45), (11, 91)]

/-- Classical total prime-knot counts (mirrors identified), OEIS A002863. -/
def expectedAllPrimeCounts : List (Nat × Nat) :=
  [(3, 1), (4, 1), (5, 2), (6, 3), (7, 7), (8, 21), (9, 49), (10, 165), (11, 552)]

end ConwayEnumeration
