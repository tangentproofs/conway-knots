/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import ConwayEnumeration

/-!
# `enumerate_knots` executable

Usage:
```
lake exe enumerate_knots -- 7
lake exe enumerate_knots -- 8 --check
```

Prints distinct rational (2-bridge) prime-knot Conway notations with crossing
number ≤ the given bound. With `--check`, also compares counts against the
classical 2-bridge sequence and notes where the full prime-knot census diverges.
-/

open ConwayEnumeration

/-- Parse a Nat CLI argument. -/
def parseNat (s : String) : Option Nat :=
  s.toNat?

/-- Print one knot line. -/
def printKnot (k : RationalPrimeKnot) : IO Unit :=
  IO.println s!"  cr={k.crossingNumber}  Conway {k.conwayNotation}  Schubert {k.key.1}/{k.key.2}"

/-- Summarize counts and compare to classical tables when `check`. -/
def printSummary (knots : List RationalPrimeKnot) (maxN : Nat) (check : Bool) : IO Unit := do
  IO.println ""
  IO.println s!"Rational (2-bridge) prime knots with crossing number ≤ {maxN}: {knots.length} total"
  let lo := 3
  let hi := maxN
  if hi ≥ lo then
    let counts := countsByCrossing knots lo hi
    IO.println "Counts by crossing number:"
    for (cr, c) in counts do
      let exp2 := expectedTwoBridgeCounts.find? (·.1 == cr)
      let expAll := expectedAllPrimeCounts.find? (·.1 == cr)
      let suffix2 :=
        match exp2 with
        | some (_, e) =>
            if e == c then "  [= 2-bridge table]"
            else s!"  [2-bridge table expects {e}]"
        | none => ""
      let suffixAll :=
        if check then
          match expAll with
          | some (_, e) =>
              if e == c then "  [= full prime census]"
              else s!"  [full prime census {e}; gap {e - c} non-rational]"
          | none => ""
        else ""
      IO.println s!"  {cr}: {c}{suffix2}{suffixAll}"
  if check then
    IO.println ""
    IO.println "Gaps vs Conway 1970 full census:"
    IO.println "  • Through 7 crossings: all prime knots are rational — counts should match."
    IO.println "  • From 8 crossings: basic polyhedra / non-rational algebraic knots omitted."
    IO.println "  • Flype reduction for non-rational diagrams: not implemented."
    IO.println "  • Meta-API / Muse checkin loop: not touched."

def usage : String :=
  "Usage: enumerate_knots <maxCrossing> [--check]\n\
   Example: lake exe enumerate_knots -- 7\n\
   Example: lake exe enumerate_knots -- 8 --check"

def main (args : List String) : IO UInt32 := do
  let args := args.filter (· ≠ "--")
  match args with
  | [] =>
      IO.eprintln usage
      return 2
  | maxS :: rest =>
      match parseNat maxS with
      | none =>
          IO.eprintln s!"Could not parse max crossing number: {maxS}"
          IO.eprintln usage
          return 2
      | some maxN =>
          if maxN = 0 then
            IO.eprintln "maxCrossing must be at least 1"
            return 2
          let check := rest.contains "--check" || rest.contains "-c"
          if maxN > 14 then
            IO.println s!"Note: maxCrossing={maxN} may be slow (exponential CF compositions)."
          IO.println s!"Conway rational-knot enumerator (2-bridge fragment)"
          IO.println s!"Maximum crossing number: {maxN}"
          IO.println "────────────────────────────────────────"
          let knots := enumerateRationalPrimes maxN
          for k in knots do
            if k.crossingNumber ≥ 3 then
              printKnot k
          printSummary knots maxN check
          return 0
