/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Tangle

/-!
# Integer and vertical tangles

The elementary rational tangles are `[0]`, `[∞]`, `[+1]` and `[-1]`. Integer
tangles `[n]` are `n` horizontal twists; vertical tangles `[n]⁻¹` are `n`
vertical twists. Crossing type follows Kauffman–Lambropoulou Figure 2
(Ernst–Sumners convention): positive as in `[+1]`, negative as in `[-1]`.

Combinatorially `[+1]` is a single positive crossing whose overstrand runs
NW–SE, which is the local picture whose coloring fraction is `1`. The
mirror `[-1]` switches that crossing. The integer tangle `[n]` is the
`n`-fold horizontal sum of `[±1]` with `[0]`, and the vertical tangle is
the inversion of `[n]`.
-/

namespace RationalTangles

/-- The positive crossing `[+1]`. Ports `0` and `2` (overstrand) occupy NW
    and SE; the two under-arcs occupy NE and SW. -/
def one : TangleDiagram where
  crossings := [{ a0 := 0, a1 := 1, a2 := 2, a3 := 3, sign := .pos }]
  NW := 0
  NE := 1
  SE := 2
  SW := 3

/-- The negative crossing `[-1]`, the mirror of `[+1]`. -/
def negOne : TangleDiagram :=
  one.mirror

/-- `[±1]` as a function of crossing sign. -/
def crossingTangle : CrossingSign → TangleDiagram
  | .pos => one
  | .neg => negOne

/-- The integer tangle `[n]`: `|n|` horizontal twists of the sign of `n`. -/
def integerTangle (n : Int) : TangleDiagram :=
  let unit := if 0 ≤ n then one else negOne
  (List.replicate n.natAbs unit).foldl TangleDiagram.add TangleDiagram.zero

/-- The vertical tangle `[n]⁻¹`, obtained as the inversion of `[n]`. -/
def verticalTangle (n : Int) : TangleDiagram :=
  (integerTangle n).invert

/-- `|n|` vertical twists of the sign of `n`, stacked below `[∞]`. This is
    the right-and-bottom picture of Conway `[n]ⁱ = 1/[n]`. It is not the
    PD-code `(integerTangle n).invert`, which mirrors every crossing. -/
def verticalTwists (n : Int) : TangleDiagram :=
  let unit := if 0 ≤ n then one else negOne
  (List.replicate n.natAbs unit).foldl TangleDiagram.mul TangleDiagram.infinity

@[simp] theorem integerTangle_zero : integerTangle 0 = TangleDiagram.zero :=
  rfl

@[simp] theorem integerTangle_one : integerTangle 1 = TangleDiagram.zero + one :=
  rfl

@[simp] theorem integerTangle_negOne :
    integerTangle (-1) = TangleDiagram.zero + negOne :=
  rfl

@[simp] theorem verticalTwists_zero :
    verticalTwists 0 = TangleDiagram.infinity :=
  rfl

@[simp] theorem verticalTwists_one :
    verticalTwists 1 = TangleDiagram.infinity * one :=
  rfl

@[simp] theorem verticalTwists_negOne :
    verticalTwists (-1) = TangleDiagram.infinity * negOne :=
  rfl

@[simp] theorem negOne_eq_mirror_one : negOne = -one :=
  rfl

/-- `+1` or `-1` as an integer. -/
def CrossingSign.toInt : CrossingSign → Int
  | .pos => 1
  | .neg => -1

@[simp] theorem CrossingSign.toInt_pos : CrossingSign.pos.toInt = 1 := rfl
@[simp] theorem CrossingSign.toInt_neg : CrossingSign.neg.toInt = -1 := rfl

end RationalTangles
