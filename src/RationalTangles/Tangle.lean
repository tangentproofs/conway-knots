/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Reidemeister

/-!
# 2-tangles and isotopy

A 2-tangle is a combinatorial diagram in the disc: the PD-code type
`TangleDiagram` of two arcs (and finitely many circles) with four fixed
endpoints NW, NE, SE, SW. Throughout, “tangle” means a tangle diagram, as in
Kauffman–Lambropoulou.

Two diagrams are isotopic when they differ by a finite sequence of
Reidemeister moves in the interior of the disc (including planar isotopy),
with the four endpoints held fixed.

The class of 2-tangles is closed under addition `T + S` (place `S` to the
right of `T`, joining NE–NW and SE–SW), multiplication `T * S` (place `S`
below `T`, joining SW–NW and SE–NE), mirror image `-T` (switch every
crossing), rotation `T.rotate` (counterclockwise by 90°), and inversion
`T.invert` (the paper's `Tⁱ := -Tʳ`: mirror of the counterclockwise 90°
rotation).
-/

namespace RationalTangles

/-- A 2-tangle diagram in the disc, with four endpoints in the standard
    NW/NE/SE/SW positions. This is the PD-code type `TangleDiagram`. -/
abbrev TwoTangle := TangleDiagram


namespace Crossing

/-- The largest arc identifier incident to `C`. -/
def maxArc (C : Crossing) : Nat :=
  max C.a0 (max C.a1 (max C.a2 C.a3))

/-- Switch over and under at a crossing (90° port rotation so that ports
    `0` and `2` remain the overstrand) and reverse the crossing type.
    This is the local picture of taking the mirror image. -/
def switch (C : Crossing) : Crossing :=
  { a0 := C.a1, a1 := C.a2, a2 := C.a3, a3 := C.a0, sign := C.sign.flip }

@[simp] theorem switch_switch (C : Crossing) : C.switch.switch = C.rotate180 := by
  rcases C with ⟨a0, a1, a2, a3, s⟩
  cases s <;> rfl

theorem switch_maxArc (C : Crossing) : C.switch.maxArc = C.maxArc := by
  simp [Crossing.switch, Crossing.maxArc]
  omega

theorem switch_rename (f : Nat → Nat) (C : Crossing) :
    (C.rename f).switch = C.switch.rename f := rfl

/-- The largest incident identifier is one of the four ports. -/
theorem maxArc_memArc (C : Crossing) : C.memArc C.maxArc := by
  unfold Crossing.maxArc Crossing.memArc
  omega

end Crossing

namespace TangleDiagram

/-- The largest arc identifier appearing in the diagram (crossings or
    boundary). Used to shift a second diagram off the first's names. -/
def maxArc (D : TangleDiagram) : Nat :=
  let b := max D.NW (max D.NE (max D.SE D.SW))
  D.crossings.foldl (fun m C => max m C.maxArc) b

/-- Arc `a` is a boundary port or is incident to some crossing. -/
def appears (T : TangleDiagram) (a : Nat) : Prop :=
  a = T.NW ∨ a = T.NE ∨ a = T.SE ∨ a = T.SW ∨
    ∃ C ∈ T.crossings, C.memArc a

/-- Mirror image `-T`: switch over and under at every crossing. Endpoints
    stay put. In particular `-[n] = [-n]`. -/
def mirror (T : TangleDiagram) : TangleDiagram :=
  { T with crossings := T.crossings.map Crossing.switch }

/-- Counterclockwise rotation of `T` by 90°. Crossing PD-data is local
    (ports are relative to the overstrand), so only the four endpoints
    cycle: NW ← NE ← SE ← SW ← NW. -/
def rotate (T : TangleDiagram) : TangleDiagram :=
  { T with NW := T.NE, NE := T.SE, SE := T.SW, SW := T.NW }

/-- Inversion `Tⁱ := -Tʳ`: rotate counterclockwise by 90°, then mirror.
    For integer tangles this produces the corresponding vertical tangle. -/
def invert (T : TangleDiagram) : TangleDiagram :=
  T.rotate.mirror

/-- Place `S` to the right of `T`, joining `T.NE` to `S.NW` and `T.SE` to
    `S.SW`. The sum of two 2-tangles is a 2-tangle; it is rational iff at
    least one summand is an integer tangle. -/
def add (T S : TangleDiagram) : TangleDiagram :=
  let S' := S.rename (· + (T.maxArc + 1))
  let f (a : Nat) : Nat :=
    if a = S'.NW then T.NE
    else if a = S'.SW then T.SE
    else a
  let S'' := S'.rename f
  { crossings := T.crossings ++ S''.crossings
    NW := T.NW
    NE := S''.NE
    SE := S''.SE
    SW := T.SW }

/-- Place `S` below `T`, joining `T.SW` to `S.NW` and `T.SE` to `S.NE`. -/
def mul (T S : TangleDiagram) : TangleDiagram :=
  let S' := S.rename (· + (T.maxArc + 1))
  let f (a : Nat) : Nat :=
    if a = S'.NW then T.SW
    else if a = S'.NE then T.SE
    else a
  let S'' := S'.rename f
  { crossings := T.crossings ++ S''.crossings
    NW := T.NW
    NE := T.NE
    SE := S''.SE
    SW := S''.SW }

end TangleDiagram

theorem foldl_maxArc_map_switch (cs : List Crossing) (b : Nat) :
    (cs.map Crossing.switch).foldl (fun m C => max m C.maxArc) b =
      cs.foldl (fun m C => max m C.maxArc) b := by
  induction cs generalizing b with
  | nil => rfl
  | cons C cs ih =>
    simp [List.foldl]
    rw [Crossing.switch_maxArc, ih]

theorem maxArc_mirror (T : TangleDiagram) : T.mirror.maxArc = T.maxArc := by
  simp [TangleDiagram.mirror, TangleDiagram.maxArc, foldl_maxArc_map_switch]

theorem mirror_add (T S : TangleDiagram) :
    (T.add S).mirror = T.mirror.add S.mirror := by
  unfold TangleDiagram.add
  rw [maxArc_mirror]
  simp [TangleDiagram.mirror, TangleDiagram.rename, List.map_append, List.map_map,
    Function.comp, Crossing.switch_rename]
  intro _ _; rfl

theorem mirror_mul (T S : TangleDiagram) :
    (T.mul S).mirror = T.mirror.mul S.mirror := by
  unfold TangleDiagram.mul
  rw [maxArc_mirror]
  simp [TangleDiagram.mirror, TangleDiagram.rename, List.map_append, List.map_map,
    Function.comp, Crossing.switch_rename]
  intro _ _; rfl

theorem mirror_invert (T : TangleDiagram) :
    T.invert.mirror = T.mirror.invert := by
  simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror]

/-- Inversion is also the counterclockwise rotate of the mirror. -/
theorem invert_eq_mirror_rotate (T : TangleDiagram) :
    T.invert = T.mirror.rotate :=
  rfl

@[simp] theorem mirror_zero : TangleDiagram.zero.mirror = TangleDiagram.zero := rfl
@[simp] theorem mirror_infinity : TangleDiagram.infinity.mirror = TangleDiagram.infinity := rfl

instance : Add TangleDiagram := ⟨TangleDiagram.add⟩
instance : Mul TangleDiagram := ⟨TangleDiagram.mul⟩
instance : Neg TangleDiagram := ⟨TangleDiagram.mirror⟩

/-- `[0]` on the right of `T` is a no-op: the two horizontal strands of `[0]`
    are glued onto `T.NE` and `T.SE`, which already occupy those boundary
    ports. -/
theorem add_zero_eq (T : TangleDiagram) : T.add TangleDiagram.zero = T := by
  unfold TangleDiagram.add
  simp [TangleDiagram.zero, TangleDiagram.rename]

/-- `[0]ʳ = [∞]`. -/
theorem rotate_zero :
    TangleDiagram.zero.rotate = TangleDiagram.infinity :=
  rfl

/-- `[0]ⁱ = [∞]`. -/
theorem invert_zero :
    TangleDiagram.zero.invert = TangleDiagram.infinity :=
  rfl

/-- `[∞]` below `T` is a no-op: the two vertical strands of `[∞]` are glued
    onto `T.SW` and `T.SE`, which already occupy those boundary ports.
    This is not `infinity.invert = zero` (those PD-codes differ by a rename). -/
theorem mul_infinity_eq (T : TangleDiagram) :
    T.mul TangleDiagram.infinity = T := by
  unfold TangleDiagram.mul
  simp [TangleDiagram.infinity, TangleDiagram.rename]

end RationalTangles
