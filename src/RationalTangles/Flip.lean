/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import RationalTangles.Tangle

/-!
# Flips

A flip is a 180° rotation in space of a 2-tangle (Kauffman–Lambropoulou
Definition 3). The horizontal flip rotates around a horizontal axis in the
plane of the diagram (top and bottom endpoints swap; crossings are
mirrored). The vertical flip rotates around a vertical axis (left and right
endpoints swap; crossings are mirrored).

In general a flip switches endpoints and need not be an isotopy of
2-tangles. For rational tangles it is, by the flipping lemma.
-/

namespace RationalTangles

namespace TangleDiagram

/-- Horizontal flip `T^{hflip}`: 180° rotation around a horizontal axis in
    the plane of `T`. Top and bottom endpoints swap, and every crossing is
    switched. -/
def hflip (T : TangleDiagram) : TangleDiagram :=
  let T' := T.mirror
  { T' with NW := T'.SW, NE := T'.SE, SE := T'.NE, SW := T'.NW }

/-- Vertical flip `T^{vflip}`: 180° rotation around a vertical axis in the
    plane of `T`. Left and right endpoints swap, and every crossing is
    switched. -/
def vflip (T : TangleDiagram) : TangleDiagram :=
  let T' := T.mirror
  { T' with NW := T'.NE, NE := T'.NW, SE := T'.SW, SW := T'.SE }

/-- Planar 180° rotation of the diagram: each crossing is rotated in the
    plane (signs preserved) and the endpoints cycle `NW↔SE`, `NE↔SW`.
    This is `hflip.vflip` (two spatial flips restore crossing signs). -/
def rot180 (T : TangleDiagram) : TangleDiagram where
  crossings := T.crossings.map Crossing.rotate180
  NW := T.SE
  NE := T.SW
  SE := T.NW
  SW := T.NE

end TangleDiagram

theorem max_four_comm (w x y z : Nat) :
    max w (max x (max y z)) = max z (max y (max x w)) := by
  omega

theorem maxArc_hflip (T : TangleDiagram) : T.hflip.maxArc = T.maxArc := by
  unfold TangleDiagram.hflip TangleDiagram.mirror TangleDiagram.maxArc
  simp [foldl_maxArc_map_switch]
  rw [max_four_comm]

theorem maxArc_vflip (T : TangleDiagram) : T.vflip.maxArc = T.maxArc := by
  unfold TangleDiagram.vflip TangleDiagram.mirror TangleDiagram.maxArc
  simp [foldl_maxArc_map_switch]
  ac_rfl

theorem rot180_eq_hflip_vflip (T : TangleDiagram) : T.rot180 = T.hflip.vflip := by
  cases T
  simp [TangleDiagram.rot180, TangleDiagram.hflip, TangleDiagram.vflip,
    TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch]

theorem rot180_eq_vflip_hflip (T : TangleDiagram) : T.rot180 = T.vflip.hflip := by
  cases T
  simp [TangleDiagram.rot180, TangleDiagram.hflip, TangleDiagram.vflip,
    TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch]

theorem TangleDiagram.rot180_NW (T : TangleDiagram) : T.rot180.NW = T.SE := rfl
theorem TangleDiagram.rot180_NE (T : TangleDiagram) : T.rot180.NE = T.SW := rfl
theorem TangleDiagram.rot180_SE (T : TangleDiagram) : T.rot180.SE = T.NW := rfl
theorem TangleDiagram.rot180_SW (T : TangleDiagram) : T.rot180.SW = T.NE := rfl

theorem TangleDiagram.vflip_NW (T : TangleDiagram) : T.vflip.NW = T.NE := rfl
theorem TangleDiagram.vflip_NE (T : TangleDiagram) : T.vflip.NE = T.NW := rfl
theorem TangleDiagram.vflip_SE (T : TangleDiagram) : T.vflip.SE = T.SW := rfl
theorem TangleDiagram.vflip_SW (T : TangleDiagram) : T.vflip.SW = T.SE := rfl

/-- The two `add` glue maps that appear in `hflip_add_eq` agree when `S`
    has distinct left ports. -/
theorem hflip_add_glue_eq (T S : TangleDiagram) (h : S.NW ≠ S.SW) (s a : Nat) :
    (if a = S.NW then T.NE else if a = S.SW then T.SE else a + s) =
      (if a = S.SW then T.SE else if a = S.NW then T.NE else a + s) := by
  by_cases hNW : a = S.NW
  · by_cases hSW : a = S.SW
    · exact (h (hNW.symm.trans hSW)).elim
    · have hL : (if a = S.NW then T.NE else if a = S.SW then T.SE else a + s) = T.NE := by
        rw [if_pos hNW]
      have hR : (if a = S.SW then T.SE else if a = S.NW then T.NE else a + s) = T.NE := by
        rw [if_neg hSW, if_pos hNW]
      exact hL.trans hR.symm
  · by_cases hSW : a = S.SW
    · have hL : (if a = S.NW then T.NE else if a = S.SW then T.SE else a + s) = T.SE := by
        rw [if_neg hNW, if_pos hSW]
      have hR : (if a = S.SW then T.SE else if a = S.NW then T.NE else a + s) = T.SE := by
        rw [if_pos hSW]
      exact hL.trans hR.symm
    · have hL : (if a = S.NW then T.NE else if a = S.SW then T.SE else a + s) = a + s := by
        rw [if_neg hNW, if_neg hSW]
      have hR : (if a = S.SW then T.SE else if a = S.NW then T.NE else a + s) = a + s := by
        rw [if_neg hSW, if_neg hNW]
      exact hL.trans hR.symm

theorem eq_of_tangle (A B : TangleDiagram)
    (hcs : A.crossings = B.crossings) (hNW : A.NW = B.NW)
    (hNE : A.NE = B.NE) (hSE : A.SE = B.SE) (hSW : A.SW = B.SW) : A = B := by
  cases A; cases B; simp_all

theorem TangleDiagram.hflip_NW (T : TangleDiagram) : T.hflip.NW = T.SW := rfl
theorem TangleDiagram.hflip_NE (T : TangleDiagram) : T.hflip.NE = T.SE := rfl
theorem TangleDiagram.hflip_SE (T : TangleDiagram) : T.hflip.SE = T.NE := rfl
theorem TangleDiagram.hflip_SW (T : TangleDiagram) : T.hflip.SW = T.NW := rfl

theorem add_rename_fun (T S : TangleDiagram) :
    (T.add S).crossings =
      T.crossings ++
        S.crossings.map (Crossing.rename fun a =>
          if a + (T.maxArc + 1) = S.NW + (T.maxArc + 1) then T.NE
          else if a + (T.maxArc + 1) = S.SW + (T.maxArc + 1) then T.SE
          else a + (T.maxArc + 1)) := by
  unfold TangleDiagram.add
  simp [TangleDiagram.rename, List.map_map, Function.comp, Crossing.rename]

theorem add_NE_rename (T S : TangleDiagram) :
    (T.add S).NE =
      if S.NE = S.NW then T.NE
      else if S.NE = S.SW then T.SE
      else S.NE + (T.maxArc + 1) := by
  simp [TangleDiagram.add, TangleDiagram.rename]

theorem add_SE_rename (T S : TangleDiagram) :
    (T.add S).SE =
      if S.SE = S.NW then T.NE
      else if S.SE = S.SW then T.SE
      else S.SE + (T.maxArc + 1) := by
  simp [TangleDiagram.add, TangleDiagram.rename]

end RationalTangles
