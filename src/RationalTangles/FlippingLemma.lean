/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import RationalTangles.StandardForm

/-!
# Flipping lemma and existence of standard form

Kauffman–Lambropoulou Lemma 2 and Lemma 3.
-/

namespace RationalTangles

open Function

@[simp] theorem add_eq_add (T S : TangleDiagram) : T + S = T.add S := rfl
@[simp] theorem mul_eq_mul (T S : TangleDiagram) : T * S = T.mul S := rfl


/-! ## Arc permutations used as planar isotopies -/

def swap01 (n : Nat) : Nat :=
  if n = 0 then 1 else if n = 1 then 0 else n

theorem swap01_injective : Injective swap01 := by
  intro a b h
  unfold swap01 at h
  split_ifs at h <;> omega

def rev03 (n : Nat) : Nat :=
  if n < 4 then 3 - n else n

theorem rev03_injective : Injective rev03 := by
  intro a b h
  unfold rev03 at h
  split_ifs at h with ha hb hb
  · omega
  · have : 3 - a ≥ 4 := by omega
    omega
  · have : 3 - b ≥ 4 := by omega
    omega
  · exact h

def swap01_23 (n : Nat) : Nat :=
  if n = 0 then 1
  else if n = 1 then 0
  else if n = 2 then 3
  else if n = 3 then 2
  else n

theorem swap01_23_injective : Injective swap01_23 := by
  intro a b h
  unfold swap01_23 at h
  split_ifs at h <;> omega

def oneToZeroAdd (n : Nat) : Nat :=
  if n = 1 then 3 else if n = 2 then 4 else if n = 3 then 1 else if n = 4 then 2 else n

theorem oneToZeroAdd_injective : Injective oneToZeroAdd := by
  intro a b h
  unfold oneToZeroAdd at h
  split_ifs at h <;> omega

/-! ## Planar isotopy helpers -/

theorem pairRel_nil {α} {R : α → α → Prop} : pairRel R [] [] :=
  trivial

theorem planar_zero_hflip :
    PlanarIsotopy TangleDiagram.zero TangleDiagram.zero.hflip := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem planar_infinity_vflip :
    PlanarIsotopy TangleDiagram.infinity TangleDiagram.infinity.vflip := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem planar_one_hflip : PlanarIsotopy one.hflip one := by
  refine ⟨rev03, rev03_injective, ?_, ?_, ?_, ?_, one.crossings, ?_, List.Perm.rfl⟩
  · simp [one, TangleDiagram.hflip, TangleDiagram.mirror, rev03]
  · simp [one, TangleDiagram.hflip, TangleDiagram.mirror, rev03]
  · simp [one, TangleDiagram.hflip, TangleDiagram.mirror, rev03]
  · simp [one, TangleDiagram.hflip, TangleDiagram.mirror, rev03]
  · refine ⟨?_, trivial⟩
    simp [one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.rename, Crossing.switch,
      CrossingSign.flip, rev03, Crossing.reverseUnders, Crossing.rotate180,
      Crossing.sameUpToRotation]

theorem planar_one_vflip : PlanarIsotopy one.vflip one := by
  refine ⟨swap01_23, swap01_23_injective, ?_, ?_, ?_, ?_, one.crossings, ?_, List.Perm.rfl⟩
  · simp [one, TangleDiagram.vflip, TangleDiagram.mirror, swap01_23]
  · simp [one, TangleDiagram.vflip, TangleDiagram.mirror, swap01_23]
  · simp [one, TangleDiagram.vflip, TangleDiagram.mirror, swap01_23]
  · simp [one, TangleDiagram.vflip, TangleDiagram.mirror, swap01_23]
  · refine ⟨?_, trivial⟩
    simp [one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.rename, Crossing.switch,
      CrossingSign.flip, swap01_23, Crossing.reverseUnders, Crossing.rotate180,
      Crossing.sameUpToRotation]

theorem planar_negOne_hflip : PlanarIsotopy negOne.hflip negOne := by
  refine ⟨rev03, rev03_injective, ?_, ?_, ?_, ?_, negOne.crossings, ?_, List.Perm.rfl⟩
  · simp [negOne, one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.switch, rev03]
  · simp [negOne, one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.switch, rev03]
  · simp [negOne, one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.switch, rev03]
  · simp [negOne, one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.switch, rev03]
  · refine ⟨?_, trivial⟩
    simp [negOne, one, TangleDiagram.hflip, TangleDiagram.mirror, Crossing.rename,
      Crossing.switch, CrossingSign.flip, rev03, Crossing.reverseUnders, Crossing.rotate180,
      Crossing.sameUpToRotation]

theorem planar_negOne_vflip : PlanarIsotopy negOne.vflip negOne := by
  refine ⟨swap01_23, swap01_23_injective, ?_, ?_, ?_, ?_, negOne.crossings, ?_, List.Perm.rfl⟩
  · simp [negOne, one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.switch, swap01_23]
  · simp [negOne, one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.switch, swap01_23]
  · simp [negOne, one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.switch, swap01_23]
  · simp [negOne, one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.switch, swap01_23]
  · refine ⟨?_, trivial⟩
    simp [negOne, one, TangleDiagram.vflip, TangleDiagram.mirror, Crossing.rename,
      Crossing.switch, CrossingSign.flip, swap01_23, Crossing.reverseUnders,
      Crossing.rotate180, Crossing.sameUpToRotation]

theorem planar_one_zero_add : PlanarIsotopy one (TangleDiagram.zero.add one) := by
  refine ⟨oneToZeroAdd, oneToZeroAdd_injective, ?_, ?_, ?_, ?_,
    (TangleDiagram.zero.add one).crossings, ?_, List.Perm.rfl⟩
  · simp [one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc]
  · simp [one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc, Crossing.rename]
  · simp [one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc, Crossing.rename]
  · simp [one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc, Crossing.rename]
  · refine ⟨Or.inl ?_, trivial⟩
    simp [one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc, Crossing.rename]

theorem rename_id (C : Crossing) : C.rename id = C := rfl

theorem rotate180_same (C : Crossing) : C.rotate180.sameUpToRotation C :=
  Or.inr (Or.inl rfl)

theorem pairRel_rotate180 (cs : List Crossing) :
    pairRel Crossing.sameUpToRotation (cs.map Crossing.rotate180) cs := by
  induction cs with
  | nil => trivial
  | cons C cs ih =>
    exact ⟨rotate180_same C, ih⟩

theorem pairRel_same_rotate180 (cs : List Crossing) :
    pairRel Crossing.sameUpToRotation cs (cs.map Crossing.rotate180) := by
  induction cs with
  | nil => trivial
  | cons C cs ih =>
    exact ⟨Crossing.sameUpToRotation_rotate180 C, ih⟩

theorem planar_hflip_hflip (T : TangleDiagram) :
    PlanarIsotopy T.hflip.hflip T := by
  have hmap :
      T.hflip.hflip.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.hflip, TangleDiagram.mirror, List.map_map, Function.comp,
      Crossing.switch_switch]
  refine ⟨id, injective_id, ?_, ?_, ?_, ?_, T.crossings, ?_, List.Perm.rfl⟩
  · simp [TangleDiagram.hflip, TangleDiagram.mirror]
  · simp [TangleDiagram.hflip, TangleDiagram.mirror]
  · simp [TangleDiagram.hflip, TangleDiagram.mirror]
  · simp [TangleDiagram.hflip, TangleDiagram.mirror]
  · have : T.hflip.hflip.crossings.map (Crossing.rename id) =
        T.crossings.map Crossing.rotate180 := by
      simp [hmap, rename_id]
    simpa [this] using pairRel_rotate180 T.crossings

theorem planar_vflip_vflip (T : TangleDiagram) :
    PlanarIsotopy T.vflip.vflip T := by
  have hmap :
      T.vflip.vflip.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.vflip, TangleDiagram.mirror, List.map_map, Function.comp,
      Crossing.switch_switch]
  refine ⟨id, injective_id, ?_, ?_, ?_, ?_, T.crossings, ?_, List.Perm.rfl⟩
  · simp [TangleDiagram.vflip, TangleDiagram.mirror]
  · simp [TangleDiagram.vflip, TangleDiagram.mirror]
  · simp [TangleDiagram.vflip, TangleDiagram.mirror]
  · simp [TangleDiagram.vflip, TangleDiagram.mirror]
  · have : T.vflip.vflip.crossings.map (Crossing.rename id) =
        T.crossings.map Crossing.rotate180 := by
      simp [hmap, rename_id]
    simpa [this] using pairRel_rotate180 T.crossings

theorem invert_invert_eq_hflip_vflip (T : TangleDiagram) :
    T.invert.invert = T.hflip.vflip := by
  cases T
  simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
    TangleDiagram.hflip, TangleDiagram.vflip, List.map_map, Function.comp,
    Crossing.switch_switch]

theorem planar_rotate_rotate_invert_invert (T : TangleDiagram) :
    PlanarIsotopy T.rotate.rotate T.invert.invert := by
  have hmap :
      T.invert.invert.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
      List.map_map, Function.comp, Crossing.switch_switch]
  refine ⟨id, injective_id, ?_, ?_, ?_, ?_, T.invert.invert.crossings, ?_, List.Perm.rfl⟩
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror]
  · simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror]
  · have hren : Crossing.rename id = id := funext rename_id
    have : T.rotate.rotate.crossings.map (Crossing.rename id) = T.crossings := by
      simp [TangleDiagram.rotate, hren]
    simpa [this, hmap] using pairRel_same_rotate180 T.crossings

/-! ## Elementary flips -/

theorem isotopic_zero_hflip :
    Isotopic TangleDiagram.zero TangleDiagram.zero.hflip :=
  isotopic_planar planar_zero_hflip

theorem isotopic_zero_vflip :
    Isotopic TangleDiagram.zero TangleDiagram.zero.vflip := by
  have : TangleDiagram.zero.vflip = TangleDiagram.zero := rfl
  rw [this]
  exact .refl _

theorem isotopic_infinity_hflip :
    Isotopic TangleDiagram.infinity TangleDiagram.infinity.hflip := by
  have : TangleDiagram.infinity.hflip = TangleDiagram.infinity := rfl
  rw [this]
  exact .refl _

theorem isotopic_infinity_vflip :
    Isotopic TangleDiagram.infinity TangleDiagram.infinity.vflip :=
  isotopic_planar planar_infinity_vflip

theorem isotopic_one_hflip : Isotopic one one.hflip :=
  .symm (isotopic_planar planar_one_hflip)

theorem isotopic_one_vflip : Isotopic one one.vflip :=
  .symm (isotopic_planar planar_one_vflip)

theorem isotopic_negOne_hflip : Isotopic negOne negOne.hflip :=
  .symm (isotopic_planar planar_negOne_hflip)

theorem isotopic_negOne_vflip : Isotopic negOne negOne.vflip :=
  .symm (isotopic_planar planar_negOne_vflip)

theorem isotopic_crossingTangle_hflip (s : CrossingSign) :
    Isotopic (crossingTangle s) (crossingTangle s).hflip := by
  cases s <;> simp [crossingTangle]
  · exact isotopic_one_hflip
  · exact isotopic_negOne_hflip

theorem isotopic_crossingTangle_vflip (s : CrossingSign) :
    Isotopic (crossingTangle s) (crossingTangle s).vflip := by
  cases s <;> simp [crossingTangle]
  · exact isotopic_one_vflip
  · exact isotopic_negOne_vflip

theorem isotopic_hflip_involutive (T : TangleDiagram) :
    Isotopic T.hflip.hflip T :=
  isotopic_planar (planar_hflip_hflip T)

theorem isotopic_vflip_involutive (T : TangleDiagram) :
    Isotopic T.vflip.vflip T :=
  isotopic_planar (planar_vflip_vflip T)

theorem planar_hflip_rot180_vflip (T : TangleDiagram) :
    PlanarIsotopy T.hflip.rot180 T.vflip := by
  refine ⟨id, injective_id, rfl, rfl, rfl, rfl, T.vflip.crossings, ?_, List.Perm.rfl⟩
  have hmap :
      T.hflip.rot180.crossings.map (Crossing.rename id) =
        T.vflip.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.hflip, TangleDiagram.vflip, TangleDiagram.rot180,
      TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch,
      rename_id]
  simpa [hmap] using pairRel_rotate180 T.vflip.crossings

theorem planar_vflip_rot180_hflip (T : TangleDiagram) :
    PlanarIsotopy T.vflip.rot180 T.hflip := by
  refine ⟨id, injective_id, rfl, rfl, rfl, rfl, T.hflip.crossings, ?_, List.Perm.rfl⟩
  have hmap :
      T.vflip.rot180.crossings.map (Crossing.rename id) =
        T.hflip.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.hflip, TangleDiagram.vflip, TangleDiagram.rot180,
      TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch,
      rename_id]
  simpa [hmap] using pairRel_rotate180 T.hflip.crossings

theorem invert_invert_eq_rot180 (T : TangleDiagram) :
    T.invert.invert = T.rot180 := by
  rw [invert_invert_eq_hflip_vflip, rot180_eq_hflip_vflip]

def cycle02_13 (n : Nat) : Nat :=
  if n = 0 then 2 else if n = 2 then 0 else if n = 1 then 3 else if n = 3 then 1 else n

theorem cycle02_13_injective : Injective cycle02_13 := by
  intro a b h
  unfold cycle02_13 at h
  split_ifs at h <;> omega

theorem planar_zero_rot180 :
    PlanarIsotopy TangleDiagram.zero.rot180 TangleDiagram.zero := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem planar_infinity_rot180 :
    PlanarIsotopy TangleDiagram.infinity.rot180 TangleDiagram.infinity := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem planar_one_rot180 : PlanarIsotopy one.rot180 one := by
  refine ⟨cycle02_13, cycle02_13_injective, ?_, ?_, ?_, ?_, one.crossings, ?_, List.Perm.rfl⟩
  · simp [one, TangleDiagram.rot180, cycle02_13]
  · simp [one, TangleDiagram.rot180, cycle02_13]
  · simp [one, TangleDiagram.rot180, cycle02_13]
  · simp [one, TangleDiagram.rot180, cycle02_13]
  · refine ⟨?_, trivial⟩
    simp [one, TangleDiagram.rot180, Crossing.rename, Crossing.rotate180, cycle02_13,
      Crossing.sameUpToRotation]

theorem planar_negOne_rot180 : PlanarIsotopy negOne.rot180 negOne := by
  refine ⟨cycle02_13, cycle02_13_injective, ?_, ?_, ?_, ?_, negOne.crossings, ?_, List.Perm.rfl⟩
  · simp [negOne, one, TangleDiagram.rot180, TangleDiagram.mirror, Crossing.switch, cycle02_13]
  · simp [negOne, one, TangleDiagram.rot180, TangleDiagram.mirror, Crossing.switch, cycle02_13]
  · simp [negOne, one, TangleDiagram.rot180, TangleDiagram.mirror, Crossing.switch, cycle02_13]
  · simp [negOne, one, TangleDiagram.rot180, TangleDiagram.mirror, Crossing.switch, cycle02_13]
  · refine ⟨?_, trivial⟩
    simp [negOne, one, TangleDiagram.rot180, TangleDiagram.mirror, Crossing.rename,
      Crossing.switch, Crossing.rotate180, cycle02_13, Crossing.sameUpToRotation]

theorem isotopic_zero_rot180 :
    Isotopic TangleDiagram.zero.rot180 TangleDiagram.zero :=
  isotopic_planar planar_zero_rot180

theorem isotopic_infinity_rot180 :
    Isotopic TangleDiagram.infinity.rot180 TangleDiagram.infinity :=
  isotopic_planar planar_infinity_rot180

theorem isotopic_one_rot180 : Isotopic one.rot180 one :=
  isotopic_planar planar_one_rot180

theorem isotopic_negOne_rot180 : Isotopic negOne.rot180 negOne :=
  isotopic_planar planar_negOne_rot180

theorem isotopic_crossingTangle_rot180 (s : CrossingSign) :
    Isotopic (crossingTangle s).rot180 (crossingTangle s) := by
  cases s <;> simp [crossingTangle]
  · exact isotopic_one_rot180
  · exact isotopic_negOne_rot180

/-! ## Lemma 2 on twist-form expressions -/

/-- Sign-preserving Figure 5 slide: `[±1]+t ∼ t.rot180+[±1]`.
    Not the switched algebraic `Flype` (`t.hflip`). -/
theorem flype_add (s : CrossingSign) (t : TangleDiagram) :
    Isotopic (crossingTangle s + t) (t.rot180 + crossingTangle s) :=
  .flype_slide_add s t

/-- Sign-preserving Figure 5 slide: `[±1]*t ∼ t.rot180*[±1]`. -/
theorem flype_mul (s : CrossingSign) (t : TangleDiagram) :
    Isotopic (crossingTangle s * t) (t.rot180 * crossingTangle s) :=
  .flype_slide_mul s t

/-- Sign-preserving planar 180° of a twist-form diagram. -/
theorem TwistExpr.isotopic_rot180 (e : TwistExpr) :
    Isotopic e.diagram.rot180 e.diagram := by
  induction e with
  | zero => simpa [TwistExpr.diagram] using isotopic_zero_rot180
  | infinity => simpa [TwistExpr.diagram] using isotopic_infinity_rot180
  | one => simpa [TwistExpr.diagram] using isotopic_one_rot180
  | negOne => simpa [TwistExpr.diagram] using isotopic_negOne_rot180
  | addRight e s ih =>
    simp only [TwistExpr.diagram, add_eq_add]
    have hswap : Isotopic (e.diagram.add (crossingTangle s)).rot180
        ((crossingTangle s).rot180.add e.diagram.rot180) :=
      .rot180_add e.diagram (crossingTangle s)
    have hunit : Isotopic (crossingTangle s).rot180 (crossingTangle s) :=
      isotopic_crossingTangle_rot180 s
    have hleft : Isotopic ((crossingTangle s).rot180.add e.diagram.rot180)
        ((crossingTangle s).add e.diagram) :=
      .trans (.add_left hunit) (.add_right ih)
    have hcomm : Isotopic ((crossingTangle s).add e.diagram)
        (e.diagram.add (crossingTangle s)) :=
      .trans (flype_add s e.diagram) (.add_left ih)
    exact .trans hswap (.trans hleft hcomm)
  | addLeft e s ih =>
    simp only [TwistExpr.diagram, add_eq_add]
    have hswap : Isotopic ((crossingTangle s).add e.diagram).rot180
        (e.diagram.rot180.add (crossingTangle s).rot180) :=
      .rot180_add (crossingTangle s) e.diagram
    have hunit : Isotopic (crossingTangle s).rot180 (crossingTangle s) :=
      isotopic_crossingTangle_rot180 s
    have hto : Isotopic (e.diagram.rot180.add (crossingTangle s).rot180)
        (e.diagram.add (crossingTangle s)) :=
      .trans (.add_left ih) (.add_right hunit)
    have hcomm : Isotopic (e.diagram.add (crossingTangle s))
        ((crossingTangle s).add e.diagram) :=
      .trans (.add_left ih.symm) (.symm (flype_add s e.diagram))
    exact .trans hswap (.trans hto hcomm)
  | mulBottom e s ih =>
    simp only [TwistExpr.diagram, mul_eq_mul]
    have hswap : Isotopic (e.diagram.mul (crossingTangle s)).rot180
        ((crossingTangle s).rot180.mul e.diagram.rot180) :=
      .rot180_mul e.diagram (crossingTangle s)
    have hunit : Isotopic (crossingTangle s).rot180 (crossingTangle s) :=
      isotopic_crossingTangle_rot180 s
    have hleft : Isotopic ((crossingTangle s).rot180.mul e.diagram.rot180)
        ((crossingTangle s).mul e.diagram) :=
      .trans (.mul_left hunit) (.mul_right ih)
    have hcomm : Isotopic ((crossingTangle s).mul e.diagram)
        (e.diagram.mul (crossingTangle s)) :=
      .trans (flype_mul s e.diagram) (.mul_left ih)
    exact .trans hswap (.trans hleft hcomm)
  | mulTop e s ih =>
    simp only [TwistExpr.diagram, mul_eq_mul]
    have hswap : Isotopic ((crossingTangle s).mul e.diagram).rot180
        (e.diagram.rot180.mul (crossingTangle s).rot180) :=
      .rot180_mul (crossingTangle s) e.diagram
    have hunit : Isotopic (crossingTangle s).rot180 (crossingTangle s) :=
      isotopic_crossingTangle_rot180 s
    have hto : Isotopic (e.diagram.rot180.mul (crossingTangle s).rot180)
        (e.diagram.mul (crossingTangle s)) :=
      .trans (.mul_left ih) (.mul_right hunit)
    have hcomm : Isotopic (e.diagram.mul (crossingTangle s))
        ((crossingTangle s).mul e.diagram) :=
      .trans (.mul_left ih.symm) (.symm (flype_mul s e.diagram))
    exact .trans hswap (.trans hto hcomm)

/-- A rational tangle is isotopic to its planar 180° rotate. -/
theorem isotopic_rot180 {T : TangleDiagram} (h : IsRational T) :
    Isotopic T.rot180 T := by
  obtain ⟨e, he⟩ := h
  exact .trans (.rot180_cong he) (.trans e.isotopic_rot180 he.symm)

/-- Lemma 2 (iii): a rational tangle is isotopic to the double inversion
    `(Tⁱ)ⁱ = (Tʳ)ʳ`. Horizontal/vertical flips are spatial (`Crossing.switch`)
    and are not claimed as `Isotopic` generators; the coloring-honest
    content is `T.rot180 ∼ T`. -/
theorem flipping_lemma (T : TangleDiagram) (h : IsRational T) :
    Isotopic T.rot180 T ∧
      Isotopic T T.invert.invert ∧
      Isotopic T.invert.invert T.rotate.rotate := by
  refine ⟨isotopic_rot180 h, ?_, ?_⟩
  · rw [invert_invert_eq_rot180]
    exact (isotopic_rot180 h).symm
  · exact .symm (isotopic_planar (planar_rotate_rotate_invert_invert T))

/-! ## Lemma 3: standard form -/

def TwistExpr.toStandard : TwistExpr → StandardExpr
  | zero => .zero
  | infinity => .infinity
  | one => .addRight .zero .pos
  | negOne => .addRight .zero .neg
  | addRight e s => .addRight e.toStandard s
  | addLeft e s => .addRight e.toStandard s
  | mulBottom e s => .mulBottom e.toStandard s
  | mulTop e s => .mulBottom e.toStandard s

theorem isotopic_one_addRight_zero :
    Isotopic one (StandardExpr.addRight .zero .pos).diagram := by
  simpa [StandardExpr.diagram, crossingTangle, add_eq_add] using
    isotopic_planar planar_one_zero_add

theorem planar_negOne_zero_add : PlanarIsotopy negOne (TangleDiagram.zero.add negOne) := by
  refine ⟨oneToZeroAdd, oneToZeroAdd_injective, ?_, ?_, ?_, ?_,
    (TangleDiagram.zero.add negOne).crossings, ?_, List.Perm.rfl⟩
  · simp [negOne, one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero,
      TangleDiagram.mirror, Crossing.switch, oneToZeroAdd, TangleDiagram.maxArc,
      Crossing.maxArc]
  · simp [negOne, one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero,
      TangleDiagram.mirror, Crossing.switch, oneToZeroAdd, TangleDiagram.maxArc,
      Crossing.maxArc, Crossing.rename]
  · simp [negOne, one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero,
      TangleDiagram.mirror, Crossing.switch, oneToZeroAdd, TangleDiagram.maxArc,
      Crossing.maxArc, Crossing.rename]
  · simp [negOne, one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero,
      TangleDiagram.mirror, Crossing.switch, oneToZeroAdd, TangleDiagram.maxArc,
      Crossing.maxArc, Crossing.rename]
  · refine ⟨Or.inl ?_, trivial⟩
    simp [negOne, one, TangleDiagram.add, TangleDiagram.rename, TangleDiagram.zero,
      TangleDiagram.mirror, Crossing.switch, Crossing.rename, oneToZeroAdd,
      TangleDiagram.maxArc, Crossing.maxArc]

theorem TwistExpr.toStandard_isotopic (e : TwistExpr) :
    Isotopic e.diagram e.toStandard.diagram := by
  induction e with
  | zero => exact .refl _
  | infinity => exact .refl _
  | one => exact isotopic_one_addRight_zero
  | negOne =>
    change Isotopic RationalTangles.negOne _
    simpa [TwistExpr.toStandard, StandardExpr.diagram, crossingTangle, add_eq_add] using
      isotopic_planar planar_negOne_zero_add
  | addRight e s ih =>
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, add_eq_add] using
      Isotopic.add_left ih
  | mulBottom e s ih =>
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, mul_eq_mul] using
      Isotopic.mul_left ih
  | addLeft e s ih =>
    have hflyp : Isotopic (crossingTangle s + e.diagram)
        (e.diagram + crossingTangle s) :=
      .trans (flype_add s e.diagram)
        (.add_left e.isotopic_rot180)
    refine .trans hflyp ?_
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, add_eq_add] using
      Isotopic.add_left ih
  | mulTop e s ih =>
    have hflyp : Isotopic (crossingTangle s * e.diagram)
        (e.diagram * crossingTangle s) :=
      .trans (flype_mul s e.diagram)
        (.mul_left e.isotopic_rot180)
    refine .trans hflyp ?_
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, mul_eq_mul] using
      Isotopic.mul_left ih

/-- Lemma 3: every rational tangle can be brought via isotopy to standard form. -/
theorem standard_form_exists (T : TangleDiagram) (h : IsRational T) :
    ∃ e : StandardExpr, Isotopic T e.diagram := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.toStandard, .trans he e.toStandard_isotopic⟩

end RationalTangles
