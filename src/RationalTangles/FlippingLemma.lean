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

theorem isotopic_rot180_of_flips {T : TangleDiagram}
    (hh : Isotopic T T.hflip) (hv : Isotopic T T.vflip) :
    Isotopic T.rot180 T := by
  rw [rot180_eq_hflip_vflip]
  exact .trans (.vflip_cong hh.symm) hv.symm

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

theorem TwistExpr.isotopic_flips (e : TwistExpr) :
    Isotopic e.diagram e.diagram.hflip ∧ Isotopic e.diagram e.diagram.vflip := by
  induction e with
  | zero => exact ⟨isotopic_zero_hflip, isotopic_zero_vflip⟩
  | infinity => exact ⟨isotopic_infinity_hflip, isotopic_infinity_vflip⟩
  | one => exact ⟨isotopic_one_hflip, isotopic_one_vflip⟩
  | negOne => exact ⟨isotopic_negOne_hflip, isotopic_negOne_vflip⟩
  | addRight e s ih =>
    obtain ⟨ihh, ihv⟩ := ih
    simp only [TwistExpr.diagram, add_eq_add]
    constructor
    · refine .trans ?_ (.symm (.hflip_add e.diagram (crossingTangle s)))
      exact .trans (.add_left ihh) (.add_right (isotopic_crossingTangle_hflip s))
    · have hslide :
          Isotopic (crossingTangle s + e.diagram.vflip)
            (e.diagram.vflip.rot180 + crossingTangle s) :=
        flype_add s e.diagram.vflip
      have hrot : Isotopic e.diagram.vflip.rot180 e.diagram.hflip :=
        isotopic_planar (planar_vflip_rot180_hflip e.diagram)
      have hcomm : Isotopic (crossingTangle s + e.diagram.vflip)
          (e.diagram + crossingTangle s) :=
        .trans hslide (.trans (.add_left hrot) (.add_left ihh.symm))
      refine .trans hcomm.symm ?_
      refine .trans ?_ (.symm (.vflip_add e.diagram (crossingTangle s)))
      exact .add_left (isotopic_crossingTangle_vflip s)
  | addLeft e s ih =>
    obtain ⟨ihh, ihv⟩ := ih
    simp only [TwistExpr.diagram, add_eq_add]
    constructor
    · refine .trans ?_ (.symm (.hflip_add (crossingTangle s) e.diagram))
      exact .trans (.add_left (isotopic_crossingTangle_hflip s)) (.add_right ihh)
    · have hrot : Isotopic e.diagram.rot180 e.diagram :=
        isotopic_rot180_of_flips ihh ihv
      have hST : Isotopic (crossingTangle s + e.diagram)
          (e.diagram + crossingTangle s) :=
        .trans (flype_add s e.diagram) (.add_left hrot)
      refine .trans hST ?_
      refine .trans ?_ (.symm (.vflip_add (crossingTangle s) e.diagram))
      exact .trans (.add_left ihv) (.add_right (isotopic_crossingTangle_vflip s))
  | mulBottom e s ih =>
    obtain ⟨ihh, ihv⟩ := ih
    simp only [TwistExpr.diagram, mul_eq_mul]
    constructor
    · refine .symm ?_
      refine .trans (.hflip_mul e.diagram (crossingTangle s)) ?_
      refine .trans (.mul_left (isotopic_crossingTangle_hflip s).symm) ?_
      refine .trans (flype_mul s e.diagram.hflip) ?_
      refine .trans
        (.mul_left (isotopic_planar (planar_hflip_rot180_vflip e.diagram))) ?_
      exact .mul_left ihv.symm
    · refine .trans ?_ (.symm (.vflip_mul e.diagram (crossingTangle s)))
      exact .trans (.mul_left ihv) (.mul_right (isotopic_crossingTangle_vflip s))
  | mulTop e s ih =>
    obtain ⟨ihh, ihv⟩ := ih
    simp only [TwistExpr.diagram, mul_eq_mul]
    constructor
    · refine .trans ?_ (.symm (.hflip_mul (crossingTangle s) e.diagram))
      refine .trans (flype_mul s e.diagram) ?_
      refine .trans (.mul_left (isotopic_rot180_of_flips ihh ihv)) ?_
      refine .trans (.mul_left ihh) ?_
      exact .mul_right (isotopic_crossingTangle_hflip s)
    · refine .trans ?_ (.symm (.vflip_mul (crossingTangle s) e.diagram))
      exact .trans (.mul_left (isotopic_crossingTangle_vflip s)) (.mul_right ihv)

/-- Lemma 2 (i)–(iii): a rational tangle is isotopic to its horizontal flip,
    its vertical flip, and the double inversion `(Tⁱ)ⁱ = (Tʳ)ʳ`. -/
theorem flipping_lemma (T : TangleDiagram) (h : IsRational T) :
    Isotopic T T.hflip ∧ Isotopic T T.vflip ∧
      Isotopic T T.invert.invert ∧ Isotopic T.invert.invert T.rotate.rotate := by
  obtain ⟨e, he⟩ := h
  obtain ⟨hh, hv⟩ := e.isotopic_flips
  have hT_h : Isotopic T T.hflip :=
    .trans he (.trans hh (.symm (.hflip_cong he)))
  have hT_v : Isotopic T T.vflip :=
    .trans he (.trans hv (.symm (.vflip_cong he)))
  refine ⟨hT_h, hT_v, ?_, ?_⟩
  · rw [invert_invert_eq_hflip_vflip]
    exact .trans hT_v (.vflip_cong hT_h)
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
        (.add_left (isotopic_rot180_of_flips e.isotopic_flips.1 e.isotopic_flips.2))
    refine .trans hflyp ?_
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, add_eq_add] using
      Isotopic.add_left ih
  | mulTop e s ih =>
    have hflyp : Isotopic (crossingTangle s * e.diagram)
        (e.diagram * crossingTangle s) :=
      .trans (flype_mul s e.diagram)
        (.mul_left (isotopic_rot180_of_flips e.isotopic_flips.1 e.isotopic_flips.2))
    refine .trans hflyp ?_
    simpa [TwistExpr.diagram, TwistExpr.toStandard, StandardExpr.diagram, mul_eq_mul] using
      Isotopic.mul_left ih

/-- Lemma 3: every rational tangle can be brought via isotopy to standard form. -/
theorem standard_form_exists (T : TangleDiagram) (h : IsRational T) :
    ∃ e : StandardExpr, Isotopic T e.diagram := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.toStandard, .trans he e.toStandard_isotopic⟩

end RationalTangles
