/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import RationalTangles.FlippingLemma
import RationalTangles.ContinuedFractionForm

/-!
# Existence of continued fraction form (Proposition 1)
-/

namespace RationalTangles

open Function

def swap05_16 (n : Nat) : Nat :=
  if n = 0 then 5 else if n = 5 then 0 else if n = 1 then 6 else if n = 6 then 1 else n

theorem swap05_16_injective : Injective swap05_16 := by
  intro a b h
  unfold swap05_16 at h
  split_ifs at h <;> omega

theorem one_add_negOne_crossings :
    (one.add negOne).crossings =
      [{ a0 := 0, a1 := 1, a2 := 2, a3 := 3, sign := .pos },
       { a0 := 5, a1 := 6, a2 := 2, a3 := 1, sign := .neg }] := by
  native_decide

theorem collapseR2_one_negOne_eq :
    collapseR2 (one.add negOne) 0 1 =
      { crossings := [], NW := 5, NE := 5, SE := 6, SW := 6 } := by
  native_decide

theorem planar_zero_collapseR2_one_negOne :
    PlanarIsotopy TangleDiagram.zero (collapseR2 (one.add negOne) 0 1) := by
  rw [collapseR2_one_negOne_eq]
  refine ⟨swap05_16, swap05_16_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem isR2_one_negOne :
    IsR2Pair
      { a0 := 0, a1 := 1, a2 := 2, a3 := 3, sign := .pos }
      { a0 := 5, a1 := 6, a2 := 2, a3 := 1, sign := .neg } := by
  refine ⟨by decide, ?_, ?_, 2, 1, ?_⟩
  · simp [Crossing.adjacentDistinct]
  · simp [Crossing.adjacentDistinct]
  · refine ⟨by decide, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨Or.inr rfl, Or.inr rfl, Or.inl rfl, Or.inr rfl⟩⟩
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · simp [Crossing.memArc]
    · intro a ⟨hCa, hDa⟩
      simp [Crossing.memArc] at hCa hDa
      omega

theorem isotopic_one_add_negOne_zero :
    Isotopic (one.add negOne) TangleDiagram.zero := by
  have hlen : (one.add negOne).crossings.length = 2 := by
    rw [one_add_negOne_crossings]; rfl
  have h0 : 0 < (one.add negOne).crossings.length := by omega
  have h1 : 1 < (one.add negOne).crossings.length := by omega
  refine .step (.r2 (Or.inr ?_))
  simp only [one_add_negOne_crossings] at h0 h1 ⊢
  refine ⟨⟨0, h0⟩, ⟨1, h1⟩, Fin.ne_of_val_ne Nat.zero_ne_one, isR2_one_negOne,
    planar_zero_collapseR2_one_negOne⟩

theorem isotopic_negOne_add_one_zero :
    Isotopic (negOne.add one) TangleDiagram.zero :=
  .trans (flype_add .neg one) <|
    .trans (.add_left isotopic_one_hflip.symm) isotopic_one_add_negOne_zero

/-! ## Inversion of twist-form expressions -/

def TwistExpr.inverted : TwistExpr → TwistExpr
  | zero => infinity
  | infinity => zero
  | one => one
  | negOne => negOne
  | addRight e s => .mulTop e.inverted s
  | addLeft e s => .mulBottom e.inverted s
  | mulBottom e s => .addRight e.inverted s
  | mulTop e s => .addLeft e.inverted s

theorem planar_infinity_invert :
    PlanarIsotopy TangleDiagram.infinity.invert TangleDiagram.zero := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

theorem isotopic_infinity_invert :
    Isotopic TangleDiagram.infinity.invert TangleDiagram.zero :=
  isotopic_planar planar_infinity_invert

theorem TwistExpr.inverted_isotopic (e : TwistExpr) :
    Isotopic e.diagram.invert e.inverted.diagram := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.inverted, invert_zero]
    exact .refl _
  | infinity =>
    simpa [TwistExpr.diagram, TwistExpr.inverted] using isotopic_infinity_invert
  | one =>
    simpa [TwistExpr.diagram, TwistExpr.inverted, crossingTangle] using
      (Isotopic.invert_unit CrossingSign.pos).symm
  | negOne =>
    simpa [TwistExpr.diagram, TwistExpr.inverted, crossingTangle] using
      (Isotopic.invert_unit CrossingSign.neg).symm
  | addRight e s ih =>
    refine .trans (Isotopic.invert_add e.diagram (crossingTangle s)) ?_
    refine .trans (.mul_left (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.mul_right ih
  | addLeft e s ih =>
    refine .trans (Isotopic.invert_add (crossingTangle s) e.diagram) ?_
    refine .trans (.mul_right (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.mul_left ih
  | mulBottom e s ih =>
    refine .trans (Isotopic.invert_mul e.diagram (crossingTangle s)) ?_
    refine .trans (.add_right (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.add_left ih
  | mulTop e s ih =>
    refine .trans (Isotopic.invert_mul (crossingTangle s) e.diagram) ?_
    refine .trans (.add_left (Isotopic.invert_unit s).symm) ?_
    simpa [TwistExpr.diagram, TwistExpr.inverted] using Isotopic.add_right ih

theorem isRational_invert {T : TangleDiagram} (h : IsRational T) :
    IsRational T.invert := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.inverted, .trans (.invert_cong he) e.inverted_isotopic⟩

def StandardExpr.toTwist : StandardExpr → TwistExpr
  | zero => .zero
  | infinity => .infinity
  | addRight e s => .addRight e.toTwist s
  | mulBottom e s => .mulBottom e.toTwist s

theorem StandardExpr.toTwist_diagram (e : StandardExpr) :
    e.toTwist.diagram = e.diagram := by
  induction e <;> simp [StandardExpr.toTwist, StandardExpr.diagram, TwistExpr.diagram, *]

theorem StandardExpr.isRational (e : StandardExpr) : IsRational e.diagram :=
  ⟨e.toTwist, by simpa [e.toTwist_diagram] using Isotopic.refl _⟩

theorem lemma4_unit (T : TangleDiagram) (h : IsRational T) (s : CrossingSign) :
    Isotopic (T.mul (crossingTangle s))
      ((crossingTangle s).add T.invert).invert := by
  obtain ⟨e, he⟩ := h
  have hmul : Isotopic (T.mul (crossingTangle s)) (e.diagram.mul (crossingTangle s)) :=
    Isotopic.mul_left he
  have hR : IsRational (T.mul (crossingTangle s)) :=
    ⟨.mulBottom e s, by simpa [TwistExpr.diagram] using hmul⟩
  obtain ⟨_, _, hii, _⟩ := flipping_lemma _ hR
  have hstep : Isotopic (T.mul (crossingTangle s)).invert.invert
      (T.invert.add (crossingTangle s).invert).invert :=
    .invert_cong (Isotopic.invert_mul T (crossingTangle s))
  have hunit : Isotopic (T.invert.add (crossingTangle s).invert).invert
      (T.invert.add (crossingTangle s)).invert :=
    .invert_cong (.add_right (Isotopic.invert_unit s).symm)
  have hTinv : IsRational T.invert := isRational_invert ⟨e, he⟩
  obtain ⟨hTh, _, _, _⟩ := flipping_lemma T.invert hTinv
  have hcomm : Isotopic (T.invert.add (crossingTangle s))
      ((crossingTangle s).add T.invert) :=
    .trans (.add_left hTh) (.symm (flype_add s T.invert))
  exact .trans hii <| .trans hstep <| .trans hunit (.invert_cong hcomm)

theorem isotopic_crossing_integer (s : CrossingSign) :
    Isotopic (crossingTangle s) (integerTangle s.toInt) := by
  cases s <;> simp [crossingTangle, CrossingSign.toInt, integerTangle]
  · exact .symm (Isotopic.zero_add one)
  · exact .symm (Isotopic.zero_add negOne)



end RationalTangles
