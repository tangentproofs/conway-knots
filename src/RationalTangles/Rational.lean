/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Flype

/-!
# Rational tangles in twist form

A rational tangle in twist form is created by consecutive additions and
multiplications by `[±1]`, starting from `[0]` or `[∞]` (Kauffman–
Lambropoulou Definition 1). The inductive type `TwistExpr` is that
algebraic expression; its diagram interpretation is a PD-code, and a
diagram is rational when it is isotopic to some twist-form diagram.

Addition or multiplication of two non-integer rational tangles need not
remain rational; the constructors only adjoin a single `[±1]` at a time.
-/

namespace RationalTangles

/-- An algebraic twist-form expression for a rational tangle: start from
    `[0]` or `[∞]` (or the elementary `[±1]`) and repeatedly add `[±1]` on
    the left or right, or multiply by `[±1]` on the top or bottom. -/
inductive TwistExpr where
  | zero
  | infinity
  | one
  | negOne
  | addRight : TwistExpr → CrossingSign → TwistExpr
  | addLeft : TwistExpr → CrossingSign → TwistExpr
  | mulBottom : TwistExpr → CrossingSign → TwistExpr
  | mulTop : TwistExpr → CrossingSign → TwistExpr
  deriving DecidableEq, Repr

namespace TwistExpr

/-- The diagram denoted by a twist-form expression. -/
def diagram : TwistExpr → TangleDiagram
  | zero => TangleDiagram.zero
  | infinity => TangleDiagram.infinity
  | one => RationalTangles.one
  | negOne => RationalTangles.negOne
  | addRight e s => e.diagram + crossingTangle s
  | addLeft e s => crossingTangle s + e.diagram
  | mulBottom e s => e.diagram * crossingTangle s
  | mulTop e s => crossingTangle s * e.diagram

/-- Switch every crossing sign: the twist-form expression for `-T`. -/
def mirror : TwistExpr → TwistExpr
  | zero => zero
  | infinity => infinity
  | one => negOne
  | negOne => one
  | addRight e s => addRight e.mirror s.flip
  | addLeft e s => addLeft e.mirror s.flip
  | mulBottom e s => mulBottom e.mirror s.flip
  | mulTop e s => mulTop e.mirror s.flip

/-- Twist diagrams built without left-add / top-mul (so every `add`/`mul` uses
    a unit with distinct glue ports). -/
def rightBottom : TwistExpr → Prop
  | zero | infinity | one | negOne => True
  | addRight e _ | mulBottom e _ => e.rightBottom
  | addLeft _ _ | mulTop _ _ => False

theorem rightBottom_mirror (e : TwistExpr) (h : e.rightBottom) :
    e.mirror.rightBottom := by
  induction e with
  | zero | infinity | one | negOne => simp [mirror, rightBottom]
  | addRight e s ih =>
    simpa [mirror, rightBottom] using ih h
  | mulBottom e s ih =>
    simpa [mirror, rightBottom] using ih h
  | addLeft e s => cases h
  | mulTop e s => cases h

/-- Twist expressions that never use a top product. Algebraic `F` agrees with
    the right-and-bottom evaluation of `toStandard` on this class, because
    addition is commutative while the Conway product is not. -/
def noMulTop : TwistExpr → Prop
  | zero | infinity | one | negOne => True
  | addRight e _ | addLeft e _ | mulBottom e _ => e.noMulTop
  | mulTop _ _ => False

theorem noMulTop_of_rightBottom (e : TwistExpr) (h : e.rightBottom) :
    e.noMulTop := by
  induction e with
  | zero | infinity | one | negOne => simp [noMulTop]
  | addRight e s ih =>
    simpa [noMulTop] using ih h
  | mulBottom e s ih =>
    simpa [noMulTop] using ih h
  | addLeft e s => cases h
  | mulTop e s => cases h

end TwistExpr

/-- A diagram created by consecutive additions and multiplications by
    `[±1]`, starting from `[0]` or `[∞]`. -/
def IsTwistForm (T : TangleDiagram) : Prop :=
  ∃ e : TwistExpr, T = e.diagram

/-- A 2-tangle is rational when it is isotopic to a twist-form diagram. -/
def IsRational (T : TangleDiagram) : Prop :=
  ∃ e : TwistExpr, Isotopic T e.diagram

end RationalTangles
