/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.Rational

/-!
# Standard form

A rational tangle is in standard form when it is created by consecutive
additions of `[±1]` only on the right and multiplications by `[±1]` only
at the bottom, starting from `[0]` or `[∞]` (Kauffman–Lambropoulou
Definition 4). This is the right-and-bottom convention of Figure 1.
-/

namespace RationalTangles

/-- A standard-form expression: right addition of `[±1]` and bottom
    multiplication by `[±1]`, starting from `[0]` or `[∞]`. -/
inductive StandardExpr where
  | zero
  | infinity
  | addRight : StandardExpr → CrossingSign → StandardExpr
  | mulBottom : StandardExpr → CrossingSign → StandardExpr
  deriving DecidableEq, Repr

namespace StandardExpr

/-- The diagram denoted by a standard-form expression. -/
def diagram : StandardExpr → TangleDiagram
  | zero => TangleDiagram.zero
  | infinity => TangleDiagram.infinity
  | addRight e s => e.diagram + crossingTangle s
  | mulBottom e s => e.diagram * crossingTangle s

/-- Switch every crossing sign: the standard-form expression for `-T`. -/
def mirror : StandardExpr → StandardExpr
  | zero => zero
  | infinity => infinity
  | addRight e s => addRight e.mirror s.flip
  | mulBottom e s => mulBottom e.mirror s.flip

end StandardExpr

/-- A diagram in standard form (right-and-bottom convention). -/
def IsStandardForm (T : TangleDiagram) : Prop :=
  ∃ e : StandardExpr, T = e.diagram

end RationalTangles
