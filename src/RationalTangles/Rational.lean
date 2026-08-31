/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.IntegerTangle

/-!
# Rational tangles in twist form

A rational tangle in twist form is created by consecutive additions and
multiplications by `[±1]`, starting from `[0]` or `[∞]` (Kauffman–
Lambropoulou Definition 1). The inductive type `TwistExpr` is that
algebraic expression; its diagram interpretation is a PD-code, and a
diagram is rational when it is isotopic to some twist-form diagram.

Addition or multiplication of two non-integer rational tangles need not
remain rational; the constructors only adjoin a single `[±1]` at a time
(or combine previously constructed twist-form expressions, which is the
same generation).
-/

namespace RationalTangles

/-- An algebraic twist-form expression for a rational tangle. -/
inductive TwistExpr where
  | zero
  | infinity
  | one
  | negOne
  | add : TwistExpr → TwistExpr → TwistExpr
  | mul : TwistExpr → TwistExpr → TwistExpr
  deriving DecidableEq, Repr

namespace TwistExpr

/-- The diagram denoted by a twist-form expression. -/
def diagram : TwistExpr → TangleDiagram
  | zero => TangleDiagram.zero
  | infinity => TangleDiagram.infinity
  | one => RationalTangles.one
  | negOne => RationalTangles.negOne
  | add T S => T.diagram + S.diagram
  | mul T S => T.diagram * S.diagram

end TwistExpr

/-- A diagram created by consecutive additions and multiplications by
    `[±1]`, starting from `[0]` or `[∞]`. -/
def IsTwistForm (T : TangleDiagram) : Prop :=
  ∃ e : TwistExpr, T = e.diagram

/-- A 2-tangle is rational when it is isotopic to a twist-form diagram. -/
def IsRational (T : TangleDiagram) : Prop :=
  ∃ e : TwistExpr, Isotopic T e.diagram

end RationalTangles
