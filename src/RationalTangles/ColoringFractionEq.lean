/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColoringToStandard
import RationalTangles.ContinuedFractionFormExists

/-!
# `f = F` along the twist → standard → continued-fraction path

`coloring_fraction_toStandard` already identifies the coloring fraction of a
`slideReady` twist-form diagram with `e.toStandard.fraction`. This file shows
that the latter is the continued-fraction value of `e.toStandard.toTerms`
(Remark 6 / Definition 8 on standard form), so `f(T) = F(T)` on that path.

This does **not** identify `TwistExpr.fraction` of a `mulTop` node with the
standard-form value: Conway product `[s]*e = 1/(1/s+F(e))` differs from
`e*[s]` (e.g. `[1]*[∞]`), while `toStandard` sends both to the same
right-and-bottom expression. Leftover `Isotopic` generators (`invert_cong`,
Figure 14 transfers, unrestricted flypes) are unused.
-/

namespace RationalTangles

theorem CrossingSign.cfValue_eq_ofInt (s : CrossingSign) :
    s.cfValue = CFValue.ofInt s.toInt := by
  cases s <;> rfl

theorem valueOfList_bumpHead (s : Int) :
    ∀ t : List Int,
      valueOfList (bumpHead s t) = (valueOfList t).add (CFValue.ofInt s)
  | [] => by
    simp [bumpHead, valueOfList, CFValue.add]
  | a :: t => by
    calc
      valueOfList (bumpHead s (a :: t))
          = (CFValue.ofInt (a + s)).add (valueOfList t).inv := by
            simp [bumpHead, valueOfList_cons]
      _ = ((CFValue.ofInt a).add (CFValue.ofInt s)).add (valueOfList t).inv := by
            rw [CFValue.ofInt_add]
      _ = (CFValue.ofInt a).add ((CFValue.ofInt s).add (valueOfList t).inv) :=
            CFValue.add_assoc _ _ _
      _ = (CFValue.ofInt a).add ((valueOfList t).inv.add (CFValue.ofInt s)) := by
            rw [CFValue.add_comm (CFValue.ofInt s)]
      _ = ((CFValue.ofInt a).add (valueOfList t).inv).add (CFValue.ofInt s) :=
            (CFValue.add_assoc _ _ _).symm
      _ = (valueOfList (a :: t)).add (CFValue.ofInt s) := by
            simp [valueOfList_cons]

theorem valueOfList_invertTerms :
    ∀ t : List Int, valueOfList (invertTerms t) = (valueOfList t).inv
  | [] => by
    simp [invertTerms, valueOfList, CFValue.inv, CFValue.ofInt, CFValue.add]
  | a :: t => by
    simp only [invertTerms]
    split_ifs with ha
    · subst ha
      simp [valueOfList_cons, CFValue.ofInt_zero, CFValue.zero_add, CFValue.inv_inv]
    · simp [valueOfList_cons, CFValue.ofInt_zero, CFValue.zero_add]

theorem valueOfList_zero_one_negOne : valueOfList [0, 1, -1] = .inf := by
  have hneg : (-1 : Rat) ≠ 0 := by decide
  -- `[0, 1, -1] = 0 + 1/(1 + 1/(-1)) = 1/0 = ∞`
  simp [valueOfList, CFValue.ofInt, CFValue.add, CFValue.inv, hneg]

/-- Definition 8 on standard form: the arithmetical fraction is the value of
    the continued-fraction term list produced by `toTerms`. -/
theorem StandardExpr.fraction_eq_valueOfList (e : StandardExpr) :
    e.fraction = valueOfList e.toTerms := by
  induction e with
  | zero =>
    simp [StandardExpr.fraction, StandardExpr.toTerms, valueOfList,
      CFValue.ofInt, CFValue.add, CFValue.inv]
    rfl
  | infinity =>
    simp [StandardExpr.fraction, StandardExpr.toTerms, valueOfList]
  | addRight e s ih =>
    simp only [StandardExpr.toTerms]
    rw [valueOfList_bumpHead, ← ih]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.toInt, one_eq_ofInt_one]
  | mulBottom e s ih =>
    simp only [StandardExpr.toTerms]
    rw [valueOfList_invertTerms, valueOfList_bumpHead, valueOfList_invertTerms, ← ih]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.toInt, one_eq_ofInt_one]

theorem StandardExpr.fraction_eq_toCF_value (e : StandardExpr) :
    e.fraction = e.toCF.value := by
  rw [StandardExpr.fraction_eq_valueOfList]
  change valueOfList e.toTerms = valueOfList e.cfTerms
  cases h : e.toTerms with
  | nil =>
    have hcf : e.cfTerms = [0, 1, -1] := by simp [StandardExpr.cfTerms, h]
    rw [hcf, valueOfList_zero_one_negOne]; rfl
  | cons a rest =>
    have hcf : e.cfTerms = a :: rest := by simp [StandardExpr.cfTerms, h]
    rw [hcf]

theorem StandardExpr.toTwist_toStandard (e : StandardExpr) :
    e.toTwist.toStandard = e := by
  induction e with
  | zero => rfl
  | infinity => rfl
  | addRight e s ih =>
    simp [StandardExpr.toTwist, TwistExpr.toStandard, ih]
  | mulBottom e s ih =>
    simp [StandardExpr.toTwist, TwistExpr.toStandard, ih]

theorem StandardExpr.toTwist_slideReady (e : StandardExpr) :
    e.toTwist.slideReady := by
  induction e with
  | zero | infinity => simp [StandardExpr.toTwist, TwistExpr.slideReady]
  | addRight e s ih =>
    simpa [StandardExpr.toTwist, TwistExpr.slideReady] using ih
  | mulBottom e s ih =>
    simpa [StandardExpr.toTwist, TwistExpr.slideReady] using ih

theorem StandardExpr.toTwist_fraction (e : StandardExpr) :
    e.toTwist.fraction = e.fraction := by
  induction e with
  | zero =>
    simp [StandardExpr.toTwist, TwistExpr.fraction, StandardExpr.fraction]
  | infinity =>
    simp [StandardExpr.toTwist, TwistExpr.fraction, StandardExpr.fraction]
  | addRight e s ih =>
    simp only [StandardExpr.toTwist, TwistExpr.fraction, ih]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, CFValue.ofInt_neg]
  | mulBottom e s ih =>
    simp only [StandardExpr.toTwist, TwistExpr.fraction, ih]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, CFValue.ofInt_neg]

theorem TwistExpr.fraction_addLeft_eq_addRight (e : TwistExpr) (s : CrossingSign) :
    (TwistExpr.addLeft e s).fraction = (TwistExpr.addRight e s).fraction :=
  CFValue.add_comm _ _

theorem TwistExpr.toStandard_addLeft (e : TwistExpr) (s : CrossingSign) :
    (TwistExpr.addLeft e s).toStandard = (TwistExpr.addRight e s).toStandard :=
  rfl

theorem TwistExpr.toStandard_mulTop (e : TwistExpr) (s : CrossingSign) :
    (TwistExpr.mulTop e s).toStandard = (TwistExpr.mulBottom e s).toStandard :=
  rfl

/-- Twist diagrams built without left-add / top-mul (so every `add`/`mul` uses
    a unit with distinct glue ports) satisfy DiagonalSum. -/
def TwistExpr.rightBottom : TwistExpr → Prop
  | zero | infinity | one | negOne => True
  | addRight e _ | mulBottom e _ => e.rightBottom
  | addLeft _ _ | mulTop _ _ => False

theorem twist_coloring_diagonal_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int) (h : e.diagram.IsColored col) :
    (ColorMatrix.of e.diagram col).DiagonalSum := by
  induction e generalizing col with
  | zero =>
    simpa [TwistExpr.diagram] using zero_diagonal_any col
  | infinity =>
    simpa [TwistExpr.diagram] using infinity_diagonal_any col
  | one =>
    simpa [TwistExpr.diagram] using one_diagonal_any col h
  | negOne =>
    simpa [TwistExpr.diagram] using negOne_diagonal_any col h
  | addRight e s ih =>
    have hrb' : e.rightBottom := hrb
    simp [TwistExpr.diagram] at h ⊢
    exact ColorMatrix.DiagonalSum_of_add (crossingTangle_NW_ne_SW s)
      (ih hrb' col (IsColored_add_left h))
      (crossingTangle_diagonal_any s _ (IsColored_add_right h))
  | mulBottom e s ih =>
    have hrb' : e.rightBottom := hrb
    simp [TwistExpr.diagram] at h ⊢
    exact ColorMatrix.DiagonalSum_of_mul (crossingTangle_NW_ne_NE s)
      (ih hrb' col (IsColored_mul_top h))
      (crossingTangle_diagonal_any s _ (IsColored_mul_bottom h))
  | addLeft e s =>
    cases hrb
  | mulTop e s =>
    cases hrb

/-- For right-and-bottom twist expressions, `F` agrees with the standard-form
    evaluation used by `toStandard`. -/
theorem TwistExpr.fraction_eq_toStandard_rightBottom (e : TwistExpr)
    (hrb : e.rightBottom) :
    e.fraction = e.toStandard.fraction := by
  induction e with
  | zero =>
    simp [TwistExpr.fraction, TwistExpr.toStandard, StandardExpr.fraction]
  | infinity =>
    simp [TwistExpr.fraction, TwistExpr.toStandard, StandardExpr.fraction]
  | one =>
    simp [TwistExpr.fraction, TwistExpr.toStandard, StandardExpr.fraction]
    have h0 : (0 : CFValue) = .ofRat 0 := rfl
    simp [h0, CFValue.zero_add]
  | negOne =>
    simp [TwistExpr.fraction, TwistExpr.toStandard, StandardExpr.fraction]
    have h0 : (0 : CFValue) = .ofRat 0 := rfl
    simp [h0, CFValue.zero_add]
  | addRight e s ih =>
    have hrb' : e.rightBottom := hrb
    simp only [TwistExpr.fraction, TwistExpr.toStandard]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, ih hrb']
  | mulBottom e s ih =>
    have hrb' : e.rightBottom := hrb
    simp only [TwistExpr.fraction, TwistExpr.toStandard]
    cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, ih hrb']
  | addLeft e s =>
    cases hrb
  | mulTop e s =>
    cases hrb

/-- `addLeft` preserves `F` relative to `toStandard` once the inner expression does
    (addition is commutative). -/
theorem TwistExpr.fraction_eq_toStandard_addLeft (e : TwistExpr) (s : CrossingSign)
    (ih : e.fraction = e.toStandard.fraction) :
    (TwistExpr.addLeft e s).fraction =
      (TwistExpr.addLeft e s).toStandard.fraction := by
  simp only [TwistExpr.fraction, TwistExpr.toStandard]
  cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, CFValue.add_comm, ih]

/-- On a `slideReady` twist-form diagram, `f = F` where `F` is the arithmetical
    fraction of `toStandard` (and hence of its continued-fraction term list).
    The `DiagonalSum` hypothesis is discharged for right-and-bottom expressions
    by `twist_coloring_diagonal_rightBottom`; for `addLeft`/`mulTop` it remains
    an input (as in `coloring_fraction_toStandard`). -/
theorem TwistExpr.rightBottom_slideReady (e : TwistExpr) (hrb : e.rightBottom) :
    e.slideReady := by
  induction e with
  | zero | infinity | one | negOne => simp [TwistExpr.slideReady]
  | addRight e s ih =>
    simpa [TwistExpr.slideReady] using ih hrb
  | mulBottom e s ih =>
    simpa [TwistExpr.slideReady] using ih hrb
  | addLeft e s => cases hrb
  | mulTop e s => cases hrb

theorem coloring_fraction_eq_F_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.fraction := by
  have hok := TwistExpr.rightBottom_slideReady e hrb
  have hdiag := twist_coloring_diagonal_rightBottom e hrb col hc
  exact (coloring_fraction_toStandard e hok col hc hdiag hm).trans
    (TwistExpr.fraction_eq_toStandard_rightBottom e hrb).symm

/-- On a standard-form diagram, every non-monochrome coloring has `f = F`,
    with `F` the continued-fraction value of `toTerms`. -/
theorem coloring_fraction_eq_F_standard (e : StandardExpr) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = valueOfList e.toTerms :=
  (standard_fraction_any_coloring e col hc hm).trans
    (StandardExpr.fraction_eq_valueOfList e)

/-- On a `slideReady` twist-form diagram, the coloring fraction equals the
    arithmetical fraction of the standard-form expression (Theorem 4(7) along
    the explicit `toStandard` path, not along an arbitrary `Isotopic`
    witness of `IsRational`). -/
theorem coloring_fraction_eq_F (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.toStandard.fraction :=
  coloring_fraction_toStandard e hok col hc hdiag hm

/-- Same as `coloring_fraction_eq_F`, written as the continued-fraction
    evaluation of the standard-form term list (Remark 6). -/
theorem coloring_fraction_eq_F_cf (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = valueOfList e.toStandard.toTerms :=
  (coloring_fraction_eq_F e hok col hc hdiag hm).trans
    (StandardExpr.fraction_eq_valueOfList e.toStandard)

end RationalTangles
