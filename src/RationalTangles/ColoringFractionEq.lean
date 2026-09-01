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
standard-form value: the Conway product on the top differs from the
right-and-bottom product, while `toStandard` sends both to the same
right-and-bottom expression. Leftover `Isotopic` generators (`invert_cong`,
Figure 14 transfers, unrestricted flypes) are unused.

If two `slideReady` expressions denote the same PD-code and a non-monochrome
`DiagonalSum` coloring of that code exists, they share `toStandard.fraction`
(so that value is a function of the diagram). On `rightBottom` the coloring
is discharged by `colorFrom`. This is not isotopy invariance of `F`.

Along `ColoringIsotopy` (not leftover `Isotopic.invert_cong` / transfer /
unrestricted flype), the same identification `f = toStandard.fraction` shows
that standard-form `F` is unchanged. For right-and-bottom diagrams, a *fresh*
coloring of the inverted PD-code (via `coloring_invert_inv_rightBottom`) has
fraction `1/F(T)`; if two such diagrams are related by `ColoringIsotopy`,
those inverted fractions agree. That is fraction-level functoriality of invert
on this class, not a `ColoringIsotopy` constructor and not transport of every
coloring across `Crossing.switch`.
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

/-- Propagate two initial strand colors through a right-and-bottom twist
    expression (the same construction as `StandardExpr.colorFrom`, plus
    the elementary `[±1]` diagrams). Left-add / top-mul are dummy: those
    cases are excluded by `rightBottom`. -/
def TwistExpr.colorFrom : TwistExpr → Int → Int → (Nat → Int)
  | .zero, a, c => colorZero a c
  | .infinity, a, b => colorInfinity a b
  | .one, a, c => colorOne a c
  | .negOne, a, c => colorNegOne a c
  | .addRight e .pos, a, c => colorAddOne e.diagram (e.colorFrom a c)
  | .addRight e .neg, a, c => colorAddNegOne e.diagram (e.colorFrom a c)
  | .mulBottom e .pos, a, c => colorMulOne e.diagram (e.colorFrom a c)
  | .mulBottom e .neg, a, c => colorMulNegOne e.diagram (e.colorFrom a c)
  | .addLeft e _, a, c => e.colorFrom a c
  | .mulTop e _, a, c => e.colorFrom a c

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

theorem TwistExpr.fraction_eq_toStandard_addRight (e : TwistExpr) (s : CrossingSign)
    (ih : e.fraction = e.toStandard.fraction) :
    (TwistExpr.addRight e s).fraction =
      (TwistExpr.addRight e s).toStandard.fraction := by
  simp only [TwistExpr.fraction, TwistExpr.toStandard]
  cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, ih]

theorem TwistExpr.fraction_eq_toStandard_mulBottom (e : TwistExpr) (s : CrossingSign)
    (ih : e.fraction = e.toStandard.fraction) :
    (TwistExpr.mulBottom e s).fraction =
      (TwistExpr.mulBottom e s).toStandard.fraction := by
  simp only [TwistExpr.fraction, TwistExpr.toStandard]
  cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue, ih]

/-- Conway product is not commutative, so `mulTop` agrees with `toStandard`
    only when the two products evaluate equally. -/
theorem TwistExpr.fraction_eq_toStandard_mulTop (e : TwistExpr) (s : CrossingSign)
    (ih : e.fraction = e.toStandard.fraction)
    (hc : (s.cfValue.inv.add e.fraction).inv =
            (e.fraction.inv.add s.cfValue).inv) :
    (TwistExpr.mulTop e s).fraction =
      (TwistExpr.mulTop e s).toStandard.fraction := by
  calc
    (TwistExpr.mulTop e s).fraction
        = (s.cfValue.inv.add e.fraction).inv := rfl
    _ = (e.fraction.inv.add s.cfValue).inv := hc
    _ = (e.toStandard.fraction.inv.add s.cfValue).inv := by rw [ih]
    _ = (TwistExpr.mulTop e s).toStandard.fraction := by
        simp only [TwistExpr.toStandard]
        cases s <;> simp [StandardExpr.fraction, CrossingSign.cfValue]

/-- Algebraic `F` equals the standard-form evaluation of `toStandard` on every
    twist expression that never uses a top product (left addition is allowed). -/
theorem TwistExpr.fraction_eq_toStandard_of_noMulTop (e : TwistExpr)
    (h : e.noMulTop) :
    e.fraction = e.toStandard.fraction := by
  induction e with
  | zero | infinity | one | negOne =>
    exact TwistExpr.fraction_eq_toStandard_rightBottom _ trivial
  | addRight e s ih =>
    have h' : e.noMulTop := h
    exact TwistExpr.fraction_eq_toStandard_addRight e s (ih h')
  | addLeft e s ih =>
    have h' : e.noMulTop := h
    exact TwistExpr.fraction_eq_toStandard_addLeft e s (ih h')
  | mulBottom e s ih =>
    have h' : e.noMulTop := h
    exact TwistExpr.fraction_eq_toStandard_mulBottom e s (ih h')
  | mulTop e s =>
    cases h

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

theorem TwistExpr.colorFrom_isColored (e : TwistExpr) (hrb : e.rightBottom)
    (a c : Int) :
    e.diagram.IsColored (e.colorFrom a c) := by
  induction e generalizing a c with
  | zero => exact zero_isColored a c
  | infinity => exact infinity_isColored a c
  | one => exact one_isColored a c
  | negOne => exact negOne_isColored a c
  | addRight e s ih =>
    have hrb' : e.rightBottom := hrb
    cases s with
    | pos =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      exact IsColored_add_one e.diagram (e.colorFrom a c) (ih hrb' a c)
    | neg =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      exact IsColored_add_negOne e.diagram (e.colorFrom a c) (ih hrb' a c)
  | mulBottom e s ih =>
    have hrb' : e.rightBottom := hrb
    cases s with
    | pos =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      exact IsColored_mul_one e.diagram (e.colorFrom a c) (ih hrb' a c)
    | neg =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      exact IsColored_mul_negOne e.diagram (e.colorFrom a c) (ih hrb' a c)
  | addLeft e s => cases hrb
  | mulTop e s => cases hrb

theorem TwistExpr.colorFrom_diagonal (e : TwistExpr) (hrb : e.rightBottom)
    (a c : Int) :
    (ColorMatrix.of e.diagram (e.colorFrom a c)).DiagonalSum :=
  twist_coloring_diagonal_rightBottom e hrb (e.colorFrom a c)
    (e.colorFrom_isColored hrb a c)

theorem TwistExpr.colorFrom_notMono (e : TwistExpr) (hrb : e.rightBottom) :
    (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NotMono := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.colorFrom, ColorMatrix.NotMono,
      ColorMatrix.of, TangleDiagram.zero, colorZero]
  | infinity =>
    simp [TwistExpr.diagram, TwistExpr.colorFrom, ColorMatrix.NotMono,
      ColorMatrix.of, TangleDiagram.infinity, colorInfinity]
  | one =>
    change (ColorMatrix.of RationalTangles.one (colorOne 0 1)).NotMono
    rw [one_matrix]
    simp [ColorMatrix.NotMono]
  | negOne =>
    change (ColorMatrix.of RationalTangles.negOne (colorNegOne 0 1)).NotMono
    rw [negOne_matrix]
    simp [ColorMatrix.NotMono]
  | addRight e s ih =>
    have hrb' : e.rightBottom := hrb
    have hd := e.colorFrom_diagonal hrb' 0 1
    have ih' := ih hrb'
    cases s with
    | pos =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_add_one]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih' hd ⊢
      omega
    | neg =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_add_negOne]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih' hd ⊢
      omega
  | mulBottom e s ih =>
    have hrb' : e.rightBottom := hrb
    have hd := e.colorFrom_diagonal hrb' 0 1
    have ih' := ih hrb'
    cases s with
    | pos =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_mul_one]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih' hd ⊢
      omega
    | neg =>
      simp [TwistExpr.diagram, TwistExpr.colorFrom, crossingTangle]
      erw [ColorMatrix.of_mul_negOne]
      simp [ColorMatrix.NotMono, ColorMatrix.of, ColorMatrix.DiagonalSum] at ih' hd ⊢
      omega
  | addLeft e s => cases hrb
  | mulTop e s => cases hrb

/-- The propagated coloring of a right-and-bottom twist diagram has
    coloring fraction `F(e)`, so the coloring hypotheses of
    `coloring_fraction_eq_F_rightBottom` can be discharged. -/
theorem TwistExpr.colorFrom_eq_fraction (e : TwistExpr) (hrb : e.rightBottom) :
    (ColorMatrix.of e.diagram (e.colorFrom 0 1)).fraction = e.fraction :=
  coloring_fraction_eq_F_rightBottom e hrb (e.colorFrom 0 1)
    (e.colorFrom_isColored hrb 0 1) (e.colorFrom_notMono hrb)

theorem coloring_fraction_eq_F_rightBottom_exists (e : TwistExpr)
    (hrb : e.rightBottom) :
    ∃ col : Nat → Int, e.diagram.IsColored col ∧
      (ColorMatrix.of e.diagram col).DiagonalSum ∧
      (ColorMatrix.of e.diagram col).NotMono ∧
      (ColorMatrix.of e.diagram col).fraction = e.fraction :=
  ⟨e.colorFrom 0 1, e.colorFrom_isColored hrb 0 1, e.colorFrom_diagonal hrb 0 1,
    e.colorFrom_notMono hrb, e.colorFrom_eq_fraction hrb⟩

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

theorem CrossingSign.cfValue_flip (s : CrossingSign) :
    s.flip.cfValue = s.cfValue.neg := by
  cases s with
  | pos =>
    simp [CrossingSign.flip, CrossingSign.cfValue, CFValue.ofInt, CFValue.neg]
  | neg =>
    simp [CrossingSign.flip, CrossingSign.cfValue, CFValue.ofInt, CFValue.neg]
    rfl

theorem TwistExpr.fraction_mirror (e : TwistExpr) :
    e.mirror.fraction = e.fraction.neg := by
  induction e with
  | zero =>
    simp [TwistExpr.mirror, TwistExpr.fraction]
    rfl
  | infinity =>
    simp [TwistExpr.mirror, TwistExpr.fraction]
  | one =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CFValue.neg, CFValue.ofInt]
  | negOne =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CFValue.neg, CFValue.ofInt]
    rfl
  | addRight e s ih =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CrossingSign.cfValue_flip, ih,
      CFValue.neg_add]
  | addLeft e s ih =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CrossingSign.cfValue_flip, ih,
      CFValue.neg_add]
  | mulBottom e s ih =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CrossingSign.cfValue_flip, ih,
      CFValue.neg_inv, CFValue.neg_add]
  | mulTop e s ih =>
    simp [TwistExpr.mirror, TwistExpr.fraction, CrossingSign.cfValue_flip, ih,
      CFValue.neg_inv, CFValue.neg_add]

/-- On a right-and-bottom twist diagram, a non-monochrome coloring of the
    mirror has coloring fraction `-f(T)`. Uses a fresh coloring of
    `e.mirror` (via `colorFrom`): `SameEndpointColors` after `one.mirror`
    is false. -/
theorem coloring_mirror_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col col' : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hc' : e.diagram.mirror.IsColored col')
    (hm' : (ColorMatrix.of e.diagram.mirror col').NotMono) :
    (ColorMatrix.of e.diagram.mirror col').fraction =
      (ColorMatrix.of e.diagram col).fraction.neg := by
  obtain ⟨colM, hcM, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_rightBottom e hrb) col' hc'
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono := by
    simpa [hMat] using hm'
  have hfT := coloring_fraction_eq_F_rightBottom e hrb col hc hm
  have hfM := coloring_fraction_eq_F_rightBottom e.mirror
    (TwistExpr.rightBottom_mirror e hrb) colM hcM hmM
  rw [hfrac.symm, hfM, TwistExpr.fraction_mirror, hfT]

/-- Paper Theorem 4(4) on right-and-bottom twist form: `f(Tʳ) = -1/f(T)`.
    Same coloring: rotation only cycles endpoints. -/
theorem coloring_invert_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram.rotate col).fraction =
      (ColorMatrix.of e.diagram col).fraction.negInv :=
  coloring_fraction_rotate e.diagram col
    (twist_coloring_diagonal_rightBottom e hrb col hc) hm

/-- Paper Theorem 4(6) on right-and-bottom twist form: `f(Tⁱ) = 1/f(T)`.
    Fresh coloring of `e.mirror` via `colorFrom`, transported along
    `coloring_mirror_diagram_rev_rightBottom` onto `e.diagram.mirror`,
    then the same coloring of the rotate (`T.invert = T.mirror.rotate`). -/
theorem coloring_invert_inv_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction =
        (ColorMatrix.of e.diagram col).fraction.inv := by
  have hrbM : e.mirror.rightBottom := TwistExpr.rightBottom_mirror e hrb
  let colM := e.mirror.colorFrom 0 1
  have hcM : e.mirror.diagram.IsColored colM := e.mirror.colorFrom_isColored hrbM 0 1
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono :=
    e.mirror.colorFrom_notMono hrbM
  have hdM : (ColorMatrix.of e.mirror.diagram colM).DiagonalSum :=
    e.mirror.colorFrom_diagonal hrbM 0 1
  obtain ⟨col', hc', hMat, _hfrac⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_rev_rightBottom e hrb) colM hcM
  have hm' : (ColorMatrix.of e.diagram.mirror col').NotMono := by
    simpa [hMat] using hmM
  have hd' : (ColorMatrix.of e.diagram.mirror col').DiagonalSum := by
    simpa [hMat] using hdM
  have hcI : e.diagram.invert.IsColored col' := by
    simpa [invert_eq_mirror_rotate] using coloring_rotate _ col' hc'
  refine ⟨col', hcI, ?_, ?_⟩
  · have hrot :
        ColorMatrix.of e.diagram.invert col' =
          (ColorMatrix.of e.diagram.mirror col').rotate := by
      simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
    simpa [hrot] using ColorMatrix.NotMono_rotate hd' hm'
  · have hrot :
        (ColorMatrix.of e.diagram.invert col').fraction =
          (ColorMatrix.of e.diagram.mirror col').fraction.negInv := by
      simpa [invert_eq_mirror_rotate] using
        coloring_fraction_rotate e.diagram.mirror col' hd' hm'
    have hfM := coloring_mirror_rightBottom e hrb col col' hc hm hc' hm'
    rw [hrot, hfM, CFValue.negInv, ← CFValue.neg_inv, CFValue.neg_neg]

/-- Horizontal sum with a unit on the left has `DiagonalSum` when the inner
    diagram is right-and-bottom and the glue ports are distinct (the
    `slideReady` hypothesis of `addLeft`, not a degenerate identification). -/
theorem twist_coloring_diagonal_addLeft (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom)
    (hne : e.diagram.NW ≠ e.diagram.SW)
    (col : Nat → Int)
    (h : (TwistExpr.addLeft e s).diagram.IsColored col) :
    (ColorMatrix.of (TwistExpr.addLeft e s).diagram col).DiagonalSum := by
  simp [TwistExpr.diagram] at h ⊢
  exact ColorMatrix.DiagonalSum_of_add hne
    (crossingTangle_diagonal_any s _ (IsColored_add_left h))
    (twist_coloring_diagonal_rightBottom e hrb _
      (IsColored_add_right h))

theorem TwistExpr.addLeft_slideReady (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom) (hne : e.diagram.NW ≠ e.diagram.SW) :
    (TwistExpr.addLeft e s).slideReady :=
  ⟨hne, TwistExpr.rightBottom_slideReady e hrb⟩

/-- On `addLeft` of a right-and-bottom expression, with non-degenerate glue,
    `f = F`. The coloring is transported to the common `toStandard` image of
    `addLeft` and `addRight` (`toStandard_addLeft`); `DiagonalSum` is the
    honest glue of a unit on the left onto an inner right-and-bottom
    diagram, not a fake identification. -/
theorem coloring_fraction_eq_F_addLeft (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom)
    (hne : e.diagram.NW ≠ e.diagram.SW)
    (col : Nat → Int)
    (hc : (TwistExpr.addLeft e s).diagram.IsColored col)
    (hm : (ColorMatrix.of (TwistExpr.addLeft e s).diagram col).NotMono) :
    (ColorMatrix.of (TwistExpr.addLeft e s).diagram col).fraction =
      (TwistExpr.addLeft e s).fraction := by
  have hok := TwistExpr.addLeft_slideReady e s hrb hne
  have hdiag := twist_coloring_diagonal_addLeft e s hrb hne col hc
  have hf := coloring_fraction_eq_F (TwistExpr.addLeft e s) hok col hc hdiag hm
  have hF := TwistExpr.fraction_eq_toStandard_addLeft e s
    (TwistExpr.fraction_eq_toStandard_rightBottom e hrb)
  exact hf.trans hF.symm

/-- Vertical product with a unit on top has `DiagonalSum` when the inner
    diagram is right-and-bottom and the glue ports are distinct (the
    `slideReady` hypothesis of `mulTop`). -/
theorem twist_coloring_diagonal_mulTop (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom)
    (hne : e.diagram.NW ≠ e.diagram.NE)
    (col : Nat → Int)
    (h : (TwistExpr.mulTop e s).diagram.IsColored col) :
    (ColorMatrix.of (TwistExpr.mulTop e s).diagram col).DiagonalSum := by
  simp [TwistExpr.diagram] at h ⊢
  exact ColorMatrix.DiagonalSum_of_mul hne
    (crossingTangle_diagonal_any s _ (IsColored_mul_top h))
    (twist_coloring_diagonal_rightBottom e hrb _
      (IsColored_mul_bottom h))

theorem TwistExpr.mulTop_slideReady (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom) (hne : e.diagram.NW ≠ e.diagram.NE) :
    (TwistExpr.mulTop e s).slideReady :=
  ⟨hne, TwistExpr.rightBottom_slideReady e hrb⟩

/-- Conway product on the top is *not* the same arithmetic as bottom
    product, so `TwistExpr.mulTop.fraction` need not equal `toStandard`.
    The coloring fraction still matches the standard-form (right-and-bottom)
    evaluation, i.e. `F` of the isotopic `mulBottom`. -/
theorem TwistExpr.fraction_mulBottom_eq_toStandard_mulTop
    (e : TwistExpr) (s : CrossingSign) (hrb : e.rightBottom) :
    (TwistExpr.mulBottom e s).fraction =
      (TwistExpr.mulTop e s).toStandard.fraction := by
  rw [TwistExpr.toStandard_mulTop]
  exact TwistExpr.fraction_eq_toStandard_rightBottom (.mulBottom e s) hrb

/-- On `mulTop` of a right-and-bottom expression, with non-degenerate glue,
    `f` equals the arithmetical fraction of `toStandard` (the same value as
    `mulBottom`). `DiagonalSum` is the honest glue of a unit on top onto an
    inner right-and-bottom diagram. -/
theorem coloring_fraction_eq_F_mulTop (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom)
    (hne : e.diagram.NW ≠ e.diagram.NE)
    (col : Nat → Int)
    (hc : (TwistExpr.mulTop e s).diagram.IsColored col)
    (hm : (ColorMatrix.of (TwistExpr.mulTop e s).diagram col).NotMono) :
    (ColorMatrix.of (TwistExpr.mulTop e s).diagram col).fraction =
      (TwistExpr.mulTop e s).toStandard.fraction := by
  have hok := TwistExpr.mulTop_slideReady e s hrb hne
  have hdiag := twist_coloring_diagonal_mulTop e s hrb hne col hc
  exact coloring_fraction_eq_F (TwistExpr.mulTop e s) hok col hc hdiag hm

theorem coloring_fraction_eq_F_mulTop_bottom (e : TwistExpr) (s : CrossingSign)
    (hrb : e.rightBottom)
    (hne : e.diagram.NW ≠ e.diagram.NE)
    (col : Nat → Int)
    (hc : (TwistExpr.mulTop e s).diagram.IsColored col)
    (hm : (ColorMatrix.of (TwistExpr.mulTop e s).diagram col).NotMono) :
    (ColorMatrix.of (TwistExpr.mulTop e s).diagram col).fraction =
      (TwistExpr.mulBottom e s).fraction :=
  (coloring_fraction_eq_F_mulTop e s hrb hne col hc hm).trans
    (TwistExpr.fraction_mulBottom_eq_toStandard_mulTop e s hrb).symm

/-- Two `slideReady` twist expressions with the same PD-code have the same
    standard-form evaluation, once a non-monochrome `DiagonalSum` coloring of
    that code is given. Thus `toStandard.fraction` depends on the diagram, not
    the expression tree. This is not well-definedness along an `Isotopic`
    witness of `IsRational`. -/
theorem TwistExpr.toStandard_fraction_eq_of_diagram_slideReady
    {e₁ e₂ : TwistExpr}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (hd : e₁.diagram = e₂.diagram)
    (col : Nat → Int)
    (hc : e₁.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e₁.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e₁.diagram col).NotMono) :
    e₁.toStandard.fraction = e₂.toStandard.fraction := by
  have hf1 := coloring_fraction_eq_F e₁ hok₁ col hc hdiag hm
  have hc2 : e₂.diagram.IsColored col := hd ▸ hc
  have hdiag2 : (ColorMatrix.of e₂.diagram col).DiagonalSum := hd ▸ hdiag
  have hm2 : (ColorMatrix.of e₂.diagram col).NotMono := hd ▸ hm
  have hf2 := coloring_fraction_eq_F e₂ hok₂ col hc2 hdiag2 hm2
  have hM : (ColorMatrix.of e₁.diagram col).fraction =
      (ColorMatrix.of e₂.diagram col).fraction := by rw [hd]
  exact hf1.symm.trans (hM.trans hf2)

/-- Algebraic `F` agrees on `noMulTop` parses of the same PD-code, given a
    coloring as in `toStandard_fraction_eq_of_diagram_slideReady`. -/
theorem TwistExpr.fraction_eq_of_diagram_noMulTop
    {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (hd : e₁.diagram = e₂.diagram)
    (col : Nat → Int)
    (hc : e₁.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e₁.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e₁.diagram col).NotMono) :
    e₁.fraction = e₂.fraction :=
  (TwistExpr.fraction_eq_toStandard_of_noMulTop e₁ hn₁).trans
    ((TwistExpr.toStandard_fraction_eq_of_diagram_slideReady
        hok₁ hok₂ hd col hc hdiag hm).trans
      (TwistExpr.fraction_eq_toStandard_of_noMulTop e₂ hn₂).symm)

/-- Two right-and-bottom twist expressions with the same PD-code have the
    same standard-form evaluation. The coloring is `colorFrom 0 1`. -/
theorem TwistExpr.toStandard_fraction_eq_of_diagram_rightBottom
    {e₁ e₂ : TwistExpr}
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom)
    (hd : e₁.diagram = e₂.diagram) :
    e₁.toStandard.fraction = e₂.toStandard.fraction :=
  TwistExpr.toStandard_fraction_eq_of_diagram_slideReady
    (TwistExpr.rightBottom_slideReady e₁ hr₁)
    (TwistExpr.rightBottom_slideReady e₂ hr₂) hd
    (e₁.colorFrom 0 1)
    (e₁.colorFrom_isColored hr₁ 0 1)
    (e₁.colorFrom_diagonal hr₁ 0 1)
    (e₁.colorFrom_notMono hr₁)

/-- Algebraic `F` is likewise a function of the PD-code on right-and-bottom
    twist expressions. -/
theorem TwistExpr.fraction_eq_of_diagram_rightBottom
    {e₁ e₂ : TwistExpr}
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom)
    (hd : e₁.diagram = e₂.diagram) :
    e₁.fraction = e₂.fraction :=
  (TwistExpr.fraction_eq_toStandard_rightBottom e₁ hr₁).trans
    ((TwistExpr.toStandard_fraction_eq_of_diagram_rightBottom hr₁ hr₂ hd).trans
      (TwistExpr.fraction_eq_toStandard_rightBottom e₂ hr₂).symm)

/-- Two standard-form expressions with the same PD-code have the same
    arithmetical fraction. -/
theorem StandardExpr.fraction_eq_of_diagram {e₁ e₂ : StandardExpr}
    (hd : e₁.diagram = e₂.diagram) :
    e₁.fraction = e₂.fraction := by
  have hf1 := StandardExpr.colorFrom_eq_fraction e₁
  have hc : e₂.diagram.IsColored (e₁.colorFrom 0 1) := by
    simpa [hd] using e₁.colorFrom_isColored 0 1
  have hm : (ColorMatrix.of e₂.diagram (e₁.colorFrom 0 1)).NotMono := by
    simpa [hd] using e₁.colorFrom_notMono
  have hf2 := standard_fraction_any_coloring e₂ (e₁.colorFrom 0 1) hc hm
  have hM : (ColorMatrix.of e₁.diagram (e₁.colorFrom 0 1)).fraction =
      (ColorMatrix.of e₂.diagram (e₁.colorFrom 0 1)).fraction := by
    simp [hd]
  exact hf1.symm.trans (hM.trans hf2)


/-- A fresh coloring of the inverted PD-code of a right-and-bottom twist
    diagram has coloring fraction `1/F(T)`. Composes
    `coloring_invert_inv_rightBottom` with `f = F`. Not a coloring of
    `Isotopic.invert_cong` (that constructor switches every crossing). -/
theorem coloring_invert_inv_eq_F_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction = e.fraction.inv := by
  obtain ⟨col', hc', hm', hf⟩ := coloring_invert_inv_rightBottom e hrb col hc hm
  refine ⟨col', hc', hm', hf.trans (congrArg CFValue.inv ?_)⟩
  exact coloring_fraction_eq_F_rightBottom e hrb col hc hm

/-- Same as `coloring_invert_inv_eq_F_rightBottom`, discharging the coloring
    by `colorFrom 0 1`. -/
theorem coloring_invert_inv_eq_F_rightBottom_colorFrom (e : TwistExpr)
    (hrb : e.rightBottom) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction = e.fraction.inv :=
  coloring_invert_inv_eq_F_rightBottom e hrb (e.colorFrom 0 1)
    (e.colorFrom_isColored hrb 0 1) (e.colorFrom_notMono hrb)

/-- Standard-form `F` of a `slideReady` twist expression is unchanged along
    `ColoringIsotopy`, once a non-monochrome `DiagonalSum` coloring of the
    source is given (so `f = toStandard.fraction` applies on both sides).
    This is `f`-invariance of `coloring_fraction_ColoringIsotopy` lifted to
    `F` on `slideReady` diagrams. It is not Theorem 2 for arbitrary
    `Isotopic` witnesses. -/
theorem TwistExpr.toStandard_fraction_ColoringIsotopy {e₁ e₂ : TwistExpr}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram)
    (col : Nat → Int)
    (hc : e₁.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e₁.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e₁.diagram col).NotMono) :
    e₁.toStandard.fraction = e₂.toStandard.fraction := by
  have hf1 := coloring_fraction_eq_F e₁ hok₁ col hc hdiag hm
  obtain ⟨col', hc', hMat, hfrac⟩ := coloring_fraction_ColoringIsotopy h col hc
  have hdiag' : (ColorMatrix.of e₂.diagram col').DiagonalSum := by
    simpa [hMat] using hdiag
  have hm' : (ColorMatrix.of e₂.diagram col').NotMono := by
    simpa [hMat] using hm
  have hf2 := coloring_fraction_eq_F e₂ hok₂ col' hc' hdiag' hm'
  exact hf1.symm.trans (hfrac.symm.trans hf2)

/-- Algebraic `F` is likewise unchanged along `ColoringIsotopy` for
    `noMulTop` `slideReady` expressions, given a coloring as in
    `toStandard_fraction_ColoringIsotopy`. -/
theorem TwistExpr.fraction_ColoringIsotopy_noMulTop {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram)
    (col : Nat → Int)
    (hc : e₁.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e₁.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e₁.diagram col).NotMono) :
    e₁.fraction = e₂.fraction :=
  (TwistExpr.fraction_eq_toStandard_of_noMulTop e₁ hn₁).trans
    ((TwistExpr.toStandard_fraction_ColoringIsotopy
        hok₁ hok₂ h col hc hdiag hm).trans
      (TwistExpr.fraction_eq_toStandard_of_noMulTop e₂ hn₂).symm)

/-- Algebraic `F` of a right-and-bottom twist expression is unchanged along
    `ColoringIsotopy`. The coloring is `colorFrom 0 1`. -/
theorem TwistExpr.fraction_ColoringIsotopy_rightBottom {e₁ e₂ : TwistExpr}
    (hr₁ : e₁.rightBottom) (hr₂ : e₂.rightBottom)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.fraction = e₂.fraction :=
  TwistExpr.fraction_ColoringIsotopy_noMulTop
    (TwistExpr.noMulTop_of_rightBottom e₁ hr₁)
    (TwistExpr.noMulTop_of_rightBottom e₂ hr₂)
    (TwistExpr.rightBottom_slideReady e₁ hr₁)
    (TwistExpr.rightBottom_slideReady e₂ hr₂) h
    (e₁.colorFrom 0 1)
    (e₁.colorFrom_isColored hr₁ 0 1)
    (e₁.colorFrom_diagonal hr₁ 0 1)
    (e₁.colorFrom_notMono hr₁)

/-- If two right-and-bottom twist diagrams are related by `ColoringIsotopy`,
    then *fresh* colorings of their inverted PD-codes have the same coloring
    fraction `1/F(T)`. This is the fraction-level content of
    `Isotopic.invert_cong` on this class. It does not add `invert_cong` to
    `ColoringIsotopy` (colorings are not transported across `switch`). -/
theorem coloring_invert_cong_rightBottom {e e' : TwistExpr}
    (hrb : e.rightBottom) (hrb' : e'.rightBottom)
    (h : ColoringIsotopy e.diagram e'.diagram) :
    ∃ colI colI',
      e.diagram.invert.IsColored colI ∧
      e'.diagram.invert.IsColored colI' ∧
      (ColorMatrix.of e.diagram.invert colI).NotMono ∧
      (ColorMatrix.of e'.diagram.invert colI').NotMono ∧
      (ColorMatrix.of e.diagram.invert colI).fraction =
        (ColorMatrix.of e'.diagram.invert colI').fraction := by
  obtain ⟨colI, hcI, hmI, hfI⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom e hrb
  obtain ⟨colI', hcI', hmI', hfI'⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom e' hrb'
  refine ⟨colI, colI', hcI, hcI', hmI, hmI', ?_⟩
  rw [hfI, hfI', TwistExpr.fraction_ColoringIsotopy_rightBottom hrb hrb' h]

end RationalTangles
