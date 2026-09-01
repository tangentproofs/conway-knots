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
right-and-bottom expression. Unrestricted Figure 14 transfers and flypes are
not `ColoringIsotopy` constructors. On `[±1]`, Figure 14 (`transfer_odd`) is colored with independent
colorings of each side (the coloring of `T.mirror.invert` reuses the arc
map of `T` because double mirror is `rotate180`; `SameEndpointColors`
after `one.mirror` remains false). Integer `[n]` and `[0]` are not
colored here.

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


/-! ## Figure 14 (`transfer_odd`) on units and integer tangles

`Isotopic.transfer_odd` is `(T+[-1])*[+1] ∼ [+1]+(-T)ⁱ`. The right-hand
side applies `Crossing.switch` to `T`, so this is not a `ColoringIsotopy`
constructor. Double mirror is `rotate180`, so the *same* arc coloring of
`T` colors `T.mirror.invert = T.mirror.mirror.rotate`; that is not
`SameEndpointColors` after `one.mirror`.
-/

theorem IsColored_mirror_mirror (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) : T.mirror.mirror.IsColored col := by
  intro C hC
  have hmap :
      T.mirror.mirror.crossings = T.crossings.map Crossing.rotate180 := by
    simp [TangleDiagram.mirror, List.map_map, Function.comp, Crossing.switch_switch]
  rw [hmap, List.mem_map] at hC
  obtain ⟨C0, hC0, rfl⟩ := hC
  exact ColoringRule_rotate180 C0 col (h C0 hC0)

theorem IsColored_mirror_invert (T : TangleDiagram) (col : Nat → Int)
    (h : T.IsColored col) : T.mirror.invert.IsColored col := by
  simpa [invert_eq_mirror_rotate] using
    coloring_rotate T.mirror.mirror col (IsColored_mirror_mirror T col h)

theorem ColorMatrix.of_mirror_mirror (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of T.mirror.mirror col = ColorMatrix.of T col := by
  simp [ColorMatrix.of, TangleDiagram.mirror]

theorem ColorMatrix.of_mirror_invert (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of T.mirror.invert col = (ColorMatrix.of T col).rotate := by
  rw [invert_eq_mirror_rotate, ColorMatrix.of_rotate, ColorMatrix.of_mirror_mirror]

theorem coloring_fraction_mirror_invert (T : TangleDiagram) (col : Nat → Int)
    (hdiag : (ColorMatrix.of T col).DiagonalSum)
    (hm : (ColorMatrix.of T col).NotMono) :
    (ColorMatrix.of T.mirror.invert col).fraction =
      (ColorMatrix.of T col).fraction.negInv := by
  rw [ColorMatrix.of_mirror_invert]
  exact ColorMatrix.fraction_rotate hdiag hm

theorem TangleDiagram.mirror_invert_NW (T : TangleDiagram) :
    T.mirror.invert.NW = T.NE := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.mirror_invert_NE (T : TangleDiagram) :
    T.mirror.invert.NE = T.SE := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.mirror_invert_SE (T : TangleDiagram) :
    T.mirror.invert.SE = T.SW := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.mirror_invert_SW (T : TangleDiagram) :
    T.mirror.invert.SW = T.NW := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem CFValue.transfer_odd_value (x : CFValue) :
    ((x.add (ofInt (-1))).inv.add (ofInt 1)).inv =
      (ofInt 1).add (x.neg.inv) := by
  cases x with
  | inf =>
    simp [ofInt, add, neg, inv]
  | ofRat q =>
    have hsum : (ofRat q).add (ofInt (-1)) = ofRat (q - 1) := by
      simp [ofInt, add, sub_eq_add_neg]
    rw [hsum]
    by_cases h1 : q - 1 = 0
    · have hq : q = 1 := by linarith
      subst hq
      simp [ofInt, add, neg, inv]
    · have hq1 : (q - 1 : Rat) ≠ 0 := by exact_mod_cast h1
      rw [inv_ofRat hq1]
      have hadd :
          (ofRat (q - 1)⁻¹).add (ofInt 1) = ofRat ((q - 1)⁻¹ + 1) := by
        simp [ofInt, add]
      rw [hadd]
      have hval : ((q - 1)⁻¹ + 1 : Rat) = q / (q - 1) := by
        field_simp [hq1]
        ring
      rw [hval]
      by_cases hq0 : q = 0
      · subst hq0
        simp [inv, add, ofInt]
      · have hfrac : q / (q - 1) ≠ 0 := div_ne_zero hq0 hq1
        rw [inv_ofRat hfrac]
        have hnq : -q ≠ 0 := by intro h; exact hq0 (neg_eq_zero.mp h)
        have hR : (ofInt 1).add (ofRat q).neg.inv =
            ofRat (1 + (-q)⁻¹) := by
          simp [ofInt, add, neg, inv, hq0, hnq]
        rw [hR]
        congr 1
        field_simp [hq0, hq1]
        ring

theorem TwistExpr.fraction_transfer_odd (e : TwistExpr) :
    (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).fraction =
      (1 : CFValue).add (e.fraction.neg.inv) := by
  simpa [TwistExpr.fraction, CrossingSign.cfValue, one_eq_ofInt_one] using
    CFValue.transfer_odd_value e.fraction

theorem TwistExpr.transferOdd_rightBottom (e : TwistExpr) (h : e.rightBottom) :
    (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).rightBottom :=
  h


theorem TwistExpr.transferOdd_diagram (e : TwistExpr) :
    (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).diagram =
      (e.diagram.add RationalTangles.negOne).mul RationalTangles.one :=
  rfl

theorem ColorMatrix.ext {M N : ColorMatrix}
    (hNW : M.NW = N.NW) (hNE : M.NE = N.NE)
    (hSW : M.SW = N.SW) (hSE : M.SE = N.SE) : M = N := by
  cases M; cases N; congr

/-- Glue `[+1]` on the left of a colored diagram with distinct left ports. -/
theorem coloring_one_add (S : TangleDiagram) (colS : Nat → Int)
    (hcS : S.IsColored colS) (hne : S.NW ≠ S.SW) :
    ∃ colG, (RationalTangles.one.add S).IsColored colG ∧
      ColorMatrix.of (RationalTangles.one.add S) colG =
        { NW := colS S.SW
          NE := colS S.NE
          SW := 2 * colS S.SW - colS S.NW
          SE := colS S.SE } := by
  let U := RationalTangles.one
  let colU := colorOne (colS S.SW) (colS S.NW)
  let colG := colorGlueAdd U S colU colS
  have glueNE : colU U.NE = colS S.NW := by
    simp [colU, colorOne_1, U, RationalTangles.one]
  have glueSE : colU U.SE = colS S.SW ∨ S.NW = S.SW := by
    left
    simp [colU, colorOne_2, U, RationalTangles.one]
  refine ⟨colG,
    IsColored_colorGlueAdd U S colU colS (one_isColored _ _) hcS glueNE glueSE, ?_⟩
  have hNW : colG (U.add S).NW = colU U.NW :=
    colorGlueAdd_of_le U S colU colS (maxArc_ge_NW U)
  have hSW : colG (U.add S).SW = colU U.SW :=
    colorGlueAdd_of_le U S colU colS (maxArc_ge_SW U)
  have hNE : colG (U.add S).NE = colS S.NE := by
    rw [add_NE U S]
    exact colorGlueAdd_comp_shift U S colU colS glueNE glueSE S.NE
  have hSE : colG (U.add S).SE = colS S.SE := by
    rw [add_SE U S]
    exact colorGlueAdd_comp_shift U S colU colS glueNE glueSE S.SE
  apply ColorMatrix.ext
  · simpa [ColorMatrix.of, colU, colorOne_0, U, RationalTangles.one] using hNW
  · simpa [ColorMatrix.of] using hNE
  · simpa [ColorMatrix.of, colU, colorOne_3, U, RationalTangles.one] using hSW
  · simpa [ColorMatrix.of] using hSE

theorem coloring_fraction_one_add (S : TangleDiagram) (colS : Nat → Int)
    (hcS : S.IsColored colS) (hne : S.NW ≠ S.SW)
    (hdiagS : (ColorMatrix.of S colS).DiagonalSum)
    (hcol : colS S.NW ≠ colS S.SW) :
    ∃ colG, (RationalTangles.one.add S).IsColored colG ∧
      (ColorMatrix.of (RationalTangles.one.add S) colG).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add S) colG).fraction =
        (1 : CFValue).add (ColorMatrix.of S colS).fraction := by
  obtain ⟨colG, hcG, hMat⟩ := coloring_one_add S colS hcS hne
  refine ⟨colG, hcG, ?_, ?_⟩
  · rw [hMat]
    dsimp [ColorMatrix.NotMono]
    intro h
    simp [ColorMatrix.DiagonalSum, ColorMatrix.of] at hdiagS
    exact hcol (by omega)
  · have hglue :
        (ColorMatrix.mk (colS S.SW) (colS S.NW)
            (2 * colS S.SW - colS S.NW) (colS S.SW)).fraction.add
          (ColorMatrix.of S colS).fraction =
        (ColorMatrix.mk (colS S.SW) (colS S.NE)
            (2 * colS S.SW - colS S.NW) (colS S.SE)).fraction := by
      have hd : colS S.NW - colS S.SW = colS S.NE - colS S.SE := by
        simp [ColorMatrix.DiagonalSum, ColorMatrix.of] at hdiagS
        omega
      simpa [ColorMatrix.of] using
        ColorMatrix.fraction_add_glue (colS S.SW) (colS S.NW)
          (2 * colS S.SW - colS S.NW) (colS S.SW) (colS S.NE) (colS S.SE) hd
    have hone :
        (ColorMatrix.mk (colS S.SW) (colS S.NW)
          (2 * colS S.SW - colS S.NW) (colS S.SW)).fraction = (1 : CFValue) :=
      one_fraction (β := colS S.SW) (α := colS S.NW) hcol
    rw [hMat, ← hglue, hone]

/-- Color both sides of Figure 14 on a right-and-bottom twist diagram
    whose `colorFrom 0 1` has distinct `NW`/`NE`. The left-hand side is
    colored by `colorFrom`; the right-hand side reuses that coloring on
    `T.mirror.invert` (double mirror is `rotate180`) and glues `[+1]`. -/
theorem coloring_transfer_odd_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (hports : e.diagram.NW ≠ e.diagram.NE)
    (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
    ∃ colL colR,
      ((e.diagram.add RationalTangles.negOne).mul RationalTangles.one).IsColored
        colL ∧
      (RationalTangles.one.add e.diagram.mirror.invert).IsColored colR ∧
      (ColorMatrix.of ((e.diagram.add RationalTangles.negOne).mul
        RationalTangles.one) colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add e.diagram.mirror.invert)
        colR).NotMono ∧
      (ColorMatrix.of ((e.diagram.add RationalTangles.negOne).mul
        RationalTangles.one) colL).fraction =
        (ColorMatrix.of (RationalTangles.one.add e.diagram.mirror.invert)
          colR).fraction := by
  let eL : TwistExpr := .mulBottom (.addRight e .neg) .pos
  have hrbL : eL.rightBottom := hrb
  let colT := e.colorFrom 0 1
  let colL := eL.colorFrom 0 1
  have hcT := e.colorFrom_isColored hrb 0 1
  have hdiagT := e.colorFrom_diagonal hrb 0 1
  have hmT := e.colorFrom_notMono hrb
  have hcS : e.diagram.mirror.invert.IsColored colT :=
    IsColored_mirror_invert e.diagram colT hcT
  have hneS : e.diagram.mirror.invert.NW ≠ e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    exact hports.symm
  have hdiagS : (ColorMatrix.of e.diagram.mirror.invert colT).DiagonalSum := by
    rw [ColorMatrix.of_mirror_invert]
    exact ColorMatrix.DiagonalSum.rotate hdiagT
  have hcolS : colT e.diagram.mirror.invert.NW ≠
      colT e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    exact hne.symm
  obtain ⟨colR, hcR, hmR, hfR⟩ :=
    coloring_fraction_one_add e.diagram.mirror.invert colT hcS hneS hdiagS hcolS
  refine ⟨colL, colR, ?_, hcR, eL.colorFrom_notMono hrbL, hmR, ?_⟩
  · simpa [eL, TwistExpr.diagram, crossingTangle] using
      eL.colorFrom_isColored hrbL 0 1
  · have hfL := eL.colorFrom_eq_fraction hrbL
    have hfT := e.colorFrom_eq_fraction hrb
    have hfS := coloring_fraction_mirror_invert e.diagram colT hdiagT hmT
    have hLd :
        ColorMatrix.of ((e.diagram.add RationalTangles.negOne).mul
          RationalTangles.one) colL =
          ColorMatrix.of eL.diagram colL := by
      simp [eL, TwistExpr.diagram, crossingTangle]
    rw [hLd, hfL, hfR, hfS, hfT, TwistExpr.fraction_transfer_odd]
    exact congrArg (CFValue.add (1 : CFValue)) (CFValue.neg_inv e.fraction).symm

theorem coloring_transfer_odd_one :
    ∃ colL colR,
      ((RationalTangles.one.add RationalTangles.negOne).mul
        RationalTangles.one).IsColored colL ∧
      (RationalTangles.one.add RationalTangles.one.mirror.invert).IsColored colR ∧
      (ColorMatrix.of ((RationalTangles.one.add RationalTangles.negOne).mul
        RationalTangles.one) colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one.mirror.invert)
        colR).NotMono ∧
      (ColorMatrix.of ((RationalTangles.one.add RationalTangles.negOne).mul
        RationalTangles.one) colL).fraction =
        (ColorMatrix.of (RationalTangles.one.add RationalTangles.one.mirror.invert)
          colR).fraction := by
  simpa [TwistExpr.diagram] using
    coloring_transfer_odd_rightBottom .one trivial one_NW_ne_NE (by
      change (ColorMatrix.of RationalTangles.one (colorOne 0 1)).NW ≠
        (ColorMatrix.of RationalTangles.one (colorOne 0 1)).NE
      simp [one_matrix])

theorem coloring_transfer_odd_negOne :
    ∃ colL colR,
      ((RationalTangles.negOne.add RationalTangles.negOne).mul
        RationalTangles.one).IsColored colL ∧
      (RationalTangles.one.add RationalTangles.negOne.mirror.invert).IsColored
        colR ∧
      (ColorMatrix.of ((RationalTangles.negOne.add RationalTangles.negOne).mul
        RationalTangles.one) colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add
        RationalTangles.negOne.mirror.invert) colR).NotMono ∧
      (ColorMatrix.of ((RationalTangles.negOne.add RationalTangles.negOne).mul
        RationalTangles.one) colL).fraction =
        (ColorMatrix.of (RationalTangles.one.add
          RationalTangles.negOne.mirror.invert) colR).fraction := by
  have hne :
      (ColorMatrix.of TwistExpr.negOne.diagram
        (TwistExpr.negOne.colorFrom 0 1)).NW ≠
      (ColorMatrix.of TwistExpr.negOne.diagram
        (TwistExpr.negOne.colorFrom 0 1)).NE := by
    simp only [TwistExpr.diagram, TwistExpr.colorFrom]
    change (ColorMatrix.of RationalTangles.negOne (colorNegOne 0 1)).NW ≠
      (ColorMatrix.of RationalTangles.negOne (colorNegOne 0 1)).NE
    rw [negOne_matrix]
    decide
  simpa [TwistExpr.diagram] using
    coloring_transfer_odd_rightBottom .negOne trivial negOne_NW_ne_NE hne

/-! ## Fresh coloring fractions for `invert_add` / `invert_mul` on units

`Isotopic.invert_add` / `invert_mul` apply `Crossing.switch`, so a coloring
of one side is not reused on the other. On `[±1]` the two PD-codes still
have the same coloring fraction, computed from independent `colorFrom`
colorings (the inverted sum via `coloring_invert_inv_eq_F_rightBottom_colorFrom`,
the inverted-unit product via `colorFrom` of a right-and-bottom product
transported along `ColoringIsotopy.invert_unit`).

Kinks `[∞]+[±1]` (degenerate glue: both right ports of `[∞]` are the same
arc) are not treated here.
-/

def TwistExpr.ofCrossingSign : CrossingSign → TwistExpr
  | .pos => .one
  | .neg => .negOne

theorem TwistExpr.ofCrossingSign_diagram (s : CrossingSign) :
    (TwistExpr.ofCrossingSign s).diagram = crossingTangle s := by
  cases s with
  | pos => simp only [TwistExpr.ofCrossingSign, TwistExpr.diagram, crossingTangle]
  | neg => simp only [TwistExpr.ofCrossingSign, TwistExpr.diagram, crossingTangle]

theorem TwistExpr.ofCrossingSign_rightBottom (s : CrossingSign) :
    (TwistExpr.ofCrossingSign s).rightBottom := by
  cases s <;> trivial

theorem TwistExpr.ofCrossingSign_fraction (s : CrossingSign) :
    (TwistExpr.ofCrossingSign s).fraction = s.cfValue := by
  cases s with
  | pos => simp only [TwistExpr.ofCrossingSign, TwistExpr.fraction, CrossingSign.cfValue]
  | neg => simp only [TwistExpr.ofCrossingSign, TwistExpr.fraction, CrossingSign.cfValue]

theorem CFValue.inv_one : (1 : CFValue).inv = 1 := by
  have h : (1 : Rat) ≠ 0 := by decide
  change (ofRat 1).inv = ofRat 1
  rw [inv_ofRat h]
  congr 1
  norm_num

theorem CFValue.inv_ofInt_negOne : (ofInt (-1)).inv = ofInt (-1) := by
  have h : ((-1 : Int) : Rat) ≠ 0 := by decide
  simp only [ofInt]
  rw [inv_ofRat h]
  congr 1
  norm_num

theorem CrossingSign.cfValue_inv (s : CrossingSign) :
    s.cfValue.inv = s.cfValue := by
  cases s with
  | pos =>
    simp only [CrossingSign.cfValue]
    exact CFValue.inv_one
  | neg =>
    simp only [CrossingSign.cfValue]
    exact CFValue.inv_ofInt_negOne

/-- Algebra of `invert_add` on units: `1/(a+b) = 1/(1/b + a)`. -/
theorem CFValue.invert_add_units (a b : CrossingSign) :
    (a.cfValue.add b.cfValue).inv = (b.cfValue.inv.add a.cfValue).inv := by
  rw [CrossingSign.cfValue_inv]
  rw [CFValue.add_comm b.cfValue a.cfValue]

theorem TwistExpr.addRight_ofCrossingSign_fraction (s t : CrossingSign) :
    (TwistExpr.addRight (TwistExpr.ofCrossingSign s) t).fraction =
      s.cfValue.add t.cfValue := by
  simp only [TwistExpr.fraction, TwistExpr.ofCrossingSign_fraction]

theorem TwistExpr.mulBottom_ofCrossingSign_fraction (s t : CrossingSign) :
    (TwistExpr.mulBottom (TwistExpr.ofCrossingSign s) t).fraction =
      (s.cfValue.inv.add t.cfValue).inv := by
  simp only [TwistExpr.fraction, TwistExpr.ofCrossingSign_fraction]

theorem coloring_mul_invert_units (s t : CrossingSign) :
    ColoringIsotopy
      ((crossingTangle t).mul (crossingTangle s))
      ((crossingTangle t).invert.mul (crossingTangle s).invert) := by
  have hglue :
      (crossingTangle s).NW = (crossingTangle s).NE →
        (crossingTangle s).invert.NW = (crossingTangle s).invert.NE := by
    intro h
    exact (crossingTangle_NW_ne_NE s h).elim
  exact ColoringIsotopy.trans
    (ColoringIsotopy.mul_right (ColoringIsotopy.invert_unit s) hglue)
    (ColoringIsotopy.mul_left (ColoringIsotopy.invert_unit t))

theorem coloring_add_invert_units (s t : CrossingSign) :
    ColoringIsotopy
      ((crossingTangle s).add (crossingTangle t))
      ((crossingTangle s).invert.add (crossingTangle t).invert) := by
  have hglue :
      (crossingTangle t).NW = (crossingTangle t).SW →
        (crossingTangle t).invert.NW = (crossingTangle t).invert.SW := by
    intro h
    exact (crossingTangle_NW_ne_SW t h).elim
  exact ColoringIsotopy.trans
    (ColoringIsotopy.add_right (ColoringIsotopy.invert_unit t) hglue)
    (ColoringIsotopy.add_left (ColoringIsotopy.invert_unit s))

/-- Fresh coloring of `(T+S)ⁱ` and of `Sⁱ * Tⁱ` for `T,S ∈ {[+1],[-1]}`.
    Not a `ColoringIsotopy` constructor (`invert_add` switches crossings). -/
theorem coloring_invert_add_units (s t : CrossingSign) :
    ∃ colL colR,
      (((crossingTangle s).add (crossingTangle t)).invert).IsColored colL ∧
      (((crossingTangle t).invert.mul (crossingTangle s).invert)).IsColored colR ∧
      (ColorMatrix.of ((crossingTangle s).add (crossingTangle t)).invert
        colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle t).invert.mul (crossingTangle s).invert)
        colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).add (crossingTangle t)).invert
        colL).fraction =
        (ColorMatrix.of ((crossingTangle t).invert.mul
          (crossingTangle s).invert) colR).fraction := by
  let eL : TwistExpr := .addRight (.ofCrossingSign s) t
  have hrbL : eL.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  let eR : TwistExpr := .mulBottom (.ofCrossingSign t) s
  have hrbR : eR.rightBottom := TwistExpr.ofCrossingSign_rightBottom t
  have hdiag :
      eL.diagram = (crossingTangle s).add (crossingTangle t) := by
    simp only [eL, TwistExpr.diagram, TwistExpr.ofCrossingSign_diagram]
    rfl
  have hdiagR :
      eR.diagram = (crossingTangle t).mul (crossingTangle s) := by
    simp only [eR, TwistExpr.diagram, TwistExpr.ofCrossingSign_diagram]
    rfl
  have hcL' :
      ((crossingTangle s).add (crossingTangle t)).invert.IsColored colL := by
    simpa only [hdiag] using hcL
  have hmL' :
      (ColorMatrix.of ((crossingTangle s).add (crossingTangle t)).invert
        colL).NotMono := by
    simpa only [hdiag] using hmL
  have hfL' :
      (ColorMatrix.of ((crossingTangle s).add (crossingTangle t)).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hdiag] using hfL
  let col0 := eR.colorFrom 0 1
  have hc0 := eR.colorFrom_isColored hrbR 0 1
  have hm0 := eR.colorFrom_notMono hrbR
  have hf0 := eR.colorFrom_eq_fraction hrbR
  have hstep : ColoringIsotopy eR.diagram
      ((crossingTangle t).invert.mul (crossingTangle s).invert) := by
    simpa only [hdiagR] using coloring_mul_invert_units s t
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep col0 hc0
  have hmR : (ColorMatrix.of
      ((crossingTangle t).invert.mul (crossingTangle s).invert) colR).NotMono := by
    simpa only [hMat] using hm0
  refine ⟨colL, colR, hcL', hcR, hmL', hmR, ?_⟩
  have hfR :
      (ColorMatrix.of ((crossingTangle t).invert.mul (crossingTangle s).invert)
        colR).fraction = eR.fraction :=
    hfrac.trans hf0
  rw [hfL', hfR, TwistExpr.addRight_ofCrossingSign_fraction,
    TwistExpr.mulBottom_ofCrossingSign_fraction]
  exact CFValue.invert_add_units s t

/-- Fresh coloring of `(T*S)ⁱ` and of `Tⁱ + Sⁱ` for `T,S ∈ {[+1],[-1]}`.
    Not a `ColoringIsotopy` constructor (`invert_mul` switches crossings). -/
theorem coloring_invert_mul_units (s t : CrossingSign) :
    ∃ colL colR,
      (((crossingTangle s).mul (crossingTangle t)).invert).IsColored colL ∧
      (((crossingTangle s).invert.add (crossingTangle t).invert)).IsColored colR ∧
      (ColorMatrix.of ((crossingTangle s).mul (crossingTangle t)).invert
        colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).invert.add (crossingTangle t).invert)
        colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).mul (crossingTangle t)).invert
        colL).fraction =
        (ColorMatrix.of ((crossingTangle s).invert.add
          (crossingTangle t).invert) colR).fraction := by
  let eL : TwistExpr := .mulBottom (.ofCrossingSign s) t
  have hrbL : eL.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  let eR : TwistExpr := .addRight (.ofCrossingSign s) t
  have hrbR : eR.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  have hdiag :
      eL.diagram = (crossingTangle s).mul (crossingTangle t) := by
    simp only [eL, TwistExpr.diagram, TwistExpr.ofCrossingSign_diagram]
    rfl
  have hdiagR :
      eR.diagram = (crossingTangle s).add (crossingTangle t) := by
    simp only [eR, TwistExpr.diagram, TwistExpr.ofCrossingSign_diagram]
    rfl
  have hcL' :
      ((crossingTangle s).mul (crossingTangle t)).invert.IsColored colL := by
    simpa only [hdiag] using hcL
  have hmL' :
      (ColorMatrix.of ((crossingTangle s).mul (crossingTangle t)).invert
        colL).NotMono := by
    simpa only [hdiag] using hmL
  have hfL' :
      (ColorMatrix.of ((crossingTangle s).mul (crossingTangle t)).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hdiag] using hfL
  let col0 := eR.colorFrom 0 1
  have hc0 := eR.colorFrom_isColored hrbR 0 1
  have hm0 := eR.colorFrom_notMono hrbR
  have hf0 := eR.colorFrom_eq_fraction hrbR
  have hstep : ColoringIsotopy eR.diagram
      ((crossingTangle s).invert.add (crossingTangle t).invert) := by
    simpa only [hdiagR] using coloring_add_invert_units s t
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep col0 hc0
  have hmR : (ColorMatrix.of
      ((crossingTangle s).invert.add (crossingTangle t).invert) colR).NotMono := by
    simpa only [hMat] using hm0
  refine ⟨colL, colR, hcL', hcR, hmL', hmR, ?_⟩
  have hfR :
      (ColorMatrix.of ((crossingTangle s).invert.add (crossingTangle t).invert)
        colR).fraction = eR.fraction :=
    hfrac.trans hf0
  rw [hfL', hfR, TwistExpr.mulBottom_ofCrossingSign_fraction,
    TwistExpr.addRight_ofCrossingSign_fraction, CFValue.inv_inv,
    CrossingSign.cfValue_inv]

theorem coloring_invert_add_one_one :
    ∃ colL colR,
      ((RationalTangles.one.add RationalTangles.one).invert).IsColored colL ∧
      (RationalTangles.one.invert.mul RationalTangles.one.invert).IsColored colR ∧
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one).invert
        colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.invert.mul RationalTangles.one.invert)
        colR).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one).invert
        colL).fraction =
        (ColorMatrix.of (RationalTangles.one.invert.mul
          RationalTangles.one.invert) colR).fraction := by
  simpa only [crossingTangle] using coloring_invert_add_units .pos .pos

theorem coloring_invert_mul_one_one :
    ∃ colL colR,
      ((RationalTangles.one.mul RationalTangles.one).invert).IsColored colL ∧
      (RationalTangles.one.invert.add RationalTangles.one.invert).IsColored colR ∧
      (ColorMatrix.of (RationalTangles.one.mul RationalTangles.one).invert
        colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.invert.add RationalTangles.one.invert)
        colR).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.mul RationalTangles.one).invert
        colL).fraction =
        (ColorMatrix.of (RationalTangles.one.invert.add
          RationalTangles.one.invert) colR).fraction := by
  simpa only [crossingTangle] using coloring_invert_mul_units .pos .pos

/-! ## Fresh coloring fractions for `invert_add` / `invert_mul` with `[0]`
    and `[∞]` (no kinks)

`[∞]+[±1]` is excluded: both right ports of `[∞]` are the same arc.
`infinity.invert` is not rewritten to `zero` (those PD-codes differ by a
rename). Independent `colorFrom` colorings; inversion still switches
crossings, so this is not a `ColoringIsotopy` constructor.
-/

theorem TwistExpr.addRight_zero_fraction (s : CrossingSign) :
    (TwistExpr.addRight .zero s).fraction = s.cfValue := by
  simp only [TwistExpr.fraction]
  exact CFValue.zero_add s.cfValue

theorem TwistExpr.mulBottom_infinity_fraction (s : CrossingSign) :
    (TwistExpr.mulBottom .infinity s).fraction = s.cfValue.inv := by
  simp [TwistExpr.fraction, CFValue.inv_inf]
  rw [show (0 : CFValue) = CFValue.ofRat 0 from rfl, CFValue.zero_add]

theorem coloring_mul_invert_right_unit (T : TangleDiagram) (s : CrossingSign) :
    ColoringIsotopy (T.mul (crossingTangle s))
      (T.mul (crossingTangle s).invert) := by
  have hglue :
      (crossingTangle s).NW = (crossingTangle s).NE →
        (crossingTangle s).invert.NW = (crossingTangle s).invert.NE := by
    intro h
    exact (crossingTangle_NW_ne_NE s h).elim
  exact ColoringIsotopy.mul_right (ColoringIsotopy.invert_unit s) hglue

theorem coloring_add_invert_right_unit (T : TangleDiagram) (s : CrossingSign) :
    ColoringIsotopy (T.add (crossingTangle s))
      (T.add (crossingTangle s).invert) := by
  have hglue :
      (crossingTangle s).NW = (crossingTangle s).SW →
        (crossingTangle s).invert.NW = (crossingTangle s).invert.SW := by
    intro h
    exact (crossingTangle_NW_ne_SW s h).elim
  exact ColoringIsotopy.add_right (ColoringIsotopy.invert_unit s) hglue

/-- Planar rename swapping arcs `0` and `1`: `[∞]ⁱ` to `[0]` reversed. -/
theorem planar_zero_infinity_invert :
    PlanarIsotopy TangleDiagram.zero TangleDiagram.infinity.invert := by
  refine ⟨swap01, swap01_injective, rfl, rfl, rfl, rfl, [], pairRel_nil, List.Perm.nil⟩

/-- Fresh coloring of `([0]+[±1])ⁱ` and of `[±1]ⁱ * [0]ⁱ`. The product is
    `[±1]ⁱ * [∞]`, which is the same PD-code as `[±1]ⁱ`. -/
theorem coloring_invert_add_zero_unit (s : CrossingSign) :
    ∃ colL colR,
      ((TangleDiagram.zero.add (crossingTangle s)).invert).IsColored colL ∧
      (((crossingTangle s).invert.mul TangleDiagram.zero.invert)).IsColored
        colR ∧
      (ColorMatrix.of (TangleDiagram.zero.add (crossingTangle s)).invert
        colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).invert.mul TangleDiagram.zero.invert)
        colR).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.add (crossingTangle s)).invert
        colL).fraction =
        (ColorMatrix.of ((crossingTangle s).invert.mul
          TangleDiagram.zero.invert) colR).fraction := by
  let eL : TwistExpr := .addRight .zero s
  have hrbL : eL.rightBottom := trivial
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  have hdiag :
      eL.diagram = TangleDiagram.zero.add (crossingTangle s) := rfl
  have hcL' :
      (TangleDiagram.zero.add (crossingTangle s)).invert.IsColored colL := by
    simpa only [hdiag] using hcL
  have hmL' :
      (ColorMatrix.of (TangleDiagram.zero.add (crossingTangle s)).invert
        colL).NotMono := by
    simpa only [hdiag] using hmL
  have hfL' :
      (ColorMatrix.of (TangleDiagram.zero.add (crossingTangle s)).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hdiag] using hfL
  have hR :
      (crossingTangle s).invert.mul TangleDiagram.zero.invert =
        (crossingTangle s).invert := by
    rw [invert_zero, mul_infinity_eq]
  let eU : TwistExpr := .ofCrossingSign s
  have hrbU : eU.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  let col0 := eU.colorFrom 0 1
  have hc0 := eU.colorFrom_isColored hrbU 0 1
  have hm0 := eU.colorFrom_notMono hrbU
  have hf0 := eU.colorFrom_eq_fraction hrbU
  have hdiagU : eU.diagram = crossingTangle s :=
    TwistExpr.ofCrossingSign_diagram s
  have hstep : ColoringIsotopy (crossingTangle s) (crossingTangle s).invert :=
    ColoringIsotopy.invert_unit s
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep (by simpa only [hdiagU] using col0)
      (by simpa only [hdiagU] using hc0)
  have hmR0 : (ColorMatrix.of (crossingTangle s).invert colR).NotMono := by
    have hmU : (ColorMatrix.of (crossingTangle s) col0).NotMono := by
      simpa only [hdiagU] using hm0
    simpa only [hMat] using hmU
  refine ⟨colL, colR, hcL', ?_, hmL', ?_, ?_⟩
  · simpa only [hR] using hcR
  · simpa only [hR] using hmR0
  · have hfR :
        (ColorMatrix.of ((crossingTangle s).invert.mul TangleDiagram.zero.invert)
          colR).fraction = eU.fraction := by
      simpa only [hR] using (hfrac.trans (by simpa only [hdiagU] using hf0))
    rw [hfL', hfR, TwistExpr.addRight_zero_fraction,
      TwistExpr.ofCrossingSign_fraction, CrossingSign.cfValue_inv]

/-- Fresh coloring of `([±1]+[0])ⁱ` and of `[0]ⁱ * [±1]ⁱ`. Glue of `[∞]`
    under `[∞]*[±1]` has distinct ports (not a kink). -/
theorem coloring_invert_add_unit_zero (s : CrossingSign) :
    ∃ colL colR,
      (((crossingTangle s).add TangleDiagram.zero).invert).IsColored colL ∧
      ((TangleDiagram.zero.invert.mul (crossingTangle s).invert)).IsColored
        colR ∧
      (ColorMatrix.of ((crossingTangle s).add TangleDiagram.zero).invert
        colL).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.invert.mul (crossingTangle s).invert)
        colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).add TangleDiagram.zero).invert
        colL).fraction =
        (ColorMatrix.of (TangleDiagram.zero.invert.mul
          (crossingTangle s).invert) colR).fraction := by
  have hL :
      (crossingTangle s).add TangleDiagram.zero = crossingTangle s :=
    add_zero_eq _
  let eL : TwistExpr := .ofCrossingSign s
  have hrbL : eL.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  have hdiag : eL.diagram = crossingTangle s :=
    TwistExpr.ofCrossingSign_diagram s
  have hcL' :
      ((crossingTangle s).add TangleDiagram.zero).invert.IsColored colL := by
    simpa only [hL, hdiag] using hcL
  have hmL' :
      (ColorMatrix.of ((crossingTangle s).add TangleDiagram.zero).invert
        colL).NotMono := by
    simpa only [hL, hdiag] using hmL
  have hfL' :
      (ColorMatrix.of ((crossingTangle s).add TangleDiagram.zero).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hL, hdiag] using hfL
  let eR : TwistExpr := .mulBottom .infinity s
  have hrbR : eR.rightBottom := trivial
  have hdiagR :
      eR.diagram = TangleDiagram.infinity.mul (crossingTangle s) := rfl
  let col0 := eR.colorFrom 0 1
  have hc0 := eR.colorFrom_isColored hrbR 0 1
  have hm0 := eR.colorFrom_notMono hrbR
  have hf0 := eR.colorFrom_eq_fraction hrbR
  have hstep : ColoringIsotopy eR.diagram
      (TangleDiagram.zero.invert.mul (crossingTangle s).invert) := by
    simpa only [hdiagR, invert_zero] using
      coloring_mul_invert_right_unit TangleDiagram.infinity s
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep col0 hc0
  have hmR : (ColorMatrix.of
      (TangleDiagram.zero.invert.mul (crossingTangle s).invert) colR).NotMono := by
    simpa only [hMat] using hm0
  refine ⟨colL, colR, hcL', hcR, hmL', hmR, ?_⟩
  have hfR :
      (ColorMatrix.of (TangleDiagram.zero.invert.mul (crossingTangle s).invert)
        colR).fraction = eR.fraction :=
    hfrac.trans hf0
  rw [hfL', hfR, TwistExpr.ofCrossingSign_fraction,
    TwistExpr.mulBottom_infinity_fraction]

/-- Fresh coloring of `([∞]*[±1])ⁱ` and of `[∞]ⁱ + [±1]ⁱ`. Glue ports of
    `[∞]*[±1]` are distinct; `[∞]+[±1]` is not used. -/
theorem coloring_invert_mul_infinity_unit (s : CrossingSign) :
    ∃ colL colR,
      ((TangleDiagram.infinity.mul (crossingTangle s)).invert).IsColored colL ∧
      ((TangleDiagram.infinity.invert.add (crossingTangle s).invert)).IsColored
        colR ∧
      (ColorMatrix.of (TangleDiagram.infinity.mul (crossingTangle s)).invert
        colL).NotMono ∧
      (ColorMatrix.of (TangleDiagram.infinity.invert.add
        (crossingTangle s).invert) colR).NotMono ∧
      (ColorMatrix.of (TangleDiagram.infinity.mul (crossingTangle s)).invert
        colL).fraction =
        (ColorMatrix.of (TangleDiagram.infinity.invert.add
          (crossingTangle s).invert) colR).fraction := by
  let eL : TwistExpr := .mulBottom .infinity s
  have hrbL : eL.rightBottom := trivial
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  have hdiag :
      eL.diagram = TangleDiagram.infinity.mul (crossingTangle s) := rfl
  have hcL' :
      (TangleDiagram.infinity.mul (crossingTangle s)).invert.IsColored colL := by
    simpa only [hdiag] using hcL
  have hmL' :
      (ColorMatrix.of (TangleDiagram.infinity.mul (crossingTangle s)).invert
        colL).NotMono := by
    simpa only [hdiag] using hmL
  have hfL' :
      (ColorMatrix.of (TangleDiagram.infinity.mul (crossingTangle s)).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hdiag] using hfL
  let eR : TwistExpr := .addRight .zero s
  have hrbR : eR.rightBottom := trivial
  have hdiagR :
      eR.diagram = TangleDiagram.zero.add (crossingTangle s) := rfl
  let col0 := eR.colorFrom 0 1
  have hc0 := eR.colorFrom_isColored hrbR 0 1
  have hm0 := eR.colorFrom_notMono hrbR
  have hf0 := eR.colorFrom_eq_fraction hrbR
  have hstep : ColoringIsotopy eR.diagram
      (TangleDiagram.infinity.invert.add (crossingTangle s).invert) := by
    simpa only [hdiagR] using
      (ColoringIsotopy.trans
        (ColoringIsotopy.add_left (S := crossingTangle s)
          (.isotopy planar_zero_infinity_invert))
        (coloring_add_invert_right_unit TangleDiagram.infinity.invert s))
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep col0 hc0
  have hmR : (ColorMatrix.of
      (TangleDiagram.infinity.invert.add (crossingTangle s).invert)
        colR).NotMono := by
    simpa only [hMat] using hm0
  refine ⟨colL, colR, hcL', hcR, hmL', hmR, ?_⟩
  have hfR :
      (ColorMatrix.of (TangleDiagram.infinity.invert.add
        (crossingTangle s).invert) colR).fraction = eR.fraction :=
    hfrac.trans hf0
  rw [hfL', hfR, TwistExpr.mulBottom_infinity_fraction,
    TwistExpr.addRight_zero_fraction, CFValue.inv_inv]

/-- Fresh coloring of `([±1]*[∞])ⁱ` and of `[±1]ⁱ + [∞]ⁱ`. The product is
    the same PD-code as `[±1]`. -/
theorem coloring_invert_mul_unit_infinity (s : CrossingSign) :
    ∃ colL colR,
      (((crossingTangle s).mul TangleDiagram.infinity).invert).IsColored colL ∧
      (((crossingTangle s).invert.add TangleDiagram.infinity.invert)).IsColored
        colR ∧
      (ColorMatrix.of ((crossingTangle s).mul TangleDiagram.infinity).invert
        colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).invert.add
        TangleDiagram.infinity.invert) colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).mul TangleDiagram.infinity).invert
        colL).fraction =
        (ColorMatrix.of ((crossingTangle s).invert.add
          TangleDiagram.infinity.invert) colR).fraction := by
  have hL :
      (crossingTangle s).mul TangleDiagram.infinity = crossingTangle s :=
    mul_infinity_eq _
  let eL : TwistExpr := .ofCrossingSign s
  have hrbL : eL.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  have hdiag : eL.diagram = crossingTangle s :=
    TwistExpr.ofCrossingSign_diagram s
  have hcL' :
      ((crossingTangle s).mul TangleDiagram.infinity).invert.IsColored colL := by
    simpa only [hL, hdiag] using hcL
  have hmL' :
      (ColorMatrix.of ((crossingTangle s).mul TangleDiagram.infinity).invert
        colL).NotMono := by
    simpa only [hL, hdiag] using hmL
  have hfL' :
      (ColorMatrix.of ((crossingTangle s).mul TangleDiagram.infinity).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hL, hdiag] using hfL
  let eU : TwistExpr := .ofCrossingSign s
  have hrbU : eU.rightBottom := TwistExpr.ofCrossingSign_rightBottom s
  let col0 := eU.colorFrom 0 1
  have hc0 := eU.colorFrom_isColored hrbU 0 1
  have hm0 := eU.colorFrom_notMono hrbU
  have hf0 := eU.colorFrom_eq_fraction hrbU
  have hglue0 :
      TangleDiagram.zero.NW = TangleDiagram.zero.SW →
        TangleDiagram.infinity.invert.NW = TangleDiagram.infinity.invert.SW := by
    intro h
    have h01 : TangleDiagram.zero.NW ≠ TangleDiagram.zero.SW := by decide
    exact (h01 h).elim
  have hdiagU : eU.diagram = crossingTangle s :=
    TwistExpr.ofCrossingSign_diagram s
  have hstep : ColoringIsotopy eU.diagram
      ((crossingTangle s).invert.add TangleDiagram.infinity.invert) := by
    simpa only [hdiagU] using
      (ColoringIsotopy.trans (ColoringIsotopy.invert_unit s)
        (ColoringIsotopy.trans
          (ColoringIsotopy.add_zero_symm (crossingTangle s).invert)
          (ColoringIsotopy.add_right (.isotopy planar_zero_infinity_invert)
            hglue0)))
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy hstep col0 hc0
  have hmR : (ColorMatrix.of
      ((crossingTangle s).invert.add TangleDiagram.infinity.invert)
        colR).NotMono := by
    simpa only [hMat] using hm0
  refine ⟨colL, colR, hcL', hcR, hmL', hmR, ?_⟩
  have hfR :
      (ColorMatrix.of ((crossingTangle s).invert.add
        TangleDiagram.infinity.invert) colR).fraction = eU.fraction :=
    hfrac.trans hf0
  rw [hfL', hfR, TwistExpr.ofCrossingSign_fraction, CrossingSign.cfValue_inv]

theorem coloring_invert_add_zero_one :
    ∃ colL colR,
      ((TangleDiagram.zero.add RationalTangles.one).invert).IsColored colL ∧
      (RationalTangles.one.invert.mul TangleDiagram.zero.invert).IsColored
        colR ∧
      (ColorMatrix.of (TangleDiagram.zero.add RationalTangles.one).invert
        colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.invert.mul TangleDiagram.zero.invert)
        colR).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.add RationalTangles.one).invert
        colL).fraction =
        (ColorMatrix.of (RationalTangles.one.invert.mul
          TangleDiagram.zero.invert) colR).fraction := by
  simpa only [crossingTangle] using coloring_invert_add_zero_unit .pos

theorem coloring_invert_add_one_zero :
    ∃ colL colR,
      ((RationalTangles.one.add TangleDiagram.zero).invert).IsColored colL ∧
      (TangleDiagram.zero.invert.mul RationalTangles.one.invert).IsColored
        colR ∧
      (ColorMatrix.of (RationalTangles.one.add TangleDiagram.zero).invert
        colL).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.invert.mul RationalTangles.one.invert)
        colR).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add TangleDiagram.zero).invert
        colL).fraction =
        (ColorMatrix.of (TangleDiagram.zero.invert.mul
          RationalTangles.one.invert) colR).fraction := by
  simpa only [crossingTangle] using coloring_invert_add_unit_zero .pos

/-- Fresh colorings of `([+1]+[+1])ⁱ` and of the right-and-bottom vertical
    chain `[∞]*[+1]*[+1]`, both with fraction `1/2`. Not a
    `ColoringIsotopy` between the diagrams. -/
theorem coloring_invert_one_add_one_eq_vertical :
    ∃ colL colR,
      ((RationalTangles.one.add RationalTangles.one).invert).IsColored colL ∧
      ((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one).IsColored colR ∧
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one).invert
        colL).NotMono ∧
      (ColorMatrix.of ((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one) colR).NotMono ∧
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one).invert
        colL).fraction =
        (ColorMatrix.of ((TangleDiagram.infinity.mul RationalTangles.one).mul
          RationalTangles.one) colR).fraction := by
  let eL : TwistExpr := .addRight .one .pos
  have hrbL : eL.rightBottom := trivial
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  let eR : TwistExpr := .mulBottom (.mulBottom .infinity .pos) .pos
  have hrbR : eR.rightBottom := trivial
  let colR := eR.colorFrom 0 1
  have hcR := eR.colorFrom_isColored hrbR 0 1
  have hmR := eR.colorFrom_notMono hrbR
  have hfR := eR.colorFrom_eq_fraction hrbR
  refine ⟨colL, colR, hcL, hcR, hmL, hmR, ?_⟩
  have hL :
      eL.diagram = RationalTangles.one.add RationalTangles.one := rfl
  have hR :
      eR.diagram =
        (TangleDiagram.infinity.mul RationalTangles.one).mul
          RationalTangles.one := rfl
  have hfL' :
      (ColorMatrix.of (RationalTangles.one.add RationalTangles.one).invert
        colL).fraction = eL.fraction.inv := by
    simpa only [hL] using hfL
  have hfR' :
      (ColorMatrix.of ((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one) colR).fraction = eR.fraction := by
    simpa only [hR] using hfR
  rw [hfL', hfR']
  simp [eL, eR, TwistExpr.fraction, CrossingSign.cfValue, CFValue.inv_inf]
  rw [show (0 : CFValue) = CFValue.ofRat 0 from rfl, CFValue.zero_add]

/-- Fresh colorings of `([+1]+[+1]+[+1])ⁱ` and of `[∞]*[+1]*[+1]*[+1]`,
    both with fraction `1/3`. -/
theorem coloring_invert_one_add_one_add_one_eq_vertical :
    ∃ colL colR,
      (((RationalTangles.one.add RationalTangles.one).add
        RationalTangles.one).invert).IsColored colL ∧
      (((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one).mul RationalTangles.one).IsColored colR ∧
      (ColorMatrix.of ((RationalTangles.one.add RationalTangles.one).add
        RationalTangles.one).invert colL).NotMono ∧
      (ColorMatrix.of (((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one).mul RationalTangles.one) colR).NotMono ∧
      (ColorMatrix.of ((RationalTangles.one.add RationalTangles.one).add
        RationalTangles.one).invert colL).fraction =
        (ColorMatrix.of (((TangleDiagram.infinity.mul RationalTangles.one).mul
          RationalTangles.one).mul RationalTangles.one) colR).fraction := by
  let eL : TwistExpr := .addRight (.addRight .one .pos) .pos
  have hrbL : eL.rightBottom := trivial
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_rightBottom_colorFrom eL hrbL
  let eR : TwistExpr :=
    .mulBottom (.mulBottom (.mulBottom .infinity .pos) .pos) .pos
  have hrbR : eR.rightBottom := trivial
  let colR := eR.colorFrom 0 1
  have hcR := eR.colorFrom_isColored hrbR 0 1
  have hmR := eR.colorFrom_notMono hrbR
  have hfR := eR.colorFrom_eq_fraction hrbR
  refine ⟨colL, colR, hcL, hcR, hmL, hmR, ?_⟩
  have hfL' :
      (ColorMatrix.of ((RationalTangles.one.add RationalTangles.one).add
        RationalTangles.one).invert colL).fraction = eL.fraction.inv := hfL
  have hfR' :
      (ColorMatrix.of (((TangleDiagram.infinity.mul RationalTangles.one).mul
        RationalTangles.one).mul RationalTangles.one) colR).fraction =
        eR.fraction := hfR
  rw [hfL', hfR']
  simp [eL, eR, TwistExpr.fraction, CrossingSign.cfValue, CFValue.inv_inf]
  rw [show (0 : CFValue) = CFValue.ofRat 0 from rfl, CFValue.zero_add]

end RationalTangles
