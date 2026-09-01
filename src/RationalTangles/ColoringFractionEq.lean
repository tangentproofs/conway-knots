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

end RationalTangles
