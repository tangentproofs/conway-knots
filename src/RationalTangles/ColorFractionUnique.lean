/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColoringFractionEq

/-!
# Uniqueness of the coloring fraction on a slideReady diagram

Any two non-monochrome integral colorings of a `slideReady` twist-form
diagram have the same coloring fraction `f`, because each equals
`e.toStandard.fraction` (`coloring_fraction_eq_F`). Affine identities for
`colorFrom` are recorded here but uniqueness does not need them.
This is not Theorem 2: it is uniqueness on a fixed PD-code, not along
arbitrary `Isotopic` generators.
-/

namespace RationalTangles


theorem colorZero_affine (a c n k : Int) :
    colorZero (n * a + k) (n * c + k) = fun x => n * colorZero a c x + k := by
  funext x
  simp [colorZero]
  split_ifs <;> rfl

theorem colorInfinity_affine (a b n k : Int) :
    colorInfinity (n * a + k) (n * b + k) = fun x => n * colorInfinity a b x + k := by
  funext x
  simp [colorInfinity]
  split_ifs <;> rfl

theorem colorOne_affine (beta alpha n k : Int) :
    colorOne (n * beta + k) (n * alpha + k) = fun x => n * colorOne beta alpha x + k := by
  funext x
  simp [colorOne]
  split_ifs <;> ring

theorem colorNegOne_affine (beta alpha n k : Int) :
    colorNegOne (n * beta + k) (n * alpha + k) =
      fun x => n * colorNegOne beta alpha x + k := by
  funext x
  simp [colorNegOne]
  split_ifs <;> ring

theorem colorAddOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorAddOne T (fun a => n * col a + k) = fun a => n * colorAddOne T col a + k := by
  funext a
  simp [colorAddOne]
  split_ifs <;> ring

theorem colorAddNegOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorAddNegOne T (fun a => n * col a + k) =
      fun a => n * colorAddNegOne T col a + k := by
  funext a
  simp [colorAddNegOne]
  split_ifs <;> ring

theorem colorMulOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorMulOne T (fun a => n * col a + k) = fun a => n * colorMulOne T col a + k := by
  funext a
  simp [colorMulOne]
  split_ifs <;> ring

theorem colorMulNegOne_affine (T : TangleDiagram) (col : Nat → Int) (n k : Int) :
    colorMulNegOne T (fun a => n * col a + k) =
      fun a => n * colorMulNegOne T col a + k := by
  funext a
  simp [colorMulNegOne]
  split_ifs <;> ring

theorem colorGlueAdd_affine (T S : TangleDiagram) (colT colS : Nat → Int) (n k : Int) :
    colorGlueAdd T S (fun a => n * colT a + k) (fun a => n * colS a + k) =
      fun a => n * colorGlueAdd T S colT colS a + k := by
  funext a
  by_cases h : T.maxArc < a
  · simp [colorGlueAdd, h]
  · simp [colorGlueAdd, h]

theorem colorGlueMul_affine (T S : TangleDiagram) (colT colS : Nat → Int) (n k : Int) :
    colorGlueMul T S (fun a => n * colT a + k) (fun a => n * colS a + k) =
      fun a => n * colorGlueMul T S colT colS a + k := by
  funext a
  by_cases h : T.maxArc < a
  · simp [colorGlueMul, h]
  · simp [colorGlueMul, h]

theorem colorAddLeftOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorAddLeftOne S (fun a => n * colS a + k) =
      fun a => n * colorAddLeftOne S colS a + k := by
  have hU := colorOne_affine (colS S.SW) (colS S.NW) n k
  have hG := colorGlueAdd_affine one S (colorOne (colS S.SW) (colS S.NW)) colS n k
  simp [colorAddLeftOne]
  rw [hU, hG]

theorem colorAddLeftNegOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorAddLeftNegOne S (fun a => n * colS a + k) =
      fun a => n * colorAddLeftNegOne S colS a + k := by
  have hbeta : n * (2 * colS S.NW - colS S.SW) + k =
      2 * (n * colS S.NW + k) - (n * colS S.SW + k) := by ring
  have hU := colorNegOne_affine (colS S.NW) (2 * colS S.NW - colS S.SW) n k
  have hG := colorGlueAdd_affine negOne S
    (colorNegOne (colS S.NW) (2 * colS S.NW - colS S.SW)) colS n k
  simp [colorAddLeftNegOne]
  rw [← hbeta, hU]
  exact hG

theorem colorMulTopOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorMulTopOne S (fun a => n * colS a + k) =
      fun a => n * colorMulTopOne S colS a + k := by
  have halpha : n * (2 * colS S.NE - colS S.NW) + k =
      2 * (n * colS S.NE + k) - (n * colS S.NW + k) := by ring
  have hU := colorOne_affine (colS S.NE) (2 * colS S.NE - colS S.NW) n k
  have hG := colorGlueMul_affine one S
    (colorOne (colS S.NE) (2 * colS S.NE - colS S.NW)) colS n k
  simp [colorMulTopOne]
  rw [← halpha, hU]
  exact hG

theorem colorMulTopNegOne_affine (S : TangleDiagram) (colS : Nat → Int) (n k : Int) :
    colorMulTopNegOne S (fun a => n * colS a + k) =
      fun a => n * colorMulTopNegOne S colS a + k := by
  have halpha : n * (2 * colS S.NW - colS S.NE) + k =
      2 * (n * colS S.NW + k) - (n * colS S.NE + k) := by ring
  have hU := colorNegOne_affine (colS S.NW) (2 * colS S.NW - colS S.NE) n k
  have hG := colorGlueMul_affine negOne S
    (colorNegOne (colS S.NW) (2 * colS S.NW - colS S.NE)) colS n k
  simp [colorMulTopNegOne]
  rw [← halpha, hU]
  exact hG

theorem TwistExpr.colorFrom_affine (e : TwistExpr) (a c n k : Int) :
    e.colorFrom (n * a + k) (n * c + k) = fun x => n * e.colorFrom a c x + k := by
  induction e generalizing a c with
  | zero => exact colorZero_affine a c n k
  | infinity => exact colorInfinity_affine a c n k
  | one => exact colorOne_affine a c n k
  | negOne => exact colorNegOne_affine a c n k
  | addRight e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorAddOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorAddNegOne_affine]
  | mulBottom e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorMulOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorMulNegOne_affine]
  | addLeft e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorAddLeftOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorAddLeftNegOne_affine]
  | mulTop e s ih =>
    cases s with
    | pos => simp [TwistExpr.colorFrom, ih, colorMulTopOne_affine]
    | neg => simp [TwistExpr.colorFrom, ih, colorMulTopNegOne_affine]

theorem TwistExpr.colorFrom_eq_affine_01 (e : TwistExpr) (a c : Int) :
    e.colorFrom a c = fun x => (c - a) * e.colorFrom 0 1 x + a := by
  have h := e.colorFrom_affine 0 1 (c - a) a
  have ha : (c - a) * 0 + a = a := by ring
  have hc : (c - a) * 1 + a = c := by ring
  simpa [ha, hc] using h

theorem ColorMatrix.NotMono_of_eq_affine {M N : ColorMatrix} {p q : Int}
    (h : N = M.affine p q) (hN : N.NotMono) : p ≠ 0 := by
  intro hp
  subst h
  simp [ColorMatrix.affine, ColorMatrix.NotMono, hp] at hN

/-- Uniqueness of `f` on a `slideReady` diagram: every non-monochrome coloring
    has `f = e.toStandard.fraction`, so any two agree. `DiagonalSum` is
    discharged by `twist_coloring_diagonal_slideReady`. -/
theorem coloring_fraction_unique_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col col' : Nat → Int)
    (hc : e.diagram.IsColored col) (hc' : e.diagram.IsColored col')
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hm' : (ColorMatrix.of e.diagram col').NotMono) :
    (ColorMatrix.of e.diagram col).fraction =
      (ColorMatrix.of e.diagram col').fraction :=
  (coloring_fraction_eq_F e hok col hc
      (twist_coloring_diagonal_slideReady e hok col hc) hm).trans
    (coloring_fraction_eq_F e hok col' hc'
      (twist_coloring_diagonal_slideReady e hok col' hc') hm').symm


theorem ColorMatrix.of_colorFrom_affine_01 (e : TwistExpr) (a c : Int) :
    ColorMatrix.of e.diagram (e.colorFrom a c) =
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).affine (c - a) a := by
  have hfun := e.colorFrom_eq_affine_01 a c
  calc
    ColorMatrix.of e.diagram (e.colorFrom a c)
        = ColorMatrix.of e.diagram (fun x => (c - a) * e.colorFrom 0 1 x + a) := by
          simp [hfun]
    _ = (ColorMatrix.of e.diagram (e.colorFrom 0 1)).affine (c - a) a :=
          ColorMatrix.of_affineMap _ _ _ _

end RationalTangles
