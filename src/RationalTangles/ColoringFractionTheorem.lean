/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/

import RationalTangles.ColorFraction
import RationalTangles.ColorFractionUnique
import RationalTangles.DiagonalSumGeneral

/-!
# Coloring fraction, parts of Theorem 4

Paper-numbered wrappers around the proved Theorem 4 fragments
(Kauffman–Lambropoulou §5, Theorem 4): each statement below is one part of
the theorem, proved by the lemma named in its proof. The invariance assembly
(part 2) and the all-rational agreement (part 7) are not claimed here; see
the blueprint node for the exact boundary.
-/

namespace RationalTangles

/-- Theorem 4.1: every coloring of a standard-form diagram satisfies the
    diagonal sum rule. -/
theorem theorem4_diagonal_sum (e : StandardExpr) (col : Nat → Int)
    (h : e.diagram.IsColored col) :
    (ColorMatrix.of e.diagram col).DiagonalSum :=
  standard_coloring_diagonal e col h

/-- Theorem 4.1 (general): every coloring of a diagram coloring-isotopic
    to a `slideReady` twist satisfies the diagonal sum rule. The
    reverse direction and unrestricted `Isotopic` transport are not
    claimed; see `DiagonalSumGeneral` for the exact boundary. -/
theorem theorem4_diagonal_coloringIsotopy {D : TangleDiagram}
    (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy D e.diagram) (col : Nat → Int)
    (hc : D.IsColored col) :
    (ColorMatrix.of D col).DiagonalSum :=
  diagonal_of_ColoringIsotopy_slideReady e hok h col hc

/-- Theorem 4.3: the coloring fraction adds across a horizontal sum. -/
theorem theorem4_additivity (T S : TangleDiagram) (col : Nat → Int)
    (hSW : S.NW ≠ S.SW)
    (hS : (ColorMatrix.of S (colorAddRight T S col)).DiagonalSum) :
    (ColorMatrix.of T col).fraction.add
        (ColorMatrix.of S (colorAddRight T S col)).fraction =
      (ColorMatrix.of (T.add S) col).fraction :=
  coloring_fraction_add T S col hSW hS

/-- Theorem 4.4: on a `slideReady` twist, every non-monochrome coloring of
    `-1/T` (mirror-then-invert, i.e. `T.mirror.invert`) has fraction `-1/F`.
    By `TangleDiagram.mirror_invert` this is the PD-code of `-(T.invert)`. -/
theorem theorem4_neg_inverse (e : TwistExpr)
    (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.mirror.invert.IsColored col)
    (hm : (ColorMatrix.of e.diagram.mirror.invert col).NotMono) :
    (ColorMatrix.of e.diagram.mirror.invert col).fraction =
      e.toStandard.fraction.negInv :=
  coloring_mirror_invert_any_eq_negInv_F_slideReady e hok col hc hm

/-- Theorem 4.5: on a `slideReady` twist, every non-monochrome coloring of
    the PD-mirror `-T` has fraction `-F`. -/
theorem theorem4_mirror_negation (e : TwistExpr)
    (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.mirror.IsColored col)
    (hm : (ColorMatrix.of e.diagram.mirror col).NotMono) :
    (ColorMatrix.of e.diagram.mirror col).fraction =
      e.toStandard.fraction.neg :=
  coloring_mirror_any_eq_neg_F_slideReady e hok col hc hm

/-- Theorem 4.6: on a `slideReady` twist, the inverse `1/T` carries `1/F`.
    This is the invert half of part 4 without the mirror. -/
theorem theorem4_inverse (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction e.diagram.invert e.toStandard.fraction.inv :=
  HasColoringFraction.invert_slideReady e hok

/-- Theorem 4.7 (all rational, coloring-ready neighborhood): on any
    diagram coloring-isotopic to a `slideReady` twist, every
    non-monochrome integral coloring has fraction equal to the
    arithmetical fraction of the expression. -/
theorem theorem4_all_rational_agreement {D : TangleDiagram}
    (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy D e.diagram) (col : Nat → Int)
    (hc : D.IsColored col)
    (hm : (ColorMatrix.of D col).NotMono) :
    (ColorMatrix.of D col).fraction = e.toStandard.fraction :=
  coloring_fraction_agreement_any_isotopy e hok h col hc hm

/-- Theorem 4.7 (standard form): on a standard-form diagram, every
    non-monochrome integral coloring has fraction equal to the arithmetical
    fraction of the expression. -/
theorem theorem4_standard_agreement (e : StandardExpr) (col : Nat → Int)
    (h : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.fraction :=
  standard_fraction_any_coloring e col h hm

/-- Theorem 4.7 (existence): a standard-form diagram admits a non-monochrome
    integral coloring whose fraction is the arithmetical fraction. -/
theorem theorem4_standard_coloring_exists (e : StandardExpr) :
    ∃ col, e.diagram.IsColored col ∧
      (ColorMatrix.of e.diagram col).DiagonalSum ∧
      (ColorMatrix.of e.diagram col).NotMono ∧
      (ColorMatrix.of e.diagram col).fraction = e.fraction :=
  standard_coloring_eq_fraction e

/-- Theorem 4.2 (uniqueness on standard forms): the coloring fraction of a
    fixed standard-form diagram does not depend on the choice of
    non-monochrome integral coloring. -/
theorem theorem4_standard_uniqueness (e : StandardExpr) (col col' : Nat → Int)
    (h : e.diagram.IsColored col) (h' : e.diagram.IsColored col')
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hm' : (ColorMatrix.of e.diagram col').NotMono) :
    (ColorMatrix.of e.diagram col).fraction =
      (ColorMatrix.of e.diagram col').fraction :=
  standard_form_fraction_unique e col col' h h' hm hm'

end RationalTangles
