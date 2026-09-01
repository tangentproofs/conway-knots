/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColoringIsotopy
import RationalTangles.FlippingLemma

/-!
# Mirror and invert of standard-form colorings

Gluing `colorMirrorUnit` (matrix `hswap`) of a unit onto an `hswap`
coloring of the left/top summand does not match the glue identifications
of `add`/`mul`, so the composite matrix is not `hswap`. Instead, double
mirror is planar isotopy (`Crossing.rotate180`), so `e.diagram.mirror` is
`ColoringIsotopy` to `e.mirror.diagram`, and uniqueness of `f` on standard
form gives `f(-T) = -f(T)`.
-/

namespace RationalTangles

theorem coloring_crossingTangle_mirror (s : CrossingSign) :
    ColoringIsotopy (crossingTangle s).mirror (crossingTangle s.flip) := by
  cases s with
  | pos =>
    simp [crossingTangle, CrossingSign.flip, negOne]
    exact .refl _
  | neg =>
    simp [crossingTangle, CrossingSign.flip, negOne]
    exact .isotopy (planar_mirror_mirror one)

theorem coloring_mirror_diagram (e : StandardExpr) :
    ColoringIsotopy e.diagram.mirror e.mirror.diagram := by
  induction e with
  | zero =>
    simp [StandardExpr.diagram, StandardExpr.mirror]
    exact .refl _
  | infinity =>
    simp [StandardExpr.diagram, StandardExpr.mirror]
    exact .refl _
  | addRight e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).SW := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).SW :=
        crossingTangle_NW_ne_SW s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := (crossingTangle s).mirror) ih)
        (.add_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).NE := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).NE :=
        crossingTangle_NW_ne_NE s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := (crossingTangle s).mirror) ih)
        (.mul_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_mul] using hstep

theorem coloring_crossingTangle_mirror_rev (s : CrossingSign) :
    ColoringIsotopy (crossingTangle s.flip) (crossingTangle s).mirror := by
  cases s with
  | pos =>
    simp [crossingTangle, CrossingSign.flip, negOne]
    exact .refl _
  | neg =>
    simp [crossingTangle, CrossingSign.flip, negOne]
    exact .isotopy (planar_mirror_mirror_rev one)

theorem coloring_mirror_diagram_rev (e : StandardExpr) :
    ColoringIsotopy e.mirror.diagram e.diagram.mirror := by
  induction e with
  | zero =>
    simp [StandardExpr.diagram, StandardExpr.mirror]
    exact .refl _
  | infinity =>
    simp [StandardExpr.diagram, StandardExpr.mirror]
    exact .refl _
  | addRight e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).SW →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).SW :=
        crossingTangle_NW_ne_SW s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := crossingTangle s.flip) ih)
        (.add_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    simp only [StandardExpr.diagram, StandardExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).NE →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).NE :=
        crossingTangle_NW_ne_NE s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := crossingTangle s.flip) ih)
        (.mul_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_mul] using hstep

theorem one_eq_ofInt_one : (1 : CFValue) = CFValue.ofInt 1 := rfl

theorem StandardExpr.fraction_mirror (e : StandardExpr) :
    e.mirror.fraction = e.fraction.neg := by
  induction e with
  | zero =>
    simp [StandardExpr.mirror, StandardExpr.fraction]
    rfl
  | infinity =>
    simp [StandardExpr.mirror, StandardExpr.fraction]
  | addRight e s ih =>
    cases s with
    | pos =>
      simp [StandardExpr.mirror, StandardExpr.fraction, CrossingSign.flip, ih,
        CFValue.neg_add, one_eq_ofInt_one]
    | neg =>
      simp [StandardExpr.mirror, StandardExpr.fraction, CrossingSign.flip, ih,
        CFValue.neg_add, one_eq_ofInt_one]
  | mulBottom e s ih =>
    cases s with
    | pos =>
      simp [StandardExpr.mirror, StandardExpr.fraction, CrossingSign.flip, ih,
        CFValue.neg_inv, CFValue.neg_add, one_eq_ofInt_one]
    | neg =>
      simp [StandardExpr.mirror, StandardExpr.fraction, CrossingSign.flip, ih,
        CFValue.neg_inv, CFValue.neg_add, one_eq_ofInt_one]

/-- On a standard-form diagram, a non-monochrome coloring of the mirror has
    coloring fraction `-f(T)`. -/
theorem coloring_mirror_standard (e : StandardExpr) (col col' : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hc' : e.diagram.mirror.IsColored col')
    (hm' : (ColorMatrix.of e.diagram.mirror col').NotMono) :
    (ColorMatrix.of e.diagram.mirror col').fraction =
      (ColorMatrix.of e.diagram col).fraction.neg := by
  obtain ⟨colM, hcM, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram e) col' hc'
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono := by
    simpa [hMat] using hm'
  have hfT := standard_fraction_any_coloring e col hc hm
  have hfM := standard_fraction_any_coloring e.mirror colM hcM hmM
  rw [hfrac.symm, hfM, StandardExpr.fraction_mirror, hfT]

/-- Paper Theorem 4(4): the color matrix of `T.rotate` is the rotation of
    `M(T)`, so `f(Tʳ) = -1/f(T)` on a non-monochrome standard coloring.
    (The paper writes this as `f(-1/T)`.) Same coloring: rotation only
    cycles endpoints. -/
theorem coloring_invert_standard (e : StandardExpr) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram.rotate col).fraction =
      (ColorMatrix.of e.diagram col).fraction.negInv :=
  coloring_fraction_rotate e.diagram col (standard_coloring_diagonal e col hc) hm

end RationalTangles
