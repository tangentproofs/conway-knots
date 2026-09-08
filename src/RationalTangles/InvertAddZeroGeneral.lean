/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColorFractionUnique

/-!
# Invert-add with a `[0]` summand at the standard value

`HasColoringFraction.invert_add_right_zero` / `invert_add_left_zero`
already transport a coloring of `T.invert` across a `[0]` summand for an
*arbitrary* diagram `T`, with no port or `DiagonalSum` hypotheses. This
file records the value-level consequence on `slideReady` twists: every
non-monochrome coloring of `Tⁱ` has fraction `F⁻¹`
(`coloring_invert_inv_any_slideReady`), so both sides of invert-add with
a `[0]` summand carry `e.toStandard.fraction.inv`, for arbitrary input
colorings and by existence via `colorFrom`. This is the `[0]`-summand
piece of Theorem 4.7 (all-rational agreement) at the standard value.

Residual gap (not claimed): a variant taking `HasColoringFraction T v`
— a coloring of `T` rather than of `T.invert` — would need transport of
an integral coloring across a single `Crossing.switch` (PD-mirror /
`invert_cong`). Only units (`coloring_invert_unit`), double mirrors
(`IsColored_mirror_mirror`, i.e. `rotate180`), and the `slideReady`
algebraic-mirror comparisons transport across `switch`; the general
single-`switch` reuse of a coloring is false, so this variant is not
proved here.
-/

namespace RationalTangles

/-- Right `[0]` invert-add on a `slideReady` twist at the standard value:
    `(T+[0])ⁱ` carries `F⁻¹`, for every non-monochrome coloring of `Tⁱ`. -/
theorem HasColoringFraction.invert_add_right_zero_any_slideReady
    (e : TwistExpr) (hok : e.slideReady) (colI : Nat → Int)
    (hcI : e.diagram.invert.IsColored colI)
    (hmI : (ColorMatrix.of e.diagram.invert colI).NotMono) :
    HasColoringFraction (e.diagram.add TangleDiagram.zero).invert
      e.toStandard.fraction.inv := by
  have hf := coloring_invert_inv_any_slideReady e hok colI hcI hmI
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    (HasColoringFraction.invert_add_right_zero ⟨colI, hcI, hmI, hf⟩).1
  exact ⟨colL, hcL, hmL, hfL⟩

/-- Left `[0]` invert-add on a `slideReady` twist at the standard value:
    `([0]+T)ⁱ` carries `F⁻¹`, for every non-monochrome coloring of `Tⁱ`. -/
theorem HasColoringFraction.invert_add_left_zero_any_slideReady
    (e : TwistExpr) (hok : e.slideReady) (colI : Nat → Int)
    (hcI : e.diagram.invert.IsColored colI)
    (hmI : (ColorMatrix.of e.diagram.invert colI).NotMono) :
    HasColoringFraction (TangleDiagram.zero.add e.diagram).invert
      e.toStandard.fraction.inv := by
  have hf := coloring_invert_inv_any_slideReady e hok colI hcI hmI
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    (HasColoringFraction.invert_add_left_zero ⟨colI, hcI, hmI, hf⟩).1
  exact ⟨colL, hcL, hmL, hfL⟩

/-- Existence version on the right: `(T+[0])ⁱ` carries `F⁻¹`. -/
theorem HasColoringFraction.invert_add_right_zero_slideReady_exists
    (e : TwistExpr) (hok : e.slideReady) :
    HasColoringFraction (e.diagram.add TangleDiagram.zero).invert
      e.toStandard.fraction.inv := by
  obtain ⟨colI, hcI, hmI, _⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  exact HasColoringFraction.invert_add_right_zero_any_slideReady e hok
    colI hcI hmI

/-- Existence version on the left: `([0]+T)ⁱ` carries `F⁻¹`. -/
theorem HasColoringFraction.invert_add_left_zero_slideReady_exists
    (e : TwistExpr) (hok : e.slideReady) :
    HasColoringFraction (TangleDiagram.zero.add e.diagram).invert
      e.toStandard.fraction.inv := by
  obtain ⟨colI, hcI, hmI, _⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  exact HasColoringFraction.invert_add_left_zero_any_slideReady e hok
    colI hcI hmI

end RationalTangles
