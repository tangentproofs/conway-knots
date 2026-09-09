/-
Copyright (c) 2026 Michal Wallace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace
-/
import RationalTangles.ColorFractionUnique
import RationalTangles.CanonicalFormUnique

/-!
# Diagonal sum beyond twist diagrams (maximal proved fragment)

Theorem 4.1 of Kauffman–Lambropoulou says every color matrix satisfies the
diagonal sum rule. Proved unconditionally on standard forms
(`standard_coloring_diagonal`) and on `slideReady` twist diagrams
(`twist_coloring_diagonal_slideReady`).

This file extends that coverage to every diagram `ColoringIsotopy`-related
*to* a `slideReady` twist (hence to the `ReversibleColoringIsotopy`
neighborhood in both directions): transport preserves the color matrix
(`coloring_ColoringIsotopy`), and the target matrix satisfies the rule.
On a `slideReady` left-add / top-mul this discharges the `DiagonalSum`
hypothesis of the restricted Figure 5 slides, so those slides transport
*every* coloring (no `DiagonalSum` input needed by the caller), at both
the `SameEndpointColors` and the `HasColoringFraction` level.

This is not DiagonalSum on an arbitrary rational diagram. The residual gap
is exactly the documented blockers: transport along unrestricted
`Isotopic.flype_slide_add` / `Isotopic.flype_slide_mul` (no `DiagonalSum` /
port hypotheses), along the switch-based generators (`invert_cong`,
`invert_add`, `invert_mul`, `mirror_cong`), and `addLeft` / `mulTop`
twists without their port hypotheses (not `slideReady`). None of those
inductions is claimed here.
-/

namespace RationalTangles

/-- On a `slideReady` twist, every non-monochrome coloring has coloring
    fraction `F`, with the `DiagonalSum` hypothesis of
    `coloring_fraction_eq_F` discharged internally by
    `twist_coloring_diagonal_slideReady`. Callers no longer supply
    `DiagonalSum` by hand on this class. -/
theorem coloring_fraction_eq_F_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.toStandard.fraction :=
  coloring_fraction_eq_F e hok col hc
    (twist_coloring_diagonal_slideReady e hok col hc) hm

/-- Algebraic `F` is unchanged along `ColoringIsotopy` for `noMulTop`
    `slideReady` expressions, with every coloring hypothesis discharged
    by `colorFrom 0 1` (`toStandard_fraction_ColoringIsotopy_colorFrom`).
    Only the structural `noMulTop`/`slideReady` hypotheses remain. -/
theorem TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom
    {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.fraction = e₂.fraction :=
  (TwistExpr.fraction_eq_toStandard_of_noMulTop e₁ hn₁).trans
    ((TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom
        hok₁ hok₂ h).trans
      (TwistExpr.fraction_eq_toStandard_of_noMulTop e₂ hn₂).symm)

/-- Every integral coloring of a diagram `ColoringIsotopy`-related *to* a
    `slideReady` twist satisfies `DiagonalSum`. The reverse one-way
    direction (from the twist onto `D`) is not claimed. -/
theorem diagonal_of_ColoringIsotopy_slideReady
    {D : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy D e.diagram)
    (col : Nat → Int) (hc : D.IsColored col) :
    (ColorMatrix.of D col).DiagonalSum := by
  obtain ⟨col', hc', hs⟩ := coloring_ColoringIsotopy h col hc
  have hM := ColorMatrix.of_sameEndpoint hs
  have hd := twist_coloring_diagonal_slideReady e hok col' hc'
  rwa [hM] at hd

/-- Same identification when the path is a reversible coloring isotopy *to*
    the `slideReady` twist. -/
theorem diagonal_of_ReversibleColoringIsotopy_slideReady
    {D : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ReversibleColoringIsotopy D e.diagram)
    (col : Nat → Int) (hc : D.IsColored col) :
    (ColorMatrix.of D col).DiagonalSum :=
  diagonal_of_ColoringIsotopy_slideReady e hok h.toColoringIsotopy col hc

/-- Reverse of a reversible coloring isotopy from a `slideReady` twist:
    `DiagonalSum` on the source of the reverse path. -/
theorem diagonal_of_ReversibleColoringIsotopy_slideReady_symm
    {D : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ReversibleColoringIsotopy e.diagram D)
    (col : Nat → Int) (hc : D.IsColored col) :
    (ColorMatrix.of D col).DiagonalSum :=
  diagonal_of_ReversibleColoringIsotopy_slideReady e hok h.symm col hc

/-- Restricted Figure 5 slide for *every* coloring of a `slideReady`
    left-add: the `DiagonalSum` hypothesis of `coloring_flype_slide_add`
    is discharged by `twist_coloring_diagonal_slideReady` on the
    `addLeft` twist. Not unrestricted `Isotopic.flype_slide_add`. -/
theorem coloring_flype_slide_add_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) (s : CrossingSign)
    (hne : e.diagram.NW ≠ e.diagram.SW)
    (col : Nat → Int)
    (hc : ((crossingTangle s).add e.diagram).IsColored col) :
    ∃ col', (e.diagram.rot180.add (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).add e.diagram)
        (e.diagram.rot180.add (crossingTangle s)) col col' := by
  have hokL : (TwistExpr.addLeft e s).slideReady := ⟨hne, hok⟩
  have hcL : (TwistExpr.addLeft e s).diagram.IsColored col := by
    simpa [TwistExpr.diagram, add_eq_add] using hc
  have hd := twist_coloring_diagonal_slideReady _ hokL col hcL
  have hd' : (ColorMatrix.of ((crossingTangle s).add e.diagram) col).DiagonalSum := by
    simpa [TwistExpr.diagram, add_eq_add] using hd
  exact coloring_flype_slide_add s e.diagram col hc hne hd'

/-- Restricted Figure 5 slide for *every* coloring of a `slideReady`
    top-mul: the `DiagonalSum` hypothesis of `coloring_flype_slide_mul`
    is discharged by `twist_coloring_diagonal_slideReady` on the
    `mulTop` twist. Not unrestricted `Isotopic.flype_slide_mul`. -/
theorem coloring_flype_slide_mul_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) (s : CrossingSign)
    (hne : e.diagram.NW ≠ e.diagram.NE)
    (col : Nat → Int)
    (hc : ((crossingTangle s).mul e.diagram).IsColored col) :
    ∃ col', (e.diagram.rot180.mul (crossingTangle s)).IsColored col' ∧
      SameEndpointColors ((crossingTangle s).mul e.diagram)
        (e.diagram.rot180.mul (crossingTangle s)) col col' := by
  have hokL : (TwistExpr.mulTop e s).slideReady := ⟨hne, hok⟩
  have hcL : (TwistExpr.mulTop e s).diagram.IsColored col := by
    simpa [TwistExpr.diagram, mul_eq_mul] using hc
  have hd := twist_coloring_diagonal_slideReady _ hokL col hcL
  have hd' : (ColorMatrix.of ((crossingTangle s).mul e.diagram) col).DiagonalSum := by
    simpa [TwistExpr.diagram, mul_eq_mul] using hd
  exact coloring_flype_slide_mul s e.diagram col hc hne hd'

/-- `HasColoringFraction` transport across the restricted Figure 5 slide
    for *every* non-monochrome coloring of a `slideReady` left-add,
    carrying that coloring's own fraction value. This extends
    `HasColoringFraction.flype_slide_add` (whose `DiagonalSum` hypothesis
    is discharged here) from caller-supplied `DiagonalSum` to all
    colorings on this class. -/
theorem HasColoringFraction.flype_slide_add_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) (s : CrossingSign)
    (hne : e.diagram.NW ≠ e.diagram.SW)
    (col : Nat → Int)
    (hc : ((crossingTangle s).add e.diagram).IsColored col)
    (hm : (ColorMatrix.of ((crossingTangle s).add e.diagram) col).NotMono) :
    HasColoringFraction (e.diagram.rot180.add (crossingTangle s))
      (ColorMatrix.of ((crossingTangle s).add e.diagram) col).fraction := by
  have hokL : (TwistExpr.addLeft e s).slideReady := ⟨hne, hok⟩
  have hcL : (TwistExpr.addLeft e s).diagram.IsColored col := by
    simpa [TwistExpr.diagram, add_eq_add] using hc
  have hd := twist_coloring_diagonal_slideReady _ hokL col hcL
  have hd' : (ColorMatrix.of ((crossingTangle s).add e.diagram) col).DiagonalSum := by
    simpa [TwistExpr.diagram, add_eq_add] using hd
  exact HasColoringFraction.flype_slide_add col hc hne hd' hm rfl

/-- `HasColoringFraction` transport across the restricted Figure 5 slide
    for *every* non-monochrome coloring of a `slideReady` top-mul,
    carrying that coloring's own fraction value. This extends
    `HasColoringFraction.flype_slide_mul` the same way. -/
theorem HasColoringFraction.flype_slide_mul_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) (s : CrossingSign)
    (hne : e.diagram.NW ≠ e.diagram.NE)
    (col : Nat → Int)
    (hc : ((crossingTangle s).mul e.diagram).IsColored col)
    (hm : (ColorMatrix.of ((crossingTangle s).mul e.diagram) col).NotMono) :
    HasColoringFraction (e.diagram.rot180.mul (crossingTangle s))
      (ColorMatrix.of ((crossingTangle s).mul e.diagram) col).fraction := by
  have hokL : (TwistExpr.mulTop e s).slideReady := ⟨hne, hok⟩
  have hcL : (TwistExpr.mulTop e s).diagram.IsColored col := by
    simpa [TwistExpr.diagram, mul_eq_mul] using hc
  have hd := twist_coloring_diagonal_slideReady _ hokL col hcL
  have hd' : (ColorMatrix.of ((crossingTangle s).mul e.diagram) col).DiagonalSum := by
    simpa [TwistExpr.diagram, mul_eq_mul] using hd
  exact HasColoringFraction.flype_slide_mul col hc hne hd' hm rfl

/-! ## Sharpness: the port hypotheses are necessary

On the PD-degenerate families excluded from `slideReady` — `addLeft`
with `t.NW = t.SW` (the `[∞]` family) and `mulTop` with `t.NW = t.NE`
(the `[0]` family) — `DiagonalSum` can genuinely fail. Both witnesses
below use one coloring, valid on the single crossing, whose boundary
colors break the rule. So the port hypotheses are sharp, not merely
unproved.
-/

/-- Witness coloring for sharpness: valid on a single `[+1]` crossing
    (`0 = 2` overstrand, `5 + -5 = 2·0` under), but `NW ≠ SW` and
    `NW ≠ NE` colors. -/
def sharpCol : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 5 else if a = 2 then 0
  else if a = 3 then -5 else if a = 5 then 7 else 0

/-- Without `t.NW ≠ t.SW`, `DiagonalSum` can fail: on `[+1]+[∞]` the sum
    has `NE = SE` (both fresh), so the rule would demand `NW = SW`
    colors, which the crossing rule does not impose. -/
theorem not_diagonal_addLeft_infinity :
    ∃ col, ((crossingTangle CrossingSign.pos).add
      TangleDiagram.infinity).IsColored col ∧
      ¬ (ColorMatrix.of ((crossingTangle CrossingSign.pos).add
        TangleDiagram.infinity) col).DiagonalSum := by
  refine ⟨sharpCol, ?_, ?_⟩
  · intro C hC
    have hcs : ((crossingTangle CrossingSign.pos).add
          TangleDiagram.infinity).crossings =
        [⟨0, 1, 2, 3, CrossingSign.pos⟩] := by
      decide
    rw [hcs] at hC
    have hC' : C = ⟨0, 1, 2, 3, CrossingSign.pos⟩ :=
      List.mem_singleton.1 hC
    have hr : sharpCol 0 = sharpCol 2 ∧ sharpCol 1 + sharpCol 3 = 2 * sharpCol 0 :=
      ⟨rfl, rfl⟩
    rw [hC']
    exact hr
  · have hM : ColorMatrix.of ((crossingTangle CrossingSign.pos).add
        TangleDiagram.infinity) sharpCol = ⟨0, 7, -5, 7⟩ := by
      rfl
    rw [hM]
    have hF : ¬ (0 + 7 = 7 + -5) := by omega
    simp only [ColorMatrix.DiagonalSum]
    simp

/-- Without `t.NW ≠ t.NE`, `DiagonalSum` can fail: on `[+1]*[0]` the
    product has `SW = SE` (both fresh), so the rule would demand
    `NW = NE` colors, which the crossing rule does not impose. -/
theorem not_diagonal_mulTop_zero :
    ∃ col, ((crossingTangle CrossingSign.pos).mul
      TangleDiagram.zero).IsColored col ∧
      ¬ (ColorMatrix.of ((crossingTangle CrossingSign.pos).mul
        TangleDiagram.zero) col).DiagonalSum := by
  refine ⟨sharpCol, ?_, ?_⟩
  · intro C hC
    have hcs : ((crossingTangle CrossingSign.pos).mul
          TangleDiagram.zero).crossings =
        [⟨0, 1, 2, 3, CrossingSign.pos⟩] := by
      decide
    rw [hcs] at hC
    have hC' : C = ⟨0, 1, 2, 3, CrossingSign.pos⟩ :=
      List.mem_singleton.1 hC
    have hr : sharpCol 0 = sharpCol 2 ∧ sharpCol 1 + sharpCol 3 = 2 * sharpCol 0 :=
      ⟨rfl, rfl⟩
    rw [hC']
    exact hr
  · have hM : ColorMatrix.of ((crossingTangle CrossingSign.pos).mul
        TangleDiagram.zero) sharpCol = ⟨0, 5, 7, 7⟩ := by
      rfl
    rw [hM]
    have hF : ¬ (0 + 7 = 5 + 7) := by omega
    simp only [ColorMatrix.DiagonalSum]
    simp


/-! ## Sharpness: switch transport can fail -/

/-- No color-matrix transport across a single crossing switch: on
    [+1] the PD-mirror keeps the same ports but carries the switched
    crossing, so SameEndpointColors forces boundary colors that violate
    the switched rule. Hence mirror_cong (and any recoloring-based mirror
    transport) is false in general: the switch wall is sharp. -/
theorem not_coloring_mirror_transport :
    Exists (fun col => RationalTangles.one.IsColored col ∧
      Not (Exists (fun col2 => RationalTangles.one.mirror.IsColored col2 ∧
        SameEndpointColors RationalTangles.one
          RationalTangles.one.mirror col col2))) := by
  refine ⟨sharpCol, ?_, ?_⟩
  · intro C hC
    have hcs : RationalTangles.one.crossings =
        [⟨0, 1, 2, 3, CrossingSign.pos⟩] := rfl
    rw [hcs] at hC
    have hC0 : C = ⟨0, 1, 2, 3, CrossingSign.pos⟩ :=
      List.mem_singleton.1 hC
    have hr : sharpCol 0 = sharpCol 2 ∧ sharpCol 1 + sharpCol 3 = 2 * sharpCol 0 :=
      ⟨rfl, rfl⟩
    rw [hC0]
    exact hr
  · rintro ⟨col2, hc2, hs⟩
    obtain ⟨hNW, hNE, hSE, hSW⟩ := hs
    have pNE : RationalTangles.one.mirror.NE = 1 := rfl
    have qNE : RationalTangles.one.NE = 1 := rfl
    have s1 : sharpCol 1 = 5 := rfl
    have pSW : RationalTangles.one.mirror.SW = 3 := rfl
    have qSW : RationalTangles.one.SW = 3 := rfl
    have s3 : sharpCol 3 = -5 := rfl
    simp only [pNE, qNE, s1, pSW, qSW, s3] at hNE hSW
    have hcsM : RationalTangles.one.mirror.crossings =
        [⟨1, 2, 3, 0, CrossingSign.neg⟩] := rfl
    have hCmem : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
        RationalTangles.one.mirror.crossings := by
      rw [hcsM]
      exact List.mem_singleton_self _
    have hrM := hc2 _ hCmem
    obtain ⟨hEq, _⟩ := hrM
    rw [hNE, hSW] at hEq
    exact absurd hEq (by decide)


/-- Witness coloring for two-crossing invert sharpness: valid on both
    [+1] crossings of [+1]+[+1] (0 = 2, 5 + -5 = 2*0;
    5 = 5, 10 + 0 = 2*5), but forcing contradictory values on the
    invert. -/
def sharpColTwo : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 5 else if a = 2 then 0
  else if a = 3 then -5 else if a = 5 then 10 else if a = 6 then 5 else 0

/-- No color-matrix transport across invert on two crossings: single
    crossings always transport (the rotate step realigns the switched
    rule), but on [+1]+[+1] the first switched rule forces
    colR 1 = col 6 and colR 2 = 2*col 6 - col 3 while the second
    demands colR 5 = colR 2, i.e. col 0 = 15 against col 0 = 0.
    Hence invert_cong is false in general. -/
theorem not_coloring_invert_transport :
    Exists (fun col => (((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.pos)).IsColored col) ∧
      Not (Exists (fun colR => (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).invert.IsColored colR) ∧
        SameEndpointColors (((crossingTangle CrossingSign.pos).add
          (crossingTangle CrossingSign.pos)))
          ((((crossingTangle CrossingSign.pos).add
            (crossingTangle CrossingSign.pos)).invert)) col colR))) := by
  refine ⟨sharpColTwo, ?_, ?_⟩
  · intro C hC
    have hcs : (((crossingTangle CrossingSign.pos).add
          (crossingTangle CrossingSign.pos)).crossings) =
        [⟨0, 1, 2, 3, CrossingSign.pos⟩, ⟨1, 5, 6, 2, CrossingSign.pos⟩] := by
      decide
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · have hr : sharpColTwo 0 = sharpColTwo 2 ∧
          sharpColTwo 1 + sharpColTwo 3 = 2 * sharpColTwo 0 := ⟨rfl, rfl⟩
      exact hr
    · have hr : sharpColTwo 1 = sharpColTwo 6 ∧
          sharpColTwo 5 + sharpColTwo 2 = 2 * sharpColTwo 1 := ⟨rfl, rfl⟩
      exact hr
  · rintro ⟨colR, hcR, hs⟩
    obtain ⟨hNW, hNE, hSE, hSW⟩ := hs
    have e5 : colR 5 = 0 := hNW
    have e6 : colR 6 = 10 := hNE
    have e3 : colR 3 = 5 := hSE
    have e0 : colR 0 = -5 := hSW
    have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
        (((crossingTangle CrossingSign.pos).add
          (crossingTangle CrossingSign.pos)).invert.crossings) := by
      decide
    have m2 : (⟨5, 6, 2, 1, CrossingSign.neg⟩ : Crossing) ∈
        (((crossingTangle CrossingSign.pos).add
          (crossingTangle CrossingSign.pos)).invert.crossings) := by
      decide
    have hr1 := hcR _ m1
    obtain ⟨f1a, f1b⟩ := hr1
    have hr2 := hcR _ m2
    obtain ⟨gA, _⟩ := hr2
    linarith


/-- Theorem 2 on the coloring-ready fragment: along ColoringIsotopy
    between slideReady twists, standard-form fractions agree and every
    carried coloring fraction transfers. This covers R1/R2/R3, local
    flypes, planar isotopy, and add/mul congruence (every
    ColoringIsotopy constructor). Explicitly excluded: unrestricted
    flype_slide_add/mul and the switch-based generators
    (invert_cong, invert_add, invert_mul, mirror_cong,
    transfer) — some of these transports are refuted
    (not_coloring_mirror_transport, not_coloring_invert_transport,
    not_diagonal_addLeft_infinity, not_diagonal_mulTop_zero), the
    rest remain outstanding. Not full Isotopic invariance. -/
theorem coloring_fraction_invariant_ColoringIsotopy {e₁ e₂ : TwistExpr}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.toStandard.fraction = e₂.toStandard.fraction ∧
      ∀ v : CFValue, HasColoringFraction e₁.diagram v →
        HasColoringFraction e₂.diagram v := by
  refine ⟨TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom hok₁ hok₂ h,
    fun v hf => HasColoringFraction.of_ColoringIsotopy h hf⟩


/-- Planar 180 transport at the carried-fraction level: every coloring
    fraction of a slideReady twist is a coloring fraction of its planar
    rotation, discharging the DiagonalSum input of
    coloring_fraction_rot180_diagonal internally. Strictly stronger than
    existence at F (rot180_slideReady). -/
theorem HasColoringFraction.rot180_any_slideReady (e : TwistExpr)
    (hok : e.slideReady) {v : CFValue}
    (h : HasColoringFraction e.diagram v) :
    HasColoringFraction e.diagram.rot180 v := by
  obtain ⟨col, hc, hm, hf⟩ := h
  have hd := twist_coloring_diagonal_slideReady e hok col hc
  obtain ⟨colR, hcR, hM, hfrac⟩ :=
    coloring_fraction_rot180_diagonal e.diagram col hc hd
  refine ⟨colR, hcR, ?_, hfrac.trans hf⟩
  simpa [hM] using hm

/-- Fraction-level rot180_cong for carried fractions: transport along
    ColoringIsotopy, then rotate. Not a ColoringIsotopy
    constructor. -/
theorem HasColoringFraction.rot180_cong_any_slideReady (e₁ e₂ : TwistExpr)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) {v : CFValue}
    (hf : HasColoringFraction e₁.diagram v) :
    HasColoringFraction e₂.diagram.rot180 v :=
  HasColoringFraction.rot180_any_slideReady e₂ hok₂
    (HasColoringFraction.of_ColoringIsotopy h hf)


/-- Restricted Figure 5 slide for every coloring of a sum whose summand
    is only ColoringIsotopy-related to a slideReady twist (not itself
    twist-form): DiagonalSum of the sum assembles from the transported
    summand diagonal (diagonal_of_ColoringIsotopy_slideReady) and the
    unit diagonal via DiagonalSum_of_add. The port hypothesis stays. -/
theorem coloring_flype_slide_add_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW) :
    Exists (fun colR => (t.rot180.add (crossingTangle s)).IsColored colR ∧
      SameEndpointColors ((crossingTangle s).add t)
        (t.rot180.add (crossingTangle s)) col colR) := by
  have hdiagT : (ColorMatrix.of t
      (colorAddRight (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_add_right hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_add_left hc)
  have hd : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_add hne hdiagU hdiagT
  exact coloring_flype_slide_add s t col hc hne hd

/-- Restricted Figure 5 slide for every coloring of a product whose factor
    is only ColoringIsotopy-related to a slideReady twist. Dual to
    coloring_flype_slide_add_any_isotopy via DiagonalSum_of_mul. -/
theorem coloring_flype_slide_mul_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE) :
    Exists (fun colR => (t.rot180.mul (crossingTangle s)).IsColored colR ∧
      SameEndpointColors ((crossingTangle s).mul t)
        (t.rot180.mul (crossingTangle s)) col colR) := by
  have hdiagT : (ColorMatrix.of t
      (colorMulBottom (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_mul_bottom hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_mul_top hc)
  have hd : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_mul hne hdiagU hdiagT
  exact coloring_flype_slide_mul s t col hc hne hd

/-- HasColoringFraction transport across the restricted Figure 5 slide
    for every non-monochrome coloring of a sum with an isotopy-related
    summand, carrying that coloring's own fraction value. -/
theorem HasColoringFraction.flype_slide_add_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW)
    (hm : (ColorMatrix.of ((crossingTangle s).add t) col).NotMono) :
    HasColoringFraction (t.rot180.add (crossingTangle s))
      (ColorMatrix.of ((crossingTangle s).add t) col).fraction := by
  have hdiagT : (ColorMatrix.of t
      (colorAddRight (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_add_right hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_add_left hc)
  have hd : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_add hne hdiagU hdiagT
  exact HasColoringFraction.flype_slide_add col hc hne hd hm rfl

/-- HasColoringFraction transport across the restricted Figure 5 slide
    for every non-monochrome coloring of a product with an isotopy-related
    factor, carrying that coloring's own fraction value. -/
theorem HasColoringFraction.flype_slide_mul_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE)
    (hm : (ColorMatrix.of ((crossingTangle s).mul t) col).NotMono) :
    HasColoringFraction (t.rot180.mul (crossingTangle s))
      (ColorMatrix.of ((crossingTangle s).mul t) col).fraction := by
  have hdiagT : (ColorMatrix.of t
      (colorMulBottom (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_mul_bottom hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_mul_top hc)
  have hd : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_mul hne hdiagU hdiagT
  exact HasColoringFraction.flype_slide_mul col hc hne hd hm rfl


/-- Commutativity of left-unit addition for colorings whose summand is
    only ColoringIsotopy-related to a slideReady twist: the
    DiagonalSum input of coloring_commute_add is assembled from
    the transported summand diagonal and the unit diagonal. Port
    hypothesis stays. -/
theorem coloring_commute_add_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW) :
    Exists (fun colR => (t.add (crossingTangle s)).IsColored colR ∧
      SameEndpointColors ((crossingTangle s).add t)
        (t.add (crossingTangle s)) col colR) := by
  have hdiagT : (ColorMatrix.of t
      (colorAddRight (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_add_right hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_add_left hc)
  have hd : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_add hne hdiagU hdiagT
  exact coloring_commute_add s t col hc hne hd

/-- Commutativity of left-unit multiplication, same isotopy-related
    generality via DiagonalSum_of_mul. -/
theorem coloring_commute_mul_any_isotopy (s : CrossingSign)
    {t : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy t e.diagram) (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE) :
    Exists (fun colR => (t.mul (crossingTangle s)).IsColored colR ∧
      SameEndpointColors ((crossingTangle s).mul t)
        (t.mul (crossingTangle s)) col colR) := by
  have hdiagT : (ColorMatrix.of t
      (colorMulBottom (crossingTangle s) t col)).DiagonalSum :=
    diagonal_of_ColoringIsotopy_slideReady e hok h _
      (IsColored_mul_bottom hc)
  have hdiagU : (ColorMatrix.of (crossingTangle s) col).DiagonalSum :=
    crossingTangle_diagonal_any s _ (IsColored_mul_top hc)
  have hd : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_mul hne hdiagU hdiagT
  exact coloring_commute_mul s t col hc hne hd

/-- Recolor any diagram ColoringIsotopy-related to a slideReady
    twist along toStandard, preserving the color matrix: transport to
    the twist (coloring_ColoringIsotopy), discharge DiagonalSum
    there, then coloring_toStandard. No twist-form or
    DiagonalSum input on the source. The all-rational step toward
    Theorem 4.7 on the coloring-ready neighborhood. -/
theorem coloring_toStandard_any_isotopy {D : TangleDiagram}
    (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy D e.diagram) (col : Nat → Int)
    (hc : D.IsColored col) :
    Exists (fun colR => e.toStandard.diagram.IsColored colR ∧
      SameEndpointColors D e.toStandard.diagram col colR) := by
  obtain ⟨col1, hc1, hs1⟩ := coloring_ColoringIsotopy h col hc
  have hdiag1 : (ColorMatrix.of e.diagram col1).DiagonalSum :=
    twist_coloring_diagonal_slideReady e hok col1 hc1
  obtain ⟨colR, hcR, hsR⟩ := coloring_toStandard e hok col1 hc1 hdiag1
  exact ⟨colR, hcR, hs1.trans hsR⟩


/-- All-rational agreement on the coloring-ready neighborhood: every
    non-monochrome coloring of a diagram ColoringIsotopy-related to a
    slideReady twist has fraction F. Transport the coloring forward
    (coloring_fraction_ColoringIsotopy), transfer non-monochromeness
    along the preserved matrix, and apply f = F
    (coloring_fraction_eq_F_any_slideReady). The maximal honest form
    of Theorem 4.7 short of full Isotopic invariance. -/
theorem coloring_fraction_agreement_any_isotopy {D : TangleDiagram}
    (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy D e.diagram) (col : Nat → Int)
    (hc : D.IsColored col)
    (hm : (ColorMatrix.of D col).NotMono) :
    (ColorMatrix.of D col).fraction = e.toStandard.fraction := by
  obtain ⟨colR, hcR, hM, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy h col hc
  have hmR : (ColorMatrix.of e.diagram colR).NotMono := by
    rw [hM]
    exact hm
  have hf := coloring_fraction_eq_F_any_slideReady e hok colR hcR hmR
  exact hfrac.symm.trans hf


/-- Classification on the proved fragment, both directions: along
    ColoringIsotopy between noMulTop slideReady twists,
    algebraic fractions agree (forward invariance) and equal fractions
    give isotopic diagrams (reconstruction). Full Isotopic
    invariance in either direction is not claimed: the excluded
    generators are unproved, and mirror/invert/diagonal transports are
    refuted on the sharpness witnesses. -/
theorem rational_classification_fragment {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.fraction = e₂.fraction ∧
      Isotopic e₁.diagram e₂.diagram := by
  have hf := TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom
    hn₁ hn₂ hok₁ hok₂ h
  exact ⟨hf, twist_same_fraction_isotopic_of_noMulTop hn₁ hn₂ hf⟩


/-- Existence on the reversible neighborhood: a diagram reversibly
    coloring-isotopic from a slideReady twist admits a non-monochrome
    integral coloring satisfying DiagonalSum with fraction F. The
    colorFrom coloring of the twist transports forward along the
    symmetric path (one-way ColoringIsotopy from the twist cannot supply
    colorings of the source, so the reversible hypothesis is sharp). -/
theorem exists_coloring_fraction_reversible_slideReady
    {D : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ReversibleColoringIsotopy e.diagram D) :
    Exists (fun col => D.IsColored col ∧
      (ColorMatrix.of D col).NotMono ∧
      (ColorMatrix.of D col).DiagonalSum ∧
      (ColorMatrix.of D col).fraction = e.toStandard.fraction) := by
  obtain ⟨colR, hcR, hM, hfrac⟩ := coloring_fraction_ColoringIsotopy
    h.toColoringIsotopy (e.colorFrom 0 1)
    (e.colorFrom_isColored_slideReady hok 0 1)
  have hmT := e.colorFrom_notMono_slideReady hok
  have hdT := e.colorFrom_diagonal_slideReady hok 0 1
  have hmR : (ColorMatrix.of D colR).NotMono := by
    rw [hM]
    exact hmT
  have hdR : (ColorMatrix.of D colR).DiagonalSum := by
    rw [hM]
    exact hdT
  have hfR : (ColorMatrix.of D colR).fraction = e.toStandard.fraction := by
    have hfT := coloring_fraction_eq_F e hok (e.colorFrom 0 1)
      (e.colorFrom_isColored_slideReady hok 0 1) hdT hmT
    exact hfrac.trans hfT
  exact ⟨colR, hcR, hmR, hdR, hfR⟩


/-- Existence on the one-way forward neighborhood: a diagram receiving a
    ColoringIsotopy path from a slideReady twist admits a
    non-monochrome integral coloring satisfying DiagonalSum with
    fraction F. Strictly weaker hypothesis than the reversible version
    above (one-way paths suffice when they point at the diagram). -/
theorem exists_coloring_fraction_isotopy_from_slideReady
    {D : TangleDiagram} (e : TwistExpr) (hok : e.slideReady)
    (h : ColoringIsotopy e.diagram D) :
    Exists (fun col => D.IsColored col ∧
      (ColorMatrix.of D col).NotMono ∧
      (ColorMatrix.of D col).DiagonalSum ∧
      (ColorMatrix.of D col).fraction = e.toStandard.fraction) := by
  obtain ⟨colR, hcR, hM, hfrac⟩ := coloring_fraction_ColoringIsotopy
    h (e.colorFrom 0 1) (e.colorFrom_isColored_slideReady hok 0 1)
  have hmT := e.colorFrom_notMono_slideReady hok
  have hdT := e.colorFrom_diagonal_slideReady hok 0 1
  have hmR : (ColorMatrix.of D colR).NotMono := by
    rw [hM]
    exact hmT
  have hdR : (ColorMatrix.of D colR).DiagonalSum := by
    rw [hM]
    exact hdT
  have hfR : (ColorMatrix.of D colR).fraction = e.toStandard.fraction := by
    have hfT := coloring_fraction_eq_F e hok (e.colorFrom 0 1)
      (e.colorFrom_isColored_slideReady hok 0 1) hdT hmT
    exact hfrac.trans hfT
  exact ⟨colR, hcR, hmR, hdR, hfR⟩

/-- Unrestricted Figure 5 slide on [+1]+[+1]: every coloring transports,
    no DiagonalSum needed. The target interior arcs are forced while all
    remaining equations reduce to source-validity identities. -/
theorem coloring_flype_slide_add_one_one (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.pos)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.pos).rot180.add
      (crossingTangle CrossingSign.pos)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)))
        (((crossingTangle CrossingSign.pos).rot180.add
          (crossingTangle CrossingSign.pos))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 0 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 6 else if a = 5 then col 5 else if a = 6 then col 6
    else col a
  have hcs : (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨0, 1, 2, 3, CrossingSign.pos⟩, ⟨1, 5, 6, 2, CrossingSign.pos⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.pos).rot180.add
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨3, 5, 6, 0, CrossingSign.pos⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 0 = col 0 ∧ col 6 + col 3 = 2 * col 0
      exact ⟨rfl, by linarith⟩
    · show col 6 = col 6 ∧ col 5 + col 0 = 2 * col 6
      exact ⟨rfl, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [+1]*[+1], dually. -/
theorem coloring_flype_slide_mul_one_one (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.pos).mul
      (crossingTangle CrossingSign.pos)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.pos).rot180.mul
      (crossingTangle CrossingSign.pos)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.pos).mul
        (crossingTangle CrossingSign.pos)))
        (((crossingTangle CrossingSign.pos).rot180.mul
          (crossingTangle CrossingSign.pos))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 0 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 1 else if a = 6 then col 6 else if a = 7 then col 7
    else col a
  have hcs : (((crossingTangle CrossingSign.pos).mul
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨0, 1, 2, 3, CrossingSign.pos⟩, ⟨3, 2, 6, 7, CrossingSign.pos⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.pos).rot180.mul
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨1, 0, 6, 7, CrossingSign.pos⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 0 = col 0 ∧ col 1 + col 3 = 2 * col 0
      exact ⟨rfl, by linarith⟩
    · show col 3 = col 6 ∧ col 0 + col 7 = 2 * col 3
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩


/-- Witness coloring with fraction 1/2 on ([+1]+[+1]) inv. -/
def sharpColAddInv : Nat → Int := fun a =>
  if a = 1 then 0 else if a = 2 then 2 else if a = 3 then 0
  else if a = 0 then -2 else if a = 5 then 2 else if a = 6 then 4 else 0

/-- ([+1]+[+1]) inv carries value 1/2. -/
theorem HasColoringFraction.invert_add_one_add_one :
    HasColoringFraction
      (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).invert)
      (CFValue.ofRat (1/2 : Rat)) := by
  have hcs : (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).invert.crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩] := by
    decide
  have hM : ColorMatrix.of
      (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).invert) sharpColAddInv =
      ⟨2, 4, -2, 0⟩ := by
    rfl
  refine ⟨sharpColAddInv, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColAddInv 1 = sharpColAddInv 3 ∧
        sharpColAddInv 2 + sharpColAddInv 0 = 2 * sharpColAddInv 1
      exact ⟨by decide, by decide⟩
    · show sharpColAddInv 5 = sharpColAddInv 2 ∧
        sharpColAddInv 6 + sharpColAddInv 1 = 2 * sharpColAddInv 5
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (4 : Int) - 0 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (4 - 2) (4 - 0))) =
      CFValue.ofRat (1/2 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (4 - 2) (4 - 0) = (1/2 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Every non-monochrome coloring of [+1] inv * [+1] inv has fraction
    1/2: the two switched rules plus endpoint matching force numerator
    d and denominator 2d for nonzero d. -/
theorem coloring_fraction_invert_mul_one_one (colR : Nat → Int)
    (hcR : ((crossingTangle CrossingSign.pos).invert.mul
      (crossingTangle CrossingSign.pos).invert).IsColored colR)
    (hmR : (ColorMatrix.of
      ((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert) colR).NotMono) :
    (ColorMatrix.of
      ((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert) colR).fraction =
      CFValue.ofRat (1/2 : Rat) := by
  have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert).crossings) := by
    decide
  have m2 : (⟨0, 3, 7, 4, CrossingSign.neg⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert).crossings) := by
    decide
  have hr1 := hcR _ m1
  have hr2 := hcR _ m2
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  have hmRw : Not ((colR 1 = colR 2) ∧ (colR 2 = colR 7)) := hmR
  have hnum : colR 2 - colR 1 = colR 1 - colR 0 := by linarith
  have hden2 : colR 2 - colR 7 = 2 * (colR 1 - colR 0) := by linarith
  have hd : colR 1 - colR 0 ≠ 0 := by
    intro hz0
    have c12 : colR 1 = colR 2 := by linarith
    have c27 : colR 2 = colR 7 := by linarith
    exact hmRw ⟨c12, c27⟩
  have hden : colR 2 - colR 7 ≠ 0 := by
    rw [hden2]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((colR 2 - colR 1 : Int) : Rat) =
      ((colR 1 - colR 0 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((colR 2 - colR 7 : Int) : Rat) =
      ((2 * (colR 1 - colR 0) : Int) : Rat) := by
    exact_mod_cast hden2
  have hdR : ((colR 1 - colR 0 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((colR 2 - colR 1 : Int) : Rat) /
      ((colR 2 - colR 7 : Int) : Rat) = 1 / 2 := by
    have h2ne : ((2 * (colR 1 - colR 0) : Int) : Rat) ≠ 0 :=
      Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hd)
    rw [hnumR, hdenR, div_eq_iff h2ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      ((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert) colR).fraction =
      CFValue.ofRat (((colR 2 - colR 1 : Int) : Rat) /
        ((colR 2 - colR 7 : Int) : Rat)) := by
    show (if colR 2 - colR 7 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (colR 2 - colR 1) (colR 2 - colR 7))) =
      CFValue.ofRat (((colR 2 - colR 1 : Int) : Rat) /
        ((colR 2 - colR 7 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction 1/2 on [+1] inv * [+1] inv. -/
def sharpColMulInv : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 1 else if a = 4 then -1 else if a = 6 then 0
  else if a = 7 then 0 else 0

/-- Existence half for the right side, via an explicit witness. -/
theorem coloring_fraction_invert_mul_one_one_existence :
    Exists (fun colR => (((crossingTangle CrossingSign.pos).invert.mul
      (crossingTangle CrossingSign.pos).invert).IsColored colR) ∧
      (ColorMatrix.of
        ((crossingTangle CrossingSign.pos).invert.mul
          (crossingTangle CrossingSign.pos).invert) colR).NotMono ∧
      (ColorMatrix.of
        ((crossingTangle CrossingSign.pos).invert.mul
          (crossingTangle CrossingSign.pos).invert) colR).fraction =
        CFValue.ofRat (1/2 : Rat)) := by
  refine ⟨sharpColMulInv, ?_, ?_, ?_⟩
  · intro C hC
    have hcs : (((crossingTangle CrossingSign.pos).invert.mul
          (crossingTangle CrossingSign.pos).invert).crossings) =
        [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨0, 3, 7, 4, CrossingSign.neg⟩] := by
      decide
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColMulInv 1 = sharpColMulInv 3 ∧
        sharpColMulInv 2 + sharpColMulInv 0 = 2 * sharpColMulInv 1
      exact ⟨by decide, by decide⟩
    · show sharpColMulInv 0 = sharpColMulInv 7 ∧
        sharpColMulInv 3 + sharpColMulInv 4 = 2 * sharpColMulInv 0
      exact ⟨by decide, by decide⟩
  · have hM : ColorMatrix.of
        (((crossingTangle CrossingSign.pos).invert.mul
          (crossingTangle CrossingSign.pos).invert))
        sharpColMulInv = ⟨1, 2, -1, 0⟩ := by
      rfl
    rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · have hM : ColorMatrix.of
        (((crossingTangle CrossingSign.pos).invert.mul
          (crossingTangle CrossingSign.pos).invert))
        sharpColMulInv = ⟨1, 2, -1, 0⟩ := by
      rfl
    rw [hM]
    show (if (2 : Int) - 0 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (2 - 1) (2 - 0))) =
      CFValue.ofRat (1/2 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (2 - 1) (2 - 0) = (1/2 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Both sides of unit invert-add carry 1/2. -/
theorem HasColoringFraction.invert_add_mul_agree_one_one :
    HasColoringFraction
      (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).invert)
      (CFValue.ofRat (1/2 : Rat)) ∧
    HasColoringFraction
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.pos).invert))
      (CFValue.ofRat (1/2 : Rat)) := by
  obtain ⟨cL, hcL, hmL, hfL⟩ := HasColoringFraction.invert_add_one_add_one
  obtain ⟨cR, hcR, hmR, hfR⟩ :=
    coloring_fraction_invert_mul_one_one_existence
  exact ⟨⟨cL, hcL, hmL, hfL⟩, ⟨cR, hcR, hmR, hfR⟩⟩

/-- Witness coloring with fraction -1/2 on ([-1]+[-1]) inv. -/
def sharpColAddNegInv : Nat → Int := fun a =>
  if a = 0 then 2 else if a = 1 then 0 else if a = 2 then 2
  else if a = 3 then 4 else if a = 5 then -2 else if a = 6 then 0 else 0

/-- ([-1]+[-1]) inv carries value -1/2. -/
theorem HasColoringFraction.invert_add_negOne_negOne :
    HasColoringFraction
      (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).invert)
      (CFValue.ofRat (-1/2 : Rat)) := by
  have hcs : (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).invert.crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨6, 2, 1, 5, CrossingSign.pos⟩] := by
    decide
  have hM : ColorMatrix.of
      (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).invert) sharpColAddNegInv =
      ⟨-2, 0, 2, 4⟩ := by
    rfl
  refine ⟨sharpColAddNegInv, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColAddNegInv 2 = sharpColAddNegInv 0 ∧
        sharpColAddNegInv 3 + sharpColAddNegInv 1 = 2 * sharpColAddNegInv 2
      exact ⟨by decide, by decide⟩
    · show sharpColAddNegInv 6 = sharpColAddNegInv 1 ∧
        sharpColAddNegInv 2 + sharpColAddNegInv 5 = 2 * sharpColAddNegInv 6
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (0 : Int) - 4 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (0 - -2) (0 - 4))) =
      CFValue.ofRat (-1/2 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (0 - -2) (0 - 4) = (-1/2 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Every non-monochrome coloring of [-1] inv * [-1] inv has fraction
    -1/2: the two switched rules plus endpoint matching force numerator
    m and denominator -2m for nonzero m. -/
theorem coloring_fraction_invert_mul_negOne_negOne (colR : Nat → Int)
    (hcR : ((crossingTangle CrossingSign.neg).invert.mul
      (crossingTangle CrossingSign.neg).invert).IsColored colR)
    (hmR : (ColorMatrix.of
      ((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert) colR).NotMono) :
    (ColorMatrix.of
      ((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert) colR).fraction =
      CFValue.ofRat (-1/2 : Rat) := by
  have m1 : (⟨2, 3, 0, 1, CrossingSign.pos⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert).crossings) := by
    decide
  have m2 : (⟨3, 7, 4, 0, CrossingSign.pos⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert).crossings) := by
    decide
  have hr1 := hcR _ m1
  have hr2 := hcR _ m2
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  have hmRw : Not ((colR 1 = colR 2) ∧ (colR 2 = colR 7)) := hmR
  have hnum : colR 2 - colR 1 = colR 3 - colR 2 := by linarith
  have hden2 : colR 2 - colR 7 = 2 * (colR 2 - colR 3) := by linarith
  have hd : colR 2 - colR 3 ≠ 0 := by
    intro hz0
    have c12 : colR 1 = colR 2 := by linarith
    have c27 : colR 2 = colR 7 := by linarith
    exact hmRw ⟨c12, c27⟩
  have hden : colR 2 - colR 7 ≠ 0 := by
    rw [hden2]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((colR 2 - colR 1 : Int) : Rat) =
      ((colR 3 - colR 2 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((colR 2 - colR 7 : Int) : Rat) =
      ((2 * (colR 2 - colR 3) : Int) : Rat) := by
    exact_mod_cast hden2
  have hdR : ((colR 2 - colR 3 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((colR 2 - colR 1 : Int) : Rat) /
      ((colR 2 - colR 7 : Int) : Rat) = -1 / 2 := by
    have h2ne : ((2 * (colR 2 - colR 3) : Int) : Rat) ≠ 0 :=
      Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hd)
    rw [hnumR, hdenR, div_eq_iff h2ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      ((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert) colR).fraction =
      CFValue.ofRat (((colR 2 - colR 1 : Int) : Rat) /
        ((colR 2 - colR 7 : Int) : Rat)) := by
    show (if colR 2 - colR 7 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (colR 2 - colR 1) (colR 2 - colR 7))) =
      CFValue.ofRat (((colR 2 - colR 1 : Int) : Rat) /
        ((colR 2 - colR 7 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction -1/2 on [-1] inv * [-1] inv. -/
def sharpColMulNegInv : Nat → Int := fun a =>
  if a = 0 then 2 else if a = 1 then 4 else if a = 2 then 2
  else if a = 3 then 0 else if a = 4 then 0 else if a = 7 then -2 else 0

/-- Existence half for the negative product side, via an explicit witness. -/
theorem coloring_fraction_invert_mul_negOne_negOne_existence :
    Exists (fun colR => (((crossingTangle CrossingSign.neg).invert.mul
      (crossingTangle CrossingSign.neg).invert).IsColored colR) ∧
      (ColorMatrix.of
        ((crossingTangle CrossingSign.neg).invert.mul
          (crossingTangle CrossingSign.neg).invert) colR).NotMono ∧
      (ColorMatrix.of
        ((crossingTangle CrossingSign.neg).invert.mul
          (crossingTangle CrossingSign.neg).invert) colR).fraction =
        CFValue.ofRat (-1/2 : Rat)) := by
  refine ⟨sharpColMulNegInv, ?_, ?_, ?_⟩
  · intro C hC
    have hcs : (((crossingTangle CrossingSign.neg).invert.mul
          (crossingTangle CrossingSign.neg).invert).crossings) =
        [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨3, 7, 4, 0, CrossingSign.pos⟩] := by
      decide
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColMulNegInv 2 = sharpColMulNegInv 0 ∧
        sharpColMulNegInv 3 + sharpColMulNegInv 1 = 2 * sharpColMulNegInv 2
      exact ⟨by decide, by decide⟩
    · show sharpColMulNegInv 3 = sharpColMulNegInv 4 ∧
        sharpColMulNegInv 7 + sharpColMulNegInv 0 = 2 * sharpColMulNegInv 3
      exact ⟨by decide, by decide⟩
  · have hM : ColorMatrix.of
        (((crossingTangle CrossingSign.neg).invert.mul
          (crossingTangle CrossingSign.neg).invert))
        sharpColMulNegInv = ⟨4, 2, 0, -2⟩ := by
      rfl
    rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · have hM : ColorMatrix.of
        (((crossingTangle CrossingSign.neg).invert.mul
          (crossingTangle CrossingSign.neg).invert))
        sharpColMulNegInv = ⟨4, 2, 0, -2⟩ := by
      rfl
    rw [hM]
    show (if (2 : Int) - -2 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (2 - 4) (2 - -2))) =
      CFValue.ofRat (-1/2 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (2 - 4) (2 - -2) = (-1/2 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Both sides of negative unit invert-add carry -1/2. -/
theorem HasColoringFraction.invert_add_mul_agree_negOne_negOne :
    HasColoringFraction
      (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).invert)
      (CFValue.ofRat (-1/2 : Rat)) ∧
    HasColoringFraction
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.neg).invert))
      (CFValue.ofRat (-1/2 : Rat)) := by
  obtain ⟨cL, hcL, hmL, hfL⟩ := HasColoringFraction.invert_add_negOne_negOne
  obtain ⟨cR, hcR, hmR, hfR⟩ :=
    coloring_fraction_invert_mul_negOne_negOne_existence
  exact ⟨⟨cL, hcL, hmL, hfL⟩, ⟨cR, hcR, hmR, hfR⟩⟩

/-- Every coloring of [+1] inv * [-1] inv has fraction inf: the two
    rules force the denominator to vanish, with no non-monochrome
    hypothesis needed. -/
theorem coloring_fraction_invert_mul_one_negOne (colR : Nat → Int)
    (hcR : ((crossingTangle CrossingSign.pos).invert.mul
      (crossingTangle CrossingSign.neg).invert).IsColored colR) :
    (ColorMatrix.of
      ((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert) colR).fraction =
      CFValue.inf := by
  have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert).crossings) := by
    decide
  have m2 : (⟨3, 7, 4, 0, CrossingSign.pos⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert).crossings) := by
    decide
  have hr1 := hcR _ m1
  have hr2 := hcR _ m2
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  have hden0 : colR 2 - colR 7 = 0 := by linarith
  show (if colR 2 - colR 7 = 0 then CFValue.inf
    else CFValue.ofRat
      (Rat.divInt (colR 2 - colR 1) (colR 2 - colR 7))) = CFValue.inf
  rw [if_pos hden0]

/-- Witness coloring with fraction inf on [+1] inv * [-1] inv. -/
def sharpColMulOneNegInv : Nat → Int := fun a =>
  if a = 0 then 2 else if a = 1 then 0 else if a = 2 then -2
  else if a = 3 then 0 else if a = 4 then 0 else if a = 7 then -2 else 0

/-- [+1] inv * [-1] inv carries value inf, directly witnessed. -/
theorem HasColoringFraction.invert_mul_one_negOne :
    HasColoringFraction
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert))
      CFValue.inf := by
  have hcs : (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert).crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨3, 7, 4, 0, CrossingSign.pos⟩] := by
    decide
  have hM : ColorMatrix.of
      (((crossingTangle CrossingSign.pos).invert.mul
        (crossingTangle CrossingSign.neg).invert)) sharpColMulOneNegInv =
      ⟨0, -2, 0, -2⟩ := by
    rfl
  refine ⟨sharpColMulOneNegInv, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColMulOneNegInv 1 = sharpColMulOneNegInv 3 ∧
        sharpColMulOneNegInv 2 + sharpColMulOneNegInv 0 =
          2 * sharpColMulOneNegInv 1
      exact ⟨by decide, by decide⟩
    · show sharpColMulOneNegInv 3 = sharpColMulOneNegInv 4 ∧
        sharpColMulOneNegInv 7 + sharpColMulOneNegInv 0 =
          2 * sharpColMulOneNegInv 3
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (-2 : Int) - -2 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (-2 - 0) (-2 - -2))) = CFValue.inf
    rw [if_pos (by norm_num)]

/-- Every coloring of [-1] inv * [+1] inv has fraction inf: the two
    rules identify the middle arcs, forcing the denominator to vanish,
    with no non-monochrome hypothesis needed. -/
theorem coloring_fraction_invert_mul_negOne_one (colR : Nat → Int)
    (hcR : ((crossingTangle CrossingSign.neg).invert.mul
      (crossingTangle CrossingSign.pos).invert).IsColored colR) :
    (ColorMatrix.of
      ((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert) colR).fraction =
      CFValue.inf := by
  have m1 : (⟨2, 3, 0, 1, CrossingSign.pos⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert).crossings) := by
    decide
  have m2 : (⟨0, 3, 7, 4, CrossingSign.neg⟩ : Crossing) ∈
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert).crossings) := by
    decide
  have hr1 := hcR _ m1
  have hr2 := hcR _ m2
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  have hden0 : colR 2 - colR 7 = 0 := by linarith
  show (if colR 2 - colR 7 = 0 then CFValue.inf
    else CFValue.ofRat
      (Rat.divInt (colR 2 - colR 1) (colR 2 - colR 7))) = CFValue.inf
  rw [if_pos hden0]

/-- Witness coloring with fraction inf on [-1] inv * [+1] inv. -/
def sharpColMulNegOneInv : Nat → Int := fun a =>
  if a = 0 then 2 else if a = 1 then 0 else if a = 2 then 2
  else if a = 3 then 4 else if a = 4 then 0 else if a = 7 then 2 else 0

/-- [-1] inv * [+1] inv carries value inf, directly witnessed. -/
theorem HasColoringFraction.invert_mul_negOne_one :
    HasColoringFraction
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert))
      CFValue.inf := by
  have hcs : (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert).crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨0, 3, 7, 4, CrossingSign.neg⟩] := by
    decide
  have hM : ColorMatrix.of
      (((crossingTangle CrossingSign.neg).invert.mul
        (crossingTangle CrossingSign.pos).invert)) sharpColMulNegOneInv =
      ⟨0, 2, 0, 2⟩ := by
    rfl
  refine ⟨sharpColMulNegOneInv, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · show sharpColMulNegOneInv 2 = sharpColMulNegOneInv 0 ∧
        sharpColMulNegOneInv 3 + sharpColMulNegOneInv 1 =
          2 * sharpColMulNegOneInv 2
      exact ⟨by decide, by decide⟩
    · show sharpColMulNegOneInv 0 = sharpColMulNegOneInv 7 ∧
        sharpColMulNegOneInv 3 + sharpColMulNegOneInv 4 =
          2 * sharpColMulNegOneInv 0
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (2 : Int) - 2 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (2 - 0) (2 - 2))) = CFValue.inf
    rw [if_pos (by norm_num)]

/-- Unrestricted Figure 5 slide on [-1]+[-1]: every coloring transports,
    no DiagonalSum needed. The target interior arcs are forced while all
    remaining equations reduce to source-validity identities. -/
theorem coloring_flype_slide_add_negOne_negOne (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.neg).add
      (crossingTangle CrossingSign.neg)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.neg).rot180.add
      (crossingTangle CrossingSign.neg)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)))
        (((crossingTangle CrossingSign.neg).rot180.add
          (crossingTangle CrossingSign.neg))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 3 else if a = 5 then col 5 else if a = 6 then col 6
    else col a
  have hcs : (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.neg).rot180.add
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨3, 0, 1, 2, CrossingSign.neg⟩, ⟨5, 6, 0, 3, CrossingSign.neg⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 3 = col 3 ∧ col 2 + col 0 = 2 * col 3
      exact ⟨rfl, by linarith⟩
    · show col 5 = col 2 ∧ col 6 + col 3 = 2 * col 5
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [-1]*[-1], dually. -/
theorem coloring_flype_slide_mul_negOne_negOne (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.neg).mul
      (crossingTangle CrossingSign.neg)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.neg).rot180.mul
      (crossingTangle CrossingSign.neg)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.neg).mul
        (crossingTangle CrossingSign.neg)))
        (((crossingTangle CrossingSign.neg).rot180.mul
          (crossingTangle CrossingSign.neg))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 1 else if a = 6 then col 6 else if a = 7 then col 7
    else col a
  have hcs : (((crossingTangle CrossingSign.neg).mul
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨2, 6, 7, 3, CrossingSign.neg⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.neg).rot180.mul
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨3, 0, 1, 2, CrossingSign.neg⟩, ⟨0, 6, 7, 1, CrossingSign.neg⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 1 = col 3 ∧ col 2 + col 0 = 2 * col 1
      exact ⟨by linarith, by linarith⟩
    · show col 2 = col 7 ∧ col 6 + col 3 = 2 * col 2
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [+1]+[-1]: every coloring transports,
    no DiagonalSum needed. The target interior arcs are forced while all
    remaining equations reduce to source-validity identities. -/
theorem coloring_flype_slide_add_one_negOne (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.neg)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.pos).rot180.add
      (crossingTangle CrossingSign.neg)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.neg)))
        (((crossingTangle CrossingSign.pos).rot180.add
          (crossingTangle CrossingSign.neg))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 1 else if a = 5 then col 5 else if a = 6 then col 6
    else col a
  have hcs : (((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨0, 1, 2, 3, CrossingSign.pos⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.pos).rot180.add
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨5, 6, 0, 3, CrossingSign.neg⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 0 = col 2 ∧ col 1 + col 3 = 2 * col 0
      exact ⟨by linarith, by linarith⟩
    · show col 5 = col 2 ∧ col 6 + col 1 = 2 * col 5
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [-1]+[+1], with the orders exchanged. -/
theorem coloring_flype_slide_add_negOne_one (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.neg).add
      (crossingTangle CrossingSign.pos)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.neg).rot180.add
      (crossingTangle CrossingSign.pos)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.pos)))
        (((crossingTangle CrossingSign.neg).rot180.add
          (crossingTangle CrossingSign.pos))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 3 else if a = 5 then col 5 else if a = 6 then col 6
    else col a
  have hcs : (((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨1, 5, 6, 2, CrossingSign.pos⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.neg).rot180.add
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨3, 0, 1, 2, CrossingSign.neg⟩, ⟨3, 5, 6, 0, CrossingSign.pos⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 3 = col 3 ∧ col 2 + col 0 = 2 * col 3
      exact ⟨rfl, by linarith⟩
    · show col 3 = col 6 ∧ col 5 + col 2 = 2 * col 3
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [+1]*[-1], dually. -/
theorem coloring_flype_slide_mul_one_negOne (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.pos).mul
      (crossingTangle CrossingSign.neg)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.pos).rot180.mul
      (crossingTangle CrossingSign.neg)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.pos).mul
        (crossingTangle CrossingSign.neg)))
        (((crossingTangle CrossingSign.pos).rot180.mul
          (crossingTangle CrossingSign.neg))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 1 else if a = 6 then col 6 else if a = 7 then col 7
    else col a
  have hcs : (((crossingTangle CrossingSign.pos).mul
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨0, 1, 2, 3, CrossingSign.pos⟩, ⟨2, 6, 7, 3, CrossingSign.neg⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.pos).rot180.mul
        (crossingTangle CrossingSign.neg)).crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨0, 6, 7, 1, CrossingSign.neg⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 0 = col 2 ∧ col 1 + col 3 = 2 * col 0
      exact ⟨by linarith, by linarith⟩
    · show col 2 = col 7 ∧ col 6 + col 3 = 2 * col 2
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unrestricted Figure 5 slide on [-1]*[+1], with the orders exchanged. -/
theorem coloring_flype_slide_mul_negOne_one (col : Nat → Int)
    (hc : (((crossingTangle CrossingSign.neg).mul
      (crossingTangle CrossingSign.pos)).IsColored col)) :
    Exists (fun colR => (((crossingTangle CrossingSign.neg).rot180.mul
      (crossingTangle CrossingSign.pos)).IsColored colR) ∧
      SameEndpointColors (((crossingTangle CrossingSign.neg).mul
        (crossingTangle CrossingSign.pos)))
        (((crossingTangle CrossingSign.neg).rot180.mul
          (crossingTangle CrossingSign.pos))) col colR) := by
  let colR : Nat → Int := fun a =>
    if a = 0 then col 2 else if a = 1 then col 3 else if a = 2 then col 0
    else if a = 3 then col 1 else if a = 6 then col 6 else if a = 7 then col 7
    else col a
  have hcs : (((crossingTangle CrossingSign.neg).mul
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨3, 2, 6, 7, CrossingSign.pos⟩] := by
    decide
  have hcsR : (((crossingTangle CrossingSign.neg).rot180.mul
        (crossingTangle CrossingSign.pos)).crossings) =
      [⟨3, 0, 1, 2, CrossingSign.neg⟩, ⟨1, 0, 6, 7, CrossingSign.pos⟩] := by
    decide
  have r1 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inl rfl))
  have r2 := hc _ (by rw [hcs]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨colR, ?_, ?_⟩
  · intro C hC
    rw [hcsR] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    obtain ⟨e1a, e1b⟩ := r1
    obtain ⟨e2a, e2b⟩ := r2
    rcases hC with rfl | rfl
    · show col 1 = col 3 ∧ col 2 + col 0 = 2 * col 1
      exact ⟨by linarith, by linarith⟩
    · show col 3 = col 6 ∧ col 2 + col 7 = 2 * col 3
      exact ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every non-monochrome coloring of ([+1]+[+1]+[+1]) inv has fraction
    1/3: the three switched rules force numerator d and denominator 3d
    for nonzero d. -/
theorem coloring_fraction_invert_add_one_one_one (col : Nat → Int)
    (hc : ((((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).invert).IsColored col)
    (hm : (ColorMatrix.of
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).NotMono) :
    (ColorMatrix.of
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (1/3 : Rat) := by
  have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m2 : (⟨5, 6, 2, 1, CrossingSign.neg⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m3 : (⟨8, 9, 6, 5, CrossingSign.neg⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have hr1 := hc _ m1
  have hr2 := hc _ m2
  have hr3 := hc _ m3
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  obtain ⟨e3a, e3b⟩ := hr3
  have hmRw : Not ((col 8 = col 9) ∧ (col 9 = col 3)) := hm
  have hnum : col 9 - col 8 = col 1 - col 0 := by linarith
  have hden3 : col 9 - col 3 = 3 * (col 1 - col 0) := by linarith
  have hd : col 1 - col 0 ≠ 0 := by
    intro hz0
    have c89 : col 8 = col 9 := by linarith
    have c93 : col 9 = col 3 := by linarith
    exact hmRw ⟨c89, c93⟩
  have hden : col 9 - col 3 ≠ 0 := by
    rw [hden3]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((col 9 - col 8 : Int) : Rat) =
      ((col 1 - col 0 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((col 9 - col 3 : Int) : Rat) =
      ((3 * (col 1 - col 0) : Int) : Rat) := by
    exact_mod_cast hden3
  have hdR : ((col 1 - col 0 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((col 9 - col 8 : Int) : Rat) /
      ((col 9 - col 3 : Int) : Rat) = 1 / 3 := by
    have h3ne : ((3 * (col 1 - col 0) : Int) : Rat) ≠ 0 :=
      Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hd)
    rw [hnumR, hdenR, div_eq_iff h3ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (((col 9 - col 8 : Int) : Rat) /
        ((col 9 - col 3 : Int) : Rat)) := by
    show (if col 9 - col 3 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (col 9 - col 8) (col 9 - col 3))) =
      CFValue.ofRat (((col 9 - col 8 : Int) : Rat) /
        ((col 9 - col 3 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction 1/3 on ([+1]+[+1]+[+1]) inv. -/
def sharpColAddThree : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 1 else if a = 5 then 2 else if a = 6 then 3
  else if a = 8 then 3 else if a = 9 then 4 else 0

/-- ([+1]+[+1]+[+1]) inv carries value 1/3. -/
theorem HasColoringFraction.invert_add_one_one_one :
    HasColoringFraction
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert)
      (CFValue.ofRat (1/3 : Rat)) := by
  have hcs : ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩,
        ⟨8, 9, 6, 5, CrossingSign.neg⟩] := by
    decide
  have hM : ColorMatrix.of
      ((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) sharpColAddThree =
      ⟨3, 4, 0, 1⟩ := by
    rfl
  refine ⟨sharpColAddThree, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl
    · show sharpColAddThree 1 = sharpColAddThree 3 ∧
        sharpColAddThree 2 + sharpColAddThree 0 = 2 * sharpColAddThree 1
      exact ⟨by decide, by decide⟩
    · show sharpColAddThree 5 = sharpColAddThree 2 ∧
        sharpColAddThree 6 + sharpColAddThree 1 = 2 * sharpColAddThree 5
      exact ⟨by decide, by decide⟩
    · show sharpColAddThree 8 = sharpColAddThree 6 ∧
        sharpColAddThree 9 + sharpColAddThree 5 = 2 * sharpColAddThree 8
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (4 : Int) - 1 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (4 - 3) (4 - 1))) =
      CFValue.ofRat (1/3 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (4 - 3) (4 - 1) = (1/3 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Every non-monochrome coloring of ([+1]+[+1]+[+1]+[+1]) inv has
    fraction 1/4: the four switched rules force numerator d and
    denominator 4d for nonzero d. -/
theorem coloring_fraction_invert_add_four_one (col : Nat → Int)
    (hc : (((((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).invert).IsColored col)
    (hm : (ColorMatrix.of
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).NotMono) :
    (ColorMatrix.of
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (1/4 : Rat) := by
  have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m2 : (⟨5, 6, 2, 1, CrossingSign.neg⟩ : Crossing) ∈
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m3 : (⟨8, 9, 6, 5, CrossingSign.neg⟩ : Crossing) ∈
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m4 : (⟨11, 12, 9, 8, CrossingSign.neg⟩ : Crossing) ∈
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have hr1 := hc _ m1
  have hr2 := hc _ m2
  have hr3 := hc _ m3
  have hr4 := hc _ m4
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  obtain ⟨e3a, e3b⟩ := hr3
  obtain ⟨e4a, e4b⟩ := hr4
  have hmRw : Not ((col 11 = col 12) ∧ (col 12 = col 3)) := hm
  have hnum : col 12 - col 11 = col 1 - col 0 := by linarith
  have hden4 : col 12 - col 3 = 4 * (col 1 - col 0) := by linarith
  have hd : col 1 - col 0 ≠ 0 := by
    intro hz0
    have c1112 : col 11 = col 12 := by linarith
    have c123 : col 12 = col 3 := by linarith
    exact hmRw ⟨c1112, c123⟩
  have hden : col 12 - col 3 ≠ 0 := by
    rw [hden4]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((col 12 - col 11 : Int) : Rat) =
      ((col 1 - col 0 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((col 12 - col 3 : Int) : Rat) =
      ((4 * (col 1 - col 0) : Int) : Rat) := by
    exact_mod_cast hden4
  have hdR : ((col 1 - col 0 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((col 12 - col 11 : Int) : Rat) /
      ((col 12 - col 3 : Int) : Rat) = 1 / 4 := by
    have h4ne : ((4 * (col 1 - col 0) : Int) : Rat) ≠ 0 :=
      Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hd)
    rw [hnumR, hdenR, div_eq_iff h4ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (((col 12 - col 11 : Int) : Rat) /
        ((col 12 - col 3 : Int) : Rat)) := by
    show (if col 12 - col 3 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (col 12 - col 11) (col 12 - col 3))) =
      CFValue.ofRat (((col 12 - col 11 : Int) : Rat) /
        ((col 12 - col 3 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction 1/4 on ([+1]+[+1]+[+1]+[+1]) inv. -/
def sharpColAddFour : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 1 else if a = 5 then 2 else if a = 6 then 3
  else if a = 8 then 3 else if a = 9 then 4 else if a = 11 then 4
  else if a = 12 then 5 else 0

/-- ([+1]+[+1]+[+1]+[+1]) inv carries value 1/4. -/
theorem HasColoringFraction.invert_add_four_one :
    HasColoringFraction
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert)
      (CFValue.ofRat (1/4 : Rat)) := by
  have hcs : (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩,
        ⟨8, 9, 6, 5, CrossingSign.neg⟩, ⟨11, 12, 9, 8, CrossingSign.neg⟩] := by
    decide
  have hM : ColorMatrix.of
      (((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) sharpColAddFour =
      ⟨4, 5, 0, 1⟩ := by
    rfl
  refine ⟨sharpColAddFour, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    · show sharpColAddFour 1 = sharpColAddFour 3 ∧
        sharpColAddFour 2 + sharpColAddFour 0 = 2 * sharpColAddFour 1
      exact ⟨by decide, by decide⟩
    · show sharpColAddFour 5 = sharpColAddFour 2 ∧
        sharpColAddFour 6 + sharpColAddFour 1 = 2 * sharpColAddFour 5
      exact ⟨by decide, by decide⟩
    · show sharpColAddFour 8 = sharpColAddFour 6 ∧
        sharpColAddFour 9 + sharpColAddFour 5 = 2 * sharpColAddFour 8
      exact ⟨by decide, by decide⟩
    · show sharpColAddFour 11 = sharpColAddFour 9 ∧
        sharpColAddFour 12 + sharpColAddFour 8 = 2 * sharpColAddFour 11
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (5 : Int) - 1 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (5 - 4) (5 - 1))) =
      CFValue.ofRat (1/4 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (5 - 4) (5 - 1) = (1/4 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Every non-monochrome coloring of ([+1]+[+1]+[+1]+[+1]+[+1]) inv has
    fraction 1/5: the five switched rules force numerator d and
    denominator 5d for nonzero d. -/
theorem coloring_fraction_invert_add_five_one (col : Nat → Int)
    (hc : ((((((crossingTangle CrossingSign.pos).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).add
      (crossingTangle CrossingSign.pos)).invert).IsColored col)
    (hm : (ColorMatrix.of
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).NotMono) :
    (ColorMatrix.of
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (1/5 : Rat) := by
  have m1 : (⟨1, 2, 3, 0, CrossingSign.neg⟩ : Crossing) ∈
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m2 : (⟨5, 6, 2, 1, CrossingSign.neg⟩ : Crossing) ∈
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m3 : (⟨8, 9, 6, 5, CrossingSign.neg⟩ : Crossing) ∈
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m4 : (⟨11, 12, 9, 8, CrossingSign.neg⟩ : Crossing) ∈
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have m5 : (⟨14, 15, 12, 11, CrossingSign.neg⟩ : Crossing) ∈
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) := by
    decide
  have hr1 := hc _ m1
  have hr2 := hc _ m2
  have hr3 := hc _ m3
  have hr4 := hc _ m4
  have hr5 := hc _ m5
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  obtain ⟨e3a, e3b⟩ := hr3
  obtain ⟨e4a, e4b⟩ := hr4
  obtain ⟨e5a, e5b⟩ := hr5
  have hmRw : Not ((col 14 = col 15) ∧ (col 15 = col 3)) := hm
  have hnum : col 15 - col 14 = col 1 - col 0 := by linarith
  have hden5 : col 15 - col 3 = 5 * (col 1 - col 0) := by linarith
  have hd : col 1 - col 0 ≠ 0 := by
    intro hz0
    have c1415 : col 14 = col 15 := by linarith
    have c153 : col 15 = col 3 := by linarith
    exact hmRw ⟨c1415, c153⟩
  have hden : col 15 - col 3 ≠ 0 := by
    rw [hden5]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((col 15 - col 14 : Int) : Rat) =
      ((col 1 - col 0 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((col 15 - col 3 : Int) : Rat) =
      ((5 * (col 1 - col 0) : Int) : Rat) := by
    exact_mod_cast hden5
  have hdR : ((col 1 - col 0 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((col 15 - col 14 : Int) : Rat) /
      ((col 15 - col 3 : Int) : Rat) = 1 / 5 := by
    have h5ne : ((5 * (col 1 - col 0) : Int) : Rat) ≠ 0 :=
      Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hd)
    rw [hnumR, hdenR, div_eq_iff h5ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) col).fraction =
      CFValue.ofRat (((col 15 - col 14 : Int) : Rat) /
        ((col 15 - col 3 : Int) : Rat)) := by
    show (if col 15 - col 3 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (col 15 - col 14) (col 15 - col 3))) =
      CFValue.ofRat (((col 15 - col 14 : Int) : Rat) /
        ((col 15 - col 3 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction 1/5 on ([+1]+[+1]+[+1]+[+1]+[+1]) inv. -/
def sharpColAddFive : Nat → Int := fun a =>
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 1 else if a = 5 then 2 else if a = 6 then 3
  else if a = 8 then 3 else if a = 9 then 4 else if a = 11 then 4
  else if a = 12 then 5 else if a = 14 then 5 else if a = 15 then 6 else 0

/-- ([+1]+[+1]+[+1]+[+1]+[+1]) inv carries value 1/5. -/
theorem HasColoringFraction.invert_add_five_one :
    HasColoringFraction
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert)
      (CFValue.ofRat (1/5 : Rat)) := by
  have hcs : ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert.crossings) =
      [⟨1, 2, 3, 0, CrossingSign.neg⟩, ⟨5, 6, 2, 1, CrossingSign.neg⟩,
        ⟨8, 9, 6, 5, CrossingSign.neg⟩, ⟨11, 12, 9, 8, CrossingSign.neg⟩,
        ⟨14, 15, 12, 11, CrossingSign.neg⟩] := by
    decide
  have hM : ColorMatrix.of
      ((((((crossingTangle CrossingSign.pos).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).add
        (crossingTangle CrossingSign.pos)).invert) sharpColAddFive =
      ⟨5, 6, 0, 1⟩ := by
    rfl
  refine ⟨sharpColAddFive, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · show sharpColAddFive 1 = sharpColAddFive 3 ∧
        sharpColAddFive 2 + sharpColAddFive 0 = 2 * sharpColAddFive 1
      exact ⟨by decide, by decide⟩
    · show sharpColAddFive 5 = sharpColAddFive 2 ∧
        sharpColAddFive 6 + sharpColAddFive 1 = 2 * sharpColAddFive 5
      exact ⟨by decide, by decide⟩
    · show sharpColAddFive 8 = sharpColAddFive 6 ∧
        sharpColAddFive 9 + sharpColAddFive 5 = 2 * sharpColAddFive 8
      exact ⟨by decide, by decide⟩
    · show sharpColAddFive 11 = sharpColAddFive 9 ∧
        sharpColAddFive 12 + sharpColAddFive 8 = 2 * sharpColAddFive 11
      exact ⟨by decide, by decide⟩
    · show sharpColAddFive 14 = sharpColAddFive 12 ∧
        sharpColAddFive 15 + sharpColAddFive 11 = 2 * sharpColAddFive 14
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (6 : Int) - 1 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (6 - 5) (6 - 1))) =
      CFValue.ofRat (1/5 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (6 - 5) (6 - 1) = (1/5 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]

/-- Left-nested chain of positive units: `unitChain 0 = [+1]+[+1]`.
    Rung `n` of the invert-add ladder carries `1/(n+2)`. -/
def unitChain : Nat → TangleDiagram
  | 0 => one.add one
  | (n + 1) => (unitChain n).add one

theorem unitChain_succ (n : Nat) :
    unitChain (n + 1) = (unitChain n).add one := rfl

theorem unitChain_maxArc (n : Nat) :
    (unitChain n).maxArc = 3 * n + 6 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [unitChain_succ, maxArc_add_one, ih]
    omega

theorem unitChain_NW (n : Nat) : (unitChain n).NW = 0 := by
  induction n with
  | zero => decide
  | succ n ih => rw [unitChain_succ, add_one_NW, ih]

theorem unitChain_SW (n : Nat) : (unitChain n).SW = 3 := by
  induction n with
  | zero => decide
  | succ n ih => rw [unitChain_succ, add_one_SW, ih]

theorem unitChain_NE (n : Nat) : (unitChain n).NE = 3 * n + 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [unitChain_succ, add_one_NE, unitChain_maxArc n]
    omega

theorem unitChain_SE (n : Nat) : (unitChain n).SE = 3 * n + 6 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [unitChain_succ, add_one_SE, unitChain_maxArc n]
    omega

/-- The appended crossing of one more unit, in closed form. -/
theorem unitChain_add_crossings (n : Nat) :
    ((unitChain n).add one).crossings =
      (unitChain n).crossings ++
        [⟨3 * n + 5, 3 * n + 8, 3 * n + 9, 3 * n + 6,
          CrossingSign.pos⟩] := by
  rw [add_one_crossings, unitChain_NE n, unitChain_maxArc n, unitChain_SE n,
    show 3 * n + 6 + 2 = 3 * n + 8 from by omega,
    show 3 * n + 6 + 3 = 3 * n + 9 from by omega]

/-- Ports of the inverted chain, in closed form. -/
theorem unitChain_invert_ports (n : Nat) :
    (unitChain n).invert.NW = 3 * n + 5 ∧
    (unitChain n).invert.NE = 3 * n + 6 ∧
    (unitChain n).invert.SE = 3 ∧
    (unitChain n).invert.SW = 0 := by
  have hNW : (unitChain n).invert.NW = (unitChain n).NE := rfl
  have hNE : (unitChain n).invert.NE = (unitChain n).SE := rfl
  have hSE : (unitChain n).invert.SE = (unitChain n).SW := rfl
  have hSW : (unitChain n).invert.SW = (unitChain n).NW := rfl
  rw [hNW, hNE, hSE, hSW, unitChain_NE n, unitChain_SE n, unitChain_SW n,
    unitChain_NW n]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Prefix correspondence under inversion: the next rung appends exactly
    the switched new crossing. -/
theorem unitChain_invert_succ_crossings (n : Nat) :
    (unitChain (n + 1)).invert.crossings =
      (unitChain n).invert.crossings ++
        [⟨3 * n + 8, 3 * n + 9, 3 * n + 6, 3 * n + 5,
          CrossingSign.neg⟩] := by
  have h1 : unitChain (n + 1) = (unitChain n).add one := rfl
  have h4 : (unitChain n).invert.crossings =
      ((unitChain n).crossings).map Crossing.switch := rfl
  have h5 : ((unitChain n).add one).invert.crossings =
      (((unitChain n).add one).crossings).map Crossing.switch := rfl
  have hmap : ([⟨3 * n + 5, 3 * n + 8, 3 * n + 9, 3 * n + 6,
      CrossingSign.pos⟩].map Crossing.switch) =
      [⟨3 * n + 8, 3 * n + 9, 3 * n + 6, 3 * n + 5,
        CrossingSign.neg⟩] := rfl
  rw [h1, h5, unitChain_add_crossings n, List.map_append, ← h4, hmap]

/-- Every non-monochrome coloring of ([-1]+[-1]+[-1]) inv has fraction
    -1/3: the three switched rules force numerator d and denominator -3d
    for nonzero d. -/
theorem coloring_fraction_invert_add_negOne_negOne_negOne (col : Nat → Int)
    (hc : ((((crossingTangle CrossingSign.neg).add
      (crossingTangle CrossingSign.neg)).add
      (crossingTangle CrossingSign.neg)).invert).IsColored col)
    (hm : (ColorMatrix.of
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert) col).NotMono) :
    (ColorMatrix.of
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert) col).fraction =
      CFValue.ofRat (-1/3 : Rat) := by
  have m1 : (⟨2, 3, 0, 1, CrossingSign.pos⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert.crossings) := by
    decide
  have m2 : (⟨6, 2, 1, 5, CrossingSign.pos⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert.crossings) := by
    decide
  have m3 : (⟨9, 6, 5, 8, CrossingSign.pos⟩ : Crossing) ∈
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert.crossings) := by
    decide
  have hr1 := hc _ m1
  have hr2 := hc _ m2
  have hr3 := hc _ m3
  obtain ⟨e1a, e1b⟩ := hr1
  obtain ⟨e2a, e2b⟩ := hr2
  obtain ⟨e3a, e3b⟩ := hr3
  have hmRw : Not ((col 8 = col 9) ∧ (col 9 = col 3)) := hm
  have hnum : col 9 - col 8 = col 2 - col 1 := by linarith
  have hden3 : col 9 - col 3 = -(3 * (col 2 - col 1)) := by linarith
  have hd : col 2 - col 1 ≠ 0 := by
    intro hz0
    have c89 : col 8 = col 9 := by linarith
    have c93 : col 9 = col 3 := by linarith
    exact hmRw ⟨c89, c93⟩
  have hden : col 9 - col 3 ≠ 0 := by
    rw [hden3, neg_ne_zero]
    exact mul_ne_zero (by norm_num) hd
  have hnumR : ((col 9 - col 8 : Int) : Rat) =
      ((col 2 - col 1 : Int) : Rat) := by
    exact_mod_cast hnum
  have hdenR : ((col 9 - col 3 : Int) : Rat) =
      ((-(3 * (col 2 - col 1)) : Int) : Rat) := by
    exact_mod_cast hden3
  have hdR : ((col 2 - col 1 : Int) : Rat) ≠ 0 :=
    Int.cast_ne_zero.mpr hd
  have hval : ((col 9 - col 8 : Int) : Rat) /
      ((col 9 - col 3 : Int) : Rat) = -1 / 3 := by
    have h3 : (3 : Int) * (col 2 - col 1) ≠ 0 :=
      mul_ne_zero (by norm_num) hd
    have h3ne : ((-(3 * (col 2 - col 1)) : Int) : Rat) ≠ 0 := by
      have h3n : (-(3 * (col 2 - col 1)) : Int) ≠ 0 := neg_ne_zero.mpr h3
      exact_mod_cast h3n
    rw [hnumR, hdenR, div_eq_iff h3ne]
    push_cast
    ring
  have hfrac : (ColorMatrix.of
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert) col).fraction =
      CFValue.ofRat (((col 9 - col 8 : Int) : Rat) /
        ((col 9 - col 3 : Int) : Rat)) := by
    show (if col 9 - col 3 = 0 then CFValue.inf
      else CFValue.ofRat
        (Rat.divInt (col 9 - col 8) (col 9 - col 3))) =
      CFValue.ofRat (((col 9 - col 8 : Int) : Rat) /
        ((col 9 - col 3 : Int) : Rat))
    rw [if_neg hden, Rat.divInt_eq_div]
  rw [hfrac, hval]

/-- Witness coloring with fraction -1/3 on ([-1]+[-1]+[-1]) inv. -/
def sharpColAddNegThree : Nat → Int := fun a =>
  if a = 0 then 2 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 3 else if a = 5 then 0 else if a = 6 then 1
  else if a = 8 then -1 else if a = 9 then 0 else 0

/-- ([-1]+[-1]+[-1]) inv carries value -1/3. -/
theorem HasColoringFraction.invert_add_negOne_negOne_negOne :
    HasColoringFraction
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert)
      (CFValue.ofRat (-1/3 : Rat)) := by
  have hcs : ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert.crossings) =
      [⟨2, 3, 0, 1, CrossingSign.pos⟩, ⟨6, 2, 1, 5, CrossingSign.pos⟩,
        ⟨9, 6, 5, 8, CrossingSign.pos⟩] := by
    decide
  have hM : ColorMatrix.of
      ((((crossingTangle CrossingSign.neg).add
        (crossingTangle CrossingSign.neg)).add
        (crossingTangle CrossingSign.neg)).invert) sharpColAddNegThree =
      ⟨-1, 0, 2, 3⟩ := by
    rfl
  refine ⟨sharpColAddNegThree, ?_, ?_, ?_⟩
  · intro C hC
    rw [hcs] at hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl
    · show sharpColAddNegThree 2 = sharpColAddNegThree 0 ∧
        sharpColAddNegThree 3 + sharpColAddNegThree 1 =
          2 * sharpColAddNegThree 2
      exact ⟨by decide, by decide⟩
    · show sharpColAddNegThree 6 = sharpColAddNegThree 1 ∧
        sharpColAddNegThree 2 + sharpColAddNegThree 5 =
          2 * sharpColAddNegThree 6
      exact ⟨by decide, by decide⟩
    · show sharpColAddNegThree 9 = sharpColAddNegThree 5 ∧
        sharpColAddNegThree 6 + sharpColAddNegThree 8 =
          2 * sharpColAddNegThree 9
      exact ⟨by decide, by decide⟩
  · rw [hM]
    unfold ColorMatrix.NotMono
    decide
  · rw [hM]
    show (if (0 : Int) - 3 = 0 then CFValue.inf
      else CFValue.ofRat (Rat.divInt (0 - -1) (0 - 3))) =
      CFValue.ofRat (-1/3 : Rat)
    rw [if_neg (by norm_num)]
    have hdiv : Rat.divInt (0 - -1) (0 - 3) = (-1/3 : Rat) := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [hdiv]
end RationalTangles
