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

The algebraic mirror of `negOne` is `one`, while PD-mirror is `Crossing.switch`
(double switch is `rotate180`), so `maxArc_mirror` does not identify
`e.mirror.diagram.maxArc` with `e.diagram.maxArc`. Same `appears` implies
same `maxArc`; on `unit.add S` the appearing arcs are determined by
`S.appears` and the glue ports. That gives `TwistExpr.mirror_maxArc`, port
lemmas, `slideReady_mirror`, and a `ColoringIsotopy` between `e.diagram.mirror`
and `e.mirror.diagram` for `slideReady` expressions (extending
`coloring_mirror_diagram_rightBottom`). Invert uniqueness on this class
reuses `colorFrom_isColored_slideReady`. Any non-monochrome coloring of
`T.invert` has fraction `1/F` (`invert_eq_mirror_rotate` plus uniqueness
on the PD-mirror). If two `slideReady` expressions are related by
`ColoringIsotopy`, fresh invert colorings therefore agree. That is
fraction-level `invert_cong` on this class; it does not add `invert_cong`
to `ColoringIsotopy`. The same uniqueness after mirror gives
fraction-level `mirror_cong`: fresh PD-mirror colorings have fraction
`-F`, so they agree along `ColoringIsotopy`. Figure 14 (`transfer_odd`)
is compared at the fraction level on this class: the left-hand side is
a `slideReady` twist, and the right-hand side glues `[+1]` onto a
fresh coloring of `T.mirror.invert`, whose fraction is `-1/F` by
uniqueness after mirror rather than `SameEndpointColors` after
`one.mirror`.

`SlideReadyIsotopy` packages those comparisons (plus `ColoringIsotopy` on
`slideReady` diagrams) as a relation that carries a common coloring
fraction. Restricted `rot180` of a `slideReady` diagram (paper: planar
180° preserves the tangle, so `f` is unchanged — not the 90° identity
`f(Tʳ)=-1/f(T)`), Figure 14 with switched signs (`transfer_odd_neg`),
and Figure 5 slides under `DiagonalSum` and the `hne` port hypotheses
are included as constructors of this relation, not of `ColoringIsotopy`.
Fraction-level `rot180_add` / `rot180_mul` on a `slideReady` right-add or
bottom-mul of a unit compares `(e.addRight s).diagram.rot180` with
`(crossingTangle s).rot180.add e.diagram.rot180` (and the product
analogue) at `f`, using uniqueness of `f=F` on the rotated twist
diagram. There is no `TwistExpr` for `rot180` of a general summand, so
this comparison is not a `SlideReadyIsotopy` constructor. Fraction-level
`rot180_cong` on this class: if two `slideReady` diagrams are related by
`ColoringIsotopy` (or, with both ends `slideReady` twist expressions, by
`SlideReadyIsotopy`), any non-monochrome colorings of the two `rot180`
PD-codes have the same `f`, both equal to `F`. That uniqueness plus
`F`-invariance is not added as a constructor of `ColoringIsotopy`.
Standard-form `F` is invariant along the relation when both endpoints are
`slideReady` twist diagrams. This is not `Isotopic`: isotopy can leave
the twist/`slideReady` class. Invert-add of two general (non-unit) PD-code summands is not a
`TwistExpr`, so it is not a `SlideReadyIsotopy` constructor. For two
`rightBottom`/`slideReady` diagrams with finite nonzero `F`, glue of
affine-matched colorings colors the PD-sum; algebraic mirrors glue and
transport along `ColoringIsotopy` to the PD-mirror of the sum, then
rotate for `(T+S)ⁱ`; invert colorings glue with `coloring_fraction_mul`
for `Sⁱ*Tⁱ` (`colorAddRight`/`colorMulBottom` recover the affine
right/bottom coloring). Skip `0`/`∞` on two general summands
(matching would force `n = 0` or monochrome). Invert-add when a
summand is the `[0]` diagram is colored separately via `add_zero_eq` /
the `[0]+T` reindex (not glue). Invert-add with a summand `[∞]` is
still omitted (`T+[∞]` merges `NE` with `SE`). Unrestricted
`flype_slide_*` (no `DiagonalSum`/`hne`) and paths that leave twist
form remain omitted. None of those leftover constructors is added to
`ColoringIsotopy`.

`HasColoringFraction` is carried along `ColoringIsotopy` on arbitrary
diagrams, along invert/mirror/`rot180` of a `slideReady` twist (and
along `rot180` of any diagram whose coloring has `DiagonalSum`), along
Figure 14 when the port hypotheses hold, along invert-add of two
`rightBottom`/`slideReady` diagrams with finite nonzero `F`, and along
invert-add when a summand is the `[0]` diagram. Restricted
Figure 5 slides (with `DiagonalSum` and `hne`) likewise preserve the
carried value. Induction of `HasColoringFraction` along full `Isotopic`
is blocked by the unrestricted constructors `Isotopic.flype_slide_add`
and `Isotopic.flype_slide_mul` (no `DiagonalSum`/`hne`), and by
`Isotopic.invert_add` when a summand is `[∞]` or a non-`[0]` diagram
of fraction `0`. That induction is not claimed.
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


/-! ## Appearing arcs and algebraic-mirror PD-codes -/

theorem Crossing.memArc_rename (f : Nat → Nat) (C : Crossing) {b : Nat} :
    (C.rename f).memArc b ↔ ∃ a, C.memArc a ∧ f a = b := by
  simp only [Crossing.rename, Crossing.memArc]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨C.a0, Or.inl rfl, rfl⟩
    · exact ⟨C.a1, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨C.a2, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨C.a3, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨a, ha, hfa⟩
    rcases ha with h0 | h1 | h2 | h3
    · exact Or.inl (h0 ▸ hfa).symm
    · exact Or.inr (Or.inl (h1 ▸ hfa).symm)
    · exact Or.inr (Or.inr (Or.inl (h2 ▸ hfa).symm))
    · exact Or.inr (Or.inr (Or.inr (h3 ▸ hfa).symm))

theorem foldl_maxArc_eq_start_or_mem (cs : List Crossing) (b : Nat) :
    cs.foldl (fun m C => max m C.maxArc) b = b ∨
      ∃ C ∈ cs, cs.foldl (fun m C => max m C.maxArc) b = C.maxArc := by
  induction cs generalizing b with
  | nil => exact Or.inl rfl
  | cons C cs ih =>
    simp only [List.foldl]
    rcases ih (max b C.maxArc) with h | ⟨C', hC', hmax⟩
    · rw [h]
      by_cases hb : C.maxArc ≤ b
      · exact Or.inl (Nat.max_eq_left hb)
      · exact Or.inr ⟨C, List.mem_cons_self, Nat.max_eq_right (Nat.le_of_not_ge hb)⟩
    · exact Or.inr ⟨C', List.mem_cons_of_mem _ hC', hmax⟩

theorem foldl_maxArc_le (cs : List Crossing) (b M : Nat)
    (hb : b ≤ M) (hC : ∀ C ∈ cs, C.maxArc ≤ M) :
    cs.foldl (fun m C => max m C.maxArc) b ≤ M := by
  induction cs generalizing b with
  | nil => simpa
  | cons C cs ih =>
    simp [List.foldl]
    apply ih
    · exact Nat.max_le.mpr ⟨hb, hC C List.mem_cons_self⟩
    · intro C' hC'
      exact hC C' (List.mem_cons_of_mem _ hC')

theorem max4_eq_or (w x y z : Nat) :
    max w (max x (max y z)) = w ∨ max w (max x (max y z)) = x ∨
      max w (max x (max y z)) = y ∨ max w (max x (max y z)) = z := by
  omega

theorem TangleDiagram.maxArc_appears (T : TangleDiagram) : T.appears T.maxArc := by
  unfold TangleDiagram.maxArc TangleDiagram.appears
  set b := max T.NW (max T.NE (max T.SE T.SW))
  have hb : b = T.NW ∨ b = T.NE ∨ b = T.SE ∨ b = T.SW :=
    max4_eq_or T.NW T.NE T.SE T.SW
  rcases foldl_maxArc_eq_start_or_mem T.crossings b with h | ⟨C, hC, hmax⟩
  · rcases hb with hNW | hNE | hSE | hSW
    · left; exact h.trans hNW
    · right; left; exact h.trans hNE
    · right; right; left; exact h.trans hSE
    · right; right; right; left; exact h.trans hSW
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmax ▸ Crossing.maxArc_memArc C⟩)))

theorem TangleDiagram.appears_le_maxArc (T : TangleDiagram) {a : Nat}
    (h : T.appears a) : a ≤ T.maxArc := by
  rcases h with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
  · exact maxArc_ge_NW T
  · exact maxArc_ge_NE T
  · exact maxArc_ge_SE T
  · exact maxArc_ge_SW T
  · have hm := maxArc_ge_of_mem T hC
    have ha : a ≤ C.maxArc := by
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Crossing.a0_le_maxArc C
      · exact Crossing.a1_le_maxArc C
      · exact Crossing.a2_le_maxArc C
      · exact Crossing.a3_le_maxArc C
    exact le_trans ha hm

theorem TangleDiagram.maxArc_eq_of_appears {T S : TangleDiagram}
    (h : ∀ a, T.appears a ↔ S.appears a) : T.maxArc = S.maxArc := by
  apply Nat.le_antisymm
  · exact S.appears_le_maxArc ((h T.maxArc).mp T.maxArc_appears)
  · exact T.appears_le_maxArc ((h S.maxArc).mpr S.maxArc_appears)

theorem Crossing.rename_maxArc_le (f : Nat → Nat) (C : Crossing) (M : Nat)
    (h : ∀ a, C.memArc a → f a ≤ M) : (C.rename f).maxArc ≤ M := by
  have h0 : f C.a0 ≤ M := h C.a0 (Or.inl rfl)
  have h1 : f C.a1 ≤ M := h C.a1 (Or.inr (Or.inl rfl))
  have h2 : f C.a2 ≤ M := h C.a2 (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : f C.a3 ≤ M := h C.a3 (Or.inr (Or.inr (Or.inr rfl)))
  simp [Crossing.rename, Crossing.maxArc]
  omega

theorem one_appears (a : Nat) : one.appears a ↔ a ≤ 3 := by
  constructor
  · intro h
    simp [TangleDiagram.appears, one, Crossing.memArc] at h
    omega
  · intro h
    simp [TangleDiagram.appears, one, Crossing.memArc]
    omega

theorem negOne_appears (a : Nat) : negOne.appears a ↔ a ≤ 3 := by
  simp [negOne, TangleDiagram.appears, TangleDiagram.mirror, one,
    Crossing.switch, Crossing.memArc]
  omega

theorem crossingTangle_appears (s : CrossingSign) (a : Nat) :
    (crossingTangle s).appears a ↔ a ≤ 3 := by
  cases s with
  | pos => simpa [crossingTangle] using one_appears a
  | neg =>
    constructor
    · intro h
      simp [crossingTangle, negOne, TangleDiagram.appears, TangleDiagram.mirror,
        Crossing.switch, one, Crossing.memArc] at h
      omega
    · intro h
      simp [crossingTangle, negOne, TangleDiagram.appears, TangleDiagram.mirror,
        Crossing.switch, one, Crossing.memArc]
      omega

theorem crossingTangle_memArc_le (s : CrossingSign) {C : Crossing}
    (hC : C ∈ (crossingTangle s).crossings) {a : Nat} (ha : C.memArc a) :
    a ≤ 3 :=
  (crossingTangle_appears s a).1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, ha⟩))))

theorem crossingTangle_exists_memArc (s : CrossingSign) {a : Nat} (ha : a ≤ 3) :
    ∃ C ∈ (crossingTangle s).crossings, C.memArc a := by
  cases s with
  | pos =>
    refine ⟨⟨0, 1, 2, 3, .pos⟩, ?_, ?_⟩
    · simp [crossingTangle, one]
    · simp [Crossing.memArc]; omega
  | neg =>
    refine ⟨Crossing.switch ⟨0, 1, 2, 3, .pos⟩, ?_, ?_⟩
    · simp [crossingTangle, negOne, one, TangleDiagram.mirror]
    · simp [Crossing.switch, Crossing.memArc]; omega

theorem addGlue_shift_unit_le (T : TangleDiagram) (s : CrossingSign) {a : Nat}
    (ha : a ≤ 3) :
    addGlue T (crossingTangle s) (a + (T.maxArc + 1)) ≤ T.maxArc + 3 := by
  rw [addGlue_shift_eq]
  simp [crossingTangle_NW, crossingTangle_SW]
  split_ifs
  · exact le_trans (maxArc_ge_NE T) (by omega)
  · exact le_trans (maxArc_ge_SE T) (by omega)
  · omega

theorem add_crossingTangle_NE (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).NE = T.maxArc + 2 := by
  cases s <;> (simp [add_NE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem add_crossingTangle_SE (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).SE = T.maxArc + 3 := by
  cases s <;> (simp [add_SE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem add_crossingTangle_maxArc (T : TangleDiagram) (s : CrossingSign) :
    (T.add (crossingTangle s)).maxArc = T.maxArc + 3 := by
  let U := crossingTangle s
  have hNE := add_crossingTangle_NE T s
  have hSE := add_crossingTangle_SE T s
  apply Nat.le_antisymm
  · unfold TangleDiagram.maxArc
    rw [add_crossings_append]
    refine foldl_maxArc_le _ _ (T.maxArc + 3) ?_ ?_
    · change max T.NW (max (T.add (crossingTangle s)).NE
          (max (T.add (crossingTangle s)).SE T.SW)) ≤ T.maxArc + 3
      rw [hNE, hSE]
      have := maxArc_ge_NW T
      have := maxArc_ge_SW T
      omega
    · intro C hC
      rw [List.mem_append] at hC
      rcases hC with hC | hC
      · exact le_trans (maxArc_ge_of_mem T hC) (by omega)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        refine Crossing.rename_maxArc_le _ _ _ ?_
        intro a ha
        simpa [Function.comp, addShift] using
          addGlue_shift_unit_le T s (crossingTangle_memArc_le s hC0 ha)
  · rw [← hSE]
    exact maxArc_ge_SE _

theorem mulGlue_shift_unit_le (T : TangleDiagram) (s : CrossingSign) {a : Nat}
    (ha : a ≤ 3) :
    mulGlue T (crossingTangle s) (a + (T.maxArc + 1)) ≤ T.maxArc + 4 := by
  rw [mulGlue_shift_eq]
  simp [crossingTangle_NW, crossingTangle_NE]
  split_ifs
  · exact le_trans (maxArc_ge_SW T) (by omega)
  · exact le_trans (maxArc_ge_SE T) (by omega)
  · omega

theorem mul_SE_rename (T S : TangleDiagram) :
    (T.mul S).SE =
      if S.SE = S.NW then T.SW
      else if S.SE = S.NE then T.SE
      else S.SE + (T.maxArc + 1) := by
  simp [TangleDiagram.mul, TangleDiagram.rename]

theorem mul_SW_rename (T S : TangleDiagram) :
    (T.mul S).SW =
      if S.SW = S.NW then T.SW
      else if S.SW = S.NE then T.SE
      else S.SW + (T.maxArc + 1) := by
  simp [TangleDiagram.mul, TangleDiagram.rename]

theorem mul_crossingTangle_SE (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).SE = T.maxArc + 3 := by
  cases s <;> (simp [mul_SE_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem mul_crossingTangle_SW (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).SW = T.maxArc + 4 := by
  cases s <;> (simp [mul_SW_rename, crossingTangle, one, negOne,
    TangleDiagram.mirror]; omega)

theorem mul_crossingTangle_maxArc (T : TangleDiagram) (s : CrossingSign) :
    (T.mul (crossingTangle s)).maxArc = T.maxArc + 4 := by
  have hSE := mul_crossingTangle_SE T s
  have hSW := mul_crossingTangle_SW T s
  apply Nat.le_antisymm
  · unfold TangleDiagram.maxArc
    rw [mul_crossings_append]
    refine foldl_maxArc_le _ _ (T.maxArc + 4) ?_ ?_
    · change max T.NW (max T.NE (max (T.mul (crossingTangle s)).SE
          (T.mul (crossingTangle s)).SW)) ≤ T.maxArc + 4
      rw [hSE, hSW]
      have := maxArc_ge_NW T
      have := maxArc_ge_NE T
      omega
    · intro C hC
      rw [List.mem_append] at hC
      rcases hC with hC | hC
      · exact le_trans (maxArc_ge_of_mem T hC) (by omega)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        refine Crossing.rename_maxArc_le _ _ _ ?_
        intro a ha
        simpa [Function.comp, addShift] using
          mulGlue_shift_unit_le T s (crossingTangle_memArc_le s hC0 ha)
  · rw [← hSW]
    exact maxArc_ge_SW _

theorem mem_add_mapped {T S : TangleDiagram} {C : Crossing}
    (hC : C ∈ S.crossings) :
    C.rename (addGlue T S ∘ addShift T) ∈ (T.add S).crossings := by
  rw [add_crossings_append]
  exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))

theorem mem_mul_mapped {T S : TangleDiagram} {C : Crossing}
    (hC : C ∈ S.crossings) :
    C.rename (mulGlue T S ∘ addShift T) ∈ (T.mul S).crossings := by
  rw [mul_crossings_append]
  exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨C, hC, rfl⟩))

theorem appears_add_crossingTangle (T : TangleDiagram) (s : CrossingSign) (a : Nat) :
    (T.add (crossingTangle s)).appears a ↔
      T.appears a ∨ a = T.maxArc + 2 ∨ a = T.maxArc + 3 := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · exact Or.inl (Or.inl (by simpa [TangleDiagram.add] using hNW))
    · rw [add_crossingTangle_NE] at hNE; exact Or.inr (Or.inl hNE)
    · rw [add_crossingTangle_SE] at hSE; exact Or.inr (Or.inr hSE)
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [TangleDiagram.add] using hSW)))))
    · rw [add_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩))))
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        have hb3 := crossingTangle_memArc_le s hC0 hb
        have hf := addGlue_shift_eq T (crossingTangle s) b
        simp [crossingTangle_NW, crossingTangle_SW, Function.comp, addShift, U] at hba hf
        rw [hf] at hba
        split_ifs at hba with hNW hSW
        · exact Or.inl (Or.inr (Or.inl hba.symm))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hba.symm)))
        · have hb02 : b ≠ 0 ∧ b ≠ 3 := ⟨hNW, hSW⟩
          have : b = 1 ∨ b = 2 := by omega
          rcases this with rfl | rfl
          · apply Or.inr; apply Or.inl; omega
          · apply Or.inr; apply Or.inr; omega
  · intro h
    rcases h with hT | rfl | rfl
    · rcases hT with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · left; simp [TangleDiagram.add]
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NW] : (crossingTangle s).NW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NW, hmem0, by
          simpa [Function.comp, addShift] using addGlue_NW T (crossingTangle s)⟩
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_SW] : (crossingTangle s).SW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).SW, hmem0, by
          simpa [Function.comp, addShift] using
            addGlue_SW T (crossingTangle s) (crossingTangle_NW_ne_SW s)⟩
      · right; right; right; left; simp [TangleDiagram.add]
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, by simp [add_crossings_append, hC], hmem⟩)))
    · exact Or.inr (Or.inl (add_crossingTangle_NE T s).symm)
    · exact Or.inr (Or.inr (Or.inl (add_crossingTangle_SE T s).symm))

theorem appears_mul_crossingTangle (T : TangleDiagram) (s : CrossingSign) (a : Nat) :
    (T.mul (crossingTangle s)).appears a ↔
      T.appears a ∨ a = T.maxArc + 3 ∨ a = T.maxArc + 4 := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · exact Or.inl (Or.inl (by simpa [TangleDiagram.mul] using hNW))
    · exact Or.inl (Or.inr (Or.inl (by simpa [TangleDiagram.mul] using hNE)))
    · rw [mul_crossingTangle_SE] at hSE; exact Or.inr (Or.inl hSE)
    · rw [mul_crossingTangle_SW] at hSW; exact Or.inr (Or.inr hSW)
    · rw [mul_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩))))
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        have hb3 := crossingTangle_memArc_le s hC0 hb
        have hf := mulGlue_shift_eq T (crossingTangle s) b
        simp [crossingTangle_NW, crossingTangle_NE, Function.comp, addShift, U] at hba hf
        rw [hf] at hba
        split_ifs at hba with hNW hNE
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hba.symm))))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hba.symm)))
        · have hb01 : b ≠ 0 ∧ b ≠ 1 := ⟨hNW, hNE⟩
          have : b = 2 ∨ b = 3 := by omega
          rcases this with rfl | rfl
          · apply Or.inr; apply Or.inl; omega
          · apply Or.inr; apply Or.inr; omega
  · intro h
    rcases h with hT | rfl | rfl
    · rcases hT with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · left; simp [TangleDiagram.mul]
      · right; left; simp [TangleDiagram.mul]
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NE] : (crossingTangle s).NE ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NE, hmem0, by
          simpa [Function.comp, addShift] using
            mulGlue_NE T (crossingTangle s) (crossingTangle_NW_ne_NE s)⟩
      · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (by simp [crossingTangle_NW] : (crossingTangle s).NW ≤ 3)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC0, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨(crossingTangle s).NW, hmem0, by
          simpa [Function.comp, addShift] using mulGlue_NW T (crossingTangle s)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C, by simp [mul_crossings_append, hC], hmem⟩)))
    · exact Or.inr (Or.inr (Or.inl (mul_crossingTangle_SE T s).symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mul_crossingTangle_SW T s).symm)))

theorem appears_add_left_unit (s : CrossingSign) (S : TangleDiagram) (a : Nat) :
    ((crossingTangle s).add S).appears a ↔
      a ≤ 3 ∨ ∃ b, S.appears b ∧
        addGlue (crossingTangle s) S
          (b + ((crossingTangle s).maxArc + 1)) = a := by
  let U := crossingTangle s
  have hUmax : U.maxArc = 3 := crossingTangle_maxArc s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · have : a = 0 := by simpa [TangleDiagram.add, crossingTangle_NW] using hNW
      omega
    · refine Or.inr ⟨S.NE, Or.inr (Or.inl rfl),
        (add_NE (crossingTangle s) S).symm.trans hNE.symm⟩
    · refine Or.inr ⟨S.SE, Or.inr (Or.inr (Or.inl rfl)),
        (add_SE (crossingTangle s) S).symm.trans hSE.symm⟩
    · have : a = 3 := by simpa [TangleDiagram.add, crossingTangle_SW] using hSW
      omega
    · rw [add_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · have : U.appears a := Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩)))
        exact Or.inl ((crossingTangle_appears s a).1 this)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        refine Or.inr ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, hC0, hb⟩))), ?_⟩
        simpa [Function.comp, addShift] using hba
  · intro h
    rcases h with ha | ⟨b, hbS, hglue⟩
    · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s ha
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, ?_, hmem0⟩)))
      rw [add_crossings_append]
      exact List.mem_append.2 (Or.inl hC0)
    · rcases hbS with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · have : a = (crossingTangle s).NE :=
          hglue.symm.trans (addGlue_NW (crossingTangle s) S)
        obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (le_trans (le_of_eq (crossingTangle_NE s)) (by decide : (1 : Nat) ≤ 3))
        rw [this]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
      · exact Or.inr (Or.inl (hglue.symm.trans (add_NE (crossingTangle s) S).symm))
      · exact Or.inr (Or.inr (Or.inl (hglue.symm.trans (add_SE (crossingTangle s) S).symm)))
      · have hba := hglue
        rw [addGlue_shift_eq] at hba
        split_ifs at hba with hNW hSW
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_NE s)) (by decide : (1 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_SE s)) (by decide : (2 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [add_crossings_append, hC0], hmem0⟩)))
        · exact (hSW rfl).elim
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_add_mapped hC, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨b, hmem, by simpa [Function.comp, addShift] using hglue⟩

theorem appears_mul_top_unit (s : CrossingSign) (S : TangleDiagram) (a : Nat) :
    ((crossingTangle s).mul S).appears a ↔
      a ≤ 3 ∨ ∃ b, S.appears b ∧
        mulGlue (crossingTangle s) S
          (b + ((crossingTangle s).maxArc + 1)) = a := by
  let U := crossingTangle s
  constructor
  · intro h
    rcases h with hNW | hNE | hSE | hSW | ⟨C, hC, hmem⟩
    · have : a = 0 := by simpa [TangleDiagram.mul, crossingTangle_NW] using hNW
      omega
    · have : a = 1 := by simpa [TangleDiagram.mul, crossingTangle_NE] using hNE
      omega
    · refine Or.inr ⟨S.SE, Or.inr (Or.inr (Or.inl rfl)),
        (mul_SE_glue (crossingTangle s) S).symm.trans hSE.symm⟩
    · refine Or.inr ⟨S.SW, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        (mul_SW_glue (crossingTangle s) S).symm.trans hSW.symm⟩
    · rw [mul_crossings_append, List.mem_append] at hC
      rcases hC with hC | hC
      · have : U.appears a := Or.inr (Or.inr (Or.inr (Or.inr ⟨C, hC, hmem⟩)))
        exact Or.inl ((crossingTangle_appears s a).1 this)
      · obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
        rw [Crossing.memArc_rename] at hmem
        obtain ⟨b, hb, hba⟩ := hmem
        refine Or.inr ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, hC0, hb⟩))), ?_⟩
        simpa [Function.comp, addShift] using hba
  · intro h
    rcases h with ha | ⟨b, hbS, hglue⟩
    · obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s ha
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, ?_, hmem0⟩)))
      rw [mul_crossings_append]
      exact List.mem_append.2 (Or.inl hC0)
    · rcases hbS with rfl | rfl | rfl | rfl | ⟨C, hC, hmem⟩
      · have : a = (crossingTangle s).SW :=
          hglue.symm.trans (mulGlue_NW (crossingTangle s) S)
        obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
          (le_of_eq (crossingTangle_SW s))
        rw [this]
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
      · have hba := hglue
        rw [mulGlue_shift_eq] at hba
        split_ifs at hba with hNW hNE
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_of_eq (crossingTangle_SW s))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
        · subst hba
          obtain ⟨C0, hC0, hmem0⟩ := crossingTangle_exists_memArc s
            (le_trans (le_of_eq (crossingTangle_SE s)) (by decide : (2 : Nat) ≤ 3))
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨C0, by simp [mul_crossings_append, hC0], hmem0⟩)))
        · exact (hNE rfl).elim
      · rw [← mul_SE_glue] at hglue
        rw [← hglue]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [← mul_SW_glue] at hglue
        rw [← hglue]
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, mem_mul_mapped hC, ?_⟩)))
        rw [Crossing.memArc_rename]
        exact ⟨b, hmem, by simpa [Function.comp, addShift] using hglue⟩

theorem addGlue_crossingTangle_congr (s t : CrossingSign) {S S' : TangleDiagram}
    (hNW : S.NW = S'.NW) (hSW : S.SW = S'.SW) (b : Nat) :
    addGlue (crossingTangle s) S (b + ((crossingTangle s).maxArc + 1)) =
      addGlue (crossingTangle t) S' (b + ((crossingTangle t).maxArc + 1)) := by
  rw [addGlue_shift_eq, addGlue_shift_eq]
  simp [crossingTangle_NE, crossingTangle_SE, crossingTangle_maxArc, hNW, hSW]

theorem mulGlue_crossingTangle_congr (s t : CrossingSign) {S S' : TangleDiagram}
    (hNW : S.NW = S'.NW) (hNE : S.NE = S'.NE) (b : Nat) :
    mulGlue (crossingTangle s) S (b + ((crossingTangle s).maxArc + 1)) =
      mulGlue (crossingTangle t) S' (b + ((crossingTangle t).maxArc + 1)) := by
  rw [mulGlue_shift_eq, mulGlue_shift_eq]
  simp [crossingTangle_SW, crossingTangle_SE, crossingTangle_maxArc, hNW, hNE]

theorem TwistExpr.mirror_diagram_core (e : TwistExpr) :
    e.mirror.diagram.NW = e.diagram.NW ∧
    e.mirror.diagram.NE = e.diagram.NE ∧
    e.mirror.diagram.SE = e.diagram.SE ∧
    e.mirror.diagram.SW = e.diagram.SW ∧
    (∀ a, e.mirror.diagram.appears a ↔ e.diagram.appears a) ∧
    e.mirror.diagram.maxArc = e.diagram.maxArc := by
  induction e with
  | zero =>
    simp [TwistExpr.mirror, TwistExpr.diagram]
  | infinity =>
    simp [TwistExpr.mirror, TwistExpr.diagram]
  | one =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro a
      simpa [TwistExpr.mirror, TwistExpr.diagram] using
        (negOne_appears a).trans (one_appears a).symm
    · simpa [TwistExpr.mirror, TwistExpr.diagram, Neg.neg] using
        maxArc_mirror RationalTangles.one
  | negOne =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro a
      simpa [TwistExpr.mirror, TwistExpr.diagram] using
        (one_appears a).trans (negOne_appears a).symm
    · simpa [TwistExpr.mirror, TwistExpr.diagram, Neg.neg] using
        (maxArc_mirror RationalTangles.one).symm
  | addRight e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hNEsum :
        (e.mirror.diagram.add (crossingTangle s.flip)).NE =
          (e.diagram.add (crossingTangle s)).NE := by
      rw [add_crossingTangle_NE, add_crossingTangle_NE, hmax]
    have hSEsum :
        (e.mirror.diagram.add (crossingTangle s.flip)).SE =
          (e.diagram.add (crossingTangle s)).SE := by
      rw [add_crossingTangle_SE, add_crossingTangle_SE, hmax]
    refine ⟨?_, hNEsum, hSEsum, ?_, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, hNW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, hSW]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_crossingTangle, appears_add_crossingTangle, happ, hmax]
    · simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [add_crossingTangle_maxArc, add_crossingTangle_maxArc, hmax]
  | mulBottom e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hSEsum :
        (e.mirror.diagram.mul (crossingTangle s.flip)).SE =
          (e.diagram.mul (crossingTangle s)).SE := by
      rw [mul_crossingTangle_SE, mul_crossingTangle_SE, hmax]
    have hSWsum :
        (e.mirror.diagram.mul (crossingTangle s.flip)).SW =
          (e.diagram.mul (crossingTangle s)).SW := by
      rw [mul_crossingTangle_SW, mul_crossingTangle_SW, hmax]
    refine ⟨?_, ?_, hSEsum, hSWsum, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, hNW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, hNE]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_crossingTangle, appears_mul_crossingTangle, happ, hmax]
    · simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [mul_crossingTangle_maxArc, mul_crossingTangle_maxArc, hmax]
  | addLeft e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hNEsum :
        ((crossingTangle s.flip).add e.mirror.diagram).NE =
          ((crossingTangle s).add e.diagram).NE := by
      rw [add_NE, add_NE, hNE]
      exact addGlue_crossingTangle_congr s.flip s hNW hSW _
    have hSEsum :
        ((crossingTangle s.flip).add e.mirror.diagram).SE =
          ((crossingTangle s).add e.diagram).SE := by
      rw [add_SE, add_SE, hSE]
      exact addGlue_crossingTangle_congr s.flip s hNW hSW _
    refine ⟨?_, hNEsum, hSEsum, ?_, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, crossingTangle_NW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.add, crossingTangle_SW]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_left_unit, appears_add_left_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (addGlue_crossingTangle_congr s.flip s hNW hSW b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (addGlue_crossingTangle_congr s s.flip hNW.symm hSW.symm b).symm.trans hglue
    · apply TangleDiagram.maxArc_eq_of_appears
      intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, add_eq_add]
      rw [appears_add_left_unit, appears_add_left_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (addGlue_crossingTangle_congr s.flip s hNW hSW b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (addGlue_crossingTangle_congr s s.flip hNW.symm hSW.symm b).symm.trans hglue
  | mulTop e s ih =>
    obtain ⟨hNW, hNE, hSE, hSW, happ, hmax⟩ := ih
    have hSEsum :
        ((crossingTangle s.flip).mul e.mirror.diagram).SE =
          ((crossingTangle s).mul e.diagram).SE := by
      rw [mul_SE_glue, mul_SE_glue, hSE]
      exact mulGlue_crossingTangle_congr s.flip s hNW hNE _
    have hSWsum :
        ((crossingTangle s.flip).mul e.mirror.diagram).SW =
          ((crossingTangle s).mul e.diagram).SW := by
      rw [mul_SW_glue, mul_SW_glue, hSW]
      exact mulGlue_crossingTangle_congr s.flip s hNW hNE _
    refine ⟨?_, ?_, hSEsum, hSWsum, ?_, ?_⟩
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, crossingTangle_NW]
    · simp [TwistExpr.mirror, TwistExpr.diagram, TangleDiagram.mul, crossingTangle_NE]
    · intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_top_unit, appears_mul_top_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s.flip s hNW hNE b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s s.flip hNW.symm hNE.symm b).symm.trans hglue
    · apply TangleDiagram.maxArc_eq_of_appears
      intro a
      simp only [TwistExpr.mirror, TwistExpr.diagram, mul_eq_mul]
      rw [appears_mul_top_unit, appears_mul_top_unit]
      constructor
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mp hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s.flip s hNW hNE b).symm.trans hglue
      · rintro (ha | ⟨b, hb, hglue⟩)
        · exact Or.inl ha
        · refine Or.inr ⟨b, (happ b).mpr hb, ?_⟩
          exact (mulGlue_crossingTangle_congr s s.flip hNW.symm hNE.symm b).symm.trans hglue

theorem TwistExpr.mirror_NW (e : TwistExpr) : e.mirror.diagram.NW = e.diagram.NW :=
  (e.mirror_diagram_core).1

theorem TwistExpr.mirror_NE (e : TwistExpr) : e.mirror.diagram.NE = e.diagram.NE :=
  (e.mirror_diagram_core).2.1

theorem TwistExpr.mirror_SE (e : TwistExpr) : e.mirror.diagram.SE = e.diagram.SE :=
  (e.mirror_diagram_core).2.2.1

theorem TwistExpr.mirror_SW (e : TwistExpr) : e.mirror.diagram.SW = e.diagram.SW :=
  (e.mirror_diagram_core).2.2.2.1

theorem TwistExpr.mirror_appears (e : TwistExpr) (a : Nat) :
    e.mirror.diagram.appears a ↔ e.diagram.appears a :=
  (e.mirror_diagram_core).2.2.2.2.1 a

theorem TwistExpr.mirror_maxArc (e : TwistExpr) :
    e.mirror.diagram.maxArc = e.diagram.maxArc :=
  (e.mirror_diagram_core).2.2.2.2.2

theorem TwistExpr.slideReady_mirror (e : TwistExpr) (hok : e.slideReady) :
    e.mirror.slideReady := by
  induction e with
  | zero | infinity | one | negOne => simp [TwistExpr.mirror, TwistExpr.slideReady]
  | addRight e s ih =>
    simpa [TwistExpr.mirror, TwistExpr.slideReady] using ih hok
  | mulBottom e s ih =>
    simpa [TwistExpr.mirror, TwistExpr.slideReady] using ih hok
  | addLeft e s ih =>
    obtain ⟨hne, hok'⟩ := hok
    refine ⟨?_, ih hok'⟩
    simpa [TwistExpr.mirror, TwistExpr.slideReady, e.mirror_NW, e.mirror_SW] using hne
  | mulTop e s ih =>
    obtain ⟨hne, hok'⟩ := hok
    refine ⟨?_, ih hok'⟩
    simpa [TwistExpr.mirror, TwistExpr.slideReady, e.mirror_NW, e.mirror_NE] using hne

theorem TwistExpr.toStandard_mirror (e : TwistExpr) :
    e.mirror.toStandard = e.toStandard.mirror := by
  induction e with
  | zero | infinity => rfl
  | one | negOne =>
    simp [TwistExpr.mirror, TwistExpr.toStandard, StandardExpr.mirror, CrossingSign.flip]
  | addRight e s ih | addLeft e s ih | mulBottom e s ih | mulTop e s ih =>
    simp [TwistExpr.mirror, TwistExpr.toStandard, StandardExpr.mirror, ih]

theorem coloring_mirror_diagram_slideReady (e : TwistExpr) (hok : e.slideReady) :
    ColoringIsotopy e.diagram.mirror e.mirror.diagram := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | infinity =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | one =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | negOne =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .isotopy (planar_mirror_mirror one)
  | addRight e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).SW := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).SW :=
        crossingTangle_NW_ne_SW s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := (crossingTangle s).mirror) (ih hok'))
        (.add_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE →
        (crossingTangle s.flip).NW = (crossingTangle s.flip).NE := by
      intro h
      have : (crossingTangle s).NW ≠ (crossingTangle s).NE :=
        crossingTangle_NW_ne_NE s
      simp [TangleDiagram.mirror] at h
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := (crossingTangle s).mirror) (ih hok'))
        (.mul_right (coloring_crossingTangle_mirror s) hglue)
    simpa [mirror_mul] using hstep
  | addLeft e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.diagram.mirror.NW = e.diagram.mirror.SW →
        e.mirror.diagram.NW = e.mirror.diagram.SW := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_SW] using h
    have hstep :=
      ColoringIsotopy.trans
        (.add_right (T := (crossingTangle s).mirror) (ih hok') hglue)
        (.add_left (S := e.mirror.diagram) (coloring_crossingTangle_mirror s))
    simpa [mirror_add] using hstep
  | mulTop e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.diagram.mirror.NW = e.diagram.mirror.NE →
        e.mirror.diagram.NW = e.mirror.diagram.NE := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_NE] using h
    have hstep :=
      ColoringIsotopy.trans
        (.mul_right (T := (crossingTangle s).mirror) (ih hok') hglue)
        (.mul_left (S := e.mirror.diagram) (coloring_crossingTangle_mirror s))
    simpa [mirror_mul] using hstep

theorem coloring_mirror_diagram_rev_slideReady (e : TwistExpr) (hok : e.slideReady) :
    ColoringIsotopy e.mirror.diagram e.diagram.mirror := by
  induction e with
  | zero =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | infinity =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | one =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .refl _
  | negOne =>
    simp [TwistExpr.diagram, TwistExpr.mirror]
    exact .isotopy (planar_mirror_mirror_rev one)
  | addRight e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).SW →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.SW := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).SW :=
        crossingTangle_NW_ne_SW s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.add_left (S := crossingTangle s.flip) (ih hok'))
        (.add_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_add] using hstep
  | mulBottom e s ih =>
    have hok' : e.slideReady := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : (crossingTangle s.flip).NW = (crossingTangle s.flip).NE →
        (crossingTangle s).mirror.NW = (crossingTangle s).mirror.NE := by
      intro h
      have : (crossingTangle s.flip).NW ≠ (crossingTangle s.flip).NE :=
        crossingTangle_NW_ne_NE s.flip
      exact (this h).elim
    have hstep :=
      ColoringIsotopy.trans (.mul_left (S := crossingTangle s.flip) (ih hok'))
        (.mul_right (coloring_crossingTangle_mirror_rev s) hglue)
    simpa [mirror_mul] using hstep
  | addLeft e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.mirror.diagram.NW = e.mirror.diagram.SW →
        e.diagram.mirror.NW = e.diagram.mirror.SW := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_SW] using h
    have hstep :=
      ColoringIsotopy.trans
        (.add_right (T := crossingTangle s.flip) (ih hok') hglue)
        (.add_left (S := e.diagram.mirror) (coloring_crossingTangle_mirror_rev s))
    simpa [mirror_add] using hstep
  | mulTop e s ih =>
    obtain ⟨_hne, hok'⟩ := hok
    simp only [TwistExpr.diagram, TwistExpr.mirror]
    have hglue : e.mirror.diagram.NW = e.mirror.diagram.NE →
        e.diagram.mirror.NW = e.diagram.mirror.NE := by
      intro h
      simpa [TangleDiagram.mirror, e.mirror_NW, e.mirror_NE] using h
    have hstep :=
      ColoringIsotopy.trans
        (.mul_right (T := crossingTangle s.flip) (ih hok') hglue)
        (.mul_left (S := e.diagram.mirror) (coloring_crossingTangle_mirror_rev s))
    simpa [mirror_mul] using hstep

/-- A non-monochrome coloring of the PD-mirror of a `slideReady` diagram has
    coloring fraction `-f(T)`. Fresh coloring of the algebraic mirror, via
    `ColoringIsotopy` to `e.diagram.mirror`. -/
theorem coloring_mirror_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col col' : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono)
    (hc' : e.diagram.mirror.IsColored col')
    (hm' : (ColorMatrix.of e.diagram.mirror col').NotMono) :
    (ColorMatrix.of e.diagram.mirror col').fraction =
      (ColorMatrix.of e.diagram col).fraction.neg := by
  obtain ⟨colM, hcM, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_slideReady e hok) col' hc'
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono := by
    simpa [hMat] using hm'
  have hdiag := twist_coloring_diagonal_slideReady e hok col hc
  have hokM := TwistExpr.slideReady_mirror e hok
  have hdiagM := twist_coloring_diagonal_slideReady e.mirror hokM colM hcM
  have hfT := coloring_fraction_eq_F e hok col hc hdiag hm
  have hfM := coloring_fraction_eq_F e.mirror hokM colM hcM hdiagM hmM
  rw [hfrac.symm, hfM, TwistExpr.toStandard_mirror, StandardExpr.fraction_mirror, hfT]

/-- `f(Tⁱ) = 1/f(T)` on a `slideReady` twist diagram, via a fresh coloring of
    the algebraic mirror transported along `coloring_mirror_diagram_rev_slideReady`. -/
theorem coloring_invert_inv_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction =
        (ColorMatrix.of e.diagram col).fraction.inv := by
  have hokM : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  let colM := e.mirror.colorFrom 0 1
  have hcM : e.mirror.diagram.IsColored colM :=
    e.mirror.colorFrom_isColored_slideReady hokM 0 1
  have hmM : (ColorMatrix.of e.mirror.diagram colM).NotMono :=
    e.mirror.colorFrom_notMono_slideReady hokM
  have hdM : (ColorMatrix.of e.mirror.diagram colM).DiagonalSum :=
    e.mirror.colorFrom_diagonal_slideReady hokM 0 1
  obtain ⟨col', hc', hMat, _hfrac⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_rev_slideReady e hok) colM hcM
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
    have hfM := coloring_mirror_slideReady e hok col col' hc hm hc' hm'
    rw [hrot, hfM, CFValue.negInv, ← CFValue.neg_inv, CFValue.neg_neg]

/-- Rotation does not change the crossing list, so a coloring of `T.invert`
    is a coloring of `T.mirror`. -/
theorem TangleDiagram.IsColored_of_invert (T : TangleDiagram) (col : Nat → Int)
    (h : T.invert.IsColored col) : T.mirror.IsColored col := by
  intro C hC
  have hC' : C ∈ T.invert.crossings := by
    simpa [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror] using hC
  exact h C hC'

/-- `NotMono` of a 90° rotate, with `DiagonalSum`, implies `NotMono`. -/
theorem ColorMatrix.NotMono_of_rotate {M : ColorMatrix}
    (hd : M.DiagonalSum) (hm : M.rotate.NotMono) : M.NotMono := by
  intro h
  simp [ColorMatrix.NotMono, ColorMatrix.rotate, ColorMatrix.DiagonalSum] at h hd hm
  omega

/-- A fresh coloring of the inverted PD-code of a `slideReady` twist
    diagram has coloring fraction `1/F(T)`. Composes
    `coloring_invert_inv_slideReady` with `f = F`. Not a coloring of
    `Isotopic.invert_cong`. -/
theorem coloring_invert_inv_eq_F_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction =
        e.toStandard.fraction.inv := by
  obtain ⟨col', hc', hm', hf⟩ := coloring_invert_inv_slideReady e hok col hc hm
  refine ⟨col', hc', hm', hf.trans (congrArg CFValue.inv ?_)⟩
  exact coloring_fraction_eq_F e hok col hc
    (twist_coloring_diagonal_slideReady e hok col hc) hm

/-- Same as `coloring_invert_inv_eq_F_slideReady`, discharging the coloring
    by `colorFrom 0 1`. -/
theorem coloring_invert_inv_eq_F_slideReady_colorFrom (e : TwistExpr)
    (hok : e.slideReady) :
    ∃ col', e.diagram.invert.IsColored col' ∧
      (ColorMatrix.of e.diagram.invert col').NotMono ∧
      (ColorMatrix.of e.diagram.invert col').fraction =
        e.toStandard.fraction.inv :=
  coloring_invert_inv_eq_F_slideReady e hok (e.colorFrom 0 1)
    (e.colorFrom_isColored_slideReady hok 0 1)
    (e.colorFrom_notMono_slideReady hok)

/-- Standard-form `F` of a `slideReady` twist expression is unchanged along
    `ColoringIsotopy`, with the coloring discharged by `colorFrom 0 1`. -/
theorem TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom {e₁ e₂ : TwistExpr}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.toStandard.fraction = e₂.toStandard.fraction :=
  TwistExpr.toStandard_fraction_ColoringIsotopy hok₁ hok₂ h
    (e₁.colorFrom 0 1)
    (e₁.colorFrom_isColored_slideReady hok₁ 0 1)
    (e₁.colorFrom_diagonal_slideReady hok₁ 0 1)
    (e₁.colorFrom_notMono_slideReady hok₁)

/-- Every non-monochrome coloring of `T.invert` on a `slideReady` diagram has
    fraction `1/F(T)`. The invert PD-code is the rotate of the PD-mirror
    (`invert_eq_mirror_rotate`); uniqueness of `f` on `T` and on the
    algebraic mirror identifies the PD-mirror fraction as `-F`. -/
theorem coloring_invert_inv_any_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.invert.IsColored col)
    (hm : (ColorMatrix.of e.diagram.invert col).NotMono) :
    (ColorMatrix.of e.diagram.invert col).fraction =
      e.toStandard.fraction.inv := by
  have hcMirr : e.diagram.mirror.IsColored col :=
    TangleDiagram.IsColored_of_invert _ col hc
  obtain ⟨colA, hcA, hMat, _hfracA⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_slideReady e hok) col hcMirr
  have hokA : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  have hdA : (ColorMatrix.of e.mirror.diagram colA).DiagonalSum :=
    twist_coloring_diagonal_slideReady e.mirror hokA colA hcA
  have hdMirr : (ColorMatrix.of e.diagram.mirror col).DiagonalSum := by
    simpa [hMat] using hdA
  have hrotM :
      ColorMatrix.of e.diagram.invert col =
        (ColorMatrix.of e.diagram.mirror col).rotate := by
    simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
  have hmMirr : (ColorMatrix.of e.diagram.mirror col).NotMono :=
    ColorMatrix.NotMono_of_rotate hdMirr (by simpa [hrotM] using hm)
  have hrot :
      (ColorMatrix.of e.diagram.invert col).fraction =
        (ColorMatrix.of e.diagram.mirror col).fraction.negInv := by
    simpa [invert_eq_mirror_rotate] using
      coloring_fraction_rotate e.diagram.mirror col hdMirr hmMirr
  let colT := e.colorFrom 0 1
  have hcT : e.diagram.IsColored colT := e.colorFrom_isColored_slideReady hok 0 1
  have hmT : (ColorMatrix.of e.diagram colT).NotMono :=
    e.colorFrom_notMono_slideReady hok
  have hfM := coloring_mirror_slideReady e hok colT col hcT hmT hcMirr hmMirr
  have hfT := coloring_fraction_eq_F e hok colT hcT
    (e.colorFrom_diagonal_slideReady hok 0 1) hmT
  rw [hrot, hfM, hfT, CFValue.negInv, ← CFValue.neg_inv, CFValue.neg_neg]

/-- Uniqueness of `f` after invert: any two non-monochrome colorings of
    `T.invert` on a `slideReady` diagram have the same coloring fraction. -/
theorem coloring_fraction_unique_invert_slideReady (e : TwistExpr)
    (hok : e.slideReady) (col col' : Nat → Int)
    (hc : e.diagram.invert.IsColored col)
    (hc' : e.diagram.invert.IsColored col')
    (hm : (ColorMatrix.of e.diagram.invert col).NotMono)
    (hm' : (ColorMatrix.of e.diagram.invert col').NotMono) :
    (ColorMatrix.of e.diagram.invert col).fraction =
      (ColorMatrix.of e.diagram.invert col').fraction :=
  (coloring_invert_inv_any_slideReady e hok col hc hm).trans
    (coloring_invert_inv_any_slideReady e hok col' hc' hm').symm

/-- If two `slideReady` twist diagrams are related by `ColoringIsotopy`,
    then *fresh* colorings of their inverted PD-codes have the same coloring
    fraction `1/F(T)`. This is the fraction-level content of
    `Isotopic.invert_cong` on this class. It does not add `invert_cong` to
    `ColoringIsotopy` (colorings are not transported across `switch`). -/
theorem coloring_invert_cong_slideReady {e e' : TwistExpr}
    (hok : e.slideReady) (hok' : e'.slideReady)
    (h : ColoringIsotopy e.diagram e'.diagram) :
    ∃ colI colI',
      e.diagram.invert.IsColored colI ∧
      e'.diagram.invert.IsColored colI' ∧
      (ColorMatrix.of e.diagram.invert colI).NotMono ∧
      (ColorMatrix.of e'.diagram.invert colI').NotMono ∧
      (ColorMatrix.of e.diagram.invert colI).fraction =
        (ColorMatrix.of e'.diagram.invert colI').fraction := by
  obtain ⟨colI, hcI, hmI, hfI⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  obtain ⟨colI', hcI', hmI', hfI'⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e' hok'
  refine ⟨colI, colI', hcI, hcI', hmI, hmI', ?_⟩
  rw [hfI, hfI', TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom hok hok' h]


/-! ## Fraction-level `invert_add` / `invert_mul` on `slideReady` diagrams

Independent invert-uniqueness and `colorMulTop`/`colorAddOne` colorings; not
a `ColoringIsotopy` constructor. Kinks `[∞]+[±1]` are excluded.
-/

theorem TwistExpr.addRight_slideReady (e : TwistExpr) (s : CrossingSign)
    (hok : e.slideReady) : (TwistExpr.addRight e s).slideReady :=
  hok

theorem TwistExpr.mulBottom_slideReady (e : TwistExpr) (s : CrossingSign)
    (hok : e.slideReady) : (TwistExpr.mulBottom e s).slideReady :=
  hok

theorem TangleDiagram.invert_NW (T : TangleDiagram) : T.invert.NW = T.NE := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.invert_NE (T : TangleDiagram) : T.invert.NE = T.SE := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.invert_SE (T : TangleDiagram) : T.invert.SE = T.SW := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

theorem TangleDiagram.invert_SW (T : TangleDiagram) : T.invert.SW = T.NW := by
  simp [invert_eq_mirror_rotate, TangleDiagram.rotate, TangleDiagram.mirror]

/-- Any coloring of `T.invert` on a `slideReady` diagram has `DiagonalSum`. -/
theorem twist_coloring_diagonal_invert_slideReady (e : TwistExpr)
    (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.invert.IsColored col) :
    (ColorMatrix.of e.diagram.invert col).DiagonalSum := by
  have hcMirr : e.diagram.mirror.IsColored col :=
    TangleDiagram.IsColored_of_invert _ col hc
  obtain ⟨colA, hcA, hMat, _hfracA⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_slideReady e hok) col hcMirr
  have hokA : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  have hdA := twist_coloring_diagonal_slideReady e.mirror hokA colA hcA
  have hdMirr : (ColorMatrix.of e.diagram.mirror col).DiagonalSum := by
    simpa [hMat] using hdA
  have hrot :
      ColorMatrix.of e.diagram.invert col =
        (ColorMatrix.of e.diagram.mirror col).rotate := by
    simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
  simpa [hrot] using ColorMatrix.DiagonalSum.rotate hdMirr

theorem coloring_mul_invert_left_unit (s : CrossingSign) (T : TangleDiagram) :
    ColoringIsotopy ((crossingTangle s).mul T)
      ((crossingTangle s).invert.mul T) :=
  ColoringIsotopy.mul_left (ColoringIsotopy.invert_unit s)

namespace ColorMatrix

/-- Unit on top: `f([+1]*S) = 1/(1/f(S)+1)`. -/
theorem fraction_mulTop_one {a b c d : Int} (_h : a + d = b + c)
    (hm : ¬ (a = b ∧ b = d)) :
    (mk b (2 * b - a) c d).fraction =
      ((mk a b c d).fraction.inv.add 1).inv := by
  unfold fraction
  dsimp
  have hnum : (2 * b - a) - b = b - a := by ring
  have hdenEq : (2 * b - a) - d = (b - a) + (b - d) := by omega
  by_cases hd : b - d = 0
  · have hab : a ≠ b := by intro hab; exact hm ⟨hab, by omega⟩
    have ha : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hd' : (2 * b - a) - d ≠ 0 := by rwa [hdenEq, hd, add_zero]
    simp [hd, hd', CFValue.inv, CFValue.add, hnum]
    have hden0 : (2 * b - a) - d = b - a := by omega
    simp [hden0]
    have : Rat.divInt (b - a) (b - a) = 1 := by
      rw [Rat.divInt_eq_div]
      field_simp [ha]
    simp [this]
  · by_cases ha : b - a = 0
    · have hd' : (2 * b - a) - d ≠ 0 := by rwa [hdenEq, ha, zero_add]
      simp [hd, ha, hd', CFValue.inv, CFValue.add, hnum]
    · by_cases hd' : (2 * b - a) - d = 0
      · have hsum : (b - d) + (b - a) = 0 := by omega
        simp [hd, ha, hd', CFValue.inv, CFValue.add]
        rw [divInt_add_one (b - d) (b - a) ha, hsum]
        simp [Rat.divInt_eq_zero ha]
      · simp [hd, ha, hd', CFValue.inv, CFValue.add, hnum]
        rw [divInt_add_one (b - d) (b - a) ha]
        have hnz : Rat.divInt ((b - d) + (b - a)) (b - a) ≠ 0 :=
          (Rat.divInt_ne_zero ha).mpr (by omega)
        rw [if_neg hnz, Rat.inv_divInt]
        rw [add_comm (b - d) (b - a), ← hdenEq]

/-- Unit on top: `f([-1]*S) = 1/(1/f(S)-1)`. -/
theorem fraction_mulTop_negOne {a b c d : Int} (_h : a + d = b + c)
    (hm : ¬ (a = b ∧ b = d)) :
    (mk (2 * a - b) a c d).fraction =
      ((mk a b c d).fraction.inv.add (.ofInt (-1))).inv := by
  unfold fraction
  dsimp
  have hnum : a - (2 * a - b) = b - a := by ring
  by_cases hd : b - d = 0
  · have hab : a ≠ b := by intro hab; exact hm ⟨hab, by omega⟩
    have ha : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hden : a - d ≠ 0 := by omega
    simp [hd, hden, CFValue.inv, CFValue.add, CFValue.ofInt, hnum]
    have hden' : a - d = -(b - a) := by omega
    rw [hden', Rat.divInt_neg]
    simp [Rat.divInt_eq_div, ha]
    have hz : (b : Rat) - a ≠ 0 := by exact_mod_cast ha
    field_simp
    ring
  · by_cases hb : a - d = 0
    · have ha : b - a ≠ 0 := by intro hz; omega
      have hsum : (b - d) - (b - a) = 0 := by omega
      simp [hd, hb, ha, CFValue.inv, CFValue.add, CFValue.ofInt, hnum]
      rw [divInt_sub_one _ _ ha, hsum]
      simp [Rat.divInt_eq_zero ha]
    · by_cases ha : b - a = 0
      · simp [hd, hb, ha, CFValue.inv, CFValue.add, CFValue.ofInt, hnum]
      · have hsum : (b - d) - (b - a) = a - d := by omega
        simp [hd, hb, ha, CFValue.inv, CFValue.add, CFValue.ofInt, hnum]
        rw [divInt_sub_one _ _ ha, hsum]
        have hnz : Rat.divInt (a - d) (b - a) ≠ 0 :=
          (Rat.divInt_ne_zero ha).mpr hb
        rw [if_neg hnz, Rat.inv_divInt]

end ColorMatrix

theorem coloring_fraction_mulTop_one (S : TangleDiagram) (colS : Nat → Int)
    (hcS : S.IsColored colS)
    (hdiagS : (ColorMatrix.of S colS).DiagonalSum)
    (hmS : (ColorMatrix.of S colS).NotMono) :
    (one.mul S).IsColored (colorMulTopOne S colS) ∧
      (ColorMatrix.of (one.mul S) (colorMulTopOne S colS)).NotMono ∧
      (ColorMatrix.of (one.mul S) (colorMulTopOne S colS)).fraction =
        ((ColorMatrix.of S colS).fraction.inv.add 1).inv := by
  refine ⟨IsColored_colorMulTopOne S colS hcS, ?_, ?_⟩
  · rw [ColorMatrix.of_colorMulTopOne]
    intro hmono
    simp [ColorMatrix.NotMono, ColorMatrix.DiagonalSum, ColorMatrix.of] at hmS hdiagS hmono
    omega
  · rw [ColorMatrix.of_colorMulTopOne]
    exact ColorMatrix.fraction_mulTop_one
      (by simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiagS)
      (by simpa [ColorMatrix.NotMono, ColorMatrix.of] using hmS)

theorem coloring_fraction_mulTop_negOne (S : TangleDiagram) (colS : Nat → Int)
    (hcS : S.IsColored colS)
    (hdiagS : (ColorMatrix.of S colS).DiagonalSum)
    (hmS : (ColorMatrix.of S colS).NotMono) :
    (negOne.mul S).IsColored (colorMulTopNegOne S colS) ∧
      (ColorMatrix.of (negOne.mul S) (colorMulTopNegOne S colS)).NotMono ∧
      (ColorMatrix.of (negOne.mul S) (colorMulTopNegOne S colS)).fraction =
        ((ColorMatrix.of S colS).fraction.inv.add (.ofInt (-1))).inv := by
  refine ⟨IsColored_colorMulTopNegOne S colS hcS, ?_, ?_⟩
  · rw [ColorMatrix.of_colorMulTopNegOne]
    intro hmono
    simp [ColorMatrix.NotMono, ColorMatrix.DiagonalSum, ColorMatrix.of] at hmS hdiagS hmono
    omega
  · rw [ColorMatrix.of_colorMulTopNegOne]
    exact ColorMatrix.fraction_mulTop_negOne
      (by simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdiagS)
      (by simpa [ColorMatrix.NotMono, ColorMatrix.of] using hmS)

/-- Fresh colorings of `(e+[s])ⁱ` and of `[s]ⁱ * eⁱ` on a `slideReady`
    diagram with non-kink right ports. Not a `ColoringIsotopy`. -/
theorem coloring_invert_add_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) (_hne : e.diagram.NE ≠ e.diagram.SE) :
    ∃ colL colR,
      ((e.diagram.add (crossingTangle s)).invert).IsColored colL ∧
      (((crossingTangle s).invert.mul e.diagram.invert)).IsColored colR ∧
      (ColorMatrix.of (e.diagram.add (crossingTangle s)).invert colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).invert.mul e.diagram.invert)
        colR).NotMono ∧
      (ColorMatrix.of (e.diagram.add (crossingTangle s)).invert colL).fraction =
        (ColorMatrix.of ((crossingTangle s).invert.mul e.diagram.invert)
          colR).fraction := by
  have hokL : (TwistExpr.addRight e s).slideReady :=
    TwistExpr.addRight_slideReady e s hok
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom (.addRight e s) hokL
  obtain ⟨colI, hcI, hmI, hfI⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  have hdI := twist_coloring_diagonal_invert_slideReady e hok colI hcI
  have hstep : ColoringIsotopy
      ((crossingTangle s).mul e.diagram.invert)
      ((crossingTangle s).invert.mul e.diagram.invert) :=
    coloring_mul_invert_left_unit s _
  cases s with
  | pos =>
    obtain ⟨hcM, hmM, hfM⟩ :=
      coloring_fraction_mulTop_one e.diagram.invert colI hcI hdI hmI
    have hcM' :
        ((crossingTangle .pos).mul e.diagram.invert).IsColored
          (colorMulTopOne e.diagram.invert colI) := by
      simpa [crossingTangle] using hcM
    obtain ⟨colR, hcR, hMat, hfrac⟩ :=
      coloring_fraction_ColoringIsotopy hstep
        (colorMulTopOne e.diagram.invert colI) hcM'
    refine ⟨colL, colR, hcL, hcR, hmL, ?_, ?_⟩
    · have hEq := hMat
      simp [crossingTangle] at hEq hmM ⊢
      exact hEq ▸ hmM
    · have hfR :
          (ColorMatrix.of ((crossingTangle .pos).invert.mul e.diagram.invert)
            colR).fraction =
            ((ColorMatrix.of e.diagram.invert colI).fraction.inv.add 1).inv := by
        simpa [crossingTangle] using hfrac.trans hfM
      change (ColorMatrix.of (e.addRight CrossingSign.pos).diagram.invert
          colL).fraction =
        (ColorMatrix.of ((crossingTangle CrossingSign.pos).invert.mul
          e.diagram.invert) colR).fraction
      rw [hfL, hfR, hfI]
      simp [TwistExpr.toStandard, StandardExpr.addRight_fraction,
        CrossingSign.cfValue, CFValue.inv_inv]
  | neg =>
    obtain ⟨hcM, hmM, hfM⟩ :=
      coloring_fraction_mulTop_negOne e.diagram.invert colI hcI hdI hmI
    have hcM' :
        ((crossingTangle .neg).mul e.diagram.invert).IsColored
          (colorMulTopNegOne e.diagram.invert colI) := by
      simpa [crossingTangle] using hcM
    obtain ⟨colR, hcR, hMat, hfrac⟩ :=
      coloring_fraction_ColoringIsotopy hstep
        (colorMulTopNegOne e.diagram.invert colI) hcM'
    refine ⟨colL, colR, hcL, hcR, hmL, ?_, ?_⟩
    · have hEq := hMat
      simp [crossingTangle] at hEq hmM ⊢
      exact hEq ▸ hmM
    · have hfR :
          (ColorMatrix.of ((crossingTangle .neg).invert.mul e.diagram.invert)
            colR).fraction =
            ((ColorMatrix.of e.diagram.invert colI).fraction.inv.add
              (.ofInt (-1))).inv := by
        simpa [crossingTangle] using hfrac.trans hfM
      change (ColorMatrix.of (e.addRight CrossingSign.neg).diagram.invert
          colL).fraction =
        (ColorMatrix.of ((crossingTangle CrossingSign.neg).invert.mul
          e.diagram.invert) colR).fraction
      rw [hfL, hfR, hfI]
      simp [TwistExpr.toStandard, StandardExpr.addRight_fraction,
        CrossingSign.cfValue, CFValue.inv_inv]

/-- Fresh colorings of `(e*[s])ⁱ` and of `eⁱ + [s]ⁱ` on a `slideReady`
    diagram. Not a `ColoringIsotopy`. -/
theorem coloring_invert_mul_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) :
    ∃ colL colR,
      ((e.diagram.mul (crossingTangle s)).invert).IsColored colL ∧
      ((e.diagram.invert.add (crossingTangle s).invert)).IsColored colR ∧
      (ColorMatrix.of (e.diagram.mul (crossingTangle s)).invert colL).NotMono ∧
      (ColorMatrix.of (e.diagram.invert.add (crossingTangle s).invert)
        colR).NotMono ∧
      (ColorMatrix.of (e.diagram.mul (crossingTangle s)).invert colL).fraction =
        (ColorMatrix.of (e.diagram.invert.add (crossingTangle s).invert)
          colR).fraction := by
  have hokL : (TwistExpr.mulBottom e s).slideReady :=
    TwistExpr.mulBottom_slideReady e s hok
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom (.mulBottom e s) hokL
  obtain ⟨colI, hcI, hmI, hfI⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  have hdI := twist_coloring_diagonal_invert_slideReady e hok colI hcI
  have hstep := coloring_add_invert_right_unit e.diagram.invert s
  cases s with
  | pos =>
    have hcA : (e.diagram.invert.add one).IsColored
        (colorAddOne e.diagram.invert colI) :=
      IsColored_add_one _ colI hcI
    have hM := ColorMatrix.of_add_one e.diagram.invert colI
    have hmA : (ColorMatrix.of (e.diagram.invert.add one)
        (colorAddOne e.diagram.invert colI)).NotMono := by
      rw [hM]
      intro hmono
      simp [ColorMatrix.NotMono, ColorMatrix.DiagonalSum, ColorMatrix.of]
        at hmI hdI hmono
      omega
    have hfA :
        (ColorMatrix.of (e.diagram.invert.add one)
          (colorAddOne e.diagram.invert colI)).fraction =
          (ColorMatrix.of e.diagram.invert colI).fraction.add 1 := by
      rw [hM]
      exact ColorMatrix.fraction_add_one
        (a := colI e.diagram.invert.NW) (b := colI e.diagram.invert.NE)
        (c := colI e.diagram.invert.SW) (d := colI e.diagram.invert.SE)
        (by simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdI)
    have hcA' : (e.diagram.invert.add (crossingTangle .pos)).IsColored
        (colorAddOne e.diagram.invert colI) := by
      simpa [crossingTangle] using hcA
    obtain ⟨colR, hcR, hMat, hfrac⟩ :=
      coloring_fraction_ColoringIsotopy hstep
        (colorAddOne e.diagram.invert colI) hcA'
    refine ⟨colL, colR, hcL, hcR, hmL, ?_, ?_⟩
    · have hEq := hMat
      simp [crossingTangle] at hEq hmA ⊢
      exact hEq ▸ hmA
    · have hfR :
          (ColorMatrix.of (e.diagram.invert.add
            (crossingTangle .pos).invert) colR).fraction =
            (ColorMatrix.of e.diagram.invert colI).fraction.add 1 := by
        simpa [crossingTangle] using hfrac.trans hfA
      change (ColorMatrix.of (e.mulBottom CrossingSign.pos).diagram.invert
          colL).fraction =
        (ColorMatrix.of (e.diagram.invert.add
          (crossingTangle CrossingSign.pos).invert) colR).fraction
      rw [hfL, hfR, hfI]
      simp [TwistExpr.toStandard, StandardExpr.mulBottom_fraction,
        CrossingSign.cfValue, CFValue.inv_inv]
  | neg =>
    have hcA : (e.diagram.invert.add negOne).IsColored
        (colorAddNegOne e.diagram.invert colI) :=
      IsColored_add_negOne _ colI hcI
    have hM := ColorMatrix.of_add_negOne e.diagram.invert colI
    have hmA : (ColorMatrix.of (e.diagram.invert.add negOne)
        (colorAddNegOne e.diagram.invert colI)).NotMono := by
      rw [hM]
      intro hmono
      simp [ColorMatrix.NotMono, ColorMatrix.DiagonalSum, ColorMatrix.of]
        at hmI hdI hmono
      omega
    have hfA :
        (ColorMatrix.of (e.diagram.invert.add negOne)
          (colorAddNegOne e.diagram.invert colI)).fraction =
          (ColorMatrix.of e.diagram.invert colI).fraction.add
            (.ofInt (-1)) := by
      rw [hM]
      exact ColorMatrix.fraction_add_negOne
        (a := colI e.diagram.invert.NW) (b := colI e.diagram.invert.NE)
        (c := colI e.diagram.invert.SW) (d := colI e.diagram.invert.SE)
        (by simpa [ColorMatrix.DiagonalSum, ColorMatrix.of] using hdI)
    have hcA' : (e.diagram.invert.add (crossingTangle .neg)).IsColored
        (colorAddNegOne e.diagram.invert colI) := by
      simpa [crossingTangle] using hcA
    obtain ⟨colR, hcR, hMat, hfrac⟩ :=
      coloring_fraction_ColoringIsotopy hstep
        (colorAddNegOne e.diagram.invert colI) hcA'
    refine ⟨colL, colR, hcL, hcR, hmL, ?_, ?_⟩
    · have hEq := hMat
      simp [crossingTangle] at hEq hmA ⊢
      exact hEq ▸ hmA
    · have hfR :
          (ColorMatrix.of (e.diagram.invert.add
            (crossingTangle .neg).invert) colR).fraction =
            (ColorMatrix.of e.diagram.invert colI).fraction.add
              (.ofInt (-1)) := by
        simpa [crossingTangle] using hfrac.trans hfA
      change (ColorMatrix.of (e.mulBottom CrossingSign.neg).diagram.invert
          colL).fraction =
        (ColorMatrix.of (e.diagram.invert.add
          (crossingTangle CrossingSign.neg).invert) colR).fraction
      rw [hfL, hfR, hfI]
      simp [TwistExpr.toStandard, StandardExpr.mulBottom_fraction,
        CrossingSign.cfValue, CFValue.inv_inv]

/-! ## Fraction-level `mirror_cong` and Figure 14 (`transfer_odd`)

Independent colorings; not `ColoringIsotopy` constructors. Kinks with
`NW = NE` (the `[0]` family) are excluded from left-glue of `[+1]`.
-/

/-- Any non-monochrome coloring of the PD-mirror of a `slideReady` diagram
    has fraction `-F(T)`. -/
theorem coloring_mirror_any_eq_neg_F_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.mirror.IsColored col)
    (hm : (ColorMatrix.of e.diagram.mirror col).NotMono) :
    (ColorMatrix.of e.diagram.mirror col).fraction =
      e.toStandard.fraction.neg := by
  let colT := e.colorFrom 0 1
  have hcT : e.diagram.IsColored colT := e.colorFrom_isColored_slideReady hok 0 1
  have hmT : (ColorMatrix.of e.diagram colT).NotMono :=
    e.colorFrom_notMono_slideReady hok
  have hf := coloring_mirror_slideReady e hok colT col hcT hmT hc hm
  have hfT := coloring_fraction_eq_F e hok colT hcT
    (e.colorFrom_diagonal_slideReady hok 0 1) hmT
  rw [hf, hfT]

/-- If two `slideReady` diagrams are related by `ColoringIsotopy`, fresh
    colorings of their PD-mirrors have the same coloring fraction `-F`.
    Fraction-level `Isotopic.mirror_cong` on this class; not a
    `ColoringIsotopy` constructor. -/
theorem coloring_mirror_cong_slideReady {e e' : TwistExpr}
    (hok : e.slideReady) (hok' : e'.slideReady)
    (h : ColoringIsotopy e.diagram e'.diagram) :
    ∃ colM colM',
      e.diagram.mirror.IsColored colM ∧
      e'.diagram.mirror.IsColored colM' ∧
      (ColorMatrix.of e.diagram.mirror colM).NotMono ∧
      (ColorMatrix.of e'.diagram.mirror colM').NotMono ∧
      (ColorMatrix.of e.diagram.mirror colM).fraction =
        (ColorMatrix.of e'.diagram.mirror colM').fraction := by
  have hokM : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  have hokM' : e'.mirror.slideReady := TwistExpr.slideReady_mirror e' hok'
  obtain ⟨colM, hcM, hMatM, _hfracM⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_rev_slideReady e hok)
      (e.mirror.colorFrom 0 1) (e.mirror.colorFrom_isColored_slideReady hokM 0 1)
  obtain ⟨colM', hcM', hMatM', _hfracM'⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_rev_slideReady e' hok')
      (e'.mirror.colorFrom 0 1) (e'.mirror.colorFrom_isColored_slideReady hokM' 0 1)
  have hmM : (ColorMatrix.of e.diagram.mirror colM).NotMono := by
    simpa [hMatM] using e.mirror.colorFrom_notMono_slideReady hokM
  have hmM' : (ColorMatrix.of e'.diagram.mirror colM').NotMono := by
    simpa [hMatM'] using e'.mirror.colorFrom_notMono_slideReady hokM'
  refine ⟨colM, colM', hcM, hcM', hmM, hmM', ?_⟩
  have hf := coloring_mirror_any_eq_neg_F_slideReady e hok colM hcM hmM
  have hf' := coloring_mirror_any_eq_neg_F_slideReady e' hok' colM' hcM' hmM'
  rw [hf, hf', TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom hok hok' h]

theorem TwistExpr.toStandard_transfer_odd (e : TwistExpr) :
    (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).toStandard.fraction =
      (1 : CFValue).add e.toStandard.fraction.neg.inv := by
  simp [TwistExpr.toStandard, StandardExpr.addRight_fraction,
    StandardExpr.mulBottom_fraction, CrossingSign.cfValue]
  simpa [one_eq_ofInt_one] using
    CFValue.transfer_odd_value e.toStandard.fraction

/-- Any non-monochrome coloring of `T.mirror.invert` on a `slideReady`
    diagram has fraction `-1/F(T)`. Uniqueness after mirror identifies
    `f(T.mirror) = -F`, so this is `1/f(T.mirror)`; the PD-code is the
    rotate of the double mirror (`planar_mirror_mirror`). -/
theorem coloring_mirror_invert_any_eq_negInv_F_slideReady (e : TwistExpr)
    (hok : e.slideReady) (col : Nat → Int)
    (hc : e.diagram.mirror.invert.IsColored col)
    (hm : (ColorMatrix.of e.diagram.mirror.invert col).NotMono) :
    (ColorMatrix.of e.diagram.mirror.invert col).fraction =
      e.toStandard.fraction.negInv := by
  have hcMM : e.diagram.mirror.mirror.IsColored col :=
    TangleDiagram.IsColored_of_invert e.diagram.mirror col hc
  obtain ⟨colT, hcT, hMat, hfracT⟩ :=
    coloring_fraction_ColoringIsotopy
      (.isotopy (planar_mirror_mirror e.diagram)) col hcMM
  have hdT := twist_coloring_diagonal_slideReady e hok colT hcT
  have hdMM : (ColorMatrix.of e.diagram.mirror.mirror col).DiagonalSum := by
    simpa [hMat] using hdT
  have hrot :
      ColorMatrix.of e.diagram.mirror.invert col =
        (ColorMatrix.of e.diagram.mirror.mirror col).rotate := by
    simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
  have hmMM : (ColorMatrix.of e.diagram.mirror.mirror col).NotMono :=
    ColorMatrix.NotMono_of_rotate hdMM (by simpa [hrot] using hm)
  have hmT : (ColorMatrix.of e.diagram colT).NotMono := by
    simpa [hMat] using hmMM
  have hfT := coloring_fraction_eq_F e hok colT hcT hdT hmT
  have hrotF :
      (ColorMatrix.of e.diagram.mirror.invert col).fraction =
        (ColorMatrix.of e.diagram.mirror.mirror col).fraction.negInv := by
    simpa [invert_eq_mirror_rotate] using
      coloring_fraction_rotate e.diagram.mirror.mirror col hdMM hmMM
  have hokM : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  obtain ⟨colPd, hcPd, hMatPd, _⟩ :=
    coloring_fraction_ColoringIsotopy
      (coloring_mirror_diagram_rev_slideReady e hok)
      (e.mirror.colorFrom 0 1)
      (e.mirror.colorFrom_isColored_slideReady hokM 0 1)
  have hmPd : (ColorMatrix.of e.diagram.mirror colPd).NotMono := by
    simpa [hMatPd] using e.mirror.colorFrom_notMono_slideReady hokM
  have hfM := coloring_mirror_any_eq_neg_F_slideReady e hok colPd hcPd hmPd
  calc
    (ColorMatrix.of e.diagram.mirror.invert col).fraction
        = (ColorMatrix.of e.diagram.mirror.mirror col).fraction.negInv := hrotF
    _ = (ColorMatrix.of e.diagram colT).fraction.negInv := by rw [hfracT]
    _ = e.toStandard.fraction.negInv := by rw [hfT]
    _ = e.toStandard.fraction.neg.inv := by
          simp [CFValue.negInv, CFValue.neg_inv]
    _ = (ColorMatrix.of e.diagram.mirror colPd).fraction.inv := by rw [hfM]
    _ = e.toStandard.fraction.neg.inv := by rw [hfM]
    _ = e.toStandard.fraction.negInv := by
          simp [CFValue.negInv, CFValue.neg_inv]

/-- Figure 14 at the fraction level on a `slideReady` diagram with distinct
    `NW`/`NE` (not the `[0]` kink). Independent colorings of
    `(T+[-1])*[+1]` and `[+1]+(-T)ⁱ`; uniqueness after mirror supplies
    `f((-T)ⁱ) = -1/F(T)`. Not a `ColoringIsotopy`. -/
theorem coloring_transfer_odd_slideReady (e : TwistExpr) (hok : e.slideReady)
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
  have hokL : eL.slideReady :=
    TwistExpr.mulBottom_slideReady _ _ (TwistExpr.addRight_slideReady e .neg hok)
  let colL := eL.colorFrom 0 1
  have hcL : eL.diagram.IsColored colL :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hmL : (ColorMatrix.of eL.diagram colL).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hfL := coloring_fraction_eq_F eL hokL colL hcL
    (eL.colorFrom_diagonal_slideReady hokL 0 1) hmL
  let colT := e.colorFrom 0 1
  have hcT : e.diagram.IsColored colT := e.colorFrom_isColored_slideReady hok 0 1
  have hmT : (ColorMatrix.of e.diagram colT).NotMono :=
    e.colorFrom_notMono_slideReady hok
  have hdT := e.colorFrom_diagonal_slideReady hok 0 1
  obtain ⟨colMM, hcMM, hMatMM, _⟩ :=
    coloring_fraction_ColoringIsotopy
      (.isotopy (planar_mirror_mirror_rev e.diagram)) colT hcT
  have hcI : e.diagram.mirror.invert.IsColored colMM := by
    simpa [invert_eq_mirror_rotate] using coloring_rotate _ colMM hcMM
  have hdMM : (ColorMatrix.of e.diagram.mirror.mirror colMM).DiagonalSum := by
    simpa [hMatMM] using hdT
  have hmMM : (ColorMatrix.of e.diagram.mirror.mirror colMM).NotMono := by
    simpa [hMatMM] using hmT
  have hrot :
      ColorMatrix.of e.diagram.mirror.invert colMM =
        (ColorMatrix.of e.diagram.mirror.mirror colMM).rotate := by
    simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
  have hmI : (ColorMatrix.of e.diagram.mirror.invert colMM).NotMono := by
    simpa [hrot] using ColorMatrix.NotMono_rotate hdMM hmMM
  have hneS : e.diagram.mirror.invert.NW ≠ e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    exact hports.symm
  have hdiagS : (ColorMatrix.of e.diagram.mirror.invert colMM).DiagonalSum := by
    simpa [hrot] using ColorMatrix.DiagonalSum.rotate hdMM
  have hcolS : colMM e.diagram.mirror.invert.NW ≠
      colMM e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    change (ColorMatrix.of e.diagram.mirror.mirror colMM).NE ≠
      (ColorMatrix.of e.diagram.mirror.mirror colMM).NW
    have hNE := congrArg ColorMatrix.NE hMatMM
    have hNW := congrArg ColorMatrix.NW hMatMM
    have hne' :
        (ColorMatrix.of e.diagram colT).NE ≠
          (ColorMatrix.of e.diagram colT).NW := hne.symm
    exact hNE.trans_ne (hne'.trans_eq hNW.symm)
  obtain ⟨colR, hcR, hmR, hfR⟩ :=
    coloring_fraction_one_add e.diagram.mirror.invert colMM hcI hneS hdiagS hcolS
  have hfI :=
    coloring_mirror_invert_any_eq_negInv_F_slideReady e hok colMM hcI hmI
  refine ⟨colL, colR, ?_, hcR, ?_, hmR, ?_⟩
  · simpa [eL, TwistExpr.diagram, crossingTangle] using hcL
  · simpa [eL, TwistExpr.diagram, crossingTangle] using hmL
  · have hLd :
        ColorMatrix.of ((e.diagram.add RationalTangles.negOne).mul
          RationalTangles.one) colL =
          ColorMatrix.of eL.diagram colL := by
      simp [eL, TwistExpr.diagram, crossingTangle]
    rw [hLd, hfL, hfR, hfI, TwistExpr.toStandard_transfer_odd]
    simp [CFValue.negInv, CFValue.neg_inv]

theorem TwistExpr.toStandard_transfer_odd_neg (e : TwistExpr) :
    (TwistExpr.mulBottom (TwistExpr.addRight e .pos) .neg).toStandard.fraction =
      (CFValue.ofInt (-1)).add e.toStandard.fraction.neg.inv := by
  simp [TwistExpr.toStandard, StandardExpr.addRight_fraction,
    StandardExpr.mulBottom_fraction, CrossingSign.cfValue]
  simpa [one_eq_ofInt_one] using
    CFValue.transfer_odd_neg_value e.toStandard.fraction

/-- Switched Figure 14 at the fraction level on a `slideReady` diagram
    with distinct `NW`/`NE`. Independent colorings of `(T+[+1])*[-1]`
    and `[-1]+(-T)ⁱ`; uniqueness after mirror supplies `f((-T)ⁱ)=-1/F`.
    Not a `ColoringIsotopy`. -/
theorem coloring_transfer_odd_neg_slideReady (e : TwistExpr) (hok : e.slideReady)
    (hports : e.diagram.NW ≠ e.diagram.NE)
    (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
    ∃ colL colR,
      ((e.diagram.add RationalTangles.one).mul RationalTangles.negOne).IsColored
        colL ∧
      (RationalTangles.negOne.add e.diagram.mirror.invert).IsColored colR ∧
      (ColorMatrix.of ((e.diagram.add RationalTangles.one).mul
        RationalTangles.negOne) colL).NotMono ∧
      (ColorMatrix.of (RationalTangles.negOne.add e.diagram.mirror.invert)
        colR).NotMono ∧
      (ColorMatrix.of ((e.diagram.add RationalTangles.one).mul
        RationalTangles.negOne) colL).fraction =
        (ColorMatrix.of (RationalTangles.negOne.add e.diagram.mirror.invert)
          colR).fraction := by
  let eL : TwistExpr := .mulBottom (.addRight e .pos) .neg
  have hokL : eL.slideReady :=
    TwistExpr.mulBottom_slideReady _ _ (TwistExpr.addRight_slideReady e .pos hok)
  let colL := eL.colorFrom 0 1
  have hcL : eL.diagram.IsColored colL :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hmL : (ColorMatrix.of eL.diagram colL).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hfL := coloring_fraction_eq_F eL hokL colL hcL
    (eL.colorFrom_diagonal_slideReady hokL 0 1) hmL
  let colT := e.colorFrom 0 1
  have hcT : e.diagram.IsColored colT := e.colorFrom_isColored_slideReady hok 0 1
  have hmT : (ColorMatrix.of e.diagram colT).NotMono :=
    e.colorFrom_notMono_slideReady hok
  have hdT := e.colorFrom_diagonal_slideReady hok 0 1
  obtain ⟨colMM, hcMM, hMatMM, _⟩ :=
    coloring_fraction_ColoringIsotopy
      (.isotopy (planar_mirror_mirror_rev e.diagram)) colT hcT
  have hcI : e.diagram.mirror.invert.IsColored colMM := by
    simpa [invert_eq_mirror_rotate] using coloring_rotate _ colMM hcMM
  have hdMM : (ColorMatrix.of e.diagram.mirror.mirror colMM).DiagonalSum := by
    simpa [hMatMM] using hdT
  have hmMM : (ColorMatrix.of e.diagram.mirror.mirror colMM).NotMono := by
    simpa [hMatMM] using hmT
  have hrot :
      ColorMatrix.of e.diagram.mirror.invert colMM =
        (ColorMatrix.of e.diagram.mirror.mirror colMM).rotate := by
    simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
  have hmI : (ColorMatrix.of e.diagram.mirror.invert colMM).NotMono := by
    simpa [hrot] using ColorMatrix.NotMono_rotate hdMM hmMM
  have hneS : e.diagram.mirror.invert.NW ≠ e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    exact hports.symm
  have hdiagS : (ColorMatrix.of e.diagram.mirror.invert colMM).DiagonalSum := by
    simpa [hrot] using ColorMatrix.DiagonalSum.rotate hdMM
  have hcolS : colMM e.diagram.mirror.invert.NW ≠
      colMM e.diagram.mirror.invert.SW := by
    rw [TangleDiagram.mirror_invert_NW, TangleDiagram.mirror_invert_SW]
    change (ColorMatrix.of e.diagram.mirror.mirror colMM).NE ≠
      (ColorMatrix.of e.diagram.mirror.mirror colMM).NW
    have hNE := congrArg ColorMatrix.NE hMatMM
    have hNW := congrArg ColorMatrix.NW hMatMM
    have hne' :
        (ColorMatrix.of e.diagram colT).NE ≠
          (ColorMatrix.of e.diagram colT).NW := hne.symm
    exact hNE.trans_ne (hne'.trans_eq hNW.symm)
  obtain ⟨colR, hcR, hmR, hfR⟩ :=
    coloring_fraction_negOne_add e.diagram.mirror.invert colMM hcI hneS hdiagS hcolS
  have hfI :=
    coloring_mirror_invert_any_eq_negInv_F_slideReady e hok colMM hcI hmI
  refine ⟨colL, colR, ?_, hcR, ?_, hmR, ?_⟩
  · simpa [eL, TwistExpr.diagram, crossingTangle] using hcL
  · simpa [eL, TwistExpr.diagram, crossingTangle] using hmL
  · have hLd :
        ColorMatrix.of ((e.diagram.add RationalTangles.one).mul
          RationalTangles.negOne) colL =
          ColorMatrix.of eL.diagram colL := by
      simp [eL, TwistExpr.diagram, crossingTangle]
    rw [hLd, hfL, hfR, hfI, TwistExpr.toStandard_transfer_odd_neg]
    simp [CFValue.negInv, CFValue.neg_inv]

/-! ## Restricted `rot180` and Figure 5 slides

Planar 180° cycles endpoints. Under `DiagonalSum`, `coloring_rot180_diagonal`
restores disc colors, so `f` is unchanged (two 90° rotations: `(-1/f)` twice
is `f`, not the 90° identity `f(Tʳ)=-1/f(T)`). Uniqueness of
`f=F` on the original `slideReady` diagram identifies every non-monochrome
coloring of `T.rot180`. Figure 5 slides reuse `coloring_flype_slide_*`.
On a unit right-sum or bottom-product, the same uniqueness identifies
`f` of `(T+S).rot180` with a glued coloring of `S.rot180+T.rot180`
(and the product analogue). The rotated general summand is not a
`TwistExpr` diagram, so this is not a `SlideReadyIsotopy` constructor.
-/

theorem ColorMatrix.of_rot180 (T : TangleDiagram) (col : Nat → Int) :
    ColorMatrix.of T.rot180 col = (ColorMatrix.of T col).rotate.rotate := by
  simp [ColorMatrix.of, ColorMatrix.rotate, TangleDiagram.rot180]

theorem ColorMatrix.NotMono_of_rot180 (T : TangleDiagram) (col : Nat → Int)
    (hd : (ColorMatrix.of T col).DiagonalSum)
    (hm : (ColorMatrix.of T col).NotMono) :
    (ColorMatrix.of T.rot180 col).NotMono := by
  rw [ColorMatrix.of_rot180]
  exact ColorMatrix.NotMono_rotate (ColorMatrix.DiagonalSum.rotate hd)
    (ColorMatrix.NotMono_rotate hd hm)

theorem CFValue.negInv_negInv (x : CFValue) : x.negInv.negInv = x := by
  simp [CFValue.negInv, CFValue.neg_inv, CFValue.inv_inv, CFValue.neg_neg]

/-- Any non-monochrome coloring of `T.rot180` on a `slideReady` diagram has
    fraction `F(T)`. Disc colors need not match those of `T`; uniqueness of
    `f` on `T` after `coloring_rot180_diagonal` identifies the value. -/
theorem coloring_rot180_any_eq_F_slideReady (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.rot180.IsColored col)
    (hm : (ColorMatrix.of e.diagram.rot180 col).NotMono) :
    (ColorMatrix.of e.diagram.rot180 col).fraction = e.toStandard.fraction := by
  have hcT : e.diagram.IsColored col := by
    simpa [rot180_rot180] using IsColored_rot180 e.diagram.rot180 col hc
  have hdT := twist_coloring_diagonal_slideReady e hok col hcT
  have hdiag : (ColorMatrix.of e.diagram.rot180 col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_rot180 e.diagram col hdT
  obtain ⟨col', hc', hs⟩ :=
    coloring_rot180_diagonal e.diagram.rot180 col hc hdiag
  have hc'T : e.diagram.IsColored col' := by
    simpa [rot180_rot180] using hc'
  have hM : ColorMatrix.of e.diagram col' = ColorMatrix.of e.diagram.rot180 col :=
    ColorMatrix.of_sameEndpoint (by simpa [rot180_rot180] using hs)
  have hmT : (ColorMatrix.of e.diagram col').NotMono := by
    simpa [hM] using hm
  have hd' : (ColorMatrix.of e.diagram col').DiagonalSum := by
    simpa [hM] using hdiag
  have hf := coloring_fraction_eq_F e hok col' hc'T hd' hmT
  exact (congrArg ColorMatrix.fraction hM.symm).trans hf

/-- Same statement on `rightBottom`, written with algebraic `F`. -/
theorem coloring_rot180_any_eq_F_rightBottom (e : TwistExpr) (hrb : e.rightBottom)
    (col : Nat → Int)
    (hc : e.diagram.rot180.IsColored col)
    (hm : (ColorMatrix.of e.diagram.rot180 col).NotMono) :
    (ColorMatrix.of e.diagram.rot180 col).fraction = e.fraction := by
  have hok := TwistExpr.rightBottom_slideReady e hrb
  have hf := coloring_rot180_any_eq_F_slideReady e hok col hc hm
  exact hf.trans (TwistExpr.fraction_eq_toStandard_rightBottom e hrb).symm

/-- Uniqueness of `f` after `rot180`: any two non-monochrome colorings of
    `T.rot180` on a `slideReady` diagram have the same coloring fraction. -/
theorem coloring_fraction_unique_rot180_slideReady (e : TwistExpr)
    (hok : e.slideReady) (col col' : Nat → Int)
    (hc : e.diagram.rot180.IsColored col)
    (hc' : e.diagram.rot180.IsColored col')
    (hm : (ColorMatrix.of e.diagram.rot180 col).NotMono)
    (hm' : (ColorMatrix.of e.diagram.rot180 col').NotMono) :
    (ColorMatrix.of e.diagram.rot180 col).fraction =
      (ColorMatrix.of e.diagram.rot180 col').fraction :=
  (coloring_rot180_any_eq_F_slideReady e hok col hc hm).trans
    (coloring_rot180_any_eq_F_slideReady e hok col' hc' hm').symm

/-- A coloring of `T.rot180` with the same color matrix (hence `f=F`) as a
    `slideReady` coloring of `T`. -/
theorem coloring_rot180_slideReady (e : TwistExpr) (hok : e.slideReady) :
    ∃ col col',
      e.diagram.IsColored col ∧ e.diagram.rot180.IsColored col' ∧
      (ColorMatrix.of e.diagram col).NotMono ∧
      (ColorMatrix.of e.diagram.rot180 col').NotMono ∧
      ColorMatrix.of e.diagram.rot180 col' = ColorMatrix.of e.diagram col ∧
      (ColorMatrix.of e.diagram.rot180 col').fraction =
        e.toStandard.fraction := by
  let col := e.colorFrom 0 1
  have hc : e.diagram.IsColored col := e.colorFrom_isColored_slideReady hok 0 1
  have hm : (ColorMatrix.of e.diagram col).NotMono :=
    e.colorFrom_notMono_slideReady hok
  have hd := e.colorFrom_diagonal_slideReady hok 0 1
  have hf := coloring_fraction_eq_F e hok col hc hd hm
  obtain ⟨col', hc', hM, hfrac⟩ :=
    coloring_fraction_rot180_diagonal e.diagram col hc hd
  exact ⟨col, col', hc, hc', hm, hM ▸ hm, hM, hfrac.trans hf⟩

/-- Restricted Figure 5 slide on a `slideReady` summand. -/
theorem coloring_flype_slide_add_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) (hne : e.diagram.NW ≠ e.diagram.SW) :
    ∃ colL colR,
      ((crossingTangle s).add e.diagram).IsColored colL ∧
      (e.diagram.rot180.add (crossingTangle s)).IsColored colR ∧
      (ColorMatrix.of ((crossingTangle s).add e.diagram) colL).NotMono ∧
      (ColorMatrix.of (e.diagram.rot180.add (crossingTangle s)) colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).add e.diagram) colL).fraction =
        (ColorMatrix.of (e.diagram.rot180.add (crossingTangle s)) colR).fraction ∧
      (ColorMatrix.of ((crossingTangle s).add e.diagram) colL).fraction =
        (TwistExpr.addLeft e s).toStandard.fraction := by
  let eL : TwistExpr := .addLeft e s
  have hokL : eL.slideReady := ⟨hne, hok⟩
  let colL := eL.colorFrom 0 1
  have hcL : eL.diagram.IsColored colL :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hmL : (ColorMatrix.of eL.diagram colL).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hdL := eL.colorFrom_diagonal_slideReady hokL 0 1
  have hfL := coloring_fraction_eq_F eL hokL colL hcL hdL hmL
  have hcL' : ((crossingTangle s).add e.diagram).IsColored colL := by
    simpa [eL, TwistExpr.diagram] using hcL
  have hdL' : (ColorMatrix.of ((crossingTangle s).add e.diagram) colL).DiagonalSum := by
    simpa [eL, TwistExpr.diagram] using hdL
  obtain ⟨colR, hcR, hs⟩ :=
    coloring_flype_slide_add s e.diagram colL hcL' hne hdL'
  have hM := ColorMatrix.of_sameEndpoint hs
  have hLd :
      ColorMatrix.of ((crossingTangle s).add e.diagram) colL =
        ColorMatrix.of eL.diagram colL := by
    simp [eL, TwistExpr.diagram]
  refine ⟨colL, colR, hcL', hcR, ?_, ?_, ?_, ?_⟩
  · simpa [hLd] using hmL
  · simpa [hM, hLd] using hmL
  · rw [hM]
  · rw [hLd, hfL]

/-- Restricted Figure 5 slide on a `slideReady` factor. -/
theorem coloring_flype_slide_mul_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) (hne : e.diagram.NW ≠ e.diagram.NE) :
    ∃ colL colR,
      ((crossingTangle s).mul e.diagram).IsColored colL ∧
      (e.diagram.rot180.mul (crossingTangle s)).IsColored colR ∧
      (ColorMatrix.of ((crossingTangle s).mul e.diagram) colL).NotMono ∧
      (ColorMatrix.of (e.diagram.rot180.mul (crossingTangle s)) colR).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).mul e.diagram) colL).fraction =
        (ColorMatrix.of (e.diagram.rot180.mul (crossingTangle s)) colR).fraction ∧
      (ColorMatrix.of ((crossingTangle s).mul e.diagram) colL).fraction =
        (TwistExpr.mulTop e s).toStandard.fraction := by
  let eL : TwistExpr := .mulTop e s
  have hokL : eL.slideReady := ⟨hne, hok⟩
  let colL := eL.colorFrom 0 1
  have hcL : eL.diagram.IsColored colL :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hmL : (ColorMatrix.of eL.diagram colL).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hdL := eL.colorFrom_diagonal_slideReady hokL 0 1
  have hfL := coloring_fraction_eq_F eL hokL colL hcL hdL hmL
  have hcL' : ((crossingTangle s).mul e.diagram).IsColored colL := by
    simpa [eL, TwistExpr.diagram] using hcL
  have hdL' : (ColorMatrix.of ((crossingTangle s).mul e.diagram) colL).DiagonalSum := by
    simpa [eL, TwistExpr.diagram] using hdL
  obtain ⟨colR, hcR, hs⟩ :=
    coloring_flype_slide_mul s e.diagram colL hcL' hne hdL'
  have hM := ColorMatrix.of_sameEndpoint hs
  have hLd :
      ColorMatrix.of ((crossingTangle s).mul e.diagram) colL =
        ColorMatrix.of eL.diagram colL := by
    simp [eL, TwistExpr.diagram]
  refine ⟨colL, colR, hcL', hcR, ?_, ?_, ?_, ?_⟩
  · simpa [hLd] using hmL
  · simpa [hM, hLd] using hmL
  · rw [hM]
  · rw [hLd, hfL]

/-- Fraction-level `rot180_add` on a `slideReady` right unit sum:
    `(T+[±1]).rot180` and `[±1].rot180 + T.rot180` have the same `f`,
    which equals `F`. The rotated summand is not a `TwistExpr` diagram,
    so this is not a `SlideReadyIsotopy` constructor. -/
theorem coloring_rot180_add_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) :
    ∃ colL colR,
      (e.diagram.add (crossingTangle s)).rot180.IsColored colL ∧
      ((crossingTangle s).rot180.add e.diagram.rot180).IsColored colR ∧
      (ColorMatrix.of (e.diagram.add (crossingTangle s)).rot180 colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).rot180.add e.diagram.rot180)
        colR).NotMono ∧
      (ColorMatrix.of (e.diagram.add (crossingTangle s)).rot180 colL).fraction =
        (ColorMatrix.of ((crossingTangle s).rot180.add e.diagram.rot180)
          colR).fraction ∧
      (ColorMatrix.of (e.diagram.add (crossingTangle s)).rot180 colL).fraction =
        (TwistExpr.addRight e s).toStandard.fraction := by
  let eL : TwistExpr := .addRight e s
  have hokL : eL.slideReady := TwistExpr.addRight_slideReady e s hok
  let T := e.diagram
  let U := crossingTangle s
  let col := eL.colorFrom 0 1
  have hc : eL.diagram.IsColored col :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hm : (ColorMatrix.of eL.diagram col).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hd := eL.colorFrom_diagonal_slideReady hokL 0 1
  have hcSum : (T.add U).IsColored col := by
    simpa [eL, TwistExpr.diagram] using hc
  have hcL : (T.add U).rot180.IsColored col := IsColored_rot180 _ col hcSum
  have hmL : (ColorMatrix.of (T.add U).rot180 col).NotMono := by
    simpa [eL, TwistExpr.diagram] using ColorMatrix.NotMono_of_rot180 eL.diagram col hd hm
  have hfL := coloring_rot180_any_eq_F_slideReady eL hokL col
    (by simpa [eL, TwistExpr.diagram] using hcL)
    (by simpa [eL, TwistExpr.diagram] using hmL)
  let colU := colorAddRight T U col
  have hT : T.IsColored col := IsColored_add_left hcSum
  have hU : U.IsColored colU := IsColored_add_right hcSum
  have hT180 : T.rot180.IsColored col := IsColored_rot180 T col hT
  have hU180 : U.rot180.IsColored colU := IsColored_rot180 U colU hU
  have glueNE : colU U.rot180.NE = col T.rot180.NW := by
    change colU U.SW = col T.SE
    exact (colorAddRight_SW T U col).resolve_right (crossingTangle_NW_ne_SW s)
  have glueSE : colU U.rot180.SE = col T.rot180.SW ∨ T.rot180.NW = T.rot180.SW := by
    by_cases hports : T.rot180.NW = T.rot180.SW
    · exact Or.inr hports
    · left
      change colU U.NW = col T.NE
      exact colorAddRight_NW T U col
  let colR := colorGlueAdd U.rot180 T.rot180 colU col
  have hcR : (U.rot180.add T.rot180).IsColored colR :=
    IsColored_colorGlueAdd U.rot180 T.rot180 colU col hU180 hT180 glueNE glueSE
  have hNW : colR (U.rot180.add T.rot180).NW = col (T.add U).rot180.NW := by
    change colR U.rot180.NW = col (T.add U).SE
    dsimp [colR]
    rw [colorGlueAdd_of_le U.rot180 T.rot180 colU col (maxArc_ge_NW U.rot180)]
    exact colorAddRight_SE T U col
  have hNE : colR (U.rot180.add T.rot180).NE = col (T.add U).rot180.NE := by
    have h1 : colR (U.rot180.add T.rot180).NE = col T.rot180.NE := by
      dsimp [colR]
      rw [add_NE]
      exact colorGlueAdd_comp_shift U.rot180 T.rot180 colU col glueNE glueSE
        T.rot180.NE
    rw [h1]
    rfl
  have hSW : colR (U.rot180.add T.rot180).SW = col (T.add U).rot180.SW := by
    change colR U.rot180.SW = col (T.add U).NE
    dsimp [colR]
    rw [colorGlueAdd_of_le U.rot180 T.rot180 colU col (maxArc_ge_SW U.rot180)]
    exact colorAddRight_NE T U col
  have hSE : colR (U.rot180.add T.rot180).SE = col (T.add U).rot180.SE := by
    have h1 : colR (U.rot180.add T.rot180).SE = col T.rot180.SE := by
      dsimp [colR]
      rw [add_SE]
      exact colorGlueAdd_comp_shift U.rot180 T.rot180 colU col glueNE glueSE
        T.rot180.SE
    rw [h1]
    rfl
  have hMat :
      ColorMatrix.of (U.rot180.add T.rot180) colR =
        ColorMatrix.of (T.add U).rot180 col := by
    simp [ColorMatrix.of, hNW, hNE, hSW, hSE]
  have hmR : (ColorMatrix.of (U.rot180.add T.rot180) colR).NotMono := by
    simpa [hMat] using hmL
  have hfR :
      (ColorMatrix.of (U.rot180.add T.rot180) colR).fraction =
        eL.toStandard.fraction := by
    rw [hMat]
    simpa [eL, TwistExpr.diagram] using hfL
  refine ⟨col, colR, hcL, hcR, hmL, hmR, ?_, ?_⟩
  · simpa [eL, TwistExpr.diagram] using
      (show (ColorMatrix.of (T.add U).rot180 col).fraction =
          (ColorMatrix.of (U.rot180.add T.rot180) colR).fraction from
        (hfL.trans hfR.symm))
  · simpa [eL, TwistExpr.diagram] using hfL

/-- Fraction-level `rot180_mul` on a `slideReady` bottom unit product. -/
theorem coloring_rot180_mul_slideReady (e : TwistExpr) (hok : e.slideReady)
    (s : CrossingSign) :
    ∃ colL colR,
      (e.diagram.mul (crossingTangle s)).rot180.IsColored colL ∧
      ((crossingTangle s).rot180.mul e.diagram.rot180).IsColored colR ∧
      (ColorMatrix.of (e.diagram.mul (crossingTangle s)).rot180 colL).NotMono ∧
      (ColorMatrix.of ((crossingTangle s).rot180.mul e.diagram.rot180)
        colR).NotMono ∧
      (ColorMatrix.of (e.diagram.mul (crossingTangle s)).rot180 colL).fraction =
        (ColorMatrix.of ((crossingTangle s).rot180.mul e.diagram.rot180)
          colR).fraction ∧
      (ColorMatrix.of (e.diagram.mul (crossingTangle s)).rot180 colL).fraction =
        (TwistExpr.mulBottom e s).toStandard.fraction := by
  let eL : TwistExpr := .mulBottom e s
  have hokL : eL.slideReady := TwistExpr.mulBottom_slideReady e s hok
  let T := e.diagram
  let U := crossingTangle s
  let col := eL.colorFrom 0 1
  have hc : eL.diagram.IsColored col :=
    eL.colorFrom_isColored_slideReady hokL 0 1
  have hm : (ColorMatrix.of eL.diagram col).NotMono :=
    eL.colorFrom_notMono_slideReady hokL
  have hd := eL.colorFrom_diagonal_slideReady hokL 0 1
  have hcProd : (T.mul U).IsColored col := by
    simpa [eL, TwistExpr.diagram] using hc
  have hcL : (T.mul U).rot180.IsColored col := IsColored_rot180 _ col hcProd
  have hmL : (ColorMatrix.of (T.mul U).rot180 col).NotMono := by
    simpa [eL, TwistExpr.diagram] using ColorMatrix.NotMono_of_rot180 eL.diagram col hd hm
  have hfL := coloring_rot180_any_eq_F_slideReady eL hokL col
    (by simpa [eL, TwistExpr.diagram] using hcL)
    (by simpa [eL, TwistExpr.diagram] using hmL)
  let colU := colorMulBottom T U col
  have hT : T.IsColored col := IsColored_mul_top hcProd
  have hU : U.IsColored colU := IsColored_mul_bottom hcProd
  have hT180 : T.rot180.IsColored col := IsColored_rot180 T col hT
  have hU180 : U.rot180.IsColored colU := IsColored_rot180 U colU hU
  have glueNW : colU U.rot180.SW = col T.rot180.NW := by
    change colU U.NE = col T.SE
    exact (colorMulBottom_NE T U col).resolve_right (crossingTangle_NW_ne_NE s)
  have glueNE : colU U.rot180.SE = col T.rot180.NE ∨ T.rot180.NW = T.rot180.NE := by
    by_cases hports : T.rot180.NW = T.rot180.NE
    · exact Or.inr hports
    · left
      change colU U.NW = col T.SW
      exact colorMulBottom_NW T U col
  let colR := colorGlueMul U.rot180 T.rot180 colU col
  have hcR : (U.rot180.mul T.rot180).IsColored colR :=
    IsColored_colorGlueMul U.rot180 T.rot180 colU col hU180 hT180 glueNW glueNE
  have hNW : colR (U.rot180.mul T.rot180).NW = col (T.mul U).rot180.NW := by
    change colR U.rot180.NW = col (T.mul U).SE
    dsimp [colR]
    rw [colorGlueMul_of_le U.rot180 T.rot180 colU col (maxArc_ge_NW U.rot180)]
    exact colorMulBottom_SE T U col
  have hNE : colR (U.rot180.mul T.rot180).NE = col (T.mul U).rot180.NE := by
    change colR U.rot180.NE = col (T.mul U).SW
    dsimp [colR]
    rw [colorGlueMul_of_le U.rot180 T.rot180 colU col (maxArc_ge_NE U.rot180)]
    exact colorMulBottom_SW T U col
  have hSW : colR (U.rot180.mul T.rot180).SW = col (T.mul U).rot180.SW := by
    have h1 : colR (U.rot180.mul T.rot180).SW = col T.rot180.SW := by
      dsimp [colR]
      rw [mul_SW_glue]
      exact colorGlueMul_comp_shift U.rot180 T.rot180 colU col glueNW glueNE
        T.rot180.SW
    rw [h1]
    rfl
  have hSE : colR (U.rot180.mul T.rot180).SE = col (T.mul U).rot180.SE := by
    have h1 : colR (U.rot180.mul T.rot180).SE = col T.rot180.SE := by
      dsimp [colR]
      rw [mul_SE_glue]
      exact colorGlueMul_comp_shift U.rot180 T.rot180 colU col glueNW glueNE
        T.rot180.SE
    rw [h1]
    rfl
  have hMat :
      ColorMatrix.of (U.rot180.mul T.rot180) colR =
        ColorMatrix.of (T.mul U).rot180 col := by
    simp [ColorMatrix.of, hNW, hNE, hSW, hSE]
  have hmR : (ColorMatrix.of (U.rot180.mul T.rot180) colR).NotMono := by
    simpa [hMat] using hmL
  have hfR :
      (ColorMatrix.of (U.rot180.mul T.rot180) colR).fraction =
        eL.toStandard.fraction := by
    rw [hMat]
    simpa [eL, TwistExpr.diagram] using hfL
  refine ⟨col, colR, hcL, hcR, hmL, hmR, ?_, ?_⟩
  · simpa [eL, TwistExpr.diagram] using
      (show (ColorMatrix.of (T.mul U).rot180 col).fraction =
          (ColorMatrix.of (U.rot180.mul T.rot180) colR).fraction from
        (hfL.trans hfR.symm))
  · simpa [eL, TwistExpr.diagram] using hfL

/-- If two `slideReady` twist diagrams are related by `ColoringIsotopy`,
    then any non-monochrome colorings of their `rot180` PD-codes have the
    same coloring fraction `F`. Fraction-level `rot180_cong` on this
    class; uniqueness of `f=F` on each rotated diagram plus invariance of
    `F` along `ColoringIsotopy`. Not a `ColoringIsotopy` constructor. -/
theorem coloring_rot180_cong_slideReady {e e' : TwistExpr}
    (hok : e.slideReady) (hok' : e'.slideReady)
    (h : ColoringIsotopy e.diagram e'.diagram)
    (col col' : Nat → Int)
    (hc : e.diagram.rot180.IsColored col)
    (hc' : e'.diagram.rot180.IsColored col')
    (hm : (ColorMatrix.of e.diagram.rot180 col).NotMono)
    (hm' : (ColorMatrix.of e'.diagram.rot180 col').NotMono) :
    (ColorMatrix.of e.diagram.rot180 col).fraction =
      (ColorMatrix.of e'.diagram.rot180 col').fraction := by
  have hf := coloring_rot180_any_eq_F_slideReady e hok col hc hm
  have hf' := coloring_rot180_any_eq_F_slideReady e' hok' col' hc' hm'
  rw [hf, hf', TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom hok hok' h]


/-! ## Fraction-level `invert_add` of two `slideReady` diagrams

Independent glue colorings of `(T+S)ⁱ` and of `Sⁱ * Tⁱ` when `T+S` is not
itself a `TwistExpr`. Requires finite nonzero `F` so affine matching of
integral colorings has `n ≠ 0`. Not a `ColoringIsotopy` constructor, and
not unrestricted `flype_slide`. -/

theorem CFValue.neg_negInv (x : CFValue) : x.neg.negInv = x.inv := by
  cases x with
  | inf => simp [CFValue.negInv, CFValue.inv, CFValue.neg]
  | ofRat q =>
    by_cases hq : q = 0
    · simp [CFValue.negInv, CFValue.inv, CFValue.neg, hq]
    · have hnq : -q ≠ 0 := by intro h; apply hq; linarith
      simp [CFValue.negInv, CFValue.inv, CFValue.neg, hq, hnq]

theorem ColorMatrix.of_colorGlueAdd (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNE : colT T.NE = colS S.NW)
    (hSE : colT T.SE = colS S.SW ∨ S.NW = S.SW) :
    ColorMatrix.of (T.add S) (colorGlueAdd T S colT colS) =
      { NW := colT T.NW
        NE := colS S.NE
        SW := colT T.SW
        SE := colS S.SE } := by
  refine ColorMatrix.ext ?_ ?_ ?_ ?_
  · change colorGlueAdd T S colT colS (T.add S).NW = colT T.NW
    exact colorGlueAdd_of_le T S colT colS (maxArc_ge_NW T)
  · change colorGlueAdd T S colT colS (T.add S).NE = colS S.NE
    rw [add_NE]
    exact colorGlueAdd_comp_shift T S colT colS hNE hSE S.NE
  · change colorGlueAdd T S colT colS (T.add S).SW = colT T.SW
    exact colorGlueAdd_of_le T S colT colS (maxArc_ge_SW T)
  · change colorGlueAdd T S colT colS (T.add S).SE = colS S.SE
    rw [add_SE]
    exact colorGlueAdd_comp_shift T S colT colS hNE hSE S.SE

theorem ColorMatrix.of_colorGlueMul (T S : TangleDiagram) (colT colS : Nat → Int)
    (hNW : colT T.SW = colS S.NW)
    (hNE : colT T.SE = colS S.NE ∨ S.NW = S.NE) :
    ColorMatrix.of (T.mul S) (colorGlueMul T S colT colS) =
      { NW := colT T.NW
        NE := colT T.NE
        SW := colS S.SW
        SE := colS S.SE } := by
  refine ColorMatrix.ext ?_ ?_ ?_ ?_
  · change colorGlueMul T S colT colS (T.mul S).NW = colT T.NW
    exact colorGlueMul_of_le T S colT colS (maxArc_ge_NW T)
  · change colorGlueMul T S colT colS (T.mul S).NE = colT T.NE
    exact colorGlueMul_of_le T S colT colS (maxArc_ge_NE T)
  · change colorGlueMul T S colT colS (T.mul S).SW = colS S.SW
    rw [mul_SW_glue]
    exact colorGlueMul_comp_shift T S colT colS hNW hNE S.SW
  · change colorGlueMul T S colT colS (T.mul S).SE = colS S.SE
    rw [mul_SE_glue]
    exact colorGlueMul_comp_shift T S colT colS hNW hNE S.SE

theorem TwistExpr.colorFrom_NE_ne_SE_of_ne_inf (e : TwistExpr) (hok : e.slideReady)
    (hF : e.toStandard.fraction ≠ .inf) :
    (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE ≠
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).SE := by
  intro heq
  have hf := coloring_fraction_eq_F e hok (e.colorFrom 0 1)
    (e.colorFrom_isColored_slideReady hok 0 1)
    (e.colorFrom_diagonal_slideReady hok 0 1)
    (e.colorFrom_notMono_slideReady hok)
  have : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).fraction = .inf := by
    simp [ColorMatrix.fraction, heq]
  exact hF (hf.symm.trans this)

/-- Affine-match two colorings so they glue along an `add` seam. -/
theorem coloring_affine_match_add (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (_hdT : (ColorMatrix.of T colT).DiagonalSum)
    (_hdS : (ColorMatrix.of S colS).DiagonalSum)
    (hmT : (ColorMatrix.of T colT).NotMono)
    (hmS : (ColorMatrix.of S colS).NotMono)
    (hdenT : colT T.NE ≠ colT T.SE)
    (hdenS : colS S.NW ≠ colS S.SW) :
    let nT := colS S.NW - colS S.SW
    let nS := colT T.NE - colT T.SE
    let kS := nT * colT T.NE - nS * colS S.NW
    let colT' := fun a => nT * colT a + 0
    let colS' := fun a => nS * colS a + kS
    nT ≠ 0 ∧ nS ≠ 0 ∧
      T.IsColored colT' ∧ S.IsColored colS' ∧
      colT' T.NE = colS' S.NW ∧ colT' T.SE = colS' S.SW ∧
      (ColorMatrix.of T colT').fraction = (ColorMatrix.of T colT).fraction ∧
      (ColorMatrix.of S colS').fraction = (ColorMatrix.of S colS).fraction ∧
      (ColorMatrix.of T colT').NotMono ∧ (ColorMatrix.of S colS').NotMono ∧
      (ColorMatrix.of T colT').DiagonalSum ∧
      (ColorMatrix.of S colS').DiagonalSum := by
  intro nT nS kS colT' colS'
  have hnT : nT ≠ 0 := sub_ne_zero.mpr hdenS
  have hnS : nS ≠ 0 := sub_ne_zero.mpr hdenT
  have hcT' : T.IsColored colT' := coloring_affine T colT nT 0 hT
  have hcS' : S.IsColored colS' := coloring_affine S colS nS kS hS
  refine ⟨hnT, hnS, hcT', hcS', ?glueNE, ?glueSE, ?fT, ?fS, ?mT, ?mS, ?dT, ?dS⟩
  case glueNE =>
    change nT * colT T.NE + 0 = nS * colS S.NW + (nT * colT T.NE - nS * colS S.NW)
    ring
  case glueSE =>
    change nT * colT T.SE + 0 = nS * colS S.SW + (nT * colT T.NE - nS * colS S.NW)
    ring
  case fT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nT 0 hnT
  case fS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nS kS hnS
  case mT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.NotMono_affine _ nT 0 hnT hmT
  case mS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.NotMono_affine _ nS kS hnS hmS
  case dT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nT 0 _hdT
  case dS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nS kS _hdS

/-- Affine-match two colorings so they glue along a `mul` seam. -/
theorem coloring_affine_match_mul (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (hdT : (ColorMatrix.of T colT).DiagonalSum)
    (hdS : (ColorMatrix.of S colS).DiagonalSum)
    (hmT : (ColorMatrix.of T colT).NotMono)
    (hmS : (ColorMatrix.of S colS).NotMono)
    (hdenT : colT T.SW ≠ colT T.SE)
    (hdenS : colS S.NW ≠ colS S.NE) :
    let nT := colS S.NW - colS S.NE
    let nS := colT T.SW - colT T.SE
    let kS := nT * colT T.SW - nS * colS S.NW
    let colT' := fun a => nT * colT a + 0
    let colS' := fun a => nS * colS a + kS
    nT ≠ 0 ∧ nS ≠ 0 ∧
      T.IsColored colT' ∧ S.IsColored colS' ∧
      colT' T.SW = colS' S.NW ∧ colT' T.SE = colS' S.NE ∧
      (ColorMatrix.of T colT').fraction = (ColorMatrix.of T colT).fraction ∧
      (ColorMatrix.of S colS').fraction = (ColorMatrix.of S colS).fraction ∧
      (ColorMatrix.of T colT').NotMono ∧ (ColorMatrix.of S colS').NotMono ∧
      (ColorMatrix.of T colT').DiagonalSum ∧
      (ColorMatrix.of S colS').DiagonalSum := by
  intro nT nS kS colT' colS'
  have hnT : nT ≠ 0 := sub_ne_zero.mpr hdenS
  have hnS : nS ≠ 0 := sub_ne_zero.mpr hdenT
  have hcT' : T.IsColored colT' := coloring_affine T colT nT 0 hT
  have hcS' : S.IsColored colS' := coloring_affine S colS nS kS hS
  refine ⟨hnT, hnS, hcT', hcS', ?glueSW, ?glueSE, ?fT, ?fS, ?mT, ?mS, ?dT, ?dS⟩
  case glueSW =>
    change nT * colT T.SW + 0 = nS * colS S.NW + (nT * colT T.SW - nS * colS S.NW)
    ring
  case glueSE =>
    change nT * colT T.SE + 0 = nS * colS S.NE + (nT * colT T.SW - nS * colS S.NW)
    -- uses DiagonalSum on T and S to relate SE/NE differences
    simp [ColorMatrix.DiagonalSum, ColorMatrix.of] at hdT hdS
    nlinarith
  case fT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nT 0 hnT
  case fS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nS kS hnS
  case mT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.NotMono_affine _ nT 0 hnT hmT
  case mS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.NotMono_affine _ nS kS hnS hmS
  case dT =>
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nT 0 hdT
  case dS =>
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nS kS hdS

theorem ColorMatrix.NE_ne_SE_of_fraction_ne_inf (M : ColorMatrix)
    (h : M.fraction ≠ .inf) : M.NE ≠ M.SE := by
  intro heq
  apply h
  simp [ColorMatrix.fraction, heq]

theorem ColorMatrix.NE_ne_NW_of_fraction_finite_ne_zero (M : ColorMatrix)
    (hfin : M.fraction ≠ .inf) (hnz : M.fraction ≠ 0) : M.NE ≠ M.NW := by
  intro heq
  apply hnz
  have hd : M.NE - M.SE ≠ 0 :=
    sub_ne_zero.mpr (ColorMatrix.NE_ne_SE_of_fraction_ne_inf M hfin)
  have hfrac : M.fraction =
      .ofRat (Rat.divInt (M.NE - M.NW) (M.NE - M.SE)) := by
    simp [ColorMatrix.fraction, hd]
  have hnum : M.NE - M.NW = 0 := by rw [heq]; ring
  have hden : M.NE - M.SE ≠ 0 := hd
  rw [hfrac, hnum, (Rat.divInt_eq_zero hden).2 rfl]
  rfl

theorem ColorMatrix.NW_ne_SW_of_DiagonalSum_ne_inf (M : ColorMatrix)
    (hd : M.DiagonalSum) (h : M.NE ≠ M.SE) : M.NW ≠ M.SW := by
  intro heq
  simp [ColorMatrix.DiagonalSum] at hd
  omega

theorem ColorMatrix.SW_ne_SE_of_DiagonalSum_ne_zero (M : ColorMatrix)
    (hd : M.DiagonalSum) (h : M.NE ≠ M.NW) : M.SW ≠ M.SE := by
  intro heq
  simp [ColorMatrix.DiagonalSum] at hd
  omega

theorem ColorMatrix.NotMono_of_NE_ne_SE (M : ColorMatrix) (h : M.NE ≠ M.SE) :
    M.NotMono := by
  intro hm
  exact h hm.2

theorem CFValue.inv_eq_zero_iff (x : CFValue) : x.inv = 0 ↔ x = .inf := by
  cases x with
  | inf =>
    simp [CFValue.inv]
    rfl
  | ofRat q =>
    constructor
    · intro h
      by_cases hq : q = 0
      · simp [CFValue.inv, hq] at h
      · simp [CFValue.inv, hq] at h
        have : q⁻¹ = 0 := CFValue.ofRat_injective h
        exact (inv_ne_zero hq this).elim
    · intro h
      cases h

theorem CFValue.inv_eq_inf_iff (x : CFValue) : x.inv = .inf ↔ x = 0 := by
  cases x with
  | inf =>
    simp [CFValue.inv]
  | ofRat q =>
    constructor
    · intro h
      by_cases hq : q = 0
      · simp [CFValue.inv, hq] at h ⊢
        rfl
      · simp [CFValue.inv, hq] at h
    · intro h
      have hq : q = 0 := CFValue.ofRat_injective h
      simp [CFValue.inv, hq]

theorem CFValue.neg_eq_inf_iff (x : CFValue) : x.neg = .inf ↔ x = .inf := by
  cases x <;> simp [CFValue.neg]

/-- Glue affine-matched finite colorings along an `add` seam, identifying
    `colorAddRight` with the affine right-hand coloring. -/
theorem coloring_glue_add_finite (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (hdT : (ColorMatrix.of T colT).DiagonalSum)
    (hdS : (ColorMatrix.of S colS).DiagonalSum)
    (_hmT : (ColorMatrix.of T colT).NotMono)
    (_hmS : (ColorMatrix.of S colS).NotMono)
    (hfinT : (ColorMatrix.of T colT).fraction ≠ .inf)
    (hfinS : (ColorMatrix.of S colS).fraction ≠ .inf) :
    ∃ col colS',
      (T.add S).IsColored col ∧
      S.IsColored colS' ∧
      colorAddRight T S col = colS' ∧
      (ColorMatrix.of T col).DiagonalSum ∧
      (ColorMatrix.of S colS').DiagonalSum ∧
      (ColorMatrix.of (T.add S) col).DiagonalSum ∧
      (ColorMatrix.of (T.add S) col).NotMono ∧
      (ColorMatrix.of (T.add S) col).fraction =
        (ColorMatrix.of T colT).fraction.add (ColorMatrix.of S colS).fraction := by
  have hdenT : colT T.NE ≠ colT T.SE :=
    ColorMatrix.NE_ne_SE_of_fraction_ne_inf _ hfinT
  have hdenS : colS S.NW ≠ colS S.SW :=
    ColorMatrix.NW_ne_SW_of_DiagonalSum_ne_inf _ hdS
      (ColorMatrix.NE_ne_SE_of_fraction_ne_inf _ hfinS)
  have hports : S.NW ≠ S.SW := fun h => hdenS (h ▸ rfl)
  let nT := colS S.NW - colS S.SW
  let nS := colT T.NE - colT T.SE
  let kS := nT * colT T.NE - nS * colS S.NW
  let colT' : Nat → Int := fun a => nT * colT a + 0
  let colS' : Nat → Int := fun a => nS * colS a + kS
  have hnT : nT ≠ 0 := sub_ne_zero.mpr hdenS
  have hnS : nS ≠ 0 := sub_ne_zero.mpr hdenT
  have hcT' : T.IsColored colT' := coloring_affine T colT nT 0 hT
  have hcS' : S.IsColored colS' := coloring_affine S colS nS kS hS
  have glueNE : colT' T.NE = colS' S.NW := by
    change nT * colT T.NE + 0 = nS * colS S.NW + (nT * colT T.NE - nS * colS S.NW)
    ring
  have glueSE : colT' T.SE = colS' S.SW := by
    change nT * colT T.SE + 0 = nS * colS S.SW + (nT * colT T.NE - nS * colS S.NW)
    ring
  let col := colorGlueAdd T S colT' colS'
  have hc : (T.add S).IsColored col :=
    IsColored_colorGlueAdd T S colT' colS' hcT' hcS' glueNE (Or.inl glueSE)
  have hAddR : colorAddRight T S col = colS' :=
    colorAddRight_colorGlueAdd T S colT' colS' glueNE (Or.inl glueSE)
  have hMT : ColorMatrix.of T col = ColorMatrix.of T colT' := by
    refine ColorMatrix.ext ?_ ?_ ?_ ?_
    · exact colorGlueAdd_of_le T S colT' colS' (maxArc_ge_NW T)
    · exact colorGlueAdd_of_le T S colT' colS' (maxArc_ge_NE T)
    · exact colorGlueAdd_of_le T S colT' colS' (maxArc_ge_SW T)
    · exact colorGlueAdd_of_le T S colT' colS' (maxArc_ge_SE T)
  have hdT' : (ColorMatrix.of T colT').DiagonalSum := by
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nT 0 hdT
  have hdS' : (ColorMatrix.of S colS').DiagonalSum := by
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nS kS hdS
  have hdTcol : (ColorMatrix.of T col).DiagonalSum := by simpa [hMT] using hdT'
  have hdG : (ColorMatrix.of (T.add S) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_add hports hdTcol (by rw [hAddR]; exact hdS')
  have hM := ColorMatrix.of_colorGlueAdd T S colT' colS' glueNE (Or.inl glueSE)
  have hneSE : colS' S.NE ≠ colS' S.SE := by
    intro h
    have : nS * (colS S.NE - colS S.SE) = 0 := by
      change nS * colS S.NE + kS = nS * colS S.SE + kS at h
      linarith
    rcases Int.mul_eq_zero.mp this with h0 | hsub
    · exact hnS h0
    · exact (ColorMatrix.NE_ne_SE_of_fraction_ne_inf _ hfinS)
        (Int.eq_of_sub_eq_zero hsub)
  have hmG : (ColorMatrix.of (T.add S) col).NotMono := by
    rw [hM]
    exact ColorMatrix.NotMono_of_NE_ne_SE _ hneSE
  have fT : (ColorMatrix.of T colT').fraction = (ColorMatrix.of T colT).fraction := by
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nT 0 hnT
  have fS : (ColorMatrix.of S colS').fraction = (ColorMatrix.of S colS).fraction := by
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nS kS hnS
  have hfadd := coloring_fraction_add T S col hports (by rw [hAddR]; exact hdS')
  have hf : (ColorMatrix.of (T.add S) col).fraction =
      (ColorMatrix.of T colT).fraction.add (ColorMatrix.of S colS).fraction := by
    rw [hAddR] at hfadd
    rw [hfadd.symm, hMT, fT, fS]
  exact ⟨col, colS', hc, hcS', hAddR, hdTcol, hdS', hdG, hmG, hf⟩

/-- Glue affine-matched finite nonzero colorings along a `mul` seam,
    identifying `colorMulBottom` with the affine bottom coloring. -/
theorem coloring_glue_mul_finite (T S : TangleDiagram) (colT colS : Nat → Int)
    (hT : T.IsColored colT) (hS : S.IsColored colS)
    (hdT : (ColorMatrix.of T colT).DiagonalSum)
    (hdS : (ColorMatrix.of S colS).DiagonalSum)
    (_hmT : (ColorMatrix.of T colT).NotMono)
    (_hmS : (ColorMatrix.of S colS).NotMono)
    (hfinT : (ColorMatrix.of T colT).fraction ≠ .inf)
    (hfinS : (ColorMatrix.of S colS).fraction ≠ .inf)
    (hnzT : (ColorMatrix.of T colT).fraction ≠ 0)
    (hnzS : (ColorMatrix.of S colS).fraction ≠ 0) :
    ∃ col colS',
      (T.mul S).IsColored col ∧
      S.IsColored colS' ∧
      colorMulBottom T S col = colS' ∧
      (ColorMatrix.of T col).DiagonalSum ∧
      (ColorMatrix.of S colS').DiagonalSum ∧
      (ColorMatrix.of (T.mul S) col).DiagonalSum ∧
      (ColorMatrix.of (T.mul S) col).NotMono ∧
      (ColorMatrix.of (T.mul S) col).fraction =
        ((ColorMatrix.of T colT).fraction.inv.add
          (ColorMatrix.of S colS).fraction.inv).inv := by
  have hdenT : colT T.SW ≠ colT T.SE :=
    ColorMatrix.SW_ne_SE_of_DiagonalSum_ne_zero _ hdT
      (ColorMatrix.NE_ne_NW_of_fraction_finite_ne_zero _ hfinT hnzT)
  have hdenS : colS S.NW ≠ colS S.NE :=
    (ColorMatrix.NE_ne_NW_of_fraction_finite_ne_zero _ hfinS hnzS).symm
  have hports : S.NW ≠ S.NE := fun h => hdenS (h ▸ rfl)
  let nT := colS S.NW - colS S.NE
  let nS := colT T.SW - colT T.SE
  let kS := nT * colT T.SW - nS * colS S.NW
  let colT' : Nat → Int := fun a => nT * colT a + 0
  let colS' : Nat → Int := fun a => nS * colS a + kS
  have hnT : nT ≠ 0 := sub_ne_zero.mpr hdenS
  have hnS : nS ≠ 0 := sub_ne_zero.mpr hdenT
  have hcT' : T.IsColored colT' := coloring_affine T colT nT 0 hT
  have hcS' : S.IsColored colS' := coloring_affine S colS nS kS hS
  have glueSW : colT' T.SW = colS' S.NW := by
    change nT * colT T.SW + 0 = nS * colS S.NW + (nT * colT T.SW - nS * colS S.NW)
    ring
  have glueSE : colT' T.SE = colS' S.NE := by
    change nT * colT T.SE + 0 = nS * colS S.NE + (nT * colT T.SW - nS * colS S.NW)
    simp [ColorMatrix.DiagonalSum, ColorMatrix.of] at hdT hdS
    nlinarith
  let col := colorGlueMul T S colT' colS'
  have hc : (T.mul S).IsColored col :=
    IsColored_colorGlueMul T S colT' colS' hcT' hcS' glueSW (Or.inl glueSE)
  have hMulB : colorMulBottom T S col = colS' :=
    colorMulBottom_colorGlueMul T S colT' colS' glueSW (Or.inl glueSE)
  have hMT : ColorMatrix.of T col = ColorMatrix.of T colT' := by
    refine ColorMatrix.ext ?_ ?_ ?_ ?_
    · exact colorGlueMul_of_le T S colT' colS' (maxArc_ge_NW T)
    · exact colorGlueMul_of_le T S colT' colS' (maxArc_ge_NE T)
    · exact colorGlueMul_of_le T S colT' colS' (maxArc_ge_SW T)
    · exact colorGlueMul_of_le T S colT' colS' (maxArc_ge_SE T)
  have hdT' : (ColorMatrix.of T colT').DiagonalSum := by
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nT 0 hdT
  have hdS' : (ColorMatrix.of S colS').DiagonalSum := by
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.DiagonalSum_affine _ nS kS hdS
  have hdTcol : (ColorMatrix.of T col).DiagonalSum := by simpa [hMT] using hdT'
  have hdG : (ColorMatrix.of (T.mul S) col).DiagonalSum :=
    ColorMatrix.DiagonalSum_of_mul hports hdTcol (by rw [hMulB]; exact hdS')
  have hM := ColorMatrix.of_colorGlueMul T S colT' colS' glueSW (Or.inl glueSE)
  have hneNWNE : colT' T.NW ≠ colT' T.NE := by
    intro h
    have : nT * (colT T.NW - colT T.NE) = 0 := by
      change nT * colT T.NW + 0 = nT * colT T.NE + 0 at h
      linarith
    rcases Int.mul_eq_zero.mp this with h0 | hsub
    · exact hnT h0
    · exact (ColorMatrix.NE_ne_NW_of_fraction_finite_ne_zero _ hfinT hnzT)
        (Int.eq_of_sub_eq_zero hsub).symm
  have hmG : (ColorMatrix.of (T.mul S) col).NotMono := by
    rw [hM]
    intro hm
    exact hneNWNE hm.1
  have fT : (ColorMatrix.of T colT').fraction = (ColorMatrix.of T colT).fraction := by
    rw [show colT' = fun a => nT * colT a + 0 from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nT 0 hnT
  have fS : (ColorMatrix.of S colS').fraction = (ColorMatrix.of S colS).fraction := by
    rw [show colS' = fun a => nS * colS a + kS from rfl, ColorMatrix.of_affineMap]
    exact ColorMatrix.fraction_affine _ nS kS hnS
  have hfmul := coloring_fraction_mul T S col hports hdTcol
    (by rw [hMulB]; exact hdS') hmG
  have hf : (ColorMatrix.of (T.mul S) col).fraction =
      ((ColorMatrix.of T colT).fraction.inv.add
        (ColorMatrix.of S colS).fraction.inv).inv := by
    rw [hMulB] at hfmul
    rw [hfmul.symm, hMT, fT, fS]
  exact ⟨col, colS', hc, hcS', hMulB, hdTcol, hdS', hdG, hmG, hf⟩

/-- `colorFrom` of two `rightBottom`/`slideReady` diagrams with finite `F`
    glue to a coloring of the PD-sum `T.add S`. -/
theorem coloring_add_two_rightBottom (e f : TwistExpr)
    (_hrb : e.rightBottom) (_hrb' : f.rightBottom)
    (hok : e.slideReady) (hok' : f.slideReady)
    (hfin : e.toStandard.fraction ≠ .inf)
    (hfin' : f.toStandard.fraction ≠ .inf) :
    ∃ col,
      (e.diagram.add f.diagram).IsColored col ∧
      (ColorMatrix.of (e.diagram.add f.diagram) col).NotMono ∧
      (ColorMatrix.of (e.diagram.add f.diagram) col).DiagonalSum ∧
      (ColorMatrix.of (e.diagram.add f.diagram) col).fraction =
        e.toStandard.fraction.add f.toStandard.fraction := by
  let colT := e.colorFrom 0 1
  let colS := f.colorFrom 0 1
  have hT : e.diagram.IsColored colT := e.colorFrom_isColored_slideReady hok 0 1
  have hS : f.diagram.IsColored colS := f.colorFrom_isColored_slideReady hok' 0 1
  have hdT := e.colorFrom_diagonal_slideReady hok 0 1
  have hdS := f.colorFrom_diagonal_slideReady hok' 0 1
  have hmT := e.colorFrom_notMono_slideReady hok
  have hmS := f.colorFrom_notMono_slideReady hok'
  have hfT := coloring_fraction_eq_F e hok colT hT hdT hmT
  have hfS := coloring_fraction_eq_F f hok' colS hS hdS hmS
  have hfinT : (ColorMatrix.of e.diagram colT).fraction ≠ .inf := by
    rw [hfT]; exact hfin
  have hfinS : (ColorMatrix.of f.diagram colS).fraction ≠ .inf := by
    rw [hfS]; exact hfin'
  obtain ⟨col, _, hc, _, _, _, _, hdG, hmG, hf⟩ :=
    coloring_glue_add_finite e.diagram f.diagram colT colS hT hS hdT hdS hmT hmS
      hfinT hfinS
  exact ⟨col, hc, hmG, hdG, hf.trans (by rw [hfT, hfS])⟩

/-- Fresh coloring of the PD-mirror via the algebraic mirror's `colorFrom`. -/
theorem coloring_pd_mirror_of_colorFrom (e : TwistExpr) (hok : e.slideReady) :
    ∃ col, e.diagram.mirror.IsColored col ∧
      (ColorMatrix.of e.diagram.mirror col).NotMono ∧
      (ColorMatrix.of e.diagram.mirror col).DiagonalSum ∧
      (ColorMatrix.of e.diagram.mirror col).fraction = e.toStandard.fraction.neg := by
  have hokM : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  obtain ⟨col, hc, hMat, hfrac⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_diagram_rev_slideReady e hok)
      (e.mirror.colorFrom 0 1) (e.mirror.colorFrom_isColored_slideReady hokM 0 1)
  have hmA := e.mirror.colorFrom_notMono_slideReady hokM
  have hdA := e.mirror.colorFrom_diagonal_slideReady hokM 0 1
  have hm : (ColorMatrix.of e.diagram.mirror col).NotMono := by simpa [hMat] using hmA
  have hd : (ColorMatrix.of e.diagram.mirror col).DiagonalSum := by simpa [hMat] using hdA
  have hfA := coloring_fraction_eq_F e.mirror hokM (e.mirror.colorFrom 0 1)
    (e.mirror.colorFrom_isColored_slideReady hokM 0 1) hdA hmA
  refine ⟨col, hc, hm, hd, ?_⟩
  rw [hfrac, hfA, TwistExpr.toStandard_mirror, StandardExpr.fraction_mirror]

/-- `ColoringIsotopy` from the algebraic-mirror sum to the PD-mirror of the
    sum (existing `add_left`/`add_right`, not a leftover generator). -/
theorem coloring_mirror_add_two (e f : TwistExpr)
    (hok : e.slideReady) (hok' : f.slideReady) :
    ColoringIsotopy (e.mirror.diagram.add f.mirror.diagram)
      (e.diagram.mirror.add f.diagram.mirror) := by
  have hglue : f.mirror.diagram.NW = f.mirror.diagram.SW →
      f.diagram.mirror.NW = f.diagram.mirror.SW := by
    intro h
    simpa [TangleDiagram.mirror, TwistExpr.mirror_NW, TwistExpr.mirror_SW] using h
  exact ColoringIsotopy.trans
    (.add_left (S := f.mirror.diagram) (coloring_mirror_diagram_rev_slideReady e hok))
    (.add_right (coloring_mirror_diagram_rev_slideReady f hok') hglue)

/-- Fresh colorings of `(T+S)ⁱ` and of `Sⁱ * Tⁱ` for two `rightBottom` /
    `slideReady` diagrams with finite nonzero `F`. Not a `ColoringIsotopy`,
    not unrestricted `flype_slide`, and not a `SlideReadyIsotopy` constructor
    (`T.add S` is not a `TwistExpr`). -/
theorem coloring_invert_add_two_rightBottom (e f : TwistExpr)
    (hrb : e.rightBottom) (hrb' : f.rightBottom)
    (hok : e.slideReady) (hok' : f.slideReady)
    (hfin : e.toStandard.fraction ≠ .inf)
    (hfin' : f.toStandard.fraction ≠ .inf)
    (hnz : e.toStandard.fraction ≠ (0 : CFValue))
    (hnz' : f.toStandard.fraction ≠ (0 : CFValue)) :
    ∃ colL colR,
      ((e.diagram.add f.diagram).invert).IsColored colL ∧
      ((f.diagram.invert.mul e.diagram.invert)).IsColored colR ∧
      (ColorMatrix.of (e.diagram.add f.diagram).invert colL).NotMono ∧
      (ColorMatrix.of (f.diagram.invert.mul e.diagram.invert) colR).NotMono ∧
      (ColorMatrix.of (e.diagram.add f.diagram).invert colL).fraction =
        (ColorMatrix.of (f.diagram.invert.mul e.diagram.invert) colR).fraction ∧
      (ColorMatrix.of (e.diagram.add f.diagram).invert colL).fraction =
        (e.toStandard.fraction.add f.toStandard.fraction).inv := by
  have hokMe : e.mirror.slideReady := TwistExpr.slideReady_mirror e hok
  have hokMf : f.mirror.slideReady := TwistExpr.slideReady_mirror f hok'
  have hrbMe : e.mirror.rightBottom := TwistExpr.rightBottom_mirror e hrb
  have hrbMf : f.mirror.rightBottom := TwistExpr.rightBottom_mirror f hrb'
  have hfinMe : e.mirror.toStandard.fraction ≠ .inf := by
    rw [TwistExpr.toStandard_mirror, StandardExpr.fraction_mirror]
    intro h
    exact hfin ((CFValue.neg_eq_inf_iff _).1 h)
  have hfinMf : f.mirror.toStandard.fraction ≠ .inf := by
    rw [TwistExpr.toStandard_mirror, StandardExpr.fraction_mirror]
    intro h
    exact hfin' ((CFValue.neg_eq_inf_iff _).1 h)
  obtain ⟨colSumM, hcSumM, hmSumM, hdSumM, hfSumM⟩ :=
    coloring_add_two_rightBottom e.mirror f.mirror hrbMe hrbMf hokMe hokMf
      hfinMe hfinMf
  obtain ⟨colMirr, hcMirr, hMatMirr, hfracMirr⟩ :=
    coloring_fraction_ColoringIsotopy (coloring_mirror_add_two e f hok hok')
      colSumM hcSumM
  have hcMirr' : (e.diagram.add f.diagram).mirror.IsColored colMirr := by
    simpa [mirror_add] using hcMirr
  have hMatMirr' :
      ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr =
        ColorMatrix.of (e.mirror.diagram.add f.mirror.diagram) colSumM := by
    simpa [mirror_add] using hMatMirr
  have hcL : (e.diagram.add f.diagram).invert.IsColored colMirr := by
    simpa [invert_eq_mirror_rotate] using coloring_rotate _ colMirr hcMirr'
  have hdMirr : (ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr).DiagonalSum := by
    simpa [hMatMirr'] using hdSumM
  have hmMirr : (ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr).NotMono := by
    simpa [hMatMirr'] using hmSumM
  have hmL : (ColorMatrix.of (e.diagram.add f.diagram).invert colMirr).NotMono := by
    have hrot :
        ColorMatrix.of (e.diagram.add f.diagram).invert colMirr =
          (ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr).rotate := by
      simp [invert_eq_mirror_rotate, ColorMatrix.of_rotate]
    simpa [hrot] using ColorMatrix.NotMono_rotate hdMirr hmMirr
  have hfL :
      (ColorMatrix.of (e.diagram.add f.diagram).invert colMirr).fraction =
        (e.toStandard.fraction.add f.toStandard.fraction).inv := by
    have hrot :
        (ColorMatrix.of (e.diagram.add f.diagram).invert colMirr).fraction =
          (ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr).fraction.negInv :=
      coloring_fraction_rotate _ colMirr hdMirr hmMirr
    have hfM :
        (ColorMatrix.of (e.diagram.add f.diagram).mirror colMirr).fraction =
          e.mirror.toStandard.fraction.add f.mirror.toStandard.fraction := by
      rw [hMatMirr', hfSumM]
    rw [hrot, hfM, TwistExpr.toStandard_mirror, TwistExpr.toStandard_mirror,
      StandardExpr.fraction_mirror, StandardExpr.fraction_mirror]
    rw [← CFValue.neg_add, CFValue.neg_negInv]
  obtain ⟨colSinv, hcSinv, hmSinv, hfSinv⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom f hok'
  obtain ⟨colTinv, hcTinv, hmTinv, hfTinv⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  have hdSinv := twist_coloring_diagonal_invert_slideReady f hok' colSinv hcSinv
  have hdTinv := twist_coloring_diagonal_invert_slideReady e hok colTinv hcTinv
  have hfinSinv : (ColorMatrix.of f.diagram.invert colSinv).fraction ≠ .inf := by
    rw [hfSinv]
    intro h
    exact hnz' ((CFValue.inv_eq_inf_iff _).1 h)
  have hfinTinv : (ColorMatrix.of e.diagram.invert colTinv).fraction ≠ .inf := by
    rw [hfTinv]
    intro h
    exact hnz ((CFValue.inv_eq_inf_iff _).1 h)
  have hnzSinv : (ColorMatrix.of f.diagram.invert colSinv).fraction ≠ 0 := by
    rw [hfSinv]
    intro h
    exact hfin' ((CFValue.inv_eq_zero_iff _).1 h)
  have hnzTinv : (ColorMatrix.of e.diagram.invert colTinv).fraction ≠ 0 := by
    rw [hfTinv]
    intro h
    exact hfin ((CFValue.inv_eq_zero_iff _).1 h)
  obtain ⟨colR, _, hcR, _, _, _, _, _, hmR, hfR⟩ :=
    coloring_glue_mul_finite f.diagram.invert e.diagram.invert
      colSinv colTinv hcSinv hcTinv hdSinv hdTinv hmSinv hmTinv
      hfinSinv hfinTinv hnzSinv hnzTinv
  have hfR' :
      (ColorMatrix.of (f.diagram.invert.mul e.diagram.invert) colR).fraction =
        (e.toStandard.fraction.add f.toStandard.fraction).inv := by
    rw [hfR, hfSinv, hfTinv, CFValue.inv_inv, CFValue.inv_inv, CFValue.add_comm]
  refine ⟨colMirr, colR, hcL, hcR, hmL, hmR, ?_, hfL⟩
  exact hfL.trans hfR'.symm

/-- Invert of `[0]+T` is the invert of `T` with the same arc reindex as
    `zero_add`. -/
theorem invert_zero_add_crossings (T : TangleDiagram) :
    (TangleDiagram.zero.add T).invert.crossings =
      T.invert.crossings.map (Crossing.rename (zeroAddReindex T)) := by
  simp [TangleDiagram.invert, TangleDiagram.rotate, TangleDiagram.mirror,
    zero_add_crossings_reindex, List.map_map, Function.comp,
    Crossing.switch_rename]

/-- Recolor `Tⁱ` along the `[0]+T` reindex. Dummy names `0`/`1` take
    `T.NW`/`T.SW` (the inverted `SW`/`SE`), so this needs no port
    hypothesis. -/
theorem IsColored_colorZeroAdd_invert (T : TangleDiagram) (col : Nat → Int)
    (hc : T.invert.IsColored col) :
    (TangleDiagram.zero.add T).invert.IsColored (colorZeroAdd T col) := by
  intro C hC
  rw [invert_zero_add_crossings] at hC
  obtain ⟨C0, hC0, rfl⟩ := List.mem_map.1 hC
  rw [ColoringRule_rename]
  have hfun : colorZeroAdd T col ∘ zeroAddReindex T = col :=
    funext (colorZeroAdd_reindex T col)
  simpa [hfun] using hc C0 hC0

theorem coloring_invert_zero_add (T : TangleDiagram) (col : Nat → Int)
    (hc : T.invert.IsColored col) :
    ∃ col', (TangleDiagram.zero.add T).invert.IsColored col' ∧
      SameEndpointColors T.invert (TangleDiagram.zero.add T).invert col col' := by
  refine ⟨colorZeroAdd T col, IsColored_colorZeroAdd_invert T col hc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TangleDiagram.invert_NW, TangleDiagram.invert_NW, zero_add_NE_reindex,
      colorZeroAdd_reindex]
  · rw [TangleDiagram.invert_NE, TangleDiagram.invert_NE, zero_add_SE_reindex,
      colorZeroAdd_reindex]
  · rw [TangleDiagram.invert_SE, TangleDiagram.invert_SE]
    simp [TangleDiagram.add, TangleDiagram.zero, colorZeroAdd]
  · rw [TangleDiagram.invert_SW, TangleDiagram.invert_SW]
    simp [TangleDiagram.add, TangleDiagram.zero, colorZeroAdd]

theorem coloring_fraction_invert_zero_add (T : TangleDiagram) (col : Nat → Int)
    (hc : T.invert.IsColored col) :
    ∃ col', (TangleDiagram.zero.add T).invert.IsColored col' ∧
      ColorMatrix.of (TangleDiagram.zero.add T).invert col' =
        ColorMatrix.of T.invert col ∧
      (ColorMatrix.of (TangleDiagram.zero.add T).invert col').fraction =
        (ColorMatrix.of T.invert col).fraction := by
  obtain ⟨col', hc', hs⟩ := coloring_invert_zero_add T col hc
  have hM := ColorMatrix.of_sameEndpoint hs
  exact ⟨col', hc', hM, hM ▸ rfl⟩

/-- Fresh colorings of `(T+[0])ⁱ` and of `[0]ⁱ * Tⁱ` on a `slideReady`
    diagram. Left PD-code is `Tⁱ` (`add_zero_eq`); right is `[∞]*Tⁱ`,
    colored by the left-mul reindex. Not a `ColoringIsotopy`
    (`invert_add` switches crossings). Covers a right summand `[0]`,
    including when `F(T)=∞`. -/
theorem coloring_invert_add_slideReady_zero (e : TwistExpr)
    (hok : e.slideReady) :
    ∃ colL colR,
      ((e.diagram.add TangleDiagram.zero).invert).IsColored colL ∧
      ((TangleDiagram.zero.invert.mul e.diagram.invert)).IsColored colR ∧
      (ColorMatrix.of (e.diagram.add TangleDiagram.zero).invert
        colL).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.invert.mul e.diagram.invert)
        colR).NotMono ∧
      (ColorMatrix.of (e.diagram.add TangleDiagram.zero).invert
        colL).fraction =
        (ColorMatrix.of (TangleDiagram.zero.invert.mul e.diagram.invert)
          colR).fraction ∧
      (ColorMatrix.of (e.diagram.add TangleDiagram.zero).invert
        colL).fraction =
        (e.toStandard.fraction.add (0 : CFValue)).inv := by
  have hL : e.diagram.add TangleDiagram.zero = e.diagram := add_zero_eq _
  obtain ⟨colL, hcL, hmL, hfL⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  have hcL' :
      (e.diagram.add TangleDiagram.zero).invert.IsColored colL := by
    simpa only [hL] using hcL
  have hmL' :
      (ColorMatrix.of (e.diagram.add TangleDiagram.zero).invert
        colL).NotMono := by
    simpa only [hL] using hmL
  have hfL' :
      (ColorMatrix.of (e.diagram.add TangleDiagram.zero).invert
        colL).fraction = e.toStandard.fraction.inv := by
    simpa only [hL] using hfL
  have hR :
      TangleDiagram.zero.invert.mul e.diagram.invert =
        TangleDiagram.infinity.mul e.diagram.invert := by
    rw [invert_zero]
  obtain ⟨colR, hcR, hMat, hfrac⟩ :=
    coloring_fraction_infinity_mul e.diagram.invert colL hcL
  refine ⟨colL, colR, hcL', ?_, hmL', ?_, ?_, ?_⟩
  · simpa only [hR] using hcR
  · have hmR :
        (ColorMatrix.of (TangleDiagram.infinity.mul e.diagram.invert)
          colR).NotMono := by
      simpa only [hMat] using hmL
    simpa only [hR] using hmR
  · have hfR :
        (ColorMatrix.of (TangleDiagram.zero.invert.mul e.diagram.invert)
          colR).fraction = e.toStandard.fraction.inv := by
      simpa only [hR] using hfrac.trans hfL
    exact hfL'.trans hfR.symm
  · rw [hfL']
    simp [show (0 : CFValue) = CFValue.ofRat 0 from rfl, CFValue.add_zero]

/-- Fresh colorings of `([0]+T)ⁱ` and of `Tⁱ * [0]ⁱ` on a `slideReady`
    diagram. Right PD-code is `Tⁱ` (`mul_infinity_eq` after `invert_zero`);
    left is the invert of the `[0]+T` reindex, colored by
    `coloring_fraction_invert_zero_add`. Not a `ColoringIsotopy`. Covers a
    left summand `[0]`. -/
theorem coloring_invert_add_zero_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    ∃ colL colR,
      ((TangleDiagram.zero.add e.diagram).invert).IsColored colL ∧
      ((e.diagram.invert.mul TangleDiagram.zero.invert)).IsColored colR ∧
      (ColorMatrix.of (TangleDiagram.zero.add e.diagram).invert
        colL).NotMono ∧
      (ColorMatrix.of (e.diagram.invert.mul TangleDiagram.zero.invert)
        colR).NotMono ∧
      (ColorMatrix.of (TangleDiagram.zero.add e.diagram).invert
        colL).fraction =
        (ColorMatrix.of (e.diagram.invert.mul TangleDiagram.zero.invert)
          colR).fraction ∧
      (ColorMatrix.of (TangleDiagram.zero.add e.diagram).invert
        colL).fraction =
        ((0 : CFValue).add e.toStandard.fraction).inv := by
  obtain ⟨col0, hc0, hm0, hf0⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  have hR :
      e.diagram.invert.mul TangleDiagram.zero.invert = e.diagram.invert := by
    rw [invert_zero, mul_infinity_eq]
  have hcR :
      (e.diagram.invert.mul TangleDiagram.zero.invert).IsColored col0 := by
    simpa only [hR] using hc0
  have hmR :
      (ColorMatrix.of (e.diagram.invert.mul TangleDiagram.zero.invert)
        col0).NotMono := by
    simpa only [hR] using hm0
  have hfR :
      (ColorMatrix.of (e.diagram.invert.mul TangleDiagram.zero.invert)
        col0).fraction = e.toStandard.fraction.inv := by
    simpa only [hR] using hf0
  obtain ⟨colL, hcL, hMat, hfrac⟩ :=
    coloring_fraction_invert_zero_add e.diagram col0 hc0
  refine ⟨colL, col0, hcL, hcR, ?_, hmR, ?_, ?_⟩
  · simpa only [hMat] using hm0
  · have hfL :
        (ColorMatrix.of (TangleDiagram.zero.add e.diagram).invert
          colL).fraction = e.toStandard.fraction.inv :=
      hfrac.trans hf0
    exact hfL.trans hfR.symm
  · have hfL :
        (ColorMatrix.of (TangleDiagram.zero.add e.diagram).invert
          colL).fraction = e.toStandard.fraction.inv :=
      hfrac.trans hf0
    rw [hfL]
    simp [show (0 : CFValue) = CFValue.ofRat 0 from rfl, CFValue.zero_add]

/-! ## `SlideReadyIsotopy`

The relation generated by coloring-ready isotopy on `slideReady` twist
diagrams together with the leftover generators already compared at `f`
(`invert_cong` / `invert_add` / `invert_mul` of a unit, `mirror_cong`,
Figure 14). A carried `CFValue` is a coloring fraction of both ends.
This is not `Isotopic`.
-/

/-- Existence of a non-monochrome integral coloring with fraction `v`. -/
def HasColoringFraction (D : TangleDiagram) (v : CFValue) : Prop :=
  ∃ col, D.IsColored col ∧ (ColorMatrix.of D col).NotMono ∧
    (ColorMatrix.of D col).fraction = v

/-- Directed comparison along the coloring-ready generators and the leftover
    moves that have been identified at the coloring fraction on `slideReady`
    twist diagrams. The third argument is a coloring fraction of both
    endpoints. Intermediates need not be twist-form.

    This is not `Isotopic`: it omits invert-add of two general (non-unit)
    summands, unrestricted `flype_slide_*` (without `DiagonalSum` and the
    port hypotheses), and paths that leave twist form. Fraction-level
    `rot180_cong` is a theorem on this class, not a constructor.
    Constructors are not added to `ColoringIsotopy`. Induction of
    `HasColoringFraction` along `Isotopic` is blocked by unrestricted
    `flype_slide_add`/`flype_slide_mul`. -/
inductive SlideReadyIsotopy : TangleDiagram → TangleDiagram → CFValue → Prop where
  | refl (e : TwistExpr) (hok : e.slideReady) :
      SlideReadyIsotopy e.diagram e.diagram e.toStandard.fraction
  | trans {D E F : TangleDiagram} {v : CFValue} :
      SlideReadyIsotopy D E v → SlideReadyIsotopy E F v → SlideReadyIsotopy D F v
  | coloring (e₁ e₂ : TwistExpr) (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
      (h : ColoringIsotopy e₁.diagram e₂.diagram) :
      SlideReadyIsotopy e₁.diagram e₂.diagram e₁.toStandard.fraction
  | invert_cong (e e' : TwistExpr) (hok : e.slideReady) (hok' : e'.slideReady)
      (h : ColoringIsotopy e.diagram e'.diagram) :
      SlideReadyIsotopy e.diagram.invert e'.diagram.invert
        e.toStandard.fraction.inv
  | invert_add (e : TwistExpr) (hok : e.slideReady) (s : CrossingSign)
      (hne : e.diagram.NE ≠ e.diagram.SE) :
      SlideReadyIsotopy
        (e.diagram.add (crossingTangle s)).invert
        ((crossingTangle s).invert.mul e.diagram.invert)
        (TwistExpr.addRight e s).toStandard.fraction.inv
  | invert_mul (e : TwistExpr) (hok : e.slideReady) (s : CrossingSign) :
      SlideReadyIsotopy
        (e.diagram.mul (crossingTangle s)).invert
        (e.diagram.invert.add (crossingTangle s).invert)
        (TwistExpr.mulBottom e s).toStandard.fraction.inv
  | mirror_cong (e e' : TwistExpr) (hok : e.slideReady) (hok' : e'.slideReady)
      (h : ColoringIsotopy e.diagram e'.diagram) :
      SlideReadyIsotopy e.diagram.mirror e'.diagram.mirror
        e.toStandard.fraction.neg
  | transfer_odd (e : TwistExpr) (hok : e.slideReady)
      (hports : e.diagram.NW ≠ e.diagram.NE)
      (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
        (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
      SlideReadyIsotopy
        ((e.diagram.add RationalTangles.negOne).mul RationalTangles.one)
        (RationalTangles.one.add e.diagram.mirror.invert)
        (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).toStandard.fraction
  | transfer_odd_neg (e : TwistExpr) (hok : e.slideReady)
      (hports : e.diagram.NW ≠ e.diagram.NE)
      (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
        (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
      SlideReadyIsotopy
        ((e.diagram.add RationalTangles.one).mul RationalTangles.negOne)
        (RationalTangles.negOne.add e.diagram.mirror.invert)
        (TwistExpr.mulBottom (TwistExpr.addRight e .pos) .neg).toStandard.fraction
  | rot180 (e : TwistExpr) (hok : e.slideReady) :
      SlideReadyIsotopy e.diagram e.diagram.rot180 e.toStandard.fraction
  | rot180_rev (e : TwistExpr) (hok : e.slideReady) :
      SlideReadyIsotopy e.diagram.rot180 e.diagram e.toStandard.fraction
  | flype_slide_add (e : TwistExpr) (hok : e.slideReady) (s : CrossingSign)
      (hne : e.diagram.NW ≠ e.diagram.SW) :
      SlideReadyIsotopy
        ((crossingTangle s).add e.diagram)
        (e.diagram.rot180.add (crossingTangle s))
        (TwistExpr.addLeft e s).toStandard.fraction
  | flype_slide_mul (e : TwistExpr) (hok : e.slideReady) (s : CrossingSign)
      (hne : e.diagram.NW ≠ e.diagram.NE) :
      SlideReadyIsotopy
        ((crossingTangle s).mul e.diagram)
        (e.diagram.rot180.mul (crossingTangle s))
        (TwistExpr.mulTop e s).toStandard.fraction

theorem HasColoringFraction.colorFrom_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction e.diagram e.toStandard.fraction := by
  refine ⟨e.colorFrom 0 1, e.colorFrom_isColored_slideReady hok 0 1,
    e.colorFrom_notMono_slideReady hok, ?_⟩
  exact coloring_fraction_eq_F e hok (e.colorFrom 0 1)
    (e.colorFrom_isColored_slideReady hok 0 1)
    (e.colorFrom_diagonal_slideReady hok 0 1)
    (e.colorFrom_notMono_slideReady hok)

theorem SlideReadyIsotopy.has_fraction {D E : TangleDiagram} {v : CFValue}
    (h : SlideReadyIsotopy D E v) :
    HasColoringFraction D v ∧ HasColoringFraction E v := by
  induction h with
  | refl e hok =>
    exact ⟨HasColoringFraction.colorFrom_slideReady e hok,
      HasColoringFraction.colorFrom_slideReady e hok⟩
  | trans h1 h2 ih1 ih2 =>
    exact ⟨ih1.1, ih2.2⟩
  | coloring e₁ e₂ hok₁ hok₂ h =>
    let col := e₁.colorFrom 0 1
    have hc : e₁.diagram.IsColored col :=
      e₁.colorFrom_isColored_slideReady hok₁ 0 1
    have hm : (ColorMatrix.of e₁.diagram col).NotMono :=
      e₁.colorFrom_notMono_slideReady hok₁
    have hf := coloring_fraction_eq_F e₁ hok₁ col hc
      (e₁.colorFrom_diagonal_slideReady hok₁ 0 1) hm
    obtain ⟨col', hc', hMat, hfrac⟩ := coloring_fraction_ColoringIsotopy h col hc
    have hm' : (ColorMatrix.of e₂.diagram col').NotMono := by
      simpa [hMat] using hm
    exact ⟨⟨col, hc, hm, hf⟩, ⟨col', hc', hm', hfrac.trans hf⟩⟩
  | invert_cong e e' hok hok' h =>
    obtain ⟨colI, colI', hcI, hcI', hmI, hmI', hagree⟩ :=
      coloring_invert_cong_slideReady hok hok' h
    have hf := coloring_invert_inv_any_slideReady e hok colI hcI hmI
    exact ⟨⟨colI, hcI, hmI, hf⟩, ⟨colI', hcI', hmI', hagree.symm.trans hf⟩⟩
  | invert_add e hok s hne =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree⟩ :=
      coloring_invert_add_slideReady e hok s hne
    have hokL : (TwistExpr.addRight e s).slideReady :=
      TwistExpr.addRight_slideReady e s hok
    have hfL :=
      coloring_invert_inv_any_slideReady (.addRight e s) hokL colL hcL hmL
    exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩
  | invert_mul e hok s =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree⟩ :=
      coloring_invert_mul_slideReady e hok s
    have hokL : (TwistExpr.mulBottom e s).slideReady :=
      TwistExpr.mulBottom_slideReady e s hok
    have hfL :=
      coloring_invert_inv_any_slideReady (.mulBottom e s) hokL colL hcL hmL
    exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩
  | mirror_cong e e' hok hok' h =>
    obtain ⟨colM, colM', hcM, hcM', hmM, hmM', hagree⟩ :=
      coloring_mirror_cong_slideReady hok hok' h
    have hf := coloring_mirror_any_eq_neg_F_slideReady e hok colM hcM hmM
    exact ⟨⟨colM, hcM, hmM, hf⟩, ⟨colM', hcM', hmM', hagree.symm.trans hf⟩⟩
  | transfer_odd e hok hports hne =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree⟩ :=
      coloring_transfer_odd_slideReady e hok hports hne
    let eL : TwistExpr := .mulBottom (.addRight e .neg) .pos
    have hokL : eL.slideReady :=
      TwistExpr.mulBottom_slideReady _ _
        (TwistExpr.addRight_slideReady e .neg hok)
    have hcL' : eL.diagram.IsColored colL := by
      simpa [eL, TwistExpr.diagram, crossingTangle] using hcL
    have hmL' : (ColorMatrix.of eL.diagram colL).NotMono := by
      simpa [eL, TwistExpr.diagram, crossingTangle] using hmL
    have hfL := coloring_fraction_eq_F eL hokL colL hcL'
      (twist_coloring_diagonal_slideReady eL hokL colL hcL') hmL'
    have hLd :
        ColorMatrix.of ((e.diagram.add RationalTangles.negOne).mul
          RationalTangles.one) colL =
          ColorMatrix.of eL.diagram colL := by
      simp [eL, TwistExpr.diagram, crossingTangle]
    refine ⟨⟨colL, hcL, hmL, ?_⟩, ⟨colR, hcR, hmR, ?_⟩⟩
    · rw [hLd, hfL]
    · rw [hagree.symm, hLd, hfL]
  | transfer_odd_neg e hok hports hne =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree⟩ :=
      coloring_transfer_odd_neg_slideReady e hok hports hne
    let eL : TwistExpr := .mulBottom (.addRight e .pos) .neg
    have hokL : eL.slideReady :=
      TwistExpr.mulBottom_slideReady _ _
        (TwistExpr.addRight_slideReady e .pos hok)
    have hcL' : eL.diagram.IsColored colL := by
      simpa [eL, TwistExpr.diagram, crossingTangle] using hcL
    have hmL' : (ColorMatrix.of eL.diagram colL).NotMono := by
      simpa [eL, TwistExpr.diagram, crossingTangle] using hmL
    have hfL := coloring_fraction_eq_F eL hokL colL hcL'
      (twist_coloring_diagonal_slideReady eL hokL colL hcL') hmL'
    have hLd :
        ColorMatrix.of ((e.diagram.add RationalTangles.one).mul
          RationalTangles.negOne) colL =
          ColorMatrix.of eL.diagram colL := by
      simp [eL, TwistExpr.diagram, crossingTangle]
    refine ⟨⟨colL, hcL, hmL, ?_⟩, ⟨colR, hcR, hmR, ?_⟩⟩
    · rw [hLd, hfL]
    · rw [hagree.symm, hLd, hfL]
  | rot180 e hok =>
    obtain ⟨col, col', hc, hc', hm, hm', _hM, hf'⟩ :=
      coloring_rot180_slideReady e hok
    exact ⟨⟨col, hc, hm, coloring_fraction_eq_F e hok col hc
        (twist_coloring_diagonal_slideReady e hok col hc) hm⟩,
      ⟨col', hc', hm', hf'⟩⟩
  | rot180_rev e hok =>
    obtain ⟨col, col', hc, hc', hm, hm', _hM, hf'⟩ :=
      coloring_rot180_slideReady e hok
    exact ⟨⟨col', hc', hm', hf'⟩,
      ⟨col, hc, hm, coloring_fraction_eq_F e hok col hc
        (twist_coloring_diagonal_slideReady e hok col hc) hm⟩⟩
  | flype_slide_add e hok s hne =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree, hfL⟩ :=
      coloring_flype_slide_add_slideReady e hok s hne
    exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩
  | flype_slide_mul e hok s hne =>
    obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree, hfL⟩ :=
      coloring_flype_slide_mul_slideReady e hok s hne
    exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩

/-- Standard-form `F` of `slideReady` twist expressions is unchanged along
    `SlideReadyIsotopy`. Both endpoints must themselves be `slideReady`
    twist diagrams (uniqueness of `f = F` on that class). This is not
    Theorem 2: `Isotopic` can leave the twist/`slideReady` class, and
    `SlideReadyIsotopy` is a proper fragment of `Isotopic`. -/
theorem TwistExpr.toStandard_fraction_SlideReadyIsotopy {e₁ e₂ : TwistExpr}
    {v : CFValue}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : SlideReadyIsotopy e₁.diagram e₂.diagram v) :
    e₁.toStandard.fraction = e₂.toStandard.fraction := by
  obtain ⟨⟨col, hc, hm, hf⟩, ⟨col', hc', hm', hf'⟩⟩ :=
    SlideReadyIsotopy.has_fraction h
  have hF1 := coloring_fraction_eq_F e₁ hok₁ col hc
    (twist_coloring_diagonal_slideReady e₁ hok₁ col hc) hm
  have hF2 := coloring_fraction_eq_F e₂ hok₂ col' hc'
    (twist_coloring_diagonal_slideReady e₂ hok₂ col' hc') hm'
  exact hF1.symm.trans (hf.trans (hf'.symm.trans hF2))

/-- The carried coloring fraction equals standard-form `F` at a
    `slideReady` endpoint. -/
theorem TwistExpr.toStandard_fraction_eq_SlideReadyIsotopy_value {e₁ e₂ : TwistExpr}
    {v : CFValue}
    (hok₁ : e₁.slideReady) (_hok₂ : e₂.slideReady)
    (h : SlideReadyIsotopy e₁.diagram e₂.diagram v) :
    v = e₁.toStandard.fraction := by
  obtain ⟨⟨col, hc, hm, hf⟩, _⟩ := SlideReadyIsotopy.has_fraction h
  have hF1 := coloring_fraction_eq_F e₁ hok₁ col hc
    (twist_coloring_diagonal_slideReady e₁ hok₁ col hc) hm
  exact hf.symm.trans hF1

/-- Standard-form `F` of standard-form expressions is unchanged along
    `SlideReadyIsotopy`. Not invariance along full `Isotopic`. -/
theorem StandardExpr.fraction_SlideReadyIsotopy {e₁ e₂ : StandardExpr}
    {v : CFValue}
    (h : SlideReadyIsotopy e₁.diagram e₂.diagram v) :
    e₁.fraction = e₂.fraction := by
  have h' : SlideReadyIsotopy e₁.toTwist.diagram e₂.toTwist.diagram v := by
    simpa [StandardExpr.toTwist_diagram] using h
  have hf := TwistExpr.toStandard_fraction_SlideReadyIsotopy
    (StandardExpr.toTwist_slideReady e₁)
    (StandardExpr.toTwist_slideReady e₂) h'
  simpa [StandardExpr.toTwist_toStandard] using hf

/-- If two `slideReady` twist diagrams are related by `SlideReadyIsotopy`,
    any non-monochrome colorings of their `rot180` PD-codes have the same
    coloring fraction `F`. Same uniqueness plus `F`-invariance as
    `coloring_rot180_cong_slideReady`. -/
theorem coloring_rot180_cong_SlideReadyIsotopy {e e' : TwistExpr} {v : CFValue}
    (hok : e.slideReady) (hok' : e'.slideReady)
    (h : SlideReadyIsotopy e.diagram e'.diagram v)
    (col col' : Nat → Int)
    (hc : e.diagram.rot180.IsColored col)
    (hc' : e'.diagram.rot180.IsColored col')
    (hm : (ColorMatrix.of e.diagram.rot180 col).NotMono)
    (hm' : (ColorMatrix.of e'.diagram.rot180 col').NotMono) :
    (ColorMatrix.of e.diagram.rot180 col).fraction =
      (ColorMatrix.of e'.diagram.rot180 col').fraction := by
  have hf := coloring_rot180_any_eq_F_slideReady e hok col hc hm
  have hf' := coloring_rot180_any_eq_F_slideReady e' hok' col' hc' hm'
  have hF := TwistExpr.toStandard_fraction_SlideReadyIsotopy hok hok' h
  rw [hf, hf', hF]

/-- Fraction-level `rot180_cong` as a `SlideReadyIsotopy` between the
    rotated diagrams. Composes `rot180_rev`, the given path, and `rot180`
    after identifying the carried value with standard-form `F`. Not a
    constructor of `ColoringIsotopy`. -/
theorem SlideReadyIsotopy.rot180_cong {e e' : TwistExpr} {v : CFValue}
    (hok : e.slideReady) (hok' : e'.slideReady)
    (h : SlideReadyIsotopy e.diagram e'.diagram v) :
    SlideReadyIsotopy e.diagram.rot180 e'.diagram.rot180
      e.toStandard.fraction := by
  have hv : v = e.toStandard.fraction :=
    TwistExpr.toStandard_fraction_eq_SlideReadyIsotopy_value hok hok' h
  have hF : e.toStandard.fraction = e'.toStandard.fraction :=
    TwistExpr.toStandard_fraction_SlideReadyIsotopy hok hok' h
  have hpath : SlideReadyIsotopy e.diagram e'.diagram e.toStandard.fraction :=
    hv ▸ h
  have h2 : SlideReadyIsotopy e'.diagram e'.diagram.rot180
      e.toStandard.fraction :=
    hF ▸ SlideReadyIsotopy.rot180 e' hok'
  exact (SlideReadyIsotopy.rot180_rev e hok).trans (hpath.trans h2)

/-! ## `HasColoringFraction` along colorable `Isotopic` constructors

Carry a non-monochrome coloring fraction along the generators we can
color, even when the result is not a `TwistExpr`. Unrestricted
`Isotopic.flype_slide_add` / `flype_slide_mul` (no `DiagonalSum`/`hne`)
and `Isotopic.invert_add` at a summand `[∞]` (or a non-`[0]` diagram
of fraction `0`) are not included: they block induction of
`HasColoringFraction` along `Isotopic`. None of these is added to
`ColoringIsotopy`. Invert-add with a `[0]` summand is a theorem on
`HasColoringFraction`, not a constructor of `ColoringIsotopy`.
-/

/-- `ColoringIsotopy` preserves a carried coloring fraction. -/
theorem HasColoringFraction.of_ColoringIsotopy {D E : TangleDiagram} {v : CFValue}
    (h : ColoringIsotopy D E) (hf : HasColoringFraction D v) :
    HasColoringFraction E v := by
  obtain ⟨col, hc, hm, hfrac⟩ := hf
  obtain ⟨col', hc', hMat, hfrac'⟩ := coloring_fraction_ColoringIsotopy h col hc
  refine ⟨col', hc', ?_, hfrac'.trans hfrac⟩
  simpa [hMat] using hm

/-- Planar `180°` under `DiagonalSum` preserves the coloring fraction on
    an arbitrary diagram (not necessarily twist-form). -/
theorem HasColoringFraction.rot180_diagonal {D : TangleDiagram} {v : CFValue}
    (col : Nat → Int) (hc : D.IsColored col)
    (hm : (ColorMatrix.of D col).NotMono)
    (hd : (ColorMatrix.of D col).DiagonalSum)
    (hfrac : (ColorMatrix.of D col).fraction = v) :
    HasColoringFraction D.rot180 v := by
  obtain ⟨col', hc', hM, hf'⟩ := coloring_fraction_rot180_diagonal D col hc hd
  refine ⟨col', hc', ?_, hf'.trans hfrac⟩
  simpa [hM] using hm

/-- Invert of a `slideReady` twist is colored with fraction `1/F`. -/
theorem HasColoringFraction.invert_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction e.diagram.invert e.toStandard.fraction.inv := by
  obtain ⟨col', hc', hm', hf'⟩ :=
    coloring_invert_inv_eq_F_slideReady_colorFrom e hok
  exact ⟨col', hc', hm', hf'⟩

/-- PD-mirror of a `slideReady` twist is colored with fraction `-F`. -/
theorem HasColoringFraction.mirror_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction e.diagram.mirror e.toStandard.fraction.neg := by
  obtain ⟨col, hc, hm, _hd, hf⟩ := coloring_pd_mirror_of_colorFrom e hok
  exact ⟨col, hc, hm, hf⟩

/-- Planar `180°` of a `slideReady` twist is colored with fraction `F`. -/
theorem HasColoringFraction.rot180_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction e.diagram.rot180 e.toStandard.fraction := by
  obtain ⟨_col, col', _hc, hc', _hm, hm', _hM, hf'⟩ :=
    coloring_rot180_slideReady e hok
  exact ⟨col', hc', hm', hf'⟩

/-- Restricted Figure 5 slide on a sum: `DiagonalSum` and distinct left
    ports. Not unrestricted `Isotopic.flype_slide_add`. -/
theorem HasColoringFraction.flype_slide_add {s : CrossingSign}
    {t : TangleDiagram} {v : CFValue} (col : Nat → Int)
    (hc : ((crossingTangle s).add t).IsColored col)
    (hne : t.NW ≠ t.SW)
    (hd : (ColorMatrix.of ((crossingTangle s).add t) col).DiagonalSum)
    (hm : (ColorMatrix.of ((crossingTangle s).add t) col).NotMono)
    (hfrac : (ColorMatrix.of ((crossingTangle s).add t) col).fraction = v) :
    HasColoringFraction (t.rot180.add (crossingTangle s)) v := by
  obtain ⟨col', hc', hM, hf'⟩ :=
    coloring_fraction_flype_slide_add s t col hc hne hd
  refine ⟨col', hc', ?_, hf'.trans hfrac⟩
  simpa [hM] using hm

/-- Restricted Figure 5 slide on a product. Not unrestricted
    `Isotopic.flype_slide_mul`. -/
theorem HasColoringFraction.flype_slide_mul {s : CrossingSign}
    {t : TangleDiagram} {v : CFValue} (col : Nat → Int)
    (hc : ((crossingTangle s).mul t).IsColored col)
    (hne : t.NW ≠ t.NE)
    (hd : (ColorMatrix.of ((crossingTangle s).mul t) col).DiagonalSum)
    (hm : (ColorMatrix.of ((crossingTangle s).mul t) col).NotMono)
    (hfrac : (ColorMatrix.of ((crossingTangle s).mul t) col).fraction = v) :
    HasColoringFraction (t.rot180.mul (crossingTangle s)) v := by
  obtain ⟨col', hc', hM, hf'⟩ :=
    coloring_fraction_flype_slide_mul s t col hc hne hd
  refine ⟨col', hc', ?_, hf'.trans hfrac⟩
  simpa [hM] using hm

/-- Both sides of Figure 14, when defined on a `slideReady` diagram. -/
theorem HasColoringFraction.transfer_odd_slideReady (e : TwistExpr)
    (hok : e.slideReady)
    (hports : e.diagram.NW ≠ e.diagram.NE)
    (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
    HasColoringFraction
        ((e.diagram.add RationalTangles.negOne).mul RationalTangles.one)
        (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).toStandard.fraction ∧
      HasColoringFraction
        (RationalTangles.one.add e.diagram.mirror.invert)
        (TwistExpr.mulBottom (TwistExpr.addRight e .neg) .pos).toStandard.fraction :=
  SlideReadyIsotopy.has_fraction
    (SlideReadyIsotopy.transfer_odd e hok hports hne)

/-- Figure 14 with switched signs, when defined. -/
theorem HasColoringFraction.transfer_odd_neg_slideReady (e : TwistExpr)
    (hok : e.slideReady)
    (hports : e.diagram.NW ≠ e.diagram.NE)
    (hne : (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NW ≠
      (ColorMatrix.of e.diagram (e.colorFrom 0 1)).NE) :
    HasColoringFraction
        ((e.diagram.add RationalTangles.one).mul RationalTangles.negOne)
        (TwistExpr.mulBottom (TwistExpr.addRight e .pos) .neg).toStandard.fraction ∧
      HasColoringFraction
        (RationalTangles.negOne.add e.diagram.mirror.invert)
        (TwistExpr.mulBottom (TwistExpr.addRight e .pos) .neg).toStandard.fraction :=
  SlideReadyIsotopy.has_fraction
    (SlideReadyIsotopy.transfer_odd_neg e hok hports hne)

/-- Invert-add of two `rightBottom`/`slideReady` diagrams with finite
    nonzero `F`: both `(T+S)ⁱ` and `Sⁱ*Tⁱ` carry
    `(F(T)+F(S))⁻¹`. Skip `0`/`∞`. Not a `TwistExpr`, so not a
    `SlideReadyIsotopy` constructor, and not unrestricted `flype_slide`. -/
theorem HasColoringFraction.invert_add_two_rightBottom (e f : TwistExpr)
    (hrb : e.rightBottom) (hrb' : f.rightBottom)
    (hok : e.slideReady) (hok' : f.slideReady)
    (hfin : e.toStandard.fraction ≠ .inf)
    (hfin' : f.toStandard.fraction ≠ .inf)
    (hnz : e.toStandard.fraction ≠ (0 : CFValue))
    (hnz' : f.toStandard.fraction ≠ (0 : CFValue)) :
    HasColoringFraction (e.diagram.add f.diagram).invert
        (e.toStandard.fraction.add f.toStandard.fraction).inv ∧
      HasColoringFraction (f.diagram.invert.mul e.diagram.invert)
        (e.toStandard.fraction.add f.toStandard.fraction).inv := by
  obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree, hfL⟩ :=
    coloring_invert_add_two_rightBottom e f hrb hrb' hok hok' hfin hfin' hnz hnz'
  exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩

/-- Invert-add with right summand `[0]`: both `(T+[0])ⁱ` and `[0]ⁱ*Tⁱ`
    carry `F(T)⁻¹`. Not a `ColoringIsotopy`. -/
theorem HasColoringFraction.invert_add_slideReady_zero (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction (e.diagram.add TangleDiagram.zero).invert
        (e.toStandard.fraction.add (0 : CFValue)).inv ∧
      HasColoringFraction (TangleDiagram.zero.invert.mul e.diagram.invert)
        (e.toStandard.fraction.add (0 : CFValue)).inv := by
  obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree, hfL⟩ :=
    coloring_invert_add_slideReady_zero e hok
  exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩

/-- Invert-add with left summand `[0]`: both `([0]+T)ⁱ` and `Tⁱ*[0]ⁱ`
    carry `F(T)⁻¹`. Not a `ColoringIsotopy`. -/
theorem HasColoringFraction.invert_add_zero_slideReady (e : TwistExpr)
    (hok : e.slideReady) :
    HasColoringFraction (TangleDiagram.zero.add e.diagram).invert
        ((0 : CFValue).add e.toStandard.fraction).inv ∧
      HasColoringFraction (e.diagram.invert.mul TangleDiagram.zero.invert)
        ((0 : CFValue).add e.toStandard.fraction).inv := by
  obtain ⟨colL, colR, hcL, hcR, hmL, hmR, hagree, hfL⟩ :=
    coloring_invert_add_zero_slideReady e hok
  exact ⟨⟨colL, hcL, hmL, hfL⟩, ⟨colR, hcR, hmR, hagree.symm.trans hfL⟩⟩

end RationalTangles
