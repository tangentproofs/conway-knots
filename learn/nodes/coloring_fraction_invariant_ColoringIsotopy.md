---
id: coloring_fraction_invariant_ColoringIsotopy
title: 'PARTIAL: the fraction survives coloring-safe moves'
summary: '**The surprise:** the fraction can be read off by coloring arcs with integers and dividing two boundary
  differences. Colorings ride along Reidemeister moves, so the fraction can''t change; but the Lean gets this only
  for a smaller, one-way set of moves.'
review: draft
authors:
- grok-bot
caveats:
- '**PARTIAL.** Invariance along `ColoringIsotopy`, not `Isotopic`. That relation is smaller and directed: it has
  no `symm`, and it omits `flype_slide_add/mul`, `rot180_*`, `mirror_cong`, `invert_*` and `transfer_*`.'
- The `r1`/`r2` moves of `ColoringIsotopy` require `WellFormed` diagrams, and no lemma in the repo proves `WellFormed`
  for any construction, so those moves can be used only where a caller supplies it (Claude audit, §4–5).
- The refuted transports show that one proof technique (keep the boundary colors) fails across a crossing switch.
  They don't show that any move is false.
widgets:
- type: walkthrough
  title: How the invariance is proved (ColoringFractionEq.lean, lines 1299-1314)
  config:
    steps:
    - text: 'Start from a known coloring of e₁: colorFrom 0 1 (two starting colors 0 and 1, pushed through the recipe)'
      note: TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom (ColorFractionUnique.lean lines 1432-1440) supplies
        it, with its proofs that it is a coloring, satisfies the diagonal rule and is not constant.
      link: TwistExpr.colorFrom
    - text: On e₁, that coloring's fraction is the standard-form fraction (f = F)
      lean: have hf1 := coloring_fraction_eq_F e₁ hok₁ col hc hdiag hm
      link: coloring_fraction_eq_F
    - text: Carry the coloring across the coloring-safe moves; boundary colors are unchanged
      lean: obtain ⟨col', hc', hMat, hfrac⟩ := coloring_fraction_ColoringIsotopy h col hc
      link: coloring_fraction_ColoringIsotopy
      hard: true
    - text: Same boundary colors, so the diagonal rule and non-constancy carry over
      lean: simpa [hMat] using hdiag
    - text: On e₂, f = F again
      lean: have hf2 := coloring_fraction_eq_F e₂ hok₂ col' hc' hdiag' hm'
    - text: 'Chain: F(e₁) = f = F(e₂)'
      lean: exact hf1.symm.trans (hfrac.symm.trans hf2)
quiz:
- q: Along which relation is the fraction proved invariant?
  type: choice
  choices:
  - Isotopic (all moves)
  - ColoringIsotopy (a smaller, one-directional set of moves)
  - Equality of PD-codes only
  answer: 1
  explain: 'The hypothesis is `h : ColoringIsotopy e₁.diagram e₂.diagram`. ColoringIsotopy omits flype slides, 180°
    rotations, mirror/inversion moves and transfer moves, and has no symmetry constructor.'
- q: What is the coloring fraction of a colored diagram?
  type: choice
  choices:
  - (NE − NW)/(NE − SE) of the boundary colors, with ∞ when NE = SE
  - The sum of all colors
  - The number of crossings
  answer: 0
  explain: '`ColorMatrix.fraction`: `if M.NE - M.SE = 0 then .inf else .ofRat (Rat.divInt (M.NE - M.NW) (M.NE -
    M.SE))`.'
- q: Do the moves in ColoringIsotopy include the mirror and inversion moves?
  type: choice
  choices:
  - 'Yes'
  - No, and the Lean proves the simple 'keep the boundary colors' transport fails for them on tiny examples
  answer: 1
  explain: '`not_coloring_mirror_transport` and `not_coloring_invert_transport` (DiagonalSumGeneral.lean lines 261-354)
    are concrete counterexamples.'
- q: Which fraction appears in the first conclusion?
  type: choice
  choices:
  - '`e.fraction`'
  - '`e.toStandard.fraction`, the value after rewriting the recipe into standard form'
  answer: 1
  explain: The first conjunct is `e₁.toStandard.fraction = e₂.toStandard.fraction`. On top-product-free recipes
    it equals `e.fraction`.
---
## Plain English

**Kauffman–Lambropoulou's Theorem 2.** The fraction of a rational tangle is an isotopy invariant.

**What this Lean theorem says (`coloring_fraction_invariant_ColoringIsotopy`, DiagonalSumGeneral.lean lines 368-375).** Let e₁, e₂ be [`slideReady`](#/node/TwistExpr.slideReady) twist recipes whose diagrams are linked by coloring-safe moves ([`ColoringIsotopy`](#/node/ColoringIsotopy)) from e₁ to e₂. Then

1. their standard-form fractions agree ([`toStandard`](#/node/TwistExpr.toStandard), [`StandardExpr.fraction`](#/node/StandardExpr.fraction)), and
2. every coloring fraction of e₁'s diagram is a coloring fraction of e₂'s ([`HasColoringFraction`](#/node/HasColoringFraction)).

### Why colorings

Color every arc with an integer so that at each crossing the two under-arcs average to the over-arc ([`IsColored`](#/node/TangleDiagram.IsColored)). Read the four boundary colors NW, NE, SW, SE ([`ColorMatrix.of`](#/node/ColorMatrix.of)). The **coloring fraction** is (NE − NW)/(NE − SE) ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)).

* A coloring can be carried across each coloring-safe move without changing the boundary colors ([`coloring_fraction_ColoringIsotopy`](#/node/coloring_fraction_ColoringIsotopy)).
* On a twist diagram, *every* non-constant coloring has coloring fraction equal to the arithmetic fraction ([`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady)).

So: color e₁, carry the coloring across, and read the same number at e₂.
