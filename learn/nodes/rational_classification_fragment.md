---
id: rational_classification_fragment
title: 'PARTIAL: Conway''s classification on the proved fragment'
summary: '**The surprise:** the theorem named ''classification'' is not an if-and-only-if. It assumes two twist
  recipes are already linked by coloring-safe moves, and concludes their fractions agree (and that they are isotopic,
  which the hypothesis nearly gives already).'
review: draft
authors:
- grok-bot
caveats:
- '**PARTIAL.** Not Conway''s theorem: no ''isotopic ⇒ same fraction'' direction for `Isotopic`, and no ''same fraction
  ⇒ ColoringIsotopy''.'
- '`noMulTop` matters for the *meaning* of the statement: on recipes with a top product, `TwistExpr.fraction` computes
  1/(s + F) where the Conway product needs 1/(s + 1/F) (see TwistExpr.fraction). The Claude audit calls this load-bearing.'
- The second conjunct depends on `native_decide`, through the canonical-form proof (Claude audit, §6; not confirmed
  with `#print axioms` because nothing was built).
- '`Isotopic` includes assumed moves; one of them (`flype_slide_add/mul`) may be stronger than real isotopy for
  non-rational pieces (see Isotopic).'
widgets:
- type: walkthrough
  title: How DiagonalSumGeneral.lean proves it (DiagonalSumGeneral.lean, lines 584-592)
  config:
    steps:
    - text: Color e₁ with the step-by-step coloring colorFrom 0 1, carry it along the coloring-safe moves to e₂,
        and read off f = F on both ends
      lean: have hf := TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom
      note: This gives equal standard-form fractions; noMulTop turns them into equal recipe fractions.
      link: coloring_fraction_invariant_ColoringIsotopy
      uses:
      - TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom
      - TwistExpr.fraction_eq_toStandard_of_noMulTop
    - text: Equal fractions ⇒ isotopic diagrams, by canonical continued fractions
      lean: exact ⟨hf, twist_same_fraction_isotopic_of_noMulTop hn₁ hn₂ hf⟩
      note: The reconstruction half. It does not use the coloring at all.
      link: twist_same_fraction_isotopic_of_noMulTop
      hard: true
quiz:
- q: Is this Lean theorem an 'if and only if' like Conway's?
  type: choice
  choices:
  - Yes, both directions for Isotopic
  - 'No: both conclusions follow from a ColoringIsotopy hypothesis; there is no ''isotopic ⇒ same fraction'' for
    Isotopic'
  - Yes, both directions for ColoringIsotopy
  answer: 1
  explain: 'The hypothesis is `h : ColoringIsotopy e₁.diagram e₂.diagram` and the conclusion is `e₁.fraction = e₂.fraction
    ∧ Isotopic e₁.diagram e₂.diagram`. Nothing assumes `Isotopic` and concludes equal fractions.'
- q: Which recipes are excluded by `noMulTop`?
  type: choice
  choices:
  - Recipes that add a crossing on the left
  - Recipes that ever multiply a crossing on top
  - Recipes with more than 10 crossings
  - Recipes containing [∞]
  answer: 1
  explain: '`noMulTop` is false exactly when a `mulTop` constructor appears. On such recipes the repo''s `TwistExpr.fraction`
    is not the Conway fraction, so the restriction matters for the meaning of the statement, not just its proof.'
- q: Why does the second conjunct (`Isotopic e₁.diagram e₂.diagram`) add little?
  type: choice
  choices:
  - Because Isotopic is trivial
  - Because almost every ColoringIsotopy move is also an Isotopic move, so the hypothesis nearly gives it directly
  - Because it is assumed as a hypothesis
  answer: 1
  explain: Of the 19 `ColoringIsotopy` constructors, 18 map directly onto `Isotopic` constructors (some through
    `symm`); only the local R3 model `r3Local` has no bridge lemma in the repo (cf. Claude audit, §1).
- q: Does this theorem apply to an arbitrary rational tangle diagram?
  type: choice
  choices:
  - 'Yes'
  - 'No: it is about diagrams of twist recipes (TwistExpr), and the fraction belongs to the recipe'
  answer: 1
  explain: 'The objects are `e₁ e₂ : TwistExpr`. The fraction of a rational tangle up to isotopy is not defined
    in this development.'
---
## Plain English

**Conway's theorem (1970).** Two rational tangles are isotopic **if and only if** they have the same fraction.

**What this Lean theorem says (`rational_classification_fragment`, DiagonalSumGeneral.lean lines 584-592).** Take two twist recipes e₁ and e₂ ([`TwistExpr`](#/node/TwistExpr)) such that

1. neither recipe ever multiplies a crossing on **top** ([`noMulTop`](#/node/TwistExpr.noMulTop)),
2. both pass a port side-condition ([`slideReady`](#/node/TwistExpr.slideReady)), and
3. the diagram of e₁ can be turned into the diagram of e₂ by **coloring-safe moves** ([`ColoringIsotopy`](#/node/ColoringIsotopy)): Reidemeister I–III in the forms the project handles, planar isotopy, local flypes and gluing congruences, applied in one direction.

Then

* their fractions are equal ([`TwistExpr.fraction`](#/node/TwistExpr.fraction)), **and**
* their diagrams are [`Isotopic`](#/node/Isotopic).

### How to read it

Both conclusions hang off the same hypothesis 3. So this is the shape *"coloring-safe moves ⇒ same fraction"* (one half of Conway, on a smaller move set), with the other half (*"same fraction ⇒ isotopic"*) applied straight afterwards. The two halves never meet in an "if and only if" for a single relation:

* the invariance half is proved only along `ColoringIsotopy`;
* the reconstruction half lands in `Isotopic`, which is bigger.

The second conjunct says little beyond the hypothesis. Every coloring-safe move except the local Reidemeister III model is literally a constructor of `Isotopic` too, so `ColoringIsotopy ⇒ Isotopic` is one missing bridging lemma away from free. The proof doesn't use that; it goes the long way, through canonical continued fractions ([`twist_same_fraction_isotopic_of_noMulTop`](#/node/twist_same_fraction_isotopic_of_noMulTop)).

The docstring is candid about all this: "Full Isotopic invariance in either direction is not claimed."
