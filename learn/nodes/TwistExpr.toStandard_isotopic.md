---
id: TwistExpr.toStandard_isotopic
title: A recipe is isotopic to its standard form
summary: '**The surprise:** moving a crossing from the left of a tangle to its right is a flype, and it needs the
  tangle to be isotopic to its own half-turn, which is the flipping lemma, applied inside the induction.'
review: draft
authors:
- grok-bot
caveats:
- Uses the assumed move `flype_slide_add/mul` (see Isotopic).
quiz:
- q: Which move moves a left crossing to the right?
  type: choice
  choices:
  - Reidemeister II
  - The flype slide
  - Mirror
  answer: 1
  explain: '`flype_add s e.diagram`.'
- q: Why is T.rot180 ∼ T available?
  type: choice
  choices:
  - T is a twist diagram (rational), flipping lemma
  - It's true for every diagram
  answer: 0
  explain: '`e.isotopic_rot180`.'
- q: Does this lemma need noMulTop?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: It holds for every recipe; noMulTop is needed for the fraction, not the isotopy.
---
## Plain English

**Theorem (`TwistExpr.toStandard_isotopic`, FlippingLemma.lean lines 516-547).** Every recipe's diagram is [`Isotopic`](#/node/Isotopic) to the diagram of its [standard form](#/node/TwistExpr.toStandard). For `addLeft`: [s] + T ∼ T.rot180 + [s] (flype slide) ∼ T + [s] (T is isotopic to its half-turn). Likewise for `mulTop`.
