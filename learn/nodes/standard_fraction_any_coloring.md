---
id: standard_fraction_any_coloring
title: On standard forms, every coloring gives F
summary: '**The surprise:** gluing [+1] on the right adds exactly 1 to (NE − NW)/(NE − SE) for every coloring at
  once. Induction on the recipe does the rest.'
review: draft
authors:
- grok-bot
quiz:
- q: What kind of proof is it?
  type: choice
  choices:
  - Induction on the standard form
  - A computer search
  answer: 0
  explain: '`induction e generalizing col`.'
- q: Does it need slideReady?
  type: choice
  choices:
  - No, standard forms are always fine
  - 'Yes'
  answer: 0
  explain: No port conditions on right additions or bottom products.
- q: Does it need the diagonal rule as a hypothesis?
  type: choice
  choices:
  - No; it proves it along the way (standard_coloring_diagonal)
  - 'Yes'
  answer: 0
  explain: The proof calls `standard_coloring_diagonal`.
---
## Plain English

**Theorem (`standard_fraction_any_coloring`, ColorFraction.lean lines 860-941).** For a [standard form](#/node/StandardExpr) e and any non-constant coloring of its diagram, the coloring fraction is [`e.fraction`](#/node/StandardExpr.fraction). Induction: [0] and [∞] directly, then each right addition or bottom product transforms the fraction like the arithmetic.
