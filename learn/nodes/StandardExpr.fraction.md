---
id: StandardExpr.fraction
title: The fraction of a standard form
summary: '**The surprise:** this is the trustworthy fraction: headlines 3 and 4 state their F this way (after rewriting
  into standard form), so they avoid the top-product slip in the recipe fraction.'
review: draft
authors:
- grok-bot
quiz:
- q: Bottom product by [−1] sends F to?
  type: choice
  choices:
  - F − 1
  - 1/(1/F − 1)
  - −F
  answer: 1
  explain: '`(e.fraction.inv.add (.ofInt (-1))).inv`.'
- q: Fraction of [0] + [+1] + [+1]?
  type: choice
  choices:
  - '2'
  - 1/2
  - '0'
  answer: 0
  explain: 0 + 1 + 1.
- q: Which headlines use this fraction?
  type: choice
  choices:
  - The coloring headlines (3 and 4)
  - None
  answer: 0
  explain: They state `e.toStandard.fraction`.
---
## Plain English

**Definition (`StandardExpr.fraction`, ColorFraction.lean lines 627-633).** [0] ↦ 0, [∞] ↦ ∞, right addition of [±1]: F ↦ F ± 1, bottom product: F ↦ 1/(1/F ± 1).
