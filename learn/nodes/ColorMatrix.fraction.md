---
id: ColorMatrix.fraction
title: The coloring fraction (NE − NW)/(NE − SE)
summary: '**The surprise:** one division of boundary differences gives the tangle''s continued fraction, with ∞
  exactly when NE = SE.'
review: draft
authors:
- grok-bot
quiz:
- q: NW = 0, NE = 3, SE = 1. Fraction?
  type: choice
  choices:
  - 3/2
  - 2/3
  - '3'
  answer: 0
  explain: (3 − 0)/(3 − 1).
- q: When is it ∞?
  type: choice
  choices:
  - When NE = SE
  - When NW = 0
  answer: 0
  explain: '`if M.NE - M.SE = 0 then .inf`.'
- q: Does it use SW?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: Only NW, NE, SE appear (SW is fixed by the diagonal rule).
---
## Plain English

**Definition (`ColorMatrix.fraction`, Coloring.lean lines 79-81).** If NE = SE, ∞. Otherwise (NE − NW)/(NE − SE) as a rational.

Checks: [0] gives (a − a)/(a − c) = 0; [∞] gives ∞; [+1] gives 1.
