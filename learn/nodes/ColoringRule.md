---
id: ColoringRule
title: The coloring rule at a crossing
summary: '**The surprise:** one linear equation per crossing, α + γ = 2β, is all it takes. Fox''s 3-colorings are
  this rule read modulo 3.'
review: draft
authors:
- grok-bot
quiz:
- q: Over-strand color 4, one under-arc 1. The other?
  type: choice
  choices:
  - '7'
  - '3'
  - '5'
  answer: 0
  explain: 1 + γ = 8.
- q: Must the two over-strand ports have the same color?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`col C.a0 = col C.a2`.'
- q: Is a constant coloring valid?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: β + β = 2β. That's why `NotMono` is needed.
---
## Plain English

**Definition (`ColoringRule`, Coloring.lean lines 45-46).** At a [crossing](#/node/Crossing), the over-strand ports 0 and 2 have the same color β, and the under-arcs' colors satisfy α + γ = 2β.
