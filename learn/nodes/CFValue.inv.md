---
id: CFValue.inv
title: Reciprocal with 1/0 = ∞
summary: '**The surprise:** the reciprocal is total here: 1/0 = ∞ and 1/∞ = 0, exactly what inverting [0] into [∞]
  and back requires.'
review: draft
authors:
- grok-bot
quiz:
- q: What is inv 0?
  type: choice
  choices:
  - '0'
  - ∞
  - undefined
  answer: 1
  explain: '`if q = 0 then inf`.'
- q: What is inv ∞?
  type: choice
  choices:
  - '0'
  - ∞
  - '1'
  answer: 0
  explain: '`| inf => ofRat 0`.'
- q: What is inv (−2)?
  type: choice
  choices:
  - '2'
  - −1/2
  - 1/2
  answer: 1
  explain: Ordinary reciprocal.
---
## Plain English

**Definition (`CFValue.inv`, ContinuedFraction.lean lines 47-49).** q ↦ 1/q for q ≠ 0; 0 ↦ ∞; ∞ ↦ 0.
