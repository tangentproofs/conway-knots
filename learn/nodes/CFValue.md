---
id: CFValue
title: 'Fractions with infinity: ℚ ∪ {∞}'
summary: '**The surprise:** there is one infinity, not two: −∞ = ∞. Tangle fractions live on the projective line,
  where 1/0 is a perfectly good value (the tangle [∞]).'
review: draft
authors:
- grok-bot
quiz:
- q: What is 1/0 in CFValue?
  type: choice
  choices:
  - Undefined
  - inf
  - '0'
  answer: 1
  explain: '`inv (ofRat 0) = inf`.'
- q: What is ∞ + 3?
  type: choice
  choices:
  - ∞
  - '3'
  - undefined
  answer: 0
  explain: '`| inf, _ => inf`.'
- q: What is −∞?
  type: choice
  choices:
  - −∞, a separate value
  - ∞ itself
  answer: 1
  explain: '`neg inf = inf` (one point at infinity).'
---
## Plain English

**Definition (`CFValue`, ContinuedFraction.lean lines 35-38).** Either a rational `ofRat q` or `inf`. Arithmetic: [`inv`](#/node/CFValue.inv) sends 0 ↦ ∞ and ∞ ↦ 0; [`add`](#/node/CFValue.add) makes ∞ absorbing; negation fixes ∞.
