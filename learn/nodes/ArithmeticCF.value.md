---
id: ArithmeticCF.value
title: The value of a continued fraction
summary: '**The surprise:** [a₁, …, aₙ] is evaluated from the inside out with the same ∞-aware arithmetic as tangles,
  so [0] terms and 1/0 never cause trouble.'
review: draft
authors:
- grok-bot
quiz:
- q: Value of [1, 1, 3]?
  type: choice
  choices:
  - 7/4
  - '5'
  - 4/7
  answer: 0
  explain: 1 + 1/(1 + 1/3) = 1 + 3/4.
- q: Value of [3]?
  type: choice
  choices:
  - '3'
  - 1/3
  answer: 0
  explain: A single term.
- q: Which arithmetic is used?
  type: choice
  choices:
  - CFValue (with ∞)
  - Floats
  answer: 0
  explain: '`valueOfList` returns a CFValue.'
---
## Plain English

**Definition (`ArithmeticCF.value`, ContinuedFraction.lean lines 346-347).** a₁ + 1/(a₂ + 1/(… + 1/aₙ)) in [`CFValue`](#/node/CFValue) (`valueOfList`).
