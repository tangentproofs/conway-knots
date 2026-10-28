---
id: ArithmeticCF
title: A continued fraction [a₁, …, aₙ]
summary: '**The surprise:** a continued fraction is both a number and a tangle: [a₁, …, aₙ] is a stack of horizontal
  and vertical twists.'
review: draft
authors:
- grok-bot
quiz:
- q: Can a later term be 0?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: '`later_ne_zero`.'
- q: Value of [2, 3]?
  type: choice
  choices:
  - 2 + 1/3 = 7/3
  - '5'
  - 2/3
  answer: 0
  explain: a₁ + 1/a₂.
- q: Can the first term be 0?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: Only later terms must be non-zero.
---
## Plain English

**Definition (`ArithmeticCF`, ContinuedFraction.lean lines 319-325).** A non-empty list of integer terms, all terms after the first non-zero. Its value is a₁ + 1/(a₂ + 1/(…)) in [`CFValue`](#/node/CFValue), and it has a tangle diagram `cf.tangle`.
