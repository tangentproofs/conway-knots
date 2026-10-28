---
id: CrossingSign.cfValue
title: 'The number of a crossing sign: +1 or −1'
summary: '**The surprise:** this tiny map is where pictures become arithmetic: every twist contributes exactly ±1
  to a continued fraction.'
review: draft
authors:
- grok-bot
quiz:
- q: What is the value of `neg`?
  type: choice
  choices:
  - '0'
  - '1'
  - −1
  - ∞
  answer: 2
  explain: '`.neg => .ofInt (-1)`.'
- q: What is the value of `pos`?
  type: choice
  choices:
  - '1'
  - −1
  - '2'
  answer: 0
  explain: '`.pos => 1`.'
- q: What type do the values have?
  type: choice
  choices:
  - ℤ
  - CFValue (a rational or ∞)
  - ℕ
  answer: 1
  explain: '`CrossingSign.cfValue : CrossingSign → CFValue`.'
---
## Plain English

**Definition (`CrossingSign.cfValue`, TangleFraction.lean lines 23-25).** `pos` ↦ 1 and `neg` ↦ −1, as [`CFValue`](#/node/CFValue)s. These are the fractions of [+1] and [−1].
