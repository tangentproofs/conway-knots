---
id: crossingTangle
title: '[±1] as a function of a sign'
summary: '**The surprise:** every twist recipe adds or multiplies by exactly this one-crossing tangle, so all rational
  tangles are built from a single kind of building block.'
review: draft
authors:
- grok-bot
quiz:
- q: What is `crossingTangle .neg`?
  type: choice
  choices:
  - '[+1]'
  - '[−1]'
  - '[0]'
  answer: 1
  explain: '`| .neg => negOne`.'
- q: How many crossings does `crossingTangle s` have?
  type: choice
  choices:
  - '0'
  - '1'
  - '2'
  answer: 1
  explain: Both [+1] and [−1] have one crossing.
- q: Where is it used?
  type: choice
  choices:
  - In every add/multiply step of a twist recipe
  - Only in [∞]
  answer: 0
  explain: '`TwistExpr.diagram` glues `crossingTangle s` at each step.'
---
## Plain English

**Definition (`crossingTangle`, IntegerTangle.lean lines 40-42).** `pos` ↦ [+1] ([`one`](#/node/one)), `neg` ↦ [−1] ([`negOne`](#/node/negOne)).
