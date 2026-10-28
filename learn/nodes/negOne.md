---
id: negOne
title: The single crossing [−1]
summary: '**The surprise:** [−1] isn''t built from scratch: it is defined as the mirror image of [+1], so all the
  mirror machinery is tested on the smallest case.'
review: draft
authors:
- grok-bot
quiz:
- q: How is [−1] defined?
  type: choice
  choices:
  - As a new crossing list
  - As the mirror of [+1]
  answer: 1
  explain: '`def negOne : TangleDiagram := one.mirror`.'
- q: What is its fraction?
  type: choice
  choices:
  - '1'
  - −1
  - '0'
  answer: 1
  explain: '`TwistExpr.fraction negOne = .ofInt (-1)`.'
- q: How many crossings does it have?
  type: choice
  choices:
  - '0'
  - '1'
  - '2'
  answer: 1
  explain: Mirroring keeps the single crossing and switches it.
---
## Plain English

**Definition (`negOne`, IntegerTangle.lean lines 36-37).** `one.mirror`: [+1] with its crossing switched ([`TangleDiagram.mirror`](#/node/TangleDiagram.mirror)). Its fraction is −1.
