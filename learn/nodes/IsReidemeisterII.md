---
id: IsReidemeisterII
title: 'Reidemeister II: two opposite crossings'
summary: '**The surprise:** [+1] + [−1] untwists to [0] by one R2 move. Its PD-code check is one of the six facts
  the repo proves with native_decide.'
review: draft
authors:
- grok-bot
quiz:
- q: How many crossings does an R2 move remove?
  type: choice
  choices:
  - '1'
  - '2'
  - '3'
  answer: 1
  explain: An R2 pair.
- q: Which tangle reduces to [0] by R2?
  type: choice
  choices:
  - '[+1] + [−1]'
  - '[+1] + [+1]'
  answer: 0
  explain: Opposite crossings cancel.
- q: Is R2 symmetric here?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`IsReidemeisterIIAdd D E ∨ IsReidemeisterIIAdd E D`.'
---
## Plain English

**Definition (`IsReidemeisterII`, Reidemeister.lean lines 349-350).** One of D, E has an extra pair of crossings forming a bigon (`IsR2Pair`) whose collapse (`collapseR2`) gives the other, up to planar isotopy.
