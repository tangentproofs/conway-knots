---
id: CFValue.add
title: Adding fractions with ∞
summary: '**The surprise:** ∞ + x = ∞ matches the picture: adding a twist beside [∞] makes a kink that untwists
  back to [∞].'
review: draft
authors:
- grok-bot
quiz:
- q: What is ∞ + (−1)?
  type: choice
  choices:
  - ∞
  - −1
  - '0'
  answer: 0
  explain: ∞ is absorbing.
- q: What is 1/2 + 1/3?
  type: choice
  choices:
  - 5/6
  - 2/5
  - 1/6
  answer: 0
  explain: Ordinary rational addition.
- q: Why is ∞ + 1 = ∞ geometrically sensible?
  type: choice
  choices:
  - '[∞] + [1] is a kink, isotopic to [∞]'
  - It isn't
  answer: 0
  explain: Reidemeister I removes the kink.
---
## Plain English

**Definition (`CFValue.add`, ContinuedFraction.lean lines 52-55).** Rationals add as usual; if either side is ∞, the result is ∞.
