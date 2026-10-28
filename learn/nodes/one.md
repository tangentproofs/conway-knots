---
id: one
title: The single crossing [+1]
summary: '**The surprise:** in any coloring of [+1], (NE − NW)/(NE − SE) is exactly 1, whatever colors you choose
  (as long as they are not all equal). That is f = F on the smallest example.'
review: draft
authors:
- grok-bot
quiz:
- q: Which corners does the over-strand of [+1] join?
  type: choice
  choices:
  - NW and SE
  - NE and SW
  - NW and NE
  answer: 0
  explain: Ports 0 and 2 (over) are at NW and SE.
- q: If NW = SE = 3 and NE = 7, what is the SW color?
  type: choice
  choices:
  - '7'
  - −1
  - '3'
  - '10'
  answer: 1
  explain: 'α + γ = 2β: 7 + γ = 6, so γ = −1.'
- q: What is the coloring fraction of [+1] with those colors?
  type: choice
  choices:
  - '1'
  - 7/3
  - −1
  answer: 0
  explain: (NE − NW)/(NE − SE) = (7 − 3)/(7 − 3) = 1.
---
## Plain English

**Definition (`one`, IntegerTangle.lean lines 28-33).** One positive crossing with arcs 0, 1, 2, 3 at NW, NE, SE, SW. The over-strand runs NW–SE.

Color the over-strand β and the NE under-arc α. The rule forces SW = 2β − α. Then (NE − NW)/(NE − SE) = (α − β)/(α − β) = 1.

[−1] ([`negOne`](#/node/negOne)) is its mirror image.
