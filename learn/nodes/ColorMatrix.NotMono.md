---
id: ColorMatrix.NotMono
title: Not all boundary colors equal
summary: '**The surprise:** a constant coloring is always valid and tells you nothing, so every f = F statement
  must exclude it, and that''s all this hypothesis does.'
review: draft
authors:
- grok-bot
quiz:
- q: Is the constant coloring NotMono?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 1
  explain: All three of NW, NE, SE are equal, so it is monochrome.
- q: 'NW = 1, NE = 1, SE = 2: NotMono?'
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: NE ≠ SE, so not all three are equal.
- q: Why exclude constant colorings?
  type: choice
  choices:
  - They give 0/0
  - They violate the rule
  answer: 0
  explain: (NE − NW)/(NE − SE) would be 0/0.
---
## Plain English

**Definition (`ColorMatrix.NotMono`, ColorFraction.lean lines 23-24).** Not (NW = NE and NE = SE).
