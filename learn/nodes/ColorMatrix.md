---
id: ColorMatrix
title: The four boundary colors
summary: '**The surprise:** after all the crossings, only four numbers matter: the colors at NW, NE, SW, SE.'
review: draft
authors:
- grok-bot
quiz:
- q: How many entries?
  type: choice
  choices:
  - '2'
  - '4'
  - '8'
  answer: 1
  explain: NW, NE, SW, SE.
- q: What type are they?
  type: choice
  choices:
  - Integers
  - Fractions
  answer: 0
  explain: All four fields have type `Int`.
- q: Where do they come from?
  type: choice
  choices:
  - '`ColorMatrix.of D col`: the colors of the corner arcs'
  - The crossings' signs
  answer: 0
  explain: See ColorMatrix.of.
---
## Plain English

**Definition (`ColorMatrix`, Coloring.lean lines 54-59).** Four integers NW, NE, SW, SE, laid out as [[NW, NE], [SW, SE]].
