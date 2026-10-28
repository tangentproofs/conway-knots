---
id: ColorMatrix.of
title: Read off the boundary colors
summary: '**The surprise:** the matrix ignores the interior entirely: it reads the color of the arc at each corner,
  which is why moves that fix the corners can''t change it.'
review: draft
authors:
- grok-bot
quiz:
- q: What is `(ColorMatrix.of D col).NE`?
  type: choice
  choices:
  - col D.NE
  - D.NE
  - col 0
  answer: 0
  explain: '`NE := col D.NE`.'
- q: Does it depend on the crossings?
  type: choice
  choices:
  - No, only on the corner arcs
  - 'Yes'
  answer: 0
  explain: Only the four corners are read.
- q: 'For [0] with arc colors a, c: NW, NE, SW, SE ='
  type: choice
  choices:
  - a, a, c, c
  - a, c, a, c
  answer: 0
  explain: Arc 0 is NW–NE, arc 1 is SW–SE.
---
## Plain English

**Definition (`ColorMatrix.of`, Coloring.lean lines 64-68).** NW := col D.NW, and likewise for NE, SW, SE.
