---
id: TangleDiagram.rotate
title: Rotate a quarter turn
summary: '**The surprise:** turning a tangle 90° touches only the four corner labels. The crossing data is local,
  so nothing else in the code moves.'
review: draft
authors:
- grok-bot
quiz:
- q: What changes under `rotate`?
  type: choice
  choices:
  - Only the corner labels
  - Every crossing sign
  - The arc numbers
  answer: 0
  explain: '`{ T with NW := T.NE, NE := T.SE, SE := T.SW, SW := T.NW }`.'
- q: Rotating [0] gives?
  type: choice
  choices:
  - '[0]'
  - '[∞]'
  - '[1]'
  answer: 1
  explain: '`rotate_zero : TangleDiagram.zero.rotate = TangleDiagram.infinity`.'
- q: What does rotation do to the fraction?
  type: choice
  choices:
  - x ↦ −1/x
  - x ↦ x + 1
  - nothing
  answer: 0
  explain: F(Tʳ) = −1/F(T) (Kauffman–Lambropoulou).
---
## Plain English

**Definition (`TangleDiagram.rotate`, Tangle.lean lines 87-88).** Counterclockwise 90°: the corners cycle NW ← NE ← SE ← SW ← NW. Crossings are unchanged. F(Tʳ) = −1/F(T).
