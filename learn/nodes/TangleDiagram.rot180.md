---
id: TangleDiagram.rot180
title: Planar half-turn
summary: '**The surprise:** a half-turn in the plane keeps every crossing sign. For rational tangles it is an isotopy
  (the flipping lemma), but for general tangles it need not be, and that gap matters for the flype move.'
review: draft
authors:
- grok-bot
quiz:
- q: Does the half-turn change crossing signs?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 1
  explain: '`crossings := T.crossings.map Crossing.rotate180`; `rotate180` keeps the sign.'
- q: Where does NW go?
  type: choice
  choices:
  - To NE
  - To SE
  - Nowhere
  answer: 1
  explain: '`NW := T.SE`, `SE := T.NW`.'
- q: For which tangles is T isotopic to its half-turn classically?
  type: choice
  choices:
  - All 2-tangles
  - Rational tangles (flipping lemma)
  - None
  answer: 1
  explain: The repo's Flip.lean says flips 'need not be an isotopy of 2-tangles. For rational tangles it is'.
---
## Plain English

**Definition (`TangleDiagram.rot180`, Flip.lean lines 45-50).** Rotate every crossing 180° in the plane (signs kept) and swap corners NW ↔ SE, NE ↔ SW. It equals the horizontal flip followed by the vertical flip.

The flipping lemma (`flipping_lemma`, FlippingLemma.lean lines 470-477) says a rational tangle is isotopic to its half-turn. The move `flype_slide_add` in [`Isotopic`](#/node/Isotopic) uses `t.rot180` for **every** t. Classically the flype gives the single flip t^h, which differs from the half-turn by one more flip. The Claude audit flags that this may make `Isotopic` too generous for non-rational t.
