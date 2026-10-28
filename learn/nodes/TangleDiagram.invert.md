---
id: TangleDiagram.invert
title: 'Inversion Tⁱ: rotate, then mirror'
summary: '**The surprise:** inversion is the reciprocal. Rotating gives −1/x and mirroring negates, so Tⁱ has fraction
  1/F(T).'
review: draft
authors:
- grok-bot
quiz:
- q: How is inversion defined?
  type: choice
  choices:
  - Mirror then add [0]
  - Rotate 90° counterclockwise, then mirror
  - Rotate 180°
  answer: 1
  explain: '`def invert (T) := T.rotate.mirror`.'
- q: What is F(Tⁱ)?
  type: choice
  choices:
  - F(T)
  - 1/F(T)
  - −F(T)
  answer: 1
  explain: −(−1/x) = 1/x.
- q: Is inversion used by the coloring-safe moves?
  type: choice
  choices:
  - Only for single crossings (`invert_unit`)
  - Always
  answer: 0
  explain: General `invert_cong`/`invert_add`/`invert_mul` are excluded from ColoringIsotopy.
---
## Plain English

**Definition (`TangleDiagram.invert`, Tangle.lean lines 92-93).** `T.rotate.mirror` ([`rotate`](#/node/TangleDiagram.rotate), then [`mirror`](#/node/TangleDiagram.mirror)), the paper's Tⁱ = −Tʳ. F(Tⁱ) = 1/F(T). Inverting [n] gives the vertical twist 1/[n].
