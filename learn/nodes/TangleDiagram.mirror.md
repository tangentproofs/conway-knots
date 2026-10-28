---
id: TangleDiagram.mirror
title: 'Mirror image −T: switch every crossing'
summary: '**The surprise:** the mirror changes no arc and no corner, only the crossing data, yet it negates the
  fraction. Colorings don''t survive the switch unchanged, which is why the coloring proof can''t handle mirror
  moves.'
review: draft
authors:
- grok-bot
quiz:
- q: What changes under the mirror?
  type: choice
  choices:
  - The corners
  - Every crossing is switched
  - Nothing
  answer: 1
  explain: '`crossings := T.crossings.map Crossing.switch`; corners unchanged.'
- q: What happens to the fraction?
  type: choice
  choices:
  - It is negated
  - It is inverted
  - It is unchanged
  answer: 0
  explain: F(−T) = −F(T); e.g. −[1] = [−1].
- q: Is the mirror an isotopy?
  type: choice
  choices:
  - 'Yes'
  - 'No: [+1] and [−1] have different fractions'
  answer: 1
  explain: It is a different tangle in general.
---
## Plain English

**Definition (`TangleDiagram.mirror`, Tangle.lean lines 81-82).** Apply `Crossing.switch` to every crossing: the over-strand becomes the under-strand (ports shift by one) and the sign flips. Corners stay put. F(−T) = −F(T).

The repo proves that a coloring of [+1] can't always be carried to its mirror with the same boundary colors (`not_coloring_mirror_transport`, DiagonalSumGeneral.lean lines 261-295).
