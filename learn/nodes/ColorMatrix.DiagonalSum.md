---
id: ColorMatrix.DiagonalSum
title: The diagonal rule NW + SE = NE + SW
summary: '**The surprise:** Kauffman–Lambropoulou prove every rational tangle''s colorings obey NW + SE = NE + SW.
  Here it''s proved for slideReady twist diagrams, and refuted for the excluded ones.'
review: draft
authors:
- grok-bot
quiz:
- q: Which entries are summed?
  type: choice
  choices:
  - The diagonals NW + SE and NE + SW
  - The rows
  answer: 0
  explain: '`M.NW + M.SE = M.NE + M.SW`.'
- q: Does it hold for every coloring of a slideReady twist diagram?
  type: choice
  choices:
  - Yes, `twist_coloring_diagonal_slideReady`
  - 'No'
  answer: 0
  explain: ColoringFractionEq.lean lines 976-1007.
- q: Does it hold for [+1] + [∞] (adding on the left of [∞])?
  type: choice
  choices:
  - 'Not always: `not_diagonal_addLeft_infinity`'
  - Always
  answer: 0
  explain: That's why slideReady excludes it.
---
## Plain English

**Definition (`ColorMatrix.DiagonalSum`, Coloring.lean lines 247-248).** NW + SE = NE + SW.

For [+1]: β + β = α + (2β − α). ✓
