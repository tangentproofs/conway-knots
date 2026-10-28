---
id: TwistExpr.slideReady
title: 'slideReady: no gluing onto a bare strand'
summary: '**The surprise:** the excluded cases are real: adding a crossing on the left of [∞] (a kink) breaks the
  diagonal coloring rule, and the repo proves it fails there.'
review: draft
authors:
- grok-bot
quiz:
- q: What does `addLeft e s` require?
  type: choice
  choices:
  - e.diagram.NW ≠ e.diagram.SW
  - e.diagram.NW ≠ e.diagram.NE
  - nothing
  answer: 0
  explain: '`| addLeft e _ => e.diagram.NW ≠ e.diagram.SW ∧ e.slideReady`.'
- q: Is every standard form slideReady?
  type: choice
  choices:
  - 'Yes: right additions and bottom products are unrestricted'
  - 'No'
  answer: 0
  explain: Only `addLeft` and `mulTop` carry conditions.
- q: Which example breaks the diagonal rule?
  type: choice
  choices:
  - '[0] + [1]'
  - '[1] + [∞] (adding on the left of [∞])'
  - '[1] + [1]'
  answer: 1
  explain: '`not_diagonal_addLeft_infinity`.'
---
## Plain English

**Definition (`TwistExpr.slideReady`, ColoringToStandard.lean lines 72-76).** Every `addLeft` step needs the inner diagram's NW and SW corners on **different** arcs. Every `mulTop` step needs its NW and NE on different arcs. Right additions and bottom products are unrestricted.

Same arc at NW and SW means a bare vertical strand runs down the left side (as in [∞]). Gluing a crossing there makes a kink. The Lean proves the diagonal rule fails in exactly those cases (`not_diagonal_addLeft_infinity`, `not_diagonal_mulTop_zero`, DiagonalSumGeneral.lean lines 198-251).
