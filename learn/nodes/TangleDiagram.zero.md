---
id: TangleDiagram.zero
title: 'The tangle [0]: two horizontal arcs'
summary: '**The surprise:** [0] has no crossings at all. Its whole content is that NW and NE share one arc and SW
  and SE share another, so its fraction (NE − NW)/(NE − SE) is 0.'
review: draft
authors:
- grok-bot
quiz:
- q: How many crossings does [0] have?
  type: choice
  choices:
  - '0'
  - '1'
  - '2'
  answer: 0
  explain: '`crossings := []`.'
- q: Which corners does the arc numbered 0 join?
  type: choice
  choices:
  - NW and SW
  - NW and NE
  - NW and SE
  answer: 1
  explain: '`NW := 0, NE := 0`.'
- q: What is the fraction of [0]?
  type: choice
  choices:
  - '0'
  - '1'
  - ∞
  answer: 0
  explain: Both `TwistExpr.fraction` and the coloring fraction give 0.
---
## Plain English

**Definition (`TangleDiagram.zero`, Reidemeister.lean lines 192-197).** No crossings; arc 0 runs NW–NE and arc 1 runs SW–SE.

Color arc 0 with a and arc 1 with c ≠ a: the coloring fraction is (a − a)/(a − c) = 0, matching its fraction 0. Adding [0] on the right of a diagram changes nothing (`add_zero_eq`).
