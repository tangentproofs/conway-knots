---
id: TangleDiagram.infinity
title: 'The tangle [∞]: two vertical arcs'
summary: '**The surprise:** [∞] is [0] turned 90°, and its fraction is 1/0. The fractions here live on ℚ ∪ {∞},
  the projective line, so turning a tangle a quarter turn acts like taking a reciprocal.'
review: draft
authors:
- grok-bot
quiz:
- q: Which corners does arc 1 join?
  type: choice
  choices:
  - NE and SE
  - NW and NE
  - SW and SE
  answer: 0
  explain: '`NE := 1, SE := 1`.'
- q: What is the fraction of [∞]?
  type: choice
  choices:
  - '0'
  - ∞ (1/0)
  - '1'
  answer: 1
  explain: '`TwistExpr.fraction infinity = .inf`.'
- q: What does inverting [0] give?
  type: choice
  choices:
  - '[0]'
  - '[∞]'
  - '[1]'
  answer: 1
  explain: '`invert_zero : TangleDiagram.zero.invert = TangleDiagram.infinity`.'
---
## Plain English

**Definition (`TangleDiagram.infinity`, Reidemeister.lean lines 200-205).** No crossings; arc 0 runs NW–SW and arc 1 runs NE–SE.

In any coloring NE = SE, so (NE − NW)/(NE − SE) has denominator 0: the coloring fraction is ∞ ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)). Inverting [0] gives [∞] (`invert_zero`).
