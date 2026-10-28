---
id: TwistExpr.diagram
title: The diagram of a recipe
summary: '**The surprise:** turning a recipe into a picture is just repeated gluing with + and *, so every twist
  diagram''s code is produced by the same honest operations, never hand-written.'
review: draft
authors:
- grok-bot
quiz:
- q: What is `(addLeft e s).diagram`?
  type: choice
  choices:
  - e.diagram + [s]
  - '[s] + e.diagram'
  - e.diagram * [s]
  answer: 1
  explain: '`| addLeft e s => crossingTangle s + e.diagram`.'
- q: What is `(mulBottom e s).diagram`?
  type: choice
  choices:
  - e.diagram * [s]
  - '[s] * e.diagram'
  answer: 0
  explain: Bottom multiplication puts [s] below.
- q: How many crossings does a recipe with n steps from [0] have?
  type: choice
  choices:
  - n
  - 2n
  - '0'
  answer: 0
  explain: Each step adds one crossing.
---
## Plain English

**Definition (`TwistExpr.diagram`, Rational.lean lines 41-49).** [0], [∞], [+1] and [−1] give their diagrams. `addRight e s` gives `e.diagram + [s]`, `addLeft e s` gives `[s] + e.diagram`, `mulBottom e s` gives `e.diagram * [s]` and `mulTop e s` gives `[s] * e.diagram` ([`add`](#/node/TangleDiagram.add), [`mul`](#/node/TangleDiagram.mul), [`crossingTangle`](#/node/crossingTangle)).
