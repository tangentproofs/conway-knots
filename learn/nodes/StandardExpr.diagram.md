---
id: StandardExpr.diagram
title: The diagram of a standard form
summary: '**The surprise:** a standard form''s picture is built with only two of the four gluing moves, right addition
  and bottom product, and that''s enough for every rational tangle.'
review: draft
authors:
- grok-bot
quiz:
- q: What is `(mulBottom e s).diagram`?
  type: choice
  choices:
  - e.diagram * [s]
  - '[s] * e.diagram'
  answer: 0
  explain: Bottom product puts [s] below.
- q: Which gluing moves are used?
  type: choice
  choices:
  - Right addition and bottom product
  - All four
  answer: 0
  explain: Only two constructors glue.
- q: What does `zero` give?
  type: choice
  choices:
  - '[0]'
  - '[∞]'
  - '[+1]'
  answer: 0
  explain: '`| zero => TangleDiagram.zero`.'
---
## Plain English

**Definition (`StandardExpr.diagram`, StandardForm.lean lines 32-36).** [0] and [∞] as themselves; `addRight e s` ↦ `e.diagram + [s]`; `mulBottom e s` ↦ `e.diagram * [s]` ([`add`](#/node/TangleDiagram.add), [`mul`](#/node/TangleDiagram.mul)).
