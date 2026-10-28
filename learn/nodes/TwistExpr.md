---
id: TwistExpr
title: 'Twist recipes: build a tangle one crossing at a time'
summary: '**The surprise:** every rational tangle comes from a recipe that only ever glues one crossing on: left
  or right, top or bottom. The fraction belongs to the recipe, and the theorems compare recipes.'
review: draft
authors:
- grok-bot
quiz:
- q: How many crossings does each recipe step glue on?
  type: choice
  choices:
  - One
  - Two
  - Any number
  answer: 0
  explain: Each constructor takes a `CrossingSign` and glues `crossingTangle s`.
- q: Which of these is not a recipe step?
  type: choice
  choices:
  - addLeft
  - mulTop
  - addRight
  - mirror
  answer: 3
  explain: The constructors are zero, infinity, one, negOne, addRight, addLeft, mulBottom, mulTop.
- q: Are the headline theorems about recipes or about tangles up to isotopy?
  type: choice
  choices:
  - Recipes (TwistExpr)
  - Tangles up to isotopy
  answer: 0
  explain: 'They quantify over `e₁ e₂ : TwistExpr`.'
---
## Plain English

**Definition (`TwistExpr`, Rational.lean lines 27-36).** A recipe starts from [0], [∞], [+1] or [−1] and repeatedly

* adds a crossing on the right (`addRight`) or the left (`addLeft`), or
* multiplies by a crossing at the bottom (`mulBottom`) or on top (`mulTop`).

Each step carries a [sign](#/node/CrossingSign). [`diagram`](#/node/TwistExpr.diagram) builds the PD-code; [`fraction`](#/node/TwistExpr.fraction) computes the number.

A diagram is **rational** when it is [`Isotopic`](#/node/Isotopic) to the diagram of some recipe (`IsRational`, Rational.lean lines 107-108).
