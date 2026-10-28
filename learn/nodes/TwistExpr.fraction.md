---
id: TwistExpr.fraction
title: The fraction of a recipe (with a top-product slip)
summary: '**The surprise:** the formula for a top product is off: it gives 1/(s + F) where the Conway product needs
  1/(s + 1/F). That''s why the classification headlines exclude top products.'
review: draft
authors:
- grok-bot
caveats:
- On recipes containing `mulTop`, this function is not the tangle fraction (Claude audit, §3). Headlines 1 and 2
  assume `noMulTop`; headlines 3 and 4 use `toStandard.fraction` instead.
quiz:
- q: Start at [0], add [+1] twice, then multiply [+1] at the bottom. Fraction?
  type: choice
  choices:
  - '3'
  - 2/3
  - 1/3
  - 3/2
  answer: 1
  explain: 2, then 1/(1/2 + 1) = 2/3.
- q: For which recipes is `TwistExpr.fraction` the Conway fraction?
  type: choice
  choices:
  - All recipes
  - Recipes without top products (noMulTop)
  - Only standard forms
  answer: 1
  explain: The `mulTop` clause misses an inverse; on noMulTop recipes it agrees with the standard-form value (`fraction_eq_toStandard_of_noMulTop`).
- q: What does adding [−1] do to the fraction?
  type: choice
  choices:
  - Subtracts 1
  - Inverts it
  - Nothing
  answer: 0
  explain: '`addRight e s => e.fraction.add s.cfValue` with value −1.'
---
## Plain English

**Definition (`TwistExpr.fraction`, TangleFraction.lean lines 30-38).** Evaluate the recipe in ℚ ∪ {∞} ([`CFValue`](#/node/CFValue)):

* [0] ↦ 0, [∞] ↦ ∞, [±1] ↦ ±1;
* adding [s] on either side: F ↦ F + s;
* multiplying [s] at the bottom: F ↦ 1/(1/F + s).

**Worked example.** Start at [0], add [+1] three times: 3. Multiply [+1] at the bottom: 1/(1/3 + 1) = 3/4. Add [+1]: **7/4**.

### The top product

The code says `mulTop e s ↦ (s.cfValue.inv.add e.fraction).inv`, that is 1/(1/s + F) = 1/(s + F). The Conway product [s] * T has 1/F = 1/s + 1/F(T), so the right value is 1/(s + 1/F). The two agree only when F = ±1. The repo knows this: its standard-form rewrite gives the right value ([`toStandard`](#/node/TwistExpr.toStandard)). The classification headlines assume [`noMulTop`](#/node/TwistExpr.noMulTop), where the formula is right.

Example: [+1] * [0] is a kink on top of two arcs and isotopes to [0], fraction 0. The formula gives 1/(1 + 0) = 1.
