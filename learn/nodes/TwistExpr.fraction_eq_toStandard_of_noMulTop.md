---
id: TwistExpr.fraction_eq_toStandard_of_noMulTop
title: No top products ⇒ recipe fraction = standard-form fraction
summary: '**The surprise:** left and right additions give the same number because addition commutes, but top and
  bottom products don''t, because of the slip in the top-product formula.'
review: draft
authors:
- grok-bot
quiz:
- q: Why does addLeft cause no trouble?
  type: choice
  choices:
  - Addition is commutative
  - It's excluded
  answer: 0
  explain: s + F = F + s.
- q: What happens in the `mulTop` case of the induction?
  type: choice
  choices:
  - Contradiction with noMulTop
  - A long computation
  answer: 0
  explain: '`| mulTop e s => cases h`.'
- q: Do the two fractions agree in general on recipes with top products?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: They agree only in special cases (inner fraction ±1).
---
## Plain English

**Theorem (`TwistExpr.fraction_eq_toStandard_of_noMulTop`, ColoringFractionEq.lean lines 495-511).** If a recipe has no top products, its [fraction](#/node/TwistExpr.fraction) equals the fraction of its [standard form](#/node/TwistExpr.toStandard). Induction on the recipe; the `mulTop` case is impossible by hypothesis.
