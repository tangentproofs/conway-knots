---
id: TwistExpr.noMulTop
title: No top products
summary: '**The surprise:** forbidding just one of the four recipe steps loses no fractions at all (standard forms
  never use it), yet it is exactly what makes the recipe fraction trustworthy.'
review: draft
authors:
- grok-bot
caveats:
- Load-bearing for the *meaning* of headlines 1 and 2, not just their proofs (Claude audit, §3).
quiz:
- q: Which step is forbidden?
  type: choice
  choices:
  - addLeft
  - mulTop
  - mulBottom
  answer: 1
  explain: '`| mulTop _ _ => False`.'
- q: Are left additions allowed?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`| addRight e _ | addLeft e _ | mulBottom e _ => e.noMulTop`.'
- q: Why does it matter for the headlines?
  type: choice
  choices:
  - It's purely cosmetic
  - On recipes with top products the recipe fraction is not the Conway fraction
  answer: 1
  explain: See the `mulTop` clause of `TwistExpr.fraction`.
---
## Plain English

**Definition (`TwistExpr.noMulTop`, Rational.lean lines 83-86).** True if the recipe never uses `mulTop`; additions on either side and bottom products are allowed.

Every standard form (right additions and bottom products only) satisfies it, so every value in ℚ ∪ {∞} is reached. On these recipes [`fraction`](#/node/TwistExpr.fraction) equals the standard-form value ([`fraction_eq_toStandard_of_noMulTop`](#/node/TwistExpr.fraction_eq_toStandard_of_noMulTop)).
