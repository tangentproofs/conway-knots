---
id: TwistExpr.toStandard
title: Rewrite a recipe in standard form
summary: '**The surprise:** to put a recipe in standard form, you just relabel each left addition as a right one
  and each top product as a bottom one. The real work is proving the diagram doesn''t change, which takes flypes.'
review: draft
authors:
- grok-bot
quiz:
- q: What does `toStandard` do with `addLeft e s`?
  type: choice
  choices:
  - Deletes it
  - Makes it `addRight (toStandard e) s`
  - Makes it mulTop
  answer: 1
  explain: '`| addLeft e s => .addRight e.toStandard s`.'
- q: What does `one` become?
  type: choice
  choices:
  - '`.addRight .zero .pos` ([0] + [+1])'
  - '`.zero`'
  answer: 0
  explain: Standard forms start from [0] or [∞].
- q: Why is the rewritten diagram isotopic?
  type: choice
  choices:
  - It is the same code
  - By flypes moving the crossing across
  - It isn't
  answer: 1
  explain: '`TwistExpr.toStandard_isotopic` uses `flype_add`/`flype_mul`.'
---
## Plain English

**Definition (`TwistExpr.toStandard`, FlippingLemma.lean lines 481-489).** Turn `addLeft` into `addRight` and `mulTop` into `mulBottom` (keeping signs). [±1] becomes [0] + [±1]. The result is a [`StandardExpr`](#/node/StandardExpr).

That the diagram stays isotopic is `TwistExpr.toStandard_isotopic`: each relabelling is a flype plus the flipping lemma.
