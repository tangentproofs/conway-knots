---
id: TwistExpr.colorFrom
title: A coloring built step by step
summary: '**The surprise:** give the starting tangle two colors and every later crossing''s colors are forced, so
  each recipe comes with a ready-made coloring.'
review: draft
authors:
- grok-bot
quiz:
- q: How many starting colors?
  type: choice
  choices:
  - '1'
  - '2'
  - '4'
  answer: 1
  explain: '`TwistExpr → Int → Int → (Nat → Int)`.'
- q: Which starting colors do the invariance proofs use?
  type: choice
  choices:
  - 0 and 1
  - 1 and 2
  answer: 0
  explain: '`e₁.colorFrom 0 1`.'
- q: How is a new under-arc colored?
  type: choice
  choices:
  - 2β − α
  - α + β
  - '0'
  answer: 0
  explain: The rule α + γ = 2β.
---
## Plain English

**Definition (`TwistExpr.colorFrom`, ColoringFractionEq.lean lines 379-391).** From two integers a, c, color the starting tangle, then extend the coloring across each glued crossing using τ_β(α) = 2β − α. The invariance proofs use `colorFrom 0 1`, which is proved to be a coloring, satisfy the diagonal rule and be non-constant on slideReady recipes.
