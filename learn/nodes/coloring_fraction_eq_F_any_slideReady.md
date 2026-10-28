---
id: coloring_fraction_eq_F_any_slideReady
title: 'f = F: every integer coloring reads off the fraction'
summary: '**The surprise:** color the arcs of a twist diagram with integers in any valid way that isn''t constant
  on the boundary: (NE − NW)/(NE − SE) is always the same number, the tangle''s continued fraction. Arithmetic is
  hiding in the picture.'
review: draft
authors:
- grok-bot
caveats:
- '**FAITHFUL WITH CAVEATS** (Claude audit). About diagrams of slideReady twist recipes. It doesn''t cover an arbitrary
  diagram isotopic to one; for diagrams reached by coloring-safe moves, see `coloring_fraction_agreement_any_isotopy`
  (DiagonalSumGeneral.lean lines 562-574).'
- F is `e.toStandard.fraction`, which equals the recipe's own `e.fraction` only on top-product-free recipes.
- Only the f = F half of Theorem 4. The invariance half is the previous headline, along coloring-safe moves only.
widgets:
- type: walkthrough
  title: How it is proved (DiagonalSumGeneral.lean, lines 42-48)
  config:
    steps:
    - text: Every coloring of a slideReady twist diagram satisfies the diagonal rule
      lean: (twist_coloring_diagonal_slideReady e hok col hc) hm
      note: 'Induction on the recipe. The slideReady side-conditions are exactly where this would fail: the repo
        refutes it for left-adding onto [∞] and top-multiplying onto [0].'
      uses:
      - twist_coloring_diagonal_slideReady
      hard: true
    - text: …so coloring_fraction_eq_F applies
      lean: coloring_fraction_eq_F e hok col hc
      link: coloring_fraction_eq_F
quiz:
- q: Which colorings does the theorem cover?
  type: choice
  choices:
  - Only the special coloring colorFrom 0 1
  - Every integer coloring whose boundary colors are not all equal
  - Only colorings with colors 0 and 1
  answer: 1
  explain: 'The coloring `col` is arbitrary, subject to `hc : e.diagram.IsColored col` and `hm : (ColorMatrix.of
    e.diagram col).NotMono`.'
- q: What is the coloring rule at a crossing?
  type: choice
  choices:
  - The two under-arcs have the same color
  - 'The two under-arc colors average to the over-arc color: α + γ = 2β'
  - All three colors are different
  answer: 1
  explain: '`ColoringRule`: `col C.a0 = col C.a2 ∧ col C.a1 + col C.a3 = 2 * col C.a0`, with ports 0 and 2 on the
    over-strand.'
- q: Is the diagonal rule NW + SE = NE + SW a hypothesis of this theorem?
  type: choice
  choices:
  - 'Yes'
  - No, it is proved for every coloring of a slideReady twist diagram and passed to coloring_fraction_eq_F
  answer: 1
  explain: The proof is `coloring_fraction_eq_F e hok col hc (twist_coloring_diagonal_slideReady e hok col hc) hm`.
---
## Plain English

**Theorem (`coloring_fraction_eq_F_any_slideReady`, DiagonalSumGeneral.lean lines 42-48).** Let e be a [`slideReady`](#/node/TwistExpr.slideReady) twist recipe and `col` any integer coloring of its diagram ([`IsColored`](#/node/TangleDiagram.IsColored)) whose boundary colors are not all equal ([`NotMono`](#/node/ColorMatrix.NotMono)). Then the coloring fraction ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)) equals the arithmetic fraction of the recipe's standard form ([`toStandard`](#/node/TwistExpr.toStandard), [`StandardExpr.fraction`](#/node/StandardExpr.fraction)).

This is the "f = F" part of Kauffman–Lambropoulou's Theorem 4, for every coloring of every slideReady twist diagram.

### A tiny example

The single crossing [+1] ([`one`](#/node/one)) has over-arc NW–SE with color β, and under-arcs at NE and SW with colors α and 2β − α. So (NE − NW)/(NE − SE) = (α − β)/(α − β) = **1**, whatever α ≠ β you pick. Its fraction is 1.

### The proof

It is a two-line wrapper around [`coloring_fraction_eq_F`](#/node/coloring_fraction_eq_F), which also asks for the **diagonal rule** NW + SE = NE + SW ([`DiagonalSum`](#/node/ColorMatrix.DiagonalSum)). Here that hypothesis is proved, not assumed: every coloring of a slideReady twist diagram satisfies it (`twist_coloring_diagonal_slideReady`, ColoringFractionEq.lean lines 976-1007).
