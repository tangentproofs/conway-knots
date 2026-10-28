---
id: coloring_fraction_eq_F
title: f = F, given the diagonal rule
summary: '**The surprise:** the proof never compares colorings directly. It carries the coloring to the standard
  form, where every non-constant coloring is forced to give the continued fraction.'
review: draft
authors:
- grok-bot
widgets:
- type: walkthrough
  title: How ColoringToStandard.lean proves it (ColoringToStandard.lean, lines 241-253)
  config:
    steps:
    - text: Carry the coloring along the flypes that rewrite e into standard form
      lean: obtain ⟨col', hc', hs⟩ := coloring_toStandard e hok col hc hdiag
      note: Each left addition / top product becomes a Figure 5 slide; the coloring crosses it using the diagonal
        rule and the slideReady port condition.
      hard: true
    - text: Boundary colors are unchanged
      lean: have hM := ColorMatrix.of_sameEndpoint hs
    - text: On a standard form every non-constant coloring gives F
      lean: have hf := standard_fraction_any_coloring e.toStandard col' hc' hm'
      note: 'Induction on the standard form: each right addition adds 1 to (NE−NW)/(NE−SE), each bottom product
        acts on its reciprocal.'
      uses:
      - standard_fraction_any_coloring
quiz:
- q: Which hypothesis does the headline version remove?
  type: choice
  choices:
  - NotMono
  - DiagonalSum
  - slideReady
  answer: 1
  explain: It's proved by `twist_coloring_diagonal_slideReady`.
- q: Where is the coloring carried?
  type: choice
  choices:
  - To the standard form's diagram
  - To the mirror
  answer: 0
  explain: '`coloring_toStandard`.'
- q: On standard forms, which colorings give F?
  type: choice
  choices:
  - Every non-constant one
  - Only colorFrom
  answer: 0
  explain: '`standard_fraction_any_coloring`.'
---
## Plain English

**Theorem (`coloring_fraction_eq_F`, ColoringFractionEq.lean lines 654-660).** For a [slideReady](#/node/TwistExpr.slideReady) recipe e and a coloring of its diagram that satisfies the [diagonal rule](#/node/ColorMatrix.DiagonalSum) and is [not constant](#/node/ColorMatrix.NotMono), the coloring fraction equals the standard-form fraction.

The headline [`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady) removes the diagonal hypothesis.
