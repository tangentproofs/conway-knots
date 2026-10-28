---
id: TangleDiagram.IsColored
title: An integer coloring of a diagram
summary: '**The surprise:** a coloring is just a function from arc numbers to integers obeying one rule per crossing.
  Nothing global is checked, yet it detects the whole fraction.'
review: draft
authors:
- grok-bot
quiz:
- q: What type is a coloring?
  type: choice
  choices:
  - ℕ → ℤ
  - ℤ → ℕ
  - List ℤ
  answer: 0
  explain: '`col : Nat → Int`, arc number to color.'
- q: Where must the rule hold?
  type: choice
  choices:
  - At every crossing
  - At the corners
  answer: 0
  explain: '`∀ C ∈ D.crossings, ColoringRule C col`.'
- q: Does [0] have non-constant colorings?
  type: choice
  choices:
  - 'Yes: any two colors on its two arcs'
  - 'No'
  answer: 0
  explain: No crossings, so no constraints.
---
## Plain English

**Definition (`TangleDiagram.IsColored`, Coloring.lean lines 49-50).** `col : ℕ → ℤ` satisfies the [coloring rule](#/node/ColoringRule) at every crossing of the diagram.
