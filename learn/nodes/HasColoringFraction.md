---
id: HasColoringFraction
title: v is a coloring fraction of D
summary: '**The surprise:** this turns the coloring fraction into a property of the diagram alone: some non-constant
  coloring of D reads off v.'
review: draft
authors:
- grok-bot
quiz:
- q: What does `HasColoringFraction D v` assert?
  type: choice
  choices:
  - Some non-constant coloring of D has fraction v
  - Every coloring has fraction v
  answer: 0
  explain: It's an existential.
- q: Does [+1] have coloring fraction 1?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: Any non-constant coloring gives 1.
- q: Headline 3 carries this property in which direction?
  type: choice
  choices:
  - From e₁ to e₂ only
  - Both ways
  answer: 0
  explain: ColoringIsotopy is directed.
---
## Plain English

**Definition (`HasColoringFraction`, ColorFractionUnique.lean lines 3709-3711).** There is a [coloring](#/node/TangleDiagram.IsColored) of D that is [not constant on the boundary](#/node/ColorMatrix.NotMono) and whose [coloring fraction](#/node/ColorMatrix.fraction) is v.
