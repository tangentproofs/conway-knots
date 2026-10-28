---
id: coloring_fraction_ColoringIsotopy
title: Colorings ride along coloring-safe moves
summary: '**The surprise:** this is the engine of invariance, and it works for every diagram, rational or not: any
  coloring can be carried across any coloring-safe path without changing a single boundary color.'
review: draft
authors:
- grok-bot
quiz:
- q: Does it need D or E to be rational?
  type: choice
  choices:
  - No, any diagrams
  - 'Yes'
  answer: 0
  explain: D and E are arbitrary `TangleDiagram`s.
- q: What is preserved?
  type: choice
  choices:
  - The color matrix
  - The number of crossings
  answer: 0
  explain: '`ColorMatrix.of E col'' = ColorMatrix.of D col`.'
- q: Can the coloring be carried backwards along the path?
  type: choice
  choices:
  - Not in general; the relation is directed
  - Yes, always
  answer: 0
  explain: Only partial reverse lemmas exist.
---
## Plain English

**Theorem (`coloring_fraction_ColoringIsotopy`, ColoringIsotopy.lean lines 2125-2132).** If D → E by [`ColoringIsotopy`](#/node/ColoringIsotopy) and `col` colors D, there is a coloring `col'` of E with the same boundary colors ([`ColorMatrix.of`](#/node/ColorMatrix.of)), hence the same coloring fraction.

The work is in `coloring_ColoringIsotopy`, an induction over every constructor: R1, R2, local R3 (`ColoringR3.lean`), local flypes (`ColoringFlype.lean`), congruences and reindexings.
