---
id: TangleDiagram.WellFormed
title: 'Well-formed: every arc has exactly two ends'
summary: '**The surprise:** this sanity condition exists but is never proved for any diagram in the repo, not even
  [0] or [+1]. It appears only as a hypothesis on two coloring-safe moves.'
review: draft
authors:
- grok-bot
quiz:
- q: How many ends must an arc that appears have?
  type: choice
  choices:
  - '1'
  - '2'
  - '4'
  answer: 1
  explain: '`(D.endsOf a).length = 0 ∨ (D.endsOf a).length = 2`.'
- q: Is it proved for [+1] in the repo?
  type: choice
  choices:
  - 'Yes'
  - No lemma establishes it for any construction
  answer: 1
  explain: Claude audit, §5.
- q: Where is it required?
  type: choice
  choices:
  - By `Isotopic`
  - By the R1/R2 moves of `ColoringIsotopy`
  answer: 1
  explain: '`Isotopic` never asks for it.'
---
## Plain English

**Definition (`TangleDiagram.WellFormed`, Reidemeister.lean lines 245-246).** Every arc number appears at 0 or 2 places (crossing ports or corners), so the code is a proper matching of half-edges.
