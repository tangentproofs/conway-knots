---
id: IsReidemeisterIIILocal
title: The local R3 model used for colorings
summary: '**The surprise:** this is the one coloring-safe move with no bridge to Isotopic in the repo, so ColoringIsotopy
  ⊆ Isotopic is not yet a theorem.'
review: draft
authors:
- grok-bot
quiz:
- q: Is there a lemma turning it into `IsReidemeisterIII`?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: Claude audit, §1.
- q: Can the triangle's internal arcs be corner arcs?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: '`uE ≠ E.NW ∧ …`.'
- q: Are signs preserved?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`PD.sign = PE.sign ∧ …`.'
---
## Plain English

**Definition (`IsReidemeisterIIILocal`, Reidemeister.lean lines 480-499).** An over-slide R3 on a triangle whose internal arcs are not corners and touch nothing else, with signs kept and the rest matched by an injective renaming.
