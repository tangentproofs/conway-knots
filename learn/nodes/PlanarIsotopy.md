---
id: PlanarIsotopy
title: 'Planar isotopy: same picture, different code'
summary: '**The surprise:** wiggling a diagram in the plane changes nothing in a PD code except names and order,
  so planar isotopy is just renaming arcs, reordering crossings, and rotating a crossing''s ports.'
review: draft
authors:
- grok-bot
quiz:
- q: Can a planar isotopy create a crossing?
  type: choice
  choices:
  - 'Yes'
  - 'No: no crossing data is created or destroyed'
  answer: 1
  explain: It's a renaming plus a permutation.
- q: Must the renaming be injective?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`Function.Injective f`.'
- q: Does it check that the code is planar?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 1
  explain: It checks nothing geometric; it's purely combinatorial.
---
## Plain English

**Definition (`PlanarIsotopy`, Reidemeister.lean lines 260-265).** E is D with arcs renamed by an injective map, crossings permuted, and each crossing possibly read from its other over-port (or with its unders read the other way and its sign flipped, `sameUpToRotation`). Corners correspond under the renaming.
