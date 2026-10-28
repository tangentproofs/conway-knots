---
id: IsReidemeisterI
title: 'Reidemeister I: add or remove a kink'
summary: '**The surprise:** a kink is a crossing where one arc appears twice: the loop''s arc. Removing it means
  deleting that crossing and merging the two remaining arcs.'
review: draft
authors:
- grok-bot
quiz:
- q: Is R1 symmetric here?
  type: choice
  choices:
  - 'Yes: either diagram may have the extra kink'
  - 'No'
  answer: 0
  explain: '`IsReidemeisterIAdd D E ∨ IsReidemeisterIAdd E D`.'
- q: How many crossings does a kink have?
  type: choice
  choices:
  - '1'
  - '2'
  - '3'
  answer: 0
  explain: One crossing with a loop.
- q: In ColoringIsotopy, what else does R1 need?
  type: choice
  choices:
  - WellFormed on both sides
  - Nothing
  answer: 0
  explain: '`ColoringIsotopy.r1`.'
---
## Plain English

**Definition (`IsReidemeisterI`, Reidemeister.lean lines 288-289).** One of D, E is the other with one kink added: a crossing whose loop port is collapsed by `collapseKink`, up to [planar isotopy](#/node/PlanarIsotopy).
