---
id: ReidemeisterMove
title: One Reidemeister move (or a planar isotopy)
summary: '**The surprise:** knot theory''s three local moves, written as edits to a list of crossings: delete a
  kink, delete a cancelling pair, slide a strand over a crossing, or relabel.'
review: draft
authors:
- grok-bot
quiz:
- q: How many Reidemeister move types are there?
  type: choice
  choices:
  - Two
  - Three, plus planar isotopy
  - Five
  answer: 1
  explain: Constructors r1, r2, r3, isotopy.
- q: What does R2 remove?
  type: choice
  choices:
  - A kink
  - Two opposite crossings between two strands
  - A whole strand
  answer: 1
  explain: '`IsReidemeisterII` collapses an R2 pair.'
- q: Do the corners move?
  type: choice
  choices:
  - 'Yes'
  - No, they stay fixed
  answer: 1
  explain: All moves fix NW, NE, SE, SW.
---
## Plain English

**Definition (`ReidemeisterMove`, Reidemeister.lean lines 504-508).** One of: Reidemeister I (add/remove a kink, `IsReidemeisterI`), II (add/remove two opposite crossings, `IsReidemeisterII`), III (slide a strand across a crossing, `IsReidemeisterIII`), or a [planar isotopy](#/node/PlanarIsotopy). The four corners stay fixed.
