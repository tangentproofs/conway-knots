---
id: Crossing.rotate180
title: Turn a crossing 180° in the plane
summary: '**The surprise:** a half-turn swaps the two over-ports and the two under-ports but keeps the sign. It''s
  the same crossing, so planar isotopy allows it.'
review: draft
authors:
- grok-bot
quiz:
- q: Is the sign kept?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`sign := C.sign`.'
- q: Where does a0 go?
  type: choice
  choices:
  - To port 2
  - To port 1
  answer: 0
  explain: '`a2 := C.a0`.'
- q: Is it allowed by planar isotopy?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`sameUpToRotation` includes it.'
---
## Plain English

**Definition (`Crossing.rotate180`, Reidemeister.lean lines 102-103).** (a0, a1, a2, a3) ↦ (a2, a3, a0, a1), same sign.
