---
id: Crossing.switch
title: Switch a crossing
summary: '**The surprise:** switching over and under is a port shift by one plus a sign flip. That one-port shift
  is what stops colorings carrying over.'
review: draft
authors:
- grok-bot
quiz:
- q: What happens to the sign?
  type: choice
  choices:
  - It flips
  - It stays
  answer: 0
  explain: '`sign := C.sign.flip`.'
- q: Which arc is now at port 0?
  type: choice
  choices:
  - Old a1
  - Old a0
  answer: 0
  explain: '`a0 := C.a1`.'
- q: Switching twice gives?
  type: choice
  choices:
  - The crossing rotated 180°
  - The original exactly
  answer: 0
  explain: '`switch_switch : C.switch.switch = C.rotate180`.'
---
## Plain English

**Definition (`Crossing.switch`, Tangle.lean lines 45-46).** Ports rotate by one (so the old under-strand sits on ports 0 and 2) and the sign flips. Used by [`mirror`](#/node/TangleDiagram.mirror).
