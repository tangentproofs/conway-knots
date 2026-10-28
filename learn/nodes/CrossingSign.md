---
id: CrossingSign
title: 'Crossing sign: [+1] or [−1]'
summary: '**The surprise:** the sign convention here (Kauffman–Lambropoulou, after Ernst–Sumners) is the opposite
  of Conway''s 1970 paper, so a ''positive'' twist here is a negative one in Conway.'
review: draft
authors:
- grok-bot
quiz:
- q: How many crossing signs are there?
  type: choice
  choices:
  - One
  - Two
  - Four
  answer: 1
  explain: '`pos` and `neg`.'
- q: Which convention is used?
  type: choice
  choices:
  - Conway 1970
  - Kauffman–Lambropoulou (Ernst–Sumners), the opposite of Conway's
  answer: 1
  explain: The docstring says so explicitly.
- q: What does `flip` do?
  type: choice
  choices:
  - Rotates the crossing
  - Swaps pos and neg
  - Deletes the crossing
  answer: 1
  explain: '`flip : pos ↦ neg, neg ↦ pos`.'
---
## Plain English

**Definition (`CrossingSign`, Reidemeister.lean lines 48-51).** Two values, `pos` and `neg`: the crossing types of the elementary tangles [+1] and [−1].

`flip` swaps them; the mirror image of a diagram flips every sign. Its arithmetic value ([`CrossingSign.cfValue`](#/node/CrossingSign.cfValue)) is +1 or −1.
