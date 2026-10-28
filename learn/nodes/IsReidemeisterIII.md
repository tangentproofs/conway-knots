---
id: IsReidemeisterIII
title: 'Reidemeister III: slide a strand over a crossing'
summary: '**The surprise:** the repo has two versions of R3: this indexed one is used by Isotopic, and a separate
  local model is used for colorings, with no lemma linking them.'
review: draft
authors:
- grok-bot
quiz:
- q: How many crossings does R3 involve?
  type: choice
  choices:
  - '2'
  - '3'
  - '4'
  answer: 1
  explain: A triangle of three.
- q: Which R3 does ColoringIsotopy use?
  type: choice
  choices:
  - IsReidemeisterIIILocal
  - IsReidemeisterIII
  answer: 0
  explain: '`r3Local`.'
- q: Does the number of crossings change?
  type: choice
  choices:
  - 'No'
  - 'Yes'
  answer: 0
  explain: R3 slides a strand; the count stays 3.
---
## Plain English

**Definition (`IsReidemeisterIII`, Reidemeister.lean lines 425-471).** Three crossings forming a triangle in D are replaced by the slid triangle in E, matching the rest of the diagram by an injective renaming. The coloring proof uses [`IsReidemeisterIIILocal`](#/node/IsReidemeisterIIILocal).
