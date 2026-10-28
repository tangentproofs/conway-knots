---
id: Crossing
title: 'A crossing: four arc numbers and a sign'
summary: '**The surprise:** a crossing is just four numbers read counterclockwise, with the over-strand on ports
  0 and 2. The coloring rule only ever looks at which port an arc sits on.'
review: draft
authors:
- grok-bot
quiz:
- q: Which ports carry the over-strand?
  type: choice
  choices:
  - 0 and 1
  - 0 and 2
  - 1 and 3
  - 2 and 3
  answer: 1
  explain: Ports `0` and `2` are the overstrand; `1` and `3` are the two under-arcs.
- q: What else does a crossing record besides arc numbers?
  type: choice
  choices:
  - Its position in the plane
  - 'A sign: pos or neg'
  - Its color
  answer: 1
  explain: 'The last field is `sign : CrossingSign`.'
- q: If color(a0) = 5 and color(a1) = 2, what must color(a3) be?
  type: choice
  choices:
  - '5'
  - '8'
  - '3'
  - '7'
  answer: 1
  explain: α + γ = 2β with β = 5 and α = 2 gives γ = 8.
---
## Plain English

**Definition (`Crossing`, Reidemeister.lean lines 71-81).** A crossing has arc numbers `a0`, `a1`, `a2`, `a3` at its four ports, read counterclockwise. Ports 0 and 2 belong to the **over-strand**, ports 1 and 3 to the two pieces of the **under-strand**. It also has a [`sign`](#/node/CrossingSign): `pos` as in [+1], `neg` as in [−1].

Because the over-strand occupies ports 0 and 2, the coloring rule ([`ColoringRule`](#/node/ColoringRule)) reads: color(a0) = color(a2) = β and color(a1) + color(a3) = 2β.
