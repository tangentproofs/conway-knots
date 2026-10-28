---
id: TangleDiagram.add
title: 'Tangle addition T + S: side by side'
summary: '**The surprise:** gluing two tangles side by side is just list concatenation plus renaming: shift S''s
  arc numbers past T''s, then identify S''s west ends with T''s east ends.'
review: draft
authors:
- grok-bot
quiz:
- q: Where does S go in T + S?
  type: choice
  choices:
  - Below T
  - To the right of T
  - On top of T
  answer: 1
  explain: '`Place S to the right of T`.'
- q: Which arcs are identified?
  type: choice
  choices:
  - T.NE with S.NW and T.SE with S.SW
  - T.SW with S.NW
  - None
  answer: 0
  explain: The renaming `f` sends `S'.NW` to `T.NE` and `S'.SW` to `T.SE`.
- q: What happens to the crossing lists?
  type: choice
  choices:
  - They are concatenated
  - They are merged by sign
  - S's list is dropped
  answer: 0
  explain: '`crossings := T.crossings ++ S''''.crossings`.'
---
## Plain English

**Definition (`TangleDiagram.add`, Tangle.lean lines 98-109).** Place S to the right of T, joining T's NE to S's NW and T's SE to S's SW. In code:

1. rename S's arcs by adding T's largest arc number + 1, so they don't clash;
2. rename S's NW arc to T's NE arc and S's SW arc to T's SE arc;
3. concatenate the crossing lists. The new corners are T's NW/SW and S's NE/SE.

Fractions add: F(T + S) = F(T) + F(S), for rational T and S whenever the sum is rational.
