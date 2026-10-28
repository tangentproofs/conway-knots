---
id: TangleDiagram.mul
title: 'Tangle product T * S: one on top of the other'
summary: '**The surprise:** stacking S under T makes reciprocals add: 1/F(T*S) = 1/F(T) + 1/F(S). That''s why the
  product is the quarter-turned twin of addition.'
review: draft
authors:
- grok-bot
quiz:
- q: Where does S go in T * S?
  type: choice
  choices:
  - To the right
  - Below T
  - Above T
  answer: 1
  explain: '`Place S below T`.'
- q: What happens to fractions under the product?
  type: choice
  choices:
  - They add
  - Their reciprocals add
  - They multiply
  answer: 1
  explain: 1/F(T*S) = 1/F(T) + 1/F(S).
- q: Multiplying x = 2 at the bottom by [+1] gives?
  type: choice
  choices:
  - '3'
  - 2/3
  - 1/3
  answer: 1
  explain: 1/(1/2 + 1) = 2/3.
---
## Plain English

**Definition (`TangleDiagram.mul`, Tangle.lean lines 112-123).** Place S below T, joining T's SW to S's NW and T's SE to S's NE, with the same rename-and-concatenate recipe as [addition](#/node/TangleDiagram.add).

Arithmetically 1/F(T * S) = 1/F(T) + 1/F(S). So multiplying [+1] at the bottom sends a fraction x to 1/(1/x + 1).
