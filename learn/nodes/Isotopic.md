---
id: Isotopic
title: 'Isotopic: Reidemeister moves plus assumed tangle moves'
summary: '**The surprise:** ''isotopic'' here isn''t derived from Reidemeister moves alone. It''s a list of 25 rules
  (flypes, half-turns, inversions, transfer moves), each a classical fact taken as primitive. One may be stronger
  than real isotopy.'
review: draft
authors:
- grok-bot
caveats:
- '`flype_slide_add/mul` and `transfer_odd(_neg)` are quantified over arbitrary diagrams; the first may exceed real
  isotopy for non-rational pieces (Claude audit, §5: ''unresolved risk, flagged'').'
- No well-formedness or planarity is required anywhere in `Isotopic`.
quiz:
- q: Which of these is a primitive generator of `Isotopic` rather than a proved theorem?
  type: choice
  choices:
  - The flype slide [±1] + t ∼ t.rot180 + [±1]
  - Uniqueness of canonical continued fractions
  - f = F
  answer: 0
  explain: '`flype_slide_add` is a constructor of the inductive `Isotopic`.'
- q: Is `Isotopic` symmetric?
  type: choice
  choices:
  - Yes, it has a `symm` constructor
  - 'No'
  answer: 0
  explain: '`| symm {D E} : Isotopic D E → Isotopic E D`.'
- q: If `Isotopic` were larger than real isotopy, which headline would it weaken?
  type: choice
  choices:
  - '''Same fraction ⇒ Isotopic'' (headline 2)'
  - f = F (headline 4)
  answer: 0
  explain: A bigger target relation makes the reconstruction conclusion weaker; f = F doesn't mention `Isotopic`.
---
## Plain English

**Definition (`Isotopic`, Flype.lean lines 120-184).** The smallest relation on diagrams that

* is reflexive, symmetric and transitive;
* contains every Reidemeister move and planar isotopy ([`ReidemeisterMove`](#/node/ReidemeisterMove));
* contains the **assumed moves**:
  * local flypes ([`IsLocalFlype`](#/node/IsLocalFlype)) and the Figure 5 slides `flype_slide_add/mul`: [±1] + t ∼ t.rot180 + [±1];
  * congruences: isotopic pieces give isotopic sums, products, half-turns, inverses and mirrors;
  * identities: (T+S).rot180 ∼ S.rot180 + T.rot180, (T+S)ⁱ ∼ Sⁱ * Tⁱ, (T*S)ⁱ ∼ Tⁱ + Sⁱ, associativity, [0] + T ∼ T, [±1] ∼ [±1]ⁱ;
  * the transfer moves of Figure 14: (T + [−1]) * [+1] ∼ [+1] + (−T)ⁱ and its sign-switched twin.

These are classical facts about tangles, but in Lean they are generators, not theorems.

### Is it too generous?

The Claude audit found one real risk. `flype_slide_add` uses a planar half-turn of **any** t ([`rot180`](#/node/TangleDiagram.rot180)). The classical flype uses a single flip t^h, and the half-turn is two flips. For rational t the two are isotopic (flipping lemma), so the move is fine there; every use I found is on a rational piece. For non-rational t it may not be an isotopy. Also, `Isotopic` never asks diagrams to be [well-formed](#/node/TangleDiagram.WellFormed).

A too-generous `Isotopic` would make "same fraction ⇒ isotopic" weaker, not false.
