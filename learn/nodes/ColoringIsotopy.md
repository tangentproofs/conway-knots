---
id: ColoringIsotopy
title: 'ColoringIsotopy: the moves a coloring can ride along'
summary: '**The surprise:** this relation has no ''reverse'' rule. It is a one-way street of moves along which colorings
  are proved to carry over, which is exactly what limits the invariance theorem.'
review: draft
authors:
- grok-bot
caveats:
- No lemma in the repo proves `WellFormed` for any construction, so the R1/R2 moves are usable only where a caller
  supplies it (Claude audit, §4).
quiz:
- q: Does ColoringIsotopy have a symmetry rule?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 1
  explain: There is no `symm` constructor; `ReversibleColoringIsotopy` is the symmetric fragment.
- q: Which of these moves is in ColoringIsotopy?
  type: choice
  choices:
  - mirror_cong
  - flype_slide_add
  - Local flype
  - transfer_odd
  answer: 2
  explain: '`| localFlype : IsLocalFlype D E → ColoringIsotopy D E`.'
- q: What extra condition do its R1 and R2 moves need?
  type: choice
  choices:
  - None
  - Both diagrams WellFormed
  - Both diagrams rational
  answer: 1
  explain: '`| r1 : IsReidemeisterI D E → D.WellFormed → E.WellFormed → ColoringIsotopy D E`.'
---
## Plain English

**Definition (`ColoringIsotopy`, Flype.lean lines 216-265).** The relation generated, **in one direction**, by:

* reflexivity and transitivity (no symmetry);
* Reidemeister I and II on [well-formed](#/node/TangleDiagram.WellFormed) diagrams, and a local model of Reidemeister III (`IsReidemeisterIIILocal`);
* local flypes ([`IsLocalFlype`](#/node/IsLocalFlype)) and planar isotopy ([`PlanarIsotopy`](#/node/PlanarIsotopy));
* add/mul congruences (the right-hand ones with a port side-condition);
* reindexing identities: T + [0] → T, T → [0] + T, [±1] ↔ [±1]ⁱ, associativity both ways.

It leaves out the Figure 5 slides, half-turns, mirror and general inversion moves, and transfer moves. The repo shows that carrying a coloring with fixed boundary colors from a diagram to its mirror or inverse can fail (`not_coloring_mirror_transport`, `not_coloring_invert_transport`).

`coloring_fraction_ColoringIsotopy` proves that **every** coloring can be carried along any ColoringIsotopy path with the same boundary colors.
