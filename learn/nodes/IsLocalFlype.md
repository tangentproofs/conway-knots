---
id: IsLocalFlype
title: A local flype
summary: '**The surprise:** a flype is the move behind Tait''s 1870s flyping conjecture, and here it is one crossing
  sliding across a neighbouring sub-diagram that gets turned over on the way.'
review: draft
authors:
- grok-bot
caveats:
- Like `flype_slide_add`, it rotates the passed sub-diagram 180° rather than flipping it; the Claude audit notes
  the same one-flip/two-flip question applies here.
quiz:
- q: What happens to the crossings the flype passes over?
  type: choice
  choices:
  - They are deleted
  - They are rotated 180°
  - They are mirrored
  answer: 1
  explain: '`pairRel (fun C Y => (C.rotate180.rename f).sameUpToRotation Y) tD tE`.'
- q: Is a local flype a coloring-safe move?
  type: choice
  choices:
  - 'Yes'
  - 'No'
  answer: 0
  explain: '`ColoringIsotopy.localFlype`.'
- q: Do the corners change?
  type: choice
  choices:
  - They correspond under the renaming f
  - They swap
  answer: 0
  explain: '`E.NW = f D.NW` and so on.'
---
## Plain English

**Definition (`IsLocalFlype`, Flype.lean lines 107-118).** E arises from D by moving one crossing to the other side of a sub-list of crossings, rotating each of those crossings 180°, with the rest matched by an injective renaming and the corners preserved.

It is in both [`Isotopic`](#/node/Isotopic) and [`ColoringIsotopy`](#/node/ColoringIsotopy).
