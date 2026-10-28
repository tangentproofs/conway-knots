---
id: TangleDiagram
title: A 2-tangle diagram as a planar-diagram code
summary: '**The surprise:** a tangle is stored as a list of crossings, each four arc numbers plus a sign, and the
  arc numbers at the four corners. No geometry at all, and nothing forces the code to be drawable in a disc.'
review: draft
authors:
- grok-bot
caveats:
- No planarity or well-formedness is built into the type (Claude audit, §5).
quiz:
- q: What does a `TangleDiagram` store?
  type: choice
  choices:
  - Coordinates of the strings in space
  - A list of crossings (four arc numbers and a sign each) and the arc number at each corner
  - A continued fraction
  answer: 1
  explain: 'The fields are `crossings : List Crossing` and `NW NE SE SW : Nat`.'
- q: Does the type guarantee that the code is a real planar diagram?
  type: choice
  choices:
  - 'Yes'
  - 'No: there is no planarity condition, and `WellFormed` (each arc has exactly two ends) is a separate predicate'
  answer: 1
  explain: The type includes codes that can't be drawn in a disc. The headline objects are built by honest operations,
    so this doesn't affect them, but statements about arbitrary `TangleDiagram`s are about the larger model.
- q: How are two codes that differ only by renaming arcs treated?
  type: choice
  choices:
  - They are equal as Lean values
  - They are different values, related by `PlanarIsotopy`
  answer: 1
  explain: The type is not quotiented; `PlanarIsotopy` (renaming, reordering, rotating a crossing) relates them.
---
## Plain English

A **2-tangle** is two strings in a ball with their four ends pinned at the corners NW, NE, SE, SW of the picture (plus possibly closed loops).

**Definition (`TangleDiagram`, Reidemeister.lean lines 177-187).** A diagram is

* `crossings`: a list of [`Crossing`](#/node/Crossing)s. Each crossing names the four arcs that meet it, counterclockwise, with the over-strand on ports 0 and 2, plus a sign;
* `NW`, `NE`, `SE`, `SW`: the arc number touching each corner.

This is the tangle version of a knot's **PD code**. It was chosen so an integer coloring is just a function from arc numbers to ℤ ([`IsColored`](#/node/TangleDiagram.IsColored)).

The trivial tangles have no crossings: [`[0]`](#/node/TangleDiagram.zero) (two horizontal arcs) and [`[∞]`](#/node/TangleDiagram.infinity) (two vertical arcs).
