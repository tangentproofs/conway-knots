---
declaration: lemma
origin: cited
---

# Coloring invariance under flypes

Given a coloring of a 2-tangle, there is a way to recolor after a flype so
that the colors on the external strands are unchanged and the coloring rule
still holds at every crossing.

The paper groups flypes with Reidemeister moves as "easy to verify"
invariances of the coloring. This article is that verification for a flype,
not an axiom. A flype is an isotopy, but the coloring statement is a
diagram chase: it must not be imported from Tait or from an unproved
isotopy-invariance of $f$.

On a subtangle of the form $[\pm 1]+t$ (resp. $[\pm 1]\ast t$), the flype
moves the $[\pm 1]$ crossing to the opposite side while rotating $t$ by a
horizontal (resp. vertical) flip, fixing the endpoints of the subtangle.
The coloring rule at the $[\pm 1]$ crossing relates the two colors adjacent
to $t$ on that side. After the flype, the same linear relation, together
with the permutation of $t$'s endpoints under the flip, recolors $t$ so
that the four external colors of the whole 2-tangle agree with those before
the flype.

## Sources

- [Kauffman–Lambropoulou, coloring Reidemeister invariance](../../../../sources/kauffman-lambropoulou.md#coloring-reidemeister)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Flype](../../definitions/flype.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)

## Proof depends on

- [Flip](../../definitions/flip.md)
- [Color matrix](../definitions/color-matrix.md)
