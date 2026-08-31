---
declaration: lemma
origin: cited
statement: formalized
lean: RationalTangles.coloring_IsReidemeisterI
proof: formalized
---

# Coloring invariance under Reidemeister I

Given a coloring of a 2-tangle, there is a way to recolor after a
Reidemeister I move so that the colors on the external strands are
unchanged and the coloring rule still holds at every crossing.

The paper states that this (together with R2, R3, and flypes) is "easy to
verify"; this article is that verification for R1, not an axiom.

Let $\tau_\beta(\alpha):=2\beta-\alpha$. On a kink, the over-arc and the two
under-arcs are segments of a single strand. If the incoming color is
$\alpha$ and the over-arc of the kink is colored $\beta$, the outgoing
color is $\tau_\beta(\alpha)$. Closing the kink identifies the over-arc with
the outgoing (or incoming) under-arc, which forces $\beta=\alpha$ and hence
$\tau_\alpha(\alpha)=\alpha$. Thus a kink is colored by a single color, equal
to the color of the un-kinked strand, and the external strand colors are
preserved.

## Sources

- [Kauffman–Lambropoulou, coloring Reidemeister invariance](../../../../sources/kauffman-lambropoulou.md#coloring-reidemeister)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Reidemeister moves](../../definitions/reidemeister-moves.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
