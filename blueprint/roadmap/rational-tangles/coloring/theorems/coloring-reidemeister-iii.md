---
declaration: lemma
origin: cited
---

# Coloring invariance under Reidemeister III

Given a coloring of a 2-tangle, there is a way to recolor after a
Reidemeister III move so that the colors on the external strands are
unchanged and the coloring rule still holds at every crossing.

The paper states that this is "easy to verify"; this article is that
verification for R3, not an axiom.

Let $\tau_\beta(\alpha):=2\beta-\alpha$. Reidemeister III is the
self-distributivity identity of this operation,
$$
\tau_{\tau_\beta(\gamma)}(\tau_\beta(\alpha))=\tau_\beta(\tau_\gamma(\alpha)).
$$
Both sides equal $4\beta-2\gamma-\alpha$. Thus the three outgoing strand
colors after sliding a strand over a crossing agree with those before the
slide, and the external strand colors of the tangle are preserved.

## Sources

- [Kauffman–Lambropoulou, coloring Reidemeister invariance](../../../../sources/kauffman-lambropoulou.md#coloring-reidemeister)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Reidemeister moves](../../definitions/reidemeister-moves.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
