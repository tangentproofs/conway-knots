---
declaration: lemma
origin: cited
---

# Coloring invariance under Reidemeister II

Given a coloring of a 2-tangle, there is a way to recolor after a
Reidemeister II move so that the colors on the external strands are
unchanged and the coloring rule still holds at every crossing.

The paper states that this is "easy to verify"; this article is that
verification for R2, not an axiom.

Let $\tau_\beta(\alpha):=2\beta-\alpha$. This operation is an involution in
the over-color: $\tau_\beta(\tau_\beta(\alpha))=\alpha$. In an R2 pair, two
strands of incoming colors $\alpha$ and $\delta$ form two opposite
crossings with the same over-color $\beta$ (up to which strand is over).
The intermediate under-color created by the first crossing is cancelled by
the second, so the outgoing colors equal the incoming colors. Removing the
two crossings likewise leaves external colors unchanged.

## Sources

- [Kauffman–Lambropoulou, coloring Reidemeister invariance](../../../../sources/kauffman-lambropoulou.md#coloring-reidemeister)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Reidemeister moves](../../definitions/reidemeister-moves.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
