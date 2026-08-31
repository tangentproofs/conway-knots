---
declaration: def
origin: cited
statement: formalized
lean: RationalTangles.ColoringRule
---

# Coloring rule

Colors are taken from $\mathbb{Z}$ or from $\mathbb{Z}/n\mathbb{Z}$ for some
$n$. At a crossing, if two undercrossing arcs colored $\alpha$ and $\gamma$
meet an overcrossing arc colored $\beta$, then
$$
\alpha+\gamma=2\beta,
$$
equivalently $\gamma=2\beta-\alpha$ (Kauffman–Lambropoulou §5, Figure 20).
One under-arc color is determined by the other under-arc color and the
over-arc color.

Write $\tau_\beta(\alpha):=2\beta-\alpha$ for the operation that produces
the remaining under-arc. This is the coloring rule in operational form, used
to check Reidemeister invariance.

## Sources

- [Kauffman–Lambropoulou, coloring rule](../../../../sources/kauffman-lambropoulou.md#coloring-rule)

## Depends on

- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
