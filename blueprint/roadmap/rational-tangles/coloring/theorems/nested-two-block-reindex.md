---
declaration: lemma
origin: bridged
statement: formalized
lean: RationalTangles.foldAddUnits RationalTangles.integerBlock RationalTangles.addZeroBlockReindex RationalTangles.planar_of_rename RationalTangles.planar_invert_of_rename RationalTangles.planar_foldAddUnits_integerBlock RationalTangles.planar_foldAddUnits_integerBlock_invert RationalTangles.coloringIsotopy_nested_add_integerTangle RationalTangles.coloringIsotopy_nested_canceling RationalTangles.planar_nested_canceling_invert
proof: formalized
---

# Nested unit chains versus two-block PD-sums

A nested right-add of $n$ copies of $[\pm 1]$ onto a diagram $T$ is the
same projection as the two-block PD-sum $T+(n\text{ units stacked on }[0])$
after a $+2$ arc reindex: the right block is built from $[0]$, whose dummy
arcs bump `maxArc` by $2$. Matching endpoints and renamed crossings make
this a planar isotopy. It is not a flype.

Inversion preserves that rename: `Crossing.switch` commutes with
`rename`, so the inverted nested chain is planar-isotopic to the inverted
two-block sum. That is not `invert_cong` on `ColoringIsotopy`.

On integer diagrams the nested mixed-sign chain is coloring-ready isotopic
to the two-block PD-sum of opposite integer tangles, and the inverted
nested canceling chain is planar-isotopic to the inverted two-block sum.

This article does not claim Theorem 2.

## Sources

- [Kauffman–Lambropoulou Definition 2](../../../../sources/kauffman-lambropoulou.md#definition-2)

## Depends on

- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
