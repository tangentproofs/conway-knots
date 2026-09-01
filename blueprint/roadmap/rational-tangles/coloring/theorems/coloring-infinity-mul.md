---
declaration: lemma
origin: bridged
statement: formalized
lean: RationalTangles.planar_infinity_mul RationalTangles.coloring_infinity_mul RationalTangles.coloring_fraction_infinity_mul
proof: formalized
---

# Left product by the vertical trivial tangle is planar reindexing

Left-multiplying a 2-tangle diagram `T` by the vertical trivial tangle is a
renaming of the arcs of `T` (glue the top NW/NE of `T` onto the two vertical
strands). When $T.\mathrm{NW}\neq T.\mathrm{NE}$ the four endpoints match this reindexing, so
the diagrams are planar isotopic. An integral coloring of `T` transports to
the product with unchanged endpoint colors, hence the same color matrix and
coloring fraction, even if $T.\mathrm{NW}=T.\mathrm{NE}$ (the product then records an unused
NE name).

This is the degenerate flype-slide case in which the sliding "crossing" is
absent. It is not unrestricted algebraic Figure 5, and it is not a new
`ColoringIsotopy` constructor: planar isotopy is already coloring-ready when
the endpoints match.

This article does not claim Theorem 2.

## Sources

- [Kauffman–Lambropoulou Definition 2](../../../../sources/kauffman-lambropoulou.md#definition-2)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Color matrix](../definitions/color-matrix.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Flype](../../definitions/flype.md)
