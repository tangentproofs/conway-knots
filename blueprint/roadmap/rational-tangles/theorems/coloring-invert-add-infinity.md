---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_infinity RationalTangles.HasColoringFraction.invert_add_infinity_left
proof: formalized
---

# Invert-add with a trivial infinite summand

On an arbitrary diagram $T$, a right summand $[\infty]$ merges the
endpoints so that $(T+[\infty])^{i}$ admits a constant-on-crossings dummy
coloring of fraction $0$; the algebraic partner
$[\infty]^{i}*T^{i}$ is dummy-colored the same way. A left summand
$[\infty]$ is dual: $([\infty]+T)^{i}$ and $T^{i}*[\infty]^{i}$ both carry
$0$. No port or diagonal hypotheses are needed anywhere: the dummy
colorings are fresh, not transported.

On `slideReady` twists the same dummy colorings carry the formula values
$(F+[\infty])^{-1}$ and $([\infty]+F)^{-1}$, which reduce to $0$
definitionally for every $F$ (`cases F; rfl`).

This is not a `ColoringIsotopy` constructor: invert-add switches crossings.
It is not unrestricted `flype_slide`, not `invert_cong` on
`ColoringIsotopy`, and not Theorem 2.

## Split into pull-request-sized nodes

The remaining results live in:

- [Right summand $[\infty]$](invert-add-infinity/g1-right-infinity.md)
- [Left summand $[\infty]$](invert-add-infinity/g2-left-infinity.md)
- [Invert-mul with $[\infty]$ and the reindex machinery](invert-add-infinity/g3-mul-infinity.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../coloring/theorems/coloring-infinity-mul.md)
