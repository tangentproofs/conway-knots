---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.two_block_of_nested_canceling RationalTangles.HasColoringFraction.invert_two_block_of_nested_canceling
proof: formalized
---

# Invert-add of canceling chains

Nested right-adds of $n$ units of sign $s$ followed by $n$ of $s.flip$
(including `ofInteger n` followed by $|n|$ opposite units) are
`rightBottom` twists of fraction $0$; every non-monochrome coloring has
fraction $0$ by uniqueness, and invert-add reuses the unit/integer
invert-add lemmas with carried value $\infty$. The two-unit pairs
$[+1]+[-1]$ and $[-1]+[+1]$ are the base case. Mixed-sign integer pieces
summing to $0$ behave the same way.

A nested canceling chain is coloring-isotopic to the two-block PD-sum
(`coloringIsotopy_nested_canceling`, claimed with the reindex machinery),
so the two-block sum carries $0$ and its invert carries $\infty$ —
the bridge claimed here.

This is not a `ColoringIsotopy` constructor: invert-add switches crossings.
It is not unrestricted `flype_slide`, not `invert_cong` on
`ColoringIsotopy`, and not Theorem 2.

## Split into pull-request-sized nodes

The remaining results live in:

- [Two canceling units](n1-two-units.md)
- [Nested canceling chains, fractions and existence](n2-nested-fractions.md)
- [Invert-add of nested canceling chains](n3-nested-invert-add.md)
- [Mixed-sign canceling pieces](n4-mixed-sign.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)

## Proof depends on

- [Coloring fraction after invert on slide-ready diagrams](../coloring-invert-cong-slideReady.md)
