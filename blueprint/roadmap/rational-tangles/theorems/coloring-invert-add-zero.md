---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_right_zero RationalTangles.HasColoringFraction.invert_add_left_zero
proof: formalized
---

# Invert-add with a trivial horizontal summand

On a `slideReady` twist diagram $T$, a right summand $[0]$ is a PD-code
no-op (`add_zero_eq`). Fresh colorings of $(T+[0])^{i}$ therefore agree
with a coloring of $T^{i}$. The algebraic partner is $[0]^{i}*T^{i}=[\infty]*T^{i}$,
colored by the left-product reindex of $T^{i}$. Both sides carry
$(F(T)+0)^{-1}=F(T)^{-1}$.

A left summand $[0]$ is the dummy-strand reindex $[0]+T$. After invert,
that reindex is planar when $T.\mathrm{NW}\neq T.\mathrm{SW}$. Fresh
colorings of $([0]+T)^{i}$ agree with $T^{i}*[0]^{i}$ (again a no-op after
`invert_zero` and `mul_infinity_eq`), both at $F(T)^{-1}$.

Transport from a coloring of $T^{i}$ is fully general over arbitrary
diagrams with no port or diagonal hypotheses
(`HasColoringFraction.invert_add_right_zero` /
`invert_add_left_zero`): $(T+[0])^{i}$ is $T^{i}$ by `add_zero_eq`, and
$([0]+T)^{i}$ is a reindex of $T^{i}$ (`coloring_fraction_invert_zero_add`).
On `slideReady` twists every non-monochrome coloring of $T^{i}$ has
fraction $F^{-1}$, so both sides carry the standard value
(`*_any_slideReady`, plus existence versions). A variant taking a coloring
of $T$ rather than $T^{i}$ is not claimed: it would need transport across a
single `Crossing.switch`, which holds only for units, double mirrors, and
the `slideReady` algebraic-mirror comparisons.

This is not a `ColoringIsotopy` constructor: invert-add switches crossings.
It is not unrestricted `flype_slide`, not `invert_cong` on
`ColoringIsotopy`, and not Theorem 2.

## Split into pull-request-sized nodes

The remaining results live in:

- [Right summand $[0]$](invert-add-zero/g1-right-zero.md)
- [Left summand $[0]$](invert-add-zero/g2-left-zero.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../coloring/theorems/coloring-infinity-mul.md)

## Proof depends on

- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
