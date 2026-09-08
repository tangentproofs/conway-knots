---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_add_zero_slideReady RationalTangles.HasColoringFraction.invert_add_zero_slideReady RationalTangles.planar_zero_add_invert RationalTangles.HasColoringFraction.invert_add_left_zero_any_slideReady RationalTangles.HasColoringFraction.invert_add_left_zero_slideReady_exists
proof: formalized
---

# Invert-add with a left summand $[0]$

A left summand $[0]$ is the dummy-strand reindex $[0]+T$. After invert,
that reindex is planar when $T.\mathrm{NW}\neq T.\mathrm{SW}$
(`planar_zero_add_invert`), and coloring reindexes with no port
hypothesis (`coloring_fraction_invert_zero_add`). Fresh colorings of
$([0]+T)^{i}$ agree with $T^{i}*[0]^{i}$ (again a no-op after
`invert_zero` and `mul_infinity_eq`), both at $F(T)^{-1}$.

Transport from a coloring of $T^{i}$ is fully general over arbitrary
diagrams (`HasColoringFraction.invert_add_left_zero`, claimed on the
parent page). On `slideReady` twists every non-monochrome coloring of
$T^{i}$ has fraction $F^{-1}$, so the transported coloring carries the
standard value (`invert_add_left_zero_any_slideReady`, plus the
existence version). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
