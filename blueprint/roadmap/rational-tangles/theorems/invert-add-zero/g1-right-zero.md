---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_add_slideReady_zero RationalTangles.HasColoringFraction.invert_add_slideReady_zero RationalTangles.HasColoringFraction.invert_add_right_zero_any_slideReady RationalTangles.HasColoringFraction.invert_add_right_zero_slideReady_exists
proof: formalized
---

# Invert-add with a right summand $[0]$

On a `slideReady` twist diagram $T$, a right summand $[0]$ is a PD-code
no-op (`add_zero_eq`). Fresh colorings of $(T+[0])^{i}$ therefore agree
with a coloring of $T^{i}$. The algebraic partner is $[0]^{i}*T^{i}=[\infty]*T^{i}$,
colored by the left-product reindex of $T^{i}$. Both sides carry
$(F(T)+0)^{-1}=F(T)^{-1}$.

Transport from a coloring of $T^{i}$ is fully general over arbitrary
diagrams (`HasColoringFraction.invert_add_right_zero`, claimed on the
parent page). On `slideReady` twists every non-monochrome coloring of
$T^{i}$ has fraction $F^{-1}$, so the transported coloring carries the
standard value (`invert_add_right_zero_any_slideReady`, plus the
existence version). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
