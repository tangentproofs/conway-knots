---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_flype_slide_add_any_isotopy RationalTangles.coloring_flype_slide_mul_any_isotopy RationalTangles.HasColoringFraction.flype_slide_add_any_isotopy RationalTangles.HasColoringFraction.flype_slide_mul_any_isotopy RationalTangles.coloring_commute_add_any_isotopy RationalTangles.coloring_commute_mul_any_isotopy
proof: formalized
---

# Restricted flype slides with isotopy-related summands

Sign-preserving Figure 5 slides one ring outward: the summand (or
factor) need not itself be twist-form, only `ColoringIsotopy`-related to
a `slideReady` twist. `DiagonalSum` of the sum assembles from the
transported summand diagonal (`diagonal_of_ColoringIsotopy_slideReady`)
and the unit diagonal via `DiagonalSum_of_add` (dually `DiagonalSum_of_mul`
for products), so every (non-monochrome) coloring transports — at
`SameEndpointColors` and `HasColoringFraction` level, carrying its own
fraction value. The glue-port hypotheses stay as stated. Not
unrestricted `Isotopic.flype_slide_*`. Left-unit commutativity
(`[±1]+t ↔ t+[±1]`, `[±1]*t ↔ t*[±1]`) gets the same treatment via the
identical diagonal assembly. Proof part of the parent topic;
see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Flype](../../definitions/flype.md)
