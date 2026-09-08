---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.colorFrom_eq_fraction_slideReady RationalTangles.TwistExpr.toStandard_fraction_eq_of_diagram_slideReady_colorFrom RationalTangles.IsTwistForm.toStandard_fraction_unique_slideReady RationalTangles.coloring_toStandard_any_isotopy
proof: formalized
---

# Standard values of twist colorings

The core value theorems: on a `slideReady` twist every non-monochrome
coloring has fraction $F$ (`coloring_fraction_eq_F` family), reached via
the explicit `toStandard` path (`coloring_fraction_toStandard`); the
diagonal rule holds on every coloring of these diagrams
(`twist_coloring_diagonal_*`); and fresh invert colorings carry $1/F$.
At the diagram level, `toStandard.fraction` depends only on the PD-code
among `slideReady` parses — the assignments claimed here — and any
diagram `ColoringIsotopy`-related to a `slideReady` twist recolors along
`toStandard` with matrix preserved (`coloring_toStandard_any_isotopy`,
no twist-form or `DiagonalSum` input on the source).

This is Theorem 4(7) along explicit coloring paths, not along an
arbitrary `Isotopic` witness of `IsRational`: unrestricted
`flype_slide_*`, switch-based generators, and non-`slideReady` parses
remain outstanding, so this node is not marked proved beyond its
children.

## Split into pull-request-sized nodes

The remaining results live in:

- [Diagonal sum on twist diagrams](s1-diagonal.md)
- [Coloring fraction equals the standard value](s2-agreement.md)
- [The toStandard path and standard forms](s3-standard-path.md)
- [Fresh invert colorings of twists](s4-twist-invert.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
