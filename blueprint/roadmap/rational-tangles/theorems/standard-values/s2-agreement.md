---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_eq_F RationalTangles.coloring_fraction_eq_F_any_slideReady RationalTangles.coloring_fraction_eq_F_rightBottom RationalTangles.coloring_fraction_eq_F_addLeft RationalTangles.coloring_fraction_eq_F_mulTop RationalTangles.coloring_fraction_eq_F_mulTop_bottom RationalTangles.coloring_fraction_eq_F_cf RationalTangles.coloring_fraction_eq_F_standard
proof: formalized
---

# Coloring fraction equals the standard value

On a `slideReady` twist, every non-monochrome coloring satisfying the
diagonal rule has coloring fraction equal to the arithmetical fraction
of `toStandard` — on `rightBottom` diagrams with value `e.fraction`,
on `addLeft` with `F`, on `mulTop` with the `toStandard` value (top
Conway product need not equal algebraic `mulTop.fraction`), in
continued-fraction term-list form (Remark 6), and on standard forms
against the term-list value. The `DiagonalSum` input is discharged
internally on `slideReady` twists (`coloring_fraction_eq_F_any_slideReady`).
Proof part of the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
