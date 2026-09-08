---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_toNoMulTop RationalTangles.HasColoringFraction.toNoMulTop_slideReady RationalTangles.coloring_toNoMulTop_joint RationalTangles.HasColoringFraction.toNoMulTop_joint
proof: formalized
---

# Coloring transport along mulTop normalization

A `slideReady` twist recolors along `toNoMulTop` with preserved color
matrix: congruence cases reglue directly, `addLeft` restricts and
reglues on the left (glue identification discharged by the port
hypothesis), and only `mulTop` flips sides — via the Figure 5 slide,
recursion under `rot180` (there and back by the double-`rot180` trick),
and a final glue, with `DiagonalSum` discharged from `colorFrom` at
each coloring. Carried coloring fractions transfer at the same value.
The joint theorems package matrix transport with algebraic-fraction
preservation on `slideReady` + `unitMulTop` twists (independent axes:
neither hypothesis implies the other). Transport from colorings of
non-`slideReady` diagrams is outstanding.
Proof part of the parent topic; see that page for the mathematical
context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Flype](../../definitions/flype.md)
