---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_unit RationalTangles.coloring_invert_unit_rev RationalTangles.ColoringIsotopy.invert_unit_symm RationalTangles.CFValue.invert_add_units RationalTangles.coloring_mul_invert_units RationalTangles.coloring_add_invert_units
proof: formalized
---

# Unit inversion transport (the single-switch case)

Inversion of a `[±1]` unit recolors by permuting the four arc colors
(`colorInvertUnit`), in both directions, so units are the one class
where a coloring genuinely transports across a single `Crossing.switch`.
The `[±1]±[±1]` colorings and the `CFValue` unit arithmetic backing the
unit invert-add/invert-mul base cases are recorded here. Proof part of
the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
