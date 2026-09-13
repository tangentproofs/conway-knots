---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.unitChain_invert_ladder_eq RationalTangles.HasColoringFraction.unitChain_invert
proof: formalized
---

# Witnesses for every rung of the positive unit chain

Every rung is inhabited: `(unitChain n).invert` carries `1/(n+2)`.
The ladder data is factored in integer form (denominator `(n+2)`
times numerator, both nonzero), and the witness extends the previous
rung by the forced values at the two fresh arcs. Old arcs are
untouched because every prefix arc is at most `3n+6`
(`arc_le_maxArc_of_mem` with `maxArc_invert` and the `unitChain`
closed form); the extended coloring then inherits the universal
value. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
