---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_unitChain_invert
proof: formalized
---

# Inductive universal over the positive unit chain

The positive invert-add ladder closes at once: every non-monochrome
coloring of `(unitChain n).invert` has fraction `1/(n+2)`. Rung `n`
is the left-nested sum of `n+2` positive units, so this covers the
two-unit rung at `1/2` through all higher rungs, subsuming the
per-rung values of the two/three/four/five-unit nodes. The step
algebra is the per-rung pattern: the new numerator equals the old one
while the new denominator gains one more multiple, with the nonzero
transfers via `mul_ne_zero`. Rests on the collapse node for the
prefix restriction and `NotMono` transfer. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
