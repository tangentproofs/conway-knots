---
declaration: def
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortyThird
---

# Negative forty-three-unit invert-add witness coloring

The explicit `sharpColAddNegFortyThird` witness coloring for the
forty-three-unit inverted sum, extending the forty-two-unit coloring by
the forced pair `(-41,-40)` on the fresh arcs `128/129`. Split into its own
node for size: at this rung depth the def-plus-fraction-computation block
projects past ~190 lines, so the witness definition is claimed here and
the fraction computation lives in the companion existence node. A plain
if-else chain over arc indices; it elaborates with no `maxRecDepth`
override. Statement part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
