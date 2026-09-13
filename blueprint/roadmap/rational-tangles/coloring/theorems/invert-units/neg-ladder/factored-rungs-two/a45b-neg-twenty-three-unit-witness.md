---
declaration: def
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegTwentyThree
---

# Negative twenty-three-unit invert-add witness coloring

The explicit `sharpColAddNegTwentyThree` witness coloring for the
twenty-three-unit inverted sum, extending the twenty-two-unit coloring by
the forced pair `(-21,-20)` on the fresh arcs `68/69`. Split into its own
node for size: at this rung depth the def-plus-fraction-computation block
projects past ~190 lines, so the witness definition is claimed here and
the fraction computation lives in the companion existence node. A plain
if-else chain over arc indices; it elaborates with no `maxRecDepth`
override. Statement part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
