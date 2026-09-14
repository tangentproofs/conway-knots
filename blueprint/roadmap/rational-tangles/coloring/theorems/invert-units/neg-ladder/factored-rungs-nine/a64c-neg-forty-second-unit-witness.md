---
declaration: def
origin: bridged
statement: formalized
lean: RationalTangles.sharpColAddNegFortySecond
---

# Negative forty-two-unit invert-add witness coloring

The explicit `sharpColAddNegFortySecond` witness coloring for the
forty-two-unit inverted sum, extending the forty-one-unit coloring by
the forced pair `(-40,-39)` on the fresh arcs `125/126`. Split into its own
node for size: at this rung depth the def-plus-fraction-computation block
projects past ~190 lines, so the witness definition is claimed here and
the fraction computation lives in the companion existence node. A plain
if-else chain over arc indices; it elaborates with no `maxRecDepth`
override. Statement part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
