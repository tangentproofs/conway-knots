---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative twenty-two-unit invert-add existence

The twenty-two-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/22`, via the explicit `sharpColAddNegTwentyTwo` witness: the
matrix computation gives `⟨-20,-19,2,3⟩`, the twenty-two switched rules
are discharged by `decide`, and `1/-22` normalizes to `-1/22`.
The witness definition itself is claimed in the companion witness node
(split for size); this node carries the fraction computation over it.
At this rung depth the invert expression needs
`set_option maxRecDepth 4096` to elaborate. Proof part of the
parent topic; see that page for the mathematical context.

## Depends on

- [Negative twenty-two-unit invert-add witness coloring](a44b-neg-twenty-two-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
