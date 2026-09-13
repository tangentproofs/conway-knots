---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative thirty-unit invert-add existence

The thirty-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/30`, via the explicit `sharpColAddNegThirty` witness: the
matrix computation gives `⟨-28,-27,2,3⟩`, the thirty switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w30` and applied per crossing, one line each), and `1/-30`
normalizes to `-1/30`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node (split for
size); this node carries the fraction computation over both.
Size note: the thirty per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~172 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 8192` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-unit invert-add witness coloring](a52c-neg-thirty-unit-witness.md)
- [Negative thirty-unit witness rule preliminaries](a52d-neg-thirty-unit-witness-rules.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
