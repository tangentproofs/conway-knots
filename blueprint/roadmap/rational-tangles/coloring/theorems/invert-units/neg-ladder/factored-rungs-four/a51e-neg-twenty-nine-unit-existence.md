---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative twenty-nine-unit invert-add existence

The twenty-nine-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/29`, via the explicit `sharpColAddNegTwentyNine` witness: the
matrix computation gives `⟨-27,-26,2,3⟩`, the twenty-nine switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w29` and applied per crossing, one line each), and `1/-29`
normalizes to `-1/29`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node (split for
size); this node carries the fraction computation over both.
Size note: the twenty-nine per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~166 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 8192` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-nine-unit invert-add witness coloring](a51c-neg-twenty-nine-unit-witness.md)
- [Negative twenty-nine-unit witness rule preliminaries](a51d-neg-twenty-nine-unit-witness-rules.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
