---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative thirty-seven-unit invert-add existence

The thirty-seven-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/37`, via the explicit `sharpColAddNegThirtySeven` witness: the
matrix computation gives `⟨-35,-34,2,3⟩`, the thirty-seven switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w37` and applied per crossing, one line each), and the matrix-side `NotMono`
and `1/-37`-to-`-1/37` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node plus the matrix-side computation
in the companion witness-value node (both split for size); this node carries the fraction
computation over both preliminaries.
Size note: the thirty-seven per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~197 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-seven-unit invert-add witness coloring](a59c-neg-thirty-seven-unit-witness.md)
- [Negative thirty-seven-unit witness rule preliminaries](a59d-neg-thirty-seven-unit-witness-rules.md)
- [Negative thirty-seven-unit witness-value computation](a59e-neg-thirty-seven-unit-witness-value.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
