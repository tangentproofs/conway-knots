---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative thirty-six-unit invert-add existence

The thirty-six-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/36`, via the explicit `sharpColAddNegThirtySix` witness: the
matrix computation gives `⟨-34,-33,2,3⟩`, the thirty-six switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w36` and applied per crossing, one line each), and the matrix-side `NotMono`
and `1/-36`-to-`-1/36` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node plus the matrix-side computation
in the companion witness-value node (both split for size); this node carries the fraction
computation over both preliminaries.
Size note: the thirty-six per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~193 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative thirty-six-unit invert-add witness coloring](a58c-neg-thirty-six-unit-witness.md)
- [Negative thirty-six-unit witness rule preliminaries](a58d-neg-thirty-six-unit-witness-rules.md)
- [Negative thirty-six-unit witness-value computation](a58e-neg-thirty-six-unit-witness-value.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
