---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-four-unit invert-add existence

The forty-four-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/44`, via the explicit `sharpColAddNegFortyFourth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty-four switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w44` and applied per crossing, one line each), and the matrix-side `NotMono`
and `-1/44`-to-`-1/44` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty-four per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~104 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-four-unit invert-add witness coloring](a66c-neg-forty-fourth-unit-witness.md)
- [Negative forty-four-unit witness rule preliminaries](a66d-neg-forty-fourth-unit-witness-rules.md)
- [Negative forty-four-unit witness-value computation](a66e-neg-forty-fourth-unit-witness-value.md)
- [Negative forty-four-unit existence-head preliminary](a66f-neg-forty-fourth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
