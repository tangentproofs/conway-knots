---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-nine-unit invert-add existence

The forty-nine-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/49`, via the explicit `sharpColAddNegFortyNinth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty-nine switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w49` and applied per crossing, one line each), and the matrix-side `NotMono`
and `-1/49`-to-`-1/49` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty-nine per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~114 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-nine-unit invert-add witness coloring](a71c-neg-forty-ninth-unit-witness.md)
- [Negative forty-nine-unit witness rule preliminaries](a71d-neg-forty-ninth-unit-witness-rules.md)
- [Negative forty-nine-unit witness-value computation](a71e-neg-forty-ninth-unit-witness-value.md)
- [Negative forty-nine-unit existence-head preliminary](a71f-neg-forty-ninth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
