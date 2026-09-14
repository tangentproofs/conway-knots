---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-five-unit invert-add existence

The forty-five-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/45`, via the explicit `sharpColAddNegFortyFifth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty-five switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w45` and applied per crossing, one line each), and the matrix-side `NotMono`
and `-1/45`-to-`-1/45` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty-five per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~106 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-five-unit invert-add witness coloring](a67c-neg-forty-fifth-unit-witness.md)
- [Negative forty-five-unit witness rule preliminaries](a67d-neg-forty-fifth-unit-witness-rules.md)
- [Negative forty-five-unit witness-value computation](a67e-neg-forty-fifth-unit-witness-value.md)
- [Negative forty-five-unit existence-head preliminary](a67f-neg-forty-fifth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
