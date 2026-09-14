---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-eight-unit invert-add existence

The forty-eight-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/48`, via the explicit `sharpColAddNegFortyEighth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty-eight switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w48` and applied per crossing, one line each), and the matrix-side `NotMono`
and `-1/48`-to-`-1/48` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty-eight per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~112 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-eight-unit invert-add witness coloring](a70c-neg-forty-eighth-unit-witness.md)
- [Negative forty-eight-unit witness rule preliminaries](a70d-neg-forty-eighth-unit-witness-rules.md)
- [Negative forty-eight-unit witness-value computation](a70e-neg-forty-eighth-unit-witness-value.md)
- [Negative forty-eight-unit existence-head preliminary](a70f-neg-forty-eighth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
