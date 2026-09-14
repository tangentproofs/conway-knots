---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-six-unit invert-add existence

The forty-six-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/46`, via the explicit `sharpColAddNegFortySixth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty-six switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w46` and applied per crossing, one line each), and the matrix-side `NotMono`
and `-1/46`-to-`-1/46` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty-six per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~108 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-six-unit invert-add witness coloring](a68c-neg-forty-sixth-unit-witness.md)
- [Negative forty-six-unit witness rule preliminaries](a68d-neg-forty-sixth-unit-witness-rules.md)
- [Negative forty-six-unit witness-value computation](a68e-neg-forty-sixth-unit-witness-value.md)
- [Negative forty-six-unit existence-head preliminary](a68f-neg-forty-sixth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
