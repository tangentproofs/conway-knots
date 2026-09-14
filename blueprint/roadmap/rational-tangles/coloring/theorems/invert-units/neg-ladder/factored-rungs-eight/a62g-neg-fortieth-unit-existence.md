---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-unit invert-add existence

The forty-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/40`, via the explicit `sharpColAddNegFortieth` witness: the
crossing list and matrix bridge (`hcs`/`hM`) are obtained from the companion
existence-head preliminary, the forty switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w40` and applied per crossing, one line each), and the matrix-side `NotMono`
and `1/-40`-to-`-1/40` computation is obtained from the companion witness-value lemma over `hM`.
The witness definition itself is claimed in the companion witness node,
the arc equations in the companion witness-rules node, the crossing-list/matrix
bridge in the companion existence-head node, and the matrix-side computation
in the companion witness-value node (all split for size); this node assembles
the fraction computation over all three preliminaries.
Size note: the forty per-crossing steps are one-line `exact wN`
applications over the factored preliminaries — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~99 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 16384` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative forty-unit invert-add witness coloring](a62c-neg-fortieth-unit-witness.md)
- [Negative forty-unit witness rule preliminaries](a62d-neg-fortieth-unit-witness-rules.md)
- [Negative forty-unit witness-value computation](a62e-neg-fortieth-unit-witness-value.md)
- [Negative forty-unit existence-head preliminary](a62f-neg-fortieth-unit-existence-head.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
