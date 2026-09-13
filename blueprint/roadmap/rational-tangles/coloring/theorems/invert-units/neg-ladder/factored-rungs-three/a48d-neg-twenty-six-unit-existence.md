---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative twenty-six-unit invert-add existence

The twenty-six-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/26`, via the explicit `sharpColAddNegTwentySix` witness: the
matrix computation gives `⟨-24,-23,2,3⟩`, the twenty-six switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w26` and applied per crossing, one line each), and `1/-26`
normalizes to `-1/26`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node (split for
size); this node carries the fraction computation over both.
Size note: the twenty-six per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~151 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 8192` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-six-unit invert-add witness coloring](a48b-neg-twenty-six-unit-witness.md)
- [Negative twenty-six-unit witness rule preliminaries](a48c-neg-twenty-six-unit-witness-rules.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
