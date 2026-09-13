---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative twenty-eight-unit invert-add existence

The twenty-eight-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/28`, via the explicit `sharpColAddNegTwentyEight` witness: the
matrix computation gives `⟨-26,-25,2,3⟩`, the twenty-eight switched rules
are discharged through the witness-rules preliminary (obtained as
`w1 … w28` and applied per crossing, one line each), and `1/-28`
normalizes to `-1/28`.
The witness definition itself is claimed in the companion witness node,
and the arc equations in the companion witness-rules node (split for
size); this node carries the fraction computation over both.
Size note: the twenty-eight per-crossing steps are one-line `exact wN`
applications over the factored preliminary — the old inline 3-line `show`
form projects the audit span past the 200 limit at this rung depth, while
the factored form holds it at ~162 with identical proof content. At this
rung depth the invert expression needs `set_option maxRecDepth 8192` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-eight-unit invert-add witness coloring](a50b-neg-twenty-eight-unit-witness.md)
- [Negative twenty-eight-unit witness rule preliminaries](a50c-neg-twenty-eight-unit-witness-rules.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
