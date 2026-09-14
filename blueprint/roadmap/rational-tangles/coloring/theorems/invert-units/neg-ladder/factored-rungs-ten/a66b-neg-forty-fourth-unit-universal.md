---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative forty-four-unit invert-add universal

Every non-monochrome coloring of `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`
has fraction `-1/44` (universal): the forty-four switched rules force numerator
`d` and denominator `-44d` for nonzero `d`, with no `DiagonalSum` or port
inputs. The negative units are mirror-switches of the positive ones, so
the arc wirings — and the sign of the denominator multiple — differ from
the positive-ladder case; the nonzero transfer additionally needs
`neg_ne_zero` since the denominator multiple is negative. Proved over
the factored rule preliminaries (the crossings lemma plus the fraction-value
lemma that now holds the linarith tail, same `decide` + `linarith` machinery),
which keeps this node well under the span limit. At this rung depth the
invert expression needs `set_option maxRecDepth 16384` to elaborate.
Evaluated directly. Proof part of the parent topic; see that page for
the mathematical context.

## Depends on

- [Negative forty-four-unit invert-add rule preliminaries](a66-neg-forty-fourth-unit-preliminaries.md)
- [Negative forty-four-unit fraction-value preliminary](a66a-neg-forty-fourth-unit-fraction-value.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
