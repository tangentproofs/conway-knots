---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative eleven-unit invert-add universal

Every non-monochrome coloring of `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`
has fraction `-1/11` (universal): the eleven switched rules force numerator
`d` and denominator `-11d` for nonzero `d`, with no `DiagonalSum` or port
inputs. The negative units are mirror-switches of the positive ones, so
the arc wirings — and the sign of the denominator multiple — differ from
the positive-ladder case; the nonzero transfer additionally needs
`neg_ne_zero` since the denominator multiple is negative. Proved over
the factored rule preliminaries (same `decide` + `linarith` machinery),
which keeps this node well under the span limit. At this rung depth the
invert expression needs `set_option maxRecDepth 2048` to elaborate.
Evaluated directly. Proof part of the parent topic; see that page for
the mathematical context.

## Depends on

- [Negative eleven-unit invert-add rule preliminaries](a33-neg-eleven-unit-preliminaries.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
