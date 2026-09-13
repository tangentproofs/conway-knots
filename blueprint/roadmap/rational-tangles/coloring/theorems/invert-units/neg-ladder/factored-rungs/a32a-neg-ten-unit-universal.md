---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative ten-unit invert-add universal

Every non-monochrome coloring of `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`
has fraction `-1/10` (universal): the ten switched rules force numerator
`d` and denominator `-10d` for nonzero `d`, with no `DiagonalSum` or port
inputs. The negative units are mirror-switches of the positive ones, so
the arc wirings — and the sign of the denominator multiple — differ from
the positive-ladder case; the nonzero transfer additionally needs
`neg_ne_zero` since the denominator multiple is negative. Proved over
the factored rule preliminaries (same `decide` + `linarith` machinery),
which keeps this node well under the span limit. At this rung depth the
invert expression needs `set_option maxRecDepth 1024` to elaborate.
Evaluated directly. Proof part of the parent topic; see that page for
the mathematical context.

## Depends on

- [Negative ten-unit invert-add rule preliminaries](a32-neg-ten-unit-preliminaries.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
