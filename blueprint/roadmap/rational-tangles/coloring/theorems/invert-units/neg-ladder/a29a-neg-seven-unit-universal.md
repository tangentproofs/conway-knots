---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative seven-unit invert-add universal

Every non-monochrome coloring of the seven-unit inverted sum has fraction
`-1/7` (universal): the seven switched rules force numerator `d` and
denominator `-7d` for nonzero `d`, with no `DiagonalSum` or port inputs.
Same `decide` + `linarith` machinery with the `neg_ne_zero` pattern for the
negative denominator multiple. At this rung depth the invert expression
needs `set_option maxRecDepth 1024` to elaborate. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../definitions/integer-tangle.md)
