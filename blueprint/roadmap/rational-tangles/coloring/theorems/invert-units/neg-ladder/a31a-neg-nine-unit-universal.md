---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative nine-unit invert-add universal

Every non-monochrome coloring of `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ` has
fraction `-1/9` (universal): the nine switched rules force numerator `d`
and denominator `-9d` for nonzero `d`, with no `DiagonalSum` or port
inputs. The negative units are mirror-switches of the positive ones, so
the arc wirings — and the sign of the denominator multiple — differ from
the positive-ladder case; the nonzero transfer additionally needs
`neg_ne_zero` since the denominator multiple is negative. The ninth base
crossing ⟨26,27,24,23,neg⟩ rejoins the prior rung's fresh arcs 24/23 per
the add-gluing pattern, switching to ⟨27,24,23,26,pos⟩. At this rung depth
the invert expression needs `set_option maxRecDepth 1024` to elaborate.
Evaluated directly. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../definitions/integer-tangle.md)
