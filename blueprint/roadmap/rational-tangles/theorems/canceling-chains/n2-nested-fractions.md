---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.appendUnits_canceling_integerUnits_fraction RationalTangles.integerTangle_neg_ofNat RationalTangles.TwistExpr.appendUnits_ofInteger_canceling_fraction RationalTangles.coloring_fraction_canceling_integerUnits RationalTangles.coloring_fraction_canceling_ofInteger RationalTangles.HasColoringFraction.canceling_integerUnits RationalTangles.HasColoringFraction.canceling_ofInteger RationalTangles.TwistExpr.ofInteger_toStandard_fraction RationalTangles.TwistExpr.ofInteger_slideReady RationalTangles.TwistExpr.ofVertical_rightBottom RationalTangles.TwistExpr.ofVertical_fraction RationalTangles.TwistExpr.ofVertical_toStandard_fraction RationalTangles.TwistExpr.ofVertical_slideReady
proof: formalized
---

# Nested canceling chains, fractions and existence

$n$ units of sign $s$ followed by $n$ of $s.flip$ — including
`ofInteger n` followed by $|n|$ opposite units — form `rightBottom`
twists of fraction $0$ (`appendUnits_*_fraction`). Every non-monochrome
coloring has fraction $0$, with `HasColoringFraction` existence via
`colorFrom`. The `ofInteger` standard-form value and `slideReady`
facts are recorded here, with the vertical `ofVertical` analogues
(`rightBottom`, fraction, standard value, `slideReady`). Proof part of
the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
- [Left product by the vertical trivial tangle is planar reindexing](../../coloring/theorems/coloring-infinity-mul.md)
