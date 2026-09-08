---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.rational_classification_fragment
---

# Classification of rational tangles

Two rational tangles are isotopic if and only if they have the same fraction.

This is Theorem 1 of Kauffman–Lambropoulou, attributed to Conway (1970). The
paper states it in the Introduction. This DAG obtains it as the conjunction
of Theorem 2 (the fraction is an isotopy invariant, via the coloring
fraction $f$ of Theorem 4) and Theorem 3 (equal fractions yield isotopic
tangles, from §4). Tait flyping and Proposition 4 are not used.

## Formalization status

Formalized on the proved fragment
(`rational_classification_fragment`): along `ColoringIsotopy` between
`noMulTop` `slideReady` twists, algebraic fractions agree (forward
invariance, via `colorFrom`) and equal fractions give isotopic diagrams
(reconstruction). The forward direction rests on [the coloring-ready
invariance assembly](fraction-isotopy-invariant.md); the converse on
[the same-fraction results](same-fraction-isotopic.md) for
`noMulTop`/`rightBottom` parses.

Beyond the fragment: full `Isotopic` invariance in either direction is
not claimed. Unrestricted `flype_slide_*` and the switch-based
generators are unproved, and several transports are refuted outright —
matrix-preserving mirror transport ([mirror refutation](../coloring-mirror-cong-slideReady.md)),
invert transport on two crossings ([invert refutation](../slideReady/f7-invert-mirror.md)),
and the diagonal rule without port hypotheses ([diagonal sharpness](../standard-values/s1-diagonal.md)).
So this node is not yet marked proved.

Note 2 then records the bijection: if $T=[[a_1],\ldots,[a_n]]$ and
$p/q=[a_1,\ldots,a_n]$, one may write $T=[p/q]$ without ambiguity. Rational
numbers (together with $\infty$) are thus represented bijectively by rational
tangles; negatives correspond to mirrors and inverses to inverses. That
bijection is a corollary of this theorem, not a separate first-milestone
target.

## Sources

- [Kauffman–Lambropoulou Theorem 1](../../../../sources/kauffman-lambropoulou.md#theorem-1)
- [Conway 1970](../../../../sources/conway.md)

## Depends on

- [The fraction is an isotopy invariant](fraction-isotopy-invariant.md)
- [Same fraction implies isotopic](same-fraction-isotopic.md)
