---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.twist_same_fraction_isotopic RationalTangles.twist_same_fraction_isotopic_of_noMulTop RationalTangles.twist_same_fraction_isotopic_of_rightBottom RationalTangles.IsTwistForm.fraction_unique RationalTangles.IsTwistForm.toStandard_fraction_unique RationalTangles.standard_same_CFValue_isotopic RationalTangles.TwistExpr.isotopic_canonicalCF RationalTangles.TwistExpr.toNoMulTop RationalTangles.TwistExpr.toNoMulTop_noMulTop RationalTangles.TwistExpr.toNoMulTop_isotopic RationalTangles.TwistExpr.toNoMulTop_toStandard_fraction RationalTangles.TwistExpr.exists_noMulTop_isotopic RationalTangles.IsTwistForm.exists_unique_fraction_rightBottom RationalTangles.IsTwistForm.same_fraction_isotopic_rightBottom RationalTangles.IsTwistForm.exists_unique_fraction_noMulTop RationalTangles.IsTwistForm.same_fraction_isotopic_noMulTop
---

# Same fraction implies isotopic

Two rational tangles with the same fraction are isotopic.

Let $T=[[a_1],\ldots,[a_n]]$ and $S=[[b_1],\ldots,[b_m]]$ satisfy
$F(T)=F(S)=p/q$. Bring each to canonical form $T'$ and $S'$. Invariance of
$F$ gives $F(T')=F(S')=p/q$. Proposition 3 supplies a unique arithmetic
canonical expansion $p/q=[\gamma_1,\ldots,\gamma_r]$, hence a unique
alternating rational tangle
$Q=[[\gamma_1],\ldots,[\gamma_r]]$ in canonical form. If $T'\neq Q$ then two
distinct canonical continued fractions would evaluate to $p/q$, contradicting
Proposition 3. Thus $T'=Q=S'$, so $T\sim S$.

## Formalization status

Formalized for twist-form expressions whose fraction agrees with the
standard-form evaluation: unconditionally on `noMulTop` (hence on
`rightBottom`) expressions, and conditionally in general
(`twist_same_fraction_isotopic` records the exact hypotheses). Diagram-level
uniqueness of the standard-form value holds for right-and-bottom parses of
one PD-code. Diagram-level elimination of top products is now proved:
`toNoMulTop` isotopes any twist diagram to a `noMulTop` one
(`toNoMulTop_isotopic` via `flype_mul` + `isotopic_rot180`) preserving the
standard-form fraction (`toNoMulTop_toStandard_fraction`). What remains
outstanding for the unrestricted `mulTop` case is algebraic
`TwistExpr.fraction` preservation in general — the commutativity
hypothesis is now discharged when the inner fraction is `±1`
(`mulTop_comm_of_unit_fraction`, claimed with the twist-diagram
fraction results) — and coloring transport along the
normalization path, so this node is not yet marked proved. The
boundary is now sharp, not merely outstanding: the agreement
hypotheses are necessary in general, since a `mulTop` node over
inner fraction `2` has algebraic `F = 1/3` against standard-form
`2/3` (see [the fixed-point sharpness](../forms/mulTop-fixed-points.md)).

On right-and-bottom parses the fraction is a function of the PD-code
(`exists_unique_fraction_rightBottom`, relationally, so no choice
principle), and same fraction implies isotopic at diagram level for
rightBottom-parseable diagrams (`same_fraction_isotopic_rightBottom`).
The same holds on `noMulTop` `slideReady` parses
(`exists_unique_fraction_noMulTop`, `same_fraction_isotopic_noMulTop`;
the `colorFrom` discharge needs `slideReady`, while isotopy needs only
`noMulTop`). Arbitrary parses and arbitrary rational diagrams remain
outstanding.

## Sources

- [Kauffman–Lambropoulou Theorem 3](../../../../sources/kauffman-lambropoulou.md#theorem-3)

## Depends on

- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
- [Canonical form of a rational tangle](../../definitions/canonical-form.md)
- [Unique canonical continued fraction](../forms/continued-fraction-canonical.md)

## Proof depends on

- [The fraction is an isotopy invariant](fraction-isotopy-invariant.md)
- [Every rational tangle isotopes to canonical form](../forms/canonical-form-exists.md)
