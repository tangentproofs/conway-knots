---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.standard_same_CFValue_isotopic RationalTangles.twist_same_toStandard_fraction_isotopic RationalTangles.twist_same_fraction_isotopic RationalTangles.twist_same_fraction_isotopic_of_noMulTop RationalTangles.TwistExpr.isotopic_canonicalCF
proof: formalized
---

# Twist expressions of equal fraction are isotopic

Two *twist-form expressions* with the same arithmetical fraction $F$ have
isotopic diagrams, provided each expression's $F$ agrees with the
right-and-bottom evaluation of `toStandard`.

The diagrams first isotope to standard form by the slides already in
`toStandard_isotopic` (horizontal and vertical rational flypes, including
left addition and top multiplication). Standard forms of a given finite
value (or of $\infty$) then isotope to one another by uniqueness of the
canonical continued fraction. Algebraic $F$ equals that standard-form
value on every expression that never uses a top product: addition is
commutative, so left addition is allowed, while the Conway product is
not commutative.

This is strictly smaller than Theorem 3. It does not apply to an arbitrary
rational diagram (an `Isotopic` witness of `IsRational`), and it does not
claim that $F$ is well-defined along leftover `Isotopic` generators.

## Sources

- [Kauffman–Lambropoulou Theorem 3](../../../sources/kauffman-lambropoulou.md#theorem-3)
- [Kauffman–Lambropoulou Proposition 3](../../../sources/kauffman-lambropoulou.md#proposition-3)
- [Kauffman–Lambropoulou Lemma 3](../../../sources/kauffman-lambropoulou.md#lemma-3)

## Depends on

- [Fraction of a rational tangle](../definitions/tangle-fraction.md)
- [Standard form](../definitions/standard-form.md)
- [Canonical form of a rational tangle](../definitions/canonical-form.md)

## Proof depends on

- [Canonical diagrams of equal fraction are equal](canonical-same-fraction.md)
- [Every rational tangle has a standard form](standard-form-exists.md)
