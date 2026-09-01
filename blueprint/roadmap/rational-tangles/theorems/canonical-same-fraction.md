---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.canonical_tangle_eq_of_value RationalTangles.canonical_tangle_isotopic_of_value RationalTangles.StandardExpr.isotopic_canonicalCF RationalTangles.standard_same_fraction_isotopic
proof: formalized
---

# Canonical diagrams of equal fraction are equal

Two tangles already in *canonical* continued-fraction form with the same
arithmetic value are the same diagram: uniqueness of the odd-length one-sign
expansion (Proposition 3) supplies a unique `canonicalCF q`, so both diagrams
are `(canonicalCF q).tangle` and hence isotopic. The remaining canonical
form of value $\infty$ is $[\infty]$.

A standard-form expression with finite fraction $q$ isotopes to that unique
diagram. The reduction is the transfer / last-term rewrite of Proposition 2,
shown to preserve the arithmetic value, so the resulting canonical expansion
is `canonicalCF q` rather than an unspecified alternating tangle. Two standard
forms of the same finite fraction are therefore isotopic (and likewise for
value $\infty$).

This is strictly smaller than Theorem 3: it does not apply to an arbitrary
rational tangle, and it does not claim that $F$ is invariant under leftover
`Isotopic` generators.

## Sources

- [Kauffman–Lambropoulou Proposition 3](../../../sources/kauffman-lambropoulou.md#proposition-3)
- [Kauffman–Lambropoulou Proposition 2](../../../sources/kauffman-lambropoulou.md#proposition-2)

## Depends on

- [Canonical form of a rational tangle](../definitions/canonical-form.md)
- [Fraction of a rational tangle](../definitions/tangle-fraction.md)
- [Standard form](../definitions/standard-form.md)
- [Unique canonical continued fraction](continued-fraction-canonical.md)

## Proof depends on

- [Every rational tangle isotopes to canonical form](canonical-form-exists.md)
- [Every rational tangle has a continued fraction form](continued-fraction-form-exists.md)
