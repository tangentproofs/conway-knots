---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.continued_fraction_form_exists
proof: formalized
---

# Every rational tangle has a continued fraction form

Every rational tangle can be written in continued fraction form.

The argument reduces to standard form (Lemma 3) and then applies the
isotopy identities of Lemma 4,
$$
T\ast[n]^{-1} \;\sim\; \bigl([n]+T^{-1}\bigr)^{-1},
$$
repeatedly, converting a standard-form tangle into
$[[a_1],\ldots,[a_n]]$. Thus continued-fraction form and standard form are
equivalent presentations.

## Sources

- [Kauffman–Lambropoulou Proposition 1](../../../sources/kauffman-lambropoulou.md#proposition-1)

## Depends on

- [Continued fraction form](../definitions/continued-fraction-form.md)

## Proof depends on

- [Every rational tangle has a standard form](standard-form-exists.md)
