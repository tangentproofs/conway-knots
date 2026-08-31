---
declaration: def
origin: cited
---

# Continued fraction form

A **continued fraction in integer tangles** is an algebraic description of a
rational tangle via a continued fraction built from integer tangles
$[a_1],\ldots,[a_n]$ with all numerators equal to $1$:
$$
T = [[a_1],[a_2],\ldots,[a_n]]
:= [a_1] + \cfrac{1}{[a_2]+\cdots+\cfrac{1}{[a_n]}}
$$
for $a_2,\ldots,a_n\in\mathbb{Z}\setminus\{0\}$ and $n$ even or odd. The
leading term $a_1$ may be zero. A rational tangle so described is in
**continued fraction form**.

This is the tangle-level counterpart of the arithmetic continued fraction
$[a_1,\ldots,a_n]$. Lemma 5 of the paper records the effect of adding
$[\pm 1]$, inverting, and mirroring on the continued-fraction vector.

## Sources

- [Kauffman–Lambropoulou Definition 5](../../../sources/kauffman-lambropoulou.md#definition-5)

## Depends on

- [Standard form](standard-form.md)
- [Integer and vertical tangles](integer-tangle.md)
