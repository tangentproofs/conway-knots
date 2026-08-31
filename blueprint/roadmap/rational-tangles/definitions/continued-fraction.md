---
declaration: def
origin: cited
---

# Arithmetic continued fraction

Every rational number may be written as a continued fraction with all
numerators equal to $1$:
$$
[a_1,a_2,\ldots,a_n]
:= a_1 + \cfrac{1}{a_2+\cdots+\cfrac{1}{a_n}}
$$
for $a_1\in\mathbb{Z}$ and $a_2,\ldots,a_n\in\mathbb{Z}\setminus\{0\}$. The
leading term $a_1$ may be zero. The length is $n$ whether or not $a_1=0$.

A continued fraction is **termwise positive** (resp. negative) if every
numerical term is positive (resp. negative). It is in **canonical form**
(Definition 7) if it is termwise positive or negative and the length $m$ is
odd. Even length is reduced to odd length by the last-term identities
$[a_1,\ldots,a_n]=[a_1,\ldots,a_n-1,+1]$ for $a_n>0$ and
$[a_1,\ldots,a_n]=[a_1,\ldots,a_n+1,-1]$ for $a_n<0$.

The value $\infty$ is included formally as $1/0$, matching $F([\infty])$.

Mathlib already develops generalised, simple, and regular continued fractions
under `Algebra.ContinuedFractions` (including `GenContFract.of` and
termination iff rationality). That overlap is arithmetic, not a tangle
theory; it is recorded as a candidate, not as `mathlib: true`.

## Sources

- [Kauffman–Lambropoulou Definition 7](../../../sources/kauffman-lambropoulou.md#definition-7)

## Depends on

This node has no prerequisites.
