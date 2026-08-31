---
declaration: def
origin: cited
---

# Fraction of a rational tangle

Let $T$ be a rational tangle in twist form. The **fraction** $F(T)$ is the
rational number (or $\infty$) obtained by evaluating that expression in
ordinary arithmetic, with the tangle product interpreted as
$$
x\ast y := \frac{1}{\frac{1}{x}+y},
$$
and with $F([\infty]):=\infty=1/0$ as a formal expression (Definition 8).

By Remark 6, if $T=[[a_1],\ldots,[a_n]]$ is in continued fraction form then
$$
F(T)=[a_1,a_2,\ldots,a_n],
$$
and this evaluation may be taken as the definition of $F(T)$. In particular
$F([0])=0$, $F([\pm 1])=\pm 1$, $F([\pm k])=\pm k$, and
$F([{\pm k}]^{-1})=1/(\pm k)$.

Lemma 7 of the paper shows that the twist-form and continued-fraction-form
evaluations agree. Lemma 8 records the calculus
$F(T+[\pm 1])=F(T)\pm 1$, $F(T^{-1})=1/F(T)$, $F(-T)=-F(T)$.

## Sources

- [Kauffman–Lambropoulou Definition 8](../../../sources/kauffman-lambropoulou.md#definition-8)

## Depends on

- [Rational tangle](rational-tangle.md)
- [Continued fraction form](continued-fraction-form.md)
- [Arithmetic continued fraction](continued-fraction.md)
