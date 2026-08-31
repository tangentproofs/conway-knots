---
declaration: theorem
origin: cited
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

## Sources

- [Kauffman–Lambropoulou Theorem 3](../../../sources/kauffman-lambropoulou.md#theorem-3)

## Depends on

- [Fraction of a rational tangle](../definitions/tangle-fraction.md)
- [Canonical form of a rational tangle](../definitions/canonical-form.md)
- [Unique canonical continued fraction](continued-fraction-canonical.md)

## Proof depends on

- [The fraction is an isotopy invariant](fraction-isotopy-invariant.md)
- [Every rational tangle isotopes to canonical form](canonical-form-exists.md)
