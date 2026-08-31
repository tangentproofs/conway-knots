---
declaration: theorem
origin: cited
---

# Coloring fraction of a rational tangle

Let $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ be a color matrix for an
integrally colored tangle $T$. Then:

1. $M$ satisfies the diagonal sum rule $a+d=b+c$.
2. If $T$ is rational, then $f(T):=(b-a)/(b-d)$ is a topological invariant
   associated with $T$.
3. $f(T+S)=f(T)+f(S)$ when an integral coloring of $T+S$ is given, with the
   colorings of $T$ and $S$ the restrictions of that coloring.
4. $f(-1/T)=-1/f(T)$ for any integrally colored 2-tangle $T$ satisfying the
   diagonal sum rule.
5. $f(-T)=-f(T)$ for any rational tangle $T$. Hence
6. $f(1/T)=1/f(T)$ for any rational tangle $T$.
7. $f(T)=F(T)$ for any rational tangle $T$.

Thus the coloring fraction is identical to the arithmetical fraction
$F(T)$ of Definition 8.

This is Theorem 4 of Kauffman–Lambropoulou §5. The topological invariance in
(2) uses the Reidemeister and flype coloring lemmas (external strand colors
can be preserved) together with affine freedom (so $f$ is independent of the
choice of integral coloring). There is no appeal to Tait.

Sketch, following the paper. Colorings of $[0]$ and $[1]$ give
$f([0])=0/1$, $f([\infty])=1/0$, $f([1])=1$, so (7) follows from (3), (5)
and induction on twist form. For (1), the matrices of $[0]$ and $[\infty]$
have two equal rows or two equal columns; if $T$ has matrix $M$ satisfying
the rule, then $T+[1]$ has matrix $\begin{pmatrix}a&2b-d\\c&b\end{pmatrix}$,
and $a+b=(2b-d)+c$ is equivalent to $a+d=b+c$. The same holds for a
negative twist and for a twist on the left, bottom, or top. For (2), $f$ is
unchanged by $M\mapsto nM+k$ with $n\neq 0$, and for a fixed coloring the
external colors (hence $f$) survive Reidemeister moves and flypes. For (3),
the right column of $M(T)$ equals the left column of $M(S)$, and the
diagonal sum for $S$ gives $b-d=e-f$, whence
$f(T)+f(S)=(b-a)/(b-d)+(e-b)/(e-f)=(e-a)/(e-f)=f(T+S)$. For (4),
$M(-1/T)=M(T^r)=\begin{pmatrix}b&d\\a&c\end{pmatrix}$, so
$f(-1/T)=(d-b)/(d-c)=-1/f(T)$. For (5), the vertical reflect
$T':=(-T)^{v\mathrm{flip}}$ inherits a coloring with matrix
$\begin{pmatrix}b&a\\d&c\end{pmatrix}$, hence $f(T')=-f(T)$, and
$T'\sim -T$ by the flipping lemma. Property (6) is (4) and (5).

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../definitions/coloring-fraction.md)
- [Color matrix](../definitions/color-matrix.md)
- [Rational tangle](../../definitions/rational-tangle.md)
- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)

## Proof depends on

- [Affine freedom of coloring](coloring-affine.md)
- [Every rational tangle is integrally colorable](integral-colorability.md)
- [Coloring invariance under Reidemeister I](coloring-reidemeister-i.md)
- [Coloring invariance under Reidemeister II](coloring-reidemeister-ii.md)
- [Coloring invariance under Reidemeister III](coloring-reidemeister-iii.md)
- [Coloring invariance under flypes](coloring-flype-invariance.md)
- [Flipping lemma](../../theorems/flipping-lemma.md)
- [Flip](../../definitions/flip.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
