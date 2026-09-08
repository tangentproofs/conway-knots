---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.theorem4_diagonal_sum RationalTangles.theorem4_diagonal_coloringIsotopy RationalTangles.diagonal_of_ColoringIsotopy_slideReady RationalTangles.diagonal_of_ReversibleColoringIsotopy_slideReady RationalTangles.diagonal_of_ReversibleColoringIsotopy_slideReady_symm RationalTangles.theorem4_additivity RationalTangles.theorem4_neg_inverse RationalTangles.theorem4_mirror_negation RationalTangles.theorem4_inverse RationalTangles.theorem4_standard_agreement RationalTangles.coloring_fraction_agreement_any_isotopy RationalTangles.theorem4_all_rational_agreement RationalTangles.theorem4_standard_coloring_exists RationalTangles.exists_coloring_fraction_reversible_slideReady RationalTangles.exists_coloring_fraction_isotopy_from_slideReady RationalTangles.theorem4_standard_uniqueness
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

## Formalization status

Parts (1) and (3)–(7) are formalized as the `theorem4_*` wrappers in
`ColoringFractionTheorem.lean`, each proved by the lemma named in its
docstring: (1) diagonal sum on standard forms, now extended to every
coloring of every diagram `ColoringIsotopy`-related to a `slideReady`
twist (`diagonal_of_ColoringIsotopy_slideReady` and the two
`ReversibleColoringIsotopy` variants in `DiagonalSumGeneral.lean`); (3)
additivity (plus the `coloring_fraction_mul` dual); (4) `-1/F` on
mirror-invert; (5) `-F` on the mirror; (6) `1/F` on the inverse;
(7) agreement/existence/uniqueness on standard forms and `slideReady`
twists, plus all-rational agreement on the coloring-ready neighborhood
(`theorem4_all_rational_agreement`: every non-monochrome coloring of a
diagram `ColoringIsotopy`-related to a `slideReady` twist has fraction
$F$) and existence there in the reversible direction (the `colorFrom`
coloring transports forward along the symmetric path;
`exists_coloring_fraction_reversible_slideReady` — one-way
`ColoringIsotopy` from the twist cannot supply source colorings, so the
reversible hypothesis is sharp — while one-way paths *toward* a diagram
do supply them (`exists_coloring_fraction_isotopy_from_slideReady`). Diagonal sum on an arbitrary rational diagram (transport along
unrestricted `flype_slide_*` or the switch-based generators, or
`addLeft`/`mulTop` without port hypotheses) remains outstanding — and
the port side is now known-sharp, not merely unproved. Part (2) is formalized
generator-by-generator (affine freedom, Reidemeister I–III, flypes,
colorability — see proof dependencies); the single-statement assembly
"for every isotopy" is not claimed, since transport along unrestricted
`flype_slide_*` and switch-based generators is outstanding. Part (7) past
the coloring-ready neighborhood — arbitrary rational diagrams related only
by a full-`Isotopic` witness, or non-`slideReady` parses — is likewise
outstanding for the same reason.

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
- [Left product by the vertical trivial tangle is planar reindexing](coloring-infinity-mul.md)
- [Nested unit chains versus two-block PD-sums](nested-two-block-reindex.md)
- [Reversible fragment of coloring isotopy](reversible-coloring-isotopy.md)
- [Flipping lemma](flipping-lemma.md)
- [Flip](../../definitions/flip.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)
