---
kind: source
status: adopted
---

# Kauffman–Lambropoulou 2004

Louis H. Kauffman and Sofia Lambropoulou, *On the classification of rational
tangles*, Adv. Appl. Math. **33** (2004) 199–237.
Stable public record: [arXiv:math/0311499](https://arxiv.org/abs/math/0311499)
(v2, 12 Jan 2004). Local PDF: [`kauffman-lambropoulou-2004.pdf`](kauffman-lambropoulou-2004.pdf).

This is the adopted working source for the first milestone. Locations below
are theorem/definition numbers in that paper, with the corresponding page of
the arXiv PDF (the journal pagination is 199–237).

## Source map

| Blueprint target | Paper locator | arXiv PDF |
| --- | --- | --- |
| Reidemeister moves | Introduction (diagram isotopy by Reidemeister moves [31]); §5 coloring invariance | pp. 2, 34 |
| 2-tangle and isotopy | Introduction, pp. 1–2 (homeomorphism of pairs; isotopy $T\sim S$) | pp. 1–2 |
| Integer and vertical tangles | §2, opening of “The Canonical Form of Rational Tangles”; Figure 2 | p. 5 |
| Rational tangle (twist form) | Definition 1; Note 1 (equivalence with the introductory homeomorphism definition) | pp. 7–8 |
| Flype | Definition 2; alternating diagrams immediately after | pp. 8–9 |
| Flip | Definition 3 | p. 10 |
| Flipping lemma | Lemma 2 | p. 11 |
| Standard form | Definition 4 | p. 12 |
| Existence of standard form | Lemma 3 | p. 15 |
| Continued fraction form of a tangle | Definition 5 | p. 16 |
| Existence of continued fraction form | Proposition 1 | p. 17 |
| Canonical form of a rational tangle | Definition 6 | p. 18 |
| Existence of canonical form | Proposition 2 | pp. 18–20 |
| Arithmetic continued fraction | §3 opening; $[a_1,\ldots,a_n]$; Definition 7 | pp. 21–22 |
| Unique canonical continued fraction | Proposition 3 | pp. 22–23 |
| Fraction of a rational tangle | Definition 8; Remark 6 | pp. 26–27 |
| Coloring rule | §5 opening; Figure 20; $\alpha+\gamma=2\beta$ | pp. 34–35 |
| Integral colorability | §5, after Figure 20 | p. 35 |
| Color matrix | §5, $M(T)$ of NW, NE, SW, SE | p. 36 |
| Affine freedom of coloring | §5, $M\mapsto nM+k$ | p. 36 |
| Coloring Reidemeister and flype invariance | §5, “easy to verify” paragraph | p. 34 |
| Coloring fraction / Theorem 4 | Theorem 4 | pp. 36–38 |
| Tait flyping conjecture | §2, “The Tait Conjecture for Knots”; used in Proposition 4; unused in this DAG | p. 9 |
| Alternating tangles related by flypes | Proposition 4; unused in this DAG | pp. 29–31 |
| Fraction is an isotopy invariant | Theorem 2, via Theorem 4 rather than Proposition 4 | pp. 31–32, 34–38 |
| Same fraction implies isotopic | Theorem 3 | p. 32 |
| Classification | Theorem 1 (Conway, 1970) = Theorem 2 + Theorem 3, with Theorem 2 from §5 | pp. 3, 32, 34 |

Labels locate the authoritative statements; the node summaries are planning
notes and must not replace source inspection.

## Theorem 1 {#theorem-1}

Quoted from the Introduction (arXiv PDF p. 3):

> **Theorem 1 (Conway, 1970)** Two rational tangles are isotopic if and only
> if they have the same fraction.

Conway defined the fraction from the continued-fraction form of the tangle.
The paper proves Theorem 1 in §4 as Theorem 2 plus Theorem 3, and again
in §5 by obtaining Theorem 2 from the coloring fraction (Theorem 4) so as
to eliminate Tait. This DAG uses the §5 route: Theorem 2 from Theorem 4,
Theorem 3 from §4, and Theorem 1 as their conjunction.

## Definition 1 {#definition-1}

§2, arXiv PDF p. 7:

> **Definition 1** A rational tangle is in twist form if it is created by
> consecutive additions and multiplications by the tangles $[\pm 1]$, starting
> from the tangle $[0]$ or the tangle $[\infty]$.

Note 1 (p. 8) records the equivalence with the introductory definition: a
proper embedding of two unoriented arcs in a 3-ball that is homeomorphic to a
trivial tangle $(D^2\times I,\{x,y\}\times I)$.

## Definition 2 {#definition-2}

§2, arXiv PDF p. 8:

> **Definition 2** A flype is an isotopy of a 2-tangle/a knot applied on a
> 2-subtangle of the form $[\pm 1]+t$ or $[\pm 1]\ast t$ as illustrated in
> Figure 5. A flype fixes the endpoints of the subtangle on which it is
> applied. A flype shall be called rational if the 2-subtangle on which it
> acts is rational.

## Definition 3 {#definition-3}

§2, arXiv PDF p. 10:

> **Definition 3** A flip is a rotation in space of a 2-tangle by $180^\circ$.
> We say that $T^{h\mathrm{flip}}$ is the horizontal flip of the 2-tangle $T$
> if $T^{h\mathrm{flip}}$ is obtained from $T$ by a $180^\circ$-rotation
> around a horizontal axis on the plane of $T$, and $T^{v\mathrm{flip}}$ is
> the vertical flip of the tangle $T$ if $T^{v\mathrm{flip}}$ is obtained
> from $T$ by a $180^\circ$-rotation around a vertical axis on the plane of
> $T$.

## Lemma 2 {#lemma-2}

§2, arXiv PDF p. 11:

> **Lemma 2 (Flipping Lemma)** If $T$ is rational, then:
> (i) $T\sim T^{h\mathrm{flip}}$, (ii) $T\sim T^{v\mathrm{flip}}$ and
> (iii) $T\sim (T^i)^i=(T^r)^r$.

## Definition 4 {#definition-4}

§2, arXiv PDF p. 12:

> **Definition 4** A rational tangle is said to be in standard form if it is
> created by consecutive additions of the tangles $[\pm 1]$ only on the right
> (or only on the left) and multiplications by the tangles $[\pm 1]$ only at
> the bottom (or only at the top), starting from the tangle $[0]$ or
> $[\infty]$.

## Lemma 3 {#lemma-3}

§2, arXiv PDF p. 15:

> **Lemma 3** Every rational tangle can be brought via isotopy to standard
> form.

## Definition 5 {#definition-5}

§2, arXiv PDF p. 16:

> **Definition 5** A continued fraction in integer tangles is an algebraic
> description of a rational tangle via a continued fraction built from the
> tangles $[a_1],[a_2],\ldots,[a_n]$ with all numerators equal to 1.

A tangle so described is said to be in continued fraction form.

## Proposition 1 {#proposition-1}

§2, arXiv PDF p. 17:

> **Proposition 1** Every rational tangle can be written in continued fraction
> form.

## Definition 6 {#definition-6}

§2, arXiv PDF p. 18:

> **Definition 6** A rational tangle $T=[[\beta_1],[\beta_2],\ldots,[\beta_m]]$
> is in canonical form if $T$ is alternating and $m$ is odd.

## Proposition 2 {#proposition-2}

§2, arXiv PDF p. 18:

> **Proposition 2** Every rational tangle can be isotoped to canonical form.

## Definition 7 {#definition-7}

§3, arXiv PDF p. 22:

> **Definition 7** A continued fraction $[\beta_1,\beta_2,\ldots,\beta_m]$ is
> said to be in canonical form if it is termwise positive or negative and $m$
> is odd.

The arithmetic continued-fraction notation $[a_1,\ldots,a_n]$ is introduced at
the opening of §3 (p. 21).

## Proposition 3 {#proposition-3}

§3, arXiv PDF p. 22:

> **Proposition 3** Every continued fraction $[a_1,a_2,\ldots,a_n]$ can be
> transformed to a unique canonical form with sign generically equal to the
> sign of the first non-zero term.

Uniqueness is referred to Euclid's algorithm at the end of the proof (p. 23).

## Definition 8 {#definition-8}

§4, arXiv PDF p. 26–27:

> **Definition 8** We define the fraction of $T$, $F(T)$, to be the rational
> number obtained by evaluating the twist-form expression of $T$ in ordinary
> arithmetic, with $x\ast y:=1/(1/x+y)$, and $F([\infty]):=\infty=1/0$ as a
> formal expression.

Remark 6 (p. 27) records the equivalent continued-fraction evaluation:
if $T=[[a_1],\ldots,[a_n]]$ then $F(T)=[a_1,\ldots,a_n]$.

## The Tait conjecture {#tait}

§2, arXiv PDF p. 9, quoted as used:

> **The Tait Conjecture for Knots.** Two alternating knots are isotopic if
> and only if any two corresponding diagrams on $S^2$ are related by a finite
> sequence of flypes.

Proved by Menasco and Thistlethwaite (1993); assumed for vertex closures of
alternating 2-tangles in the proof of Proposition 4.

## Proposition 4 {#proposition-4}

§4, arXiv PDF p. 29:

> **Proposition 4** Two alternating rational tangles on $S^2$ are isotopic if
> and only if they differ by a finite sequence of rational flypes.

## Theorem 2 {#theorem-2}

§4, arXiv PDF p. 32:

> **Theorem 2** The fraction is an isotopy invariant of rational tangles.

The §4 proof uses Lemma 3, Proposition 1, Lemma 7, Proposition 2, Lemma 10,
Proposition 4, and Lemma 11 (flypes preserve the fraction). This DAG does
not use that argument. Section 5 obtains the same statement from Theorem 4:
$f$ is a topological invariant and $f=F$, so $F$ is an isotopy invariant.

## Theorem 3 {#theorem-3}

§4, arXiv PDF p. 32:

> **Theorem 3** Two rational tangles with the same fraction are isotopic.

## Reidemeister moves {#reidemeister-moves}

Introduction, arXiv PDF p. 2:

> Equivalently, $T,S$ are isotopic if and only if any two diagrams of theirs
> (i.e. seeing the tangles as planar graphs) have identical configurations
> of their four endpoints on the boundary of the projection disc, and they
> differ by a finite sequence of the well-known Reidemeister moves [31],
> which take place in the interior of the disc.

The three local pictures R1, R2, R3 are not drawn in the paper; they are
bridged as formalizable leaves from this usage and from the §5 coloring
invariance paragraph.

## Coloring rule {#coloring-rule}

§5, arXiv PDF p. 34:

> We shall use colors from either $\mathbb{Z}$ or from $\mathbb{Z}/n\mathbb{Z}$
> for some $n$. The coloring rule is that if two undercrossing arcs colored
> $\alpha$ and $\gamma$ meet at an overcrossing arc colored $\beta$, then
> $\alpha+\gamma=2\beta$. See Figure 20. We often think of one of the
> undercrossing arc colors as determined by the other one and the color of
> the overcrossing arc. Then one writes $\gamma=2\beta-\alpha$.

## Coloring Reidemeister invariance {#coloring-reidemeister}

§5, arXiv PDF p. 34:

> It is easy to verify that this coloring method is invariant under the
> Reidemeister moves in the following sense: Given a choice of coloring for
> the tangle (knot), there is a way to re-color it each time a Reidemeister
> move (or a flype) is performed, so that no change occurs to the colors on
> the external strands of the tangle (so that we still have a valid
> coloring).

The paper does not write the diagram chases. They are formalizable lemmas
in this DAG, not axioms.

## Integral colorability {#integral-colorability}

§5, arXiv PDF p. 35:

> When there exists a coloring of a tangle by integers, so that it is not
> necessary to reduce the colors over some modulus we shall say that the
> tangle is integrally colorable. It turns out that every rational tangle is
> integrally colorable: Choose two colors for the initial strands (e.g. the
> colors 0 and 1) and color the rational tangle as you create it by
> successive twisting. We call the colors on the initial strands the
> starting colors.

## Color matrix {#color-matrix}

§5, arXiv PDF p. 36:

> Let $\mathrm{NW}(T)$, $\mathrm{NE}(T)$, $\mathrm{SW}(T)$ and
> $\mathrm{SE}(T)$ denote these respective colors of the colored tangle $T$
> and define the color matrix of $T$, $M(T)$, by the equation
> $$
> M(T)=\begin{pmatrix}\mathrm{NW}(T)&\mathrm{NE}(T)\\\mathrm{SW}(T)&\mathrm{SE}(T)\end{pmatrix}.
> $$
> Letting $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ be a given color matrix we
> see at once [...] that
> $$
> M'=\begin{pmatrix}na+k&nb+k\\nc+k&nd+k\end{pmatrix}
> $$
> will also be a color matrix for the given tangle.

## Theorem 4 {#theorem-4}

§5, arXiv PDF pp. 36–37. The displayed fractions in the PDF extract as
stacked glyphs; the identities are those used in the proof on pp. 37–38.

> **Theorem 4** Let $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ be a color
> matrix for an integrally colored tangle $T$. Then
>
> 1. $M$ satisfies the ‘diagonal sum rule’: $a+d=b+c$.
> 2. If $T$ is rational, then the quantity $f(T):=(b-a)/(b-d)$ is a
>    topological invariant associated with the tangle $T$.
> 3. $f(T+S)=f(T)+f(S)$, when there is given an integral coloring of a
>    tangle $T+S$. The colorings of $T$ and $S$ are the restrictions of the
>    coloring of $T+S$ to these subtangles.
> 4. $f(-1/T)=-1/f(T)$ for any integrally colored 2-tangle $T$ satisfying
>    the diagonal sum rule.
> 5. $f(-T)=-f(T)$ for any rational tangle $T$. Hence,
> 6. $f(1/T)=1/f(T)$ for any rational tangle $T$.
> 7. $f(T)=F(T)$ for any rational tangle $T$.
>
> Thus the coloring fraction is identical to the arithmetical fraction
> defined earlier.

## Out of first-milestone scope

Section 6 (generating operations and history), the remainder of §5 after
Theorem 4 (Theorem 5, the Kauffman–Harary coloring conjecture, open
integrally colorable tangles), the infinite and imaginary tangles at the end
of §3, Corollary 2 (rational knots are alternating) as a knot-theoretic
consequence, the Tait/Proposition 4 proof of Theorem 2, and the sequel
classification of rational knots, are recorded on the
[coverage page](../coverage/README.md) rather than as part of the
classification path.
