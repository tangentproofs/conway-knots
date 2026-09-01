---
declaration: lemma
origin: cited
statement: formalized
lean: RationalTangles.flipping_lemma
---

# Flipping lemma

If $T$ is rational, then (Kauffman–Lambropoulou Lemma 2)
$$
T\sim T^{h\mathrm{flip}},
\qquad
T\sim T^{v\mathrm{flip}},
\qquad
T\sim (T^i)^i=(T^r)^r.
$$
In particular inversion is an operation of order two on rational tangles, so
the inverse of a rational tangle $T$ may be written $T^{-1}$, and
$T^r=-T^{-1}$.

The Lean theorem currently proves the **coloring-honest** fragment: planar
$T^{\mathrm{rot}180}\sim T$ (signs kept) and therefore
$T\sim(T^i)^i=(T^r)^r$, together with commutativity of adjoining $[\pm 1]$
via the sign-preserving flype slide. Horizontal/vertical flip are spatial
diagram operations (`Crossing.switch`) and are **not** `Isotopic`
generators, so $T\sim T^{h\mathrm{flip}}$ and $T\sim T^{v\mathrm{flip}}$
are not obtained as constructors of diagram isotopy.

## Sources

- [Kauffman–Lambropoulou Lemma 2](../../../sources/kauffman-lambropoulou.md#lemma-2)

## Depends on

- [Rational tangle](../definitions/rational-tangle.md)
- [Flype](../definitions/flype.md)
- [Flip](../definitions/flip.md)
