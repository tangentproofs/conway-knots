---
declaration: def
origin: cited
statement: formalized
lean: RationalTangles.Flype
---

# Flype

A **flype** is an isotopy of a 2-tangle or a knot applied on a 2-subtangle of
the form $[\pm 1]+t$ or $[\pm 1]\ast t$ as in Figure 5 of the paper. It fixes
the endpoints of the subtangle on which it is applied. A flype is **rational**
if that 2-subtangle is rational.

Algebraically (after the flipping lemma), a rational flype is one of
$$
[\pm 1]+t \;\sim\; t+[\pm 1]
\qquad\text{or}\qquad
[\pm 1]\ast t \;\sim\; t\ast[\pm 1].
$$

A tangle (or knot) diagram is **alternating** when the crossings alternate
from under to over along every arc; equivalently, with the paper's
checkerboard shading, when all crossings have the same type. Flypes preserve
the alternating structure. Lemma 1 and Corollary 1 of the paper record that
every 2-subtangle of a rational tangle in twist form is a rational truncation,
so every flype of a rational tangle is rational.

## Sources

- [Kauffman–Lambropoulou Definition 2](../../../sources/kauffman-lambropoulou.md#definition-2)

## Depends on

- [2-tangle and isotopy](two-tangle-isotopy.md)
- [Integer and vertical tangles](integer-tangle.md)
