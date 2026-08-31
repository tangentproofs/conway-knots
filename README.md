# Rational tangles

A Lean 4 + Autoform project whose first milestone is Conway's classification
of rational tangles:

> Two rational tangles are isotopic if and only if they have the same fraction.

**Origin.** J.H. Conway, “An Enumeration of Knots and Some of Their Algebraic
Properties”, in Leech (ed.), *Computational Problems in Abstract Algebra*,
Pergamon, 1970, pp. 329–358. Cited only; the 1970 PDF is not in this
repository.

**Working source.** Louis H. Kauffman and Sofia Lambropoulou, “On the
classification of rational tangles”, *Adv. Appl. Math.* **33** (2004) 199–237,
[arXiv:math/0311499](https://arxiv.org/abs/math/0311499). The adopted PDF is
at `blueprint/sources/kauffman-lambropoulou-2004.pdf`.

**Blueprint:** [Browse the formalization blueprint](blueprint/README.md).

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).

- `lean-toolchain` and `lakefile.toml` pin Lean and Mathlib `v4.32.2`.
  Lean/elan are not installed in this workspace; do not run `lake update`
  or `lake build` until a toolchain is available.
- The Conway 1970 knot/link census is out of scope for this milestone.
- Classification is proved via the integral coloring of Kauffman–Lambropoulou
  §5 (Theorem 4), not via Tait flyping.
