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

- `lean-toolchain` and `lakefile.toml` pin Lean and Mathlib `v4.35.0-rc1`.
  Prefer `lake exe cache get` before building Mathlib targets.
- Classification is proved via the integral coloring of Kauffman–Lambropoulou
  §5 (Theorem 4), not via Tait flyping.

## Knot enumeration (Conway census fragment)

Executable `enumerate_knots` lists **rational** (2-bridge) prime knots by
Conway continued-fraction notation up to a chosen crossing bound:

```sh
lake build enumerate_knots
lake exe enumerate_knots -- 7
lake exe enumerate_knots -- 8 --check
```

Through 7 crossings this matches the full prime-knot census (all such knots
are rational). From 8 crossings it matches the 2-bridge counts only; basic
polyhedra and non-rational algebraic knots are not yet enumerated. See
`src/ConwayEnumeration/RationalKnot.lean` for method and gaps.

The enumerator does not import Mathlib or `RationalTangles`. Default
`lake build` builds `enumerate_knots` only. Theorem-track:
`lake exe cache get && lake build RationalTangles`.
