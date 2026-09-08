---
declaration: theorem
origin: cited
---

# Alternating rational tangles related by flypes

Two alternating rational tangles on $S^2$ are isotopic if and only if they
differ by a finite sequence of rational flypes.

The argument passes to the vertex closure $V(T)$ of an alternating rational
tangle, invokes the Tait flyping theorem for that closure, and reconfigures
any flype that involves the rigid vertex as a pancake flip plus a tangle
flype. Pancake flips induce horizontal or vertical flips, which the paper
treats as isotopies of rational tangles; note the formalized flipping
lemma covers only the coloring-honest fragment (planar rotation, not
$h\mathrm{flip}$/`v\mathrm{flip}` as diagram isotopies), so this step has
no Lean backing. Remaining tangle flypes are
rational by Corollary 1.

This article is retained as exposition of the unused §4 flyping argument.
It is not a dependency of Theorem 1.

## Sources

- [Kauffman–Lambropoulou Proposition 4](../../../sources/kauffman-lambropoulou.md#proposition-4)

## Depends on

- [Flype](../definitions/flype.md)
- [Rational tangle](../definitions/rational-tangle.md)

## Proof depends on

- [Tait flyping conjecture](tait-flyping.md)
- [Flipping lemma](../coloring/theorems/flipping-lemma.md)
- [Flip](../definitions/flip.md)
