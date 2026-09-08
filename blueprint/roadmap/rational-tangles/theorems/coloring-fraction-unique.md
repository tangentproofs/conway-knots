---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_unique_slideReady RationalTangles.coloring_fraction_unique_rightBottom
proof: formalized
---

# Uniqueness of the coloring fraction on larger honest classes

On a `slideReady` twist diagram every non-monochrome integral coloring has
coloring fraction equal to the standard-form value, so any two agree. On a
right-and-bottom twist the same uniqueness holds with value equal to the
arithmetical fraction of the expression (the diagonal-sum rule is
discharged).

On `addLeft` (resp. `mulTop`) of a right-and-bottom inner expression, with
the same non-degenerate glue used to color those constructors
($NW \neq SW$ / $NW \neq NE$), every non-monochrome coloring has
fraction equal to the arithmetical value (resp. the standard-form value:
top Conway product need not equal algebraic `mulTop.fraction`). Affine
uniqueness of `colorFrom` extends to those constructors, so the
`colorFrom` family shares that value. Uniqueness of arbitrary colorings
without the port hypotheses is not claimed: `DiagonalSum`/`slideReady`
need distinct glue ports.

If a diagram is related by `ColoringIsotopy` *to* a `slideReady` twist
(the twist is the target), transport preserves the color matrix, hence the
coloring fraction equals that standard-form value. The reverse one-way
direction is not claimed: unrestricted dummy-strand `zero_add` and one-way
glue do not reverse. On the reversible fragment the path may be reversed,
so uniqueness holds in both directions.

On a two-block PD-sum of integer diagrams, restriction of a non-monochrome
coloring to each summand is non-monochrome (a monochrome summand would
force the other summand or the sum to be monochrome, or would force an
infinite integer fraction). Additivity of the coloring fraction then gives
the value $n+m$.

This is not uniqueness on an arbitrary diagram. A `TwistExpr` that is not
`slideReady` (including `addLeft`/`mulTop` without port hypotheses) is
omitted. Unrestricted flype-slides (no diagonal-sum or port hypotheses)
are omitted, and are not added to `ColoringIsotopy`.
This article does not claim isotopy invariance of the arithmetical
fraction.

## Split into pull-request-sized nodes

The remaining results live in:

- [Uniqueness core on honest classes](uniqueness/c1-core.md)
- [Uniqueness along isotopy transfer](uniqueness/c2-isotopy-transfer.md)
- [Uniqueness on integer-tangle sums](uniqueness/c3-integerTangle.md)
- [Existence on addLeft and mulTop](uniqueness/c4-existence.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)
- [Integer and vertical tangles](../definitions/integer-tangle.md)

## Proof depends on

- [Coloring fraction of a rational tangle](../coloring/theorems/coloring-fraction-properties.md)
- [Affine freedom of coloring](../coloring/theorems/coloring-affine.md)
- [Nested unit chains versus two-block PD-sums](../coloring/theorems/nested-two-block-reindex.md)
- [Reversible fragment of coloring isotopy](../coloring/theorems/reversible-coloring-isotopy.md)
- [Standard-form $F$ along coloring isotopy](forms/twist-coloring-isotopy-fraction.md)
