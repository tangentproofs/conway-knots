---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_fraction_unique_slideReady RationalTangles.coloring_fraction_unique_rightBottom RationalTangles.coloring_fraction_eq_F_of_ColoringIsotopy_slideReady RationalTangles.coloring_fraction_unique_ColoringIsotopy_slideReady RationalTangles.coloring_fraction_eq_F_of_ReversibleColoringIsotopy_slideReady RationalTangles.coloring_fraction_eq_F_of_ReversibleColoringIsotopy_slideReady_symm RationalTangles.coloring_fraction_unique_ReversibleColoringIsotopy_slideReady RationalTangles.coloring_fraction_unique_ReversibleColoringIsotopy_slideReady_symm RationalTangles.coloring_fraction_integerTangle_add RationalTangles.coloring_fraction_unique_integerTangle_add RationalTangles.coloring_exists_integerTangle_add RationalTangles.HasColoringFraction.integerTangle_add
proof: formalized
---

# Uniqueness of the coloring fraction on larger honest classes

On a `slideReady` twist diagram every non-monochrome integral coloring has
coloring fraction equal to the standard-form value, so any two agree. On a
right-and-bottom twist the same uniqueness holds with value equal to the
arithmetical fraction of the expression (the diagonal-sum rule is
discharged).

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
`slideReady` is omitted. Unrestricted flype-slides (no diagonal-sum or
port hypotheses) are omitted, and are not added to `ColoringIsotopy`.
This article does not claim isotopy invariance of the arithmetical
fraction.

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
- [Standard-form $F$ along coloring isotopy](twist-coloring-isotopy-fraction.md)
