---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_add_units RationalTangles.coloring_invert_mul_units RationalTangles.coloring_invert_add_one_one RationalTangles.coloring_invert_mul_one_one RationalTangles.coloring_invert_add_zero_unit RationalTangles.coloring_invert_add_unit_zero RationalTangles.coloring_invert_mul_infinity_unit RationalTangles.coloring_invert_mul_unit_infinity RationalTangles.coloring_invert_add_zero_one RationalTangles.coloring_invert_add_one_zero RationalTangles.coloring_invert_one_add_one_eq_vertical RationalTangles.coloring_invert_one_add_one_add_one_eq_vertical
proof: formalized
---

# Coloring fraction of inverted unit sums and products

The generators `(T+S)ⁱ ∼ Sⁱ * Tⁱ` and `(T*S)ⁱ ∼ Tⁱ + Sⁱ` switch every
crossing, so a coloring of one diagram is not transported to the other.
On the elementary units `[+1]` and `[-1]`, independent fresh colorings
nonetheless have the same coloring fraction.

For signs `s,t`, a `colorFrom` coloring of the right-and-bottom sum
`[s]+[t]` is inverted to a coloring of `([s]+[t])ⁱ` with fraction
`1/(s+t)`. A `colorFrom` coloring of the right-and-bottom product
`[t]*[s]` is recolored along the coloring-ready inversion of each unit
to a coloring of `[t]ⁱ * [s]ⁱ` with the same value. The product identity
is the same comparison with the roles of sum and product exchanged.

The same comparison is honest when one summand is `[0]` (so inversion
sends it to `[∞]`) provided the glue ports are distinct: `([0]+[±1])ⁱ`
against `[±1]ⁱ * [0]ⁱ`, and `([±1]+[0])ⁱ` against `[0]ⁱ * [±1]ⁱ`.
Involving `[∞]` is restricted to products with distinct glue ports
(`[∞]*[±1]` and `[±1]*[∞]`); kinks `[∞]+[±1]` are excluded. The
PD-code of `[∞]` below a tangle is a no-op; `[∞]ⁱ` is not collapsed
to `[0]`.

On the right-and-bottom chain `[+1]+[+1]` (resp. `[+1]+[+1]+[+1]`), a
fresh invert coloring has the same fraction as `colorFrom` of the
vertical chain `[∞]*[+1]*[+1]` (resp. `[∞]*[+1]*[+1]*[+1]`). That is
the invert identity `f(Tⁱ)=1/F(T)` on these diagrams, not a
`ColoringIsotopy` between them.

This is not a `ColoringIsotopy` constructor, and it is not Theorem 2,
Theorem 3, or Theorem 4. Kinks `[∞]+[±1]` (both right ports of `[∞]` are
the same arc) are excluded.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)

## Proof depends on

- [Coloring fraction of a rational tangle](coloring-fraction-properties.md)
