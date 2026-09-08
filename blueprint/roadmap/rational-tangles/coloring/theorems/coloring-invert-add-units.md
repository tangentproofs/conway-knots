---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.coloring_invert_add_integerUnits_integerUnits
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

The same comparison holds for every integer tangle `[n]`: a fresh
coloring of `(integerTangle n)ⁱ` has fraction `1/n`, matching
`colorFrom` of `|n|` vertical twists of the sign of `n` below `[∞]`.
The twist-form builders are inductive on `natAbs`; adjoining `[±1]`
is the `[+1]+[+1]` step. This is not the PD-code
`(integerTangle n).invert` as `verticalTangle`, which mirrors.

The invert-add identity on an integer plus a unit is the same comparison:
a fresh coloring of `(integerUnits n s + [t])ⁱ` has fraction `1/(ns+t)`,
matching `colorFrom` of the vertical chain with one more bottom twist.
Matching signs recover `n+1` vertical twists, and on `[n]+[+1]` this is
`verticalTwists (n+1)`. Opposite signs cancel one unit: invert of
`integerUnits (n+1) s` plus the flipped unit matches `verticalUnits n s`,
so `(integerTangle (n+1)+[-1])ⁱ` matches `verticalTwists n` and
`(integerTangle (-(n+1))+[+1])ⁱ` matches `verticalTwists (-n)`. The
zero-length mixed seed is a remaining opposite unit. Two full integer
chains are nested right-adds (not the PD-block `integerTangle n +
integerTangle m`): invert of `appendUnits (integerUnits n s) m t` has
fraction `1/(ns+mt)`, matching `colorFrom` of the Conway product that
starts from `verticalUnits m t` and adjoins `n` bottom twists of sign
`s`. Same-sign `[n],[m] : Nat` is nested `(integerTangle n + [+1]ᵐ)ⁱ`
against `verticalTwists m` then `n` further positive twists. Mixed signs
are the flipped chain, or `[n]` plus `k` units of any sign on an `Int`
integer. The product dual inverts a vertical chain times a
unit against the integer `ns+t`. This is not PD-code
`one.invert.mul (integerTangle n).invert` (mirrors), and not a
`ColoringIsotopy`.

On a `slideReady` twist expression `e` whose right ports are distinct
(so not the kink `[∞]+[±1]`), uniqueness of `f` after invert identifies
the coloring fraction of `(e+[s])ⁱ` as `1/(F(e)+s)`. An independent
`colorMulTop` coloring of `[s]` stacked above `eⁱ`, transported along
the coloring-ready unit inversion, has the same value. The dual
compares `(e*[s])ⁱ` with `eⁱ+[s]ⁱ` via `colorAddOne`. This replaces
further integer-chain `Nat` casework. `TwistExpr` still adjoins only a
unit at a time, so two general `slideReady` summands are not expressed
as a single constructor.

This is not a `ColoringIsotopy` constructor, and it is not Theorem 2,
Theorem 3, or Theorem 4. Kinks `[∞]+[±1]` (both right ports of `[∞]` are
the same arc) are excluded.


Glue colorings of two independent `rightBottom`/`slideReady` diagrams with
finite nonzero `F` (affine matching along an `add` or `mul` seam, and the
dual identity `f(T*S)=1/(1/f(T)+1/f(S))`) color the PD-sum `T+S`. Algebraic
mirrors glue and transport along `ColoringIsotopy` to the PD-mirror of the
sum, then rotate for `(T+S)ⁱ`; invert colorings glue for `Sⁱ*Tⁱ`. The
restriction of a glue coloring is `colorAddRight` (resp. `colorMulBottom`).
`T.add S` is still not a `TwistExpr`, so this is not a `SlideReadyIsotopy`
constructor. Skip `0`/`∞`. This is not unrestricted `flype_slide`, and it is
not Theorem 2.

## Split into pull-request-sized nodes

The remaining results live in:

- [Invert-add and invert-mul of unit tangles](invert-units/a1-unit-add-mul-base.md)
- [Invert-add with a zero or unit edge](invert-units/a2-zero-unit-edges.md)
- [Invert-mul with an infinity factor](invert-units/a3-infinity-unit.md)
- [Vertical twist identifications](invert-units/a4-vertical-identifications.md)
- [Invert-add of integer chains, positive part](invert-units/a5-integer-chains-add.md)
- [Integer chains with signs and products](invert-units/a6-integer-chains-mul.md)
- [Invert-add of two integer tangles](invert-units/a7-integer-integer.md)
- [Invert-add on slideReady diagrams](invert-units/a8a-invert-add-slideReady.md)
- [Invert-mul on slideReady diagrams](invert-units/a8b-invert-mul-slideReady.md)
- [Unit top products and the invert diagonal](invert-units/a9-mulTop-one.md)
- [Color-matrix product rule](glue/a10-matrix-mul.md)
- [Glue matrices and affine matching](glue/a11-glue-matrices.md)
- [Glued colorings of sums](glue/a12a-glue-add-finite.md)
- [Glued colorings of products](glue/a12b-glue-mul-finite.md)
- [Two-block sums and PD-mirrors](glue/a13a-two-block-pieces.md)
- [Invert-add of two right-and-bottom blocks](glue/a13b-invert-add-two-block.md)
- [Port and value case helpers](glue/a14-port-helpers.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../definitions/integer-tangle.md)

## Proof depends on

- [Coloring fraction of a rational tangle](coloring-fraction-properties.md)
