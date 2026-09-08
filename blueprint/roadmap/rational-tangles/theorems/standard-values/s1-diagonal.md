---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.twist_coloring_diagonal_rightBottom RationalTangles.twist_coloring_diagonal_slideReady RationalTangles.twist_coloring_diagonal_addLeft RationalTangles.twist_coloring_diagonal_mulTop RationalTangles.sharpCol RationalTangles.not_diagonal_addLeft_infinity RationalTangles.not_diagonal_mulTop_zero
proof: formalized
---

# Diagonal sum on twist diagrams

Every integral coloring of a `rightBottom` twist diagram — and, with
the glue-port hypotheses, of `addLeft`/`mulTop` twists, hence of every
`slideReady` twist — satisfies the diagonal sum rule, by induction over
the expression using glue of the two sides. Without the port hypotheses
(`addLeft`/`mulTop` outside `slideReady`) this is not claimed — and the
port hypotheses are sharp, not merely unproved: on `[+1]+[∞]` the sum
has `NE = SE`, forcing `NW = SW` colors, and on `[+1]*[0]` the product
has `SW = SE`, forcing `NW = NE` colors, and the `sharpCol` witness
coloring (valid on the single crossing) breaks the rule in both cases
(`not_diagonal_addLeft_infinity`, `not_diagonal_mulTop_zero`). Proof
part of the parent topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../coloring/definitions/coloring-fraction.md)
- [Standard form](../../definitions/standard-form.md)
- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
