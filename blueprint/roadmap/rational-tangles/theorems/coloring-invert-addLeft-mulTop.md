---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_addLeft RationalTangles.HasColoringFraction.mirror_addLeft
proof: formalized
---

# Coloring fraction after invert on addLeft and mulTop

Uniqueness of the coloring fraction on `addLeft` (resp. `mulTop`) of a
right-and-bottom inner expression, under the glue-port hypotheses used to
color those constructors ($NW \neq SW$ / $NW \neq NE$), identifies $f$
with the arithmetical value (resp. the standard-form value). A *fresh*
coloring of the inverted PD-code therefore has fraction $1/F$, dual to
invert uniqueness on `slideReady` diagrams. Independently, a fresh
coloring of the PD-mirror has fraction $-F$.

Colorings are not transported across crossing switch, and `invert_cong`
is not added to `ColoringIsotopy`. Invert coloring without the port
hypotheses is not claimed: those constructors are not `slideReady` when
the glue ports coincide.

This is not Theorem 2, Theorem 3, or Theorem 4. It is uniqueness of $f$
after invert (and after mirror) on these two honest classes.

## Split into pull-request-sized nodes

The remaining results live in:

- [Invert and mirror on addLeft](addLeft-mulTop/d1-addLeft.md)
- [Invert and mirror on mulTop](addLeft-mulTop/d2-mulTop.md)
- [Existence on addLeft and mulTop](addLeft-mulTop/d3-existence.md)

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Standard form](../definitions/standard-form.md)

## Proof depends on

- [Uniqueness of the coloring fraction on larger honest classes](coloring-fraction-unique.md)
- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
- [Coloring fraction after mirror on slide-ready diagrams](coloring-mirror-cong-slideReady.md)
