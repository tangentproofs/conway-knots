---
declaration: theorem
origin: cited
statement: formalized
lean: RationalTangles.coloring_affine RationalTangles.ColorMatrix.fraction_affine RationalTangles.coloring_IsReidemeisterI RationalTangles.coloring_IsReidemeisterII RationalTangles.coloring_IsReidemeisterIIILocal RationalTangles.coloring_IsLocalFlype RationalTangles.rational_integrally_colorable RationalTangles.standard_form_fraction_unique RationalTangles.coloring_fraction_unique_slideReady RationalTangles.coloring_fraction_invariant_ColoringIsotopy
proof: formalized
---

# The fraction is an isotopy invariant

The fraction $F$ is an isotopy invariant of rational tangles: if $T\sim S$
are rational, then $F(T)=F(S)$.

This is Theorem 2. The proof used in this DAG is the coloring argument of
§5, not the flyping argument of §4. By Theorem 4, $f$ is a topological
invariant of rational tangles and $f(T)=F(T)$. Therefore $F$ is an isotopy
invariant.

There is no appeal to the Tait flyping conjecture or to Proposition 4.

## Formalization status

Formalized generator-by-generator: affine freedom, coloring transport along
Reidemeister I–II, local Reidemeister III, and local flypes, colorability,
and uniqueness of the fraction on standard forms and `slideReady`
twists — assembled into one statement on the coloring-ready fragment
(`coloring_fraction_invariant_ColoringIsotopy`: standard-form agreement
plus carried-fraction transfer along `ColoringIsotopy` between
`slideReady` twists, both ends `slideReady`). The single-statement
assembly "for every `Isotopic` witness" is not claimed: transport along
unrestricted `flype_slide_*` and the switch-based generators
(`invert_cong`, `invert_add`, `invert_mul`, `mirror_cong`) is outstanding,
so this node is marked proved on the coloring-ready fragment only.

## Sources

- [Kauffman–Lambropoulou Theorem 2](../../../../sources/kauffman-lambropoulou.md#theorem-2)
- [Kauffman–Lambropoulou Theorem 4](../../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Fraction of a rational tangle](../../definitions/tangle-fraction.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)

## Proof depends on

- [Coloring fraction of a rational tangle](../../coloring/theorems/coloring-fraction-properties.md)
