---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.ReversibleColoringIsotopy RationalTangles.ReversibleColoringIsotopy.toColoringIsotopy RationalTangles.ReversibleColoringIsotopy.symm RationalTangles.ColoringIsotopy.symm_of_reversible RationalTangles.coloring_ReversibleColoringIsotopy RationalTangles.HasColoringFraction.of_ReversibleColoringIsotopy RationalTangles.HasColoringFraction.of_ReversibleColoringIsotopy_symm RationalTangles.IsLocalFlype.symm RationalTangles.IsReidemeisterIIILocal.symm RationalTangles.coloring_IsLocalFlype_rev RationalTangles.coloring_IsReidemeisterIIILocal_rev RationalTangles.ColoringIsotopy.add_right_rev RationalTangles.ColoringIsotopy.mul_right_rev RationalTangles.coloring_add_right_rev RationalTangles.coloring_mul_right_rev RationalTangles.ColoringIsotopy.zero_add_rev RationalTangles.coloring_zero_add_rev
proof: formalized
---

# Reversible fragment of coloring isotopy

`ReversibleColoringIsotopy` is the fragment of `ColoringIsotopy` on which
coloring transport and the relation itself reverse. It includes local
Reidemeister I–II, local Reidemeister III, local flype, planar isotopy,
left add/mul congruence, two-way-glue right add/mul, `add_zero`, left-add
of $[0]$ when $\mathrm{NW}\neq\mathrm{SW}$, unit invert both ways, and
associators both ways.

It omits unrestricted `zero_add` when $\mathrm{NW}=\mathrm{SW}$ (dummy
strand) and one-way glue without the converse port identification. It
does not add unrestricted `flype_slide` or `invert_cong` to
`ColoringIsotopy`. This is not `Isotopic` and is not a full
`ColoringIsotopy.symm`.

Local R3 and local flype reverse as diagram relations
(`IsReidemeisterIIILocal.symm`, `IsLocalFlype.symm`), so reverse coloring
along those moves is the forward lemma on the swapped pair. Right glue
reverses by feeding the converse identification to the same constructor.
`HasColoringFraction` transfers along this fragment in both directions.

This article does not claim isotopy invariance of $f$, and it is not
Theorem 2.

## Sources

- [Kauffman–Lambropoulou, coloring Reidemeister invariance](../../../../sources/kauffman-lambropoulou.md#coloring-reidemeister)

## Depends on

- [Coloring rule](../definitions/coloring-rule.md)
- [Coloring fraction](../definitions/coloring-fraction.md)
- [Coloring invariance under Reidemeister I](coloring-reidemeister-i.md)
- [Coloring invariance under Reidemeister II](coloring-reidemeister-ii.md)
- [Coloring invariance under Reidemeister III](coloring-reidemeister-iii.md)
- [Coloring invariance under flypes](coloring-flype-invariance.md)
- [2-tangle and isotopy](../../definitions/two-tangle-isotopy.md)
