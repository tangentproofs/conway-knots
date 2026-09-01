---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.TwistExpr.toStandard_transfer_odd RationalTangles.coloring_mirror_invert_any_eq_negInv_F_slideReady RationalTangles.coloring_transfer_odd_slideReady
proof: formalized
---

# Figure 14 at the coloring fraction on slide-ready diagrams

The leftover generator `Isotopic.transfer_odd` is
$(T+[-1])\ast[+1]\sim[+1]+(-T)^{i}$. The right-hand side switches every
crossing of $T$, so this is not a `ColoringIsotopy` constructor, and
`SameEndpointColors` after `one.mirror` is false.

On a `slideReady` diagram with distinct `NW`/`NE` (not the `[0]` kink),
independent non-monochrome colorings of the two sides have the same
coloring fraction. The left-hand side is itself `slideReady`, so
$f=F$ of the corresponding twist. Uniqueness after mirror identifies
$f(-T)=-F$, hence $f((-T)^{i})=-1/F$; gluing `[+1]` on the left yields
$1-1/F$, matching the arithmetical Figure 14 identity on
`toStandard.fraction`.

This is not Theorem 2, Theorem 3, or Theorem 4. Kinks are excluded.

## Sources

- [Kauffman–Lambropoulou Theorem 4](../../../sources/kauffman-lambropoulou.md#theorem-4)

## Depends on

- [Coloring fraction](../coloring/definitions/coloring-fraction.md)
- [Flype](../definitions/flype.md)

## Proof depends on

- [Coloring fraction after mirror on slide-ready diagrams](coloring-mirror-cong-slideReady.md)
- [Coloring fraction after invert on slide-ready diagrams](coloring-invert-cong-slideReady.md)
