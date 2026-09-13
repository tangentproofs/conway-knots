---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.unitChain_invert_matrix RationalTangles.unitChain_invert_color_restrict RationalTangles.unitChain_invert_NotMono_succ RationalTangles.coloring_fraction_unitChain_invert_zero
proof: formalized
---

# Unit-chain transfer lemmas and rung zero

The load-bearing preliminaries for the general-`n` invert-add
induction, beyond the PD-code invariants of the companion node: the
closed-form boundary colors of the inverted chain, restriction of a
rung-`n+1` coloring to the prefix rung, and the chain-collapse lemma
(`NotMono` transfers down — if the prefix were monochrome, the
appended switched rule would force the whole rung monochrome).
Rung zero (two units) carries `1/2` universally, proved directly in
the per-rung style. Proof part of the parent topic; see that page for
the mathematical context.

## Depends on

- [Coloring fraction](../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
