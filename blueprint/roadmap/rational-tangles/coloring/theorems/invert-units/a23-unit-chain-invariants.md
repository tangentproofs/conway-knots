---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.unitChain_succ RationalTangles.unitChain_maxArc RationalTangles.unitChain_NW RationalTangles.unitChain_SW RationalTangles.unitChain_NE RationalTangles.unitChain_SE RationalTangles.unitChain_add_crossings RationalTangles.unitChain_invert_ports RationalTangles.unitChain_invert_succ_crossings
proof: formalized
---

# Unit-chain PD-code invariants

The recursive left-nested unit family `unitChain` (`unitChain 0 =
[+1]+[+1]`, adjoining one `[+1]` per rung) has uniform closed forms:
`maxArc = 3n+6`, ports `NW = 0`, `SW = 3`, `NE = 3n+5`, `SE = 3n+6`
(the non-uniform first glue shift is absorbed by starting the family
at two units). Each rung appends exactly one crossing in closed form,
and under inversion the next rung appends exactly the switched new
crossing after the previous rung's prefix. These are the load-bearing
preliminaries for the general-`n` invert-add induction: the crossing
prefix gives coloring restriction, the port forms give the matrix
entries. The universal induction itself is future work. Proof part of
the parent topic; see that page for the mathematical context.

## Depends on

- [Integer and vertical tangles](../../../definitions/integer-tangle.md)
