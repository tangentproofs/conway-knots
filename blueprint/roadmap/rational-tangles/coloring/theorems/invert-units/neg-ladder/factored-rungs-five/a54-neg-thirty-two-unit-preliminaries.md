---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative thirty-two-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the thirty-two-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the thirty-two switched crossings
`⟨2,3,0,1,pos⟩ … ⟨96,93,92,95,pos⟩` (the thirty-second base crossing
⟨95,96,93,92,neg⟩ rejoins the prior rung's fresh arcs 93/92 per the
add-gluing pattern, switching to ⟨96,93,92,95,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-thirty-two universal is claimed over this lemma plus the fraction-value
preliminary and stays small. At this rung depth the preliminaries elaborate at
`set_option maxRecDepth 4096` (crossings and witness-rules; the fraction-value lemma
carries 8192 since it holds the universal linarith tail) while the universal and existence
need 8192
(the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
