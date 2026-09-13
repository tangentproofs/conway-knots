---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twenty-two-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twenty-two-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twenty-two switched crossings
`⟨2,3,0,1,pos⟩ … ⟨66,63,62,65,pos⟩` (the twenty-second base crossing
⟨65,66,63,62,neg⟩ rejoins the prior rung's fresh arcs 63/62 per the
add-gluing pattern, switching to ⟨66,63,62,65,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twenty-two universal is claimed over this lemma and
stays small. At this rung depth all three proof declarations need
`set_option maxRecDepth 4096` to elaborate (the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
