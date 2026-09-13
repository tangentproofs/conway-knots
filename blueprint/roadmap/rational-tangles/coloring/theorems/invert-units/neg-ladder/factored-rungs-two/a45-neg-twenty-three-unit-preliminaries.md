---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twenty-three-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twenty-three-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twenty-three switched crossings
`⟨2,3,0,1,pos⟩ … ⟨69,66,65,68,pos⟩` (the twenty-third base crossing
⟨68,69,66,65,neg⟩ rejoins the prior rung's fresh arcs 66/65 per the
add-gluing pattern, switching to ⟨69,66,65,68,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twenty-three universal is claimed over this lemma and
stays small. At this rung depth all three proof declarations need
`set_option maxRecDepth 4096` to elaborate (the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
