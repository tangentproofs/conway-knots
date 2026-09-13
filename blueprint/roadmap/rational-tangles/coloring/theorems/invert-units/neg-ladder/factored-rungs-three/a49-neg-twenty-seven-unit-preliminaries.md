---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twenty-seven-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twenty-seven-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twenty-seven switched crossings
`⟨2,3,0,1,pos⟩ … ⟨81,78,77,80,pos⟩` (the twenty-seventh base crossing
⟨80,81,78,77,neg⟩ rejoins the prior rung's fresh arcs 78/77 per the
add-gluing pattern, switching to ⟨81,78,77,80,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twenty-seven universal is claimed over this lemma and
stays small. At this rung depth the preliminaries elaborate at
`set_option maxRecDepth 4096` while the universal and existence need 8192
(the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
