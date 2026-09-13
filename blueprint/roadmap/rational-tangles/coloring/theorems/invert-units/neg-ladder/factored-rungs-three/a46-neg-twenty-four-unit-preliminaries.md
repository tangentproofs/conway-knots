---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twenty-four-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twenty-four-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twenty-four switched crossings
`⟨2,3,0,1,pos⟩ … ⟨72,69,68,71,pos⟩` (the twenty-fourth base crossing
⟨71,72,69,68,neg⟩ rejoins the prior rung's fresh arcs 69/68 per the
add-gluing pattern, switching to ⟨72,69,68,71,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twenty-four universal is claimed over this lemma and
stays small. At this rung depth the preliminaries elaborate at
`set_option maxRecDepth 4096` while the universal and existence need 8192
(the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
