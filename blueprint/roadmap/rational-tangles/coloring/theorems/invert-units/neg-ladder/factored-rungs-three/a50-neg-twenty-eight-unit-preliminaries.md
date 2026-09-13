---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twenty-eight-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twenty-eight-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twenty-eight switched crossings
`⟨2,3,0,1,pos⟩ … ⟨84,81,80,83,pos⟩` (the twenty-eighth base crossing
⟨83,84,81,80,neg⟩ rejoins the prior rung's fresh arcs 81/80 per the
add-gluing pattern, switching to ⟨84,81,80,83,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twenty-eight universal is claimed over this lemma and
stays small. At this rung depth the preliminaries elaborate at
`set_option maxRecDepth 4096` while the universal and existence need 8192
(the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
