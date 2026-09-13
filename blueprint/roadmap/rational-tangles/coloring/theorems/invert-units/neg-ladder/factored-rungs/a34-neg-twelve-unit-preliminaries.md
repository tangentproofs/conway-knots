---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative twelve-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the twelve-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the twelve switched crossings
`⟨2,3,0,1,pos⟩ … ⟨36,33,32,35,pos⟩` (the twelfth base crossing
⟨35,36,33,32,neg⟩ rejoins the prior rung's fresh arcs 33/32 per the
add-gluing pattern, switching to ⟨36,33,32,35,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-twelve universal is claimed over this lemma and
stays small. At this rung depth all three declarations need
`set_option maxRecDepth 2048` to elaborate. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
