---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative ten-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the ten-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the ten switched crossings
`⟨2,3,0,1,pos⟩ … ⟨30,27,26,29,pos⟩` (the tenth base crossing
⟨29,30,27,26,neg⟩ rejoins the prior rung's fresh arcs 27/26 per the
add-gluing pattern, switching to ⟨30,27,26,29,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-ten universal is claimed over this lemma and
stays small. At this rung depth the invert expression needs
`set_option maxRecDepth 1024` to elaborate. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
