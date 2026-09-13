---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative fifteen-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the fifteen-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the fifteen switched crossings
`⟨2,3,0,1,pos⟩ … ⟨45,42,41,44,pos⟩` (the fifteenth base crossing
⟨44,45,42,41,neg⟩ rejoins the prior rung's fresh arcs 42/41 per the
add-gluing pattern, switching to ⟨45,42,41,44,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-fifteen universal is claimed over this lemma and
stays small. At this rung depth all three declarations need
`set_option maxRecDepth 2048` to elaborate. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
