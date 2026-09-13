---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative fourteen-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the fourteen-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the fourteen switched crossings
`⟨2,3,0,1,pos⟩ … ⟨42,39,38,41,pos⟩` (the fourteenth base crossing
⟨41,42,39,38,neg⟩ rejoins the prior rung's fresh arcs 39/38 per the
add-gluing pattern, switching to ⟨42,39,38,41,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-fourteen universal is claimed over this lemma and
stays small. At this rung depth all three declarations need
`set_option maxRecDepth 2048` to elaborate. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
