---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative sixteen-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the sixteen-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the sixteen switched crossings
`⟨2,3,0,1,pos⟩ … ⟨48,45,44,47,pos⟩` (the sixteenth base crossing
⟨47,48,45,44,neg⟩ rejoins the prior rung's fresh arcs 45/44 per the
add-gluing pattern, switching to ⟨48,45,44,47,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-sixteen universal is claimed over this lemma and
stays small. At this rung depth the preliminaries need
`set_option maxRecDepth 2048` to elaborate, while the universal and
existence need 4096. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
