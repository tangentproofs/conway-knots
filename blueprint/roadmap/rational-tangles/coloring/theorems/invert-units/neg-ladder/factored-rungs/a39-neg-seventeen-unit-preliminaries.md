---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative seventeen-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the seventeen-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the seventeen switched crossings
`⟨2,3,0,1,pos⟩ … ⟨51,48,47,50,pos⟩` (the seventeenth base crossing
⟨50,51,48,47,neg⟩ rejoins the prior rung's fresh arcs 48/47 per the
add-gluing pattern, switching to ⟨51,48,47,50,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-seventeen universal is claimed over this lemma and
stays small. At this rung depth the preliminaries need
`set_option maxRecDepth 2048` to elaborate, while the universal and
existence need 4096. Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
