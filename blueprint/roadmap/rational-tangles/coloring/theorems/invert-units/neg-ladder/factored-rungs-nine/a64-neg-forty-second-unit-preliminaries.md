---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative forty-two-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the forty-two-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the forty-two switched crossings
`⟨2,3,0,1,pos⟩ … ⟨126,123,122,125,pos⟩` (the forty-second base crossing
⟨125,126,123,122,neg⟩ rejoins the prior rung's fresh arcs 123/122 per the
add-gluing pattern, switching to ⟨126,123,122,125,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
207 lines (audit-convention 212 against the operative 444 limit, so the octet shape is retained): the rung-forty-two universal is claimed over this lemma plus the fraction-value
preliminary and stays small. At this rung depth the preliminaries elaborate at
`set_option maxRecDepth 4096` (crossings and witness-rules; the fraction-value lemma
carries 8192 since it holds the universal linarith tail) while the universal, existence, and existence-head
need 16384
(the witness def is a plain
if-else chain and needs none). Proof part of the parent
topic; see that page for the mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
