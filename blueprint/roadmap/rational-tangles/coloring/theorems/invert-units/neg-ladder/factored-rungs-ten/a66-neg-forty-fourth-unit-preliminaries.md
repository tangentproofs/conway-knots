---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative forty-four-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the forty-four-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the forty-four switched crossings
`⟨2,3,0,1,pos⟩ … ⟨132,129,128,131,pos⟩` (the forty-fourth base crossing
⟨131,132,129,128,neg⟩ rejoins the prior rung's fresh arcs 129/128 per the
add-gluing pattern, switching to ⟨132,129,128,131,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
217 lines (audit-convention 222 against the operative 444 limit, so the octet shape is retained): the rung-forty-four universal is claimed over this lemma plus the fraction-value
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
