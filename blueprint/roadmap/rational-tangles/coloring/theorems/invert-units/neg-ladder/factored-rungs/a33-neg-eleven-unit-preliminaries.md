---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_rules
proof: formalized
---

# Negative eleven-unit invert-add rule preliminaries

Shared membership and rule-equation preliminaries for the eleven-unit
inverted sum `([-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1]+[-1])ⁱ`:
a single `decide` fixes the eleven switched crossings
`⟨2,3,0,1,pos⟩ … ⟨33,30,29,32,pos⟩` (the eleventh base crossing
⟨32,33,30,29,neg⟩ rejoins the prior rung's fresh arcs 30/29 per the
add-gluing pattern, switching to ⟨33,30,29,32,pos⟩ on the +3 arc
pattern), and each coloring rule is read off as its arc equation.
Factored out because the flat nine-unit universal already spans
197/200 lines: the rung-eleven universal is claimed over this lemma and
stays small. At this rung depth the universal and existence proofs need
`set_option maxRecDepth 2048` to elaborate (the preliminary itself
stays at 1024). Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
