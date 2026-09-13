---
declaration: theorem
origin: bridged
statement: formalized
lean: RationalTangles.HasColoringFraction.invert_add_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne_negOne
proof: formalized
---

# Unrestricted negative twenty-four-unit invert-add existence

The twenty-four-unit inverted sum admits a non-monochrome integral coloring
carrying `-1/24`, via the explicit `sharpColAddNegTwentyFour` witness: the
matrix computation gives `⟨-22,-21,2,3⟩`, the twenty-four switched rules
are discharged by `decide`, and `1/-24` normalizes to `-1/24`.
The witness definition itself is claimed in the companion witness node
(split for size); this node carries the fraction computation over it.
Size note: the twenty-four `show` blocks are written in 3-line form (the
`B = 2 * C` continuation joined onto one line, whitespace-only) — the old
4-line form projects the audit span to ~202, past the 200 limit, while the
joined form holds it at ~185 with identical proof tokens. At this rung
depth the invert expression needs `set_option maxRecDepth 8192` to
elaborate. Proof part of the parent topic; see that page for the
mathematical context.

## Depends on

- [Negative twenty-four-unit invert-add witness coloring](a46b-neg-twenty-four-unit-witness.md)
- [Coloring fraction](../../../../definitions/coloring-fraction.md)
- [Integer and vertical tangles](../../../../../definitions/integer-tangle.md)
