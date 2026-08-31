---
kind: coverage
status: in-progress
---

# Coverage

Coverage is tracked at chapter level. The first milestone is Conway's
classification of rational tangles (Kauffman–Lambropoulou, Theorem 1), proved
via the integral coloring of §5. Rows span that theorem, the rest of the
adopted paper, and the Conway census the user placed out of scope. The labels
below are validated Autoform dispositions: `MAPPED`, `DECOMPOSED`, `DEFERRED`,
or `OUT`.

| Area | Coverage | Evidence |
| --- | --- | --- |
| Rational tangle classification via coloring (Kauffman–Lambropoulou §§2–3, §5 Theorem 4, Theorems 2–3, Theorem 1) | `DECOMPOSED` | [Classification theorem](../roadmap/rational-tangles/theorems/classification.md) in the [Rational tangles](../roadmap/rational-tangles/README.md) chapter, proved through the [coloring fraction](../roadmap/rational-tangles/coloring/theorems/coloring-fraction-properties.md) |
| Tait flyping / Proposition 4 proof of Theorem 2 | `OUT` | Unused alternate; [Tait](../roadmap/rational-tangles/theorems/tait-flyping.md) and [Proposition 4](../roadmap/rational-tangles/theorems/alternating-flypes.md) remain as exposition and are not dependencies of Theorem 1 |
| Remainder of §5 (Theorem 5, Kauffman–Harary coloring conjecture, open integrally colorable tangles) | `OUT` | Not used in Theorem 1 |
| Schubert classification of rational knots | `DEFERRED` | Sequel to this paper (Kauffman–Lambropoulou [17]); not Theorem 1 |
| Algebraic tangles, generating operations, and history (Kauffman–Lambropoulou §6) | `OUT` | Not used in the statement or the coloring proof of Theorem 1 |
| Infinite and imaginary tangles (closing remarks of §3) | `OUT` | Beyond finite rational tangles |
| Conway 1970 knot and link census | `OUT` | Explicitly out of first-milestone scope; the theorem is the target, not the census |

## Completion rule

The current milestone is complete when the classification node and every
article it depends on compile under recorded Lean declarations and pass
mathematical and code review. That includes the coloring lemmas of §5 and
does not include Tait, Schubert's theorems, or the Conway census.
