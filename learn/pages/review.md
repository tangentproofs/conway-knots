# The review: do the statements say what the names say?

Each headline was read against Kauffman–Lambropoulou by Grok Bot. It was then audited independently by Claude from the source alone (no build). The full audit is committed as [`learn/CLAUDE_AUDIT.md`](https://github.com/tangentproofs/conway-knots/blob/main/learn/CLAUDE_AUDIT.md), and its findings are applied to the node pages.

| Headline | Classical claim | Verdict |
|---|---|---|
| [`rational_classification_fragment`](#/node/rational_classification_fragment) | Theorem 1 (Conway): isotopic ⇔ same fraction | **PARTIAL.** Not an iff. Both conclusions follow from a `ColoringIsotopy` hypothesis, and the "isotopic" conclusion nearly follows from that hypothesis directly. Top-product-free, slideReady recipes only. |
| [`twist_same_fraction_isotopic_of_noMulTop`](#/node/twist_same_fraction_isotopic_of_noMulTop) | Theorem 3: same fraction ⇒ isotopic | **Faithful with caveats.** Real content and every fraction covered, but about recipes, not tangles. It concludes the repo's `Isotopic`, with assumed moves, and depends on `native_decide`. |
| [`coloring_fraction_invariant_ColoringIsotopy`](#/node/coloring_fraction_invariant_ColoringIsotopy) | Theorem 2: the fraction is an isotopy invariant | **PARTIAL.** Invariance along a smaller, one-way set of moves. Flype slides, half-turns, mirror and inversion moves and transfer moves are excluded. |
| [`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady) | Theorem 4: f = F | **Faithful with caveats.** Every non-constant coloring of a slideReady twist diagram reads off the standard-form fraction. It is about twist diagrams, not arbitrary rational diagrams. |

## What a careful reader should know

1. **The halves don't meet.** Invariance is proved along `ColoringIsotopy`; reconstruction concludes `Isotopic`, a larger relation. No "iff" follows for either.
2. **The recipe fraction has a slip on top products.** `TwistExpr.fraction` computes 1/(s + F) for a top product, where the Conway product needs 1/(s + 1/F). They agree only when F = ±1. Example: [+1] * [0] isotopes to [0] (fraction 0), but the formula gives 1. The classification headlines assume `noMulTop`, where the formula is right, and the coloring headlines use the standard-form fraction instead. So the headlines are unaffected, but `noMulTop` is load-bearing for what they *mean*.
3. **`Isotopic` is a list of assumed moves.** Beyond Reidemeister moves, it takes flypes, half-turns, inversion identities and the Figure 14 transfer moves as generators. The flype slide is stated with a half-turn (two flips) of an *arbitrary* sub-diagram. The classical flype uses one flip, and the two agree on rational pieces but maybe not in general. Every use I found is on a rational piece. If `Isotopic` were too generous, "same fraction ⇒ isotopic" would be weaker, not false.
4. **Refuted shortcuts, not refuted moves.** `not_coloring_mirror_transport` and `not_coloring_invert_transport` show that a coloring can't always be carried from a diagram to its mirror or inverse with the same boundary colors. This rules out the simplest way of extending the coloring proof to those moves. It doesn't show any move is wrong.
5. **The excluded port cases are real.** `slideReady` rules out gluing a crossing onto a bare strand (left of [∞], top of [0]). There the diagonal rule fails, and the repo proves it (`not_diagonal_addLeft_infinity`, `not_diagonal_mulTop_zero`).
6. **The docstrings are candid.** For example: "Full Isotopic invariance in either direction is not claimed: the excluded generators are unproved". The audit found nothing dressed up as more than it is.
7. **Nothing was built**, and two headlines depend on `native_decide`. See [Trust](#/trust).

## Smuggled hypotheses?

None found. `noMulTop` and `slideReady` are visible restrictions, and the audit argues they are essential (one for meaning, one for truth). The one hypothesis that does heavy lifting is `ColoringIsotopy` in headline 1, and it is stated plainly in the signature.

## Wording the audit would not allow

"Conway's theorem formalized", "rational tangles are classified by their fraction, verified in Lean", "the fraction is an isotopy invariant" without naming `ColoringIsotopy`, and "zero sorries, fully verified".
