# Explainer nodes for conway-knots (rational tangles). Written as Python data so the YAML is always valid;
# tools/write_nodes.py turns each entry into learn/nodes/<id>.md. Lead every summary with the surprise.
NODES = []
def node(id, title, summary, body, quiz, caveats=(), widgets=None):
    NODES.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))
def q(text, choices, answer, explain):
    return {"q": text, "type": "choice", "choices": choices, "answer": answer, "explain": explain}
def wt(title, steps):
    return [{"type": "walkthrough", "title": title, "config": {"steps": steps}}]
def st(text, lean=None, note=None, link=None, uses=None, hard=False):
    s = {"text": text}
    if lean: s["lean"] = lean
    if note: s["note"] = note
    if link: s["link"] = link
    if uses: s["uses"] = uses
    if hard: s["hard"] = True
    return s

# ---------------------------------------------------------------- headline 1
node("rational_classification_fragment", "PARTIAL: Conway's classification on the proved fragment",
 "**The surprise:** the theorem named 'classification' is not an if-and-only-if. It assumes two twist recipes are already linked by coloring-safe moves, and concludes their fractions agree (and that they are isotopic, which the hypothesis nearly gives already).",
 r"""
## Plain English

**Conway's theorem (1970).** Two rational tangles are isotopic **if and only if** they have the same fraction.

**What this Lean theorem says (`rational_classification_fragment`, DiagonalSumGeneral.lean lines 584-592).** Take two twist recipes e₁ and e₂ ([`TwistExpr`](#/node/TwistExpr)) such that

1. neither recipe ever multiplies a crossing on **top** ([`noMulTop`](#/node/TwistExpr.noMulTop)),
2. both pass a port side-condition ([`slideReady`](#/node/TwistExpr.slideReady)), and
3. the diagram of e₁ can be turned into the diagram of e₂ by **coloring-safe moves** ([`ColoringIsotopy`](#/node/ColoringIsotopy)): Reidemeister I–III in the forms the project handles, planar isotopy, local flypes and gluing congruences, applied in one direction.

Then

* their fractions are equal ([`TwistExpr.fraction`](#/node/TwistExpr.fraction)), **and**
* their diagrams are [`Isotopic`](#/node/Isotopic).

### How to read it

Both conclusions hang off the same hypothesis 3. So this is the shape *"coloring-safe moves ⇒ same fraction"* (one half of Conway, on a smaller move set), with the other half (*"same fraction ⇒ isotopic"*) applied straight afterwards. The two halves never meet in an "if and only if" for a single relation:

* the invariance half is proved only along `ColoringIsotopy`;
* the reconstruction half lands in `Isotopic`, which is bigger.

The second conjunct says little beyond the hypothesis. Every coloring-safe move except the local Reidemeister III model is literally a constructor of `Isotopic` too, so `ColoringIsotopy ⇒ Isotopic` is one missing bridging lemma away from free. The proof doesn't use that; it goes the long way, through canonical continued fractions ([`twist_same_fraction_isotopic_of_noMulTop`](#/node/twist_same_fraction_isotopic_of_noMulTop)).

The docstring is candid about all this: "Full Isotopic invariance in either direction is not claimed."
""",
 [q("Is this Lean theorem an 'if and only if' like Conway's?",
    ["Yes, both directions for Isotopic", "No: both conclusions follow from a ColoringIsotopy hypothesis; there is no 'isotopic ⇒ same fraction' for Isotopic", "Yes, both directions for ColoringIsotopy"], 1,
    "The hypothesis is `h : ColoringIsotopy e₁.diagram e₂.diagram` and the conclusion is `e₁.fraction = e₂.fraction ∧ Isotopic e₁.diagram e₂.diagram`. Nothing assumes `Isotopic` and concludes equal fractions."),
  q("Which recipes are excluded by `noMulTop`?",
    ["Recipes that add a crossing on the left", "Recipes that ever multiply a crossing on top", "Recipes with more than 10 crossings", "Recipes containing [∞]"], 1,
    "`noMulTop` is false exactly when a `mulTop` constructor appears. On such recipes the repo's `TwistExpr.fraction` is not the Conway fraction, so the restriction matters for the meaning of the statement, not just its proof."),
  q("Why does the second conjunct (`Isotopic e₁.diagram e₂.diagram`) add little?",
    ["Because Isotopic is trivial", "Because almost every ColoringIsotopy move is also an Isotopic move, so the hypothesis nearly gives it directly", "Because it is assumed as a hypothesis"], 1,
    "Of the 19 `ColoringIsotopy` constructors, 18 map directly onto `Isotopic` constructors (some through `symm`); only the local R3 model `r3Local` has no bridge lemma in the repo (cf. Claude audit, §1)."),
  q("Does this theorem apply to an arbitrary rational tangle diagram?",
    ["Yes", "No: it is about diagrams of twist recipes (TwistExpr), and the fraction belongs to the recipe"], 1,
    "The objects are `e₁ e₂ : TwistExpr`. The fraction of a rational tangle up to isotopy is not defined in this development.")],
 caveats=[
  "**PARTIAL.** Not Conway's theorem: no 'isotopic ⇒ same fraction' direction for `Isotopic`, and no 'same fraction ⇒ ColoringIsotopy'.",
  "`noMulTop` matters for the *meaning* of the statement: on recipes with a top product, `TwistExpr.fraction` computes 1/(s + F) where the Conway product needs 1/(s + 1/F) (see TwistExpr.fraction). The Claude audit calls this load-bearing.",
  "The second conjunct depends on `native_decide`, through the canonical-form proof (Claude audit, §6; not confirmed with `#print axioms` because nothing was built).",
  "`Isotopic` includes assumed moves; one of them (`flype_slide_add/mul`) may be stronger than real isotopy for non-rational pieces (see Isotopic)."],
 widgets=wt("How DiagonalSumGeneral.lean proves it (DiagonalSumGeneral.lean, lines 584-592)", [
   st("Color e₁ with the step-by-step coloring colorFrom 0 1, carry it along the coloring-safe moves to e₂, and read off f = F on both ends",
      "have hf := TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom",
      "This gives equal standard-form fractions; noMulTop turns them into equal recipe fractions.", link="coloring_fraction_invariant_ColoringIsotopy",
      uses=["TwistExpr.fraction_ColoringIsotopy_noMulTop_colorFrom", "TwistExpr.fraction_eq_toStandard_of_noMulTop"]),
   st("Equal fractions ⇒ isotopic diagrams, by canonical continued fractions",
      "exact ⟨hf, twist_same_fraction_isotopic_of_noMulTop hn₁ hn₂ hf⟩",
      "The reconstruction half. It does not use the coloring at all.", link="twist_same_fraction_isotopic_of_noMulTop", hard=True)]))

# ---------------------------------------------------------------- headline 2
node("twist_same_fraction_isotopic_of_noMulTop", "Same fraction ⇒ isotopic (for top-product-free recipes)",
 "**The surprise:** to prove two tangles are the same, you never have to compare them. Push each one to its unique canonical continued fraction (odd length, all terms the same sign); equal fractions give literally the same diagram code.",
 r"""
## Plain English

**Theorem (`twist_same_fraction_isotopic_of_noMulTop`, CanonicalFormUnique.lean lines 126-132).** If two twist recipes e₁ and e₂ ([`TwistExpr`](#/node/TwistExpr)) never multiply on top ([`noMulTop`](#/node/TwistExpr.noMulTop)) and have the same fraction ([`TwistExpr.fraction`](#/node/TwistExpr.fraction)), then their diagrams are [`Isotopic`](#/node/Isotopic).

This is the "reconstruction" half of Conway's theorem (Kauffman–Lambropoulou's Theorem 3), stated for recipes rather than for tangles up to isotopy. It covers every fraction: every recipe built only by adding on the right and multiplying at the bottom (standard form) is top-product-free, and standard forms reach every value in ℚ ∪ {∞}.

### The idea

1. Rewrite each recipe in **standard form** ([`toStandard`](#/node/TwistExpr.toStandard)): all additions on the right, all multiplications at the bottom. Moving a crossing from the left to the right of a tangle is a **flype**. The diagram stays isotopic ([`TwistExpr.toStandard_isotopic`](#/node/TwistExpr.toStandard_isotopic)).
2. On top-product-free recipes, the standard form has the same fraction ([`fraction_eq_toStandard_of_noMulTop`](#/node/TwistExpr.fraction_eq_toStandard_of_noMulTop)).
3. A standard form is a continued fraction [a₁, …, aₙ]. Using transfer moves and Reidemeister cancellations, push it to the **canonical** continued fraction of its value: odd length, all terms the same sign ([`ArithmeticCF.IsCanonical`](#/node/ArithmeticCF.IsCanonical)).
4. Each rational has exactly one canonical continued fraction ([`continued_fraction_canonical_unique`](#/node/continued_fraction_canonical_unique)). So the two canonical diagrams are the **same PD-code**, and the two original diagrams are isotopic through it.

The infinite fraction 1/0 is handled separately: both sides isotope to [∞].
""",
 [q("What is the hypothesis about the two recipes' fractions?",
    ["They are both positive", "They are equal", "They differ by an integer", "There is none"], 1,
    "`hf : e₁.fraction = e₂.fraction`."),
  q("What is special about the canonical continued fraction?",
    ["It has even length", "It has odd length and all terms of one sign, and it is unique for each rational", "It is always [1, 1, …, 1]"], 1,
    "`ArithmeticCF.IsCanonical` asks for odd length and termwise nonnegative or termwise nonpositive; `continued_fraction_canonical_unique` proves uniqueness."),
  q("Does this proof use integer colorings?",
    ["Yes, everywhere", "No: this half is coloring-free; it uses moves and continued-fraction arithmetic"], 1,
    "Colorings are only needed for the other direction (fractions are invariant). This half needs no `slideReady` either."),
  q("What does the conclusion `Isotopic` mean here?",
    ["Ambient isotopy of curves in a ball, as in topology textbooks", "The repo's relation generated by Reidemeister moves plus a list of assumed tangle moves (flypes, rotations, inversions, transfer moves)"], 1,
    "`Isotopic` is an inductive relation in Flype.lean lines 120-184. Many of its constructors are classical facts taken as primitive moves, not derived.")],
 caveats=[
  "**FAITHFUL WITH CAVEATS** (Claude audit). About recipes (`TwistExpr`), not rational tangles up to isotopy, and only for top-product-free recipes.",
  "The conclusion is the repo's `Isotopic`, which includes assumed moves. `flype_slide_add/mul` are stated with a planar 180° turn of an arbitrary sub-diagram, which may be stronger than the topological flype for non-rational pieces. Every use I found applies it to a rational piece, where it is classically true.",
  "Depends on six `native_decide` computations (R1/R2 cancellations on 1–2 crossing codes in ContinuedFractionFormExists.lean). This is my reading of the source and the audit's; `#print axioms` was not run."],
 widgets=wt("How CanonicalFormUnique.lean proves it (CanonicalFormUnique.lean, lines 32-132)", [
   st("Both recipes are top-product-free, so each fraction equals its standard-form fraction",
      "(TwistExpr.fraction_eq_toStandard_of_noMulTop e₁ hn₁)", uses=["TwistExpr.fraction_eq_toStandard_of_noMulTop"], link="TwistExpr.fraction_eq_toStandard_of_noMulTop"),
   st("…so the standard forms have equal fractions", "twist_same_toStandard_fraction_isotopic (h₁.symm.trans (hf.trans h₂))", uses=["twist_same_toStandard_fraction_isotopic"]),
   st("Each recipe is isotopic to its standard form (flypes move left additions and top products across)",
      "e₁.toStandard_isotopic.trans", link="TwistExpr.toStandard_isotopic", uses=["TwistExpr.toStandard_isotopic"]),
   st("Two standard forms with the same value are isotopic", "((standard_same_CFValue_isotopic h).trans e₂.toStandard_isotopic.symm)",
      "Split on whether the value is ∞ or a rational q.", uses=["standard_same_CFValue_isotopic"]),
   st("Rational case: both go to the canonical continued-fraction diagram of q", "(StandardExpr.isotopic_canonicalCF h₁).trans",
      uses=["standard_same_fraction_isotopic", "StandardExpr.isotopic_canonicalCF"]),
   st("Standard form → its continued fraction → the canonical one", ".trans e.toCF_isotopic",
      "The second step reduces any continued fraction to odd length and one sign, by transfer moves (KL Figure 14) and R1/R2 cancellations. The R1/R2 base cases use native_decide.",
      uses=["StandardExpr.toCF_isotopic", "ArithmeticCF.isotopic_canonicalCF"], hard=True),
   st("Canonical forms are unique, so the two canonical diagrams are the same code", None,
      "continued_fraction_canonical_unique (ContinuedFractionCanonical.lean lines 885-893).", link="continued_fraction_canonical_unique")]))

# ---------------------------------------------------------------- headline 3
node("coloring_fraction_invariant_ColoringIsotopy", "PARTIAL: the fraction survives coloring-safe moves",
 "**The surprise:** the fraction can be read off by coloring arcs with integers and dividing two boundary differences. Colorings ride along Reidemeister moves, so the fraction can't change; but the Lean gets this only for a smaller, one-way set of moves.",
 r"""
## Plain English

**Kauffman–Lambropoulou's Theorem 2.** The fraction of a rational tangle is an isotopy invariant.

**What this Lean theorem says (`coloring_fraction_invariant_ColoringIsotopy`, DiagonalSumGeneral.lean lines 368-375).** Let e₁, e₂ be [`slideReady`](#/node/TwistExpr.slideReady) twist recipes whose diagrams are linked by coloring-safe moves ([`ColoringIsotopy`](#/node/ColoringIsotopy)) from e₁ to e₂. Then

1. their standard-form fractions agree ([`toStandard`](#/node/TwistExpr.toStandard), [`StandardExpr.fraction`](#/node/StandardExpr.fraction)), and
2. every coloring fraction of e₁'s diagram is a coloring fraction of e₂'s ([`HasColoringFraction`](#/node/HasColoringFraction)).

### Why colorings

Color every arc with an integer so that at each crossing the two under-arcs average to the over-arc ([`IsColored`](#/node/TangleDiagram.IsColored)). Read the four boundary colors NW, NE, SW, SE ([`ColorMatrix.of`](#/node/ColorMatrix.of)). The **coloring fraction** is (NE − NW)/(NE − SE) ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)).

* A coloring can be carried across each coloring-safe move without changing the boundary colors ([`coloring_fraction_ColoringIsotopy`](#/node/coloring_fraction_ColoringIsotopy)).
* On a twist diagram, *every* non-constant coloring has coloring fraction equal to the arithmetic fraction ([`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady)).

So: color e₁, carry the coloring across, and read the same number at e₂.
""",
 [q("Along which relation is the fraction proved invariant?",
    ["Isotopic (all moves)", "ColoringIsotopy (a smaller, one-directional set of moves)", "Equality of PD-codes only"], 1,
    "The hypothesis is `h : ColoringIsotopy e₁.diagram e₂.diagram`. ColoringIsotopy omits flype slides, 180° rotations, mirror/inversion moves and transfer moves, and has no symmetry constructor."),
  q("What is the coloring fraction of a colored diagram?",
    ["(NE − NW)/(NE − SE) of the boundary colors, with ∞ when NE = SE", "The sum of all colors", "The number of crossings"], 0,
    "`ColorMatrix.fraction`: `if M.NE - M.SE = 0 then .inf else .ofRat (Rat.divInt (M.NE - M.NW) (M.NE - M.SE))`."),
  q("Do the moves in ColoringIsotopy include the mirror and inversion moves?",
    ["Yes", "No, and the Lean proves the simple 'keep the boundary colors' transport fails for them on tiny examples"], 1,
    "`not_coloring_mirror_transport` and `not_coloring_invert_transport` (DiagonalSumGeneral.lean lines 261-354) are concrete counterexamples."),
  q("Which fraction appears in the first conclusion?",
    ["`e.fraction`", "`e.toStandard.fraction`, the value after rewriting the recipe into standard form"], 1,
    "The first conjunct is `e₁.toStandard.fraction = e₂.toStandard.fraction`. On top-product-free recipes it equals `e.fraction`.")],
 caveats=[
  "**PARTIAL.** Invariance along `ColoringIsotopy`, not `Isotopic`. That relation is smaller and directed: it has no `symm`, and it omits `flype_slide_add/mul`, `rot180_*`, `mirror_cong`, `invert_*` and `transfer_*`.",
  "The `r1`/`r2` moves of `ColoringIsotopy` require `WellFormed` diagrams, and no lemma in the repo proves `WellFormed` for any construction, so those moves can be used only where a caller supplies it (Claude audit, §4–5).",
  "The refuted transports show that one proof technique (keep the boundary colors) fails across a crossing switch. They don't show that any move is false."],
 widgets=wt("How the invariance is proved (ColoringFractionEq.lean, lines 1299-1314)", [
   st("Start from a known coloring of e₁: colorFrom 0 1 (two starting colors 0 and 1, pushed through the recipe)", None,
      "TwistExpr.toStandard_fraction_ColoringIsotopy_colorFrom (ColorFractionUnique.lean lines 1432-1440) supplies it, with its proofs that it is a coloring, satisfies the diagonal rule and is not constant.",
      link="TwistExpr.colorFrom"),
   st("On e₁, that coloring's fraction is the standard-form fraction (f = F)", "have hf1 := coloring_fraction_eq_F e₁ hok₁ col hc hdiag hm", link="coloring_fraction_eq_F"),
   st("Carry the coloring across the coloring-safe moves; boundary colors are unchanged",
      "obtain ⟨col', hc', hMat, hfrac⟩ := coloring_fraction_ColoringIsotopy h col hc", link="coloring_fraction_ColoringIsotopy", hard=True),
   st("Same boundary colors, so the diagonal rule and non-constancy carry over", "simpa [hMat] using hdiag"),
   st("On e₂, f = F again", "have hf2 := coloring_fraction_eq_F e₂ hok₂ col' hc' hdiag' hm'"),
   st("Chain: F(e₁) = f = F(e₂)", "exact hf1.symm.trans (hfrac.symm.trans hf2)")]))

# ---------------------------------------------------------------- headline 4
node("coloring_fraction_eq_F_any_slideReady", "f = F: every integer coloring reads off the fraction",
 "**The surprise:** color the arcs of a twist diagram with integers in any valid way that isn't constant on the boundary: (NE − NW)/(NE − SE) is always the same number, the tangle's continued fraction. Arithmetic is hiding in the picture.",
 r"""
## Plain English

**Theorem (`coloring_fraction_eq_F_any_slideReady`, DiagonalSumGeneral.lean lines 42-48).** Let e be a [`slideReady`](#/node/TwistExpr.slideReady) twist recipe and `col` any integer coloring of its diagram ([`IsColored`](#/node/TangleDiagram.IsColored)) whose boundary colors are not all equal ([`NotMono`](#/node/ColorMatrix.NotMono)). Then the coloring fraction ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)) equals the arithmetic fraction of the recipe's standard form ([`toStandard`](#/node/TwistExpr.toStandard), [`StandardExpr.fraction`](#/node/StandardExpr.fraction)).

This is the "f = F" part of Kauffman–Lambropoulou's Theorem 4, for every coloring of every slideReady twist diagram.

### A tiny example

The single crossing [+1] ([`one`](#/node/one)) has over-arc NW–SE with color β, and under-arcs at NE and SW with colors α and 2β − α. So (NE − NW)/(NE − SE) = (α − β)/(α − β) = **1**, whatever α ≠ β you pick. Its fraction is 1.

### The proof

It is a two-line wrapper around [`coloring_fraction_eq_F`](#/node/coloring_fraction_eq_F), which also asks for the **diagonal rule** NW + SE = NE + SW ([`DiagonalSum`](#/node/ColorMatrix.DiagonalSum)). Here that hypothesis is proved, not assumed: every coloring of a slideReady twist diagram satisfies it (`twist_coloring_diagonal_slideReady`, ColoringFractionEq.lean lines 976-1007).
""",
 [q("Which colorings does the theorem cover?",
    ["Only the special coloring colorFrom 0 1", "Every integer coloring whose boundary colors are not all equal", "Only colorings with colors 0 and 1"], 1,
    "The coloring `col` is arbitrary, subject to `hc : e.diagram.IsColored col` and `hm : (ColorMatrix.of e.diagram col).NotMono`."),
  q("What is the coloring rule at a crossing?",
    ["The two under-arcs have the same color", "The two under-arc colors average to the over-arc color: α + γ = 2β", "All three colors are different"], 1,
    "`ColoringRule`: `col C.a0 = col C.a2 ∧ col C.a1 + col C.a3 = 2 * col C.a0`, with ports 0 and 2 on the over-strand."),
  q("Is the diagonal rule NW + SE = NE + SW a hypothesis of this theorem?",
    ["Yes", "No, it is proved for every coloring of a slideReady twist diagram and passed to coloring_fraction_eq_F"], 1,
    "The proof is `coloring_fraction_eq_F e hok col hc (twist_coloring_diagonal_slideReady e hok col hc) hm`.")],
 caveats=[
  "**FAITHFUL WITH CAVEATS** (Claude audit). About diagrams of slideReady twist recipes. It doesn't cover an arbitrary diagram isotopic to one; for diagrams reached by coloring-safe moves, see `coloring_fraction_agreement_any_isotopy` (DiagonalSumGeneral.lean lines 562-574).",
  "F is `e.toStandard.fraction`, which equals the recipe's own `e.fraction` only on top-product-free recipes.",
  "Only the f = F half of Theorem 4. The invariance half is the previous headline, along coloring-safe moves only."],
 widgets=wt("How it is proved (DiagonalSumGeneral.lean, lines 42-48)", [
   st("Every coloring of a slideReady twist diagram satisfies the diagonal rule", "(twist_coloring_diagonal_slideReady e hok col hc) hm",
      "Induction on the recipe. The slideReady side-conditions are exactly where this would fail: the repo refutes it for left-adding onto [∞] and top-multiplying onto [0].", uses=["twist_coloring_diagonal_slideReady"], hard=True),
   st("…so coloring_fraction_eq_F applies", "coloring_fraction_eq_F e hok col hc", link="coloring_fraction_eq_F")]))
