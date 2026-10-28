# Moves (isotopy relations), colorings, and the main proof steps.
import importlib.util, os
_h = importlib.util.spec_from_file_location("_h", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a_headlines.py"))
_m = importlib.util.module_from_spec(_h); _h.loader.exec_module(_m)
q, wt, st = _m.q, _m.wt, _m.st
NODES = []
def node(id, title, summary, body, quiz, caveats=(), widgets=None):
    NODES.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))

# ---------------------------------------------------------------- moves
node("Isotopic", "Isotopic: Reidemeister moves plus assumed tangle moves",
 "**The surprise:** 'isotopic' here isn't derived from Reidemeister moves alone. It's a list of 25 rules (flypes, half-turns, inversions, transfer moves), each a classical fact taken as primitive. One may be stronger than real isotopy.",
 r"""
## Plain English

**Definition (`Isotopic`, Flype.lean lines 120-184).** The smallest relation on diagrams that

* is reflexive, symmetric and transitive;
* contains every Reidemeister move and planar isotopy ([`ReidemeisterMove`](#/node/ReidemeisterMove));
* contains the **assumed moves**:
  * local flypes ([`IsLocalFlype`](#/node/IsLocalFlype)) and the Figure 5 slides `flype_slide_add/mul`: [±1] + t ∼ t.rot180 + [±1];
  * congruences: isotopic pieces give isotopic sums, products, half-turns, inverses and mirrors;
  * identities: (T+S).rot180 ∼ S.rot180 + T.rot180, (T+S)ⁱ ∼ Sⁱ * Tⁱ, (T*S)ⁱ ∼ Tⁱ + Sⁱ, associativity, [0] + T ∼ T, [±1] ∼ [±1]ⁱ;
  * the transfer moves of Figure 14: (T + [−1]) * [+1] ∼ [+1] + (−T)ⁱ and its sign-switched twin.

These are classical facts about tangles, but in Lean they are generators, not theorems.

### Is it too generous?

The Claude audit found one real risk. `flype_slide_add` uses a planar half-turn of **any** t ([`rot180`](#/node/TangleDiagram.rot180)). The classical flype uses a single flip t^h, and the half-turn is two flips. For rational t the two are isotopic (flipping lemma), so the move is fine there; every use I found is on a rational piece. For non-rational t it may not be an isotopy. Also, `Isotopic` never asks diagrams to be [well-formed](#/node/TangleDiagram.WellFormed).

A too-generous `Isotopic` would make "same fraction ⇒ isotopic" weaker, not false.
""",
 [q("Which of these is a primitive generator of `Isotopic` rather than a proved theorem?",
    ["The flype slide [±1] + t ∼ t.rot180 + [±1]", "Uniqueness of canonical continued fractions", "f = F"], 0,
    "`flype_slide_add` is a constructor of the inductive `Isotopic`."),
  q("Is `Isotopic` symmetric?", ["Yes, it has a `symm` constructor", "No"], 0, "`| symm {D E} : Isotopic D E → Isotopic E D`."),
  q("If `Isotopic` were larger than real isotopy, which headline would it weaken?",
    ["'Same fraction ⇒ Isotopic' (headline 2)", "f = F (headline 4)"], 0,
    "A bigger target relation makes the reconstruction conclusion weaker; f = F doesn't mention `Isotopic`.")],
 caveats=["`flype_slide_add/mul` and `transfer_odd(_neg)` are quantified over arbitrary diagrams; the first may exceed real isotopy for non-rational pieces (Claude audit, §5: 'unresolved risk, flagged').",
          "No well-formedness or planarity is required anywhere in `Isotopic`."])

node("ColoringIsotopy", "ColoringIsotopy: the moves a coloring can ride along",
 "**The surprise:** this relation has no 'reverse' rule. It is a one-way street of moves along which colorings are proved to carry over, which is exactly what limits the invariance theorem.",
 r"""
## Plain English

**Definition (`ColoringIsotopy`, Flype.lean lines 216-265).** The relation generated, **in one direction**, by:

* reflexivity and transitivity (no symmetry);
* Reidemeister I and II on [well-formed](#/node/TangleDiagram.WellFormed) diagrams, and a local model of Reidemeister III (`IsReidemeisterIIILocal`);
* local flypes ([`IsLocalFlype`](#/node/IsLocalFlype)) and planar isotopy ([`PlanarIsotopy`](#/node/PlanarIsotopy));
* add/mul congruences (the right-hand ones with a port side-condition);
* reindexing identities: T + [0] → T, T → [0] + T, [±1] ↔ [±1]ⁱ, associativity both ways.

It leaves out the Figure 5 slides, half-turns, mirror and general inversion moves, and transfer moves. The repo shows that carrying a coloring with fixed boundary colors from a diagram to its mirror or inverse can fail (`not_coloring_mirror_transport`, `not_coloring_invert_transport`).

`coloring_fraction_ColoringIsotopy` proves that **every** coloring can be carried along any ColoringIsotopy path with the same boundary colors.
""",
 [q("Does ColoringIsotopy have a symmetry rule?", ["Yes", "No"], 1, "There is no `symm` constructor; `ReversibleColoringIsotopy` is the symmetric fragment."),
  q("Which of these moves is in ColoringIsotopy?", ["mirror_cong", "flype_slide_add", "Local flype", "transfer_odd"], 2, "`| localFlype : IsLocalFlype D E → ColoringIsotopy D E`."),
  q("What extra condition do its R1 and R2 moves need?", ["None", "Both diagrams WellFormed", "Both diagrams rational"], 1, "`| r1 : IsReidemeisterI D E → D.WellFormed → E.WellFormed → ColoringIsotopy D E`.")],
 caveats=["No lemma in the repo proves `WellFormed` for any construction, so the R1/R2 moves are usable only where a caller supplies it (Claude audit, §4)."])

node("ReidemeisterMove", "One Reidemeister move (or a planar isotopy)",
 "**The surprise:** knot theory's three local moves, written as edits to a list of crossings: delete a kink, delete a cancelling pair, slide a strand over a crossing, or relabel.",
 r"""
## Plain English

**Definition (`ReidemeisterMove`, Reidemeister.lean lines 504-508).** One of: Reidemeister I (add/remove a kink, `IsReidemeisterI`), II (add/remove two opposite crossings, `IsReidemeisterII`), III (slide a strand across a crossing, `IsReidemeisterIII`), or a [planar isotopy](#/node/PlanarIsotopy). The four corners stay fixed.
""",
 [q("How many Reidemeister move types are there?", ["Two", "Three, plus planar isotopy", "Five"], 1, "Constructors r1, r2, r3, isotopy."),
  q("What does R2 remove?", ["A kink", "Two opposite crossings between two strands", "A whole strand"], 1, "`IsReidemeisterII` collapses an R2 pair."),
  q("Do the corners move?", ["Yes", "No, they stay fixed"], 1, "All moves fix NW, NE, SE, SW.")])

node("PlanarIsotopy", "Planar isotopy: same picture, different code",
 "**The surprise:** wiggling a diagram in the plane changes nothing in a PD code except names and order, so planar isotopy is just renaming arcs, reordering crossings, and rotating a crossing's ports.",
 r"""
## Plain English

**Definition (`PlanarIsotopy`, Reidemeister.lean lines 260-265).** E is D with arcs renamed by an injective map, crossings permuted, and each crossing possibly read from its other over-port (or with its unders read the other way and its sign flipped, `sameUpToRotation`). Corners correspond under the renaming.
""",
 [q("Can a planar isotopy create a crossing?", ["Yes", "No: no crossing data is created or destroyed"], 1, "It's a renaming plus a permutation."),
  q("Must the renaming be injective?", ["Yes", "No"], 0, "`Function.Injective f`."),
  q("Does it check that the code is planar?", ["Yes", "No"], 1, "It checks nothing geometric; it's purely combinatorial.")])

node("IsLocalFlype", "A local flype",
 "**The surprise:** a flype is the move behind Tait's 1870s flyping conjecture, and here it is one crossing sliding across a neighbouring sub-diagram that gets turned over on the way.",
 r"""
## Plain English

**Definition (`IsLocalFlype`, Flype.lean lines 107-118).** E arises from D by moving one crossing to the other side of a sub-list of crossings, rotating each of those crossings 180°, with the rest matched by an injective renaming and the corners preserved.

It is in both [`Isotopic`](#/node/Isotopic) and [`ColoringIsotopy`](#/node/ColoringIsotopy).
""",
 [q("What happens to the crossings the flype passes over?", ["They are deleted", "They are rotated 180°", "They are mirrored"], 1, "`pairRel (fun C Y => (C.rotate180.rename f).sameUpToRotation Y) tD tE`."),
  q("Is a local flype a coloring-safe move?", ["Yes", "No"], 0, "`ColoringIsotopy.localFlype`."),
  q("Do the corners change?", ["They correspond under the renaming f", "They swap"], 0, "`E.NW = f D.NW` and so on.")],
 caveats=["Like `flype_slide_add`, it rotates the passed sub-diagram 180° rather than flipping it; the Claude audit notes the same one-flip/two-flip question applies here."])

node("TangleDiagram.WellFormed", "Well-formed: every arc has exactly two ends",
 "**The surprise:** this sanity condition exists but is never proved for any diagram in the repo, not even [0] or [+1]. It appears only as a hypothesis on two coloring-safe moves.",
 r"""
## Plain English

**Definition (`TangleDiagram.WellFormed`, Reidemeister.lean lines 245-246).** Every arc number appears at 0 or 2 places (crossing ports or corners), so the code is a proper matching of half-edges.
""",
 [q("How many ends must an arc that appears have?", ["1", "2", "4"], 1, "`(D.endsOf a).length = 0 ∨ (D.endsOf a).length = 2`."),
  q("Is it proved for [+1] in the repo?", ["Yes", "No lemma establishes it for any construction"], 1, "Claude audit, §5."),
  q("Where is it required?", ["By `Isotopic`", "By the R1/R2 moves of `ColoringIsotopy`"], 1, "`Isotopic` never asks for it.")])

# ---------------------------------------------------------------- colorings
node("ColoringRule", "The coloring rule at a crossing",
 "**The surprise:** one linear equation per crossing, α + γ = 2β, is all it takes. Fox's 3-colorings are this rule read modulo 3.",
 r"""
## Plain English

**Definition (`ColoringRule`, Coloring.lean lines 45-46).** At a [crossing](#/node/Crossing), the over-strand ports 0 and 2 have the same color β, and the under-arcs' colors satisfy α + γ = 2β.
""",
 [q("Over-strand color 4, one under-arc 1. The other?", ["7", "3", "5"], 0, "1 + γ = 8."),
  q("Must the two over-strand ports have the same color?", ["Yes", "No"], 0, "`col C.a0 = col C.a2`."),
  q("Is a constant coloring valid?", ["Yes", "No"], 0, "β + β = 2β. That's why `NotMono` is needed.")])

node("TangleDiagram.IsColored", "An integer coloring of a diagram",
 "**The surprise:** a coloring is just a function from arc numbers to integers obeying one rule per crossing. Nothing global is checked, yet it detects the whole fraction.",
 r"""
## Plain English

**Definition (`TangleDiagram.IsColored`, Coloring.lean lines 49-50).** `col : ℕ → ℤ` satisfies the [coloring rule](#/node/ColoringRule) at every crossing of the diagram.
""",
 [q("What type is a coloring?", ["ℕ → ℤ", "ℤ → ℕ", "List ℤ"], 0, "`col : Nat → Int`, arc number to color."),
  q("Where must the rule hold?", ["At every crossing", "At the corners"], 0, "`∀ C ∈ D.crossings, ColoringRule C col`."),
  q("Does [0] have non-constant colorings?", ["Yes: any two colors on its two arcs", "No"], 0, "No crossings, so no constraints.")])

node("ColorMatrix", "The four boundary colors",
 "**The surprise:** after all the crossings, only four numbers matter: the colors at NW, NE, SW, SE.",
 r"""
## Plain English

**Definition (`ColorMatrix`, Coloring.lean lines 54-59).** Four integers NW, NE, SW, SE, laid out as [[NW, NE], [SW, SE]].
""",
 [q("How many entries?", ["2", "4", "8"], 1, "NW, NE, SW, SE."),
  q("What type are they?", ["Integers", "Fractions"], 0, "All four fields have type `Int`."),
  q("Where do they come from?", ["`ColorMatrix.of D col`: the colors of the corner arcs", "The crossings' signs"], 0, "See ColorMatrix.of.")])

node("ColorMatrix.of", "Read off the boundary colors",
 "**The surprise:** the matrix ignores the interior entirely: it reads the color of the arc at each corner, which is why moves that fix the corners can't change it.",
 r"""
## Plain English

**Definition (`ColorMatrix.of`, Coloring.lean lines 64-68).** NW := col D.NW, and likewise for NE, SW, SE.
""",
 [q("What is `(ColorMatrix.of D col).NE`?", ["col D.NE", "D.NE", "col 0"], 0, "`NE := col D.NE`."),
  q("Does it depend on the crossings?", ["No, only on the corner arcs", "Yes"], 0, "Only the four corners are read."),
  q("For [0] with arc colors a, c: NW, NE, SW, SE =", ["a, a, c, c", "a, c, a, c"], 0, "Arc 0 is NW–NE, arc 1 is SW–SE.")])

node("ColorMatrix.fraction", "The coloring fraction (NE − NW)/(NE − SE)",
 "**The surprise:** one division of boundary differences gives the tangle's continued fraction, with ∞ exactly when NE = SE.",
 r"""
## Plain English

**Definition (`ColorMatrix.fraction`, Coloring.lean lines 79-81).** If NE = SE, ∞. Otherwise (NE − NW)/(NE − SE) as a rational.

Checks: [0] gives (a − a)/(a − c) = 0; [∞] gives ∞; [+1] gives 1.
""",
 [q("NW = 0, NE = 3, SE = 1. Fraction?", ["3/2", "2/3", "3"], 0, "(3 − 0)/(3 − 1)."),
  q("When is it ∞?", ["When NE = SE", "When NW = 0"], 0, "`if M.NE - M.SE = 0 then .inf`."),
  q("Does it use SW?", ["No", "Yes"], 0, "Only NW, NE, SE appear (SW is fixed by the diagonal rule).")])

node("ColorMatrix.DiagonalSum", "The diagonal rule NW + SE = NE + SW",
 "**The surprise:** Kauffman–Lambropoulou prove every rational tangle's colorings obey NW + SE = NE + SW. Here it's proved for slideReady twist diagrams, and refuted for the excluded ones.",
 r"""
## Plain English

**Definition (`ColorMatrix.DiagonalSum`, Coloring.lean lines 247-248).** NW + SE = NE + SW.

For [+1]: β + β = α + (2β − α). ✓
""",
 [q("Which entries are summed?", ["The diagonals NW + SE and NE + SW", "The rows"], 0, "`M.NW + M.SE = M.NE + M.SW`."),
  q("Does it hold for every coloring of a slideReady twist diagram?", ["Yes, `twist_coloring_diagonal_slideReady`", "No"], 0, "ColoringFractionEq.lean lines 976-1007."),
  q("Does it hold for [+1] + [∞] (adding on the left of [∞])?", ["Not always: `not_diagonal_addLeft_infinity`", "Always"], 0, "That's why slideReady excludes it.")])

node("ColorMatrix.NotMono", "Not all boundary colors equal",
 "**The surprise:** a constant coloring is always valid and tells you nothing, so every f = F statement must exclude it, and that's all this hypothesis does.",
 r"""
## Plain English

**Definition (`ColorMatrix.NotMono`, ColorFraction.lean lines 23-24).** Not (NW = NE and NE = SE).
""",
 [q("Is the constant coloring NotMono?", ["Yes", "No"], 1, "All three of NW, NE, SE are equal, so it is monochrome."),
  q("NW = 1, NE = 1, SE = 2: NotMono?", ["Yes", "No"], 0, "NE ≠ SE, so not all three are equal."),
  q("Why exclude constant colorings?", ["They give 0/0", "They violate the rule"], 0, "(NE − NW)/(NE − SE) would be 0/0.")])

node("HasColoringFraction", "v is a coloring fraction of D",
 "**The surprise:** this turns the coloring fraction into a property of the diagram alone: some non-constant coloring of D reads off v.",
 r"""
## Plain English

**Definition (`HasColoringFraction`, ColorFractionUnique.lean lines 3709-3711).** There is a [coloring](#/node/TangleDiagram.IsColored) of D that is [not constant on the boundary](#/node/ColorMatrix.NotMono) and whose [coloring fraction](#/node/ColorMatrix.fraction) is v.
""",
 [q("What does `HasColoringFraction D v` assert?", ["Some non-constant coloring of D has fraction v", "Every coloring has fraction v"], 0, "It's an existential."),
  q("Does [+1] have coloring fraction 1?", ["Yes", "No"], 0, "Any non-constant coloring gives 1."),
  q("Headline 3 carries this property in which direction?", ["From e₁ to e₂ only", "Both ways"], 0, "ColoringIsotopy is directed.")])

node("TwistExpr.colorFrom", "A coloring built step by step",
 "**The surprise:** give the starting tangle two colors and every later crossing's colors are forced, so each recipe comes with a ready-made coloring.",
 r"""
## Plain English

**Definition (`TwistExpr.colorFrom`, ColoringFractionEq.lean lines 379-391).** From two integers a, c, color the starting tangle, then extend the coloring across each glued crossing using τ_β(α) = 2β − α. The invariance proofs use `colorFrom 0 1`, which is proved to be a coloring, satisfy the diagonal rule and be non-constant on slideReady recipes.
""",
 [q("How many starting colors?", ["1", "2", "4"], 1, "`TwistExpr → Int → Int → (Nat → Int)`."),
  q("Which starting colors do the invariance proofs use?", ["0 and 1", "1 and 2"], 0, "`e₁.colorFrom 0 1`."),
  q("How is a new under-arc colored?", ["2β − α", "α + β", "0"], 0, "The rule α + γ = 2β.")])

# ---------------------------------------------------------------- proof steps
node("coloring_fraction_ColoringIsotopy", "Colorings ride along coloring-safe moves",
 "**The surprise:** this is the engine of invariance, and it works for every diagram, rational or not: any coloring can be carried across any coloring-safe path without changing a single boundary color.",
 r"""
## Plain English

**Theorem (`coloring_fraction_ColoringIsotopy`, ColoringIsotopy.lean lines 2125-2132).** If D → E by [`ColoringIsotopy`](#/node/ColoringIsotopy) and `col` colors D, there is a coloring `col'` of E with the same boundary colors ([`ColorMatrix.of`](#/node/ColorMatrix.of)), hence the same coloring fraction.

The work is in `coloring_ColoringIsotopy`, an induction over every constructor: R1, R2, local R3 (`ColoringR3.lean`), local flypes (`ColoringFlype.lean`), congruences and reindexings.
""",
 [q("Does it need D or E to be rational?", ["No, any diagrams", "Yes"], 0, "D and E are arbitrary `TangleDiagram`s."),
  q("What is preserved?", ["The color matrix", "The number of crossings"], 0, "`ColorMatrix.of E col' = ColorMatrix.of D col`."),
  q("Can the coloring be carried backwards along the path?", ["Not in general; the relation is directed", "Yes, always"], 0, "Only partial reverse lemmas exist.")])

node("coloring_fraction_eq_F", "f = F, given the diagonal rule",
 "**The surprise:** the proof never compares colorings directly. It carries the coloring to the standard form, where every non-constant coloring is forced to give the continued fraction.",
 r"""
## Plain English

**Theorem (`coloring_fraction_eq_F`, ColoringFractionEq.lean lines 654-660).** For a [slideReady](#/node/TwistExpr.slideReady) recipe e and a coloring of its diagram that satisfies the [diagonal rule](#/node/ColorMatrix.DiagonalSum) and is [not constant](#/node/ColorMatrix.NotMono), the coloring fraction equals the standard-form fraction.

The headline [`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady) removes the diagonal hypothesis.
""",
 [q("Which hypothesis does the headline version remove?", ["NotMono", "DiagonalSum", "slideReady"], 1, "It's proved by `twist_coloring_diagonal_slideReady`."),
  q("Where is the coloring carried?", ["To the standard form's diagram", "To the mirror"], 0, "`coloring_toStandard`."),
  q("On standard forms, which colorings give F?", ["Every non-constant one", "Only colorFrom"], 0, "`standard_fraction_any_coloring`.")],
 widgets=wt("How ColoringToStandard.lean proves it (ColoringToStandard.lean, lines 241-253)", [
   st("Carry the coloring along the flypes that rewrite e into standard form", "obtain ⟨col', hc', hs⟩ := coloring_toStandard e hok col hc hdiag",
      "Each left addition / top product becomes a Figure 5 slide; the coloring crosses it using the diagonal rule and the slideReady port condition.", hard=True),
   st("Boundary colors are unchanged", "have hM := ColorMatrix.of_sameEndpoint hs"),
   st("On a standard form every non-constant coloring gives F", "have hf := standard_fraction_any_coloring e.toStandard col' hc' hm'",
      "Induction on the standard form: each right addition adds 1 to (NE−NW)/(NE−SE), each bottom product acts on its reciprocal.", uses=["standard_fraction_any_coloring"])]))

node("standard_fraction_any_coloring", "On standard forms, every coloring gives F",
 "**The surprise:** gluing [+1] on the right adds exactly 1 to (NE − NW)/(NE − SE) for every coloring at once. Induction on the recipe does the rest.",
 r"""
## Plain English

**Theorem (`standard_fraction_any_coloring`, ColorFraction.lean lines 860-941).** For a [standard form](#/node/StandardExpr) e and any non-constant coloring of its diagram, the coloring fraction is [`e.fraction`](#/node/StandardExpr.fraction). Induction: [0] and [∞] directly, then each right addition or bottom product transforms the fraction like the arithmetic.
""",
 [q("What kind of proof is it?", ["Induction on the standard form", "A computer search"], 0, "`induction e generalizing col`."),
  q("Does it need slideReady?", ["No, standard forms are always fine", "Yes"], 0, "No port conditions on right additions or bottom products."),
  q("Does it need the diagonal rule as a hypothesis?", ["No; it proves it along the way (standard_coloring_diagonal)", "Yes"], 0, "The proof calls `standard_coloring_diagonal`.")])

node("TwistExpr.toStandard_isotopic", "A recipe is isotopic to its standard form",
 "**The surprise:** moving a crossing from the left of a tangle to its right is a flype, and it needs the tangle to be isotopic to its own half-turn, which is the flipping lemma, applied inside the induction.",
 r"""
## Plain English

**Theorem (`TwistExpr.toStandard_isotopic`, FlippingLemma.lean lines 516-547).** Every recipe's diagram is [`Isotopic`](#/node/Isotopic) to the diagram of its [standard form](#/node/TwistExpr.toStandard). For `addLeft`: [s] + T ∼ T.rot180 + [s] (flype slide) ∼ T + [s] (T is isotopic to its half-turn). Likewise for `mulTop`.
""",
 [q("Which move moves a left crossing to the right?", ["Reidemeister II", "The flype slide", "Mirror"], 1, "`flype_add s e.diagram`."),
  q("Why is T.rot180 ∼ T available?", ["T is a twist diagram (rational), flipping lemma", "It's true for every diagram"], 0, "`e.isotopic_rot180`."),
  q("Does this lemma need noMulTop?", ["No", "Yes"], 0, "It holds for every recipe; noMulTop is needed for the fraction, not the isotopy.")],
 caveats=["Uses the assumed move `flype_slide_add/mul` (see Isotopic)."])

node("TwistExpr.fraction_eq_toStandard_of_noMulTop", "No top products ⇒ recipe fraction = standard-form fraction",
 "**The surprise:** left and right additions give the same number because addition commutes, but top and bottom products don't, because of the slip in the top-product formula.",
 r"""
## Plain English

**Theorem (`TwistExpr.fraction_eq_toStandard_of_noMulTop`, ColoringFractionEq.lean lines 495-511).** If a recipe has no top products, its [fraction](#/node/TwistExpr.fraction) equals the fraction of its [standard form](#/node/TwistExpr.toStandard). Induction on the recipe; the `mulTop` case is impossible by hypothesis.
""",
 [q("Why does addLeft cause no trouble?", ["Addition is commutative", "It's excluded"], 0, "s + F = F + s."),
  q("What happens in the `mulTop` case of the induction?", ["Contradiction with noMulTop", "A long computation"], 0, "`| mulTop e s => cases h`."),
  q("Do the two fractions agree in general on recipes with top products?", ["No", "Yes"], 0, "They agree only in special cases (inner fraction ±1).")])

node("ArithmeticCF.IsCanonical", "Canonical continued fraction: odd length, one sign",
 "**The surprise:** each rational has many continued fractions, but exactly one that has odd length with all terms the same sign, and that's the tangle's normal form.",
 r"""
## Plain English

**Definition (`ArithmeticCF.IsCanonical`, CanonicalForm.lean lines 24-26).** A continued fraction [a₁, …, aₙ] ([`ArithmeticCF`](#/node/ArithmeticCF)) is canonical when n is odd and all terms are ≥ 0 or all are ≤ 0. Example: 7/4 = 1 + 1/(1 + 1/3) = [1, 1, 3].
""",
 [q("Which is canonical?", ["[1, 1, 3]", "[1, 1]", "[2, −1, 3]"], 0, "Odd length, one sign."),
  q("Is [2, 1] canonical?", ["No, even length", "Yes"], 0, "Length 2 is even. Its value is 2 + 1/1 = 3, whose canonical form is [3]."),
  q("Can ∞ have a canonical expansion?", ["No", "Yes"], 0, "`isCanonical_value_ne_inf`.")])

node("ArithmeticCF", "A continued fraction [a₁, …, aₙ]",
 "**The surprise:** a continued fraction is both a number and a tangle: [a₁, …, aₙ] is a stack of horizontal and vertical twists.",
 r"""
## Plain English

**Definition (`ArithmeticCF`, ContinuedFraction.lean lines 319-325).** A non-empty list of integer terms, all terms after the first non-zero. Its value is a₁ + 1/(a₂ + 1/(…)) in [`CFValue`](#/node/CFValue), and it has a tangle diagram `cf.tangle`.
""",
 [q("Can a later term be 0?", ["No", "Yes"], 0, "`later_ne_zero`."),
  q("Value of [2, 3]?", ["2 + 1/3 = 7/3", "5", "2/3"], 0, "a₁ + 1/a₂."),
  q("Can the first term be 0?", ["Yes", "No"], 0, "Only later terms must be non-zero.")])

node("continued_fraction_canonical_unique", "Canonical continued fractions are unique",
 "**The surprise:** uniqueness here is literal equality of lists, so two canonical tangle diagrams of the same value are the same PD-code, with no isotopy needed.",
 r"""
## Plain English

**Theorem (`continued_fraction_canonical_unique`, ContinuedFractionCanonical.lean lines 885-893).** Two [canonical](#/node/ArithmeticCF.IsCanonical) continued fractions with the same value are equal. Kauffman–Lambropoulou's Proposition 3. Both equal `canonicalCF q`, built by an 'oddified' Euclidean algorithm.
""",
 [q("What does it conclude?", ["cf₁ = cf₂", "Isotopic cf₁.tangle cf₂.tangle"], 0, "Equality, which is stronger."),
  q("Does it involve diagrams?", ["No, pure arithmetic", "Yes"], 0, "It is about lists of integers."),
  q("Can a canonical expansion have value ∞?", ["No", "Yes"], 0, "That case is excluded.")])
