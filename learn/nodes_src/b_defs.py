# Definitions the headline statements mention.
import importlib.util, os
_h = importlib.util.spec_from_file_location("_h", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a_headlines.py"))
_m = importlib.util.module_from_spec(_h); _h.loader.exec_module(_m)
q, wt, st = _m.q, _m.wt, _m.st
NODES = []
def node(id, title, summary, body, quiz, caveats=(), widgets=None):
    NODES.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))

# ---------------------------------------------------------------- diagrams
node("TangleDiagram", "A 2-tangle diagram as a planar-diagram code",
 "**The surprise:** a tangle is stored as a list of crossings, each four arc numbers plus a sign, and the arc numbers at the four corners. No geometry at all, and nothing forces the code to be drawable in a disc.",
 r"""
## Plain English

A **2-tangle** is two strings in a ball with their four ends pinned at the corners NW, NE, SE, SW of the picture (plus possibly closed loops).

**Definition (`TangleDiagram`, Reidemeister.lean lines 177-187).** A diagram is

* `crossings`: a list of [`Crossing`](#/node/Crossing)s. Each crossing names the four arcs that meet it, counterclockwise, with the over-strand on ports 0 and 2, plus a sign;
* `NW`, `NE`, `SE`, `SW`: the arc number touching each corner.

This is the tangle version of a knot's **PD code**. It was chosen so an integer coloring is just a function from arc numbers to ℤ ([`IsColored`](#/node/TangleDiagram.IsColored)).

The trivial tangles have no crossings: [`[0]`](#/node/TangleDiagram.zero) (two horizontal arcs) and [`[∞]`](#/node/TangleDiagram.infinity) (two vertical arcs).
""",
 [q("What does a `TangleDiagram` store?",
    ["Coordinates of the strings in space", "A list of crossings (four arc numbers and a sign each) and the arc number at each corner", "A continued fraction"], 1,
    "The fields are `crossings : List Crossing` and `NW NE SE SW : Nat`."),
  q("Does the type guarantee that the code is a real planar diagram?",
    ["Yes", "No: there is no planarity condition, and `WellFormed` (each arc has exactly two ends) is a separate predicate"], 1,
    "The type includes codes that can't be drawn in a disc. The headline objects are built by honest operations, so this doesn't affect them, but statements about arbitrary `TangleDiagram`s are about the larger model."),
  q("How are two codes that differ only by renaming arcs treated?",
    ["They are equal as Lean values", "They are different values, related by `PlanarIsotopy`"], 1,
    "The type is not quotiented; `PlanarIsotopy` (renaming, reordering, rotating a crossing) relates them.")],
 caveats=["No planarity or well-formedness is built into the type (Claude audit, §5)."])

node("Crossing", "A crossing: four arc numbers and a sign",
 "**The surprise:** a crossing is just four numbers read counterclockwise, with the over-strand on ports 0 and 2. The coloring rule only ever looks at which port an arc sits on.",
 r"""
## Plain English

**Definition (`Crossing`, Reidemeister.lean lines 71-81).** A crossing has arc numbers `a0`, `a1`, `a2`, `a3` at its four ports, read counterclockwise. Ports 0 and 2 belong to the **over-strand**, ports 1 and 3 to the two pieces of the **under-strand**. It also has a [`sign`](#/node/CrossingSign): `pos` as in [+1], `neg` as in [−1].

Because the over-strand occupies ports 0 and 2, the coloring rule ([`ColoringRule`](#/node/ColoringRule)) reads: color(a0) = color(a2) = β and color(a1) + color(a3) = 2β.
""",
 [q("Which ports carry the over-strand?",
    ["0 and 1", "0 and 2", "1 and 3", "2 and 3"], 1, "Ports `0` and `2` are the overstrand; `1` and `3` are the two under-arcs."),
  q("What else does a crossing record besides arc numbers?",
    ["Its position in the plane", "A sign: pos or neg", "Its color"], 1, "The last field is `sign : CrossingSign`."),
  q("If color(a0) = 5 and color(a1) = 2, what must color(a3) be?",
    ["5", "8", "3", "7"], 1, "α + γ = 2β with β = 5 and α = 2 gives γ = 8.")])

node("CrossingSign", "Crossing sign: [+1] or [−1]",
 "**The surprise:** the sign convention here (Kauffman–Lambropoulou, after Ernst–Sumners) is the opposite of Conway's 1970 paper, so a 'positive' twist here is a negative one in Conway.",
 r"""
## Plain English

**Definition (`CrossingSign`, Reidemeister.lean lines 48-51).** Two values, `pos` and `neg`: the crossing types of the elementary tangles [+1] and [−1].

`flip` swaps them; the mirror image of a diagram flips every sign. Its arithmetic value ([`CrossingSign.cfValue`](#/node/CrossingSign.cfValue)) is +1 or −1.
""",
 [q("How many crossing signs are there?", ["One", "Two", "Four"], 1, "`pos` and `neg`."),
  q("Which convention is used?", ["Conway 1970", "Kauffman–Lambropoulou (Ernst–Sumners), the opposite of Conway's"], 1, "The docstring says so explicitly."),
  q("What does `flip` do?", ["Rotates the crossing", "Swaps pos and neg", "Deletes the crossing"], 1, "`flip : pos ↦ neg, neg ↦ pos`.")])

node("CrossingSign.cfValue", "The number of a crossing sign: +1 or −1",
 "**The surprise:** this tiny map is where pictures become arithmetic: every twist contributes exactly ±1 to a continued fraction.",
 r"""
## Plain English

**Definition (`CrossingSign.cfValue`, TangleFraction.lean lines 23-25).** `pos` ↦ 1 and `neg` ↦ −1, as [`CFValue`](#/node/CFValue)s. These are the fractions of [+1] and [−1].
""",
 [q("What is the value of `neg`?", ["0", "1", "−1", "∞"], 2, "`.neg => .ofInt (-1)`."),
  q("What is the value of `pos`?", ["1", "−1", "2"], 0, "`.pos => 1`."),
  q("What type do the values have?", ["ℤ", "CFValue (a rational or ∞)", "ℕ"], 1, "`CrossingSign.cfValue : CrossingSign → CFValue`.")])

node("TangleDiagram.zero", "The tangle [0]: two horizontal arcs",
 "**The surprise:** [0] has no crossings at all. Its whole content is that NW and NE share one arc and SW and SE share another, so its fraction (NE − NW)/(NE − SE) is 0.",
 r"""
## Plain English

**Definition (`TangleDiagram.zero`, Reidemeister.lean lines 192-197).** No crossings; arc 0 runs NW–NE and arc 1 runs SW–SE.

Color arc 0 with a and arc 1 with c ≠ a: the coloring fraction is (a − a)/(a − c) = 0, matching its fraction 0. Adding [0] on the right of a diagram changes nothing (`add_zero_eq`).
""",
 [q("How many crossings does [0] have?", ["0", "1", "2"], 0, "`crossings := []`."),
  q("Which corners does the arc numbered 0 join?", ["NW and SW", "NW and NE", "NW and SE"], 1, "`NW := 0, NE := 0`."),
  q("What is the fraction of [0]?", ["0", "1", "∞"], 0, "Both `TwistExpr.fraction` and the coloring fraction give 0.")])

node("TangleDiagram.infinity", "The tangle [∞]: two vertical arcs",
 "**The surprise:** [∞] is [0] turned 90°, and its fraction is 1/0. The fractions here live on ℚ ∪ {∞}, the projective line, so turning a tangle a quarter turn acts like taking a reciprocal.",
 r"""
## Plain English

**Definition (`TangleDiagram.infinity`, Reidemeister.lean lines 200-205).** No crossings; arc 0 runs NW–SW and arc 1 runs NE–SE.

In any coloring NE = SE, so (NE − NW)/(NE − SE) has denominator 0: the coloring fraction is ∞ ([`ColorMatrix.fraction`](#/node/ColorMatrix.fraction)). Inverting [0] gives [∞] (`invert_zero`).
""",
 [q("Which corners does arc 1 join?", ["NE and SE", "NW and NE", "SW and SE"], 0, "`NE := 1, SE := 1`."),
  q("What is the fraction of [∞]?", ["0", "∞ (1/0)", "1"], 1, "`TwistExpr.fraction infinity = .inf`."),
  q("What does inverting [0] give?", ["[0]", "[∞]", "[1]"], 1, "`invert_zero : TangleDiagram.zero.invert = TangleDiagram.infinity`.")])

node("one", "The single crossing [+1]",
 "**The surprise:** in any coloring of [+1], (NE − NW)/(NE − SE) is exactly 1, whatever colors you choose (as long as they are not all equal). That is f = F on the smallest example.",
 r"""
## Plain English

**Definition (`one`, IntegerTangle.lean lines 28-33).** One positive crossing with arcs 0, 1, 2, 3 at NW, NE, SE, SW. The over-strand runs NW–SE.

Color the over-strand β and the NE under-arc α. The rule forces SW = 2β − α. Then (NE − NW)/(NE − SE) = (α − β)/(α − β) = 1.

[−1] ([`negOne`](#/node/negOne)) is its mirror image.
""",
 [q("Which corners does the over-strand of [+1] join?", ["NW and SE", "NE and SW", "NW and NE"], 0, "Ports 0 and 2 (over) are at NW and SE."),
  q("If NW = SE = 3 and NE = 7, what is the SW color?", ["7", "−1", "3", "10"], 1, "α + γ = 2β: 7 + γ = 6, so γ = −1."),
  q("What is the coloring fraction of [+1] with those colors?", ["1", "7/3", "−1"], 0, "(NE − NW)/(NE − SE) = (7 − 3)/(7 − 3) = 1.")])

node("negOne", "The single crossing [−1]",
 "**The surprise:** [−1] isn't built from scratch: it is defined as the mirror image of [+1], so all the mirror machinery is tested on the smallest case.",
 r"""
## Plain English

**Definition (`negOne`, IntegerTangle.lean lines 36-37).** `one.mirror`: [+1] with its crossing switched ([`TangleDiagram.mirror`](#/node/TangleDiagram.mirror)). Its fraction is −1.
""",
 [q("How is [−1] defined?", ["As a new crossing list", "As the mirror of [+1]"], 1, "`def negOne : TangleDiagram := one.mirror`."),
  q("What is its fraction?", ["1", "−1", "0"], 1, "`TwistExpr.fraction negOne = .ofInt (-1)`."),
  q("How many crossings does it have?", ["0", "1", "2"], 1, "Mirroring keeps the single crossing and switches it.")])

node("crossingTangle", "[±1] as a function of a sign",
 "**The surprise:** every twist recipe adds or multiplies by exactly this one-crossing tangle, so all rational tangles are built from a single kind of building block.",
 r"""
## Plain English

**Definition (`crossingTangle`, IntegerTangle.lean lines 40-42).** `pos` ↦ [+1] ([`one`](#/node/one)), `neg` ↦ [−1] ([`negOne`](#/node/negOne)).
""",
 [q("What is `crossingTangle .neg`?", ["[+1]", "[−1]", "[0]"], 1, "`| .neg => negOne`."),
  q("How many crossings does `crossingTangle s` have?", ["0", "1", "2"], 1, "Both [+1] and [−1] have one crossing."),
  q("Where is it used?", ["In every add/multiply step of a twist recipe", "Only in [∞]"], 0, "`TwistExpr.diagram` glues `crossingTangle s` at each step.")])

node("TangleDiagram.add", "Tangle addition T + S: side by side",
 "**The surprise:** gluing two tangles side by side is just list concatenation plus renaming: shift S's arc numbers past T's, then identify S's west ends with T's east ends.",
 r"""
## Plain English

**Definition (`TangleDiagram.add`, Tangle.lean lines 98-109).** Place S to the right of T, joining T's NE to S's NW and T's SE to S's SW. In code:

1. rename S's arcs by adding T's largest arc number + 1, so they don't clash;
2. rename S's NW arc to T's NE arc and S's SW arc to T's SE arc;
3. concatenate the crossing lists. The new corners are T's NW/SW and S's NE/SE.

Fractions add: F(T + S) = F(T) + F(S), for rational T and S whenever the sum is rational.
""",
 [q("Where does S go in T + S?", ["Below T", "To the right of T", "On top of T"], 1, "`Place S to the right of T`."),
  q("Which arcs are identified?", ["T.NE with S.NW and T.SE with S.SW", "T.SW with S.NW", "None"], 0, "The renaming `f` sends `S'.NW` to `T.NE` and `S'.SW` to `T.SE`."),
  q("What happens to the crossing lists?", ["They are concatenated", "They are merged by sign", "S's list is dropped"], 0, "`crossings := T.crossings ++ S''.crossings`.")])

node("TangleDiagram.mul", "Tangle product T * S: one on top of the other",
 "**The surprise:** stacking S under T makes reciprocals add: 1/F(T*S) = 1/F(T) + 1/F(S). That's why the product is the quarter-turned twin of addition.",
 r"""
## Plain English

**Definition (`TangleDiagram.mul`, Tangle.lean lines 112-123).** Place S below T, joining T's SW to S's NW and T's SE to S's NE, with the same rename-and-concatenate recipe as [addition](#/node/TangleDiagram.add).

Arithmetically 1/F(T * S) = 1/F(T) + 1/F(S). So multiplying [+1] at the bottom sends a fraction x to 1/(1/x + 1).
""",
 [q("Where does S go in T * S?", ["To the right", "Below T", "Above T"], 1, "`Place S below T`."),
  q("What happens to fractions under the product?", ["They add", "Their reciprocals add", "They multiply"], 1, "1/F(T*S) = 1/F(T) + 1/F(S)."),
  q("Multiplying x = 2 at the bottom by [+1] gives?", ["3", "2/3", "1/3"], 1, "1/(1/2 + 1) = 2/3.")])

node("TangleDiagram.mirror", "Mirror image −T: switch every crossing",
 "**The surprise:** the mirror changes no arc and no corner, only the crossing data, yet it negates the fraction. Colorings don't survive the switch unchanged, which is why the coloring proof can't handle mirror moves.",
 r"""
## Plain English

**Definition (`TangleDiagram.mirror`, Tangle.lean lines 81-82).** Apply `Crossing.switch` to every crossing: the over-strand becomes the under-strand (ports shift by one) and the sign flips. Corners stay put. F(−T) = −F(T).

The repo proves that a coloring of [+1] can't always be carried to its mirror with the same boundary colors (`not_coloring_mirror_transport`, DiagonalSumGeneral.lean lines 261-295).
""",
 [q("What changes under the mirror?", ["The corners", "Every crossing is switched", "Nothing"], 1, "`crossings := T.crossings.map Crossing.switch`; corners unchanged."),
  q("What happens to the fraction?", ["It is negated", "It is inverted", "It is unchanged"], 0, "F(−T) = −F(T); e.g. −[1] = [−1]."),
  q("Is the mirror an isotopy?", ["Yes", "No: [+1] and [−1] have different fractions"], 1, "It is a different tangle in general.")])

node("TangleDiagram.rotate", "Rotate a quarter turn",
 "**The surprise:** turning a tangle 90° touches only the four corner labels. The crossing data is local, so nothing else in the code moves.",
 r"""
## Plain English

**Definition (`TangleDiagram.rotate`, Tangle.lean lines 87-88).** Counterclockwise 90°: the corners cycle NW ← NE ← SE ← SW ← NW. Crossings are unchanged. F(Tʳ) = −1/F(T).
""",
 [q("What changes under `rotate`?", ["Only the corner labels", "Every crossing sign", "The arc numbers"], 0, "`{ T with NW := T.NE, NE := T.SE, SE := T.SW, SW := T.NW }`."),
  q("Rotating [0] gives?", ["[0]", "[∞]", "[1]"], 1, "`rotate_zero : TangleDiagram.zero.rotate = TangleDiagram.infinity`."),
  q("What does rotation do to the fraction?", ["x ↦ −1/x", "x ↦ x + 1", "nothing"], 0, "F(Tʳ) = −1/F(T) (Kauffman–Lambropoulou).")])

node("TangleDiagram.invert", "Inversion Tⁱ: rotate, then mirror",
 "**The surprise:** inversion is the reciprocal. Rotating gives −1/x and mirroring negates, so Tⁱ has fraction 1/F(T).",
 r"""
## Plain English

**Definition (`TangleDiagram.invert`, Tangle.lean lines 92-93).** `T.rotate.mirror` ([`rotate`](#/node/TangleDiagram.rotate), then [`mirror`](#/node/TangleDiagram.mirror)), the paper's Tⁱ = −Tʳ. F(Tⁱ) = 1/F(T). Inverting [n] gives the vertical twist 1/[n].
""",
 [q("How is inversion defined?", ["Mirror then add [0]", "Rotate 90° counterclockwise, then mirror", "Rotate 180°"], 1, "`def invert (T) := T.rotate.mirror`."),
  q("What is F(Tⁱ)?", ["F(T)", "1/F(T)", "−F(T)"], 1, "−(−1/x) = 1/x."),
  q("Is inversion used by the coloring-safe moves?", ["Only for single crossings (`invert_unit`)", "Always"], 0, "General `invert_cong`/`invert_add`/`invert_mul` are excluded from ColoringIsotopy.")])

node("TangleDiagram.rot180", "Planar half-turn",
 "**The surprise:** a half-turn in the plane keeps every crossing sign. For rational tangles it is an isotopy (the flipping lemma), but for general tangles it need not be, and that gap matters for the flype move.",
 r"""
## Plain English

**Definition (`TangleDiagram.rot180`, Flip.lean lines 45-50).** Rotate every crossing 180° in the plane (signs kept) and swap corners NW ↔ SE, NE ↔ SW. It equals the horizontal flip followed by the vertical flip.

The flipping lemma (`flipping_lemma`, FlippingLemma.lean lines 470-477) says a rational tangle is isotopic to its half-turn. The move `flype_slide_add` in [`Isotopic`](#/node/Isotopic) uses `t.rot180` for **every** t. Classically the flype gives the single flip t^h, which differs from the half-turn by one more flip. The Claude audit flags that this may make `Isotopic` too generous for non-rational t.
""",
 [q("Does the half-turn change crossing signs?", ["Yes", "No"], 1, "`crossings := T.crossings.map Crossing.rotate180`; `rotate180` keeps the sign."),
  q("Where does NW go?", ["To NE", "To SE", "Nowhere"], 1, "`NW := T.SE`, `SE := T.NW`."),
  q("For which tangles is T isotopic to its half-turn classically?", ["All 2-tangles", "Rational tangles (flipping lemma)", "None"], 1, "The repo's Flip.lean says flips 'need not be an isotopy of 2-tangles. For rational tangles it is'.")])

# ---------------------------------------------------------------- recipes and fractions
node("TwistExpr", "Twist recipes: build a tangle one crossing at a time",
 "**The surprise:** every rational tangle comes from a recipe that only ever glues one crossing on: left or right, top or bottom. The fraction belongs to the recipe, and the theorems compare recipes.",
 r"""
## Plain English

**Definition (`TwistExpr`, Rational.lean lines 27-36).** A recipe starts from [0], [∞], [+1] or [−1] and repeatedly

* adds a crossing on the right (`addRight`) or the left (`addLeft`), or
* multiplies by a crossing at the bottom (`mulBottom`) or on top (`mulTop`).

Each step carries a [sign](#/node/CrossingSign). [`diagram`](#/node/TwistExpr.diagram) builds the PD-code; [`fraction`](#/node/TwistExpr.fraction) computes the number.

A diagram is **rational** when it is [`Isotopic`](#/node/Isotopic) to the diagram of some recipe (`IsRational`, Rational.lean lines 107-108).
""",
 [q("How many crossings does each recipe step glue on?", ["One", "Two", "Any number"], 0, "Each constructor takes a `CrossingSign` and glues `crossingTangle s`."),
  q("Which of these is not a recipe step?", ["addLeft", "mulTop", "addRight", "mirror"], 3, "The constructors are zero, infinity, one, negOne, addRight, addLeft, mulBottom, mulTop."),
  q("Are the headline theorems about recipes or about tangles up to isotopy?", ["Recipes (TwistExpr)", "Tangles up to isotopy"], 0, "They quantify over `e₁ e₂ : TwistExpr`.")])

node("TwistExpr.diagram", "The diagram of a recipe",
 "**The surprise:** turning a recipe into a picture is just repeated gluing with + and *, so every twist diagram's code is produced by the same honest operations, never hand-written.",
 r"""
## Plain English

**Definition (`TwistExpr.diagram`, Rational.lean lines 41-49).** [0], [∞], [+1] and [−1] give their diagrams. `addRight e s` gives `e.diagram + [s]`, `addLeft e s` gives `[s] + e.diagram`, `mulBottom e s` gives `e.diagram * [s]` and `mulTop e s` gives `[s] * e.diagram` ([`add`](#/node/TangleDiagram.add), [`mul`](#/node/TangleDiagram.mul), [`crossingTangle`](#/node/crossingTangle)).
""",
 [q("What is `(addLeft e s).diagram`?", ["e.diagram + [s]", "[s] + e.diagram", "e.diagram * [s]"], 1, "`| addLeft e s => crossingTangle s + e.diagram`."),
  q("What is `(mulBottom e s).diagram`?", ["e.diagram * [s]", "[s] * e.diagram"], 0, "Bottom multiplication puts [s] below."),
  q("How many crossings does a recipe with n steps from [0] have?", ["n", "2n", "0"], 0, "Each step adds one crossing.")])

node("TwistExpr.fraction", "The fraction of a recipe (with a top-product slip)",
 "**The surprise:** the formula for a top product is off: it gives 1/(s + F) where the Conway product needs 1/(s + 1/F). That's why the classification headlines exclude top products.",
 r"""
## Plain English

**Definition (`TwistExpr.fraction`, TangleFraction.lean lines 30-38).** Evaluate the recipe in ℚ ∪ {∞} ([`CFValue`](#/node/CFValue)):

* [0] ↦ 0, [∞] ↦ ∞, [±1] ↦ ±1;
* adding [s] on either side: F ↦ F + s;
* multiplying [s] at the bottom: F ↦ 1/(1/F + s).

**Worked example.** Start at [0], add [+1] three times: 3. Multiply [+1] at the bottom: 1/(1/3 + 1) = 3/4. Add [+1]: **7/4**.

### The top product

The code says `mulTop e s ↦ (s.cfValue.inv.add e.fraction).inv`, that is 1/(1/s + F) = 1/(s + F). The Conway product [s] * T has 1/F = 1/s + 1/F(T), so the right value is 1/(s + 1/F). The two agree only when F = ±1. The repo knows this: its standard-form rewrite gives the right value ([`toStandard`](#/node/TwistExpr.toStandard)). The classification headlines assume [`noMulTop`](#/node/TwistExpr.noMulTop), where the formula is right.

Example: [+1] * [0] is a kink on top of two arcs and isotopes to [0], fraction 0. The formula gives 1/(1 + 0) = 1.
""",
 [q("Start at [0], add [+1] twice, then multiply [+1] at the bottom. Fraction?", ["3", "2/3", "1/3", "3/2"], 1, "2, then 1/(1/2 + 1) = 2/3."),
  q("For which recipes is `TwistExpr.fraction` the Conway fraction?", ["All recipes", "Recipes without top products (noMulTop)", "Only standard forms"], 1, "The `mulTop` clause misses an inverse; on noMulTop recipes it agrees with the standard-form value (`fraction_eq_toStandard_of_noMulTop`)."),
  q("What does adding [−1] do to the fraction?", ["Subtracts 1", "Inverts it", "Nothing"], 0, "`addRight e s => e.fraction.add s.cfValue` with value −1.")],
 caveats=["On recipes containing `mulTop`, this function is not the tangle fraction (Claude audit, §3). Headlines 1 and 2 assume `noMulTop`; headlines 3 and 4 use `toStandard.fraction` instead."])

node("CFValue", "Fractions with infinity: ℚ ∪ {∞}",
 "**The surprise:** there is one infinity, not two: −∞ = ∞. Tangle fractions live on the projective line, where 1/0 is a perfectly good value (the tangle [∞]).",
 r"""
## Plain English

**Definition (`CFValue`, ContinuedFraction.lean lines 35-38).** Either a rational `ofRat q` or `inf`. Arithmetic: [`inv`](#/node/CFValue.inv) sends 0 ↦ ∞ and ∞ ↦ 0; [`add`](#/node/CFValue.add) makes ∞ absorbing; negation fixes ∞.
""",
 [q("What is 1/0 in CFValue?", ["Undefined", "inf", "0"], 1, "`inv (ofRat 0) = inf`."),
  q("What is ∞ + 3?", ["∞", "3", "undefined"], 0, "`| inf, _ => inf`."),
  q("What is −∞?", ["−∞, a separate value", "∞ itself"], 1, "`neg inf = inf` (one point at infinity).")])

node("CFValue.add", "Adding fractions with ∞",
 "**The surprise:** ∞ + x = ∞ matches the picture: adding a twist beside [∞] makes a kink that untwists back to [∞].",
 r"""
## Plain English

**Definition (`CFValue.add`, ContinuedFraction.lean lines 52-55).** Rationals add as usual; if either side is ∞, the result is ∞.
""",
 [q("What is ∞ + (−1)?", ["∞", "−1", "0"], 0, "∞ is absorbing."),
  q("What is 1/2 + 1/3?", ["5/6", "2/5", "1/6"], 0, "Ordinary rational addition."),
  q("Why is ∞ + 1 = ∞ geometrically sensible?", ["[∞] + [1] is a kink, isotopic to [∞]", "It isn't"], 0, "Reidemeister I removes the kink.")])

node("CFValue.inv", "Reciprocal with 1/0 = ∞",
 "**The surprise:** the reciprocal is total here: 1/0 = ∞ and 1/∞ = 0, exactly what inverting [0] into [∞] and back requires.",
 r"""
## Plain English

**Definition (`CFValue.inv`, ContinuedFraction.lean lines 47-49).** q ↦ 1/q for q ≠ 0; 0 ↦ ∞; ∞ ↦ 0.
""",
 [q("What is inv 0?", ["0", "∞", "undefined"], 1, "`if q = 0 then inf`."),
  q("What is inv ∞?", ["0", "∞", "1"], 0, "`| inf => ofRat 0`."),
  q("What is inv (−2)?", ["2", "−1/2", "1/2"], 1, "Ordinary reciprocal.")])

node("TwistExpr.noMulTop", "No top products",
 "**The surprise:** forbidding just one of the four recipe steps loses no fractions at all (standard forms never use it), yet it is exactly what makes the recipe fraction trustworthy.",
 r"""
## Plain English

**Definition (`TwistExpr.noMulTop`, Rational.lean lines 83-86).** True if the recipe never uses `mulTop`; additions on either side and bottom products are allowed.

Every standard form (right additions and bottom products only) satisfies it, so every value in ℚ ∪ {∞} is reached. On these recipes [`fraction`](#/node/TwistExpr.fraction) equals the standard-form value ([`fraction_eq_toStandard_of_noMulTop`](#/node/TwistExpr.fraction_eq_toStandard_of_noMulTop)).
""",
 [q("Which step is forbidden?", ["addLeft", "mulTop", "mulBottom"], 1, "`| mulTop _ _ => False`."),
  q("Are left additions allowed?", ["Yes", "No"], 0, "`| addRight e _ | addLeft e _ | mulBottom e _ => e.noMulTop`."),
  q("Why does it matter for the headlines?", ["It's purely cosmetic", "On recipes with top products the recipe fraction is not the Conway fraction"], 1, "See the `mulTop` clause of `TwistExpr.fraction`.")],
 caveats=["Load-bearing for the *meaning* of headlines 1 and 2, not just their proofs (Claude audit, §3)."])

node("TwistExpr.slideReady", "slideReady: no gluing onto a bare strand",
 "**The surprise:** the excluded cases are real: adding a crossing on the left of [∞] (a kink) breaks the diagonal coloring rule, and the repo proves it fails there.",
 r"""
## Plain English

**Definition (`TwistExpr.slideReady`, ColoringToStandard.lean lines 72-76).** Every `addLeft` step needs the inner diagram's NW and SW corners on **different** arcs. Every `mulTop` step needs its NW and NE on different arcs. Right additions and bottom products are unrestricted.

Same arc at NW and SW means a bare vertical strand runs down the left side (as in [∞]). Gluing a crossing there makes a kink. The Lean proves the diagonal rule fails in exactly those cases (`not_diagonal_addLeft_infinity`, `not_diagonal_mulTop_zero`, DiagonalSumGeneral.lean lines 198-251).
""",
 [q("What does `addLeft e s` require?", ["e.diagram.NW ≠ e.diagram.SW", "e.diagram.NW ≠ e.diagram.NE", "nothing"], 0, "`| addLeft e _ => e.diagram.NW ≠ e.diagram.SW ∧ e.slideReady`."),
  q("Is every standard form slideReady?", ["Yes: right additions and bottom products are unrestricted", "No"], 0, "Only `addLeft` and `mulTop` carry conditions."),
  q("Which example breaks the diagonal rule?", ["[0] + [1]", "[1] + [∞] (adding on the left of [∞])", "[1] + [1]"], 1, "`not_diagonal_addLeft_infinity`.")])

node("TwistExpr.toStandard", "Rewrite a recipe in standard form",
 "**The surprise:** to put a recipe in standard form, you just relabel each left addition as a right one and each top product as a bottom one. The real work is proving the diagram doesn't change, which takes flypes.",
 r"""
## Plain English

**Definition (`TwistExpr.toStandard`, FlippingLemma.lean lines 481-489).** Turn `addLeft` into `addRight` and `mulTop` into `mulBottom` (keeping signs). [±1] becomes [0] + [±1]. The result is a [`StandardExpr`](#/node/StandardExpr).

That the diagram stays isotopic is `TwistExpr.toStandard_isotopic`: each relabelling is a flype plus the flipping lemma.
""",
 [q("What does `toStandard` do with `addLeft e s`?", ["Deletes it", "Makes it `addRight (toStandard e) s`", "Makes it mulTop"], 1, "`| addLeft e s => .addRight e.toStandard s`."),
  q("What does `one` become?", ["`.addRight .zero .pos` ([0] + [+1])", "`.zero`"], 0, "Standard forms start from [0] or [∞]."),
  q("Why is the rewritten diagram isotopic?", ["It is the same code", "By flypes moving the crossing across", "It isn't"], 1, "`TwistExpr.toStandard_isotopic` uses `flype_add`/`flype_mul`.")])

node("StandardExpr", "Standard form: right additions and bottom products",
 "**The surprise:** standard forms are continued fractions in disguise: runs of right additions are the terms, and each bottom product starts a new level.",
 r"""
## Plain English

**Definition (`StandardExpr`, StandardForm.lean lines 22-27).** Start from [0] or [∞]; then add [±1] on the right or multiply [±1] at the bottom, repeatedly. That is Kauffman–Lambropoulou's Definition 4.
""",
 [q("Which steps are allowed?", ["Right additions and bottom products", "All four", "Only additions"], 0, "Constructors: zero, infinity, addRight, mulBottom."),
  q("Can a standard form start from [+1]?", ["Yes", "No: it starts from [0] or [∞]; [+1] is [0] + [+1]"], 1, "There is no `one` constructor."),
  q("Is every standard form slideReady and noMulTop?", ["Yes", "No"], 0, "Neither condition restricts right additions or bottom products.")])

node("StandardExpr.fraction", "The fraction of a standard form",
 "**The surprise:** this is the trustworthy fraction: headlines 3 and 4 state their F this way (after rewriting into standard form), so they avoid the top-product slip in the recipe fraction.",
 r"""
## Plain English

**Definition (`StandardExpr.fraction`, ColorFraction.lean lines 627-633).** [0] ↦ 0, [∞] ↦ ∞, right addition of [±1]: F ↦ F ± 1, bottom product: F ↦ 1/(1/F ± 1).
""",
 [q("Bottom product by [−1] sends F to?", ["F − 1", "1/(1/F − 1)", "−F"], 1, "`(e.fraction.inv.add (.ofInt (-1))).inv`."),
  q("Fraction of [0] + [+1] + [+1]?", ["2", "1/2", "0"], 0, "0 + 1 + 1."),
  q("Which headlines use this fraction?", ["The coloring headlines (3 and 4)", "None"], 0, "They state `e.toStandard.fraction`.")])
