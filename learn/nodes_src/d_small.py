# Smaller supporting definitions.
import importlib.util, os
_h = importlib.util.spec_from_file_location("_h", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a_headlines.py"))
_m = importlib.util.module_from_spec(_h); _h.loader.exec_module(_m)
q = _m.q
NODES = []
def node(id, title, summary, body, quiz, caveats=(), widgets=None):
    NODES.append(dict(id=id, title=title, summary=summary, body=body, quiz=quiz, caveats=list(caveats), widgets=widgets))

node("StandardExpr.diagram", "The diagram of a standard form",
 "**The surprise:** a standard form's picture is built with only two of the four gluing moves, right addition and bottom product, and that's enough for every rational tangle.",
 "\n## Plain English\n\n**Definition (`StandardExpr.diagram`, StandardForm.lean lines 32-36).** [0] and [∞] as themselves; `addRight e s` ↦ `e.diagram + [s]`; `mulBottom e s` ↦ `e.diagram * [s]` ([`add`](#/node/TangleDiagram.add), [`mul`](#/node/TangleDiagram.mul)).\n",
 [q("What is `(mulBottom e s).diagram`?", ["e.diagram * [s]", "[s] * e.diagram"], 0, "Bottom product puts [s] below."),
  q("Which gluing moves are used?", ["Right addition and bottom product", "All four"], 0, "Only two constructors glue."),
  q("What does `zero` give?", ["[0]", "[∞]", "[+1]"], 0, "`| zero => TangleDiagram.zero`.")])

node("IsReidemeisterI", "Reidemeister I: add or remove a kink",
 "**The surprise:** a kink is a crossing where one arc appears twice: the loop's arc. Removing it means deleting that crossing and merging the two remaining arcs.",
 "\n## Plain English\n\n**Definition (`IsReidemeisterI`, Reidemeister.lean lines 288-289).** One of D, E is the other with one kink added: a crossing whose loop port is collapsed by `collapseKink`, up to [planar isotopy](#/node/PlanarIsotopy).\n",
 [q("Is R1 symmetric here?", ["Yes: either diagram may have the extra kink", "No"], 0, "`IsReidemeisterIAdd D E ∨ IsReidemeisterIAdd E D`."),
  q("How many crossings does a kink have?", ["1", "2", "3"], 0, "One crossing with a loop."),
  q("In ColoringIsotopy, what else does R1 need?", ["WellFormed on both sides", "Nothing"], 0, "`ColoringIsotopy.r1`.")])

node("IsReidemeisterII", "Reidemeister II: two opposite crossings",
 "**The surprise:** [+1] + [−1] untwists to [0] by one R2 move. Its PD-code check is one of the six facts the repo proves with native_decide.",
 "\n## Plain English\n\n**Definition (`IsReidemeisterII`, Reidemeister.lean lines 349-350).** One of D, E has an extra pair of crossings forming a bigon (`IsR2Pair`) whose collapse (`collapseR2`) gives the other, up to planar isotopy.\n",
 [q("How many crossings does an R2 move remove?", ["1", "2", "3"], 1, "An R2 pair."),
  q("Which tangle reduces to [0] by R2?", ["[+1] + [−1]", "[+1] + [+1]"], 0, "Opposite crossings cancel."),
  q("Is R2 symmetric here?", ["Yes", "No"], 0, "`IsReidemeisterIIAdd D E ∨ IsReidemeisterIIAdd E D`.")])

node("IsReidemeisterIII", "Reidemeister III: slide a strand over a crossing",
 "**The surprise:** the repo has two versions of R3: this indexed one is used by Isotopic, and a separate local model is used for colorings, with no lemma linking them.",
 "\n## Plain English\n\n**Definition (`IsReidemeisterIII`, Reidemeister.lean lines 425-471).** Three crossings forming a triangle in D are replaced by the slid triangle in E, matching the rest of the diagram by an injective renaming. The coloring proof uses [`IsReidemeisterIIILocal`](#/node/IsReidemeisterIIILocal).\n",
 [q("How many crossings does R3 involve?", ["2", "3", "4"], 1, "A triangle of three."),
  q("Which R3 does ColoringIsotopy use?", ["IsReidemeisterIIILocal", "IsReidemeisterIII"], 0, "`r3Local`."),
  q("Does the number of crossings change?", ["No", "Yes"], 0, "R3 slides a strand; the count stays 3.")])

node("IsReidemeisterIIILocal", "The local R3 model used for colorings",
 "**The surprise:** this is the one coloring-safe move with no bridge to Isotopic in the repo, so ColoringIsotopy ⊆ Isotopic is not yet a theorem.",
 "\n## Plain English\n\n**Definition (`IsReidemeisterIIILocal`, Reidemeister.lean lines 480-499).** An over-slide R3 on a triangle whose internal arcs are not corners and touch nothing else, with signs kept and the rest matched by an injective renaming.\n",
 [q("Is there a lemma turning it into `IsReidemeisterIII`?", ["No", "Yes"], 0, "Claude audit, §1."),
  q("Can the triangle's internal arcs be corner arcs?", ["No", "Yes"], 0, "`uE ≠ E.NW ∧ …`."),
  q("Are signs preserved?", ["Yes", "No"], 0, "`PD.sign = PE.sign ∧ …`.")])

node("Crossing.switch", "Switch a crossing",
 "**The surprise:** switching over and under is a port shift by one plus a sign flip. That one-port shift is what stops colorings carrying over.",
 "\n## Plain English\n\n**Definition (`Crossing.switch`, Tangle.lean lines 45-46).** Ports rotate by one (so the old under-strand sits on ports 0 and 2) and the sign flips. Used by [`mirror`](#/node/TangleDiagram.mirror).\n",
 [q("What happens to the sign?", ["It flips", "It stays"], 0, "`sign := C.sign.flip`."),
  q("Which arc is now at port 0?", ["Old a1", "Old a0"], 0, "`a0 := C.a1`."),
  q("Switching twice gives?", ["The crossing rotated 180°", "The original exactly"], 0, "`switch_switch : C.switch.switch = C.rotate180`.")])

node("Crossing.rotate180", "Turn a crossing 180° in the plane",
 "**The surprise:** a half-turn swaps the two over-ports and the two under-ports but keeps the sign. It's the same crossing, so planar isotopy allows it.",
 "\n## Plain English\n\n**Definition (`Crossing.rotate180`, Reidemeister.lean lines 102-103).** (a0, a1, a2, a3) ↦ (a2, a3, a0, a1), same sign.\n",
 [q("Is the sign kept?", ["Yes", "No"], 0, "`sign := C.sign`."),
  q("Where does a0 go?", ["To port 2", "To port 1"], 0, "`a2 := C.a0`."),
  q("Is it allowed by planar isotopy?", ["Yes", "No"], 0, "`sameUpToRotation` includes it.")])

node("ArithmeticCF.value", "The value of a continued fraction",
 "**The surprise:** [a₁, …, aₙ] is evaluated from the inside out with the same ∞-aware arithmetic as tangles, so [0] terms and 1/0 never cause trouble.",
 "\n## Plain English\n\n**Definition (`ArithmeticCF.value`, ContinuedFraction.lean lines 346-347).** a₁ + 1/(a₂ + 1/(… + 1/aₙ)) in [`CFValue`](#/node/CFValue) (`valueOfList`).\n",
 [q("Value of [1, 1, 3]?", ["7/4", "5", "4/7"], 0, "1 + 1/(1 + 1/3) = 1 + 3/4."),
  q("Value of [3]?", ["3", "1/3"], 0, "A single term."),
  q("Which arithmetic is used?", ["CFValue (with ∞)", "Floats"], 0, "`valueOfList` returns a CFValue.")])
