# Claude audit of the headline statements

**Scope and method.** I read only the Lean sources under `src/RationalTangles/` and the blueprint notes; I edited nothing and built nothing. There is no `.lake/` directory in this worktree and `lean-toolchain` pins `leanprover/lean4:v4.32.2`, which the README says is not installed here — **so I cannot verify that any of this code compiles or elaborates**, and every statement below about what is "proved" means "the file contains a complete-looking tactic/term proof with no `sorry`", not "the kernel accepted it."

Classical target: Kauffman–Lambropoulou 2004 (arXiv:math/0311499) Theorem 1 (Conway 1970), with Theorem 2 (F is an isotopy invariant), Theorem 3 (same fraction ⇒ isotopic), Theorem 4 (the coloring fraction f is an isotopy invariant and f = F).

---

## 0. Mechanical integrity scan

| Probe | Result |
|---|---|
| `sorry` | none in `src/` |
| `admit` | none |
| `axiom` declarations | none |
| `implemented_by` / `@[extern]` / `unsafe` | none |
| `native_decide` | **6 uses, all in `src/RationalTangles/ContinuedFractionFormExists.lean`** (lines 32, 37, 353, 358, 363, 368) |
| `decide` | many, all on small decidable PD-code / `Fin`/`Rat` goals — kernel-checked, not a soundness concern |

The six `native_decide` calls discharge PD-code computations:

- `one_add_negOne_crossings`, `collapseR2_one_negOne_eq` (the R2 cancellation `[+1]+[-1] ∼ [0]`),
- `infinity_add_one_crossings`, `infinity_add_negOne_crossings`, `collapseKink_infinity_add_one`, `collapseKink_infinity_add_negOne` (the R1 kinks `[∞]+[±1] ∼ [∞]`).

Each of these makes the enclosing theorem depend on `Lean.ofReduceBool`, i.e. on the trusted compiler/evaluator rather than the kernel. See §6 for which headlines inherit that.

---

## 1. `rational_classification_fragment` vs Theorem 1

`src/RationalTangles/DiagonalSumGeneral.lean:584`

```lean
theorem rational_classification_fragment {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.fraction = e₂.fraction ∧
      Isotopic e₁.diagram e₂.diagram
```

**What it proves.** *Given* that two twist-form expressions' PD-codes are already related by a `ColoringIsotopy` path, and that both expressions avoid top products and satisfy the port side-conditions, their algebraic fractions coincide, and their diagrams are `Isotopic`.

**What it does not prove.** It is not an iff, and it is not even an implication in the classical shape. Theorem 1 says `Isotopic T S ↔ F T = F S`. Here:

- there is no `→` direction from `Isotopic` to equal fractions anywhere in the repository (`Isotopic`-invariance of `F` is explicitly not claimed — see the file's own docstring and the blueprint);
- there is no `→` direction from equal fractions to `ColoringIsotopy`;
- the two conjuncts are *both consequents of one hypothesis*, so the statement does not relate any single equivalence relation to the fraction. What it actually composes is: `ColoringIsotopy ⇒ equal F` (a small-relation invariance) and `equal F ⇒ Isotopic` (a large-relation reconstruction). Those two never close into an iff, for either relation.

**Is the second conjunct already implied by the hypothesis?** Essentially yes, in spirit. Of `ColoringIsotopy`'s 17 constructors, 16 map directly onto `Isotopic` generators (`refl`, `trans`, `r1`/`r2` → `.step (.r1/.r2)`, `localFlype` → `.flype`, `isotopy` → `.step (.isotopy)`, the four congruences, `add_zero`, `zero_add` and the `_rev`/`invert_unit_rev` variants via `Isotopic.symm`, both `assoc`s). The only constructor without a bridge in the repo is `r3Local` (`IsReidemeisterIIILocal` is never converted to `IsReidemeisterIII`; only `.symm` exists for it). So `ColoringIsotopy ⊆ Isotopic` is one missing lemma away from being free, and the second conjunct carries almost no information beyond the hypothesis. The proof does not take that route — it goes the long way through `twist_same_fraction_isotopic_of_noMulTop` (canonical form) — but as a *statement* the conjunct is close to vacuous given `h`.

**Every restriction.** (i) `TwistExpr` expressions, not arbitrary rational tangles or arbitrary diagrams — the fraction is attached to a *parse*, not to a tangle; (ii) `noMulTop`: no `mulTop` node anywhere (see §3 — this is not cosmetic); (iii) `slideReady`: every `addLeft` node needs `inner.NW ≠ inner.SW` and every `mulTop` node needs `inner.NW ≠ inner.NE` (excludes left-adding onto the `[∞]` family and top-multiplying onto the `[0]` family; the repo refutes the diagonal rule in exactly those cases: `not_diagonal_addLeft_infinity`, `not_diagonal_mulTop_zero`); (iv) hypothesis is `ColoringIsotopy`, a *directed* relation with no `symm` constructor, missing `flype_slide_*`, `rot180_*`, `mirror_cong`, `invert_*`, `transfer_*`; (v) conclusion's `Isotopic` is the repo's generated relation, see §5.

---

## 2. `twist_same_fraction_isotopic_of_noMulTop` vs Theorem 3

`src/RationalTangles/CanonicalFormUnique.lean:126`

```lean
theorem twist_same_fraction_isotopic_of_noMulTop {e₁ e₂ : TwistExpr}
    (hn₁ : e₁.noMulTop) (hn₂ : e₂.noMulTop)
    (hf : e₁.fraction = e₂.fraction) :
    Isotopic e₁.diagram e₂.diagram
```

**What it proves.** Real mathematical content, and the strongest of the four. For any two top-product-free twist expressions with the same `CFValue` (finite or `∞`), the two PD-codes are related by an explicit chain: `toStandard_isotopic` (Figure 5 slides + the derived twist-level flipping lemma) → `StandardExpr.toCF_isotopic` → the continued-fraction reduction `cf_to_canonical` (transfer moves, R1/R2 cancellations) → uniqueness of canonical form `canonical_tangle_eq_of_value` (which is a PD-code *equality*, a genuinely strong uniqueness statement). Notably this is not vacuous in coverage: `rightBottom ⇒ noMulTop` and every `rightBottom` expression is automatically `slideReady`, so the class contains all standard forms, hence realizes every value in `ℚ ∪ {∞}`.

**What it does not prove.** Theorem 3 is about *rational tangles*: given rational diagrams `T`, `S` with `F(T) = F(S)`, they are isotopic. Here the hypothesis is equality of the fraction of two *syntactic expressions*; there is no step from a rational diagram to a canonical parse of it. `IsRational T` is `∃ e, Isotopic T e.diagram`, and the companion results (`IsTwistForm.exists_unique_fraction_noMulTop`) only make `F` a function of the PD-code for `noMulTop`+`slideReady` parses of the *same* code — not of the isotopy class. So "the fraction of a rational tangle" is still undefined in this development, and Theorem 3's quantifier over tangles is not reached. `noMulTop` is a real restriction on *expressions* (though not on values): expressions with top products are handled only under `unitMulTop` (inner fraction `±1`) in `MulTopNormalize.lean`.

**Restrictions.** `TwistExpr` expressions; `noMulTop` on both sides (needed because `TwistExpr.fraction` is only the Conway fraction there, §3); the conclusion is the repo's `Isotopic`, whose witness here uses the assumed generators `flype_slide_add/mul`, `rot180_*`, `invert_cong`, `invert_add`, `invert_mul`, `mirror_cong`, `transfer_odd(_neg)` (§5); the proof chain reaches `native_decide` lemmas (§6). No `slideReady` is needed — this half is coloring-free.

---

## 3. A definitional finding: `TwistExpr.fraction` is the Conway fraction only on `noMulTop`

`src/RationalTangles/TangleFraction.lean:30`

```lean
def fraction : TwistExpr → CFValue
  | ...
  | mulBottom e s => (e.fraction.inv.add s.cfValue).inv
  | mulTop    e s => (s.cfValue.inv.add e.fraction).inv
```

For the Conway product, reciprocals add: `1/F(T*S) = 1/F(T) + 1/F(S)`. With `s = ±1` (so `1/s = s`), `mulBottom` gives `1/(1/F(e) + s)` ✓. But `mulTop` gives `1/(s + F(e))`, where the correct value is `1/(s + 1/F(e))`. These agree exactly when `F(e) = 1/F(e)`, i.e. `F(e) = ±1` — which is precisely the hypothesis of `TwistExpr.mulTop_comm_of_unit_fraction` / `unitMulTop`. The repo is internally consistent and candid about this ("blocker (b)", `MulTopNormalize.lean:21`), but the consequence for an auditor is sharper than "a convenience hypothesis": **on expressions containing `mulTop`, `TwistExpr.fraction` is not the tangle fraction at all**, so `noMulTop` is load-bearing for the *meaning*, not just the proof, of headlines 1 and 2. Any public wording must not suggest `noMulTop` is a technicality that merely postpones work.

Separately, headlines 3 and 4 state their fraction as `e.toStandard.fraction` (the right-and-bottom re-evaluation of the rewritten expression), not `e.fraction`; the two coincide on `noMulTop` (`fraction_eq_toStandard_of_noMulTop`) and can differ otherwise.

---

## 4. `coloring_fraction_invariant_ColoringIsotopy` vs Theorem 2

`src/RationalTangles/DiagonalSumGeneral.lean:368`

```lean
theorem coloring_fraction_invariant_ColoringIsotopy {e₁ e₂ : TwistExpr}
    (hok₁ : e₁.slideReady) (hok₂ : e₂.slideReady)
    (h : ColoringIsotopy e₁.diagram e₂.diagram) :
    e₁.toStandard.fraction = e₂.toStandard.fraction ∧
      ∀ v : CFValue, HasColoringFraction e₁.diagram v →
        HasColoringFraction e₂.diagram v
```

where `HasColoringFraction D v := ∃ col, D.IsColored col ∧ (ColorMatrix.of D col).NotMono ∧ (ColorMatrix.of D col).fraction = v` (`ColorFractionUnique.lean:3709`), `IsColored` is the purely local rule `col a0 = col a2 ∧ col a1 + col a3 = 2 * col a0` at every crossing, and `ColorMatrix.fraction M = if M.NE - M.SE = 0 then ∞ else (M.NE - M.NW)/(M.NE - M.SE)` (calibrated correctly: `[0] ↦ 0`, `[∞] ↦ ∞`).

**What it proves.** Along any `ColoringIsotopy` path between two `slideReady` twist diagrams, the standard-form fraction is the same, and every value realized as a coloring fraction on the source is realized on the target. All coloring hypotheses are discharged internally (via `colorFrom 0 1` and `twist_coloring_diagonal_slideReady`), so only structural hypotheses remain — that is genuinely nice. The transport engine `coloring_ColoringIsotopy` (`ColoringIsotopy.lean:2049`) is a full induction over every `ColoringIsotopy` constructor, including R1, R2, local R3 and local flypes, so the covered move set is substantive, not toy.

**What it does not prove.** Theorem 2 is invariance of `F` under *isotopy*. This is invariance under `ColoringIsotopy`, which is:

- **not `Isotopic`**: it omits `flype_slide_add/mul`, `rot180_cong/_add/_mul`, `mirror_cong`, `invert_cong/_add/_mul`, `transfer_odd(_neg)`, and the switched algebraic `Flype`. Several of those transports are *refuted* in the same file for color-matrix-preserving transport (`not_coloring_mirror_transport`, `not_coloring_invert_transport`), so this is a permanent boundary of the coloring method as set up, not a to-do list;
- **not symmetric**: `ColoringIsotopy` has no `symm` constructor (the file says a full `symm` is not proved; `ReversibleColoringIsotopy` is the symmetric sub-fragment). So this is invariance along a *directed* relation, and the second conjunct is one-directional (`e₁ → e₂` only);
- indexed R3 appears only through the local model `r3Local`;
- `r1`/`r2` additionally require `WellFormed` on both endpoints — and the repo proves `WellFormed` for *nothing* (see §5), so those two constructors are only usable where a caller supplies the hypothesis.

Also note the first conjunct is about `toStandard.fraction`, and `slideReady` is required on both sides.

---

## 5. `Isotopic` as a model of tangle isotopy

Definitions read: `TangleDiagram` (`Reidemeister.lean:177`), `PlanarIsotopy`, `IsReidemeisterI/II/III(Local)`, `ReidemeisterMove`, `Isotopic` and `ColoringIsotopy` (`Flype.lean:121`, `:217`), `IsLocalFlype`, `TwistExpr`, `TwistExpr.fraction`, `CFValue`, `slideReady`, `noMulTop`, `HasColoringFraction`, `IsColored`.

**Which constructors are primitive assumptions rather than derived from Reidemeister moves.** `Isotopic` has exactly four "honest" sources — `refl`, `trans`, `symm`, and `step` of a `ReidemeisterMove` (R1/R2/R3/planar). Everything else is an assumed move:

1. `flype` (`IsLocalFlype`) and 2. `flype_slide_add` / 3. `flype_slide_mul` — Figure 5;
4. `add_left/add_right/mul_left/mul_right`, 5. `rot180_cong`, 6. `invert_cong`, 7. `mirror_cong` — congruences (unproblematic: applying a global symmetry or a context to an isotopy is an isotopy);
8. `rot180_add`, `rot180_mul`, `add_assoc`, `mul_assoc`, `zero_add`, `add_zero`, `invert_add`, `invert_mul` — planar/reindexing identities of the operations (all true for arbitrary 2-tangles);
9. `invert_unit` (`[±1] ∼ [±1]ⁱ`) — classical and true;
10. `transfer_odd`, `transfer_odd_neg` — KL Figure 14, asserted for **arbitrary** `T : TangleDiagram`.

Fraction arithmetic is consistent with all of them (e.g. `transfer_odd`: `(x−1)` then `*[+1]` gives `(x−1)/x`, and `[+1] + (−T)ⁱ` gives `1 − 1/x` ✓), so none is obviously fraction-breaking.

**Could these make `Isotopic` coarser than real isotopy?** Yes — one spot is concerning enough to name, and the repository's own comments supply the evidence.

- `Flip.lean:20` states plainly: "In general a flip switches endpoints and need not be an isotopy of 2-tangles. For rational tangles it is, by the flipping lemma."
- `Flip.lean:45` defines `rot180` as the planar half-turn and proves `rot180 = hflip ∘ vflip` — *two* spatial flips.
- `Flype.lean:56` records "the paper's switched algebraic identity" as `Flype (one.add t) (t.hflip.add one)` — *one* flip — and deliberately **does not** use it as an `Isotopic` generator, substituting `flype_slide_add : Isotopic (crossingTangle s + t) (t.rot180 + crossingTangle s)` for all `t`, with the stated justification being coloring transport ("a switch flips signs"), not topology.

So the generator differs from the identity the file attributes to Figure 5 by exactly one flip of `t`, quantified over *arbitrary* `t`. At most one of the two forms can be a valid isotopy for arbitrary `t`: if the paper's one-flip form is the correct flype, then `flype_slide_add` silently bundles the flipping lemma, which by the repo's own `Flip.lean` comment is false for general 2-tangles. I verified the encoding subtlety that makes this hard to call from the outside — in this PD convention `one.hflip` *is* planar-isotopic to `one` (`sameUpToRotation` includes `reverseUnders`, so a reflection legitimately carries a sign flip), so `hflip` does model a spatial flip and the discrepancy is real rather than a convention artifact. I could not derive a contradiction inside the system (there is no crossing-cancellation generator that would let me strip the unit and conclude `t ∼ t.rot180` for all `t`; tellingly, `isotopic_add_crossing_comm` is proved only *with* an `IsRational` hypothesis). **Verdict on this point: unresolved risk, flagged.** The same `rotate180`-of-the-box choice appears in `IsLocalFlype`, which is a `ColoringIsotopy` generator too. `transfer_odd(_neg)` over arbitrary `T` is a second, milder instance of over-general quantification.

If `Isotopic` is coarser than genuine isotopy, that **weakens headline 2 and the second conjunct of headline 1** ("same fraction ⇒ Isotopic" concludes membership in a possibly-too-large relation). It would not weaken headlines 3 and 4, which are invariance statements along `ColoringIsotopy` — for those, extra generators only make the claim stronger (though less meaningful if a generator is not an isotopy).

**Well-formedness and planarity.** `TangleDiagram.WellFormed` exists (`Reidemeister.lean:245`: every arc identifier occurs at 0 or 2 ends) but:

- it is a hypothesis of exactly two constructors, `ColoringIsotopy.r1` and `.r2`, and of the coloring-transport lemmas in `ColoringInvariance.lean`. **`Isotopic` imposes no well-formedness at all** — its R1/R2 constructors accept ill-formed codes where `collapseKink` / `collapseR2` have no topological meaning;
- **no lemma in the repository establishes `WellFormed` for any construction** — not for `zero`, `infinity`, `crossingTangle`, `add`, `mul`, or `TwistExpr.diagram`. So the `WellFormed` hypotheses on `ColoringIsotopy.r1/r2` are, today, an unbridged obligation on callers;
- there is **no planarity condition anywhere**. `TangleDiagram` is a signed 4-valent PD-like code with four marked ends; the type contains codes not realizable as diagrams in a disc, and `PlanarIsotopy` is only renaming + list permutation + port half-turn, which checks nothing planar. For the headline objects (`TwistExpr.diagram`) this is harmless — those are built by honest operations — but it means `Isotopic`/`ColoringIsotopy` are relations on a strictly larger combinatorial model than "tangle diagrams," and any statement quantified over arbitrary `TangleDiagram` is a statement about that larger model.

On the brighter side, the R1/R2 encodings do not need an explicit "empty bigon" hypothesis: a loop arc or a shared bigon arc is a single PD edge with exactly two ends, so on a well-formed planar code nothing can enter the region. That argument depends on well-formedness — which, per the previous bullet, `Isotopic` never requires.

---

## 6. `coloring_fraction_eq_F` vs Theorem 4 (f = F)

`src/RationalTangles/ColoringFractionEq.lean:654`

```lean
theorem coloring_fraction_eq_F (e : TwistExpr) (hok : e.slideReady)
    (col : Nat → Int)
    (hc : e.diagram.IsColored col)
    (hdiag : (ColorMatrix.of e.diagram col).DiagonalSum)
    (hm : (ColorMatrix.of e.diagram col).NotMono) :
    (ColorMatrix.of e.diagram col).fraction = e.toStandard.fraction
```

**What it proves.** On a `slideReady` twist diagram, *every* non-monochrome integral coloring satisfying the diagonal rule has coloring fraction equal to the arithmetic standard-form value. The proof transports the coloring along the explicit `toStandard` path (`coloring_toStandard`) and then applies the unconditional uniqueness result on standard forms (`standard_fraction_any_coloring`). This is the real `f = F` content of KL Theorem 4, and the `DiagonalSum` hypothesis is redundant on this class: `coloring_fraction_eq_F_any_slideReady` (`DiagonalSumGeneral.lean:42`) discharges it from `twist_coloring_diagonal_slideReady`, so the honest headline is the hypothesis-free `_any_slideReady` version.

**What it does not prove.** (i) Only the `f = F` half of Theorem 4 — the invariance half is headline 3, along `ColoringIsotopy` only; (ii) `F` here is `e.toStandard.fraction`, the right-and-bottom re-evaluation, which equals `e.fraction` only on `noMulTop`; (iii) it is about a `slideReady` twist *parse*, along the explicit `toStandard` path — not along an arbitrary `Isotopic` witness of `IsRational`, and not for an arbitrary rational diagram (the file's own docstring says exactly this); (iv) `NotMono` is needed (monochrome colorings carry no information).

**`native_decide` exposure.** `ContinuedFractionFormExists.lean` is in the import closure of all four headline files, but import ≠ dependence. Tracing actual use:

- `isotopic_infinity_add_one` / `_negOne` (both `native_decide`-backed, via `infinity_add_*_crossings` and `collapseKink_infinity_add_*`) → `isotopic_one_add_infinity` / `isotopic_negOne_add_infinity` (`CanonicalFormExists.lean:217,222`) → `isotopic_integer_add_infinity` → `isotopic_cfTangle_snoc_zero` → `cfTangle_reduce` → `cf_to_canonical` → `cfTangle_isotopic_canonicalCF` → `ArithmeticCF.isotopic_canonicalCF` → `StandardExpr.isotopic_canonicalCF` → `standard_same_CFValue_isotopic` → `twist_same_toStandard_fraction_isotopic` → **`twist_same_fraction_isotopic_of_noMulTop`** → **`rational_classification_fragment`**.

So headline **2 and the second conjunct of headline 1 almost certainly carry `Lean.ofReduceBool`** in their axiom set. Headlines **3 and 4** go through `coloring_toStandard` / `standard_fraction_any_coloring` / `coloring_ColoringIsotopy`, which live in the coloring files and appear to use `ContinuedFractionFormExists` only for arithmetic definitions (`IsCFList`, `bumpHead`, `invertTerms`, `StandardExpr.toTerms`) and `valueOfList` lemmas — so they probably do **not** depend on `native_decide`. **This must be confirmed with `#print axioms` once a toolchain exists; I cannot confirm it by reading.** None of the six `native_decide` goals is large (two-crossing PD-code equalities); they look like candidates for `decide` or `rfl` with modest effort, which would remove the exposure entirely.

---

## 7. Verdicts

| # | Headline | Classical claim | Verdict |
|---|---|---|---|
| 1 | `rational_classification_fragment` | Theorem 1 (iff) | **PARTIAL** — not an iff; both conjuncts hang off a `ColoringIsotopy` hypothesis; second conjunct is near-implied by that hypothesis; `noMulTop` is semantically load-bearing. |
| 2 | `twist_same_fraction_isotopic_of_noMulTop` | Theorem 3 | **FAITHFUL WITH CAVEATS** — genuine content and full value coverage, but about expressions rather than tangles, `noMulTop` only, and the conclusion lands in an `Isotopic` with assumed generators (§5) plus `native_decide` exposure. |
| 3 | `coloring_fraction_invariant_ColoringIsotopy` | Theorem 2 | **PARTIAL** — invariance along a strictly smaller, *directed*, non-symmetric move set; several excluded transports are refuted, not merely open; `slideReady` twists only. |
| 4 | `coloring_fraction_eq_F` | Theorem 4 (`f = F`) | **FAITHFUL WITH CAVEATS** — a clean `f = F` for all non-monochrome colorings, but on `slideReady` twist parses along the explicit `toStandard` path, with `F` = standard-form value; the invariance half of Theorem 4 is not here. |

No headline is NOT FAITHFUL: nothing I read is dressed up as more than it is, and the in-file docstrings and the blueprint (`classification.md`) are unusually candid about the fragment boundaries. The two things I would change in the repo's own self-description are (a) say that `noMulTop` is where `TwistExpr.fraction` *is* the Conway fraction, not merely where the proof works (§3), and (b) record the one-flip/two-flip gap between `Flype` and `flype_slide_*` as an open faithfulness question about `Isotopic`, not only as a coloring-transport choice (§5).

---

## 8. Wording I would allow on a public explainer site

Allowed, as a headline:

> **What is proved:** On an explicitly delimited fragment of Conway's classification of rational tangles. For tangles given as twist-form expressions without top products, two expressions with the same fraction have isotopic diagrams — the reconstruction half of the classification, with the uniqueness of canonical continued-fraction form proved as an equality of diagram codes. In the other direction, the integral coloring fraction *f* is shown to equal the arithmetic fraction *F* on every non-monochrome coloring of such a diagram, and both are shown to be unchanged along paths built from Reidemeister I, II and III, planar isotopy, local flypes, and the addition/multiplication congruences.

Allowed, and required to appear with it:

> **What is not proved:** Conway's theorem itself. The two halves do not meet: invariance is proved along a restricted, one-directional set of moves (`ColoringIsotopy`), while reconstruction concludes in a larger relation (`Isotopic`), so no "isotopic if and only if same fraction" statement follows for either relation. A fraction is attached to a twist-form *expression*, not yet to a rational tangle up to isotopy. Expressions containing a top product are excluded, and there the formal `fraction` function is not the Conway fraction. Degenerate port cases are excluded, and in those cases the diagonal rule is explicitly refuted. Some moves — mirror and inversion transport of a coloring — are proved *impossible* to carry out this way, so the excluded set is partly a wall, not a backlog. The notion of isotopy is an assumed list of diagram moves rather than one derived from Reidemeister moves alone; one of those moves (the Figure 5 slide) is stated in a form that may be stronger than the topological move for non-rational subtangles, and no diagram well-formedness or planarity condition is enforced anywhere. Finally: in this audit nothing was compiled — no Lean toolchain is installed in the checkout — and parts of the reconstruction half rely on `native_decide`, which trusts the compiler rather than the kernel.

Wording I would **not** allow: "Conway's theorem formalized", "rational tangles are classified by their fraction, verified in Lean", "the fraction is an isotopy invariant" without naming `ColoringIsotopy`, "zero sorries, fully verified" (true about `sorry`, misleading about `native_decide` and about the uncompiled state), and anything that presents `noMulTop`/`slideReady` as mere technical hypotheses.
