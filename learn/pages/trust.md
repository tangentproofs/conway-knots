# Trust: what has and hasn't been checked

This site **explains** the Lean. It does not re-check it.

## Lean checking

| | `main` @ 76792ca (Lean files last changed in 76792ca, 2026-09-08) |
|---|---|
| Built by this site | **no**. By the owner's choice, no Lean was built on our servers for this site. |
| Built publicly (CI) | **no Lean CI** in the repository. The README says Lean is not installed in its workspace and asks not to run `lake build` until a toolchain is available. |
| `#print axioms` | **not run.** No output is recorded in the repository. |
| `sorry`, `admit`, `axiom` | none found by grep in `src/` |
| `implemented_by`, `extern`, `unsafe` | none found by grep |
| **`native_decide`** | **6 uses**, all in ContinuedFractionFormExists.lean (lines 32, 37, 353, 358, 363, 368). They check small PD-code computations: the R2 cancellation [+1] + [−1] → [0] and the R1 kinks [∞] + [±1] → [∞]. `native_decide` trusts the compiler, not the kernel (axiom `Lean.ofReduceBool`). |
| Which headlines reach them | By the source scan and the Claude audit: [`twist_same_fraction_isotopic_of_noMulTop`](#/node/twist_same_fraction_isotopic_of_noMulTop) and so [`rational_classification_fragment`](#/node/rational_classification_fragment). Probably **not** [`coloring_fraction_invariant_ColoringIsotopy`](#/node/coloring_fraction_invariant_ColoringIsotopy) or [`coloring_fraction_eq_F_any_slideReady`](#/node/coloring_fraction_eq_F_any_slideReady). Only `#print axioms` after a build can confirm this. |
| Small `decide` | many, on small PD-code / `Fin` goals: ordinary kernel checking |
| Dependencies | Mathlib only |

The six `native_decide` goals are one- and two-crossing code equalities. They look replaceable by `decide` or `rfl`, which would remove the exposure.

## What the Lean does *not* contain

- **Conway's theorem.** There is no statement "isotopic ⇔ same fraction". The source's own header (`RationalTangles.lean`) says: "The classification theorem is not yet stated."
- **Invariance under full isotopy.** The fraction is proved invariant only along [`ColoringIsotopy`](#/node/ColoringIsotopy), a smaller one-way relation. It isn't proved invariant along [`Isotopic`](#/node/Isotopic).
- **A fraction for a tangle.** Fractions belong to twist recipes. "The fraction of a rational tangle up to isotopy" is not defined.
- **Top products.** Recipes with `mulTop` are excluded from the classification headlines, and there the recipe fraction [`TwistExpr.fraction`](#/node/TwistExpr.fraction) is not the Conway fraction.
- **Isotopy from first principles.** `Isotopic` takes flypes, half-turns, inversion identities and the transfer moves as primitive generators. One generator, `flype_slide_add/mul`, may be stronger than real isotopy for non-rational pieces (Claude audit, §5).
- **Well-formedness and planarity.** `TangleDiagram` has no planarity condition. `WellFormed` is a hypothesis of two `ColoringIsotopy` moves and is proved for nothing.

## This site's own data

- **Declarations were read from the source text, not a Lean build.** `learn/tools/scan_decls.py` finds every top-level declaration (1760) with its exact lines and text, and every declaration carries `"extracted": false`. "Mentions" and "proof uses" edges are matched by name, including `x.method` and `(f x).method` calls resolved from binder and return types. They may miss or misattribute a few uses.
- **Identifier links on the source pages** come from the same name matching (`data/xref.json` is marked `"heuristic": true`). Names under core and Mathlib namespaces (`List.`, `Nat.`, `Int.`, `Rat.`, …) link to the Mathlib docs search.
- **Audit.** The headline statements were audited by a second model (Claude), reading the source only; see [the review](#/review) and `learn/CLAUDE_AUDIT.md`.
- **Explanations** are drafts by Grok Bot (`review: draft`), not yet checked by a human.

## To upgrade this page

Build on a capable machine (`lake exe cache get && lake build`), run `#print axioms` for each headline, replace `scan_decls.py` with `ExtractDecls.lean` + `build_xref.py` as on the other tangentproofs sites, and replace the "no" entries above.
