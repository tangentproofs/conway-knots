# Conway Knot Enumeration Plan

**Goal:** a Lean program that enumerates all rational knots, in the footsteps of
Conway's 1970 "An enumeration of knots and links" — with a verified-validity
story (no duplicates, complete).

**Scope rule (user's direct order, 2026-09-14):** formalize what's in the papers.
No new math. The negative-ladder rung pipeline is stopped and out of scope.

## Survey of current repo state (2026-09-14)

`src/RationalTangles/` holds 33 Lean files, all **2-tangle machinery**:

- `Tangle.lean` — `TangleDiagram` (PD-style tangle code), `add` / `mul` tangle
  operations, `crossingTangle`
- `Reidemeister.lean`, `Flype.lean` — `Isotopic : TangleDiagram → TangleDiagram → Prop`
  (Reidemeister moves **plus** local flypes as constructors; congruence lemmas for
  `add`/`mul` already proved)
- `Coloring*.lean`, `ColorFraction*.lean`, `ContinuedFraction*.lean`,
  `CanonicalForm*.lean` — coloring invariants and the **fraction classification**
  (Theorem 1: rational tangles are classified by their fraction)

**Verified absent** (grep over all of `src/`): no `Knot`/`Link` types, no closure
operations, no Conway notation, no enumeration procedure. The only occurrence of
the word "knot" in Lean sources is a doc comment in `Reidemeister.lean`.

**What this means:** the repo has the *dedup engine* (fraction classification)
but none of the *knot-level machinery*. Every phase below builds only on the
papers (Conway 1970; Kauffman–Lambropoulou) plus classical, standard corollaries.

## Phase 0 — Knot/link types

New file: `src/RationalTangles/KnotDiagram.lean`

- Define `KnotDiagram`: a closed diagram with no boundary. Simplest faithful
  choice: a `TangleDiagram` whose four boundary arcs are identified in pairs
  (or equivalently a PD code with all arcs internal).
- Define `LinkDiagram` similarly (possibly several components).
- Define knot isotopy (`KnotIsotopic`) induced by tangle `Isotopic` on
  representatives. Depends on: `Tangle.lean`, `Reidemeister.lean`, `Flype.lean`.
- No new mathematics: these are the standard definitions the papers assume.

## Phase 1 — Tangle closures

New file: `src/RationalTangles/Closure.lean`

- `numeratorClosure (T : TangleDiagram) : KnotDiagram` — connect NW–NE, SW–SE.
- `denominatorClosure (T : TangleDiagram) : KnotDiagram` — connect NW–SW, NE–SE.
- Prove: `Isotopic T S → KnotIsotopic (numeratorClosure T) (numeratorClosure S)`
  (and same for denominator) — follows from the existing `add`/`mul`
  congruence lemmas plus Reidemeister moves on the closing arcs.
- Depends on: Phase 0, `Flype.lean` (isotopy congruence).

## Phase 2 — Conway notation as Lean data

New file: `src/RationalTangles/ConwayNotation.lean`

- Inductive type of Conway symbols, mirroring Conway 1970 §2:
  `| twist : Int → ConwayTangle` (integer tangles), `| add`, `| mul` of symbols.
- Interpretation `⟦·⟧ : ConwayTangle → TangleDiagram` via existing
  `TangleDiagram.add` / `TangleDiagram.mul` / `crossingTangle`.
- Rational knots: `ConwayKnot := numeratorClosure ⟦c⟧` (Conway's tables use the
  numerator closure throughout).
- Depends on: `Tangle.lean`, Phase 1. Mostly wiring — the operations exist.

## Phase 3 — Schubert classification of rational knots (the dedup engine)

New file: `src/RationalTangles/Schubert.lean`

- Classical Schubert (1956), derived as a corollary of the repo's Theorem 1 plus
  Phase 1 closures — not new math: `KnotIsotopic (numClosure T) (numClosure S)`
  iff the tangles' fractions satisfy the Schubert equivalence
  (`q' = ±q`, `p ≡ ±p⁻¹ mod q` style relation).
- This is what makes "no duplicates" provable: two entries are the same knot
  exactly when their fractions are Schubert-equivalent.
- Depends on: Theorem 1 (fraction classification), Phase 1.

## Phase 4 — The enumeration procedure

New file: `src/RationalTangles/Enumerate.lean`

- A **computable** Lean program: for a bound `N`, generate all Conway symbols
  (equivalently all fractions `p/q`) with crossing number ≤ N, build the knot
  diagrams, deduplicate by the Schubert relation from Phase 3.
- Executable: `#eval enumerate 10` should print representatives.
- Crossing-number bookkeeping: `crossings : ConwayTangle → Nat` from the
  symbol structure (sums add, products add — standard).
- Depends on: Phases 2, 3. This is the artifact the whole project is for.

## Phase 5 — Validity proofs

New file: `src/RationalTangles/EnumerationValid.lean`

- **No duplicates:** distinct output entries are non-isotopic knots — direct
  from Phase 3 (Schubert) applied to the dedup step. Formalizable; in scope.
- **Completeness:** every rational knot with crossing number ≤ N appears in
  `enumerate N`. Needs: (a) every rational knot is `numeratorClosure` of a
  rational tangle (definition-level, from Conway 1970); (b) the generator
  covers all fractions with crossing number ≤ N (continued-fraction
  enumeration — the repo's `ContinuedFraction*.lean` files already formalize
  the needed fraction machinery). The fiddly part is the crossing-number
  bound bookkeeping, not new mathematics.
- Depends on: Phases 3, 4.

## Dependency order

```
Phase 0 (knot types)
   └─► Phase 1 (closures)
          ├─► Phase 2 (Conway notation) ─► Phase 4 (enumeration program)
          └─► Phase 3 (Schubert) ─────────► Phase 5 (validity proofs)
```

Phases 0–2 are definitions + wiring (the current Muse-on-server task on knot
machinery feeds Phase 0/1). Phases 3–5 are the theorems that make the
enumeration *verified*, not just programmed.

## Explicit non-goals

- **Tait flyping conjecture** — about alternating diagrams in general; Conway's
  enumeration (1970) predates its proof by ~20 years and never needed it.
  Settled irrelevant 2026-09-14.
- **Negative-ladder extensions** (rungs 44–49 and beyond) — new math beyond the
  papers; pipeline stopped 2026-09-14.
- **Non-rational knots** — Conway's full tables go beyond rational knots, but
  that needs machinery far outside the papers' scope. Rational knots are the
  complete, honest target for this project.
- Any theorem not stated in or directly corollaried from the papers.
