# Campaign journal

Narrative log of the Conway rational-tangle formalization campaign: what was
tried, what landed, what was refuted, and the decisions taken. Newest entries
at the bottom. Each entry is append-only — never rewrite history; correct the
record with a new entry.

## 2026-09-04 — WSL2 rescue

The Autoform MCP servers (`autoform-lsp`, `autoform-repl`) cannot start on
native Windows: `servers/lean_client.py` requires `socket.AF_UNIX` and
`os.getuid`, both absent on Win32, so both servers exit 1 with
`LeanRuntimeError`. Installed WSL2 + Ubuntu (user `michal`) after a wedged-VM
detour that needed a reboot. Set up native ext4 checkouts
(`~/wrk/autoform-bot`, `~/ver/conway-knots`), `uv`, `elan` (Lean 4.32.2),
and native Linux `opencode`. Both MCPs connect from WSL. Windows-side
`opencode.json` remains natively broken by design. Recorded in `AGENTS.md`.

## 2026-09-04 — Blueprint site live

`autoform render` + `mkdocs build` + serve. Site browsable locally; later
replaced `mkdocs serve` with a static server (the dev server 404'd deep
pages) and published to `gh-pages` via `mkdocs gh-deploy`:
https://tangentproofs.github.io/conway-knots/

## 2026-09-04 — Agent review, then full steam

Chose `agent-review` over grinding lemmas. Baselines: `lake build` green
(1001 jobs), zero sorries, `autoform check` 52 articles (24 fully proved),
`autoform audit` with kind-mismatch/overfull/cycle findings. Then: fixed
declaration kinds, split the chapter to break a dependency cycle
(colouring chapter vs theorems chapter, via moving the flipping lemma),
reorganized into foundations/forms/toolkit/classification chapters.

## 2026-09-05 — Theorem 4 capstone + splits

New `ColoringFractionTheorem.lean`: 8 thin paper-numbered wrappers around
proved Theorem-4 fragments. Wired Theorems 4/3/2 nodes with honest
boundaries (no `proof:` flags on assemblies). Split 6 oversized nodes into
~40 PR-sized sub-nodes + 7 sub-chapters. Audit clean.

## 2026-09-05 — Wiring campaign

Round after round of proved-but-unclaimed lemmas wired into the roadmap:
`[0]`/`[∞]` summands, canceling units, nested chains, two-block sums,
glue toolkit, port toolkit, standard-values chapter. Discovered and
documented an upstream audit-scanner bug (`mutual`/`end` blindness);
relocated one theorem pre-`mutual` to reclaim it rather than touching
tooling. Coverage declared complete at ~130 articles.

## 2026-09-05 — Sharpness: the wall is real

Proved the hoped-for transports are FALSE in general, not merely unproved:
mirror transport fails already on one crossing
(`not_coloring_mirror_transport`); invert transport holds at one crossing
but fails at two (`not_coloring_invert_transport`); `DiagonalSum` fails on
degenerate gluings. These turned "outstanding" into "refuted" — equally
valuable, and they constrain all future strategy.

## 2026-09-06 — Fragment chain 4 → 2 → 1 closed

Scope decision (owner): close Theorems 4 → 2 → 1 at fragment scope; park
Theorem 3 general. Three review rounds verified every prose claim against
its Lean statement, fixed drift (including a local-vs-global RIII
overstatement), and set `proof: formalized` on all three. Theorem 1 reached
`fully_proved` by re-pointing its proof-deps to flagged fragment nodes.
126 fully proved, audit clean. Committed and pushed (`76792ca`), site
redeployed.

## 2026-09-08 — Theorem 3 un-parked; wall upgraded to theorem

Attempted the general case via CF-canonicalization and alternate isotopy
paths. Both routes analysed and ruled out; instead proved
`TwistExpr.mulTop_two_inner_ne_toStandard` (inner F = 2 gives algebraic
1/3 vs standard-form 2/3): the agreement hypotheses are NECESSARY. With the
earlier ±1 necessity result, blocker (b) is closed on the finiteness
fragment — by theorem, not by gap. General Theorem 3 stays unproved, now
provably unclosable via agreement-dropping.

## 2026-09-08 — Journal started

Backfilled from session history. Standing rule: the worker appends a dated
entry every round (append-only).

## 2026-09-08 — Negative three-unit invert-add value

Proved ([-1]x3) inv carries -1/3: universal (rules force d/-3d) plus direct witness, mirroring a20 with fresh mirror-switch PD derivations. New wrinkle vs positive case: the denominator multiple is negative, so the nonzero transfers need neg_ne_zero (mul_ne_zero does not fire under a leading negation) — two-line fix, then green. Module build 22.9s vs ~19s positive baseline.
Key files/theorems: DiagonalSumGeneral.lean tail (coloring_fraction_invert_add_negOne_negOne_negOne, sharpColAddNegThree, HasColoringFraction.invert_add_negOne_negOne_negOne); new node invert-units/a24-neg-three-unit-value.md. Check 150 articles/127 fully proved, audit clean, render 174 pages/131 nodes. Decision: negative ladder rung one landed; rung two ([-1]x4 at -1/4) or the unitChain inductive universal are both open next.
