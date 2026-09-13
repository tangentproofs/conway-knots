# Resume on a new machine (Linux VM)

This is the cold-start companion to `AGENTS.md` (which covers Windows/WSL).
The math plan itself lives in `blueprint/` (read `blueprint/README.md`,
then the roadmap DAG); the decision log lives in `JOURNAL.md` (read newest
entries first). This file is only setup + operating loop.

## Setup (once)

1. `git clone git@github.com:tangentproofs/conway-knots` and
   `git checkout wip/theorem-3` (active work) or `main` (clean closure
   state: Theorems 4/2/1 flagged, Theorem 3 general parked).
2. Install `uv`, `elan` (gives `lake`/`lean`), and native `opencode`.
   Ensure `~/.opencode/bin`, `~/.local/bin`, `~/.elan/bin` are on `PATH`.
3. Write `opencode.json` in the repo root from the template below
   (machine-local file, never committed — it is ignore-listed).
4. `lake update && lake build` (first build takes a while: Mathlib).
5. Verify: `uv run --project <autoform-bot-checkout> autoform check
   blueprint --lean-root .` should print `OK`, and `... audit blueprint
   --lean-root . --json` should report `"clean":true`.

`opencode.json` template (replace `<user>`):

```json
{
  "$schema": "https://opencode.ai/config.json",
  "skills": {
    "paths": ["/home/<user>/wrk/autoform-bot/skills"]
  },
  "mcp": {
    "autoform-lsp": {
      "type": "local",
      "command": ["uv", "run", "--project", "/home/<user>/wrk/autoform-bot", "python", "-m", "servers.lsp.server"],
      "cwd": "/home/<user>/ver/conway-knots",
      "enabled": true,
      "timeout": 30000
    },
    "autoform-repl": {
      "type": "local",
      "command": ["uv", "run", "--project", "/home/<user>/wrk/autoform-bot", "--extra", "repl", "python", "-m", "servers.repl.server"],
      "cwd": "/home/<user>/ver/conway-knots",
      "enabled": true,
      "timeout": 30000
    }
  },
  "permission": {
    "external_directory": {
      "/home/<user>/wrk/autoform-bot/**": "allow"
    },
    "bash": {
      "uv run --project /home/<user>/wrk/autoform-bot *": "allow"
    }
  }
}
```

You also need a local `autoform-bot` checkout (same branch everywhere:
`main` at the merge `3b2624b` or newer). Its Lean MCP servers do not run on
Windows; on native Linux they just work.

## Operating loop (autonomous formalization)

Each round, with the repo root as workdir:

1. Pick the smallest closable gap (see "Next steps" below; `JOURNAL.md`
   tail always names one).
2. Prove it in `src/` — never `sorry`/`admit`/`axiom`; honest flags only;
   keep every roadmap node's claimed Lean span under 200 lines
   (namespace-aware); new parents go in sub-chapters with `## Depends on`.
3. `lake build` must be green before wiring any `lean:` claim.
4. `autoform check`, `autoform audit` (must be clean), `autoform render`.
5. Append a dated `JOURNAL.md` entry (append-only, never rewrite history).
6. Never commit from worker rounds; never touch serves, remotes, or tooling.

Verify every edit by re-reading the file afterward. Lean elaborates
top-to-bottom (place lemmas after dependencies; `set_option ... in` goes
before docstrings). Closed value computations via `simp` with explicit
sets, never bare `decide`; prefer `linarith` for linear goals.

## Standing scope decisions (do not revisit without the owner)

- Theorems 4/2/1 closed at fragment scope (flags set, committed).
- Theorem 3 general: parked. The agreement-dropping route is refuted by
  theorem (`mulTop_two_inner_ne_toStandard`); ±1 is necessary and
  sufficient for the commutativity equation.
- Mirror/invert transport and degenerate `DiagonalSum`: refuted, not
  merely unproved. Do not attempt again.
- Tait path (`tait-flyping.md`, `alternating-flypes.md`): exposition only,
  out of the coverage contract.

## Next steps (as of the move)

1. Negative ladder is mechanical — continue rungs or stop; the open
   question is the negative-family induction (no shared `unitChain`
   analogue yet).
2. Genuine research: Theorem-3 diagram-level blockers (unrestricted
   `flype_slide_*`, switch-generator transport).
