# AGENTS.md

## Windows-only: run opencode + Autoform MCPs inside WSL2

Native Windows is unsupported for the Autoform MCP servers
(`autoform-lsp`, `autoform-repl`). `servers/lean_client.py` requires
Unix-domain sockets (`socket.AF_UNIX`) and `os.getuid`; both are absent
on native Windows Python, so both servers exit 1 with
`LeanRuntimeError: the shared Lean runtime currently requires
Unix-domain sockets`. This section applies to Windows hosts only.
Linux/macOS run opencode directly on the working tree.

### Setup (once)

1. Install WSL2 + Ubuntu, reboot, launch Ubuntu once and create a user.
2. Inside Ubuntu, install `uv`, `elan` (gives `lake`/`lean`), and the
   native Linux `opencode`:
   - Hide Windows interop paths during the opencode install so the
     installer does not mistake the Windows `opencode.exe` for a Linux
     one, e.g. `export PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:$HOME/.local/bin`
     before `curl -fsSL https://opencode.ai/install | bash`.
   - Ensure `~/.opencode/bin`, `~/.local/bin`, `~/.elan/bin` are on
     `PATH` (persistent via `~/.bashrc`).
3. Keep native ext4 checkouts — do NOT run `uv` or `lake` on `/mnt/d`:
   - `~/wrk/autoform-bot` (copy of the Autoform plugin checkout)
   - `~/ver/conway-knots` (copy of this repo, minus `.lake/` and the
     Windows `opencode.json`)
   - NTFS-via-`/mnt/d` breaks `uv` venvs (hardlinks/permissions) and
     Lean builds. `uv sync --project /mnt/d/...` will also destroy the
     Windows `.venv`; if that happens, delete it and re-run `uv sync`
     on Windows.
4. `~/ver/conway-knots/opencode.json` must use Linux paths:
   ```json
   {
     "skills": { "paths": ["/home/<user>/wrk/autoform-bot/skills"] },
     "mcp": {
       "autoform-lsp": {
         "type": "local",
         "command": ["uv", "run", "--project", "/home/<user>/wrk/autoform-bot", "python", "-m", "servers.lsp.server"],
         "cwd": "/home/<user>/ver/conway-knots",
         "enabled": true
       },
       "autoform-repl": {
         "type": "local",
         "command": ["uv", "run", "--project", "/home/<user>/wrk/autoform-bot", "--extra", "repl", "python", "-m", "servers.repl.server"],
         "cwd": "/home/<user>/ver/conway-knots",
         "enabled": true
       }
     }
   }
   ```

### Use

```sh
wsl -d Ubuntu
cd ~/ver/conway-knots
opencode
```

`opencode mcp list` should show `autoform-lsp` and `autoform-repl`
connected. The Windows `D:\ver\conway-knots\opencode.json` (Windows
paths) is expected to keep failing natively — use WSL.

### Syncing the two checkouts

The Windows (`/mnt/d/...`) and WSL (`~/...`) trees are copies. Sync
via `git push`/`pull`, not by editing both sides. For full REPL
warmth in WSL, run `lake exe cache get && lake build` in
`~/ver/conway-knots` (Mathlib; takes a while). MCPs start without it
and warm on demand.
