# Unit C130A — tower-instantiation freeze v2: layers C.130b/c (stage carriers) + C.130d/e (threshold + input block)

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets like
`lake build Uniformity.ChapC.C130b` are fine).

## Context
The tower-instantiation freeze v2 (`docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`)
is the design for chapter I's I.10a/I.10b socket bodies. Unit F3 typed its non-OPEN core
(`leanfinal/Uniformity/ChapI/I10FreezeV2.lean`: `StageLive`, `GaugeLive`, `DeepLive`,
`TerminalReceiver`, `ArisingCore`, `DeepTwistConjunctLive`) — REUSE those, never
duplicate. The freeze's OPEN layers must now be transcribed; you own the first two.

## Read first
1. `docs/PROJECT_STATE.md`.
2. The freeze v2 doc END-TO-END, then focus your layers:
   - **C.130b/c**: general-depth `stageKey`, `stageDeg`, and the transported E.10 stage
     carrier.
   - **C.130d/e**: the source-transcribed `CanonicalThresholdAt` and the fully bound
     input block.
3. `runs/wave-b/verdict_F3.md` (what F3 landed and why the sockets stay `True`).
4. `leanfinal/Uniformity/ChapI/I10FreezeV2.lean` and C.83's `DeepTower`
   (`rg DeepTower leanfinal/Uniformity/ChapC/C83.lean`).

## Deliverable
New files `leanfinal/Uniformity/ChapC/C130b.lean` (layers b/c) and
`leanfinal/Uniformity/ChapC/C130d.lean` (layers d/e), house style of `C64.lean`,
docstrings naming the freeze layers and doc. `#print axioms` lines for every new
declaration. The freeze is the statement authority: transcribe its displayed
definitions/statements byte-faithfully into the present vocabulary; if a layer's text
cannot be typed without inventing mathematics, mark that piece BLOCKED with the exact
missing carrier (do NOT approximate, do NOT weaken).

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`, NO `True`-bodied mathematical interfaces.
- `rg` every lemma name before use.
- Do NOT touch the roll-ups, `leanspec/`, `I10FreezeV2.lean`, or other units' files
  (in flight: C131h, C131v, C131ac, C130B — C130B owns `C130f.lean`).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C130A.md`: per-layer LANDED/SUPPLY/BLOCKED, declarations,
exact verification commands.
