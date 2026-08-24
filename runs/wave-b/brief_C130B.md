# Unit C130B — tower-instantiation freeze v2: layer C.130f (lattices + gauge export)

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets are fine).

## Context
Same campaign context as unit C130A (read its brief:
`runs/wave-b/brief_C130A.md`). You own the freeze's layer:
- **C.130f**: synchronized level lattices, `GaugeLattice`, the normal section, the
  height family, and the ULift export.

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` END-TO-END, focus
   C.130f.
3. `runs/wave-b/verdict_F3.md`; `leanfinal/Uniformity/ChapI/I10FreezeV2.lean` (REUSE its
   carriers); the landed gauge vocabulary (`rg "NormSection\|GaugeArena" leanfinal/Uniformity/`).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C130f.lean`, house style of `C64.lean`,
docstring naming the freeze layer and doc, `#print axioms` lines for every new
declaration. The freeze is the statement authority: transcribe byte-faithfully; mark
anything untypeable BLOCKED with the exact missing carrier — never approximate.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`, NO `True`-bodied mathematical interfaces.
- `rg` every lemma name before use.
- Do NOT touch the roll-ups, `leanspec/`, `I10FreezeV2.lean`, or other units' files
  (in flight: C131h, C131v, C131ac, C130A — C130A owns `C130b.lean`/`C130d.lean`).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C130B.md`: LANDED/SUPPLY/BLOCKED, declarations, exact
verification command.
