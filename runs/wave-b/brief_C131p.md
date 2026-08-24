# Unit C131p — dv-engine v2 formalization: conversion utilities

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. The Lean
project is `leanfinal/` (lake, mathlib pinned v4.31.0, already built — NEVER run bare
`lake build`; verify per-file with `lake env lean <file>` from inside `leanfinal/`).

## Read first (in this order)
1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §§3.1–3.4 (the conversion
   module), and your rows of the §5 node table.

## Your nodes (from the §5 node plan)
- **C.131p′**: the `ℕ∞` finite-infimum utilities Cnv1–Cnv4 (§3.1). Deps: mathlib order
  lemmas only (search with `rg` in the mathlib cache or use `exact?`-style discovery;
  do not reinvent what mathlib has).
- **C.131q′**: `stageHeight_eq_coeff_inf` (§3.2, flatten `stageHeight`). Deps: C.02,
  B.15 (find by `rg` in `leanfinal/Uniformity/`).
- **C.131r′**: flatten `dvHgt`/`dvSupp` (§3.3). Deps: the C.06 vocabulary, p′–q′.
- **C.131s′**: reduced-development recovery / range-to-support (§3.4). Deps: B.05/B.06,
  p′.

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131p.lean`. Follow the house style of
`leanfinal/Uniformity/ChapC/C64.lean` (copyright header, module docstring naming
"Chapter C, NODES C.131p′–s′", citing the blueprint doc by filename).

## Rules (honesty invariants — non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; record the remainder as
  BLOCKED with the exact missing statement named. If a node resists, move on to the
  next — p′ and s′ do not need q′/r′.
- Never trust a lemma name from memory or from the blueprint text alone: `rg` it first.
- Do NOT touch `leanfinal/Uniformity/ChapC.lean` (roll-up — orchestrator wires it),
  any `leanspec/` file, or any other unit's file. Other units are landing
  `C131a/C131d/C131k/C131aa.lean` concurrently — ignore their files.
- Commit early (compiling Cnv1–Cnv4 within ~20 min), then per increment: `git add`
  ONLY your own file; if `git commit` hits an index.lock error, sleep 5s and retry.

## Final act
Write `runs/wave-b/verdict_C131p.md`: per-node verdict LANDED / SUPPLY / BLOCKED, the
declarations proved, and the exact `lake env lean` command you verified with.
