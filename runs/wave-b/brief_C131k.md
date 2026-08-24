# Unit C131k — dv-engine v2 formalization: structural normal forms

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. The Lean
project is `leanfinal/` (lake, mathlib pinned v4.31.0, already built — NEVER run bare
`lake build`; verify per-file with `lake env lean <file>` from inside `leanfinal/`).

## Read first (in this order)
1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §2.6 (normal form by
   structural recursion, not rewriting), and your rows of the §5 node table.

## Your nodes (from the §5 node plan)
- **C.131k′**: the structural `xNF` (x-normal form), its reconstruction lemma, and
  uniqueness. Deps: B.05/B.06 (find them: `rg` in `leanfinal/Uniformity/ChapB/`).
- **C.131l′**: the structural OUTER normal form using `devQ`. Deps: C.71 (landed —
  `leanfinal/Uniformity/ChapC/C71.lean`) and k′.

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131k.lean`. Follow the house style of
`leanfinal/Uniformity/ChapC/C64.lean` (copyright header, module docstring naming
"Chapter C, NODES C.131k′–l′", citing the blueprint doc by filename).

## Rules (honesty invariants — non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; record the remainder as
  BLOCKED with the exact missing statement named.
- Never trust a lemma name from memory or from the blueprint text alone: `rg` it in
  `leanfinal/Uniformity/` first; the blueprint's "landed" claims must be verified.
- Do NOT touch `leanfinal/Uniformity/ChapC.lean` (roll-up — orchestrator wires it),
  any `leanspec/` file, or any other unit's file. Other units are landing
  `C131a/C131d/C131p/C131aa.lean` concurrently — ignore their files.
- Commit early (compiling skeleton with the `xNF` definition within ~20 min), then per
  increment: `git add` ONLY your own file; if `git commit` hits an index.lock error,
  sleep 5s and retry.

## Final act
Write `runs/wave-b/verdict_C131k.md`: per-node verdict LANDED / SUPPLY / BLOCKED, the
declarations proved, and the exact `lake env lean` command you verified with.
