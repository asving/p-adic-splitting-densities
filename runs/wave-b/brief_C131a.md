# Unit C131a — dv-engine v2 formalization: two-index weight + product law

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. The Lean
project is `leanfinal/` (lake, mathlib pinned v4.31.0, already built — NEVER run bare
`lake build`; verify per-file with `lake env lean <file>` from inside `leanfinal/`).

## Read first (in this order)
1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0 (status discipline), §2.1
   (the two-index weight), §2.2 (addition and multiplication), and your rows of the §5
   node table.

## Your nodes (from the §5 node plan)
- **C.131a′**: `wtCoeff`, the two-index weight `WT`, zero/support lemmas.
  Deps: the C.06 arithmetic vocabulary (`addVal` etc. — find it by
  `rg addVal leanfinal/Uniformity` and read the defining file).
- **C.131b′**: `WT_add` + finite-sum valuation helpers. Deps: landed `addVal_add`.
- **C.131c′**: the two convolution lemmas and `WT_mul`. Deps: a′–b′, landed `addVal_mul`.

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131a.lean`. Follow the house style of
`leanfinal/Uniformity/ChapC/C64.lean` (copyright header, module docstring naming
"Chapter C, NODES C.131a′–c′", citing the blueprint doc by filename). Import only what
you need from `Uniformity.ChapB`/`Uniformity.ChapC` files.

## Rules (honesty invariants — non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. If a lemma resists, land what is proved and
  record the remainder as BLOCKED with the exact missing statement named.
- Never trust a lemma name from memory or from the blueprint text alone: `rg` it in
  `leanfinal/Uniformity/` first; the blueprint's "landed" claims must be verified.
- Do NOT touch `leanfinal/Uniformity/ChapC.lean` (roll-up — orchestrator wires it),
  any `leanspec/` file, or any other unit's file.

## Priority: commit increment 1 EARLY
Another in-flight unit (C131d) waits on your `WT` definition. Within your first
increment: define `wtCoeff` + `WT` + the zero/support lemmas, get
`lake env lean Uniformity/ChapC/C131a.lean` green, and COMMIT (`git add` ONLY your
file; message `C131a: increment 1 — WT defined`; if `git commit` hits an index.lock
error, sleep 5s and retry — five units run in parallel). Then continue with b′/c′,
committing per increment.

## Final act
Write `runs/wave-b/verdict_C131a.md`: per-node verdict LANDED / SUPPLY (proof text
ready but not compiled) / BLOCKED (named missing object), the list of declarations
proved, and the exact `lake env lean` command you verified with. Keep it under a page.
