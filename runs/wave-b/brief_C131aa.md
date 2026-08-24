# Unit C131aa — dv-engine v2 formalization: exact-half local lemmas

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. The Lean
project is `leanfinal/` (lake, mathlib pinned v4.31.0, already built — NEVER run bare
`lake build`; verify per-file with `lake env lean <file>` from inside `leanfinal/`).

## Read first (in this order)
1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §4.3 (local lemmas
   surrounding the exact-half cite), and your rows of the §5 node table. §§4.1–4.2 are
   context: the cite itself (`fgmn_dv_exact_mul`, gate (b)) is NOT yours to declare —
   the orchestrator owns cite authoring. You prove the LOCAL lemmas around it.

## Your nodes (from the §5 node plan)
- **C.131aa′**: `IsTestKey → IsDvPure`. Deps: C.13 (find by `rg IsTestKey` and
  `rg IsDvPure` in `leanfinal/Uniformity/`).
- **C.131ab′**: the exact residual of a test key. Deps: C.13, C.25/C.26.

A prior survey noted: no existing lemma computes the dv-polygon of a test key, so this
is real work, not assembly. The B-chain primitives to survey first: `dev`, `suppVal`,
`gaussVal`, `twistRead` (all in `leanfinal/Uniformity/ChapB/`).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131aa.lean`. Follow the house style of
`leanfinal/Uniformity/ChapC/C64.lean` (copyright header, module docstring naming
"Chapter C, NODES C.131aa′–ab′", citing the blueprint doc by filename).

## Rules (honesty invariants — non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; record the remainder as
  BLOCKED with the exact missing statement named.
- Never trust a lemma name from memory or from the blueprint text alone: `rg` it first.
- Do NOT touch `leanfinal/Uniformity/ChapC.lean` (roll-up — orchestrator wires it),
  any `leanspec/` file, or any other unit's file. Other units are landing
  `C131a/C131d/C131k/C131p.lean` concurrently — ignore their files.
- Commit early (compiling skeleton within ~20 min), then per increment: `git add` ONLY
  your own file; if `git commit` hits an index.lock error, sleep 5s and retry.

## Final act
Write `runs/wave-b/verdict_C131aa.md`: per-node verdict LANDED / SUPPLY / BLOCKED, the
declarations proved, and the exact `lake env lean` command you verified with.
