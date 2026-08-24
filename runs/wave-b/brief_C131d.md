# Unit C131d — dv-engine v2 formalization: hpure bridge + x-carry

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. The Lean
project is `leanfinal/` (lake, mathlib pinned v4.31.0, already built — NEVER run bare
`lake build`; verify per-file with `lake env lean <file>` from inside `leanfinal/`).

## Read first (in this order)
1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §2.3 (the `hpure` bridge
   and the x-carry — your proofs are written out there), and your rows of the §5 table.

## Your nodes (from the §5 node plan)
- **C.131d′**: `key_coeff_side_floor` (Lemma F4) and its cleared form (Cor F5).
  Deps (verify each by `rg` in `leanfinal/Uniformity/`): the `F.hpure` field
  (`IsPure`), landed `suppVal_of_pure`, `suppVal_le_weight`, `npHgt_X`, B.35b, and the
  C.71 margin vocabulary.
- **C.131e′**: the x-carry tail and the exact `+δ` branch (end of §2.3). Deps: d′ plus
  the C.71 margin.

## Cross-unit dependency (IMPORTANT)
Node e′'s statement uses the two-index weight `WT`, which unit C131a is landing
concurrently in `leanfinal/Uniformity/ChapC/C131a.lean` (its increment 1 = the `WT`
definition, committed early). Do d′ FIRST — it is self-contained. When you reach e′,
check whether `C131a.lean` exists and elaborates; if yes, import it and prove e′
against its `WT`. If it has not landed by the time d′ is done and committed, do NOT
define your own duplicate `WT` — deliver e′ as verdict SUPPLY with the full proof text
in your verdict file, keyed to C131a's declared names.

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131d.lean`. Follow the house style of
`leanfinal/Uniformity/ChapC/C64.lean` (copyright header, module docstring naming
"Chapter C, NODES C.131d′–e′", citing the blueprint doc by filename).

## Rules (honesty invariants — non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; record the remainder as
  BLOCKED/SUPPLY with the exact missing statement named.
- Never trust a lemma name from memory or from the blueprint text alone: `rg` it first.
- Do NOT touch `leanfinal/Uniformity/ChapC.lean` (roll-up), any `leanspec/` file, or
  any other unit's file.
- Commit early and per-increment: `git add` ONLY your own file; if `git commit` hits an
  index.lock error, sleep 5s and retry (five units run in parallel).

## Final act
Write `runs/wave-b/verdict_C131d.md`: per-node verdict LANDED / SUPPLY / BLOCKED, the
declarations proved, and the exact `lake env lean` command you verified with.
