# Unit C131f — dv-engine v2: private-export fence + composed-key monomial floor

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets like
`lake build Uniformity.ChapC.C131f` are fine).

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §2.4 (the composed-key
   price and the private-export fence), and your rows of the §5 node table.
3. The landed first-wave weight vocabulary: `leanfinal/Uniformity/ChapC/C131a.lean`
   (`wtCoeff`, `WT`, `WT_add`, `WT_mul` — REUSE these, never redefine).

## Your nodes
- **C.131f′**: public lift-pin exports/cleanup. Deps: C.46/C.47 private helpers
  (`rg composedKey leanfinal/Uniformity/` and read C46/C47).
- **C.131g′**: composed-key monomial floor and `WT K_T = E₂`. Deps: public C.47
  clauses; f′ only if generality is needed.

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131f.lean` (house style of `C64.lean`;
docstring naming "Chapter C, NODES C.131f′–g′", citing the blueprint doc). End the file
with `#print axioms` lines for every new declaration.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; the remainder BLOCKED
  with the named missing object.
- `rg` every lemma name before use. Import `Uniformity.ChapC.C131a` (olean built)
  and other landed modules as needed.
- Do NOT touch the ChapC roll-up, `leanspec/`, or other units' files (in flight:
  C131aa, C131m, C131t, C131u, F3 in ChapI).
- Do NOT `git commit` (the sandbox mounts `.git` read-only) — the orchestrator commits.
  Just write the file and verdict.

## Final act
Write `runs/wave-b/verdict_C131f.md`: per-node LANDED/SUPPLY/BLOCKED, declarations
proved, exact verification command.
