# Unit C131t — dv-engine v2: weight-to-height identification + strict exactness

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets are fine).

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §3.5 (the weight-to-height
   identification), §3.9 (the faithful band is an additional exactness theorem — for
   context on x′), and your rows of the §5 node table.
3. Landed inputs you MUST reuse (never redefine):
   - `leanfinal/Uniformity/ChapC/C131p.lean` — the conversion utilities Cnv1–Cnv9
     (`dvHgt_eq_coeff_inf`, `dvSupp_eq_nested_inf`, `stageHeight_eq_coeff_inf`,
     `dev_reconstruct_reduced`, …) — nodes p′–s′.
   - `leanfinal/Uniformity/ChapC/C131a.lean` — `wtCoeff`, `WT`.
   - C.11 (rg for it in `leanfinal/Uniformity/ChapC/`).

## Your nodes
- **C.131t′**: `dv2Hgt_eq_WT_phiNF` (deps: C.11, r′–s′ — landed in C131p).
- **C.131x′**: strict height exactness below a deeper summand (deps: t′).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131t.lean` (house style of `C64.lean`;
docstring naming "Chapter C, NODES C.131t′ + C.131x′", citing the blueprint doc). End
with `#print axioms` lines for every new declaration.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; the remainder BLOCKED
  with the named missing object.
- `rg` every lemma name before use; oleans for C131a/k/p are built.
- Do NOT touch the ChapC roll-up, `leanspec/`, or other units' files (in flight:
  C131aa, C131f, C131m, C131u, F3 in ChapI).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C131t.md`: per-node LANDED/SUPPLY/BLOCKED, declarations
proved, exact verification command.
