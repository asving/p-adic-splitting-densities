# Unit C131u — dv-engine v2: DvAbove bridge + shadow-discrepancy identification

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets are fine).

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §3.7 (the
   all-coefficient/`DvAbove` bridge), §3.8 (from the census to C.72's actual floor —
   context for the shadow discrepancy), and your rows of the §5 node table.
3. Landed inputs you MUST reuse (never redefine):
   - `leanfinal/Uniformity/ChapC/C131p.lean` — conversion utilities (esp. the flattened
     `dvHgt`/`dvSupp`, node r′).
   - `leanfinal/Uniformity/ChapC/C131k.lean` — structural `xNF`/`outerNF` (k′–l′).
   - C.52's `DvAbove` definition and C.71 (rg in `leanfinal/Uniformity/ChapC/`).

## Your nodes
- **C.131u′**: `dvAbove_of_forall_coeff_floor` (deps: the C.52 definition, r′ — landed).
- **C.131v′**: the shadow-discrepancy semantic identification (deps: C.71, k′–l′ —
  landed).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131u.lean` (house style of `C64.lean`;
docstring naming "Chapter C, NODES C.131u′–v′", citing the blueprint doc). End with
`#print axioms` lines for every new declaration.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; the remainder BLOCKED
  with the named missing object.
- `rg` every lemma name before use; oleans for C131a/k/p are built.
- Do NOT touch the ChapC roll-up, `leanspec/`, or other units' files (in flight:
  C131aa, C131f, C131m, C131t, F3 in ChapI).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C131u.md`: per-node LANDED/SUPPLY/BLOCKED, declarations
proved, exact verification command.
