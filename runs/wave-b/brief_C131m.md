# Unit C131m — dv-engine v2: tagged paid-branch recursion and the erasure theorem

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets are fine).

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §2.6 (normal form by
   structural recursion) END-TO-END including the tagged paid-branch recursion and the
   erasure theorem, §2.7 context, and your row of the §5 node table.
3. Landed inputs you MUST reuse (never redefine):
   - `leanfinal/Uniformity/ChapC/C131k.lean` — structural `xNF`/`outerNF` +
     reconstruction/uniqueness (nodes k′–l′).
   - `leanfinal/Uniformity/ChapC/C131d.lean` — `xCarry_tail_floor`,
     `xCarry_branch_wtCoeff_exact`, `xCarry_branch_WT_exact` (node e′).
   - `leanfinal/Uniformity/ChapC/C131a.lean` — `wtCoeff`, `WT`, `WT_add`, `WT_mul`.
   - C.71's `TowerDatum` (margin, hfloor): `leanfinal/Uniformity/ChapC/C71.lean`.

## Your node
- **C.131m′**: the tagged paid-branch recursion and the erasure theorem (deps: e′, l′ —
  both landed). This is the hardest single node of the wave; if the recursion's
  termination or the erasure statement resists after honest attempts, deliver the
  compiling recursion skeleton + the proved lemmas and mark the rest BLOCKED with the
  precise obstruction (do not weaken statements to force a close).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131m.lean` (house style of `C64.lean`;
docstring naming "Chapter C, NODE C.131m′", citing the blueprint doc). End with
`#print axioms` lines for every new declaration.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`.
- `rg` every lemma name before use; import the landed C131 modules (oleans built for
  C131a/k/p; build C131d's olean yourself if needed: `lake build
  Uniformity.ChapC.C131d`).
- Do NOT touch the ChapC roll-up, `leanspec/`, or other units' files (in flight:
  C131aa, C131f, C131t, C131u, F3 in ChapI).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C131m.md`: LANDED/SUPPLY/BLOCKED, declarations proved,
exact verification command, and — if blocked — the precise obstruction.
