# Unit C131h — dv-engine v2: the monic-division ledger (F6/F7/F8)

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>` from
inside `leanfinal/`; NEVER bare `lake build` — module targets are fine).

## Read first
1. `docs/PROJECT_STATE.md`.
2. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` — §0, §2.5 (monic division:
   both sides of the ledger), and your rows of the §5 node table.
3. Landed inputs you MUST reuse (never redefine):
   - `leanfinal/Uniformity/ChapC/C131a.lean` — `wtCoeff`, `WT`, `WT_add`, `WT_mul`
     (+ the finite-sum helper `le_wtCoeff_sum`, node b′).
   - `leanfinal/Uniformity/ChapC/C131f.lean` — `K_T`, `coeff_K_T`,
     `composedKey_monomial_floor`, `K_T_monomial_floor`, `WT_K_T` (node g′).
   - The corpus's monic-division pattern: `div_modByMonic_unique` (rg it — PROJECT_STATE
     §5 names it as the dev-computation pattern).

## Your nodes
- **C.131h′**: one-step quotient bound F6 (deps: b′, g′ — landed).
- **C.131i′**: one-step remainder bound F7 (deps: b′, g′–h′).
- **C.131j′**: iterated quotient/digit ledger F8 (deps: h′–i′).

## Deliverable
ONE new file `leanfinal/Uniformity/ChapC/C131h.lean` (house style of `C64.lean`;
docstring naming "Chapter C, NODES C.131h′–j′", citing the blueprint doc). End with
`#print axioms` lines for every new declaration.

## Rules (non-negotiable)
- NO `sorry`, NO new axioms, NO `unsafe`. Land what is proved; the remainder BLOCKED
  with the named missing object.
- `rg` every lemma name before use; oleans for C131a/d/k/p/aa are built (build
  C131f's yourself if needed: `lake build Uniformity.ChapC.C131f`).
- Do NOT touch the ChapC roll-up, `leanspec/`, or other units' files (in flight:
  C131v, C131ac, C130 units in ChapC too — their files are `C131v.lean`,
  `C131ac.lean`, `C130*.lean`; never write those).
- Do NOT `git commit` (sandbox mounts `.git` read-only) — the orchestrator commits.

## Final act
Write `runs/wave-b/verdict_C131h.md`: per-node LANDED/SUPPLY/BLOCKED, declarations
proved, exact verification command.
