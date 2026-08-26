# Unit BW1 (codex, default effort) — BLOCKERS_PLAN wave 1: the probe-complete landings

You are a transcription unit in the p-adic-splitting-densities campaign. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(Lean 4.31.0 + mathlib, pre-built; `lake env lean <file>` from leanfinal/; NEVER bare
`lake build`).

## The charge

docs/in-progress/BLOCKERS_PLAN_2026-08-26.md (READ the relevant node tables; verdict:
runs/wave-b/verdict_DEC4R.md) orders its enactment: "land the already-proved norm bridge
and shadow linearity first." Every fact in your scope is ALREADY PROVED in
leanfinal/scratch/DEC4_check.lean (246 lines, green, 10 decls Lean-core) — your job is
the corpus landing per the plan's node table, NOT new mathematics:

1. The norm↔resultant valuation bridge (probe F2-1, DEC4_check.lean:42-66): B53a's
   `quotKeyEquiv` + B53c's `length_quot_eq_addVal_norm` give
   `v(N_{O[x]/(g)}(Φ mod g)) = v(N_{O[x]/(Φ)}(g mod Φ))` for monic positive-degree
   polynomials.
2. The corrected F2-2 scalar-membership transfer, BOTH orientations
   (DEC4_check.lean:77-131). Use the plan's honest contract wording: ramified exactness
   SUPPLIES scalar membership; quotient symmetry TRANSFERS it. Do not state the refuted
   bare norm-nonzero implication.
3. RB3's linearity API (DEC4_check.lean:190-226): `biRead_add`, monicity of
   `biRead F (composedKey T)`, `shadowDev_add`.

## Protocol

1. Read the plan's node table for these items: exact target names, namespaces, and file
   placement. Follow the plan; where the plan is silent on placement, follow the local
   convention (one new file in leanfinal/Uniformity/ChapC/ or ChapB/ named per its
   neighbors; look at C131-series headers for the docstring/dated-note style).
2. Adapt the proofs from DEC4_check.lean (do NOT edit that file). Keep statements at the
   generality the probes proved — no narrowing, no strengthening.
3. Every new file: `lake env lean` exit 0, zero sorry, zero new axiom, `#print axioms`
   footer (expect Lean-core only) — put the footer in the verdict.
4. If a landing needs a name/import that collides (check with rg first — the corpus has
   known private-name collisions, see docs/in-progress/SIMPLIFICATION_MAP_2026-08-26.md's
   flagged slot_eq cluster), pick a fresh name and record the deviation.

## Deliverables

Your ONE new landing file (or two if the plan's table splits ChapB/ChapC) +
runs/wave-b/verdict_BW1.md (LANDED per declaration, file:line, AxChk footer, deviations).
Do NOT git add/commit. Do NOT touch leanspec/, roll-ups, scratch/DEC4_check.lean,
leanfinal/Uniformity/ChapI/, or any file outside your deliverables.
