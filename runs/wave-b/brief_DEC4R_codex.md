# Unit DEC4R (codex HIGH) — the chapter-C chain-blockers plan

You are a design unit in the p-adic-splitting-densities campaign. A Fable predecessor
(DEC4) died in an API storm AFTER landing its elaboration probes but BEFORE writing the
plan doc — you inherit the probes and finish the job. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(Lean 4.31.0 + mathlib, pre-built; `lake env lean <file>` FROM leanfinal/; NEVER bare
`lake build`).

## The inheritance

`leanfinal/scratch/DEC4_check.lean` (181 lines) — the predecessor's probes, whose header
names YOUR deliverable (`BLOCKERS_PLAN_2026-08-26.md`):
* PROBE F2-1: the C.27 norm↔resultant SYMMETRY bridge is derivable from landed B53a
  (`quotKeyEquiv`) + B53c (`length_quot_eq_addVal_norm`).
* PROBE F2-2: the norm-nonzero transfer across the symmetry (both-sides form).
* PROBE F1-1: the conditional-on-frontier landing pattern for the C.35 family typechecks.
* PROBE F3-1/F3-2: the RB3-blocked ∀-closures (`refine_invariants`, `shadow_persistence`)
  elaborate against landed vocabulary; `dev_add_of_monic` fires at the needed shape.
FIRST ACTION: run `lake env lean scratch/DEC4_check.lean` from leanfinal/ and report its
status in your verdict. If it errors, repair or honestly demote the affected probe's claim.

## The charge (PROJECT_STATE §4 item 4)

Produce the enactment plan for the remaining chapter-C blockers:
1. **The C.35 `BlockFrontier` 8-row family** — read blueprint/CHAP-C_tower_grammar.md's
   C.35 rows + leanfinal/Uniformity/ChapC/C35.lean (+C35b) for what is landed; plan the
   8 rows as conditional-on-frontier landings per probe F1-1's pattern.
2. **General C.27's two mechanisms** (runs/wave-b/verdict_AC15C27.md names them): the
   norm↔resultant bridge (probes F2-1/F2-2 say: derivable, no new mathematics — plan the
   nodes) and ramified level-1 exactness (the B53b analogue, completion-free — size it
   honestly; if it needs a genuinely new mechanism, say so and name it).
3. **RB3's two gaps** (runs/wave-b/verdict_RB3.md): the Hensel refinement step and the
   upward height bridge. Probes F3-1/F3-2 establish the statements elaborate — plan the
   proof decomposition (examples-first if the mechanism is unclear: small numeric
   instances in a python cert before Lean nodes).

HELD items you must NOT plan (adjudicated elsewhere; list them in the doc's fence
section): C.100 (OPEN-EVAL-ISO), C.102 + one_shape's htie (OPEN-LETTERS), peel_row_law
(undesigned PeelLeg), hprev/hcop at μ₃ (unit DEC3R's decision).

## Read

docs/PROJECT_STATE.md; the probes file; verdict_AC15C27.md; verdict_RB3.md; verdict_RB1.md
+ verdict_RB2.md (context); blueprint/CHAP-C_tower_grammar.md's C.27/C.35/RB rows;
leanspec/Leanspec/ChapC.lean's signed statements for the blocked names (read-only);
the landed B53a/B53b/B53c files (leanfinal/Uniformity/ChapB/).

## Deliverables (write INCREMENTALLY)

1. docs/in-progress/BLOCKERS_PLAN_2026-08-26.md — per-blocker node tables (node id,
   statement sketch, named landed inputs, mechanism, sizing), the fence section, and an
   ordering recommendation (which blocker first and why).
2. leanfinal/scratch/DEC4_check.lean — extend with any NEW probes your plan's claims
   need (keep the existing probes; zero sorry, zero axiom, exit 0).
3. runs/wave-b/verdict_DEC4R.md — LANDED/SUPPLY/BLOCKED verdict, ≤2 pages.

## Rules

Do NOT edit leanspec/, leanfinal/Uniformity/, roll-ups, or files other than your
deliverables. Do NOT git add/commit. Cite file:line for every corpus claim.
