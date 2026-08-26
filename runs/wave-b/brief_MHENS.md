# Unit MHENS (FABLE, math-first) — the dv-graded one-slope Hensel engine (the C.34/C.35 root)

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. You are a MATH unit:
rigorous informal mathematics + a design fit to the landed corpus, NOT Lean-first (optional
elaboration probe allowed). Rigor paramount; unproven steps become named OPEN lemmas.

## The problem (BLOCKED mechanism 1 of docs/in-progress/BLOCKERS_PLAN_2026-08-26.md)

The C.35 `BlockFrontier` family's root: a **dv-graded one-slope residual-primary Hensel
existence-and-uniqueness engine**. The declared cite `fgmn_dv_exact_mul` (C66b — FGMN
J. Algebra 427 (2015) Thm 2.8 + Cor 4.12(3); leanfinal/Uniformity/ChapC/C66b.lean:85-107)
certifies the dv-height of a PRODUCT once the factors exist; nothing landed CONSTRUCTS the
factors. Needed: given a one-slope dv-graded situation with residually-primary initial
data, existence + uniqueness of the block factorization (the engine that turns the eight
conditional `_of_frontier` rows of C.35 into unconditional statements).

## Read (in order)

1. docs/in-progress/BLOCKERS_PLAN_2026-08-26.md — the C.35 section IN FULL (node
   statements, exit gates, what the plan already prices) + runs/wave-b/verdict_DEC4R.md.
2. leanfinal/scratch/DEC4_check.lean (the landed probes — esp. F1-1's conditional pattern).
3. The landed neighborhood: leanfinal/Uniformity/ChapC/C34.lean, C35.lean, C35b.lean
   (the degree rider at :375-390 is INDISPENSABLE — the plan preserves it), C48 (the
   protected `fullSide_block` exact-degree shape), C66b.lean (the cite's exact scope).
4. docs/HUMAN_PROOF.md — the section this engine mirrors (search the dissection/Hensel
   language) + docs/HEURISTICS_AND_INTUITIONS_2026-08-08.md.
5. What mathlib already has: search seriously (`rg` under leanfinal/.lake for Hensel,
   `Polynomial.hensel`, adic lifting) — the engine may be a graded reskin of a landed or
   mathlib Hensel rather than new mathematics. Say so honestly if it is.

## Method

State the engine's THEOREM first (existence; uniqueness; the exact hypotheses — one-slope,
residually primary, monic normalization), then the proof: the standard successive-
approximation induction in the dv-graded valuation, with the contraction estimate made
explicit. Examples-first if the induction step is unclear: a small numeric instance
(π-adic, by hand or a short cert script verification/dv_hensel_cert.py — NEW file).
Constructed counterexamples for hypothesis necessity (drop one-slope → exhibit failure, or
prove it's droppable).

## Deliverables (write INCREMENTALLY to disk)

1. docs/in-progress/HENSEL_ENGINE_2026-08-26.md — the engine theorem(s) + rigorous proof
   (or partials + named OPEN gaps), hypothesis-necessity notes, and a formalization-trivial
   node decomposition wired to the plan's C.35 rows (each node: statement, landed inputs,
   sizing).
2. Optional: verification/dv_hensel_cert.py + log; optional leanfinal/scratch/MHENS_probe.lean.
3. runs/wave-b/verdict_MHENS.md (≤2 pages).

No git commits. No edits outside your deliverables. Final message ≤25 lines; detail on disk.
