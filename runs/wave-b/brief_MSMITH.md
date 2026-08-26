# Unit MSMITH (FABLE, math-first) — H.116b4 research core I: the restricted Smith identification

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. You are a MATH unit:
the deliverable is rigorous informal mathematics + numeric certificates, NOT Lean (an
optional elaboration probe is allowed). Rigor is paramount: every step justified; a pattern
verified on cases is a conjecture, not a proof; unproven steps become named OPEN lemmas.

## The problem (map row GR-4–8 of docs/in-progress/H116B4_MAP_2026-08-26.md)

H.116b4 (`planted_presentation_card`, signed at leanspec/Leanspec/ChapH.lean:2963) needs
THE COUNT at the gauge-resultant route: uniform pair-space presentation multiplicity. The
determinant valuation is established (`v(Res) = μμ′·min(k,k′)`, b-independent, certified
65/65 in verification/openmath/OM2_h116b_gauge_resultant.py), and exhaustive small-case
lists are rigid — but **determinant valuation does not determine the restricted truncated
Smith invariant list** (leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:422 region). Needed:
an explicit determinantal-ideal argument identifying the restricted/truncated invariant
list, in the two named regimes — EQUAL-SLOPE and ORDERED-UNEQUAL-SLOPE.

## Read (in order)

1. docs/in-progress/H116B4_MAP_2026-08-26.md — row GR-4–8 + the ordering recommendation.
2. leanfinal/notes/H116B4_OUTLINE_2026-08-18.md — WHOLE (~700 lines; the standing outline;
   its §§ around line 422 state exactly what's missing).
3. runs/wave-b/h116b4_battery.py + runs/wave-b/out_DEC5R_battery.log (the passed checks —
   your ground truth tables), verification/openmath/OM2_h116b_gauge_resultant.py.
4. blueprint/CHAP-H_general_induction.md rows H.116/H.116b1–b4 + fence A-H.7/F1.

## Method (repo discipline, binding)

Examples-first: compute restricted Smith forms for a systematic family of instances FIRST
(write verification/openmath/h116b4_smith_cert.py — a NEW file; do NOT edit the battery or
OM2_*), read the mechanism off the tables, derive the case split from observed genres, THEN
prove. Constructed counterexamples over sweeps: if a strengthening looks true, derive the
defeat equations and solve or prove infeasible. HARD FENCES: the peel-shift-REPLANT route
is CLOSED (machine-refuted — blueprint fence A-H.7/F1); prime-residue-field numerics cannot
discharge the all-complete-DVR quantifier — the final argument must be general (Smith
normal form over the DVR, determinantal ideals Fitting-style).

## Deliverables (write INCREMENTALLY to disk — API storms kill agents; committed prose survives)

1. docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md — the rigorous informal proof (or
   honest partials: proved lemmas + named OPEN gaps with exact statements), the case split,
   and a formalization-trivial node decomposition (each node: statement, inputs, sizing) so
   a later Sonnet fleet can transcribe it.
2. verification/openmath/h116b4_smith_cert.py + its output log (exact arithmetic).
3. runs/wave-b/verdict_MSMITH.md (≤2 pages, PROVED/PARTIAL/BLOCKED per claim).

No git commits. No edits outside your three deliverables (+ optional
leanfinal/scratch/MSMITH_probe.lean). Final message ≤25 lines; detail lives on disk.
