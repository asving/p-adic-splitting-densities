# Unit MLIFT (FABLE, math-first) — H.116b4 research cores II-a + II-b: one-grade lifting + the pushforward induction

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. You are a MATH unit:
rigorous informal mathematics + numeric certificates, NOT Lean (optional probe allowed).
Rigor paramount; unproven steps become named OPEN lemmas; cases ≠ proof.

## The problem (map rows GR-9 and GR-10/11 of docs/in-progress/H116B4_MAP_2026-08-26.md)

The extended battery (runs/wave-b/h116b4_battery.py, ALL CHECKS PASSED —
runs/wave-b/out_DEC5R_battery.log) has FOUND the mechanism numerically; it now needs proof
over every complete DVR:

* **II-a (one-grade nonlinear lifting, row GR-9):** every one-grade multiplication map is
  AFFINE with a level-fixed linear part Tₙ; a node is live exactly when its obstruction
  lies in the image; live nodes have exactly #ker(Tₙ) children. CAUTION the battery itself
  pins: the nonlinear fibre is NOT the linear kernel as a set (CELL-2: only 27 of 81 points
  coincide — out_DEC5R_battery.log:24) — only the COUNT transfers. Needed: the filtration
  estimates and base-stability making this exact over an arbitrary complete DVR (not just
  the prime residue-field models).
* **II-b (iteration, rows GR-10/11):** the induction invariant is UNIFORMITY OF THE
  AGGREGATE OBSTRUCTION PUSHFORWARD ON ITS REACHABLE SUPPORT (verified in every tree cell:
  out_DEC5R_battery.log:49/:66/:75). Needed: the universal proof from the filtered Smith
  data that this invariant propagates level-to-level. Downstream is mechanical (positivity
  + assembly via landed `exists_peel_finset`, leanfinal/Uniformity/ChapH/H116b1.lean:551).

## Read (in order)

1. docs/in-progress/H116B4_MAP_2026-08-26.md rows GR-9, GR-10/11 (+ its battery-check names).
2. runs/wave-b/h116b4_battery.py (esp. the DEC5R extension from ~line 479: the affine
   check, the obstruction-image liveness check, the pushforward-histogram check) +
   out_DEC5R_battery.log.
3. leanfinal/notes/H116B4_OUTLINE_2026-08-18.md — WHOLE.
4. blueprint/CHAP-H_general_induction.md H.116b rows + fence A-H.7/F1 (REPLANT CLOSED —
   no fibre-to-fibre replant map, machine-refuted).

## Method

Examples-first extensions: if a filtration estimate or stability claim isn't readable off
the existing tables, write verification/openmath/h116b4_lift_cert.py (NEW file; do NOT
edit the battery) to expose it before proving. Coordinate note: a sibling unit (MSMITH)
owns the restricted-Smith identification — you may CITE its target statement as a named
input (state it precisely as an interface lemma), do not prove it yourself.

## Deliverables (write INCREMENTALLY to disk)

1. docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md — rigorous informal proofs of II-a and
   II-b (or honest partials + named OPEN gaps), interface lemma to MSMITH stated exactly,
   and a formalization-trivial node decomposition for the Sonnet fleet.
2. verification/openmath/h116b4_lift_cert.py + output log (only if needed).
3. runs/wave-b/verdict_MLIFT.md (≤2 pages, PROVED/PARTIAL/BLOCKED per claim).

No git commits. No edits outside your deliverables (+ optional
leanfinal/scratch/MLIFT_probe.lean). Final message ≤25 lines; detail on disk.
