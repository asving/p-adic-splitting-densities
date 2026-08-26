# Unit DEC5R (codex HIGH) — the H.116b4 examples-first map

You are a research-mapping unit in the p-adic-splitting-densities campaign. A Fable
predecessor (DEC5) died in an API storm AFTER its numeric battery PASSED ALL CHECKS but
BEFORE writing the map — you inherit the battery and write the map. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities.

## The inheritance

* `runs/wave-b/h116b4_battery.py` — the battery (runs in ~70s: `python3
  runs/wave-b/h116b4_battery.py`; needs sympy). Re-run it yourself and confirm
  "ALL CHECKS PASSED".
* `runs/wave-b/out_DEC5_battery.log` — the passed run: GR-9ii (branching UNIFORM at every
  level — one K per level across all nodes), the leaf-count law (leaves = ghost ×
  image-multiplicity), GR-10 (level profiles IDENTICAL across residue classes), across
  CELL-1/2/4 parameter cells at multiple twists.

## The charge (PROJECT_STATE §4 item 5, examples-first discipline)

H.116b4 = `planted_presentation_card` — the last research-open node of chapter H's
`betaExtract_fiber_card` assembly (H.116b re-split, blueprint/CHAP-H_general_induction.md
row A-H.7): THE COUNT at the GAUGE-RESULTANT route — uniform PAIR-space presentation
multiplicity, `v(Res) = μμ'·min(k,k')` b-independent. Standing outline:
`leanfinal/notes/H116B4_OUTLINE_2026-08-18.md` (~700 lines — read it WHOLE; its closing
verdict is "research-open, numerically certified, statement unchanged"). The examples-first
discipline (docs/HEURISTICS_AND_INTUITIONS_2026-08-08.md): read WHY the law holds off the
battery's tables, derive the proof's case-split from the observed genres, THEN write the
node plan.

Your job: turn the battery's passed invariants into the 5-row proof map — for each of the
five rows of H.116b4's outline decomposition: (a) what the battery shows (quote the
specific check + cell), (b) the mechanism the numbers reveal (e.g. WHY is branching
uniform at every level? what makes dead-node counts follow the observed pattern? where
does min(k,k') enter?), (c) the Lean-facing statement sketch with named landed inputs,
(d) REUSE vs NEW mechanism, (e) honest sizing or BLOCKED-BECAUSE.

If a row's mechanism is NOT readable off the existing battery, EXTEND the battery
(append new checks to h116b4_battery.py — keep all existing checks passing) rather than
speculate: constructed instances over sweeps, per the repo discipline.

## Read

docs/PROJECT_STATE.md; the outline (WHOLE); blueprint/CHAP-H_general_induction.md rows
H.116/H.116b1–b4 + fence A-H.7/F1 (**the peel-shift-REPLANT route is CLOSED,
machine-refuted — do not re-attempt it**); runs/wave-b/verdict_XSC.md's H.116b row;
verification/openmath/OM2_h116b_gauge_resultant.py (the 65/65 certificate the blueprint
row cites); leanspec/Leanspec/ChapH.lean's signed `betaExtract_fiber_card` and the b1–b4
statements (read-only).

## Deliverables (write INCREMENTALLY)

1. docs/in-progress/H116B4_MAP_2026-08-26.md — the 5-row map as specified above + an
   ordering recommendation.
2. runs/wave-b/h116b4_battery.py — extended only if needed (all checks passing; save the
   new run log as runs/wave-b/out_DEC5R_battery.log).
3. runs/wave-b/verdict_DEC5R.md — LANDED/SUPPLY/BLOCKED verdict, ≤2 pages.

## Rules

Do NOT edit leanspec/, leanfinal/, blueprint/, or files other than your deliverables.
Do NOT git add/commit. Cite file:line (or battery check name) for every claim.
