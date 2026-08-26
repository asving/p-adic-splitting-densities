# Unit MBRIDGE (FABLE, math-first) — RB3's upward budget→height bridge

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. You are a MATH unit:
certificate-first mathematics, NOT Lean-first (optional probe allowed). Rigor paramount.

## The problem (BLOCKED mechanism 4 of docs/in-progress/BLOCKERS_PLAN_2026-08-26.md)

RB3's `shadow_persistence` decomposition is otherwise ready (its linearity API —
`biRead_add`/`shadowDev_add`/monicity — is probe-proved and being landed by concurrent unit
BW1). The one genuinely-new mechanism: **the upward bridge from a coefficient budget
(`hbudget`) to a shadow-discrepancy height lower bound `dv2Hgt ≥ θ + 1`**. The plan
mandates EXAMPLES-FIRST: a Python certificate exposing the mechanism BEFORE any proof.

## Read (in order)

1. docs/in-progress/BLOCKERS_PLAN_2026-08-26.md — the RB3 section IN FULL (its certificate
   SPECIFICATION — implement exactly that) + runs/wave-b/verdict_RB3.md (the original gap
   diagnosis) + runs/wave-b/verdict_DEC4R.md.
2. The landed DOWNWARD machinery you are inverting: leanfinal/Uniformity/ChapC/C131af.lean
   (AF-3/AF-4 — `towerLocus_dev_strict_floor`, the strict floor `(μ₂−j)E₂+1` via
   ultrametricity) and C131ag.lean (the conversion stack). Read their proofs — the upward
   direction likely reuses the same wtCoeff/WT bridge in reverse.
3. The worked example bank: leanfinal/Uniformity/ChapC/C131uf.lean — `s2Witness` with its
   explicit 12-slot budget and EXACT digit height 31 (the first landed non-drain finite
   height) — your best concrete instance; and C123r.lean (the drain contrast).
4. leanspec's signed `shadow_persistence` + `refine_invariants` closures (grep
   leanspec/Leanspec/ChapC.lean) — the exact target shapes; scratch/DEC4_check.lean:147-188
   shows they elaborate.

## Method

1. FIRST write and run verification/rb3_bridge_cert.py (NEW file) per the plan's spec:
   sweep perturbation families at the landed towers, tabulate (budget slack → observed
   dv2Hgt of the shadow discrepancy), and locate where θ+1 is tight vs slack.
2. Read the mechanism off the table (which slot carries the extremal weight; where
   ultrametric equality-off-ties fires), derive the case split, THEN prove the bridge.
3. Constructed counterexamples: if the bridge seems to hold without a hypothesis the signed
   statement carries, derive the defeat equations and solve or prove infeasibility.

## Deliverables (write INCREMENTALLY to disk)

1. verification/rb3_bridge_cert.py + its output log.
2. docs/in-progress/RB3_BRIDGE_PROOF_2026-08-26.md — the rigorous informal proof (or
   partials + named OPEN gaps) + formalization-trivial node decomposition wired to the
   plan's RB3 rows.
3. runs/wave-b/verdict_MBRIDGE.md (≤2 pages).

No git commits. No edits outside your deliverables (+ optional
leanfinal/scratch/MBRIDGE_probe.lean). Final message ≤25 lines; detail on disk.
