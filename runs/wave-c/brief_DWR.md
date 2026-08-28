# UNIT DWR — REVISE the deep-witness blueprint (post-DWV REJECT) + absorb the shared level-2 engine root

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

DWC delivered the deep-witness campaign blueprint
(docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md; verdict runs/wave-c/verdict_DWC.md).
DWV's fresh-context adversarial read (runs/wave-c/verdict_DWV.md — READ FIRST, every
finding) returned **REJECT** with two CRITICAL errors and five gaps:
- C1: the mass-two input `F0 = leaf²` forces `quot.F = quot.Φ = leaf`, contradicting
  `BlockData.hkeyfree` (self-coprimality of a monic degree-16 polynomial).
- C2: `R₅(leaf²) = (X+1)²` has ord_ψ = 2 — GN's multiplicity-one clause never selects one
  copy; the plan's C4 node is REFUTED as stated, not merely risky.
- Gaps: the cert checks neither key-freeness nor multiplicity; three missing gates
  (quotient-BlockData key-freeness, actual `ord_ψ(R_λ(F0)) = 1`, GN valuation/key-index
  alignment); the RecenterStep amendment lacks provenance binding for `B'.F`/`B'.T`; the
  occurrence→universal quantifier gate is absent from the DAG (one C3/C5 occurrence does
  NOT give `LadderSupplyLive₂`'s universally quantified fields); several nodes
  (G0/G1, D3-03/D3-10, C3, R3–R5) are research-grade mislabeled as 30–60-min
  transcription.
DWV's independent controls CONFIRMED the tower numerics (all floors margin exactly one,
both normalizer rows) — the tower itself stands; the failure is the mp1 INPUT plan and
the gate/grading hygiene.

NEW SHARED ROOT (post-DWV finding, unit F13A — runs/wave-c/verdict_F13A.md): the signed
F1.4–F1.6 rows need a LEVEL-2 TWIN of Theorem M clauses 2/3 (`dv2ResPoly`/`dv2Res`
product laws at the level datum) — the same "new multiplicative operator core" as the
blueprint's D3-03/D3-10. One design must serve both consumers.

## Your charge

1. READ: verdict_DWV in full; the blueprint in full; verdict_F13A (the level-2 twin
   demand's exact shape); verdict_SRX (the GNCitePayload surface gaps — the missing
   Newton-slope membership predicate and the residual-operator indexing);
   C134dv2g.lean's level-2 support engine (what exists one level up already);
   C133mh3.lean's §3-route headers (the level-1 proof pattern that would be twinned).
2. REDESIGN the mp1 input: a genuine occurrence where GN Thm 2.3's hypotheses hold
   HONESTLY — the input's slope residual must have ord_ψ = 1 for the selected ψ while
   the RECENTERING is genuine (Λ ≠ 0) and the quotient block is key-free. Work the
   candidates numerically first (extend verification/dwc_tower_cert.py with the
   key-freeness and multiplicity predicates DWV showed missing — the cert must now
   REFUTE leaf² itself as a control): e.g. F0 = leaf · h with h monic of the right
   degree and residual coprime to ψ (mass μ = 1 at the leaf — does MP1StepCore's hmass
   then admit it? re-derive hmass's actual demand from I10RecenterLive.lean rather than
   assuming); or a two-distinct-keys input; or an occurrence at the μ4 level instead of
   μ5. If NO honest occurrence exists in this tower, say so — that is a stop-the-line
   finding about MP1CarrierLive's inhabitability (and would force re-examining the mp1
   field's shape, an A-I.8-grade question — flag, do not enact).
3. REVISE the blueprint IN PLACE (append a dated [DWR 2026-08-28] revision section +
   edit the node table with clearly marked [DWR] rows — never silently rewrite DWC's
   text): the corrected input plan; the three missing gates added; the
   occurrence→universal quantifier gate added as an explicit node (what IS the honest
   universal-supplier statement given one occurrence? — likely the WLE exporter's
   per-witness quantification); provenance binding for RecenterStep's B'.F/B'.T; the
   research-grade nodes re-graded with honest sizings and, for the LEVEL-2 ENGINE
   (D3-03/D3-10 + F13A's twin), a dedicated sub-blueprint section (the level-1 §3
   coefficientwise route as the template — state the level-2 statements in landed
   vocabulary, F1.4–F1.6's exact demands as the acceptance tests).
4. Re-run the extended cert; report counts.

## Deliverables

- The revised blueprint (in-place per above) + `runs/wave-c/verdict_DWR.md` (what
  changed, the corrected input with its cert rows, the re-graded node/gate table, the
  level-2 engine sub-blueprint's node list, the single highest-risk node).

## Rules

No git commits. No edits to landed .lean/leanspec files. Numerics before prose (the
cert is the arbiter). Honest infeasibility findings are first-class. Owner's paper never
citable.
