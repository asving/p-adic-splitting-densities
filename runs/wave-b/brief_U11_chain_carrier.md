# Unit U11 — DESIGN: the MacLane chain-realization carrier (the convergence artifact)

You are a design unit (high reasoning) in the p-adic-splitting-densities campaign.
Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean project:
`leanfinal/` (mathlib v4.31.0, built; `lake env lean <file>` from `leanfinal/`; NEVER
bare `lake build`).

## The convergence (why this unit exists)

Three independent 2026-08-24 audits hit the SAME missing object:

1. **U7/U9 (FGMNCalculus)**: the class stays a hypothesis carrier because discharging it
   needs `FGMNChainRealization` — an actual MacLane chain whose keys transport to
   `keyAt`, with OPEN-DICT-1..4 (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md`
   §8, `FGMN_ADJUDICATION_2026-08-24.md`).
2. **F3 (chapter I sockets)**: I.10a/I.10b stay `True` pending the freeze's C.130
   layers (`runs/wave-b/verdict_F3.md`, missing-declarations list).
3. **C130A (freeze transcription)**: C.130b–e are BLOCKED because C.83's `DeepTower`
   carries **no polynomial key chain `Φ_i : O[x]`**, no node-point realization
   supplying stage valuations/digits/`Full` laws, and EFF.T2.11 pins no canonical
   threshold from `(DeepTower, i, F₀)` (`runs/wave-b/verdict_C130A.md` — read the exact
   blockers; also `verdict_C130B.md` if it exists by the time you read).

ONE design artifact — the chain-realization carrier — unblocks both the FGMNCalculus
discharge path and the chapter-I socket path. Your job is to design it.

## Read (in this order)

1. `docs/PROJECT_STATE.md`.
2. The three audit trails above, plus `docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`
   (the layer definitions the carrier must feed) and
   `leanfinal/Uniformity/ChapI/I10FreezeV2.lean` (`TerminalReceiver`, `ArisingCore` —
   the carrier must be compatible; REUSE, don't duplicate).
3. C.83's `DeepTower` (`leanfinal/Uniformity/ChapC/C83.lean`) and its main consumers
   (`rg "DeepTower" leanfinal/Uniformity/ChapC/ -l`); `TowerDatum` (C71.lean);
   `composedKey` (C47.lean); the landed `KeyFrame` vocabulary.
4. The EFF source rows the freeze cites: `rg -n "EFF.T2.11|EFF.T2.04|EFF.T2.05|EFF.T2.09|EFF.HETOW.13|EFF.GENTOW5.21" spec/ leanfinal/ blueprint/`
   and read the matched spec files' relevant sections.

## Design questions you MUST decide (end-to-end-proof criterion)

1. **Layered vs extended**: a NEW structure (e.g. `ChainRealization` over a `DeepTower`,
   carrying `Φ_i`, node points, stage valuations/digits, thresholds) vs adding fields to
   `DeepTower` itself (ripples through every consumer — count them before choosing).
   Prefer the conservative layered design unless it provably cannot express a needed law.
2. **What the depth-2 instances look like**: the corpus has concrete towers
   (`s2Tower`, `linTower`, `T.deepTower hπ`). The carrier must be INSTANTIABLE there —
   a carrier no landed tower can inhabit is another vacuous interface. Sketch the
   depth-2 instance for at least one landed tower and check what fields it can supply.
3. **The threshold**: what data pins EFF.T2.11's `T`? If the honest answer is "an extra
   input, not derivable", make it a carrier FIELD with the window law as a field, and
   say so.
4. **How the carrier feeds both consumers**: (a) the map
   `ChainRealization → Nonempty (FGMNCalculus W e' f' u')` (U9's adjudicated body — which
   fields become theorems, which stay hypotheses); (b) which C.130 layers become
   transcribable (name them layer by layer against C130A's blockers).

## Deliverable

`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md`: the decided design (structure
signatures in Lean), the four decisions with reasons, the depth-2 instantiability
sketch, the two consumer-feeding maps, and a NODE PLAN (30–60 min nodes, deps) for the
transcription fleet. Plus `leanfinal/scratch/U11_carrier_check.lean`: the proposed
structure signatures elaboration-checked (`lake env lean` exit 0 — no `sorry`, no axiom).

## Rules

- Do NOT edit `leanspec/`, `leanfinal/Uniformity/`, or blueprint chapter files. Your
  only writes: the two deliverables.
- Honesty: every field either carries a SOURCE obligation (name the EFF row / FGMN
  clause) or is an explicit repo-side dictionary field — no field that merely restates
  a consumer's conclusion (that is the vacuity trap this campaign has hit twice).
- Do NOT `git commit` — the orchestrator commits.
