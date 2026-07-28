# p-adic-splitting-densities — repo guide for agents

The general math/Lean workflow, writing protocols (`WRITING.md`), and state-file
discipline load from the parent folder's CLAUDE.md. This file is repo specifics only.

## Authority chain

`docs/PROJECT_STATE.md` is the single source of truth for what is proved and on what it
rests — read it before any work, update it after any milestone (it is this repo's
STATE.md in the parent CLAUDE.md's sense). The trusted-axiom audit is
`docs/AXIOM_FAITHFULNESS.md`; the standing audit log is
`lean/notes/SEMANTIC_AUDIT_LOG.md`; the math-language proof is `docs/HUMAN_PROOF.md`.

## The honesty invariant (this repo's central discipline)

**`sorry`-free ≠ non-vacuous.** Since the M9 rebase (W1–W4, 2026-07-19/21;
`lean/notes/M9_REBASE_BLUEPRINT_2026-07-19.md`) the canonical capstone is
`OM.RealInstanceV2.montes_unconditional` (fires `MontesV2.goal_theorem_montes` through the
real instance `realF2`): **non-vacuous and σ-keyed at ORDER 0**, machine-checked (value 1/4
at n=2 inert; split ≠ inert at q'=3; gates in `OM/RealInstanceV2Gates.lean`), footprint
Lean-core only. Its honest conditionality: palindromy needs the `htameFE` hypothesis
(certified non-trivial, not yet discharged), and the certified value is the DECIDED
(order-0 stratum) density — the full-density tie sits behind `hExhaust` in
`montes_unconditional_exhaustive`. The old vacuous chain + the tame axiom are quarantined
(`lean/quarantine/*_2026-07-21.lean.txt`). **Never describe the FULL theorem as
machine-checked** — drainage/exhaustiveness, the wild self-loop legs, and the faithful
tame cite are open (Phase B). Any progress claim must name the capstone, the instance,
the clause, and its conditionality.

## Build & verify (Lean pinned to 4.31.0; mathlib cache required)

- `cd lean && lake exe cache get && lake build` — full build (~8.6k jobs; built green
  2026-07-19 on this machine).
- **Gotcha:** `lake build LeanUrat` does NOT cover all modules (e.g. `OM/RealInstance`
  is outside the root import graph). Use plain `lake build`, or build the census target
  `lake build LeanUrat.AxChk_baseline` explicitly.
- Ground truth for the trusted base: `lake env lean LeanUrat/AxChk_baseline.lean`
  prints every capstone's `#print axioms` footprint. Run it after ANY change touching
  capstone-path code; a footprint regression is a stop-the-line event.
- Environmental caveat (from `lean/README.md`): `lake build` can hang at the final-job
  commit on loaded NFS nodes even when all modules are green; fall back to
  `lake env lean <file>` per module.
- Numeric cross-checks (`cd verification`, needs Python3+sympy; oracle needs cypari2):
  `python3 cert_crosschecks.py` (25 exact checks) · `python3 reconcile_om_bcfg.py`
  (BCFG moments, exact through n=5/6) · `python3 quartic_oracle.py` (PARI factorpadic).

## Axiom policy

Allowed: Lean core `{propext, Classical.choice, Quot.sound}` plus the explicitly
declared, cited axioms — the GMN theorem of the index and the Denef–Igusa cell recursion
(`PadicMeasure.AX_cellRecursion` and companions; measure route only). The Del Corso–
Dvornicich tame functional equation axiom was **RETIRED at W4 (2026-07-21)** — it could
not be faithfully retargeted to the corrected density and is now the capstone's explicit
`htameFE` hypothesis (see `notes/SEMANTIC_AUDIT_LOG.md`). Each surviving axiom has a
faithfulness entry in `docs/AXIOM_FAITHFULNESS.md`. Adding any new axiom requires a
published-source citation, a faithfulness entry, and a semantic-guardian audit pass;
this process has caught **two false axioms** already, so it is not a formality.
Exactly **one banked `sorry`** (`OM/Classifier.npVertices_stable_of_hull_preserved`,
off the capstone path). Do not add more; do not touch statements to make goals provable
(parent CLAUDE.md statement-fence applies).

## Standing obligations (priority order, per PROJECT_STATE.md)

1. ~~De-vacuify the real density instance~~ **DONE at order 0 (M9 rebase W1–W4,
   2026-07-21)**. Remaining Phase B: grow `omMenu` beyond the order-0 slice (deeper
   decided shapes, `typeOf`-keyed), discharge the wild self-loop `h_node` legs
   (`SelfLoopHNode`), prove drainage/exhaustiveness (`hExhaust`), and declare the
   faithful tame-FE cite (needs exhaustiveness + the M1 projective bridge).
2. **Extend classifier faithfulness from order ≤ 1 to order ≥ 2** (the deep-wild OM
   tower); design blueprints in `docs/in-progress/`.

## Map

`lean/LeanUrat/OM/RealInstanceV2.lean` THE capstone (`montes_unconditional`) +
`OM/RealInstanceV2Gates.lean` its gates · `MontesV2.lean` the abstract spine
(`MontesDataV2`, `goal_theorem_montes`/`goal_theorem_via_montes`) · `Goal.lean` the
measure-route `goal_theorem` · `Interface.lean` `DensityFoundation` · `Witness.lean`
trivial instance (V2-ported) · `MontesAxiom.lean` shared engine primitives + `OM/`
(~95 modules) the Okutsu–Montes classifier engine · `PadicMeasure.lean` measure route +
Denef cell recursion · `L3/L4/L5fix/L6M4/L7/M1/R1` mirror §§3–13 of
`docs/HUMAN_PROOF.md` · `lean/quarantine/` documented dead ends AND the retired
pre-rebase chain — read before re-attempting anything that looks tempting.
