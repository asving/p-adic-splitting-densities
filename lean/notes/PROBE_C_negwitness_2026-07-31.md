# PROBE-C record — queue items 16/17 upgraded to compiled evidence (2026-07-31)

Unit PROBE-C: two compiled probes upgrading the round-3 SUSPECT-FALSE records to
evidence-complete queue items. Both modules are NEW LEAVES (per-file gate
`lake env lean <path>`, green 2026-07-31), Lean-core axiom footprints
(`{propext, Classical.choice, Quot.sound}` — no `sorryAx`; `#print axioms` at each EOF),
zero `sorry`, zero existing statements touched.

## (1) HK-15 IAug probe — queue item 16 evidence: `LeanUrat/HC2/HK15_iaugProbe.lean`

Target: `gateChildStage` (`HC2/HK15_gateChildCarrier.lean:94–98`, sorried E-phase
skeleton) is SUSPECT-FALSE as stated — its hypothesis row admits the tuple
`(e',h',s',t') = (1,1,1,0)`, which violates (I-aug) at the gate carrier/key.

Compiled:

* `HK15Probe.gateTuple_satisfies_hyps` — the tuple satisfies the EXACT hypothesis list
  (`1 ≤ 1`, `1 ≤ 1`, `gcd 1 1 = 1`, `1·1 + 1·0 = 1`, `1 = 1 → 0 = 0`); the five Props
  are byte-identical LOCAL COPIES of the binder row `he' hh' hcop hbez he1t`
  (provenance header at the theorem).
* `HK15Probe.bStageP_w_fq : bStageP.w U31.fq = 2` — the HK-47:174 value re-derived by
  the same term `U31.bw_eq HK13R.NF_θ_fq` (HK-47 itself NOT imported; the value comes
  through the sorry-free `HK13_bStageCoreP1a` chain).
* `HK15Probe.gateTuple_iaug_violation : ¬((1:ℤ) > 1 · bStageP.w U31.fq)` and
  `HK15Probe.gateTuple_not_IAug : ¬ IAug bStageP U31.fq 1 1` — the (I-aug) violation,
  raw and named-predicate forms (`IAug` imported from the definitions-only
  `Moves/Defs`, not copied).

M1 discipline: the module does NOT import `HK15_gateChildCarrier` (holder of the
sorried `gateChildStage` + its unconditional pin universals). Import closure =
`HK13_bStageCoreP1a` chain only (grep-verified sorry-free 2026-07-31).

Consequence on record: `gateChildStage`'s stated hypotheses cannot force a faithful
D.4/D.7 child stage — any σ₁ at `(1,1,1,0)` with the claimed pins `σ₁.(e,h) = (1,1)`,
`σ₁.Φ = U31.fq` over carrier `bStageP` contradicts the (I-aug) head `h' > e'·w(Φ̂) = 2`
(HK-18's `hiaug` consumption; HK-47's TransHyp takes `(e',h') = (1,3)`, which passes).
Repair = add the (I-aug) guard to the hypothesis row — a statement-fence event already
consolidated in the sign-off queue (item 16, commit 3e8aca0); never a prover fill.

## (2) U10d negation witness — queue item 17 evidence: `LeanUrat/HC2/U10d_negWitness.lean`

Target: `zc_step_confine` (`HC2/U10_zcStep.lean:897–902`, sorried,
BLOCKED-SUSPECT-FALSE record 2026-07-31) — the rim-confinement bound quantified over
ALL pins of `Σ_{i+2}`, where the note's §C rim rule confines only FRESH cuts.

Compiled (namespace `U10dNeg`, the U1-NEG / U27_OBSTRUCTION durability pattern):

* `ZcStepConfineStmt` — LOCAL byte-identical copy of the refuted statement shape
  (binders + conclusion verbatim, wrapped as a named ∀-Prop; provenance header at the
  def). NEVER to be proved.
* `mkSigma_pinned_succ` / `mkSigma_pinned_mono` — PIN PERSISTENCE down the whole chain,
  machine-checked from the `pinTransportSystem` dite alone (spec clause (2) `Or.inl` on
  the witness branch; fallback branches keep the state verbatim). No side hypotheses.
* `mkSigma_one_pinned_of_strip` — the ROOT read pins its whole strip roster in `Σ₁`
  (existence free at read 0 — the U7 `mkSigma_recursion_zero` route via
  `clause_assign`/`mkFresh_codim`/`freshAttach_exists`; then spec clause (2) `Or.inr`
  on the strip clause, support `{c}`).
* `prevRim_le_root` — THE RIM CHAIN `prevRim n (i+1) = μ_i·cW_i ≤ μ₀·cW₀`
  (`C3_widthConfine` + coherence window containment + width chain, per step).
* `confine_bound_fails` — THE REFUTATION KERNEL, the in-file record's exact recipe: on
  ANY config in `zc_step_confine`'s hypothesis class with root `s0₀ = 0`, `0 < ustar₀`,
  `wSide₀ < n`, the coordinate `(0, wSide₀)` (box index `n−1−wSide₀`) is a read-0 STRIP
  cut (height `0 < ustar₀ = line₀.at wSide₀` by `hLineU` at `s0₀ = 0`, coherence-forced
  `Dwidth₀ = deg Φ₀ = 1`; in-band non-value), hence pinned in `Σ_{i+2}` — yet
  `prevRim n (i+1) ≤ μ₀·cW₀ ≤ wSide₀·Dwidth₀ = wSide₀`: the bound FAILS at that pin, at
  EVERY i. `hreal`/`hbox` are never consumed (strictly stronger than needed).
* `zcStepConfineStmt_false_of_config` — the ∀-sentence is FALSE at `(p, F)` given any
  such config (∃-packaged, ready for instantiation).

M1 discipline: the module does NOT import `U10_zcStep`. Vocabulary imported from its
home Defs modules (`HC2/Defs`, `MovesC/Defs`, `MovesD/Defs` — definitions-only) and the
sorry-free proved units `HC2/SharedZC`, `HC2/U7_sigmaRec`, `MovesC/C3_widthConfine`;
only the refuted statement SHAPE is locally copied.

### Honesty perimeter — the one leg NOT compiled (blocked, exact goal on record)

The charge's "one compiled legal config" leg is NOT deliverable at HEAD. The remaining
goal is exactly `zcStepConfineStmt_false_of_config`'s hypothesis:

```
∃ (n N : ℕ) (H : History p F) (keys : ℕ → Polynomial ℤ_[p])
  (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)),
  HistoryCoherent H ∧ Realizable H ∧ InBox n H ∧ 1 ≤ N ∧
  ∃ (i : ℕ) (hi1 : i + 1 < H.nodes.length) (h0 : 0 < H.nodes.length),
    (H.nodes[0]'h0).s0 = 0 ∧ 0 < (H.nodes[0]'h0).ustar ∧ (H.nodes[0]'h0).wSide < n
```

Any inhabitant forces `H.nodes.length ≥ 2` (from `i + 1 < len`), and a 2-node
`HistoryCoherent` history requires, at its final conjunct (i = 0, root ≠ recentering):
`IsNodeLift (H.nodes[0]) (H.nodes[1]).σ.Φ` AND
`TransitionCoreL (H.nodes[0]).σ (H.nodes[1]).σ (H.nodes[1]).σ.Φ e₀ h₀ zbar₀`
— the constructed child stage that is the HK-15/HK-18 Block-G frontier (sorried
skeletons at HEAD; HK-37 header: "NO CONCRETE 2-NODE GATE EXISTS ON DISK YET"), plus a
lawful `PresentSeed` instance (U15's SEED-EXIST wall). This is the SAME standing
inhabitation blocker recorded in `U1_negWitness.lean`'s honesty perimeter (task #44 /
the 2-node ReadsOf gate). NOTE: the concurrent FORGE-A delivery (commit bf023cd — the
first compiled ramified Stage at HK-47's gate read + first `StageCoreL bStageP`
assembly) is closing exactly this gap; when the 2-node gate lands, instantiate
`zcStepConfineStmt_false_of_config` (gate-shaped roots satisfy the recipe:
`s0₀ = 0 < ustar₀`, `wSide₀ < n`) to finish the last leg.

## Perimeter notes

* No existing statement, signature, definition, or hypothesis row was changed; both
  modules are new leaves outside the root import graph (per-file gate only; the trusted
  base census `AxChk_baseline` is untouched — no capstone-path code was modified).
* Concurrency note: the fleet's WIP checkpoint sweep (c361e97) committed
  `HK15_iaugProbe.lean` (final form) and the stage-1 half of `U10d_negWitness.lean`
  mid-unit; this unit's closing commit carries the kernel half + this record. The
  foreign in-flight file `MovesT/TV_A5b_forge.lean` (fleet wbbd9ior9) is deliberately
  NOT added by this unit's commit.
