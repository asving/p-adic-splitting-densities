# QUEUE EXECUTION LOG — 2026-07-31 (append-only)

Per-item execution records for THE CONSOLIDATED SIGN-OFF QUEUE + QUEUE
ADDITIONS of notes/BRIDGE_ADJUDICATIONS_2026-07-30.md (Asvin sign-off
2026-07-31, all 21 items at preferred options). Each executing agent appends
its own section atomically; never edit another item's section.

## Item 20 — KA4c ka4c_nsFiberUnion_null (executed 2026-07-31, agent: item-20)

AUTHORIZATION: Asvin 2026-07-31 verbatim "Sign-off granted on all 21 items as
preferred, execute the queue" (BRIDGE_ADJUDICATIONS_2026-07-30.md, ASVIN
SIGN-OFF block; preferred option for item 20 = add the 2 ≤ n hypothesis unless
frac_empty demonstrably ripples less).

DECISION CHECK (the adjudicated first step, `rg XCtx` census):
- XCtx constructions in the build graph: ZERO — every module (Kernels/KA4c,
  Kernels/E0Route, Kernels/WeightChargeRed, MovesX/KE1-KE9, XG2*, XG3, XD1,
  XF10, MovesU/SlotsG12b) takes `C : XCtx n p` as a PARAMETER; the one real
  instance is the open Phase-B XFamily inhabitation obligation.
- BUT two note-side compiled refutation witnesses CONSTRUCT XCtx and would
  break on a new field: notes/XE2_refutation_witness.lean:73 (`ctx0`),
  notes/XE3_REFUTATION_2026-07-27.lean:106 (`ctxD`).
- AND three standing in-file adjudications freeze the interface — "never a
  new `XCtx` field": MovesX/KE1.lean:25, KE2.lean:20-23, KE3.lean:21.
- Both null anchors already require 2 ≤ n: XF10 `discZeroNull (h2 : 2 ≤ n)`,
  XF8 `tailZero`; the XG3.lean:31 precedent derives `frac ∅ = 0` exactly by
  `frac_mono` into the null `discZero` under `hn : 2 ≤ n`.
- Downstream Lean consumers of ka4c_nsFiberUnion_null: NONE at HEAD (rg; no
  module imports Kernels.KA4c; `escape_of_x3drain` inlines its own
  Option-reindexed glue anchored on the null InfTree leg, hypothesis-free).
DECISION: 2 ≤ n (the preferred option) — frac_empty ripples strictly MORE
(2 note-side witnesses + 3 frozen-interface rulings + a bigger XFamily
inhabitation obligation), not less.

EXECUTED (LeanUrat/Kernels/KA4c.lean):
- `ka4c_nsFiberUnion_null` gains `(h2 : 2 ≤ n)` (before `C`, the XF10
  convention); import LeanUrat.MovesX.XF10 added.
- Empty-nsIdx corner PROVED: union = ∅ by `Set.iUnion_of_empty`; `frac ∅ = 0`
  by `frac_mono` into `discZero` + `discZeroNull n p h2 C` + `frac_nonneg`
  (the XG3.lean:31 corpus precedent). The BLOCKED-CORNER obstruction record
  is superseded and condensed into the theorem's STATEMENT-REPAIR RECORD
  docstring (in-file record, per rule 5).
- R10 fallback KEPT untouched: `DrainIdent` (the pre-typed named
  identification hypothesis) + both proved seam theorems
  `blockDrain_of_drainIdent`, `escape_of_x3drain`.

VERIFICATION:
- `lake env lean LeanUrat/Kernels/KA4c.lean` GREEN, zero output.
- `lake build LeanUrat.Kernels.KA4c` SUCCESS (8573 jobs).
- #print axioms (fresh oleans): ka4c_nsFiberUnion_null,
  blockDrain_of_drainIdent, escape_of_x3drain ALL Lean-core
  {propext, Classical.choice, Quot.sound}. (First check hit the stale
  pre-repair olean and showed sorryAx — rebuilt, clean.)
- KA4c.lean sorry count: 0. THE ROW CLOSES (census row
  REMAINING_CENSUS_2026-07-31.md:101 = Kernels/KA4c.lean:114 discharged).

M1 HYGIENE (rule 3): no compiled countermodel/probe of the OLD form exists
(the corner was sorried with a prose obstruction record, never refuted by a
leaf module; rg "nsFiberUnion" hits only KA4c + ledger/census notes) — no
leaf note owed.

CAPSTONE PATH (rule 4): not touched — KA4c is a leaf module imported by
nothing; AxChk_baseline diff not required.

NOTE FOR THE ORCHESTRATOR (per the item text): with the row closed,
`DrainIdent`'s named-hypothesis status can be REVISITED — the prover attempt
to construct a `DrainIdent` instance at the real pool from the
SeriesData/XCtx vocabulary is now unblocked as its own unit (it waits on the
same Phase-B XCtx/XFamily inhabitation as everything else; nothing in KA4c
fences it).

## Item 13 — PolPin.total re-scope + (†15) re-attempt (executed 2026-07-31, agent: items-8+13)

AUTHORITY: Asvin 2026-07-31 verbatim "Sign-off granted on all 21 items as preferred,
execute the queue" — item 13 preferred option (ii): re-key `OffsetPPin.total` to
HistoryCoherent nodes (note-faithful, per note 4665–4666's L1 run-node totality).

EXECUTED (statement repair, ratified PolPin.lean):
- `OffsetPPin.total` re-keyed: `∀ (H : History p F), HistoryCoherent H → ∀ i hi,
  (H.nodes[i]'hi).species = recentering → Realizes (H.nodes[i]'hi) (pol.liftOf …)`.
  The other four laws (realizes_ne_zero / support_forced / realizes_unique /
  digits_prescribed) are UNCHANGED (they are Realizes-conditional, not forcing).
- In-file consumers re-keyed to the same granularity: `lift_ne_zero`,
  `lift_center_realizer`, `no_pin_of_wrong_value`, `no_pin_of_wrong_weight`.
  `not_realizes_bare_ne_zero`, `CD_canonical` untouched.

M1 HYGIENE (rule 3 — the OLD form's compiled countermodels):
- `R7_pinProbe.lean` gains the FROZEN verbatim old structure `OffsetPPinBare`
  (bare-Node `total`) + a dated M1 header note; `offsetPPin_forces_stage_unramified`
  and `offsetPPin_isEmpty_of_ramified` re-pointed at it, proofs byte-unchanged.
- `R7_ramifiedForge.lean`: `offsetPPin_isEmpty_unconditional` / `no_offsetPPin`
  re-pointed at `OffsetPPinBare` + dated note. The countermodels refute ONLY the
  historical form; no compiled negation witness against the repaired statement exists
  (probe node unreachable: root_iff kills index 0, coherence binds frames at index ≥ 1,
  and HK22_twoNodeGate certifies ramified child frames unreachable pre-HK-06).

RE-ATTEMPT of canPolicy/canPolicy_pin (TreeCan.lean:485,492 — the census critical-path
head): **REDUCED-COMPILED, NOT DISCHARGED.** New leaf `MovesD/R7_polFillReduction.lean`
(0 sorry, Lean-core {propext, Classical.choice, Quot.sound}):
- `CanRealizes` (the realizer laws at one node, lift-blind), `canLiftOf`/`canPolicyC`
  (choice-based policy, `blind` = rfl),
- `RunRealizerExists` — THE ONE RESIDUAL LAW as a named Prop,
- `canPolicyC_pin : RunRealizerExists p F → OffsetPPin (canPolicyC p F)` — the WHOLE
  repaired pin from that one Prop (all five laws proved),
- `interior_recentering_unramified` / `interior_center_realizer_exists` — coherence's
  `IsRecenteringCore.base` supplies σ.e = 1 AND the recorded lift as a center realizer
  at every INTERIOR recentering node (the coherence-derivable half of the law).

EXACTLY HOW FAR THE D-GROUP OPENS (the charged report):
- Sorry census UNCHANGED (canPolicy/canPolicy_pin stay the 2 honest sorries; D-group
  consumers of bridgePol/bridgeTm keep sorryAx at HEAD).
- But the pair returns from REFUTED (unfillable at any policy, forge-unconditional) to
  OPEN: every consumer binding `OffsetPPin pol` binds a non-refuted interface again.
- The full residue is now ONE compiled-named Prop: `RunRealizerExists p (ZMod p)`.
  Fill recipe on its discharge: `canPolicy p := canPolicyC p (ZMod p)`,
  `canPolicy_pin p := canPolicyC_pin hex`. Its open content splits:
  (a) INTERIOR SUPPORT — the (S6b′) monomial-shape clause at deg Φ > 1 frames
      (unchanged HC-1 residue: the formula, not the Stage interface, makes the
      realizer a forced-class monomial);
  (b) LAST-NODE FLANK — bare HistoryCoherent has no IsRecenteringCore record at
      i = len−1 (clause 4 needs i+1 < len); the landing law lives at
      `JetSetup.landing`/`LandingKey`, and even the CR clauses there need the (S6b)
      threshold `wPrev Φ < h` (probe's `centerRealizer_exists_of_unramified_threshold`
      displays the exact gap). NAMED OPEN FLANK: a future compiled countermodel here
      (a coherent history ENDING in a recentering node over a ramified frame — a
      2-node-gate-scale build, currently blocked by the same HK22 wall pre-HK-06)
      would re-adjudicate the quantifier to the JetSetup carrier. Recorded, not silent.
- NOTE ON ITEM 3 COUPLING: the re-keyed total rides the NAME `HistoryCoherent`, so the
  HK-06 wave's (S-a) regrade re-key of that predicate automatically re-scopes the pin;
  no PolPin edit will be needed when item 3 lands.

VERIFIED: lake build green — PolPin, R7_pinProbe, R7_ramifiedForge,
R7_polFillReduction, TreeCan (2 expected sorries), BridgeD1_treeModelWire,
BridgeD3_treeCarrier, HK22_twoNodeGate; all touched decls Lean-core.
(BridgeD5_transferRow fails at current worktree from the CONCURRENT item-7
ReadLocality `child_local` re-signature — item-7 agent's scope, pre-existing in
worktree, independent of this item; verified by error text: `1 ≤ min N N'` guard
argument mismatch at :560/:601.)
Records: MovesD/MANIFEST.json "item13_polpin_rescope_2026-07-31"; TreeCan.lean header
ITEM 13 RE-ATTEMPT RECORD; PolPin.lean header + field docstrings.

## ITEM 9 — the (r2)-on-activeLocus two-part re-scope + the VerdictDeg sibling laws (2026-07-31, agent wr-item9)

EXECUTED at the preferred option (the drafted §23 form, BridgeB15a_r2Neg.lean:2979ff),
all four sub-items.  Files touched: `LeanUrat/MovesU/BridgeRosterPins.lean` (statement
repair + proofs), `LeanUrat/MovesU/BridgeB15a_r2Neg.lean` (dated M1 note ONLY, leaf
intact), NEW `LeanUrat/MovesU/BridgeVerdictDeg.lean` (IB-B18) + NEW
`LeanUrat/MovesU/BridgeVerdictDegGate.lean` (IB-B19).

(i) TWO-PART RE-SCOPE — LANDED AND PROVED (not just restated).  The refuted sorried
universal `bridge_r2_on_activeLocus` (BridgeRosterPins.lean:314-319) is DELETED in this
commit, per the countermodel file's coexistence rule ("delete the sorried IB-B15a in
the SAME commit").  Its replacement, the §23 drafts transcribed verbatim (N-suffix
copies -> the RosterPins originals) plus the proofs the repair opens:
  * `bridgeStaticEntryList` (vocabulary) + `BridgeDiteOK` (the named per-pool gate);
  * `bridgeStaticEntryList_okat` — PROVED: every static-family member is in OKat at
    EVERY measured pool value (K/bterm via tg_ok + subring closure over the dite/ite
    sums; Jcell via jcell_ok; iota via ι_ok + closure; Wcoef via wsh_ok);
  * IB-B15a-static `bridge_r2_static_on_activeLocus` — PROVED UNCONDITIONALLY;
  * IB-B15a-dite `bridge_r2_dite_on_activeLocus` — PROVED from `BridgeDiteOK`;
  * assembly `bridge_r2_on_activeLocus_of_diteOK` — full `RegPAtR2` on the locus
    under the gate;
  * `bridgeRegPCovered_of_diteOK` — IB-B16's covered display CLOSES: (r1) by the
    landed IB-B15b (hp kept there) + (r2) by the assembly.
  Signature note: `hp : p.Prime` dropped from the re-scoped unit (header resolution 6
  added; the OKat route never consumes primality; B15b unchanged).  M1 hygiene: the
  leaf countermodel kept intact + dated end-of-file note pinning that it refutes ONLY
  the pre-item-9 form (the gate premise `BridgeDiteOK` fails at `cmC` by
  `cm_not_definedAt`); its header's import ban recorded RETIRED as of this commit.

(ii) VerdictDeg — NEW ADDITIVE SIBLING Prop (new file, `DegCons`/`UCarriers`/
`TableShape` untouched; every existing instance incl. `cmT` stays legal):
`structure VerdictDeg (T : TableShape n) : Prop`, field `vdeg_size : ∀ e ∈ Icc 1 n,
∀ τ o, ∀ μ ∈ mem, ∀ v, μ.status = Sum.inl v → (T.vdeg v : ℕ) = μ.size * (μ.δ : ℕ)`;
derived `VerdictDeg.EF_eq` = VP-1's displayed equality E·F = d through vdeg_spec.
OPEN-DISPOSITION RESOLUTION (halted δ > 1, note silent): the note read record
wf_b933dcd7-877 is NOT present in notes/ (verified by grep — it is a work-record id),
so per the assignment's silence rule the WEAKER law landed: vdeg = size·δ (implied by,
strictly weaker than, the halted⇒δ=1 package; true in both candidate worlds; reduces
to the ledger's sketch vdeg = size when δ = 1).  Guard decision (same rule): both laws
carry `e ∈ Icc 1 n`, mirroring `DegCons.size_sum` — VP-1 speaks of realized clusters.
THREADING (per ledger): compiled non-vacuity PAIR in the gate file —
`cmT_not_verdictDeg` (the recorded t₂ (1,2)-on-size-1 cheat violates it) +
`n2T_verdictDeg` (the REAL n=2 instance satisfies it); records updated in
BridgeRosterPins (IB-B16) + the r2Neg dated note; consumers adopt as NAMED hypothesis
rows (hdom-row genre), never trivial fills — no frozen structure gains a field.

(iii) delta-weighted DegCons strengthening — `structure DegConsDelta (T) : Prop`,
field `size_sum_delta : Σ (μ.size · μ.δ) ≤ e` (same guard); derived
`DegConsDelta.size_sum` PROVES it strictly refines the carried `DegCons.size_sum`
(pointwise size ≤ size·δ).  Compiled pair: `cmT_not_degConsDelta` (the reader's second
cheat 1·1 + 1·2 = 3 > 2 fires) + `n2T_degConsDelta` (real instance satisfies).

(iv) (e4) owed first-index — VERIFIED ALREADY HANDLED at the D-SC carrier layer, NOT
duplicated: `SlotsG15b_e4Seam.lean` (landed 2026-07-31, D-SC.8 fold-in) names both
candidate readings (`SiteBeta.firstIdxCandidateRebased`/`...Ambient`) under the CF13
consumption fence; nothing added by this item.

VERIFICATION: `lake env lean` green per touched/new file; full `lake build` GREEN
("Build completed successfully"); explicit module builds green; `#print axioms` on all
11 new/re-scoped theorems = Lean-core {propext, Classical.choice, Quot.sound} (no
sorryAx, no declared axioms).  Capstone path untouched (MovesU only; no OM/* file
touched, so no AxChk diff owed per rule 4; the full build's census infos printed the
capstone footprints unchanged).  Downstream consumers: none import BridgeRosterPins or
the leaf at HEAD (verified by rg); the new gate file is the first importer of the leaf,
legal as of this commit.

## Items 6 + 18 + 19 — CL-06 LSTStmt' (i-b) VARIANT A, C6 clean-threshold repair +
## countermodel landing, R6_carrierInstance DISCHARGED (executed 2026-07-31, agent: items-6-18-19)

**Item 6 (CL-06, the A17/DEFECT-1 statement repair, VARIANT A — BP5 §3.2 display (6),
Q-3 adjudication).** `HC1/R1_LSTStmt.lean` leg (i-b) reinstates EXACTLY T4/C1's
hypothesis row `(Function.support y).Finite → (∀ c, y c ≠ 0 → K.blk H c = b) →`
(hfin + hsupp, T4-parity order); execution record added to the module docstring.
R-7 kernel freeze executed in `HC1/R6_carrierInstance.lean`: private frozen
`LSTStmt_pre_A17'` (verbatim pre-repair text) added; kernel 2b
(`LSTib_offBlock_pincer`) RETYPED against the frozen copy with a dated M1-hygiene
note (it refutes the PRE-repair form only); kernel 2a unchanged (no LSTStmt'
reference). The 70-line pass-2 obstruction record relocated VERBATIM from the R6
proof body to the file header (blueprint order: do not delete). DEFECT-2 scoping
record written (R1 + R6 headers): TYPStmt'/DOMStmt'/SecB1Stmt' texts UNCHANGED —
instance-choice defect, cured by the graded-expansion pack, never by weakening R2/R3/R4.
Ripple: R2/R3/R4/R5/CL09/CL20 rebuilt green (nothing proved the pre-repair LSTStmt';
no proof breaks). `LSTStmt'` footprint: Lean-core.

**Item 19 (R6_carrierInstance non-vacuous discharge) — PROVED, Lean-core, 0 sorry.**
`#print axioms LeanUrat.HC1.R6_carrierInstance = [propext, Classical.choice,
Quot.sound]` (build log, `lake build`). Statement UNTOUCHED (still `{F : Type*}`,
same four clauses). Witness pack = the private `r6_pack T rl`: `G := gradedExpCarrier
T` (CL-08) so the Gr-pin `∀ γ, K.G.Gr γ = T.grQ γ` is `fun _ => rfl` — the
non-vacuity clause; Hist = Unit; real Coord/ht/blk/levelSet/aDim/blockEdge; lines =
rl.line with the `i > K` interiorEnd guard; window ≡ True; display-(8) slotCoeff and
monoE. UNIVERSE GLUE (the CL-09 pin, resolved statement-neutrally): `Digit :=
Shrink.{0} ↥(T.stg 0).FQ` (Finite ⇒ Countable ⇒ Small.{0}), digits read through
`Shrink.addEquiv`; CL-09's Type-pinned `packE` untouched. Leg fold-backs: (i-a)
CL-15a + the new private `r6_wE_eq` (wE least-populated-level spec) + CL-07 LAT;
(i-b, the REPAIRED leg) CL-14 through the digit equivalence (support/block rows
transported; `r6_exists_ne` converts pack-nonzero to a populated component); (i-c)
CL-15b; (ii) rfl (CL-15c definitional); (iii) CL-15d; TYP conjunct 1 CL-16 (map_add
transport); TYP conjunct 2 CL-17 (digit-range rewrite: `equivShrink`-surjectivity +
Pi.single commutation); DOM CL-18. The NCL spine (CL-10 gate → CL-27/CL-11 → CL-12 →
CL-13 → CL-14) is consumed underneath (i-b), all Lean-core at HEAD. HC1's R6 sorry
(pre-repair :145) is CLOSED.

**Item 18 (C6_alphabetCard fence transition) — repaired + partially proved; the
countermodel LANDED atomically.**
* Repair (`HC1/C6_alphabetCard.lean`): conjunct 2 gains the NAMED hypothesis
  `Tower.cleanThreshold b γ := ∀ s : T.Addr b, T.aligned γ s → T.attainable γ s`
  (new def, review-flagged; CL-04 display-(3) vocabulary now statement-consumed).
  WEAKEST-form warrant: per the CL-04 probe record fullness is believed EQUIVALENT
  to this condition (CI-1..CI-4), so no strictly weaker non-trivial hypothesis
  restores the iff; the D.9(b) clean-threshold regime is the displayed sufficient
  instance (hence the ledger's "independence/clean-threshold" name — independence
  is CI-3 THEOREM content, not hypothesis). Conjuncts 1/3 stay unguarded.
* Proof status: conjunct 1 PROVED (`C6_conjunct1_closable`/T7); conjunct 2 →
  PROVED (`C6_conjunct2_rhs_always`); conjunct 3 PROVED (`C6_conjunct3_hyp_false`,
  ex falso). Conjunct 2 ⟸ (cleanThreshold → fullness) = the ONE remaining honest
  sorry — exactly CL-05's specified obligation (CI-1 equidistribution, CI-2 line
  card, CI-3 slot-min orthogonality, CI-4 card bridge; named in-file). The
  "clean-threshold instance discharges it" branch did NOT fire: no corpus lemma
  supplies the counting identity at HEAD. `#print axioms C6_alphabetCard =
  [propext, sorryAx, Classical.choice, Quot.sound]` (census count for the file
  unchanged at 1, now on a believed-TRUE statement).
* Countermodel landing (BP5 §3.1 LANDING GATE, atomic with the repair): CL-01a/b/c
  landed from side branch de42a7e (Tshallow + six certificates PROVED, Lean-core;
  re-verified green at HEAD by lake build). `CL01c_shallowTower.lean` gained the
  frozen `C6_stmt_pre_repair` def (verbatim pre-repair conclusion) + the compiled
  negations `C6_pre_repair_refuted_at_Tshallow` and `C6_pre_repair_theorem_refuted`
  (∀-form at the gate ambient) — both Lean-core. M1 no-coexistence satisfied: the
  negation targets ONLY the frozen copy; the pre-repair sorried universal no longer
  exists in the live tree.
* CL-04 probe slot: file UNCHANGED except a dated note (rule-3 hygiene) — the
  banked `CL04_dichotomy_probe` sorry targets display (4)'s ⟸ leg (believed FALSE
  existential), not either C6 form; disposition pends CL-05.

**Verification.** Per-target `lake build` green for every touched module
(R1, R2/R3/R4/R5 cone via R6, R6, CL09, CL20, C6, CL01a/b/c, CL04); full
`lake build` green (8579 jobs). Footprints (build-log `#print axioms`):
`LSTStmt'`, `R6_carrierInstance`, `C6_cardK_bridge`, `Tshallow_levelSet_nonempty`,
`Tshallow_alphabet_deficient`, `C6_pre_repair_refuted_at_Tshallow`,
`C6_pre_repair_theorem_refuted` all `[propext, Classical.choice, Quot.sound]`;
`C6_alphabetCard` adds `sorryAx` (the one honest CL-05 leg). Capstone path
untouched (no OM/* file; grep: no `import LeanUrat.HC1` in OM/, AxChk_baseline,
MontesV2, Goal — no AxChk diff owed per rule 4).

**HC1 census delta.** Proof sorries: R6:145 CLOSED; C6:63 remains 1 (relocated to
the ⟸ leg of the REPAIRED statement, believed true, CL-05-spec'd); CL01a/b/c
E-phase skeleton sorries (7 tokens incl. the 2 def-slot sorries) CLOSED by the
branch landing; CL04:177 banked probe slot unchanged. Net: HC1 real-sorry census
2 → 2 (C6 leg + CL04 probe slot), with R6 closed and the CL01 portfolio proved.

## ITEMS 4 + 10 EXECUTED (agent wr-item4-10, 2026-07-31)

AUTHORIZATION quoted: Asvin, 2026-07-31, verbatim: "Sign-off granted on all 21 items
as preferred, execute the queue."

### Item 4 — W17ii field repair (MovesS RS4Chain): EXECUTED, clause (ii) PROVED

Preferred option executed: the TV-H2/ESCALATION E-1 menu (b′) of
BRIDGE_BP3_TV_2026-07-30.md §3.G REV 2 — the Q4-preferred summability guard (in the
finiteness form the squeeze needs) PLUS the (a′) census fields, incl. the E-1
`shevt_disj` ratified in the same grant.  Evidence trigger: the TV-H1b COMPILED
countermodel (quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt — infinite shDom,
shWeightH ≡ 1, all pre-repair chain laws satisfied; clause (ii)'s HasSum false at
every value), so `w17ii_wave4` clause (ii) was FALSE AS STATED.

Executed changes:
1. `MovesS/Interfaces.lean` — RS4Chain gains FIVE fields (statement change,
   authorized):
   - `shdom_fin : ∀ Ŝ ∈ F.Sh, (shDom Ŝ).Finite` (the guard; a bare Summable is
     recorded DEAD per REV 2 finding 1 — it proves ∃-sum, not the WshVal tie);
   - `shdom_no_stray` (h ∈ shDom → shEvtH eventually nonempty, per pool);
   - `vis_sub_shdom` (visH ⊆ shDom eventually);
   - `shevt_off_vis` (h ∈ shDom \ visH at level N → shEvtH = ∅, eventually);
   - `shevt_disj` (E-1: pairwise disjointness of shEvtH across h ∈ visH — the
     card-additivity law the chain carried NOWHERE).
   `W17ii` itself and the projection-def `RS4Chain.wsh17_pin` are BYTE-UNTOUCHED,
   so U-28's premise `h17 : C.wsh17_pin` is byte-identical (checked: Rs4.lean
   `rs4_rational_step` recompiles unchanged).
2. `MovesV/V7_w17ii.lean` — clause (ii) PROVED by the counting squeeze (TV-H3):
   at a fixed pool and one uniform level N ≥ all census thresholds,
   WshVal·|Box| = |shEvt| (wshval_card) = Σ_{h∈visH}|shEvtH| (shevt_grouping +
   shevt_disj via Finset.card_biUnion) = Σ_{h∈shDom}|shEvtH| (vis_sub_shdom +
   shevt_off_vis via Finset.sum_subset) = (Σ_{h∈shDom} shWeightH)·|Box|
   (shweight_card); |Box| ≠ 0 (boxpos + Fintype.card_pos) cancels; shdom_fin +
   hasSum_sum_of_ne_finset_zero/hasSum_subtype_iff_indicator turn the finite sum
   into the HasSum.  THE ONE BANKED SORRY (C14) IS RETIRED.
   `#print axioms`: w17ii_wave4, w17ii_pin BOTH [propext, Classical.choice,
   Quot.sound] — Lean-core, zero sorryAx.
3. Instance re-discharges (TV-H4 "must survive the guard" gate):
   `MovesS/N2Sigmas.lean` n2ChainCore + `MovesU/BridgeB15a_r2Neg.lean` cmChain —
   both carry the device carriers (shDom = {0}, visH = {0}, shEvtH = univ):
   shdom_fin = finite singleton; shdom_no_stray = full box nonempty (boxpos);
   vis_sub_shdom = singleton-to-singleton; shevt_off_vis/shevt_disj vacuous at
   the singleton visH.  Both files GREEN.
4. TV-H1b disposition (M1 hygiene): the blueprint's "re-land the fill in the
   repair commit" is IMPOSSIBLE as written — the fill does not typecheck against
   the repaired structure (negChain pins shDom = univ, excluded by shdom_fin),
   and `w17ii_false` is now REFUTED for every chain, so its five skeleton sorries
   were unfillable-false and are DELETED (the honesty invariant; recorded
   deviation-with-reason).  `MovesV/TV_H1b.lean` converted to the dated
   retirement record + a compiled CURE SEAL (`negCarrier_shdom_finite`: at the
   countermodel's own carriers, every repaired chain has finite shDom).  The
   quarantine archive got the rule-3 dated note stating exactly which form it
   refutes (the pre-2026-07-31 census-free RS4Chain); TV_H1a.lean header got the
   outcome note (carriers stay — they host the seal).
5. Records: MovesV/MANIFEST.json banked_sorry entry RETIRED (sorried census
   4 → 3: ledgerIV_inst, ratBurdens_exists, scs_data_supply remain); V7-8 unit
   entry updated; Interfaces.lean RS4Chain + wsh17_pin docstrings updated.

### Item 10 — cl6 pgZero.countS := 0 (MovesS/N2PolyGeom.lean): EXECUTED, probe now POSITIVE

Executed the val-preserving repair exactly as recorded in the probe header:
`pgZero` redefined as a structure literal with `countS := 0` (was pgDiv-pinned 1);
`pgZero.val = 0` either way (`pgZero_val` compiled), degree pins kept
(degBoundS = 0, natDegree 0 = 0).  In-file proof ripple: `n2tgP_ok` closes the
padding branch via `pgZero_val_mem`; `n2tgP_interp`'s padding branches via the
new `evalAt_pgZero`; degree-pin lemmas unchanged (rfl at the literal).
NEW public companions (the privates are file-local): `n2_tcount_val` (countT ≡ 1
evaluates to the ℕ-count 1 at every (e,τ,o,q₀)) and `n2_scount_val` (countS
evaluates to the cell-fiber census at EVERY roster row — 1 at the real rows,
0 at the e ≠ 2 padding rows).

Probe re-run (`MovesU/SynK2_cl6N2.lean`): CONFIRMED — the repaired pack SATISFIES
the count laws.  `n2_countLaws_block2` (the block-2 genre) recompiles UNCHANGED
and green; the pre-repair `n2_polyGeomLaws_isEmpty` is not restatable at HEAD
(the pack definition changed — the compiled IsEmpty artifact lives in git
history, dated M1-hygiene note in the file header states it refuted the
pgZero.countS = 1 form only); the leaf is EXTENDED with the positive lemma
(cheap, done): `n2_polyGeomLaws_nonempty : Nonempty (PolyGeomLaws n2T n2M n2RB)`
with tCount ≡ 1 — the BridgeKernels.cl6 row's "moves out" instance evidence
(row docstring updated; the generic row itself KEPT per the SYN2-K1 precedent).
No sorries in the leaf; Lean-core.

### Verification
Per-file `lake env lean` green on every touched file (N2PolyGeom, SynK2_cl6N2,
Interfaces, N2Sigmas, BridgeB15a_r2Neg, V7_w17ii, TV_H1a, TV_H1b).  Root-graph
`lake build` green (8579 jobs; capstone census infos unchanged, Lean-core).
Full 1047-module sweep build launched for the whole Moves* cone (the root-graph
gotcha); result recorded below.
Capstone path: NO OM/* file touched; AxChk_baseline run after the sweep — see below.
