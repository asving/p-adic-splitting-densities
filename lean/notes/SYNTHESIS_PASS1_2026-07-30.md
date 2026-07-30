# WHOLE-PROOF SYNTHESIS — PASS 1 (2026-07-30)

CHARGE (standing duty, AUTHORITY UPDATE in BRIDGE_ADJUDICATIONS_2026-07-30): read the
corpus map + the five revised blueprints + PROJECT_STATE, hunt unifying ideas that
collapse multiple units/corpora into one mechanism, propose consolidations with exact
statement-level plans; orchestrator adjudicates.

INPUTS READ: PROJECT_STATE.md (updates 2026-07-30a/b/c + the two corrected 07-29
records); BRIDGE_BP1..BP5 (REVISION 2, all five, full); BRIDGE_ADJUDICATIONS;
docs/public/graph_build/maps.json (16 corpora / 315 cards); GOLF_CAMPAIGN Class-D
duplication census; spot-reads: Moves/L3_K1 + the L5_land* family, HC1/V3_readLift +
V4_readLanding, HC2/SharedRecenter + U7/U9, OM/QpType.lean, MovesT/Defs (ramIdx),
MovesS (RatfuncEvalInfinite, PowEntry*, Neumann), the LANDED E-phase skeletons
(MovesU/Bridge*.lean incl. BridgeD5_transferRow + BridgeSolve; MovesT/TV_B2 + TV_B7;
Kernels/*). Note: E-phase writers are running concurrently — several statements cited
below are already on disk as sorried skeletons, which makes the consolidation windows
time-sensitive (flagged per candidate).

════════════════════════════════════════════════════════════════════════════════
## PART 1 — RANKED UNIFICATION CANDIDATES

### C1 (TOP). The (w,R) residual-valuation engine: one shared module for the
### ~15-helper no-cancellation kernel now copied in ≥ 9 files and about to be
### copied 3 more times

**The duplicated mechanism.** From the bare `Stage` laws (`Moves/Defs.lean:106` —
`hwmul`, `hwult`, `hRmul`, `hRadd`, `hRlt`) every file that touches a landing/vertex
computation re-derives, as `private` lemmas: the weight arithmetic (`w_one`,
`w_neg_one`, `w_neg`, `w_pow`), the residual arithmetic (`R_one`, `R_neg_one_sq`,
`R_neg`, `R_pow`), the ultrametric sum bound (`w_sum_ge`), the distinct-position
no-cancellation machine (`residual_sum_machine` / `minsum_facts` / `key_no_cancel` /
`decomp_machine`: nonzero terms of one common weight with monomial residuals at
pairwise-distinct ψ-adic positions sum without cancellation), and the pure-Laurent
ψ-order toolkit (`dvd_of_dvd_mul_T`, `dvd_of_dvd_T_mul`, `psi_not_dvd_X_pow`,
`toLaurent_pow_dvd_transfer`, `psi_order_of_sum`, `pow_order_unique`, `ordAt_*`).

**Evidence (verified by grep + file reads this pass; golf Class-D concordance):**
- `Moves/L3_K1.lean` — the original, all private (563 ln).
- `Moves/L5_landBox.lean` (~17 privates), `L5_landVertex.lean` (~19),
  `L5_landVertexDigit.lean` (~19), `L5_landTwoSided_repair.lean` (~22) — golf Moves#7
  records the landVertex↔landVertexDigit pair as "copied near-verbatim (edits must be
  mirrored)" — a STANDING DRIFT RISK, not just bloat.
- `Moves/L3_liftWeight.lean` = verbatim dup of L3_K1's private `w_Phat` (Moves#4);
  `L4_TRANSi_R3` vs `L4_TRANSiii_R3` helper dups (Moves#5).
- `HC1/V3_readLift.lean` + `HC1/V4_readLanding.lean` — the SAME engine re-derived at
  the READ FRAME carrier (`v3_wv_*`, `v3_rv_*`, `v3_key_no_cancel`,
  `v3_minsum_facts`; V4:45–832 is a documented verbatim copy of V3's file-private
  kernel — golf HC1#99); micro-copies across V7/V8/V9 (HC1#100), hits in
  V10/V11/S10.
- `HC2/SharedRecenter.lean` — the PUBLIC partial home already exists (w_one …
  w_sum_ge, `decomp_machine`, hoisted 2026-07-30 for U20c/U22E1; net −449 ln), but
  only those two consumers use it, and it is keyed to `Stage` only.
- Quarantine-bound copies (BP5 §2.4): `L5_landTwoSided_R5`, `L5_landVertexDigit_repair`.

**About to be copied again (the forward leverage):** BP2 HK-02 (`V11_minimalCore`)
says "V10 helper patterns copy"; HK-52 + HK-11a redo "V10_forcedKeyWeight's 2-slot
computation pattern at σV" — the σV regrade is a THIRD carrier instance of the same
(w,R) pack (its laws are exactly what `RegradeOf` records). And BP4 KB5 (the one
"genuinely delicate stage lemma" of the D4R0K cluster) is the SAME mechanism at the
enum model: "pairwise-distinct Φ-adic positions all in one class mod e; addition
never mixes positions; min attained, no cancellation".

**Proposed unifying statement.** A new additive module pair:
- `Moves/LaurentOrd.lean` — the (w,R)-free Laurent ψ-order toolkit, verbatim hoist.
- `Moves/ResVal.lean` — structure `ResValPack (K) := (w : Polynomial ℤ_[p] → ℤ,
  R : Polynomial ℤ_[p] → LaurentPolynomial K, hwmul, hwult, hRmul, hRadd, hRlt)`
  (exact law list fixed by the Phase-0 concordance below; codomain of `w`
  parameterized over a `LinearOrderedAddCommGroup` only if the drift audit finds a
  ℚ-valued copy), with the ~9 arithmetic lemmas + `w_sum_ge` + the distinct-position
  machine in its Finset-indexed form derived ONCE.
- Instances: `Stage.pack σ` (fields := σ.w/σ.R + its laws — definitional),
  `ReadFrame.pack V` (laws = HC1 V1/V2's PROVED read-frame laws), and post-HK-06 the
  σV instance (laws from the `RegradeOf` record).

**What it deletes/collapses.** ~2,000–2,500 net lines of private proof text across 9
live files; golf items Moves#4/#5/#7, HC1#99/#100 retired with their drift-risk
records; BP2 units HK-02/HK-52/HK-11a get their supply from the σV instance instead
of a 10th/11th/12th copy (their hard content — the per-slot window recursion — stays,
but the ~200-line scaffold under it disappears); BP4 KB5's noninterference input is
consumed from the shared machine (KB5a's "min ≥ W" leg) through a small seam.

**Migration cost.** ZERO statement-fence events: every copy is `private` (BP2 §3.2
confirms private = freely restatable) and all public mains stay byte-identical. New
files are additive. Protocol per the SharedRecenter Phase-4 lesson (a non-verbatim
"hoist" was caught by Codex after a fresh-Claude pass missed it): verbatim-hoist
first, parameterize second, Codex per-conjunct equivalence pass on each migrated
file, AxChk census after each. SEQUENCING: run AFTER BP5's Moves-cluster quarantine
(removes 2–3 copies from the surface for free).

**Verdict: FEASIBLE-NOW.** Execution plan at unit granularity in PART 2.

---

### C2. One level-locality owner row instead of three: TransferRow (BP1) ≡
### StableInputs (BP3) ≡ the treeN_stable discharge inputs — all HC-2/D4R0K

**The duplicated mechanism.** The SAME open mathematics — "the tree model's reads at
working level N′ depend only on the first n·N box digits once the tree's threshold
is ≤ N" (the note's Thm 2.1 / D4R.4 / TB-CAP face, owner HC-2/D4R0K) — is being
typed as THREE separate named premise surfaces this campaign:
1. `MovesT.treeN_stable` (E11_treeN.lean:99, the fenced sorry; `TreeNStableStmt`
   rides `RS1GivenPackage.tree_n`).
2. BP3 TV-B2's `StableInputs` — LANDED at `MovesT/TV_B2.lean:86`: `chart_pin` +
   `child_cyl` (fixed-level agreement-below-n·N transfer of `(Tat N').child`);
   ratified as treeN_stable's named hypothesis (Q2 option 2, TV-B7).
3. BP1 IB-D5's `TransferRow` — LANDED at `MovesU/BridgeD5_transferRow.lean`:
   `realizes_transfer` + `fiber_transfer` (cross-level N→N′ transfer of
   `Realizes`/`fiberAt` at the same `bridgeTm` models), entering `BridgeKernels` as
   the `transfer` row, consumed by IB-D8/D15/D16/D17. Its own docstring names
   treeN_stable as "its fenced SIBLING — cited, NOT consumed".

Both (2) and (3) are statement-only, PRE-RATIFICATION rows over the same model family
(`bridgeTm` = SP8's CanTreeModel wired by IB-D1; `Tat` in TV-B2 is the same
`TreeModel` carrier). If both land as independent rows, theoremU's final honesty
surface carries the one open kernel under two names, and the eventual HC-2/D4R0K
discharge has to be done twice (or a third bridge row appears).

**Proposed unifying statement.** ONE owner row, `ReadLocality n p` (home: MovesT
Defs vicinity or a shared BridgeT file), fields:
  (i) `chart_pin` (as TV-B2);
  (ii) `child_local` — the CROSS-LEVEL locality law: for N ≤ N′, thresholds in
       range, `(Tat N h).child o ν x ↔ (Tat N' h').child o ν x'` whenever x′ extends
       x's first n·N digits (equivalently: child at N′ reads only digits < n·N);
  (iii) the NsHalts face if TV-B2's typing pass finds it non-derived.
Derivations (new small lemmas, not rows): `StableInputs` follows by taking two
extensions of one truncation (two applications of (ii) at N′ = N′); `TransferRow`'s
two fields follow because `Realizes`/`fiberAt` are mem/child/redPoly-composed (BP3's
TV-B3–B6 already prove exactly this composition at fixed level; the cross-level leg
adds IB-A12's boxProj compat, already a unit).

**What it collapses.** BridgeKernels.transfer's row and treeN_stable's StableInputs
hypothesis become the SAME named object; TV-A6's boundary record and IB-F2's honesty
ledger name ONE kernel; the future HC-2/D4R0K discharge (or the SP8-constructive
proof — see the upside note in PART 3/N3: for the CANONICAL policy the locality law
may be PROVABLE from the CanTreeModel construction rather than hypothesized, which
would discharge all three faces at once) is done once.

**Migration cost.** One statement-fence event — but BOTH landed rows are already
flagged-for-ratification ADJ units; ratifying the unified row instead is the same
adjudication. Two derivation units (routine, ~30 ln each) replace nothing but bind
the rows. The window is NOW: once D-group and B-cluster provers start consuming the
two rows separately, the merge price grows to a re-key wave.

**Verdict: FEASIBLE-NOW (time-sensitive; do at the pending ratification).**

---

### C3. One (e,f) convention: BP1 Group E (ZpBridge) must adopt / reconcile with
### OM's QpFactorization + LocalFactorData — which already solve, and already
### DOCUMENT THE WALL IN, exactly this problem

**The duplicated mechanism.** Reading a genuine ℤ_p[X] factorization with local
invariants (e_i, f_i) exists TWICE, with a third treatment now being blueprinted:
- `MovesT.ramIdx/resDeg` (Defs.lean:1107/1116): junk-dispatch through
  `IsLocalRing (AdjoinRoot g)` — reads the ORDER's invariants. BP1's IB-E0
  countermodel (h = X² − p²c: order-level (1,1) vs true (1,2)) shows this is WRONG
  as the ZpBridge's (e,f); Q2 queues the repair.
- `OM/QpType.lean:473` `QpFactorization p f` (factors, prod_eq, monic, ℚ_p-irred,
  per-factor `LocalFactorData`) + `LocalFactorData` (:68): the local field L,
  finrank = deg g, and O = THE INTEGRAL CLOSURE of ℤ_p in L as a DVR, with
  `eOf/fOf/efOf` (:97–115) = mathlib's genuine `Ideal.ramificationIdx/inertiaDeg` at
  O's maximal ideal — i.e. EXACTLY the repair target Q2 describes ("re-point at the
  integral closure / valuation ring"). OM also has the proved patterns Group E
  needs: `isUnit_add_of_mem_maximalIdeal` (QpTypeEisenstein:60), Eisenstein ⇒
  totally ramified (map card `eisenstein-anchor`), the ef-swap refutation, and
  worked (e,f) computations at concrete factors (QpTypeSplitU/ChainLeaves/Mixed).
- BP1 Group E (IB-E1…E12) as blueprinted: builds `monicFactors` from UFD factors,
  proves IP-1 (`IsLocalRing (AdjoinRoot h)`), and proves (†11g) e·f = deg "via
  `Ideal.sum_ramification_inertia` at the field's valuation ring".

**The plan-level collision (highest-value single finding of this pass).**
`OM/QpType.lean:63–67` RECORDS: "Mathlib at the pin cannot PROVE this bundle
inhabited for wild g of degree ≥ 2 (no DVR-ness of `integralClosure ℤ_[p] L`); the
Wave-2b axiom carries exactly that existence content." IB-E6's (†11g) route needs
precisely that missing content (Dedekind/DVR-ness of the integral closure to apply
sum_ramification_inertia). So as blueprinted, E6 is likely to stall at the SAME wall
OM already hit and documented — and the fleet would discover it the expensive way.
BP1's §2.4 inventory does NOT list QpType/LocalFactorData at all (an inventory gap).

**Proposed unification.** (a) The Q2 repair adjudication is decided WITH OM's
convention on the table: either re-point `ramIdx/resDeg` to a LocalFactorData-shaped
read, or — cleaner — have `ZpBridge.zfType` consume a `QpFactorization`-certificate
multiset via `efOf`, making MovesT's defs consumers-only. (b) Group E's real content
is re-scoped to "produce the certificate for every monic g" with the wild-existence
leg either (i) discharged by whatever new Mathlib/hand proof of
integral-closure-DVR-ness lands (one shared unit, benefiting BOTH corpora), or
(ii) carried as ONE named row / the already-declared cited axiom — never two
parallel treatments. (c) IB-E0/E12 stay (they gate the repair either way).

**What it collapses.** IB-E5/E6/E7's from-scratch local theory (the ~110 planned
hard-fable lines at the riskiest spot) becomes instantiation of OM's bundle; the
ef-vocabulary seam between theoremU's ℤ_p clause and OM's faithfulness gates
(`full-faithfulness`, `qp-factorization-certificate` cards) becomes definitional —
which the eventual "one proof, one story" write-up needs anyway.

**Migration cost.** Q2 is already a statement-change adjudication on RATIFIED files;
this only changes WHAT the repair points at. One new OM→MovesU import edge on the
bridge path (BP1 currently keeps OM off the mkUInstance path by design — Q1
architecture B; the import would be QpType ONLY, not the classifier; if the
orchestrator wants the path kept clean, the alternative is lifting
LocalFactorData/efOf verbatim into a shared `LeanUrat/LocalEF.lean` consumed by both).

**Verdict: FEASIBLE-NOW as the Q2 adjudication input (BLOCKING: should land before
Group E provers run); the full certificate-consumption merge FEASIBLE-AFTER-GATES
(IB-E0/E12 outcomes).**

---

### C4. Complete the SharedRecenter family: two more byte-identical helper blocks
### whose hoists have direct forward leverage on BP2's queued provers

**(a) HC2 "SharedZC".** Golf HC2#106: `clause_assign`, `card_fin_fun'`,
`valueClause_codim`, `mkFresh_codim` are verbatim private dups across U7_sigmaRec
(11 hits) and U9_zcRoot (11 hits), with `card_fin_fun` also copied in U4/U5/U6
(grep-verified this pass: 5 files). BP2 Block Z (HK-32…HK-39) proves U10 "one level
up" from U9 — §3.5 says explicitly "U9 is the template". Without a hoist, Block Z
mints copy #3 of the whole kernel. Proposal: `HC2/SharedZC.lean`, verbatim hoist
(the SharedRecenter protocol), BEFORE Block Z's post-wave provers start.
**(b) HC1 S9 shared builder.** Golf HC1#96: S9a/S9b/S9c carry a ~180-line
near-verbatim shared construction ×3 (Bézout split → hwult tower → Stage literal).
BP2 HK-15/HK-16 and BP3 TV-D6 instantiate exactly this chain at the F4 gate.
Proposal: one private→shared `S9_builder` def + laws; S9a/b/c mains byte-identical.
(The related HC1#91 — `ChildResData.ChildResLaws` ≈ `DefsV.ReadResLaws`, parallel
7-conjunct packs differing only in the key — is a STATEMENT change on ratified
files; defer unless C1's pack abstraction makes it free.)

**Deletes:** ~500–700 lines; removes the "template drift" failure mode from Block Z
and the gate builds. **Cost:** zero fence events (privates). **Verdict:
FEASIBLE-NOW; (a) should precede BP2 Block Z, (b) should precede HK-15/16 re-runs.**

---

### C5. BP4's abstract matrix layer must EXTEND the MovesS matrix layer, not
### shadow it

MovesS already owns, PROVED: `EscapeE0` + `e0_det_ne_zero` (E0DetNeZero),
`(I−A)⁻¹ ≥ 0` (E0InvNonneg), `NeumannPartial`, `PowEntryNonneg`,
`PowEntryTendsto` (pow entries → 0 FROM EscapeE0 — the converse direction of KA1),
`MulVecAbsBound`. BP4's KA1/KA2a plan "mulVec monotone toolkit" and entrywise
bounds in a NEW `Kernels/E0Matrix.lean`. Since KA1's conclusion is literally
`MovesS.EscapeE0`, the file imports MovesS.Defs anyway — the only risk is the fleet
re-proving the toolkit. Proposal: KA-unit prompts carry a mandatory
"grep MovesS/{PowEntry*,MulVecAbsBound,NeumannPartial} first" clause; KA9 is
already verify-only glue. Also note KA1+KA5 (row-sum < 1 ⟹ escape) is the shared
substochasticity core that BP4's own ROUTE 2 (`BlockDrain`) and the exhaustion
side (env_tendsto / MovesX envelope) both factor through — keep it stated in the
abstract ℚ-matrix form so all three consume it. **Deletes:** ~60–100 planned lines
+ review surface. **Cost:** none (prompt-level). **Verdict: FEASIBLE-NOW (cheap).**

---

### C6. IB-C3b (and C2's eval glue) are corollaries of PROVED MovesS rigidity
### lemmas — reclassify from hard-fable archaeology to routine

`MovesU/BridgeSolve.lean`'s sorried `eq_zero_of_evalAt_primes_zero` (IB-C3b) is a
~10-line corollary of the PROVED `MovesS.ratfunc_eval_infinite`
(RatfuncEvalInfinite.lean:16: infinite vanishing set + nonvanishing denominators ⟹
f = 0) + `Nat.infinite_setOf_prime` + cast injectivity + IB-C3a's OKat→num/denom
translation (the denominators' nonvanishing is exactly OKat membership). BP1's C3b
sketch re-derives the same proof from scratch. Similarly `interp_unique` and
`AllActiveCofinite` cover parts of IB-C2/C4's cast chains. **Deletes:** IB-C3b's
planned fresh derivation; shrinks C-group risk. **Cost:** none. **Verdict:
FEASIBLE-NOW (prover-prompt pointer; no adjudication).**

---

### C7. The finite-state transfer triple — MovesS `Kmat`/`kstep` (symbolic solve),
### MovesV counting laws (measure), MovesT site pricing (tree) — one Markov
### abstraction. SPECULATIVE; do not schedule

The three corpora state near-parallel one-step/composition laws (MovesS
`Kmat`/`bTerm`/`consumedDeltas`; MeasuredSide `kstep` with kstep_one/hmc — BP3
TV-E2 now transcribes the three-case recursion; MovesT `SibCountAt`/`JCmultiAt`
per-site pricing; HMC is exactly the factorization face of the same structure, and
`n2_hmc` its 1×1 instance). A single "finite transfer system" abstraction would
state Chapman–Kolmogorov/power/factorization laws once. BUT: the BP3 E/F/G seam
units already ARE the honest dictionary (measuredOf's laws are rfl-genre BY
CO-DESIGN), the carriers differ genuinely (ℚ(q) symbols vs ℝ masses vs ℕ counts),
and a retro-abstraction would touch ratified interfaces (statement fence) for
mostly aesthetic gain. Revisit only if a SECOND full seam of this genre appears.
**Verdict: SPECULATIVE — record, don't schedule.**

---

### C8. The carry algebra D = F[u]/(u^e − z̄) as the e ≥ 2 unifier of HC1 D-units,
### Moves L2/L4 transport, and BP2's RG-1 residual-law gap. BLOCKED ON MATHEMATICS

HC1 D1–D8 build `CarryAlg F e` with digit multiplicativity and
`D4_carryAdjoinRoot : CarryAlg ≅ F[u]/(u^e − z̄)`; Moves L2/L4 transport lemmas do
the same digit bookkeeping at e = 1 in Stage clothing; BP2's compiled-e≥2-branch
problem (RG-1/RG-2/RG-3, §3.1(c)) exists precisely because the e ≥ 2 residual laws
have no accepted note-side source (§B2-FINAL rejected at pass 8, 5 crit/2 gap).
The carry algebra IS the designated unifier — but recording its laws as coherence
clauses before B2-FINAL is accepted was rightly rejected as an axiom-smell (RG-3).
**Verdict: SPECULATIVE / blocked on the B2-FINAL rewrite; when that lands, the
Lean-side landing spot is already built (HC1 D-units + G2/G3/G4 gates) — note this
in the B2-FINAL charge so the note is written TO the carry-algebra vocabulary.**

════════════════════════════════════════════════════════════════════════════════
## PART 2 — EXECUTION PLAN FOR C1 (the residual engine), unit granularity

Ids SYN-E*. Disciplines: verbatim-hoist-then-parameterize; mains byte-identical;
Codex per-conjunct equivalence pass per migrated file (the SharedRecenter Phase-4
lesson); full `lake build` + AxChk census after every migration unit; no new
public name may shadow an existing one (the R2/MovesGr lesson).

GATE
- **SYN-E0** (routine, report-only): the CONCORDANCE TABLE. Diff all copies
  lemma-by-lemma: L3_K1 vs L5_landBox/landVertex/landVertexDigit/landTwoSided_repair
  vs L4_TRANSi/iii vs HC1 V3/V4 (ReadFrame) vs HC2 SharedRecenter vs V7/V8/V9
  micro-copies. Output: identical / α-renamed / genuinely-diverged classification,
  the exact law set each derivation consumes (hwmul/hwult/hRmul/hRadd/hRlt/...),
  and the w-codomain census (ℤ everywhere?). DIVERGED entries get their own row —
  they are the drift the golf ledger warned about; any SEMANTIC divergence found is
  a stop-and-report (possible latent bug, not a merge).
- **SYN-E0b** (sequencing, no work): confirm BP5's Moves-cluster quarantine (CL
  units for L5_landTwoSided_R5, L5_landVertexDigit_repair, L5_landTransport_R3,
  L4_TRANSviii_b_R3) lands FIRST; those copies are then out of scope.

BUILD (additive, no fence)
- **SYN-E1** `Moves/LaurentOrd.lean` (routine, ~150 ln): verbatim hoist of the
  (w,R)-free Laurent lemmas: dvd_of_dvd_mul_T, dvd_of_dvd_T_mul,
  psi_not_dvd_X_pow, toLaurent_pow_dvd_transfer, psi_order_of_sum,
  pow_order_unique, ordAt_unique/unit_mul/add, poly_dvd_of_laurent_dvd, GRf-face.
  Source of truth per lemma fixed by SYN-E0.
- **SYN-E2** `Moves/ResVal.lean` part 1 (routine, ~120 ln): `ResValPack` structure
  (fields per SYN-E0's law census) + the arithmetic nine (w_one … R_pow, w_sum_ge),
  proofs lifted from SharedRecenter (already derived from bare laws there).
- **SYN-E3** `Moves/ResVal.lean` part 2 (hard-fable, ~120 ln): the distinct-position
  no-cancellation machine in Finset-indexed form (generalizing
  SharedRecenter.decomp_machine / L3_K1.minsum_facts): family (i : S) of nonzero
  terms, common weight m, residuals = units at pairwise-distinct positions ⟹ sum
  nonzero, weight exactly m, residual = the position-sum. Pre-approved split
  E3a (min ≥ m) / E3b (read-off).
- **SYN-E4** instances (routine, ~50 ln): `Stage.pack` (rfl-fields) +
  `ReadFrame.pack` (from HC1 V1/V2's proved laws) + non-vacuity examples.

MIGRATE (one unit per file; each: delete privates, import + `open`, mains
byte-identical, Codex equivalence, AxChk)
- **SYN-M1** Moves/L5_landBox (routine) · **SYN-M2** L5_landVertex (routine) ·
  **SYN-M3** L5_landVertexDigit (routine) · **SYN-M4** L5_landTwoSided_repair
  (routine-plus — the largest copy, 22 privates) · **SYN-M5** L3_K1 +
  L3_liftWeight (retire the w_Phat dup; keep L3_K1's public statement byte-identical)
  · **SYN-M6** L4_TRANSi_R3/L4_TRANSiii_R3 (routine, small) ·
  **SYN-M7** HC1 V3_readLift + V4_readLanding at `ReadFrame.pack` (hard-fable —
  the ~800-line V4 copy dies; the V3/V4 mains and their public kernel statements
  unchanged) · **SYN-M8** HC1 V7/V8/V9/V10/V11/S10 micro-copies (routine sweep) ·
  **SYN-M9** HC2/SharedRecenter re-based on ResValPack, public names kept as
  re-exports (U20c/U22E1 untouched).

FORWARD WIRING (the payoff beyond deletion)
- **SYN-F1** (post-HK-06, coordinates with BP2): the σV instance —
  `RegradeOf.pack : ResValPack` from the recorded regrade laws; hand to BP2 so
  HK-02/HK-52/HK-11a consume SYN-E2/E3 instead of copying V10 patterns. BP2 prompt
  amendment, not a BP2 unit change.
- **SYN-F2** (coordinates with BP4 KB5): the enum-model seam — state KB5's
  noninterference input as an instance of SYN-E3's Finset form (positions =
  Φ-adic slots j₀+ek, weights = wt); KB5a consumes it. BP4 prompt amendment.

ACCEPTANCE: net ≈ −2,000 lines; sorry census unchanged; every capstone footprint
byte-identical; golf drift-risk records Moves#7/HC1#99 closed with pointers here.
Estimated effort: ~15 units, 11 routine / 3 hard / 1 report — comparable to one
mid-sized BP cluster, paid back inside the same campaign by HK-52/HK-11a/KB5.

════════════════════════════════════════════════════════════════════════════════
## PART 3 — NON-UNIFICATION FINDINGS (inconsistencies, upsides, sequencing)

- **N1 (blueprint inventory gap, feeds C3 — BLOCKING for Group E).** BP1 §2.4's OM
  inventory lists menu decoders + UniformModelN2 but omits `OM/QpType.lean`
  entirely (`QpFactorization`, `LocalFactorData`, `eOf/fOf/efOf`, the Eisenstein
  anchor, and the RECORDED wall: integralClosure-DVR-ness unprovable at the pin,
  Wave-2b axiom carries the existence). IB-E6's sum_ramification_inertia plan runs
  straight at that wall. Surface to the Q2 adjudication before E-group provers.
- **N2 (double-typed kernel row, feeds C2 — time-sensitive).** `TransferRow`
  (MovesU/BridgeD5_transferRow.lean) and `StableInputs` (MovesT/TV_B2.lean) are BOTH
  on disk as statement-only, pre-ratification rows for the same HC-2/D4R0K content.
  Ratify one unified row, not two.
- **N3 (upside already in BP1, make sure it runs).** BP1 R6: `slice_finite` may be
  PROVABLE outright (realizable carrier ⟹ nonempty fibers; `vtree_eq_of_fiberAt`
  contrapositive ⟹ disjoint across distinct trees ⟹ ≤ p^{nN} trees). The probe is
  folded into IB-D13 — worth its own explicit slot; if it lands, BridgeKernels
  loses a row and cl7_slice becomes the only finiteness row. Related upside for C2:
  for the CANONICAL policy, the locality law (ReadLocality's child_local) may be
  provable from the SP8 CanTreeModel CONSTRUCTION (its child predicate is built
  from level-N digit reads) — one construction proof would discharge treeN_stable
  + StableInputs + TransferRow simultaneously; a cheap probe unit at IB-D1/D2's
  verify stage would settle whether the row is a hypothesis at all.
- **N4 (probe coordination).** BP4 KB14 (python census probe of (U)/(R)) and BP3
  TV-A5b (Lean stray-countermodel attempt at the G1 carrier) attack the same pair
  from two sides. Complementary, but the sealed predictions should be SHARED (one
  prediction record, two artifacts), else a disagreement between them is
  undetectable.
- **N5 (micro).** IB-C3b is a corollary of `MovesS.ratfunc_eval_infinite` (C6
  above) — the landed sorry's docstring sketch re-proves it; point the prover at
  the existing lemma.
- **N6 (hygiene).** BP4 §2.1 cites the E5 fence-rule record as "2026-08-01" — that
  in-file date predates the PROJECT_STATE date correction (true date 2026-07-29);
  fix the in-file record when E5 is next touched (TV-A2).
- **N7 (sequencing dependency worth making explicit in the campaign DAG).** BP5's
  Moves/MovesGr quarantines are upstream of: C1's migration surface (three fewer
  copies), every future census (collision-free `#print axioms`), and the golf R2
  execution. Cheap, unblocks hygiene everywhere — schedule BP5's CL Moves/Gr
  clusters early, not last.
- **N8 (small dedup backlog for BP5, from the golf census, no adjudication
  needed).** MovesS `eval_algebraMap_div` triplication (PowSubstOK/N2PolyGeom/
  N2Rsh) + the N2 `okat_div/evalAt_div` idiom copies; MovesD E7/E8 private pairs;
  MovesT D14 `hist_ext` vs F0's `history_ext` (missing import); HC2 U14
  boxInv/muWidth arithmetic dup. All private-fence, all mechanical — fold into a
  single BP5 sweep unit rather than per-corpus attention.

END OF PASS 1. Recommended adjudication order: C3/N1 (blocks Group E) → C2/N2
(pre-ratification window) → C1+C4 (schedule as a cluster after BP5's quarantines)
→ C5/C6 (prompt amendments, immediate) → N3 probes.

