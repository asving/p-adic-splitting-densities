# BRIDGE BP4 — THE OPEN KERNELS (general proofs for the computationally-sealed conjectures)

AREA: E0 (per-pool regularity escape) · D4R.0-K(a) (the 40,378-case boundary lemma)
· HMC (height-domain Markov compatibility) · WEIGHT-CHARGE/X.1b + X.3 · the
general-n exhaustion sharpening.
DATE 2026-07-30 · writer: blueprint architect (bridge campaign) · sources read and
verified this pass: MOVES_2026-07-24.md §§D4-R.0/S.4/V.1(v)/X.1b/X.2/X.3/X.4,
LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md (kernel-check scoreboard + HMCAug
escalation + E0 seal records), verification/probe_results_2026-07-30.txt (all four
seal blocks), verification/l1_boundary_enum.py (full model + tallies),
MovesS/Defs.lean (EscapeE0/PoolHyp/RegP), MovesX/Defs.lean (the kernel Props),
MovesU/DefsLedger.lean (the typed capstone rows), MovesV/Defs.lean + V4_hmc/V4_hmcaug
(HMC/HMCAug + the ¬HMC census toy), MovesT/E5_rootSplit.lean (the hD4R0K (U)∧(R)
fence), MovesX/XC3/XC4/XD2-XD4/XG4 (the exhaustion threshold forms),
docs/PROJECT_STATE.md (UPDATE 2026-07-29 "DONE CRITERION MET" + 07-30b/c).

STANDING FENCE FOR THE WHOLE AREA (binds every unit below): **this area is OPEN
MATHEMATICS.** Every unit is a proof ATTEMPT with an explicit fallback: if the
attempt stalls, the unit's deliverable is a SHARPENED OBSTRUCTION RECORD — the
exact typed statement that blocked, the countermodel or missing-law shape, and the
owner tag — committed as a header/manifest record, NEVER a silent sorry and NEVER
a weakened statement. The countermodel-first rule applies to every universal
statement marked [CM-first] in §4: its countermodel-attempt unit runs BEFORE its
prover is assigned. Statement fence: units may add NAMED warranted hypotheses
(flagged ⚑ for orchestrator ratification); no existing statement is touched.

--------------------------------------------------------------------------------
## 1. GOAL — what this area delivers to theoremU when complete

`LeanUrat.MovesU.U10_theoremU` (theoremU) is proved Lean-core over `UInstance`
bundles whose hypothesis surface names exactly the open kernels. This area
attacks the five mathematical kernels on that surface. Precisely, complete
success would discharge (or reduce, with the reduction machine-checked):

  (G-A) **E0 / (REG-p).** `MovesS.RegP T M RB p hK F` (Defs.lean:618 — per-pool
        `Nonempty (PoolHyp …)` at δ = 1 and every consumed leg pool p^δ) holds at
        EVERY prime p for the real table — today theoremU takes (REG-p) per-prime
        as its gate. Deliverable shape: `EscapeE0 A` (Defs.lean:524 — nonneg +
        A^k𝟙 → 0) for every pool's active submatrix, from either the measure
        route (X.3-conditional, the note's displayed ROUTE E0, MOVES 12179-96) or
        the matrix route (per-state exit positivity). Consumers: RS.3, SQ.2,
        `RegPin.detHyp`, `SolveSeam.*` (DefsLedger.lean:536-676).
  (G-B) **D4R.0-K(a) = L1 totality.** The offset-P-lift is defined at every
        eligible recentering (MOVES 4653-4671), proved by tower induction —
        general (e,h,g,ψ)-stages, all weights above threshold, all classes,
        a > 0 anchors included. Direct Lean consumers: the `hD4R0K` (U)∧(R)
        fenced sorry in `MovesT/E5_rootSplit.lean:343` (owner HC-2/D4R0K), the
        `treeN_stable` row (E11), and the HC-1/HC-2 D4R0K owner rows.
  (G-C) **HMC.** `MovesV.HMC TE D` (Defs.lean:1180) — the exact-domain stepwise
        factorization. Known machine facts: ¬HMC at a carrier-level toy
        (`hmc_false_witness`, V4_hmc.lean:369), `hmcaug_of_hmc`
        (V4_hmcaug.lean:215), the n=2 scalar instance `n2_hmc` (N2Hmc.lean).
        Deliverable shape: HMC REDUCED to two named structural laws
        (DomProj + MarkCompose, §3.C) with the reduction machine-checked, plus
        HMC proved on the order-0/self-loop-free perimeter. Consumers:
        (COMP-Σ)/V5-5, V4-12(a), `SolveCond`.
  (G-D) **WEIGHT-CHARGE / X.1b.** `MovesX.WeightChargeT4P/-FullP`
        (MovesX/Defs.lean:367/372) — #recenterings ≤ s(n)·v_p(disc f).
        Deliverable shape: the reduction WEIGHT-CHARGE ⇐ TRACK-COUNT
        (`Cl7Kernel.track_restarts`, MovesU/DefsLedger.lean:206) + the
        disc-positivity base lemma (§3.D), machine-checked; then the
        TRACK-COUNT/different-budget attempt itself. Consumer: `cl2_route =
        MovesX.X3aRouteP` (DefsLedger.lean:167) → `x3Series` (XG4).
  (G-E) **X.3 general-n + the exhaustion sharpening.** `x3Series` is already
        PROVED conditional (XG4). The open legs this sub-area attacks: the five
        X.2 Props (`X2AffP/X2CapP/X2TailsP/X2BridgeP/X2ProgressP` = the
        theoremU rows cl3_*), `NsNullP` (paper-proved, unported), and the ALIGN
        state feeding `X1aAlignP` — i.e. everything between the proved
        conditional assembly and an unconditional X.3 at general n.

NON-GOAL (fence): htameFE/palindromy (out of scope by directive), the Phase-B/
HC-2 instantiation bridges (owner: the instantiation area), VP-SOUND's published
cites (owner: the axiom-policy area). Anything here that needs those consumes
them as named hypotheses.

--------------------------------------------------------------------------------
## 2. OBJECT INVENTORY (all verified by reading this pass)

### 2.1 Existing Lean objects CONSUMED (owner file · status)

| object | owner file | status |
|---|---|---|
| `EscapeE0` (nonneg + A^k𝟙→0) | MovesS/Defs.lean:524 | built, sorry-free |
| `PoolHyp` (Act, A, A_eval, inactive_vanish, e0) | MovesS/Defs.lean:533 | built |
| `RegP` (per-pool quantifier over consumedDeltas) | MovesS/Defs.lean:618 | built |
| `consumedDeltas`/`deltaFactors` | MovesS/Defs.lean:600-614 | built |
| `e0_det_ne_zero : EscapeE0 A → (1-A).det ≠ 0` | MovesS/E0DetNeZero.lean | PROVED |
| `EscapeE0 → (I-A)⁻¹ ≥ 0` | MovesS/E0InvNonneg.lean | PROVED |
| Neumann partials, pow-entry lemmas | MovesS/NeumannPartial.lean, PowEntry*.lean | PROVED |
| n=2 pool packages (q₀=2 etc.) | MovesS/N2Pool.lean, N2Pools.lean | PROVED (subsingleton route) |
| symbolic det chain | MovesS/Rs3DetSymbolic.lean, RatfuncEvalInfinite.lean, AllActiveCofinite.lean | PROVED (conditional) |
| `MovesV.HMC` | MovesV/Defs.lean:1180 | Prop def; OPEN kernel |
| `MovesV.HMCAug`, `hmcaug_of_hmc` | MovesV/Defs.lean:1402, V4_hmcaug.lean:215 | PROVED |
| `hmc_false_witness` (¬HMC toy) + `coupling_signature` | MovesV/V4_hmc.lean:369 | PROVED (decide-checked) |
| `witHMC` (n=1 witness satisfies HMC) | MovesV/V1_witnessB.lean:144 | PROVED |
| `n2_hmc` (1×1 kstep power law) | MovesS/N2Hmc.lean | PROVED |
| `XFamily`, `XConsts`, `XHistory`, `Pop`, `dTotal`, `countPop`, `vdisc`, `discZero` | MovesX/Defs.lean | built |
| `X1aAlignP`, `WeightChargeT4P/FullP`, `X2AffP/CapP/ProgressP/TailsP/BridgeP`, `NsNullP`, `X3aRouteP` | MovesX/Defs.lean:362-426 | Prop defs (kernel surface) |
| `x1bReduction`/`x1bReductionT4` (the two-step reduction) | MovesX/XC3.lean, XC4.lean | PROVED (conditional) |
| `x2hypCount/Dichotomy/Assembled` (√N envelope) | MovesX/XD2-XD4.lean | PROVED |
| `x3Series` (per-σ series identity) | MovesX/XG4.lean | PROVED (conditional on X3aRouteP, NsNullP, VPSoundP, CountableFiberAdditive, SeriesData) |
| `Cl7Kernel` (L, Dden, wstar, Tbound, track_restarts, zero_gain, genuine_bound) | MovesU/DefsLedger.lean:199-217 | hypothesis structure (TRACK-COUNT face) |
| `UpstreamTyped` rows cl2_route/cl3_*/cl15_align | MovesU/DefsLedger.lean:166-175 | hypothesis structure |
| `hD4R0K` (U)∧(R) fenced sorry | MovesT/E5_rootSplit.lean:343 | SORRY (fenced, owner HC-2/D4R0K); no in-corpus countermodel constructible (fence-rule record 2026-08-01 in file) |
| `treeN_stable` (TreeNStable row) | MovesT/E11_treeN.lean | SORRY (fenced, owner HC-2/D4R0K) |
| (S6b) threshold vocabulary | Moves/DefsCore.lean (grep S6b), HC1/DefsTower.lean ff. | built (B2-DEF corpus) |
| `TreeModel.child`, `rootCell`, `redPoly`, `trackOf`, `VTree.fiberAt` | MovesD/, MovesT/Defs.lean | built |

### 2.2 Enumeration/probe artifacts CONSUMED (the proof hints)

| artifact | content |
|---|---|
| verification/l1_boundary_enum.py + probe_results §PROBE-6 | 40,378 realizer cases: stage-2 grid (recursion bottoms; p∈{2,3,5}, (e,h,g) with e≤3,h≤3,g≤3), stage-3 grid (ONE genuine recursion step), W ranges [ehg+1, ehg+2e], all classes covered at every eligible W, 3 negative controls. Model: j₀ = h⁻¹W mod e; slots j₀+ek; summand weights all ≡ W; recursion guard u_k > e₁h₁g₁. |
| verification/escape_probe_a.py + results §0-3 | E0 seal 140/0: symbolic row guards (row sums = 1), sealed pool values, dead-cell lists (p=2 has 6 dead cells, p=3 one), SCC scan: every active class a SINGLETON with in-class mass κ_e(q₀) < 1 (κ₂ = 1/(q²+q+1), κ₃ = 1/(q⁶-1)·(q-1)-shaped); exits split into term + split columns. |
| verification/escape_probe_b.py | A^k𝟙 = κ^k EXACTLY per type (the active block acts diagonally at n≤3); depth partials T_k; independent digit census brackets. |
| verification/x_n3_probes.py + X1B adjudication (tasks 57/58) | X-n3 30/32; layer-(i) reading A ((CD)-pinned, d_cert-only) SEALED 0 violations; the over-broad reading refuted (155,648 violations) exactly as the note predicts. |
| verification/state_track_probes.py | STATE/TRACK 15/15 (first TRACK run) — TRACK-COUNT's L(n) face sealed. |

### 2.3 NEW objects this area builds (proposed namespace ⚑ Q1)

| object | home (proposed) | role |
|---|---|---|
| `Kernels/E0Matrix.lean`: `RowSumLt`, `NoClosedClass`, `SubStochastic` + escape theorems | new mini-corpus `LeanUrat/Kernels/` | the abstract matrix layer (§3.A) |
| `Kernels/E0Route.lean`: `KernelMassLaw`, `BlockDrain` + the ROUTE-E0 theorem | same | the typed measure route |
| `Kernels/D4R0K/Tower.lean`: `StageData`, `TowerData` (I-aug), `wt`, `offP`, `digRead` | same | the transcribed enumeration model (§3.B) |
| `Kernels/D4R0K/L1.lean`: `l1_totality` (the induction) | same | the kernel theorem |
| `Kernels/HmcReduction.lean`: `DomProj`, `MarkCompose` + `hmc_of_domProj_markCompose` | same | the HMC reduction (§3.C) |
| `Kernels/WeightChargeRed.lean`: `recentering_vdisc_pos` + `weightChargeFull_of_trackCount` | same | the X.1b reduction (§3.D) |
| `Kernels/Obstructions/*.md-headers` | same | the fallback obstruction records (one per stalled attempt) |

Everything in 2.3 is ADDITIVE — no existing statement changes; the seam units
that tie `Kernels/` objects to owner-corpus vocabulary are separate, flagged.

--------------------------------------------------------------------------------
## 3. THE MATHEMATICS

### 3.A E0 — per-pool regularity escape

**The kernel (quoted shape, MOVES 12163-12177).** For each relevant pool
q₀ = p^δ (δ = 1 and every consumed base-change leg) and each e ≤ n, with
A(q₀) the CTS-M(ii) active submatrix of K_e(q₀):

    (E0)   A(q₀)^k 𝟙 → 0  as k → ∞    (hence ρ(A) < 1, Neumann converges,
                                        (I − A)⁻¹ ≥ 0 — both already PROVED
                                        downstream of `EscapeE0` in MovesS).

**What the enumeration exhausts (the proof hint).** escape_probe_a/b found, at
every tested pool (p ≤ 7, n ≤ 3): (i) every SCC of the active digraph is a
SINGLETON (blk2, blk3) with in-class one-step mass κ_e(q₀) < 1; (ii) A^k𝟙 =
κ^k exactly — the active block acts DIAGONALLY at n ≤ 3; (iii) every row's
deficit is carried by the TERMINAL column (term = 6/7, 12/13, …), split-exit
mass appearing only at blk3. The pattern the induction must capture: a
still-in-block step is a (c = 1, m = 1) same-size single-child transition
((K-SUB)'s classification), and from EVERY realized active state the next read
has an exit outcome (terminal or split) of positive cell mass at the pool.

**Three routes, formalized in decreasing strength (all three blueprinted; any
one suffices for the escape law; the theorems are additive):**

ROUTE 1 (matrix, per-state exit positivity — the "regularity escape"):
  (1a)  [abstract] nonneg + every row sum ≤ κ < 1  ⟹  A^k𝟙 ≤ κ^k𝟙 → 0.
  (1b)  [abstract] nonneg + substochastic (row sums ≤ 1) + no closed class
        (from every state a path to a row-deficit state)  ⟹  escape.
        Key identity: with m := card ι, ε := (min positive entry)^m · (min
        row deficit) > 0, every entry of A^m𝟙 is ≤ 1 − ε; monotonicity of
        k ↦ A^k𝟙 (substochasticity) interpolates: A^k𝟙 ≤ (1−ε)^⌊k/m⌋𝟙 → 0.
  (1c)  [converse, the refuter's soundness] a closed class C (every row of C
        sums to 1 within C) forces (A^k𝟙)|_C = 𝟙 — ¬escape. This makes
        escape_probe_a's layer-1 criterion a THEOREM, not just a script.
  (1d)  [the open leg] per-state exit positivity at the REAL table: at every
        pool q₀ and every realized active state τ, the one-step exit mass
        (terminal + split) is > 0 — equivalently row sum < 1. WILD SUBTLETY:
        cell-count polynomials DO die at small pools (p = 2 kills six cells,
        probe §2), so the argument must exhibit an exit cell that SURVIVES
        every q₀ ≥ 2. Candidate: the separable-residual escape digit — a
        still-in-block state's next window read has a digit choice making the
        residual polynomial SQUAREFREE (count of squarefree monics of degree
        e over F_q is q^e − q^{e−1} > 0 for e ≥ 2, q ≥ 2; degree-1 residuals
        are separable outright), and a squarefree residual at an e_read = 1
        read is a hen/terminal outcome. The obstruction to check FIRST: the
        window digits parameterize only PART of the residual's coefficients
        (anchored strata pin a z^a factor), so squarefreeness must be forced
        by the FREE coefficients away from the anchor. If that fails at some
        (state, pool), the fallback record documents the exact window-to-
        residual map and the pinned coefficient set.

ROUTE 2 (measure — the note's own ROUTE E0, MOVES 12179-96): typed interface
  `KernelMassLaw`: (A^k𝟙)_τ = the still-in-block-after-k mass from τ
  (normalized conditional mass; k = 0 forced to 1 — non-vacuity); masses
  antitone in k. `BlockDrain`: μ(never exits the block) = 0 (the X.3
  consumer — CL-4). Then each scalar sequence is antitone, bounded below,
  with infimum μ(never exit | τ) = 0 ⟹ Tendsto 0. Monotone convergence over
  a FINITE index is elementary — no measure theory beyond the interface.
  This route makes E0's X.3-conditionality a machine-checked implication:
  X.3 ⟹ E0 at the identified kernel (per pool, transported per [2r] at δ>1).

ROUTE 3 (pool closure at n ≤ 3): decide/norm_num packages `PoolHyp` at the
  sealed pools for the real n=3 carriers, MIRRORING N2Pool/N2Pools — blocked
  on N3 carrier existence (⚑ Q3).

The det-side (S.4(ii)) is ALREADY BUILT conditional (`e0_det_ne_zero`,
Rs3DetSymbolic, RatfuncEvalInfinite): symbolic det ≠ 0 from escape at
infinitely many pools. Only glue units remain there.

### 3.B D4R.0-K(a) — the L1 tower-totality induction

**The kernel (MOVES 4653-4671 + (S6b′) 2436-2455 + pass-11 repair 2893-2900).**
At every eligible recentering read (e_read = 1, value W strictly above the
clean threshold w_prev(Φ) = e·h·g), the offset-P formula returns a realizer t
with w(t) = W and ANY prescribed residual class τ ∈ F′^× — including minimal
W, g = 1, and anchored targets a > 0.

**The formula (the enumeration's model, to be transcribed verbatim):** stage
data (e, h, g, ψ), gcd(e,h) = 1, F′ = F_prev[z]/(ψ);
  j₀ := h⁻¹·W mod e (the forced slot class);
  slots j₀, j₀+e, …, j₀+(g−1)e ≤ eg−1;
  P ∈ F_prev[z] the unique deg < g representative with z̄^m·P(z̄) = τ;
  t := Σ_{P_k ≠ 0} t_k·Φ_prev^{j₀+ek}, where t_k realizes scalar P_k at
  parent-parent-scale weight u_k := (W − (j₀+ek)h)/e — BY RECURSION one
  stage down, guarded by u_k > e_prev·h_prev·g_prev.

**The induction that captures what 40,378 cases exhaust.** The enumeration ran
the stage-2 grid (recursion bottoms at the base: digits are F_Q-unit lifts,
no threshold) and the stage-3 grid (ONE genuine recursion step). The general
proof is strong induction on the stage index r with induction hypothesis
exactly (S6b′)'s CLAIM one stage down. Per-stage obligations:

  (L1-i)   SLOT ARITHMETIC: j₀ well-defined (gcd(e,h) = 1 ⟹ h invertible
           mod e); every slot ≤ eg−1; e ∣ W − (j₀+ek)h for all k; u_k ∈ ℕ.
  (L1-ii)  GUARD: W > ehg ⟹ e·u_k = W − (j₀+ek)h ≥ W − (eg−1)h > h, and by
           (I-aug) at the previous read (h > e·w_prevprev(Φ_prev)·(…) — the
           displayed two-line chain, MOVES 2450-2455): u_k > threshold one
           stage down. So the recursive calls are ELIGIBLE.
  (L1-iii) WEIGHT EXACTNESS: every summand t_k·Φ^{j₀+ek} has parent-scale
           weight e·u_k + (j₀+ek)h = W — all summands share weight W; the
           leading form of the sum is the class read z^m·P(z̄) = τ ≠ 0
           (τ a UNIT), so no cancellation: w(t) = W exactly.
  (L1-iv)  CLASS READ: the k-th residual coefficient res(t_{j₀+ek}/p^{u_k})
           equals P_k by the IH's exactness (each t_k has exact weight u_k
           and prescribed leading scalar); the read is linear over slots
           (slots are distinct mod e ⟹ no cross-slot interference); hence
           dig(t) = τ. COVERAGE: τ ↦ t is defined for every τ ∈ F′^×
           (bijectivity of the class map onto targets = the P-representative
           uniqueness); anchored targets τ = z̄^a·u are particular classes —
           covered; the anchor offset m is absorbed into the slot-generator
           convention (the script's CONVENTION paragraph).
  (L1-v)   DETERMINISM: t is a function of (stage data, W, τ) — by
           construction (a def, not a choice).
  (L1-vi)  BASE: stage 1 — every scalar in F_Q^× realizable at every weight
           by a unit lift (no threshold).

CONVENTION FENCE (inherited from the script, binding on the seam unit): the
note's own digit map may differ from the model's by a slot-unit twist that is
a FUNCTION OF NODE DATA — a data-determined bijection of nonzero classes. The
model theorem therefore implies totality/weight/determinism under the note's
convention; WHICH class gets WHICH realizer is convention-relative. The seam
unit to the HC-1 (S6b) vocabulary must carry this twist explicitly (⚑ Q2).

**The (U)∧(R) consumer (MovesT/E5:343).** Distinct kernel content — part
(b)/Theorem B territory, at the ROOT level: (U) per-point per-track uniqueness
of realized root children; (R) realized root children have track multiplicity
≥ 2 in redPoly. Root-level sketches: (U) — two realized root children over
the same track ψ carry the same side/digit data (functions of f at the root)
and the same canonical lift (L1 determinism!) ⟹ equal nodes. (R) — a
multiplicity-1 track has a simple factor; the (c2) covering case analysis
(MOVES 7112-7119) shows the read at a simple factor terminates (hen leaf), so
no CONTINUING child exists on that track. Both are blueprinted as attempts at
the canonical OM instance; at the abstract `CellData` interface they are the
candidate law pair the E5 fence records (adjudication-tagged).

### 3.C HMC — the reduction to DomProj + MarkCompose

**The kernel (MOVES 8198-8220; Lean `MovesV.HMC`, Defs.lean:1180):**

    (HMC)  (D.dom (.cons m γ)).Mem (h₁ ++ h₂) ↔
             (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂.

**Machine facts on record:** ¬HMC holds at a census-coupled carrier toy
(`hmc_false_witness` — the composite census empty at (0,0) while both factors
are full); HMC ⟹ HMCAug (`hmcaug_of_hmc`); the HMCAUG escalation verdict (A)
withdrew the separation-witness obligation — under the full XHD exactness +
uniformity package the coupling may have no model at all (the wall channel is
the escape). The orchestrator's round-8 structural analysis (campaign note
2026-07-29) pinned the ⊇ failure point exactly: composite census positivity
needs a composite MARK, and marks do not compose.

**The reduction (this area's main deliverable — HMC is NOT claimed):** split
the iff into its two directions and NAME the missing structural laws:

  (DomProj)     Mem (h₁ ++ h₂) → Mem h₁ ∧ Mem h₂   (the ⊆/projection leg:
                a realized composite history realizes its steps). [CM-first]:
                as XHDd is TYPED (dom is data), an instance violating DomProj
                is likely constructible — then DomProj is a genuinely new
                named law, ⚑ flagged, consumed as a hypothesis (never a new
                XHDd field without ratification).
  (MarkCompose) per-step realized marks with matching retained states compose
                to a realized composite mark: Mem h₁ ∧ Mem h₂ → Mem (h₁ ++ h₂)
                — exactly the "marks compose" gap. [CM-first]: MUST fail at
                the census toy (else the toy would satisfy HMC) — the
                compiled failure witness is the sharpened obstruction record.

  THEOREM (the reduction): DomProj ∧ MarkCompose ⟹ HMC — by construction
  nearly definitional once both laws are typed on the same carriers; the
  content is the TYPING (getting the retained-state matching and the Hpt
  append right — the V4 cast-lemma toolkit exists).

**The provable perimeter:** HMC on ORDER-0/SELF-LOOP-FREE templates (the same
perimeter as the capstone's order-0 slice and the wave-A2 spword/instbij
scopings): steps whose domains are full products of per-coordinate threshold
conditions — there Mem is componentwise and the factorization is `Iff.rfl`-
adjacent. Typed via a named `Order0Sys` predicate with the V1 witness and the
HmcToy (¬Order0Sys — the toy's coupled census violates the predicate) as the
two instance checks.

### 3.D WEIGHT-CHARGE / X.1b — the TRACK-COUNT reduction + the different-budget attempt

**The kernel (MOVES 11153-11160):** #{recentering nodes of H} ≤ s(n)·v_p(disc f),
FULL population (T4 + uncertified T1) while (ALIGN-rec) is undischarged.

**The new observation this blueprint contributes (the reduction):** the typed
TRACK-COUNT face already in the capstone ledger — `Cl7Kernel.track_restarts`
(DefsLedger.lean:206): #recT1(H) + #t4(H) ≤ L(n), a CONSTANT bound, f ∉
discZero, per stratum history. Given track_restarts, WeightChargeFullP with
s(n) := L(n) follows from ONE new base lemma:

  (REC-DISC)  a stratum history with ≥ 1 recentering node forces
              v_p(disc f) ≥ 1.
  Sketch: any node beyond an immediate-hen root read sits on a track whose
  root reduction factor has multiplicity ≥ 2 (the (R) law of §3.B / the (c2)
  covering); a repeated factor of f̄ = f mod p forces disc f ≡ 0 mod p
  (Res(f̄, f̄′) = 0), i.e. vdisc ≥ 1. Then: recT1 + t4 ≤ L ≤ L·vdisc = s·vdisc
  whenever a recentering exists; and = 0 ≤ s·vdisc otherwise.

  This collapses TWO open kernels into ONE: WEIGHT-CHARGE ⇐ TRACK-COUNT +
  (REC-DISC). TRACK-COUNT is itself sealed (15/15) and open; its attempt
  units use the note's own charging material: the strict weight climb per
  recentering (D.10, DERIVED), the (1/D(n))·ℤ weight lattice (the dnLattice
  duty), and the L5fix Invariant-2 different budget via (P2):
  v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ) — each restart must consume a
  unit of a monotone consumable. The T3 degree charge (≤ ⌊log₂ n⌋, PROVED at
  XB4) is the pattern. If the attempt stalls, the obstruction record states
  the exact unbounded-ladder shape that survives the budget accounting.

**Fence:** the X1B adjudication (tasks 57/58) fixed the layer-(i) READING —
d_cert counts only certified nodes, row-0 = no bound certified. All units
here must consume the (CD)-pinned reading; the refuted over-broad reading is
a recorded countermodel, not a target.

### 3.E X.3 general-n + the exhaustion sharpening

`x3Series` (XG4) already delivers the per-σ series identity GIVEN X3aRouteP +
NsNullP (+ VPSoundP/CountableFiberAdditive/SeriesData — owners elsewhere).
X3aRouteP is fed by §3.D (WEIGHT-CHARGE legs) and the ALIGN state. What
remains IN THIS AREA, per open-surface list (PROJECT_STATE UPDATE 2026-07-29):

  (E-i)   NsNullP — (ns-null) is PROVED ON PAPER (plan REV 15, the
          single-state admissible-Z argument, four verifications). PORT it:
          the highest-value unit of the cluster (paper proof exists; no new
          mathematics).
  (E-ii)  X2AffP attempt — threshold(H) ≤ 1 + c₀(n)·Σ h_r: induction along
          the branch through D.11's per-move form ("largest constrained
          height + 1") with scale factors Π e_i ≤ n; candidate c₀ = n·(max
          per-move constant). The missing coercive accounting is real —
          attempt + obstruction fallback.
  (E-iii) X2CapP attempt — cap(H) ≤ c_cap·(1 + Σ h_r) from TB-CAP's
          per-clause caps ((τ-hen) N_V = 1; (τ-irr) per-realized-cell,
          level-indexed by the leaf cell's own heights).
  (E-iv)  X2TailsP attempt — frac(TallEvent h*) ≤ C_T·p^{−c_T h*}: price the
          FIRST height-≥h* read via the D4R.2 pool bound μ(P̂) ≤
          M(P̂)·p^{W(P̂)−A(P̂)} (A grows with the tall read's height); the
          union over prefixes needs the per-depth species-menu factor —
          convergence of that series is the risk (obstruction fallback).
  (E-v)   X2BridgeP attempt — the Undec(N) decomposition: set-theoretic from
          decision stability + the TB-CAP leaf trichotomy; likely needs ONE
          new named XCtx law (`DetectAtThr`: a complete branch tree with
          thr + cap ≤ N is decided at N) — ⚑ flagged if so.
  (E-vi)  X2ProgressP (linear) — the PROGRESS kernel proper (per-move mass
          pricing); LOWEST priority: X.3 does NOT consume it (only SQ.3's
          quantitative envelope does), and the √N form is PROVED (XD4).
  (E-vii) ALIGN-inc attempt — the certified-increment transport of GMN
          Cor 4.19's accounting through the X.1a index table (T0-T5 rows,
          reading A). Consumes the declared GMN axiom; the general assembly
          is D.12-transport bookkeeping.

The "general-n exhaustion sharpening" is exactly (E-i)-(E-v): every MovesX
threshold form is ALREADY stated at general n (verified: X2*P quantify over
all p, all branches, n a parameter); the sharpening = converting the n=3-
sealed layers into general theorems or named obstructions, never widening
any statement.

--------------------------------------------------------------------------------
## 4. UNIT SPLIT (53 units: KA 13 · KB 13 · KC 9 · KD 8 · KE 10)

Format: id · statement (informal or Lean sketch) · deps · sketch · difficulty
(routine-opus / hard-fable / adjudication) · est. Lean size. Files per §2.3.
Every [ATTEMPT] unit carries the fallback duty of §0; every [CM-first] unit's
countermodel twin runs first.

### KA — E0 (file Kernels/E0Matrix.lean, E0Route.lean; seams in MovesS)

KA1  `escapeE0_of_rowsum_lt` : (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j ≤ κ) →
     κ < 1 → EscapeE0 A. deps: —. Sketch: induction on k: A^k𝟙 ≤ κ^k𝟙
     entrywise (mulVec monotone); squeeze with κ^k → 0. routine-opus, ~35 ln.
KA2a `mulVec_mono` toolkit: nonneg matrix preserves ≤ on vectors; A^k𝟙
     antitone under substochasticity; entrywise ≤ closed under mulVec.
     deps: —. routine-opus, ~30 ln.
KA2b `deficit_spread` : A nonneg substochastic, m := Fintype.card ι, every
     state reaches a strict-deficit row in ≤ m steps ⟹ ∃ ε > 0, ∀ i,
     (A^m *ᵥ 𝟙) i ≤ 1 − ε. deps: KA2a. Sketch: ε := (min positive entry)^m ·
     (min deficit); walk the reaching path, peel one factor per step; finite
     min over states. hard-fable, ~80 ln (split further if it grows).
KA2c `escapeE0_of_noClosedClass` : nonneg + substochastic + reachability
     hypothesis ⟹ EscapeE0. deps: KA1, KA2a, KA2b. Sketch: A^{km}𝟙 ≤
     (1−ε)^k 𝟙 by KA2b + induction; interpolate by KA2a antitonicity.
     routine-opus given deps, ~40 ln.
KA2d [CM-first twin of KA2c] compiled witnesses that BOTH hypotheses are
     needed: A = [[2]] (nonneg, deficit-free reachability vacuous, no
     escape); A = [[1]] (substochastic, closed class, no escape). deps: —.
     routine-opus, ~25 ln.
KA3  `noEscape_of_closedClass` (the refuter's soundness): C ⊆ ι nonempty,
     ∀ i ∈ C, ∑_{j∈C} A i j = 1 ∧ ∀ j ∉ C, A i j = 0 ⟹ ¬ EscapeE0 A.
     deps: KA2a. Sketch: (A^k𝟙)|_C = 1 by induction; Tendsto to 0 fails.
     routine-opus, ~35 ln. (Makes escape_probe_a layer 1 a theorem.)
KA4a `KernelMassLaw`/`BlockDrain` interface records (E0Route.lean): fields
     mass : ℕ → ι → ℝ≥0∞ (or ℚ≥0), law_zero : mass 0 = 1, law_step :
     mass (k+1) τ = Σ_β A τ β · … , antitone, drain : ∀ τ, ⨅ k, mass k τ = 0;
     tie : (A^k *ᵥ 𝟙) τ = mass k τ. NON-VACUITY: a decide instance at the
     N2 pool. deps: —. routine-opus (design care), ~50 ln. ⚑ interface —
     orchestrator ratifies field list before provers run.
KA4b `escape_of_drain` : KernelMassLaw + BlockDrain → EscapeE0 A. deps:
     KA4a. Sketch: per-τ scalar sequence antitone bounded below with inf 0 ⟹
     tendsto 0 (Mathlib `tendsto_atTop_ciInf`); finite index ⟹ Pi.tendsto.
     routine-opus, ~30 ln.
KA4c ROUTE-E0 seam: the note-shaped theorem `X.3-drain ⟹ per-pool escape` —
     BlockDrain derived from a SeriesData/XCtx-level a.e.-termination
     hypothesis at the pool (the CL-4 consumer edge, MOVES 12180-12187).
     deps: KA4b + MovesX.XCtx. Statement design is the work: BlockDrain's μ
     is the still-in-block conditional mass; the never-exit event embeds in
     InfTree ∪ nsFibers. hard-fable, ~70 ln. [ATTEMPT — if the embedding
     needs an unbuilt process-to-kernel identification, the fallback record
     types it as the named CL-5 identification hypothesis and stops.]
KA5  `escapeE0_of_exitPos` : (∀ i, ∑ j, A i j < 1) → nonneg → EscapeE0 A.
     deps: KA1. Sketch: κ := Finset.max of row sums, < 1 by finiteness.
     routine-opus, ~20 ln.
KA6a [CM-first for KA6b] the exit-cell survival probe (python,
     verification/): for synthetic (K-SUB)-shaped tables at q₀ ∈ {2,3,4,8,9}
     and states with anchored windows, search for a (state, pool) whose
     EVERY exit cell dies (cell count 0 at q₀). A finding refutes the
     per-state form of E0's escape and reroutes KA6b to the class-level
     statement. deps: —. routine-opus (script + seal record), no Lean.
KA6b [ATTEMPT] the separable-residual escape digit: at every realized active
     state and every pool q₀ ≥ 2, some window digit choice yields a
     squarefree residual (⟹ terminal outcome; row sum < 1 via KA5).
     Mathematical core: squarefree monics of degree e over F_q number
     q^e − q^{e−1} > 0; the anchored z^a factor must be avoided by FREE
     window coefficients. deps: KA6a; carriers: the §M-SPECIES menu
     (MovesSp) or a self-contained window model (⚑ Q1). hard-fable —
     THE OPEN CORE of E0; fallback: the obstruction record pinning the
     window-to-residual coefficient map and which (state, pool) resists.
     Est. ~120 ln if it goes; split at the first stall.
KA7  n=3 pool closure: `PoolHyp` instances at q₀ ∈ {2,3,4} for the real n=3
     carriers by norm_num/decide, mirroring N2Pool (values sealed: κ₂, κ₃,
     dets at probe §1). deps: N3 carriers (⚑ Q3 — BLOCKED until answered).
     routine-opus per pool once carriers exist, ~60 ln each.
KA8  the δ > 1 transport: EscapeE0 at the base-changed pool from the O_δ
     theory's own instance — typed conditional over consumedDeltas: a
     structure `PoolTransport` carrying the [2r]/(e2) identification as a
     named hypothesis + theorem RegP_of_baseAndTransport. deps: KA1-KA5.
     hard-fable (typing the transport honestly), ~70 ln.
KA9  det glue: `detHyp_of_escape_infinite` — EscapeE0 at infinitely many
     prime pools ⟹ MovesS.DetHyp (symbolic), through e0_det_ne_zero +
     RatfuncEvalInfinite. deps: existing MovesS chain. Verify what
     Rs3DetSymbolic already states; this unit may be verify-only/glue.
     routine-opus, ~30 ln.

### KB — D4R.0-K(a) (files Kernels/D4R0K/Tower.lean, L1.lean; seams in HC1/MovesT)

KB1  `StageData`/`TowerData` records: per-stage (e, h, g, ψ) with gcd(e,h)=1,
     ψ monic irreducible deg g, ψ(0) ≠ 0; the (I-aug) chain h_{i} >
     e_i·(e_{i−1}h_{i−1}g_{i−1}) as a field; fields F_i as iterated
     AdjoinRoot (or the enumeration's tuple model). NON-VACUITY: the p=2
     stage-3 instance from the probe grid, by decide. deps: —.
     routine-opus (design care), ~80 ln. ⚑ interface ratification.
KB2  slot arithmetic: `j0` def (h⁻¹W mod e via ZMod e units), slots ≤ eg−1,
     e ∣ W − (j₀+ek)h, u_k := (W−(j₀+ek)h)/e ∈ ℕ with e·u_k + (j₀+ek)h = W.
     deps: KB1. Sketch: ZMod.unitOfCoprime + omega. routine-opus, ~40 ln.
KB3  the guard chain: W > ehg ⟹ ∀ k < g, u_k > threshold one stage down
     (the two-line (I-aug) inequality, MOVES 2450-2455). deps: KB1, KB2.
     Sketch: e·u_k ≥ W − (eg−1)h > ehg − (eg−1)h = h; then (I-aug):
     h > e·(prev threshold). All in ℕ with the e-divisibility from KB2 —
     avoid rational division. routine-opus, ~35 ln.
KB4  weight of a slot summand: w(t_k·Φ^{j₀+ek}) = e·w(t_k) + (j₀+ek)h at
     exact-weight t_k — the parent-scale weight law of the development.
     deps: KB1 model's `wt` def. routine-opus, ~30 ln.
KB5  leading-form nonvanishing: the sum over slots of prescribed leading
     scalars reads to z^m·P(z̄) = τ ≠ 0; distinct slot classes mod e ⟹ no
     cross-slot interference; hence w(t) = W EXACTLY (min attained, no
     cancellation at weight W). deps: KB2, KB4. hard-fable (the ultrametric
     min + read linearity — the one genuinely delicate stage lemma),
     ~80 ln; pre-approved split: KB5a (min ≥ W), KB5b (read = τ ⟹ = W).
KB6  the class map: τ ↦ P (unique deg < g representative with z̄^m·P = τ),
     bijectivity onto F′^× including anchored τ = z̄^a·u. deps: KB1.
     Sketch: AdjoinRoot representative uniqueness; z̄ invertible since
     ψ(0) ≠ 0. routine-opus, ~40 ln.
KB7  base case: stage-1 realizers — every c ∈ F_Q^× at every weight, unit
     lift, exact weight, deterministic. deps: KB1. routine-opus, ~30 ln.
KB8  `l1_totality` — THE INDUCTION: ∀ stage r, ∀ W > thr_r, ∀ τ ∈ F_r^×,
     ∃! (by-construction) t = offP r W τ with wt t = W ∧ digRead t = τ.
     deps: KB2-KB7. Sketch: strong induction on r; per-slot recursive call
     eligible by KB3; assemble by KB5 + KB6. hard-fable (the assembly),
     ~90 ln; split at need into existence/exactness/read legs.
KB9  determinism + boundary corollaries: offP is a def (function of node
     data); the enumerated boundary corners (min W, g = 1, |F′^×| = 1 at
     p = 2) fall out as instances — state them as decide checks against the
     probe's tallies (spot rows, not all 40,378). deps: KB8. routine-opus,
     ~40 ln.
KB10 negative controls as theorems (the gate's teeth, probe §3): corrupted
     slot class j₀+1 leaves the zero class; (I-aug) violation trips the
     guard. deps: KB2, KB3. routine-opus, ~35 ln.
KB11 [ADJUDICATION] the convention seam: the twist lemma — any slot-unit
     twist that is a function of node data induces a bijection of nonzero
     classes commuting with totality/weight/determinism (the script's
     CONVENTION paragraph, typed). Then the seam statement to HC-1's (S6b)
     vocabulary (Moves/DefsCore.lean thresholds). deps: KB8; owner overlap
     HC-1. adjudication (⚑ Q2 decides the target form), ~60 ln.
KB12 [ATTEMPT] (U) at the canonical instance — per-point per-track root-
     child uniqueness (E5's first conjunct): two realized root children on
     one track share side/digit data (functions of f) + the canonical lift
     (KB8 determinism) ⟹ equal. deps: KB8 + MovesD.CanonPolicy vocabulary.
     hard-fable; fallback: the obstruction record naming the missing
     child-datum-is-function-of-f law. ~70 ln.
KB13 [ATTEMPT] (R) at the canonical instance — realized root children have
     track multiplicity ≥ 2 (E5's second conjunct; the (c2) covering,
     MOVES 7112-7119): a simple factor's read is hen-terminal, no
     continuing child. deps: MovesD/MovesT root-read vocabulary. hard-fable;
     same fallback genre. ~70 ln. KB12+KB13 together discharge the E5
     `hD4R0K` sorry AT THE CANONICAL INSTANCE (the abstract CellData row
     stays owner HC-2 — do NOT touch the fenced sorry without adjudication).

### KC — HMC (file Kernels/HmcReduction.lean; instances in MovesV)

KC1  direction census at the toy: which direction of HMC fails at
     `HmcToy` — prove `¬(Mem (h₁++h₂) ← factors)` at (0,0) (the composite
     census empties) and prove the OTHER direction HOLDS toy-wide (or
     refute). deps: V4_hmc vocabulary. routine-opus (decide-adjacent),
     ~40 ln. Sharpens the obstruction: the coupling kills ⊇ only.
KC2a [CM-first] DomProj countermodel attempt: build an XHDd instance
     violating Mem (h₁++h₂) → Mem h₁ ∧ Mem h₂ (dom is free data — expected
     constructible in ~1 field). deps: MovesV.Defs. routine-opus, ~45 ln.
     Outcome either way is a deliverable: witness ⟹ DomProj is a genuine
     new named law (⚑); no witness constructible from the laws ⟹ attempt
     KC2b upgrade.
KC2b `DomProj` def + (conditional on KC2a's outcome) derivation attempt from
     the XHDd law fields (no_stray/exactness family). deps: KC2a.
     hard-fable, ~50 ln. [ATTEMPT with fallback: DomProj stays a named
     hypothesis.]
KC3  `MarkCompose` def: per-step realized marks at matching retained states
     compose — Mem h₁ ∧ Mem h₂ → Mem (h₁++h₂), typed with the V4 cast
     toolkit (castHpt/append laws exist, MovesV/Defs.lean:1196-1219).
     deps: —. routine-opus (typing only), ~35 ln. ⚑ named-law ratification.
KC4  [CM-first twin] `markCompose_fails_at_toy` : ¬ MarkCompose HmcToy —
     REQUIRED (else the toy would satisfy HMC via KC5); the compiled
     witness IS the sharpened obstruction record of the kernel. deps: KC3.
     routine-opus (decide), ~30 ln.
KC5  `hmc_of_domProj_markCompose` : DomProj ∧ MarkCompose ⟹ HMC — the
     reduction theorem. deps: KC2b/KC3. Sketch: the two directions are the
     two laws; content = retained-state bookkeeping across .cons. routine-
     opus given the defs, ~40 ln.
KC6  `Order0Sys` predicate + `hmc_of_order0` : full-product step domains ⟹
     HMC (the provable perimeter). Instances: the V1 witness satisfies
     Order0Sys (re-derive witHMC through it); HmcToy does NOT (decide).
     deps: KC3-KC5 optional. hard-fable (predicate design), ~80 ln;
     pre-approved split: KC6a predicate + instances, KC6b the theorem.
KC7  consumer glue verify-only: (COMP-hΣ) + HMC ⟹ (COMP-Σ) — confirm the
     built V5-5 conditional consumes `HMC` verbatim and nothing stronger;
     record, no new proof expected. deps: MovesV V5 modules. routine-opus,
     ~15 ln or record-only.
KC8  n=3 real-chain HMC layer (mirror n2_hmc): the block-level kstep power
     law at the n=3 carriers. deps: ⚑ Q3 carriers. routine-opus once
     unblocked, ~30 ln.

### KD — WEIGHT-CHARGE / X.1b (file Kernels/WeightChargeRed.lean; seams in MovesX)

KD1  [CM-first] the s(n)-candidate refuter (python): re-run + extend the
     STALL-probe (p = 2 cubic 2²⁴ box, quartic RS-conditioned cylinder) to
     the ratio #recenterings / vdisc; also probe REC-DISC: search for f
     with a recentering node and vdisc f = 0 — a finding REFUTES KD2.
     deps: verification/ infra. routine-opus (script + seal), no Lean.
KD2  `recentering_vdisc_pos` (REC-DISC): H in the stratum of f, f ∉
     discZero, countPop H .recT1 + countPop H .t4 ≥ 1 ⟹ 1 ≤ vdisc f.
     deps: KD1 clean; vocabulary: MovesX + the mod-p discriminant lemma.
     Sketch: a recentering node presupposes a non-hen root read ⟹ repeated
     factor of f̄ ⟹ p ∣ disc f (Res(f̄,f̄′) = 0 — Mathlib discriminant/
     resultant or the L3Squarefree route, LeanUrat/L3Squarefree.lean).
     hard-fable (the classifier-side "recentering ⟹ repeated root factor"
     leg needs an XCtx/GMN law — if unbuilt, fallback: named hypothesis
     `RecImpliesWild` + the mod-p lemma proved unconditionally). ~70 ln,
     pre-approved split: KD2a (mod-p disc lemma), KD2b (classifier leg).
KD3  `weightChargeFull_of_trackCount` : Cl7Kernel-style track_restarts
     (∀ …, countPop H .recT1 + countPop H .t4 ≤ L) + REC-DISC ⟹
     WeightChargeFullP n X ⟨s := L, …⟩. deps: KD2. Sketch: case vdisc = 0
     (then count = 0 by KD2 contrapositive) vs vdisc ≥ 1 (L ≤ L·vdisc).
     routine-opus, ~30 ln. THE REDUCTION — collapses X.1b into TRACK-COUNT.
KD4  `weightChargeT4_of_trackCount` : same with .t4 ≤ full count ≤ L.
     deps: KD3. routine-opus, ~15 ln.
KD5  `x3aRoute_of_trackCount_align` : TRACK-COUNT + REC-DISC + X1aAlignP
     (inc state) ⟹ X3aRouteP (right disjunct). deps: KD3. routine-opus,
     ~20 ln. Discharges cl2_route's shape conditionally.
KD6  [ATTEMPT] TRACK-COUNT via the weight ladder: named `KeyWeightData`
     carrier (per-node key weight, strict climb per recentering — D.10
     DERIVED content; lattice (1/D(n))ℤ — the dnLattice duty) ⟹
     #recenterings ≤ D(n)·(w_final − w_init). deps: carrier design ⚑.
     hard-fable, ~80 ln; fallback: the typed carrier + the ladder lemma
     alone (already useful — it converts TRACK-COUNT into a weight-cap
     question).
KD7  [ATTEMPT] the weight cap via the different budget: w_final ≤ c(n)·
     (1 + vdisc f) through (P2)'s leaf-different term (L5fix Invariant-2).
     THE DEEP OPEN CORE of the cluster. deps: KD6; L5fix vocabulary
     (LeanUrat/L5fix.lean). hard-fable; fallback: obstruction record naming
     the exact budget consumable that fails to be exhibited (the note's own
     "must be exhibited, not assumed", MOVES 11166). ~100 ln if it goes.
KD8  assembly + fence audit: the (CD)-pinned reading check — every KD unit's
     d_cert consumption matches reading A (task 58's adjudication); record
     unit, verify-only. deps: KD2-KD5. routine-opus, record-only.

### KE — X.3 general-n + exhaustion sharpening (files in MovesX + Kernels/)

KE1  NsNullP port (the paper-proved (ns-null)): the single-state
     admissible-Z argument (plan REV 15; four verifications on record) over
     the XCtx nsFiber vocabulary. deps: locating the paper proof text
     (MOVES (ns-null) closure record) + XCtx. hard-fable (port, not
     invention), ~90 ln; pre-approved split: KE1a (the single-state lemma),
     KE1b (fiber-null assembly).
KE2  [ATTEMPT] X2AffP: branch induction through D.11's per-move threshold
     form with scale product Π e_i ≤ n; candidate c₀ = n·C_move. deps:
     XCtx.threshold laws (check which exist; if the per-move form is
     unbuilt, ⚑ a named `ThresholdStep` law). hard-fable, ~90 ln;
     fallback: obstruction record with the branch shape whose threshold
     outruns the affine bound.
KE3  [ATTEMPT] X2CapP: from TB-CAP's per-clause caps ((τ-hen) N_V = 1
     PROVED; (τ-irr) per-realized-cell). deps: [3t] TB-CAP Lean surface
     (MovesT). hard-fable, ~70 ln; same fallback genre.
KE4  [CM-first] X2TailsP countermodel probe (python): exhaustive tall-event
     masses at n = 3, p ∈ {2,3}, h* ≤ 8 vs candidate (C_T, c_T) — refutes
     candidates, never the existential. deps: verification/. routine-opus.
KE5  [ATTEMPT] X2TailsP: price the first height-≥h* read by D4R.2's pool
     bound; sum over prefixes with the species-menu branching factor.
     deps: KE4; MovesD mass laws (D4R.1/D4R.2 built). hard-fable, ~90 ln;
     fallback: the divergent-series obstruction record.
KE6  [ATTEMPT] X2BridgeP clause 1 (the set decomposition): Undec(N) ⊆
     discZero ∪ nsFibers ∪ InfTree ∪ {thr+cap > N leaf branch}. deps:
     XCtx decision-stability laws; likely ⚑ `DetectAtThr` named law.
     hard-fable, ~70 ln.
KE7  X2BridgeP clause 2 (the a.e. clause) given clause 1 + null legs
     (discZero null = XF10 PROVED; nsFibers null = KE1; InfTree null = the
     route's own (a) leg — check XG3's exact form). deps: KE6, KE1.
     routine-opus given deps, ~40 ln.
KE8  [ATTEMPT] ALIGN-inc: the certified-increment transport (GMN Cor 4.19
     accounting through the T0-T5 index table, reading A). Consumes the
     declared GMN axiom (allowed; already trusted). deps: X1a table units
     (MovesX XA/XB built). hard-fable, ~90 ln; fallback: the per-row
     obstruction (which table row's transport fails).
KE9  [ATTEMPT, lowest priority] X2ProgressP linear — only if KE2+KE3 land
     with room; the per-move mass-pricing idea. hard-fable; explicitly
     deferrable (X.3 does not consume it). ~100 ln.
KE10 the sharpening audit: a record unit tabulating, per X-kernel Prop,
     which n=3-sealed layer now has a general-n theorem (KD/KE outputs) vs
     a named obstruction — the area's exit report, feeds the CL ledger.
     deps: all. routine-opus, record-only.

DEPENDENCY SPINE (what unblocks what): KA1→KA5→(KA6b) and KA4a→KA4b→KA4c are
independent chains; KB2-KB7 fan into KB8; KC3+KC4 before KC5; KD2→KD3→KD5;
KE1 independent (highest value/effort ratio of the whole area); KE6→KE7.
Nothing in this area blocks any other bridge-campaign area; consumers pull
through the named Props only.

--------------------------------------------------------------------------------
## 5. RISKS — statements that could be FALSE as sketched (each with its
countermodel-attempt unit, which runs BEFORE the prover)

R1. **KA6b (exit-cell survival) may be FALSE at some wild pool.** The probes
    themselves show cells DIE at p = 2 (six dead cells); the claim is only
    that SOME exit cell survives per state. If an anchored state's window
    pins every residual coefficient that controls squarefreeness, a pool
    could kill all exits. CM unit: KA6a (adversarial synthetic-table +
    real-menu search at q₀ ∈ {2,3,4,8,9}). A finding does NOT refute E0
    itself (the class-level escape can survive per-state failure) — it
    reroutes to the class-level form through KA2c.
R2. **KA2c without substochasticity is FALSE** ([[2]]-type witnesses) and
    **without reachability is FALSE** ([[1]]). CM unit: KA2d (compiled).
    Guards the abstract layer against silent hypothesis drop.
R3. **KB5 (weight exactness) hides the one real cancellation risk**: all
    slot summands share weight W, so exactness rests entirely on the
    leading-form read being τ ≠ 0. If the read map has cross-slot
    interference the model breaks. CM check: KB10's corrupted-slot negative
    control (probe NC1/NC2 transcribed) — it must FAIL for the corrupted
    formula and PASS for offP; if interference appears, the obstruction
    record pins the two slots and the enumeration is re-examined for the
    same interference (it passed 40,378 cases, so a Lean-side failure most
    likely means a transcription bug, not a math one — adjudicate before
    concluding either way).
R4. **KC2b (DomProj derivable) is probably FALSE as a derivation** — dom is
    free data in XHDd. CM unit: KC2a. Expected outcome: DomProj becomes a
    ⚑ named law; that outcome is a deliverable, not a failure.
R5. **KC5's reduction could be vacuous** if DomProj ∧ MarkCompose is
    UNSATISFIABLE at every census-coupled instance while HMC's real content
    lives elsewhere. Guard: KC4 (MarkCompose fails at the toy — so the pair
    is not True-everywhere) + KC6's Order0Sys instance (the pair HOLDS at
    the V1 witness — so it is not False-everywhere). Both checks are in
    the unit list; the reduction ships only with both.
R6. **KD2 (REC-DISC) could be FALSE** if some recentering occurs above an
    unramified root read (no repeated factor). CM unit: KD1's REC-DISC
    probe leg (exhaustive p = 2 boxes: any f with a recentering and
    vdisc = 0 refutes). The classifier-side sketch says impossible (a
    continuing track needs multiplicity ≥ 2 — the same (c2)/(R) content as
    KB13); the probe makes it an empirical gate first.
R7. **KD3's s := L(n) reduction changes the CONSTANT's meaning** (the note's
    s(n) is a charge factor, L(n) a restart cap). The Lean Props only need
    SOME s — `XConsts.s` is existential data — so no statement fence issue,
    but the CL-2 record line should note the discharge route (⚑ Q5).
R8. **KE5 (tails) may be FALSE with any fixed (C_T, c_T)** if per-depth
    branching outruns per-height decay — the known divergence risk. CM
    unit: KE4 (candidate refuter). The existential form (∃ constants) is
    what X2TailsP states; KE4 refutes candidates only.
R9. **HMC itself may be FALSE at the real table** (the note's wall channel
    is the designed escape). NOTHING in KC asserts HMC unconditionally;
    every KC output is a reduction, a perimeter theorem, or an instance
    check. Any unit found asserting bare HMC is a blueprint violation —
    reject at audit.
R10. **KA4c's drain embedding may need CL-5's identification** (the nine
    inputs) in a form no corpus yet types. Fallback pre-declared: the named
    identification hypothesis. Do not let a prover improvise the
    identification — that is the vacuity genre the campaign's round-1
    audits killed.

--------------------------------------------------------------------------------
## 6. ORCHESTRATOR QUESTIONS (decisions this blueprint cannot make)

Q1. **Namespace/placement for the new mini-corpus.** Proposed
    `lean/LeanUrat/Kernels/` (E0Matrix, E0Route, D4R0K/, HmcReduction,
    WeightChargeRed) — additive, imported by nothing until seam units land.
    Alternative: fold each into its consumer corpus (MovesS/MovesX/MovesV).
    Placement affects the AxChk sweep list (methodology rule #1: enumerated
    out-of-root-graph builds) — needs your call + a lakefile/AxChk entry.
Q2. **KB target form: enumeration model vs HC-1 carriers.** The blueprint
    proves L1 over the transcribed l1_boundary_enum model (self-contained,
    convention-scoped per the script's own fence) with a separate ⚑ seam
    unit to HC-1's (S6b) vocabulary. Ratify this two-step architecture, or
    demand L1 directly over HC-1 carriers (costlier, blocks on HC-1's
    Phase-B state)?
Q3. **N3 carriers.** KA7/KC8 (n=3 pool + HMC layers) need an N3 analogue of
    the N2* instantiation corpus. Building it is instantiation-area work
    (~30+ units by the N2 precedent). In this area's scope, that area's, or
    deferred?
Q4. **Named-law ratifications (statement fence):** DomProj, MarkCompose
    (KC2/KC3 — hypotheses of reduction theorems, NOT new XHDd fields),
    `RecImpliesWild` (KD2 fallback), `KeyWeightData` (KD6), `DetectAtThr`
    (KE6), `ThresholdStep` (KE2), the KA4a interface fields. Each lands as
    an explicit hypothesis/carrier, never a field on a ratified structure —
    confirm this is the sanctioned shape, and whether each needs its own
    Codex confirm or one batched pass.
Q5. **CL-ledger annotations.** KD3 discharges CL-2's route through CL-7's
    TRACK-COUNT face (s := L). Does the capstone ledger / the note's CL-2
    record line get an annotation now (touches the cross-note authority),
    or only at discharge time?
Q6. **Probe units in the unit economy.** KA6a/KD1/KE4 are python probe
    units (verification/, seal-record deliverables, no Lean). Confirm they
    count as campaign units with the same verify discipline (sealed
    predictions BEFORE runs, exit codes recorded in probe_results), and
    that Lean transcription is demanded only for FINDINGS (witnesses).
Q7. **The E5 fenced sorry.** KB12+KB13 aim at the CANONICAL-instance
    discharge of hD4R0K's (U)∧(R). The fenced sorry itself sits at the
    abstract interface under the full CellAssign premise row (owner
    HC-2/D4R0K, fence-rule record 2026-08-01). Touching it requires your
    adjudication of the instance-vs-interface discharge route — flag now so
    the adjudication is queued, not improvised by a prover.
Q8. **Priority ordering under a bounded fleet.** Recommended: KE1 (paper
    proof exists) → KD2/KD3 (the reduction, small) → KA1-KA5+KC1-KC5 (the
    abstract layers) → KB1-KB10 (the induction) → the [ATTEMPT] heads
    (KA6b, KD6/KD7, KE2/KE3/KE5/KE8) each behind its CM twin. Confirm or
    reorder against the other areas' pull.

--------------------------------------------------------------------------------
END BRIDGE_BP4_KERNELS. Unit count 53 (13 KA / 13 KB / 9 KC / 8 KD / 10 KE);
hardest heads: KA6b, KA2b, KB8, KB5, KC6, KD7, KE1, KE2, KE5, KE8.
