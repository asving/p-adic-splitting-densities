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
        fenced sorry in `MovesT/E5_rootSplit.lean:343` (owner HC-2/D4R0K;
        being hoisted to the named `TrackUniqOn`/`TrackRepOn` hypotheses by
        BP3 TV-A1..A5 — see the §3.B consumer edge, REV 2 F8), the
        `treeN_stable` row (E11), and the HC-1/HC-2 D4R0K owner rows.
  (G-C) **HMC.** `MovesV.HMC TE D` (Defs.lean:1180) — the exact-domain stepwise
        factorization. Known machine facts: ¬HMC at a carrier-level toy
        (`hmc_false_witness`, V4_hmc.lean:369), `hmcaug_of_hmc`
        (V4_hmcaug.lean:215), the n=2 scalar instance `n2_hmc` (N2Hmc.lean).
        Deliverable shape: HMC split into two NAMED directional laws
        (DomProj + MarkCompose, §3.C — a naming + instance-check package,
        definitional as an implication; REV 2, F9), plus
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
| `Kernels/E0Route.lean`: `blockMass` def + `BlockDrain` + the ROUTE-E0 theorem (REV 2, F7) | same | the typed measure route |
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
        Key identity (REV 2, F6 — the old "min positive entry" is undefined
        at A = 0, which satisfies the hypotheses: every row already strictly
        deficient): per state i take the reachability witness path
        i = i₀ → i₁ → … → i_ℓ (ℓ ≤ m := card ι; entries along the path > 0
        by definition of reachability; row i_ℓ strictly deficient); set
        ε_i := (Π_j A(i_j, i_{j+1})) · (1 − Σ_β A(i_ℓ, β)) > 0 (empty
        product = 1 covers ℓ = 0, hence also A = 0); ε := min_i ε_i over
        the finite state set. Peeling the path one factor per step, with
        substochastic padding on the remaining m − ℓ steps, gives every
        entry of A^m𝟙 ≤ 1 − ε; monotonicity of k ↦ A^k𝟙 (substochasticity)
        interpolates: A^k𝟙 ≤ (1−ε)^⌊k/m⌋𝟙 → 0.
  (1c)  [converse, the refuter's soundness] a closed class C (every row of C
        sums to 1 within C) forces (A^k𝟙)|_C = 𝟙 — ¬escape. This makes
        escape_probe_a's layer-1 criterion a THEOREM, not just a script.
  (1d)  [the open leg] per-state exit positivity at the REAL table: at every
        pool q₀ and every realized active state τ, the one-step exit mass
        (terminal + split) is > 0 — equivalently row sum < 1. WILD SUBTLETY:
        cell-count polynomials DO die at small pools (p = 2 kills six cells,
        probe §2), so the argument must exhibit an exit cell that SURVIVES
        every q₀ ≥ 2. Candidate (REV 2, F2 — the old single-case sketch
        "some digit choice yields a squarefree residual" is FALSE at
        anchored states): case-split on the state's anchor pin a (anchored
        strata pin a z^a factor of the residual; the window digits
        parameterize only the FREE coefficients away from the anchor):
        · a = 0: some free-digit choice makes the residual SQUAREFREE
          (squarefree monics of degree e over F_q number q^e − q^{e−1} > 0
          for e ≥ 2, q ≥ 2; degree-1 residuals are separable outright); a
          squarefree residual at an e_read = 1 read is a hen/terminal exit.
        · a = 1: target residual z·(squarefree cofactor with z ∤ cofactor)
          — still squarefree; same counting one degree down.
        · a ≥ 2: NO residual is squarefree — z² divides every one,
          REGARDLESS of the free coefficients (compiled arithmetic, not a
          probe question). The sketched universal is dead here; the exit,
          if any, must come from a DIFFERENT mechanism: either the anchored
          read's own terminal/split criterion on the COFACTOR (separable
          cofactor coprime to z — whether the real table grants that read
          an exit is exactly the open question), or the per-state form
          FAILS at these states and the class-level route (KA2c: the
          anchored state reaches a deficit state in ≥ 1 steps) takes over.
          KA6a's probe searches a ≥ 2 anchored states FIRST.
        If the free coefficients cannot force the target at some (state,
        pool), the fallback record documents the exact window-to-residual
        map and the pinned coefficient set.

ROUTE 2 (measure — the note's own ROUTE E0, MOVES 12179-96), TYPED (REV 2,
  F7 — the old sketch left the codomain undecided, law_step elided, and the
  tie's coercions unstated; that was not yet an interface): NO record at the
  abstract layer. Instead a DEF with ONE coercion point,

      blockMass (A : Matrix ι ι ℚ) (k : ℕ) (τ : ι) : ℝ :=
        ((A ^ k *ᵥ (fun _ => (1 : ℚ))) τ : ℝ)

  with LEMMAS (not fields): blockMass_zero : blockMass A 0 τ = 1;
  blockMass_step : blockMass A (k+1) τ = Σ_β (A τ β : ℝ) · blockMass A k β
  (by pow_succ/mulVec unfolding); blockMass_antitone under nonneg +
  substochastic. Then `BlockDrain A : Prop := ∀ τ, ⨅ k, blockMass A k τ = 0`
  (ℝ-valued ciInf of a bounded-below sequence — well-posed; ℚ has no such
  infima, which forced the codomain decision). BlockDrain is the X.3
  consumer — CL-4. Antitone + bounded below + inf 0 ⟹ Tendsto 0 in ℝ
  (`tendsto_atTop_ciInf`); the ℚ-valued EscapeE0.escape follows since
  `Rat.cast : ℚ → ℝ` is inducing. The SEMANTIC identification (blockMass =
  the still-in-block-after-k normalized conditional mass) is NOT a field
  anywhere — it is KA4c's seam statement against XCtx. Monotone convergence
  over a FINITE index is elementary — no measure theory beyond this.
  This route makes E0's X.3-conditionality a machine-checked implication:
  X.3 ⟹ E0 at the identified kernel (per pool, transported per [2r] at δ>1).

ROUTE 3 (pool closure at n ≤ 3): decide/norm_num packages `PoolHyp` at the
  sealed pools for the real n=3 carriers, MIRRORING N2Pool/N2Pools —
  DEFERRED (REV 2, F11: the Q3 adjudication rules "N3 carriers DEFERRED";
  KA7/KC8 leave the campaign graph; this route is not advertised this
  campaign).

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
           because the slots are pairwise-distinct Φ-adic POSITIONS: k ↦
           j₀+ek is INJECTIVE, while every slot lies in the SAME class j₀
           mod e (REV 2, F1 — the old justification "slots are distinct
           mod e" was arithmetically FALSE: j₀+ek ≡ j₀ mod e for all k;
           the independent reader CHECKS single-class membership,
           l1_boundary_enum.py:227). Noninterference is positional: each
           summand occupies its own development position (degree
           invariant: per-digit degree < deg Φ_prev, so no slot overflows
           into a neighbor — an explicit induction obligation, carried by
           KB8a), and addition never mixes distinct positions; hence
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
no CONTINUING child exists on that track. CONSUMER EDGE (REV 2, F8 — the old
"KB12+KB13 discharge the E5 sorry at the canonical instance" was a consumer
mismatch: the sorry is an ABSTRACT (U)∧(R) row and no canonical→abstract
implication exists or is planned): BP3's unit TV-A1 hoists the E5 pair into
the NAMED hypotheses `TrackUniqOn`/`TrackRepOn` (owner HC-2/D4R0K),
∀-quantified at the abstract carriers. KB12/KB13 attempt those Props'
CANONICAL-INSTANCE legs — the shape BP1's per-prime `UInstance` construction
consumes — and claim NO discharge of the abstract premise. The
instance-vs-interface bridge is the QUEUED Q7 adjudication; unit KB15
(statement-only, blocked on Q7) reserves it.

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
  (MarkCompose) DEFINED as the bare typed implication Mem h₁ ∧ Mem h₂ →
                Mem (Hpt.append h₁ h₂), the retained-state matching carried
                by the TYPING of the append (V4 cast toolkit). REV 2, F9:
                the blueprint previously mixed this with a STRUCTURAL
                reading ("per-step realized marks compose"); that version
                would need a new marks-object vocabulary (statement-fence
                ratification territory) plus a marks-to-Mem translation
                theorem. The bare implication is the chosen definition; the
                structural reading is demoted to motivation. It NAMES
                exactly the "marks compose" gap. [CM-first]: MUST fail at
                the census toy (else the toy would satisfy HMC) — the
                compiled failure witness is the sharpened obstruction record.

  THEOREM (the reduction): DomProj ∧ MarkCompose ⟹ HMC — honest status
  (REV 2, F9): with the bare-implication definitions this is DEFINITIONAL
  ASSEMBLY (Iff.intro of the two named directions), not a depth reduction.
  Its value is (i) the NAMING of the two directions as separately
  attackable laws, (ii) the typing (retained-state matching + Hpt append
  via the V4 cast-lemma toolkit), and (iii) the instance checks that give
  the pair content — KC4 (MarkCompose FAILS at the toy) and KC6 (both laws
  HOLD at Order0Sys). No marks-composition depth is claimed.

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

  The implication WEIGHT-CHARGE ⇐ TRACK-COUNT + (REC-DISC) is KD3 — sound
  as stated. BUT (REV 2, F3 — the old text advertised the ladder/budget
  attempt as TRACK-COUNT's route, which is arithmetically unsupported) the
  two targets must be kept apart:

    (T-const) `track_restarts`'s CONSTANT L(n) — p/N/depth-uniform (the
              ledger's binder order enforces the uniformity). Its ONLY
              current support is the finite 15/15 probe. The ladder route
              CANNOT deliver it: KD6 gives #recenterings ≤ D(n)·(w_final −
              w_init) and KD7 targets w_final ≤ c(n)·(1 + vdisc f); their
              composition GROWS with vdisc f — a fixed-degree family of
              increasing discriminant depth with successive recentering/
              refinement steps is the obvious stress family. (T-const)
              stays an OPEN kernel with its own CM-first stress leg (KD1,
              extended); NO prover is assigned to it in this campaign, and
              its plausibility downgrade is ESCALATED (cross-area: BP1
              owns the Cl7Kernel ledger row).
    (T-disc)  the WeightCharge SHAPE ≤ s(n)·vdisc f — deliverable WITHOUT
              (T-const): ladder (KD6) + cap (KD7) + (REC-DISC) compose
              DIRECTLY to WeightChargeFullP with s := 2·D(n)·c(n): on a
              history with ≥ 1 recentering, vdisc ≥ 1 (KD2), so
              D·c·(1 + vdisc) ≤ 2·D·c·vdisc; zero-recentering histories
              give count 0. This is the NEW unit KD10 — the schedulable
              route to the cl2_route face, never needing a constant
              restart cap.

  Attempt material for KD6/KD7 themselves: the strict weight climb per
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
## 4. UNIT SPLIT (REV 2: 64 schedulable units — KA 15 · KB 18 · KC 8 ·
## KD 10 · KE 13 — plus 2 DEFERRED by the Q3 adjudication: KA7, KC8.
## The pre-revision header claimed 53; the true pre-revision count was 55 — F12.)

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
     (A^m *ᵥ 𝟙) i ≤ 1 − ε. deps: KA2a. Sketch (REV 2, F6 — the old "min
     positive entry" is undefined at A = 0, which satisfies the
     hypotheses): per state i, ε_i := (product of the reachability-witness
     path's entries) · (deficit at the path's end) > 0 (empty product = 1
     covers path length 0, hence A = 0); ε := finite min over states; peel
     the path one factor per step, substochastic padding on the remaining
     m − ℓ steps. hard-fable, ~80 ln (split further if it grows).
KA2c `escapeE0_of_noClosedClass` : nonneg + substochastic + reachability
     hypothesis ⟹ EscapeE0. deps: KA2d (CM gate — SEQUENCED FIRST, REV 2
     F5), KA1, KA2a, KA2b. Sketch: A^{km}𝟙 ≤ (1−ε)^k 𝟙 by KA2b +
     induction; interpolate by KA2a antitonicity. routine-opus given deps,
     ~40 ln.
KA2d [CM-first twin of KA2c — runs BEFORE the KA2c prover] compiled
     witnesses that BOTH hypotheses are needed. REV 2, F4 — the old [[2]]
     witness FAILED its own premises: its single row sums to 2, so no
     strict-deficit row exists and the reachability hypothesis is violated
     rather than retained. Corrected pair:
     · drop substochasticity, keep reachability: A = !![0, 2; 1/2, 0] (ℚ):
       nonneg; row 1 sums to 1/2 (strict deficit) and is reachable from
       row 0 in one step (entry 2 > 0); NOT substochastic (row 0 sums to
       2); A^2 = 1, so A^{2k}𝟙 = 𝟙 ↛ 0 — no escape.
     · drop reachability, keep substochasticity: A = [[1]]: nonneg,
       substochastic, the single class is closed (no strict-deficit row
       exists to reach); A^k𝟙 = 𝟙 — no escape.
     deps: —. routine-opus, ~35 ln.
KA3  `noEscape_of_closedClass` (the refuter's soundness): C ⊆ ι nonempty,
     ∀ i ∈ C, ∑_{j∈C} A i j = 1 ∧ ∀ j ∉ C, A i j = 0 ⟹ ¬ EscapeE0 A.
     deps: KA2a. Sketch: (A^k𝟙)|_C = 1 by induction; Tendsto to 0 fails.
     routine-opus, ~35 ln. (Makes escape_probe_a layer 1 a theorem.)
KA4a `blockMass` def + `BlockDrain` Prop (E0Route.lean) — REV 2, F7: the
     old sketch (record with codomain "ℝ≥0∞ (or ℚ≥0)", elided law_step,
     coercion-free tie) was not yet a typed interface. Now fully decided:
     `blockMass (A : Matrix ι ι ℚ) (k : ℕ) (τ : ι) : ℝ :=
     ((A ^ k *ᵥ (fun _ => (1:ℚ))) τ : ℝ)` — a DEF (the tie is definitional,
     the single ℚ→ℝ coercion sits here); LEMMAS blockMass_zero (= 1),
     blockMass_step (= Σ_β (A τ β : ℝ) · blockMass A k β, by pow_succ),
     blockMass_antitone (under nonneg + substochastic).
     `BlockDrain A : Prop := ∀ τ, ⨅ k, blockMass A k τ = 0` (ℝ ciInf —
     ℚ has no such infima, forcing the codomain choice). NON-VACUITY: a
     decide/norm_num instance at the N2 pool. deps: —. routine-opus,
     ~55 ln. ⚑ interface — orchestrator ratifies the def + Prop shape
     before provers run.
KA4b `escape_of_drain` : nonneg + substochastic + BlockDrain A → EscapeE0 A.
     deps: KA4a. Sketch: per-τ blockMass antitone bounded below with inf 0
     ⟹ Tendsto 0 in ℝ (`tendsto_atTop_ciInf`); pull the limit back along
     the inducing `Rat.cast` to EscapeE0's ℚ-valued statement; finite
     index ⟹ Pi.tendsto. routine-opus, ~35 ln.
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
KA6a [CM-first for KA6b2] the exit-cell survival probe (python,
     verification/): for synthetic (K-SUB)-shaped tables at q₀ ∈ {2,3,4,8,9}
     and states with anchored windows, search for a (state, pool) whose
     EVERY exit cell dies (cell count 0 at q₀). SEARCH ORDER (REV 2, F2):
     a ≥ 2 anchored states FIRST — there the squarefree-residual mechanism
     is provably ABSENT (z² divides every residual), so survival must come
     from a different exit; that zone is likeliest to refute the per-state
     form. A finding refutes the per-state form of E0's escape and reroutes
     KA6b2 to the class-level statement. deps: —. routine-opus (script +
     seal record), no Lean.
KA6b1 [NEW id at REV 2 — F2/F13 split of the retired KA6b] the finite-field
     counting layer (pure F_q[z], no table seam): squarefree monics of
     degree e over F_q number q^e − q^{e−1} > 0 (e ≥ 2, q ≥ 2); degree-1
     monics separable; z·(squarefree cofactor coprime to z) is squarefree;
     PLUS the compiled impossibility lemma: for a ≥ 2, z^a·c is NEVER
     squarefree — the F2 fact, stated positively so no prover re-attempts
     the dead route. deps: —. routine-opus, ~50 ln.
KA6b2 [ATTEMPT; NEW id at REV 2 — the window/table seam, THE OPEN CORE of
     E0, restated per §3.A (1d)'s case split (the old KA6b universal "some
     digit choice yields a squarefree residual" is FALSE at a ≥ 2 anchors —
     F2)]: at every realized active state with anchor pin a ≤ 1 and every
     pool q₀ ≥ 2, some FREE window digit choice yields a squarefree
     residual (⟹ terminal exit; row sum < 1 via KA5); at a ≥ 2 states,
     exhibit the cofactor-criterion exit or REROUTE to the class-level
     escape (KA2c reachability from anchored states) — whichever KA6a's
     anchored-first findings support. deps: KA6a (CM gate — runs FIRST),
     KA6b1; carriers: the §M-SPECIES menu (MovesSp) or a self-contained
     window model (⚑ Q1). hard-fable; fallback: the obstruction record
     pinning the window-to-residual coefficient map and which (state,
     pool) resists. ~90 ln.
KA7  [DEFERRED — Q3 ADJUDICATED 2026-07-30: "N3 carriers DEFERRED" (REV 2,
     F11). Out of the campaign unit graph; id reserved; ROUTE 3 of §3.A is
     deferred with it and is NOT an advertised E0 route this campaign.]
     n=3 pool closure: `PoolHyp` instances at q₀ ∈ {2,3,4} for the real n=3
     carriers by norm_num/decide, mirroring N2Pool (values sealed: κ₂, κ₃,
     dets at probe §1). deps: N3 carriers (deferred).
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

KB1a [REV 2 — F13 split of the retired KB1 (it bundled records + field
     towers + arithmetic + an instance into one "small unit")] the
     `StageData`/`TowerData` records + arithmetic invariants only:
     per-stage (e, h, g, ψ-as-data) with gcd(e,h)=1 and the (I-aug) chain
     h_i > e_i·(e_{i−1}h_{i−1}g_{i−1}) as fields. deps: —. routine-opus
     (design care), ~40 ln. ⚑ interface ratification.
KB1b the residue-field carrier: F_i as iterated AdjoinRoot OR the
     enumeration's tuple model (per the Q2 adjudication: prove over the
     TRANSCRIBED ENUM MODEL — so the tuple model is the default; AdjoinRoot
     only if the seam unit KB11 demands it); ψ monic irreducible deg g,
     ψ(0) ≠ 0 as carrier laws. deps: KB1a. routine-opus, ~40 ln.
KB1c NON-VACUITY gate: the p=2 stage-3 instance from the probe grid, by
     decide, against KB1a+KB1b. deps: KB1a, KB1b. routine-opus, ~25 ln.
KB2  slot arithmetic: `j0` def (h⁻¹W mod e via ZMod e units), slots ≤ eg−1,
     e ∣ W − (j₀+ek)h, u_k := (W−(j₀+ek)h)/e ∈ ℕ with e·u_k + (j₀+ek)h = W.
     deps: KB1a. Sketch: ZMod.unitOfCoprime + omega. routine-opus, ~40 ln.
KB3  the guard chain: W > ehg ⟹ ∀ k < g, u_k > threshold one stage down
     (the two-line (I-aug) inequality, MOVES 2450-2455). deps: KB1a, KB2.
     Sketch: e·u_k ≥ W − (eg−1)h > ehg − (eg−1)h = h; then (I-aug):
     h > e·(prev threshold). All in ℕ with the e-divisibility from KB2 —
     avoid rational division. routine-opus, ~35 ln.
KB4  weight of a slot summand: w(t_k·Φ^{j₀+ek}) = e·w(t_k) + (j₀+ek)h at
     exact-weight t_k — the parent-scale weight law of the development.
     deps: KB1a-b (the model's `wt` def). routine-opus, ~30 ln.
KB5  leading-form nonvanishing (REV 2, F1 — the old justification "distinct
     slot classes mod e ⟹ no cross-slot interference" was arithmetically
     FALSE: every slot j₀+ek ≡ j₀ mod e): the sum over slots of prescribed
     leading scalars reads to z^m·P(z̄) = τ ≠ 0. TRUE mechanism: k ↦ j₀+ek
     is INJECTIVE, so the slots are pairwise-distinct Φ-adic POSITIONS all
     lying in the single class j₀ mod e (the independent reader's own
     check, l1_boundary_enum.py:227); with the degree invariant (each
     summand's digit degree < deg Φ_prev — KB8a's obligation, no positional
     overflow) addition never mixes positions, so coefficientwise the sum
     IS its summands: per-position weight = W, hence w(t) = W EXACTLY (min
     attained, no cancellation at weight W) and the k-th read recovers P_k.
     deps: KB2, KB4, KB10 (negative-control gate — SEQUENCED BEFORE this
     prover, REV 2 F5). hard-fable (positional bookkeeping + the degree
     invariant — the one genuinely delicate stage lemma), ~80 ln;
     pre-approved split: KB5a (min ≥ W), KB5b (read = τ ⟹ = W).
KB6  the class map: τ ↦ P (unique deg < g representative with z̄^m·P = τ),
     bijectivity onto F′^× including anchored τ = z̄^a·u. deps: KB1a-b.
     Sketch: representative uniqueness in the carrier model; z̄ invertible
     since ψ(0) ≠ 0. routine-opus, ~40 ln.
KB7  base case: stage-1 realizers — every c ∈ F_Q^× at every weight, unit
     lift, exact weight, deterministic. deps: KB1a-b. routine-opus, ~30 ln.
KB8a [REV 2 — F13 split of the retired KB8 (recursive construction +
     eligibility + weight + read + uniqueness was a mini-development)]
     `offP` construction + eligibility + DEGREE INVARIANT: the recursive
     def offP r W τ (a def, not a choice — determinism is free); every
     recursive call eligible (guard by KB3, slots in range by KB2); the
     invariant "every stage-r realizer's Φ-adic digits occupy only the
     designated slots, per-digit degree < deg Φ_prev" (KB5's
     noninterference input — REV 2, F1). deps: KB1a-c, KB2, KB3.
     hard-fable, ~60 ln.
KB8b `l1_totality` — THE INDUCTION: ∀ stage r, ∀ W > thr_r, ∀ τ ∈ F_r^×,
     wt (offP r W τ) = W ∧ digRead (offP r W τ) = τ, plus coverage
     (surjectivity onto F_r^× via KB6). deps: KB8a, KB4, KB5, KB6, KB7.
     Sketch: strong induction on r; exactness + read assembled by KB5 +
     KB6. hard-fable (the assembly), ~70 ln; pre-approved further split:
     exactness leg / read leg (split NOW in the plan, not at stall —
     REV 2, F13).
KB9  determinism + boundary corollaries: offP is a def (function of node
     data); the enumerated boundary corners (min W, g = 1, |F′^×| = 1 at
     p = 2) fall out as instances — state them as decide checks against the
     probe's tallies (spot rows, not all 40,378). deps: KB8b. routine-opus,
     ~40 ln.
KB10 negative controls as theorems (the gate's teeth, probe §3) — GATE
     UNIT, sequenced BEFORE the KB5 prover (REV 2, F5: the old ordering
     listed the gate after its prover with no dependency): corrupted slot
     class j₀+1 leaves the zero class, transcribed AT THE SCRIPT'S OWN
     SCOPE e ≥ 2 (the script runs NC1 at (p,e,h,g) = (3,2,1,2); at e = 1
     every weight is zero-class mod 1 and the control is VACUOUS — REV 2,
     F1: state the e ≥ 2 hypothesis explicitly, never quantify over
     e = 1); (I-aug) violation trips the guard (NC3 verbatim). deps: KB2,
     KB3. routine-opus, ~40 ln.
KB11 [ADJUDICATION] the convention seam: the twist lemma — any slot-unit
     twist that is a function of node data induces a bijection of nonzero
     classes commuting with totality/weight/determinism (the script's
     CONVENTION paragraph, typed). Then the seam statement to HC-1's (S6b)
     vocabulary (Moves/DefsCore.lean thresholds). deps: KB8b; owner overlap
     HC-1. adjudication (Q2 ADJUDICATED 2026-07-30: prove over the
     transcribed enum model + seam unit — this two-step architecture is
     ratified; the seam target form still needs the ⚑ detail pass), ~60 ln.
KB12 [ATTEMPT] (U) at the canonical instance — the canonical-instance leg
     of BP3 TV-A1's named `TrackUniqOn` (REV 2, F8: the target Prop is
     TV-A1's, instantiated at the canonical carriers — NOT the E5 sorry):
     two realized root children on one track share side/digit data
     (functions of f) + the canonical lift (KB8a/b determinism) ⟹ equal.
     deps: KB14 (CM gate — runs FIRST, REV 2 F5), KB8b, MovesD.CanonPolicy
     vocabulary. hard-fable; fallback: the obstruction record naming the
     missing child-datum-is-function-of-f law. ~70 ln.
KB13 [ATTEMPT] (R) at the canonical instance — the canonical-instance leg
     of BP3 TV-A1's named `TrackRepOn` (the (c2) covering, MOVES
     7112-7119): a simple factor's read is hen-terminal, no continuing
     child. deps: KB14 (CM gate — runs FIRST), MovesD/MovesT root-read
     vocabulary. hard-fable; same fallback genre. ~70 ln. CONSUMER EDGE
     (REV 2, F8 — replaces the false "together discharge the E5 hD4R0K
     sorry"): KB12+KB13 deliver instance-shaped legs for BP1's per-prime
     `UInstance` rows and for whatever route the QUEUED Q7 adjudication
     ratifies; they do NOT discharge the abstract E5 premise (owner HC-2,
     hoisted to named hypotheses by BP3 TV-A1..A5) and no
     canonical→abstract implication is claimed or planned outside KB15.
KB14 [CM-first gate for KB12+KB13 — NEW at REV 2 (F5: risky universals had
     no prior countermodel unit)] the (U)/(R) countermodel probe (python,
     verification/): over the enum/census root reads, search for (i) two
     DISTINCT realized root children on one track at one root-cell point
     (refutes U) and (ii) a realized root child on a multiplicity-1 track
     (refutes R); plus the in-corpus witness attempt at the G1 CellData
     toys (expected blocked — the E5 fence record: child_cover fails on
     both toy carriers, no CellAssign instance exists; record either way).
     Sealed predictions before runs (Q6 discipline). deps: verification/.
     routine-opus, no Lean.
KB15 [ADJUDICATION — statement-only, BLOCKED on Q7; NEW at REV 2 (F8)] the
     instance-vs-interface bridge: once the queued Q7 adjudication rules,
     STATE (do not prove) the ratified bridge between the
     canonical-instance (U)/(R) legs and the abstract
     TrackUniqOn/TrackRepOn premise row. No prover may improvise this
     bridge; until Q7 lands, KB12/13's only advertised consumer is BP1's
     instance rows. deps: Q7 ruling. adjudication, statement-only.

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
KC3  `MarkCompose` def — the BARE TYPED IMPLICATION (REV 2, F9: of the two
     readings the old text mixed, this is the chosen one; the structural
     "marks object" reading would need new ratified vocabulary + a
     marks-to-Mem translation theorem, and is dropped to motivation):
     Mem h₁ ∧ Mem h₂ → Mem (Hpt.append h₁ h₂), the retained-state matching
     carried by the append TYPING (V4 cast toolkit: castHpt/append laws,
     MovesV/Defs.lean:1196-1219). deps: —. routine-opus (typing only),
     ~35 ln. ⚑ named-law ratification.
KC4  [CM-first twin] `markCompose_fails_at_toy` : ¬ MarkCompose HmcToy —
     REQUIRED (else the toy would satisfy HMC via KC5); the compiled
     witness IS the sharpened obstruction record of the kernel. deps: KC3.
     routine-opus (decide), ~30 ln.
KC5  `hmc_of_domProj_markCompose` : DomProj ∧ MarkCompose ⟹ HMC — honest
     status (REV 2, F9): with KC3's bare-implication definition this is
     DEFINITIONAL ASSEMBLY (Iff.intro of the two named directions), not a
     depth reduction; it SHIPS ONLY together with its content guards KC4
     (the pair fails at the toy) and KC6 (the pair holds at Order0Sys),
     per R5. deps: KC3, KC4 (CM gate — SEQUENCED FIRST), KC2b. routine-
     opus given the defs, ~30 ln.
KC6  `Order0Sys` predicate + `hmc_of_order0` : full-product step domains ⟹
     HMC (the provable perimeter). Instances: the V1 witness satisfies
     Order0Sys (re-derive witHMC through it); HmcToy does NOT (decide).
     deps: KC3-KC5 optional. hard-fable (predicate design), ~80 ln;
     pre-approved split: KC6a predicate + instances, KC6b the theorem.
KC7  consumer glue verify-only: (COMP-hΣ) + HMC ⟹ (COMP-Σ) — confirm the
     built V5-5 conditional consumes `HMC` verbatim and nothing stronger;
     record, no new proof expected. deps: MovesV V5 modules. routine-opus,
     ~15 ln or record-only.
KC8  [DEFERRED — Q3 ADJUDICATED 2026-07-30: "N3 carriers DEFERRED" (REV 2,
     F11). Out of the campaign unit graph; id reserved.] n=3 real-chain
     HMC layer (mirror n2_hmc): the block-level kstep power law at the
     n=3 carriers. deps: N3 carriers (deferred).

### KD — WEIGHT-CHARGE / X.1b (file Kernels/WeightChargeRed.lean; seams in MovesX)

KD1  [CM-first] the s(n)-candidate refuter (python): re-run + extend the
     STALL-probe (p = 2 cubic 2²⁴ box, quartic RS-conditioned cylinder) to
     the ratio #recenterings / vdisc; also probe REC-DISC: search for f
     with a recentering node and vdisc f = 0 — a finding REFUTES KD2.
     NEW LEG (REV 2, F3 — the (T-const) stress): tabulate #recT1 + #t4
     against vdisc depth on the same boxes; a growing trend along a
     fixed-degree increasing-vdisc family is evidence AGAINST the ledger's
     constant-L `track_restarts` face (a finite probe cannot refute the ∀,
     but the trend record feeds the escalated cross-area review; the
     15/15 seal alone cannot support a degree-only bound). deps:
     verification/ infra. routine-opus (script + seal), no Lean.
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
     routine-opus, ~30 ln. STATUS NOTE (REV 2, F3): sound as an
     IMPLICATION, but its constant-L premise has NO supported general
     route in this campaign — KD6/KD7 do NOT feed it (their composition
     grows with vdisc); the schedulable WeightCharge discharge is KD10.
KD4  `weightChargeT4_of_trackCount` : same with .t4 ≤ full count ≤ L.
     deps: KD3. routine-opus, ~15 ln. Same status note as KD3.
KD5  `x3aRoute_of_weightCharge_align` : WeightChargeFullP (via KD10's
     ladder-cap route, or KD3 if a constant bound ever lands) + X1aAlignP
     (inc state) ⟹ X3aRouteP (right disjunct). deps: KD10 (or KD3).
     routine-opus, ~20 ln. Discharges cl2_route's shape conditionally
     (REV 2, F3: re-pointed from the TRACK-COUNT-only route).
KD6  [ATTEMPT] the weight ladder (REV 2, F3 — no longer advertised as a
     TRACK-COUNT route; its honest conclusion is vdisc-relative): named
     `KeyWeightData` carrier (per-node key weight, strict climb per
     recentering — D.10 DERIVED content; lattice (1/D(n))ℤ — the dnLattice
     duty) ⟹ #recenterings ≤ D(n)·(w_final − w_init). deps: KD9 (CM gate —
     runs FIRST, REV 2 F5); carrier design ⚑. hard-fable, ~80 ln;
     fallback: the typed carrier + the ladder lemma alone (already
     useful — it converts the count into a weight-cap question).
KD7  [ATTEMPT] the weight cap via the different budget: w_final ≤ c(n)·
     (1 + vdisc f) through (P2)'s leaf-different term (L5fix Invariant-2).
     THE DEEP OPEN CORE of the cluster. deps: KD9 (CM gate — runs FIRST),
     KD6; L5fix vocabulary (LeanUrat/L5fix.lean). hard-fable; fallback:
     obstruction record naming the exact budget consumable that fails to
     be exhibited (the note's own "must be exhibited, not assumed", MOVES
     11166). ~100 ln if it goes.
KD8  assembly + fence audit: the (CD)-pinned reading check — every KD unit's
     d_cert consumption matches reading A (task 58's adjudication); record
     unit, verify-only. deps: KD2-KD5, KD10. routine-opus, record-only.
KD9  [CM-first gate for KD6+KD7 — NEW at REV 2 (F5)] the ladder/cap probe
     (python): on the KD1 boxes, (i) verify the strict key-weight climb
     per recentering empirically and search for a recentering with ZERO
     ladder gain (refutes KD6's ladder law as sketched); (ii) fit w_final
     against 1 + vdisc f and search for super-linear growth (refutes every
     constant c(n) candidate for KD7). Sealed predictions before runs (Q6
     discipline). deps: verification/. routine-opus, no Lean.
KD10 `weightChargeFull_of_ladderCap` — NEW at REV 2 (the F3 reroute):
     KeyWeightData ladder (KD6's conclusion) + weight cap (KD7's
     conclusion) + REC-DISC (KD2) ⟹ WeightChargeFullP with s :=
     2·D(n)·c(n). Sketch: on a history with ≥ 1 recentering, vdisc ≥ 1
     (KD2), so #rec ≤ D·(w_final − w_init) ≤ D·c·(1 + vdisc) ≤
     2·D·c·vdisc; zero-recentering histories give count 0 ≤ anything.
     deps: KD2, KD6, KD7. routine-opus given deps, ~35 ln. THE schedulable
     X.1b discharge route — never needs a constant restart cap.

### KE — X.3 general-n + exhaustion sharpening (files in MovesX + Kernels/)

KE1  NsNullP port (the paper-proved (ns-null)): the single-state
     admissible-Z argument (plan REV 15; four verifications on record) over
     the XCtx nsFiber vocabulary. deps: locating the paper proof text
     (MOVES (ns-null) closure record) + XCtx. hard-fable (port, not
     invention), ~90 ln; pre-approved split: KE1a (the single-state lemma),
     KE1b (fiber-null assembly).
KE2  [ATTEMPT] X2AffP: branch induction through D.11's per-move threshold
     form with scale product Π e_i ≤ n; candidate c₀ = n·C_move. deps:
     KE11 (CM gate — runs FIRST, REV 2 F5); XCtx.threshold laws (check
     which exist; if the per-move form is unbuilt, ⚑ a named
     `ThresholdStep` law). hard-fable, ~90 ln; fallback: obstruction
     record with the branch shape whose threshold outruns the affine
     bound.
KE3  [ATTEMPT] X2CapP: from TB-CAP's per-clause caps ((τ-hen) N_V = 1
     PROVED; (τ-irr) per-realized-cell). deps: KE11 (CM gate — runs
     FIRST); [3t] TB-CAP Lean surface (MovesT). hard-fable, ~70 ln; same
     fallback genre.
KE4  [CM-first, TWO-PHASE — REV 2, F10: X2TailsP is EXISTENTIAL in
     (C_T, c_T) (XConsts data), so NO finite probe refutes it, and a probe
     run before the prover knows no candidate constants; the honest gate
     shape is candidate-stress + divergence detection]. Phase 1 (BEFORE
     the KE5 prover): exhaustive tall-event masses at n = 3, p ∈ {2,3},
     h* ≤ 8; fit the empirical decay exponent; compute the EXPLICIT
     candidate pair the KE5 sketch implies (the D4R.2 pool-bound
     composition) and stress it; track mass·p^{c·h*} growth in h* as the
     divergence detector (R8). Phase 2 (AFTER KE5 drafts its constants,
     BEFORE acceptance): re-run against the prover's actual (C_T, c_T).
     deps: verification/ (phase 2 also: KE5 draft). routine-opus.
KE5  [ATTEMPT] X2TailsP: price the first height-≥h* read by D4R.2's pool
     bound; sum over prefixes with the species-menu branching factor.
     deps: KE4 phase 1 (gate); MovesD mass laws (D4R.1/D4R.2 built);
     acceptance gated on KE4 phase 2 (REV 2, F10). hard-fable, ~90 ln;
     fallback: the divergent-series obstruction record.
KE6  [ATTEMPT] X2BridgeP clause 1 (the set decomposition): Undec(N) ⊆
     discZero ∪ nsFibers ∪ InfTree ∪ {thr+cap > N leaf branch}. deps:
     KE12 (CM gate — runs FIRST, REV 2 F5); XCtx decision-stability laws;
     likely ⚑ `DetectAtThr` named law. hard-fable, ~70 ln.
KE7  X2BridgeP clause 2 (the a.e. clause) given clause 1 + null legs
     (discZero null = XF10 PROVED; nsFibers null = KE1; InfTree null = the
     route's own (a) leg — check XG3's exact form). deps: KE6, KE1.
     routine-opus given deps, ~40 ln.
KE8  [ATTEMPT] ALIGN-inc: the certified-increment transport (GMN Cor 4.19
     accounting through the T0-T5 index table, reading A). Consumes the
     declared GMN axiom (allowed; already trusted). deps: KE13 (CM gate —
     runs FIRST, REV 2 F5); X1a table units (MovesX XA/XB built).
     hard-fable, ~90 ln; fallback: the per-row obstruction (which table
     row's transport fails).
KE9  [ATTEMPT, lowest priority] X2ProgressP linear — only if KE2+KE3 land
     with room; the per-move mass-pricing idea. hard-fable; explicitly
     deferrable (X.3 does not consume it). ~100 ln.
KE10 the sharpening audit: a record unit tabulating, per X-kernel Prop,
     which n=3-sealed layer now has a general-n theorem (KD/KE outputs) vs
     a named obstruction — the area's exit report, feeds the CL ledger.
     deps: all. routine-opus, record-only.
KE11 [CM-first gate for KE2+KE3 — NEW at REV 2 (F5)] the affine-envelope
     probe (python): thresholds and caps vs 1 + Σ h_r across the n = 3
     (and n = 2) census; fit c₀/c_cap candidates; search for branch
     families whose threshold/cap outrun every affine candidate
     (X2AffP/X2CapP carry XConsts data like tails — the gate is
     candidate-stress + growth detection, not ∀-refutation). Sealed
     predictions before runs. deps: verification/. routine-opus, no Lean.
KE12 [CM-first gate for KE6 — NEW at REV 2 (F5)] the Undec-decomposition
     probe (python): enumerate Undec(N) members at the census and check
     the four-set cover clause-by-clause; a member outside the union
     REFUTES KE6's set decomposition outright (clause 1 is a genuine ∀ —
     finitely refutable, the strongest gate genre in this area). deps:
     verification/. routine-opus, no Lean.
KE13 [CM-first gate for KE8 — NEW at REV 2 (F5)] the ALIGN transport
     row-check probe (python): recompute the T0-T5 index-table increments
     on the census under reading A and check GMN Cor 4.19's accounting
     row-by-row; a violating row pins the failing transport row before
     any prover runs. deps: verification/. routine-opus, no Lean.

DEPENDENCY SPINE (what unblocks what; REV 2 — every [CM-first] gate is now
an explicit dependency of its prover and is SEQUENCED FIRST, per the binding
cross-area adjudication, F5): KA2d→KA2c; KA1→KA5 and KA4a→KA4b→KA4c are
independent chains; KA6a(gate)+KA6b1→KA6b2; KB1a-c/KB2-KB7 + KB10(gate) fan
into KB8a→KB8b; KB14(gate)→KB12/KB13 (→KB15 after the Q7 ruling);
KC2a(gate)→KC2b; KC3+KC4(gate)→KC5; KD1(gate)→KD2→KD3, KD9(gate)→KD6→KD7,
KD2+KD6+KD7→KD10→KD5; KE1 independent (highest value/effort ratio of the
whole area); KE11(gate)→KE2/KE3; KE4-phase-1(gate)→KE5(→KE4-phase-2 before
acceptance); KE12(gate)→KE6→KE7; KE13(gate)→KE8. DEFERRED (Q3): KA7, KC8.
Nothing in this area blocks any other bridge-campaign area; consumers pull
through the named Props only (KB12/13's consumers: BP1's per-prime
`UInstance` rows + the Q7-gated KB15 bridge; the abstract E5 row stays with
BP3 TV-A1..A5 / owner HC-2).

--------------------------------------------------------------------------------
## 5. RISKS — statements that could be FALSE as sketched (each with its
countermodel-attempt unit, which runs BEFORE the prover)

R1. **KA6b2 (exit-cell survival) may be FALSE at some wild pool — and at
    a ≥ 2 anchors the squarefree mechanism is provably ABSENT** (REV 2,
    F2: z² divides every anchored-a≥2 residual regardless of the free
    coefficients — compiled arithmetic, KA6b1's impossibility lemma; the
    pre-revision universal was false as sketched). The probes also show
    cells DIE at p = 2 (six dead cells); the claim is only that SOME exit
    survives per state. CM unit: KA6a (adversarial synthetic-table +
    real-menu search at q₀ ∈ {2,3,4,8,9}, a ≥ 2 anchored states FIRST). A
    finding does NOT refute E0 itself (the class-level escape can survive
    per-state failure) — it reroutes to the class-level form through KA2c.
R2. **KA2c without substochasticity is FALSE** (witness !![0,2;1/2,0]:
    reachability retained, A² = 1, no escape — REV 2, F4: the old [[2]]
    witness failed its own premises) and **without reachability is FALSE**
    ([[1]]). CM unit: KA2d (compiled, sequenced before KA2c).
    Guards the abstract layer against silent hypothesis drop.
R3. **KB5 (weight exactness) hides the one real risk — positional overflow,
    not class arithmetic** (REV 2, F1: all slots share the class j₀ mod e;
    the risk is a summand's digits overflowing its Φ-adic position, i.e.
    the degree invariant failing, or a transcription mismatch in the read
    map). CM check: KB10's corrupted-slot negative control (probe NC1
    transcribed at its own e ≥ 2 scope, + NC2/NC3) — it must FAIL for the
    corrupted formula and PASS for offP; if interference appears, the
    obstruction record pins the two positions and the enumeration is
    re-examined (it passed 40,378 cases, so a Lean-side failure most
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
    s(n) is a charge factor, L(n) a restart cap; KD10's s := 2·D(n)·c(n)
    is a third shape). The Lean Props only need SOME s — `XConsts.s` is
    existential data — so no statement fence issue, but the CL-2 record
    line should note the actual discharge route (Q5 ADJUDICATED: annotate
    at discharge).
R8. **KE5 (tails) may be FALSE with any fixed (C_T, c_T)** if per-depth
    branching outruns per-height decay — the known divergence risk. CM
    unit: KE4, TWO-PHASE (REV 2, F10): phase 1 stresses the sketch-implied
    candidates + detects divergence BEFORE the prover; phase 2 stresses
    the prover's actual constants before acceptance. No finite probe can
    refute the existential X2TailsP itself.
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
R11. **(NEW at REV 2, F3) The ledger's constant-L TRACK-COUNT face
    (`Cl7Kernel.track_restarts`) is plausibly FALSE** — a fixed-degree
    family with increasing discriminant depth and successive recentering/
    refinement steps is the natural stress family, and the only current
    support is the finite 15/15 probe. Handling: NO prover is assigned to
    (T-const) in this campaign; KD1's new stress leg probes it; the
    WeightCharge discharge is rerouted through KD10 (never needs the
    constant); the plausibility downgrade is ESCALATED cross-area (BP1
    owns the Cl7Kernel row of theoremU's hypothesis surface). No fence
    event: Cl7Kernel is hypothesis DATA — nothing is asserted in-corpus.

--------------------------------------------------------------------------------
## 6. ORCHESTRATOR QUESTIONS (decisions this blueprint cannot make)

STATUS AT REV 2 (2026-07-30): all eight were ADJUDICATED before the Codex
review (BRIDGE_ADJUDICATIONS_2026-07-30.md, BP4 block); the rulings now bind
the units above. Q1: Kernels/ mini-corpus RATIFIED + lakefile/AxChk sweep
entry MANDATORY. Q2: prove over the transcribed enum model + seam unit
(KB11 architecture ratified). Q3: N3 carriers DEFERRED (KA7/KC8 out of the
campaign graph — REV 2, F11). Q4: confirmed — hypothesis/carrier shape only,
never new fields on frozen structures. Q5: annotate at discharge. Q6: probe
units count as campaign units, seal discipline applies. Q7: the
instance-vs-interface adjudication is QUEUED (KB15 blocked on it). Q8:
priority order confirmed. The original questions are preserved below for
the record.

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
--------------------------------------------------------------------------------
## REVISION 2 (2026-07-30, post-Codex) — finding-by-finding disposition log

Codex adversarial review verdict REVISE (4 CRITICAL / 8 GAP / 1 NOTE);
findings at /tmp/bridge/reviews/findings_bp4.txt. Every finding was verified
against the repo sources before application (l1_boundary_enum.py,
MovesS/Defs.lean, MovesU/DefsLedger.lean, MovesV/Defs.lean,
MovesT/E5_rootSplit.lean, MovesX/Defs.lean, BRIDGE_BP3_TV §TV-A1). ALL 13
FINDINGS APPLIED; none rebutted. Dispositions:

F1  (CRITICAL, slot separation) APPLIED. Verified: slots j₀+ek are ALL
    ≡ j₀ mod e (the reader checks single-class membership,
    l1_boundary_enum.py:227) — the sketched "distinct mod e" justification
    was arithmetically false. Fixed L1-iv, KB5, R3 to the true mechanism:
    k ↦ j₀+ek injective ⟹ pairwise-distinct Φ-adic POSITIONS + the degree
    invariant (now an explicit KB8a obligation). KB10's NC1 transcription
    scoped to e ≥ 2 (the script's own scope; vacuous at e = 1 — the
    review's sub-point).
F2  (CRITICAL, anchored squarefree-exit) APPLIED. For a ≥ 2 anchor pins,
    z² divides every residual — no squarefree residual exists; the KA6b
    universal was false as sketched. §3.A (1d) rewritten as an a-indexed
    case split; KA6b retired, split into KA6b1 (counting layer + the
    compiled a ≥ 2 impossibility lemma) and KA6b2 (seam attempt, restated
    target, reroute option); KA6a search order now anchored-a≥2-first; R1
    updated.
F3  (CRITICAL, constant TRACK-COUNT) APPLIED. Verified `track_restarts`
    is a constant-L p-uniform bound (DefsLedger.lean:199-217); the KD6∘KD7
    composition gives D(n)·c(n)·(1 + vdisc) — grows with vdisc, cannot
    deliver it; the 15/15 probe is finite-only. §3.D rewritten to separate
    (T-const) (open, no prover assigned, KD1 stress leg added, risk R11)
    from (T-disc) (rerouted via NEW unit KD10: ladder + cap + REC-DISC ⟹
    WeightChargeFullP with s := 2·D(n)·c(n)); KD3/KD4 carry status notes
    (sound implications, unsupported premise); KD5 re-pointed. ESCALATED
    cross-area (BP1 owns the Cl7Kernel row).
F4  (CRITICAL, KA2d witness) APPLIED. Verified: [[2]]'s single row sums to
    2, so no strict-deficit row exists — the reachability premise fails
    rather than being retained. Replaced with A = !![0, 2; 1/2, 0] (ℚ):
    reachability holds, substochasticity fails, A² = 1 ⟹ A^{2k}𝟙 = 𝟙, no
    escape. [[1]] retained for the reachability leg. R2 updated.
F5  (GAP, CM-first ordering) APPLIED. KA2d now an explicit dependency of
    KA2c (sequenced first); KB10 now a dependency of KB5; NEW CM-gate
    units created for every previously ungated risky universal: KB14 (for
    KB12/KB13), KD9 (for KD6/KD7), KE11 (for KE2/KE3), KE12 (for KE6),
    KE13 (for KE8); KE4 reshaped (see F10). Dependency spine rewritten
    with gates explicit.
F6  (GAP, min-positive-entry at A = 0) APPLIED. KA2b's ε redefined as the
    per-state path-product · end-deficit (empty product = 1 covers path
    length 0 and A = 0); §3.A (1b) sketch rewritten to match.
F7  (GAP, KA4a not typed) APPLIED. Interface fully decided: `blockMass`
    is a DEF into ℝ with the single ℚ→ℝ coercion displayed; law_zero/
    law_step/antitone are lemmas (law_step now complete); the tie is
    definitional; `BlockDrain` is an ℝ-ciInf Prop (ℚ lacks the infima —
    the codomain decision is forced and recorded); KA4b restated with the
    cast-back step. §3.A ROUTE 2 rewritten to match.
F8  (GAP, E5 consumer mismatch) APPLIED. KB12/KB13 re-targeted to the
    canonical-instance legs of BP3 TV-A1's named `TrackUniqOn`/`TrackRepOn`
    (the sibling interface reconciliation); the false "discharge the E5
    sorry at the canonical instance" claim deleted; consumers = BP1's
    per-prime UInstance rows; NEW unit KB15 (statement-only, blocked on
    the queued Q7 adjudication) reserves the instance-vs-interface bridge.
    §3.B consumer paragraph rewritten.
F9  (GAP, MarkCompose ambiguity) APPLIED. MarkCompose DEFINED as the bare
    typed implication (structural reading demoted to motivation — it would
    need unratified vocabulary + a translation theorem); KC5 relabeled
    honest DEFINITIONAL ASSEMBLY shipping only with its KC4/KC6 content
    guards; §1 (G-C) and §3.C updated.
F10 (GAP, KE4 gate shape) APPLIED. KE4 reshaped TWO-PHASE: phase 1
    (pre-prover) candidate-stress on the sketch-implied constants +
    divergence detection; phase 2 (post-draft, pre-acceptance) re-run on
    the prover's actual constants; KE5 acceptance gated on phase 2; R8
    updated. Recorded: no finite probe refutes the existential.
F11 (GAP, N3 deferral) APPLIED. KA7 and KC8 marked DEFERRED per the Q3
    adjudication, out of the campaign graph (ids reserved); ROUTE 3
    marked deferred and removed from the advertised E0 routes; §6 status
    block records all eight adjudications.
F12 (GAP, unit count) APPLIED. Pre-revision true count was 55 (KA had 15
    addressable units), not the declared 53. Post-revision declared
    count: 64 schedulable + 2 deferred (see END line).
F13 (NOTE, oversized units) APPLIED. KB1 → KB1a/KB1b/KB1c (records /
    carrier / non-vacuity gate); KB8 → KB8a/KB8b (construction+eligibility
    +degree-invariant / the induction, with the further exactness-vs-read
    split pre-planned); KA6b → KA6b1/KA6b2 (counting layer / table seam) —
    splits made in the dependency plan now, not at stall.

ESCALATIONS (returned to the orchestrator, not decided here):
E-1 (from F3) The constant-L TRACK-COUNT face (`Cl7Kernel.track_restarts`,
    theoremU hypothesis surface, owner BP1) has NO supported general route
    in any blueprint and is plausibly false (fixed-degree increasing-vdisc
    stress family). BP4 reroutes WeightCharge through KD10 and probes
    (T-const) via KD1's stress leg; BP1/campaign messaging about the CL-7
    face needs an orchestrator decision. Not a fence event (hypothesis
    data; nothing asserted in-corpus).
E-2 (from F8) The queued Q7 adjudication should ALSO fix (i) that KB12/13
    target TV-A1's named Props at the canonical carriers (cross-blueprint
    interface now written into BP4) and (ii) the shape of the KB15 bridge;
    until it lands, KB12/13's only consumer edge is BP1's instance rows.

No new statement-fence events surfaced: every revision is blueprint-level;
the one new compiled lemma (KA6b1's a ≥ 2 impossibility) is additive; no
frozen Lean statement is touched; no adjudicated decision was found wrong.

--------------------------------------------------------------------------------
END BRIDGE_BP4_KERNELS (REV 2). Unit count 64 schedulable
(15 KA / 18 KB / 8 KC / 10 KD / 13 KE) + 2 DEFERRED (KA7, KC8 — Q3);
hardest heads: KA6b2, KA2b, KB8b, KB5, KC6, KD7, KE1, KE2, KE5, KE8.
