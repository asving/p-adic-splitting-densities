# BP_VI — Movement VI: INTEGRATION + THE CORPUS BRIDGE (+ the swarm's shared infrastructure)

Architect: BP_VI (Lean conversion swarm, level 1). Date: 2026-08-03 window.
Authority: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"AUTHORITY (Asvin,
2026-08-03): THE LEAN CONVERSION SWARM" (ground rules bind every unit below) +
§"AUTHORITY (Asvin, 2026-08-01): THE PROOF SCAFFOLD" (the target statement shape).
Math source of record: `docs/ROOT_ASSEMBLY_2026-08-02.md` at REVISION 5 — §1
(ROOT)/(ROOT-C), §2 Movement V Step 19, §3.1 rows (H1)–(H6).

## 0. Charge, scope, ground-rule compliance

This movement contributes NO new mathematics. It contributes:
(A) the swarm's SHARED hypothesis surface — `Scaffold/Hypotheses.lean`, the (ROOT-C)
rows (H1)–(H6) as one named structure every division keys against;
(B) the SPINE TARGET — the scaffold-form statement `RootC` (cylinder density +
level-k squeeze + R_τ evaluation, per the 2026-08-01 authority);
(C) the CORPUS BRIDGE — the map from the EXISTING `theoremU`/capstone vocabulary
(`LeanUrat.MovesU`) into the spine: `theoremU → RootC` transport, the
`BridgeInputs`/`mkUInstance` firing route, the D-SC slot-layer connection;
(D) the NUMERICS ANCHORS — the n = 2 verified instances re-fired in scaffold shape;
(E) the AxChk extension — the scaffold's own axiom census.

Ground-rule compliance, explicit:
* New modules ONLY under `lean/LeanUrat/Scaffold/`, namespace `LeanUrat.Scaffold`.
* NO existing file is edited by any unit here. In particular `AxChk_baseline.lean`
  is NOT touched: the census extension is a standalone `Scaffold/AxChk.lean` run by
  `lake env lean` (§1.5). Existing fenced statements untouched.
* Parked items 22–29 UNTOUCHED: every unit that would need the wave-D carrier
  population or the `BridgeInputs` final wiring is fenced into the FUTURE table
  (§1.6) and assigned to NO wave. The slot-layer connection (VI-B3/B4) is
  statement-layer application only — it names the sited D-SC definitions as the
  13 slot parameters; it wires no carrier.
* No new axioms; every [M] row enters as a NAMED hypothesis row (§1.1).
* Corpus reuse by import only (§3).

Sibling-blueprint interface: BP_I–BP_V (Movements I–V) are expected to key every
step-level statement that consumes a §3.1 row to the `RootHyps` FIELD NAMES below
(the division-interface contract, §1.1 end). Wave VI-0 therefore lands FIRST and
is announced to all division leads before their prover waves start.

---

## 1. STATEMENT LAYER (namespace `LeanUrat.Scaffold`)

### 1.1 `Scaffold/Hypotheses.lean` — the (ROOT-C) hypothesis surface [SHARED, wave VI-0]

Imports: `Mathlib` only (deliberately light — every division imports this file).

Design rule (the theoremU precedent, `MovesU/U10_theoremU.lean` round-2 CRITICAL 1
+ the wave-4-boundary record): a row whose owner vocabulary is ABSENT from the
built corpus stays a bare `Prop` — but as a NAMED, VISIBLE field, never a bundled
tag. At blueprint time ALL sixteen rows are bare `Prop` fields; the standing
upgrade path is FIELD REFINEMENT (bare `Prop` → typed `Prop` over built carriers)
executed as a REVISION of this file when a division lands the carrier, with the
math-revision sync duty (ledger ground rule) owned by BP_VI.

```lean
namespace LeanUrat.Scaffold

/-- **`RootHyps n` — the (ROOT-C) hypothesis rows (H1)–(H6), ROOT §3.1 verbatim.**
    THE swarm's shared hypothesis surface: every division statement that consumes
    a §3.1 [M] row takes `H : RootHyps n` and names the field. TRANSCRIPTION
    DEVICE at E-phase (the theoremU wave-4-boundary rule): all fields are bare
    `Prop`, True-instantiable (see `trivialRootHyps`) — the conditionality claim
    of record MUST list consumed fields as UNPINNED named assumptions until their
    typed carriers land. `n` is the degree key (phantom until fields are typed). -/
structure RootHyps (n : ℕ) where
  /-- (H1) = (GR-B) at OM orders ≥ 2: the anchored-march residue-structure package
      (frame tie + residual-dictionary march, FGMN Thm 4.2 model, properness
      proviso). Order ≤ 1 is PROVED (VERIFIED leaf #4, GD23). -/
  h1_grb      : Prop
  /-- (H2) = (FRESH): the joint-with-parent level-determinacy separation clause
      (O-9's named open), incl. clause (c) = the former JUNCTION-PIN. -/
  h2_fresh    : Prop
  /-- (H3), leg 1 = D-12r: TB-CAP's (τ-irr) completeness perimeter. -/
  h3_d12r     : Prop
  /-- (H3), leg 2 = (E-N): O-1thr Theorem 3(c)'s exhaustion caveat. -/
  h3_en       : Prop
  /-- (H3), leg 3 = (ADM), THE OPERATIVE FORM (O-9 r4, FULL attainment):
      dim_{F_q} G_{β_k} = s(β_k+1) − s(β_k) = d at every on-line lattice slot.
      Automatic at r = 0 ONLY (ROOT REVISION 4, finding VC4-2). -/
  h3_adm      : Prop
  /-- (H4a) = (R1)–(R4): the T-1 stage-tower laws verbatim over O_δ = W(F_{p^δ}).
      NOT clause-(UB)-only — consumed by clause (R) through Step 18's K3-c. -/
  h4a_r1r4    : Prop
  /-- (H4b)(a) = (UB-X)(a): the per-leaf O_δ re-base audit. -/
  h4b_rebase  : Prop
  /-- (H4b)(b) = (UB-X)(b): δ-stable position classes exhaust the realized
      ledger at every δ. -/
  h4b_stable  : Prop
  /-- (K3-δ) = (UB-X)(b) RESTRICTED to Step-18 K3-c's realized δ > 1 pools —
      the named fragment clause (R) consumes (ROOT REVISION 4, finding VC4-1). -/
  h4b_k3delta : Prop
  /-- The fragment law, DISPLAYED: full (UB-X)(b) implies its (K3-δ) fragment. -/
  stable_implies_k3delta : h4b_stable → h4b_k3delta
  /-- (H4b)(c) = (UB-X)(c): full solve + type aggregation commute with
      unramified base change. -/
  h4b_commute : Prop
  /-- (H5) = (PACK): the actual-pack correspondence (D-11's open clause 4) —
      the concrete assembled pack = the intended 𝔅_n instantiation
      entry-for-entry (ROOT REVISION 4, finding VC4-3). -/
  h5_pack     : Prop
  /-- (H6)(a1) = (T-DEC): CU-2t terminal row — emission discipline at decided
      sites ((T-DEC-dec)) + the corner fence ((T-DEC-cor)). -/
  h6_tdec     : Prop
  /-- (H6)(a2) = (T-READ): emitted shape/position fields = the (c1)-shape
      polygon-side datum (the (RC-read) supply; GD-2/GD-5 family per CU-2t R4). -/
  h6_tread    : Prop
  /-- (H6)(a3) = (T-VERD): terminal verdict-field conformance. -/
  h6_tverd    : Prop
  /-- (H6)(b) = D-11 widened-charge item (vii): general-n H.6 in-fence
      conformance of the built tables (consumed at Step 18's K3-a). -/
  h6_vii      : Prop
```

Per-clause selectors — the attribution display of ROOT §1 (ROOT-C), transcribed
EXACTLY (clauses (0)/(SQ) unconditional — REVISION 4, finding VC4-4 — so they get
NO selector; clause (R) ← (H1)–(H3) + (H4a) + (H5) + (K3-δ) + (H6); clause (UB) ←
(H1)–(H3) + (H4a) + (H4b) + (H5) + (H6)):

```lean
/-- Clause (R)'s hypothesis set, per the (ROOT-C) attribution display. -/
def ClauseRHyps {n : ℕ} (H : RootHyps n) : Prop :=
  H.h1_grb ∧ H.h2_fresh ∧ (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_k3delta ∧ H.h5_pack ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii)

/-- Clause (UB)'s hypothesis set, transcribed directly: full (H4b)(b) is
    primitive here; the K3-δ fragment is derived only when clause (R) is needed. -/
def ClauseUBHyps {n : ℕ} (H : RootHyps n) : Prop :=
  H.h1_grb ∧ H.h2_fresh ∧ (H.h3_d12r ∧ H.h3_en ∧ H.h3_adm) ∧ H.h4a_r1r4 ∧
    H.h4b_rebase ∧ H.h4b_stable ∧ H.h4b_commute ∧ H.h5_pack ∧
    (H.h6_tdec ∧ H.h6_tread ∧ H.h6_tverd ∧ H.h6_vii)

theorem clauseR_of_clauseUB {n : ℕ} {H : RootHyps n} :
    ClauseUBHyps H → ClauseRHyps H

/-- HONESTY GATE (the wave-4-boundary display, machine-checked): `RootHyps` and
    its selectors are transcription devices, not mathematical discharge. Any
    theorem claiming `RootC` must also expose the typed division results that
    consume the selected rows; `ClauseRHyps`/`ClauseUBHyps` alone is insufficient. -/
def trivialRootHyps (n : ℕ) : RootHyps n   -- all fields `True`, law `id`
theorem trivialRootHyps_ub (n : ℕ) : ClauseUBHyps (trivialRootHyps n)
```

**Division-interface contract (binding on BP_I–BP_V unit tables).** A step unit
consuming a §3.1 row writes `(H : RootHyps n)` + the named field in its binder
list (e.g. `(hadm : H.h3_adm)`), never a fresh anonymous `Prop`. When a division
builds a row's carrier, the refinement lands HERE (one revision, BP_VI owner,
Codex plan-review per the standing rule) and the division re-keys — never a
parallel second hypothesis surface.

### 1.2 `Scaffold/Spine.lean` — the scaffold-form target `RootC` [wave VI-0]

Imports: `LeanUrat.MovesU.Defs`, `LeanUrat.MovesU.DefsLedger` (types reused, NOT
redefined: `SplittingType n` (Defs.lean:30), `ClassifierSpec n p` (Defs.lean:62),
`SolveData n`/`evalℝ` (Defs.lean:106/111), `RegData`/`RegP` (Defs.lean:124/209),
`ZpBridge` (DefsLedger.lean:740), `UInstance` (DefsLedger.lean:851)).

The statement shape is the 2026-08-01 scaffold authority = theoremU's conclusion
re-packaged clause-for-clause ((0)+(SQ)+(R) per prime, Σ = 1 globally); the
scaffold spine's job is to make the clause structure NAMED so divisions and the
eventual (ROOT-C) composition key to clauses, not to a 5-tuple.

```lean
open LeanUrat.MovesU Filter Topology

/-- The per-prime scaffold conclusion at data (X, B, α): clause (0) on three
    density readings (classifier-keyed, true-type, ℤ_p-read), clause (SQ)'s
    two-sided level-N bracket, and drainage. Field-for-field = theoremU's
    per-prime conclusion tuple (U10_theoremU.lean:119–138). -/
structure PrimeConclusion {n p : ℕ} [Fact p.Prime] (X : ClassifierSpec n p)
    (B : ZpBridge X) (α : SplittingType n → ℝ) : Prop where
  bracket   : ∀ (σ : SplittingType n) (N : ℕ),
      (α σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧
      (X.decided σ N : ℝ) ≤ α σ * (p : ℝ) ^ (n * N)
  dmass     : ∀ σ, Tendsto (X.dmass σ) atTop (𝓝 (α σ))
  trueDmass : ∀ σ, Tendsto (X.trueDmass σ) atTop (𝓝 (α σ))
  zpRead    : ∀ σ, Tendsto (ZpBridge.zpDmass B σ) atTop (𝓝 (α σ))
  drainage  : Tendsto X.env atTop (𝓝 0)

/-- **`RootC` — the spine target.** ONE rational family, Σ_σ R_σ = 1 identically,
    and at every (REG-p) prime the full per-prime scaffold conclusion at
    α := evalℝ R · p. (At a p failing (REG-p): NO CLAIM — D8.) -/
def RootC (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) : Prop :=
  ∃ R : SplittingType n → RatFunc ℚ,
    R = S.R ∧ (∑ σ, R σ = 1) ∧
    ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
      @PrimeConclusion n p ⟨hp⟩ (inst p hp).X (inst p hp).bridge
        (fun σ => evalℝ ⟨R⟩ σ p)
```

The literal theoremU tuple, including its order, is recorded and checked here:

```lean
def TheoremUTuple (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) : Prop :=
  ∃ R : SplittingType n → RatFunc ℚ,
    R = S.R ∧ (∑ σ, R σ = 1) ∧
    ∀ (p : ℕ) (hp : p.Prime), RegP (inst p hp).D →
      (∀ (σ : SplittingType n) (N : ℕ),
        (evalℝ ⟨R⟩ σ p - (inst p hp).X.env N) * (p : ℝ) ^ (n * N) ≤
          ((inst p hp).X.decided σ N : ℝ) ∧
        ((inst p hp).X.decided σ N : ℝ) ≤
          evalℝ ⟨R⟩ σ p * (p : ℝ) ^ (n * N)) ∧
      (∀ σ, Tendsto ((inst p hp).X.dmass σ) atTop
        (𝓝 (evalℝ ⟨R⟩ σ p))) ∧
      (∀ σ, Tendsto ((inst p hp).X.trueDmass σ) atTop
        (𝓝 (evalℝ ⟨R⟩ σ p))) ∧
      (∀ σ, Tendsto (ZpBridge.zpDmass (inst p hp).bridge σ) atTop
        (𝓝 (evalℝ ⟨R⟩ σ p))) ∧
      Tendsto (inst p hp).X.env atTop (𝓝 0)

theorem RootC_iff_tuple (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (S : SolveData n)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    RootC n C KC K7 S inst ↔ TheoremUTuple n C KC K7 S inst
```

`RootC_iff_tuple` fixes theoremU's order as bracket, classifier density,
true-type density, ℤ_p-read density, drainage. It checks the same quantifier
order (∃ R before ∀ p), the same (REG-p) guard, and all five clauses. The (ROOT)
target's clause (UB) is NOT in `RootC`: it enters only through `ClauseUBHyps` at
the future composed form (VI-F1), matching the honest Step-16 scope of ROOT §1.

### 1.3 `Scaffold/CorpusBridge.lean` — theoremU → RootC [wave VI-1]

Imports: `Scaffold/Spine.lean`, `LeanUrat.MovesU.U10_theoremU`,
`LeanUrat.MovesU.BridgeMk`, `LeanUrat.MovesU.SlotsG18_relPack`,
`LeanUrat.MovesU.SlotsG2_rel1`, `LeanUrat.MovesU.SlotsG3_rel2`,
and every concrete slot module `SlotsG4_rs0Lump` through
`SlotsG10_jcInvHist`. No reliance on re-export is permitted.

```lean
/-- VI-B1: theoremU's conclusion, transported into the spine shape. -/
theorem rootC_of_theoremU (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (S : SolveData n)
    (KT : UpstreamTyped n KC)
    (rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
      m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b)
    (hrel2d : rel2d) (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrack : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst)
    (hjc : jcInvHist)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    RootC n C KC K7 S inst

/-- VI-B2: direct VI-B1 specialization at the same inputs used by
    `theoremU_fired`; it does not consume `theoremU_fired` as an argument. -/
theorem rootC_fired (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC)
    (KT : UpstreamTyped n KC) (BP : BridgePre n C)
    (rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
      m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b)
    (hrel2d : rel2d) (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrack : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst)
    (hjc : jcInvHist)
    (BD : ∀ (p : ℕ) (hp : p.Prime), BridgeInputs n C KC K7 p hp) :
    RootC n C KC K7 (bridgeSolve C BP.hdet)
      (fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp))

/-- VI-B3: the D-SC SLOT ASSIGNMENT — the typed faces of theoremU's 13 bare-Prop
    slot parameters, NAMED (statement-layer map only; wires NO wave-D carrier —
    parked items 22–29 untouched). Records which sited definition each row takes:
    rel1..rel3 ← `RelRow_rel1..rel3 RP` (SlotsG18_relPack.lean:88–…, over a
    `RelCarrierPack`); rs0Lump ← `Slot_rs0Lump n C` (SlotsG4); trackRule ←
    `Slot_trackRule n KC K7` (SlotsG5); dnLattice ← `Slot_dnLattice n KC K7`
    (SlotsG6); m1m5Echo ← `Slot_m1m5Echo n C` (SlotsG7); x1aDict ←
    `Slot_x1aDict n KC` (SlotsG8); m4bConst ← `Slot_m4bConst n SS` over the
    measured carrier `SS : CtsMeasured n 𝓕 Sv` (SlotsG9);
    jcInvHist ← `Slot_jcInvHist n` (SlotsG10). -/
structure SlotAssignment (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (RP : RelCarrierPack)
    (𝓕 : LeanUrat.MovesV.CtsFamily n)
    (Sv : LeanUrat.MovesV.StepSys n)
    (SS : LeanUrat.MovesV.CtsMeasured n 𝓕 Sv) : Prop where
  rel1 : RelRow_rel1 RP
  rel2a : RelRow_rel2a RP
  rel2b : RelRow_rel2b RP
  rel2d : RelRow_rel2d RP
  rel2e : RelRow_rel2e RP
  rel3 : RelRow_rel3 RP
  rs0 : Slot_rs0Lump n C
  trk : Slot_trackRule n KC K7
  dn : Slot_dnLattice n KC K7
  m15 : Slot_m1m5Echo n C
  x1a : Slot_x1aDict n KC
  m4b : Slot_m4bConst n SS
  jc : Slot_jcInvHist n

/-- VI-B4: RootC fired with all thirteen theoremU propositions instantiated by
    the sited slot faces. Typed ledger, bridge preconditions, and per-prime
    bridge inputs remain explicit. -/
theorem rootC_fired_at_slots (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC)
    (KT : UpstreamTyped n KC) (BP : BridgePre n C)
    (RP : RelCarrierPack) (𝓕 : LeanUrat.MovesV.CtsFamily n)
    (Sv : LeanUrat.MovesV.StepSys n)
    (SS : LeanUrat.MovesV.CtsMeasured n 𝓕 Sv)
    (SA : SlotAssignment n C KC K7 RP 𝓕 Sv SS)
    (BD : ∀ (p : ℕ) (hp : p.Prime), BridgeInputs n C KC K7 p hp) :
    RootC n C KC K7 (bridgeSolve C BP.hdet)
      (fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp))
```

The public binder decision is fixed (REVISION 3): `SlotAssignment` takes `𝓕`
before the step system `Sv` and the measured carrier `SS`, with
`Sv : MovesV.StepSys n` and `SS : MovesV.CtsMeasured n 𝓕 Sv` (the corpus
`StepSys` takes only `n`, MovesV/Defs.lean:81, and `Slot_m4bConst`'s explicit
argument after `n` is the measured carrier, SlotsG9_m4bConst.lean:74); `m4b`
is the full `Slot_m4bConst n SS` face. `Slot_trackRule n KC K7` and
`Slot_dnLattice n KC K7` retain the explicit `(n, KC, K7)` order shown above.
No binder or existential-face choice remains for E-phase.

### 1.4 `Scaffold/AnchorN2.lean` — the numerics/instance anchors [wave VI-2]

Imports: `LeanUrat.OM.UniformCapstone`, `LeanUrat.OM.SeriesAssembly`,
`LeanUrat.OM.RealInstanceV2Gates`. Anchors are FLAGS, never substitutes (tree §0
discipline): each re-fires a machine-checked instance in scaffold shape so a
regression anywhere in the spine's import cone breaks a visible gate.

The anchor pattern (REVISION 3): each anchor `def` states THE ACTUAL
PROPOSITION its corpus gate proves (never `Nonempty` of a proof term — the
Revision-2 shape was a compiler-refuted category error), and its consumption
theorem's proof is the corpus gate term verbatim. For VI-N1 a definitional
pin (`example : AnchorN2 p σ hσ = type_of% (montes_uniform_n2 p σ hσ) := rfl`)
certifies the transcription is exact.

```lean
/-- VI-N1 is the exact capstone proposition, not a hand-reconstructed partial
    record. This preserves pole-freeness, the common rational family, value tie,
    and bracket uniqueness together, with the prime instance explicit. -/
def AnchorN2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : Prop :=
  (uniformDen σ ≠ 0 ∧
    (∀ q' : ℕ, 1 < q' → (uniformDen σ).eval (q' : ℚ) ≠ 0 ∧
      (∑ T ∈ shapesOfU σ, CU T q')
        = (uniformNum σ).eval (q' : ℚ) / (uniformDen σ).eval (q' : ℚ)) ∧
    ((M7 p).countingDensity σ
        = (uniformNum σ).eval ((p : ℕ) : ℚ) / (uniformDen σ).eval ((p : ℕ) : ℚ)
      ∧ (uniformDen σ).eval ((p : ℕ) : ℚ) ≠ 0)) ∧
  ∀ d : ℚ, (∀ N : ℕ, 1 ≤ N →
      (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N) ≤ d ∧
      d ≤ (M7 p).decidedCount σ N / (p : ℚ) ^ (2 * N)
            + (M7 p).undecidedCount N / (p : ℚ) ^ (2 * N)) →
    d = (M7 p).countingDensity σ

theorem anchor_n2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : AnchorN2 p σ hσ :=
  montes_uniform_n2 p σ hσ

example (p : ℕ) [Fact p.Prime] (σ : FactorizationType) (hσ : σ.degree = 2) :
    AnchorN2 p σ hσ = type_of% (montes_uniform_n2 p σ hσ) := rfl

/-- VI-N2: the exact `hExhaust_n2` proposition is preserved by a named wrapper;
    no denominator or coercion is retyped in the scaffold. -/
def AnchorN2Drainage : Prop :=
  Tendsto (fun N => undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)) atTop (nhds 0)
theorem anchor_n2_drainage : AnchorN2Drainage := hExhaust_n2

/-- VI-N3: stable named declarations, each preserving the complete proposition
    and all coercions of its corpus gate definitionally. -/
def AnchorV2ValueInert2 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
      OMCountV2.omCount T M9.realP) = 1 / 4
theorem anchor_v2_value_inert2 : AnchorV2ValueInert2 :=
  gate_v2_value_inert2

def AnchorV2SplitQ3 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
      OMCountV2.omCount T 3) = 1 / 9
theorem anchor_v2_split_q3 : AnchorV2SplitQ3 := gate_v2_split_q3

def AnchorV2InertQ3 : Prop :=
  (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
      OMCountV2.omCount T 3) = 1 / 3
theorem anchor_v2_inert_q3 : AnchorV2InertQ3 := gate_v2_inert_q3

def AnchorV2SigmaSeparation : Prop :=
  Order0.unramType 2 OMCountV2.lam11 ≠ Order0.unramType 2 OMCountV2.lam2
    ∧ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
          OMCountV2.omCount T 3)
      ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
          OMCountV2.omCount T 3)
theorem anchor_v2_sigma_separation : AnchorV2SigmaSeparation :=
  gate_v2_sigma_separation
```

### 1.5 `Scaffold/AxChk.lean` — the axiom-census extension [wave VI-3]

Standalone census file (NOT imported by anything; `AxChk_baseline.lean` NOT
edited). Run: `lake env lean LeanUrat/Scaffold/AxChk.lean` at every division
checkpoint (ledger ground rule). Contents are four independently reviewable ≤40-line census units in this one
standalone file: VI-A1 lists every named VI-H*/VI-S*/VI-B* theorem; VI-A2 lists
every named VI-N* theorem and its four named gate wrappers; VI-A3 lists
`theoremU`, `theoremU_fired`, `montes_uniform_n2`, `montes_unconditional`,
`hExhaust_n2`, `skeleton_finite`, `runRealizerExists_zmod`, and
`sigmaV_vertexLaw`; VI-A4 enumerates every declaration selected from the `ksub`,
`O12PoleFree`, `RegPFinite`, `O5CountingB`, and `UE_vtxUpper` families. The
module header must contain that finite enumeration; family names or wildcards
are not accepted as census rows.
Acceptance bar: Lean core only (`propext`, `Classical.choice`, `Quot.sound`) for
every row above — a regression is stop-the-line (repo CLAUDE.md).

### 1.6 FUTURE units — fenced, assigned to NO wave

| id | statement | blocker (why future) |
|---|---|---|
| VI-F1 | `rootC_of_rootHyps` — the composed spine: `ClauseRHyps H` (+ division step theorems, Movements I–V) → `RootC …`; the Lean face of ROOT §2's Step-19 composition | needs BP_I–BP_V unit deliveries; the composition order is Steps 1–18b ≺ 19 (ROOT Movement V) |
| VI-F2 | the OM-model ↔ `ClassifierSpec` faithfulness tie at n = 2 (fire VI-N1's `M7 p` instance INTO a `UInstance`-shaped witness) — the Lean face of the K-12 faithfulness-audit row (ROOT §3.2) | the audit row's grade is held pending; statement design needs the K-12 record first |
| VI-F3 | `rootC_real` — RootC at the REAL populated `BridgeInputs` (suppliers per BridgeMk.lean:46–68) with the device discharged | PARKED items 22–29 (wave-D carrier population + Lean statement repairs); UNTOUCHED by swarm authority |
| VI-F4 | clause-(UB) spine form (`RootC_UB` over `ClauseUBHyps`) | needs Movement-IV/V (UB) step statements (Step 16's scope) from BP_IV/BP_V |

---

## 2. UNIT TABLE

Every unit ≤ ~40 lines of Lean (docstrings compressed to one line per row where
needed; long provenance lives in module headers, split off as MECH units).
Difficulty: MECH (transcription/application), EASY (short proof, no search),
MED (real proof), HARD (core). Source ¶ = the blueprint paragraph above + the
math source it transcribes.

| id | target file | statement (compressed) | proof sketch | deps | diff | source ¶ |
|---|---|---|---|---|---|---|
| VI-H0 | Scaffold/Hypotheses.lean | module header: provenance block (ROOT §3.1 row map, revision pointers, sync-duty note) | prose only, no decls | — | MECH | §1.1 head |
| VI-H1 | Scaffold/Hypotheses.lean | `structure RootHyps (n : ℕ)` — sixteen bare-`Prop` hypothesis-row fields plus the seventeenth field `stable_implies_k3delta`, an implication law | structure decl, compiles by itself | VI-H0 | MECH | §1.1; ROOT §3.1 rows 1–7 |
| VI-H2 | Scaffold/Hypotheses.lean | `ClauseRHyps`/`ClauseUBHyps` defs + `clauseR_of_clauseUB` | defs; lemma = `fun h => h.1` | VI-H1 | MECH | §1.1; ROOT §1 (ROOT-C) attribution display |
| VI-H3 | Scaffold/Hypotheses.lean | `trivialRootHyps` (all-`True`) + `trivialRootHyps_ub` honesty gate | record literal, `⟨…, trivial…⟩`; `simp [ClauseRHyps, ClauseUBHyps, trivialRootHyps]` | VI-H2 | MECH | §1.1 honesty gate; U10 wave-4-boundary record |
| VI-S1 | Scaffold/Spine.lean | `structure PrimeConclusion` (5 clause fields) | structure decl over MovesU types | — (imports MovesU.Defs/DefsLedger) | MECH | §1.2; U10_theoremU.lean:119–138; 2026-08-01 authority |
| VI-S2 | Scaffold/Spine.lean | `def RootC` (∃ R, pin, Σ = 1, per-(REG-p) `PrimeConclusion`) | def only | VI-S1 | MECH | §1.2; ROOT §1 clauses (0)/(SQ)/(R) |
| VI-S3 | Scaffold/Spine.lean | `TheoremUTuple` literal five-clause signature + `RootC_iff_tuple` | destruct/rebuild in the recorded bracket, dmass, trueDmass, zpRead, drainage order | VI-S2 | EASY | §1.2 fidelity note |
| VI-B1 | Scaffold/CorpusBridge.lean | `rootC_of_theoremU` (signature = theoremU's binder list, conclusion `RootC …`) | `obtain ⟨R,hR,hs,h⟩ := theoremU …; exact ⟨R,hR,hs, fun p hp hr => let t := h p hp hr; ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2⟩⟩` | VI-S2; MovesU.U10_theoremU | EASY | §1.3; ROOT Step 19 |
| VI-B2 | Scaffold/CorpusBridge.lean | `rootC_fired` with `KT`, all thirteen propositions/proofs, `BP`, and `BD` visible | direct specialization of VI-B1 at `bridgeSolve`/`mkUInstance`; `theoremU_fired` is a parallel corpus check, not an output argument | VI-B1; MovesU.BridgeMk | MECH | §1.3; BridgeMk IB-F5 |
| VI-B3 | Scaffold/CorpusBridge.lean | `structure SlotAssignment` with fixed `(𝓕, Sv, SS)` binders (REVISION 3) and thirteen typed slot faces | structure declaration only; no E-phase interface decision remains | MovesU.SlotsG2–G10, G18 | MECH | §1.3; U10 residual-bare-rows docstring |
| VI-B4 | Scaffold/CorpusBridge.lean | full `rootC_fired_at_slots` signature: explicit `KT`, `BP`, `RP`, `𝓕`, `SS`, `SA`, and `BD`; conclusion shows the complete `mkUInstance` family | apply VI-B2 with all thirteen proposition parameters set to the displayed slot faces and all thirteen proofs projected from `SA` | VI-B2, VI-B3 | MECH | §1.3 |
| VI-N1 | Scaffold/AnchorN2.lean | `AnchorN2` exact-proposition wrapper + `anchor_n2`, with explicit `p` and `[Fact p.Prime]` | constructor containing `montes_uniform_n2 σ hσ` | OM.UniformCapstone | EASY | §1.4; ROOT §1 verified-instances block |
| VI-N2 | Scaffold/AnchorN2.lean | `AnchorN2Drainage` + named `anchor_n2_drainage`, preserving the exact `hExhaust_n2` type | constructor containing `hExhaust_n2` | OM.SeriesAssembly | MECH | §1.4 |
| VI-N3 | Scaffold/AnchorN2.lean | four named exact-proposition wrappers and four named gate theorems | constructor containing the corresponding `gate_v2_…` proof | OM.RealInstanceV2Gates | MECH | §1.4 |
| VI-A1 | Scaffold/AxChk.lean | `#print axioms` for VI-H*, VI-S*, VI-B* | explicit finite declaration list | landed scaffold core | MECH | §1.5 |
| VI-A2 | Scaffold/AxChk.lean | `#print axioms` for VI-N* and direct anchors | explicit finite declaration list | VI-N1–VI-N3 | MECH | §1.5 |
| VI-A3 | Scaffold/AxChk.lean | `#print axioms` for theoremU/bridge and OM quarry | explicit finite declaration list | imported quarry | MECH | §1.5 |
| VI-A4 | Scaffold/AxChk.lean | `#print axioms` for named `ksub`, `O12PoleFree`, `RegPFinite`, `O5CountingB`, and `UE_vtxUpper` declarations enumerated in the module header | explicit finite declaration list; no family wildcard | imported quarry | MECH | §1.5 |

Estimated: 18 waved units (15 MECH, 3 EASY), 0 sorries permitted. “Green” means
the complete target file has passed its wave's explicit `lake env lean` gate;
no claim of isolated compilation is made for fragments that share a file.
The genuinely hard integration content (VI-F1) is deliberately future: it
cannot be stated before the divisions' step statements exist.

## 3. CORPUS-REUSE MAP (which existing proved declarations discharge which units)

| existing declaration (file:line) | status | discharges / feeds |
|---|---|---|
| `theoremU` (MovesU/U10_theoremU.lean:104) | proved, conditional on its typed ledger + 13 slots | VI-B1 (sole proof input); VI-S1/S2's shape source |
| `theoremU_fired` + `mkUInstance` + `BridgeInputs` (MovesU/BridgeMk.lean:86/152/183) | proved (device-conditional) | VI-B2; VI-F3's target vocabulary |
| `bridgeSolve` (MovesU/BridgeSolve.lean:55) | landed | VI-B2/B4 solve family |
| D-SC slot layer: `Slot_rel1..rel3` (SlotsG2/G3), `Slot_rs0Lump..jcInvHist` (SlotsG4–G10), `RelCarrierPack`+`RelRow_*` (SlotsG18:79–…) | statement layer landed (H-phase behind Codex ACCEPT) | VI-B3 fields; VI-B4 instantiation |
| `montes_uniform_n2` (OM/UniformCapstone.lean:1850) | PROVED, Lean-core, every p incl. wild 2 | VI-N1 |
| `hExhaust_n2` (OM/SeriesAssembly.lean:1745) | PROVED, Lean-core | VI-N2 |
| `gate_v2_value_inert2`/`gate_v2_split_q3`/`gate_v2_inert_q3`/`gate_v2_sigma_separation` (OM/RealInstanceV2Gates.lean:90–136) | proved gates | VI-N3 |
| `montes_unconditional`(+`_exhaustive`) (OM/RealInstanceV2.lean:413/439) | proved (htameFE/hExhaust-conditional) | VI-A1 census rows; VI-F2 context |
| `O12PoleFree` rows (MovesU/O12PoleFree.lean), `RegPFinite` rows (MovesU/RegPFinite.lean:69–147), `O5CountingB` rows (MovesU/O5CountingB.lean:44–90), `skeleton_finite` (MovesV/SkeletonFinite.lean:83), `runRealizerExists_zmod` (MovesD/R7_runRealizer.lean:543), `sigmaV_vertexLaw` (HC2/HK11a_vertexTransport.lean:476), `UE_vtxUpper` rows (HC2/UE_vtxUpper.lean:70–153), `ksub` family (MovesS/Ksub*.lean) | proved | VI-A1 census rows; PRIMARY QUARRY for BP_I–BP_V (listed here so division leads route reuse through ONE map); none is re-proved by any VI unit |
| `RegP`/`RegData`/`RegPin` (MovesU/Defs.lean:124/209, DefsLedger.lean:485) | landed | VI-S2's (REG-p) guard — reused verbatim, never restated |

## 4. WAVE PLAN (for the division lead)

* **Wave VI-0 (FIRST; blocks every other division's briefs):** VI-H0 → VI-H1 →
  VI-H2 → VI-H3, then gate
  `lake env lean LeanUrat/Scaffold/Hypotheses.lean`; independently VI-S1 → VI-S2,
  then gate `lake env lean LeanUrat/Scaffold/Spine.lean`. Announce the landed
  field names and `RootC` only after both gates pass.
* **Wave VI-1:** VI-S3, then re-gate
  `lake env lean LeanUrat/Scaffold/Spine.lean`; VI-B1 → VI-B2 and VI-B3 → VI-B4,
  then gate `lake env lean LeanUrat/Scaffold/CorpusBridge.lean`.
* **Wave VI-2 (parallel to VI-1):** VI-N1 → VI-N2 → VI-N3, then gate
  `lake env lean LeanUrat/Scaffold/AnchorN2.lean`.
* **Wave VI-3 (checkpoint):** VI-A1 → VI-A2 → VI-A3 → VI-A4, then division
  checkpoint = full
  `lake build` + `lake env lean LeanUrat/Scaffold/AxChk.lean` +
  `lake env lean LeanUrat/AxChk_baseline.lean` (regression watch) + commit.
* FUTURE table (§1.6): assigned to no wave; VI-F1 re-enters when BP_I–BP_V
  division leads report their step-statement layers landed (orchestrator
  adjudication, not this lead's call).

## 5. Change discipline + sync duty

* This blueprint transcribes ROOT ASSEMBLY at REVISION 5. If a further ROOT
  revision changes the (ROOT-C) hypothesis list or per-clause attribution, the
  DELTA lands first in §1.1/§1.2 here (BP_VI owner), then in
  `Scaffold/Hypotheses.lean` — the ledger's math-revision sync duty.
* Statement-fence flags for the Codex plan review (level 2): the `RootHyps`
  field list vs ROOT §3.1 (sixteen rows plus one implication law);
  `ClauseRHyps`/`ClauseUBHyps` vs the (ROOT-C) attribution display;
  `TheoremUTuple`/`PrimeConclusion`/`RootC` vs theoremU's literal ordered
  conclusion; the fixed §1.3 `SlotAssignment` binders; and the finite,
  declaration-by-declaration VI-A1–VI-A4 census.
* Standing honesty rule for every consumer: `RootC`-family theorems inherit
  theoremU_fired's conditionality record; `RootHyps` presence is UNPINNED until
  field refinement — no acceptance claim may read either as discharged.

## REVISION 2 (review fold, 2026-08-03)
| finding | disposition | where/why |
|---|---|---|
| 1 | FIXED | §1.3 fixes `SlotAssignment` binders as `(𝓕, SS)`, uses full `Slot_m4bConst n 𝓕 SS`, and fixes track/dn order. |
| 2 | FIXED | §1.4 makes `AnchorN2` preserve the exact complete proposition of `montes_uniform_n2`, including all four advertised components. |
| 3 | FIXED | §1.4 replaces the omitted denominator and absent examples with exact-proposition wrappers and four stable named theorem declarations. |
| 4 | FIXED | §1.2 adds the complete `TheoremUTuple` signature and `RootC_iff_tuple`, fixing the five-clause tuple order. |
| 5 | FIXED | §1.3 displays `KT`, all thirteen proposition/proof pairs, `BP`, and `BD` in `rootC_fired`. |
| 6 | FIXED | §1.3 and VI-B2 now specify direct VI-B1 specialization; no theorem output is falsely passed as an argument. |
| 7 | FIXED | §1.3 gives the complete VI-B4 binders, `SA`, `BD`, and constructed `UInstance` family. |
| 8 | FIXED | VI-N3 now creates four named theorems, so every scaffold gate has a stable AxChk target. |
| 9 | FIXED | `ClauseUBHyps` is transcribed directly with full H4b primitive; K3-δ is derived only for clause R. |
| 10 | FIXED | VI-H1 now says sixteen bare-Prop rows plus one implication-law field, seventeen structure fields total. |
| 11 | FIXED | §1.1 states that selectors are transcription devices and every RootC consumer must visibly expose typed division results. |
| 12 | FIXED | `anchor_n2` explicitly binds `(p : ℕ) [Fact p.Prime]`. |
| 13 | FIXED | VI-N1 drops the unused VI-S1 dependency; AnchorN2 imports only its actual OM source. |
| 14 | FIXED | the census is split into four ≤40-line units with a mandatory finite declaration enumeration. |
| 15 | FIXED | §1.3 explicitly imports G2, G3, G4–G10, and G18; VI-B3 matches that dependency set. |
| 16 | FIXED | the blanket isolation claim is removed and every wave now has an explicit per-file `lake env lean` gate. |

## REVISION 3 (statement repairs, compile-gated, 2026-08-01)

The BP_VI division run landed 12/18 units; six (VI-B3, VI-B4, VI-N1, VI-N2,
VI-N3, VI-A2) were BLOCKED because the Revision-2 verbatim displays were
ILL-TYPED against the built corpus (the provers correctly refused to alter
statements; their compiler evidence is quoted in the Scaffold BLOCKED comments
of record). These repairs are sanctioned ONLY because the old statements were
compiler-refuted — ill-typed displays carry no mathematical content, so no
content is lost; the intended mathematics of each unit is preserved exactly.
EVERY repaired statement below was compile-verified through a probe file
(`lake env lean`, 2026-08-01, zero errors) BEFORE entering this blueprint, and
the landed files passed their per-file gates + the VI-A2/AxChk census
(Lean-core footprints `[propext, Classical.choice, Quot.sound]` on all rows).

| unit | old (Revision 2, refuted) | new (Revision 3, compiled) | compiler evidence for the old form |
|---|---|---|---|
| VI-B3 | `SlotAssignment … (𝓕 : CtsFamily n) (SS : StepSys n 𝓕)` with `m4b : Slot_m4bConst n 𝓕 SS` | binders `(𝓕 : CtsFamily n) (Sv : StepSys n) (SS : CtsMeasured n 𝓕 Sv)` with `m4b : Slot_m4bConst n SS` (`𝓕`-before-`SS` order kept) | corpus `MovesV.StepSys` takes only `(n : ℕ)` (Defs.lean:81): "Function expected at MovesV.StepSys n but this term has type Type 1"; `Slot_m4bConst`'s explicit arg after `n` is the MEASURED carrier (SlotsG9:74): "argument 𝓕 has type MovesV.CtsFamily n but is expected to have type MovesV.CtsMeasured n ?m ?m" |
| VI-B4 | `rootC_fired_at_slots` over `(SS : StepSys n 𝓕)` / `SA : SlotAssignment n C KC K7 RP 𝓕 SS` | same signature over the three repaired binders, `SA : SlotAssignment n C KC K7 RP 𝓕 Sv SS`; proof = VI-B2 at the thirteen sited faces with proofs projected from `SA` | inherits the VI-B3 binder refutation |
| VI-N1 | `AnchorN2 … : Prop := Nonempty (montes_uniform_n2 σ hσ)`; `anchor_n2 : AnchorN2 p σ := ⟨montes_uniform_n2 σ hσ⟩` | `AnchorN2 p σ hσ : Prop :=` the capstone's EXACT proposition written out; `anchor_n2 : AnchorN2 p σ hσ := montes_uniform_n2 p σ hσ`; plus definitional pin `AnchorN2 p σ hσ = type_of% (montes_uniform_n2 p σ hσ) := rfl` | `montes_uniform_n2` is a THEOREM: "argument montes_uniform_n2 … has type ⟨the capstone conjunction⟩ : Prop but is expected to have type Sort ?u" (`Nonempty : Sort u → Prop` cannot consume a proof term); also missing explicit leading `p` (UniformCapstone.lean:295 section variable): "argument σ has type FactorizationType but is expected to have type ℕ" |
| VI-N2 | `AnchorN2Drainage : Prop := Nonempty hExhaust_n2` | `AnchorN2Drainage : Prop := Tendsto (fun N => undecidedCount6 N / (M9.realP : ℚ) ^ (2 * N)) atTop (nhds 0)` (= `hExhaust_n2`'s exact statement, SeriesAssembly.lean:1745); `anchor_n2_drainage := hExhaust_n2` | same `Nonempty`-of-proof-term category error |
| VI-N3 | four `Nonempty gate_v2_…` wrappers with `⟨gate_v2_…⟩` proofs | four defs = the gates' exact propositions (RealInstanceV2Gates.lean:90/120/127/136); four theorems proved by the gate terms verbatim | same `Nonempty`-of-proof-term category error |
| VI-A2 | census rows fenced (no targets at HEAD) | rows unfenced; `import LeanUrat.Scaffold.AnchorN2` added; `rootC_fired_at_slots` row added to VI-A1; all rows Lean-core | targets did not exist while VI-N1–N3 were blocked |
