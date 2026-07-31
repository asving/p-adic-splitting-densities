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

/-- Clause (UB)'s hypothesis set = clause (R)'s + the rest of (H4b). -/
def ClauseUBHyps {n : ℕ} (H : RootHyps n) : Prop :=
  ClauseRHyps H ∧ H.h4b_rebase ∧ H.h4b_stable ∧ H.h4b_commute

theorem clauseR_of_clauseUB {n : ℕ} {H : RootHyps n} :
    ClauseUBHyps H → ClauseRHyps H

/-- HONESTY GATE (the wave-4-boundary display, machine-checked): `RootHyps` is
    True-instantiable, so its mere presence pins nothing. -/
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

Fidelity note (statement-fence flag for the Codex plan review): `RootC` is a
REPACKAGING of theoremU's conclusion — same quantifier order (∃ R before ∀ p, the
F11 discipline), same (REG-p) guard, same five clauses. It adds NO strength and
drops NONE (VI-B1 proves the transport). The (ROOT) target's clause (UB) is NOT
in `RootC`: (UB) enters only through `ClauseUBHyps` at the future composed form
(VI-F1) — matching the honest Step-16 scope of ROOT §1.

### 1.3 `Scaffold/CorpusBridge.lean` — theoremU → RootC [wave VI-1]

Imports: `Scaffold/Spine.lean`, `LeanUrat.MovesU.U10_theoremU`,
`LeanUrat.MovesU.BridgeMk`, `LeanUrat.MovesU.SlotsG18_relPack` (+ SlotsG4–G10 for
the sited slot definitions).

```lean
/-- VI-B1: theoremU's conclusion, transported into the spine shape. Pure
    repackaging — destructure the 5-tuple, build `PrimeConclusion`. -/
theorem rootC_of_theoremU (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (S : SolveData n)
    (KT : UpstreamTyped n KC)
    (rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
     m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) … (hjc : jcInvHist)          -- the 13 rows, verbatim U10
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    RootC n C KC K7 S inst

/-- VI-B2: RootC FIRED at the constructed instance family — the corpus's
    strongest general-n realization: `theoremU_fired` (BridgeMk.lean:183)
    composed with VI-B1 at S := `bridgeSolve C BP.hdet`,
    inst := `fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp)`.
    Inherits theoremU_fired's HONEST CONDITIONALITY OF RECORD verbatim
    (BridgeMk.lean:174–182) — never describe as unconditional. -/
theorem rootC_fired (n : ℕ) (hn : 2 ≤ n) … (BP : BridgePre n C)
    (…the 13 rows…)
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
    `Slot_x1aDict n KC` (SlotsG8); m4bConst ← `Slot_m4bConst …` (SlotsG9);
    jcInvHist ← `Slot_jcInvHist n` (SlotsG10). -/
structure SlotAssignment (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (RP : RelCarrierPack) : Prop where
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
  m4b : Slot_m4bConst_face n C     -- exact keying resolved at E-phase vs SlotsG9
  jc : Slot_jcInvHist n

/-- VI-B4: RootC fired WITH the slot parameters instantiated at the SITED
    definitions — the wave-4 boundary made typed in scaffold-land: given
    `SA : SlotAssignment n C KC K7 RP`, no True-instantiation reading survives. -/
theorem rootC_fired_at_slots … (SA : SlotAssignment n C KC K7 RP) … :
    RootC n C KC K7 (bridgeSolve C BP.hdet) (fun p hp => mkUInstance …)
```

E-phase resolution duty (recorded for the VI-B3 prover): `Slot_m4bConst`
(SlotsG9_m4bConst.lean:74) is keyed over `MovesV.CtsFamily`/`MovesV.StepSys`
binders, not (n, C) alone — the E-phase writer either adds those binders to
`SlotAssignment` or keys the field to an existential face; flag the choice for
the Codex audit. Same check for `Slot_trackRule`/`Slot_dnLattice` implicit-binder
order (SlotsG5/G6).

### 1.4 `Scaffold/AnchorN2.lean` — the numerics/instance anchors [wave VI-2]

Imports: `LeanUrat.OM.UniformCapstone`, `LeanUrat.OM.SeriesAssembly`,
`LeanUrat.OM.RealInstanceV2Gates`. Anchors are FLAGS, never substitutes (tree §0
discipline): each re-fires a machine-checked instance in scaffold shape so a
regression anywhere in the spine's import cone breaks a visible gate.

```lean
/-- VI-N1: the n = 2 scaffold-form anchor — `montes_uniform_n2`
    (OM/UniformCapstone.lean:1850) re-stated as the named clause bundle:
    at EVERY prime p (wild p = 2 included), single (num, den) pole-free family,
    value tie, and the (SQ) bracket-uniqueness clause. Proof: `exact
    montes_uniform_n2 σ hσ` after unfolding the bundle. -/
structure AnchorN2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType) : Prop where …
theorem anchor_n2 (σ : FactorizationType) (hσ : σ.degree = 2) : AnchorN2 p σ

/-- VI-N2: the drainage row's n = 2 witness — `hExhaust_n2`
    (OM/SeriesAssembly.lean:1745) re-fired under the scaffold name; the ONE
    unconditional exhaustion on record. -/
theorem anchor_n2_drainage : Tendsto (fun N => undecidedCount6 N / …) atTop (𝓝 0)

/-- VI-N3: order-0 value gates re-fired: `gate_v2_value_inert2` (1/4 at n = 2
    inert), `gate_v2_split_q3`/`gate_v2_inert_q3` (split ≠ inert at q' = 3),
    `gate_v2_sigma_separation` (RealInstanceV2Gates.lean:90–136). One `example`
    per gate, `exact` proofs. -/
```

### 1.5 `Scaffold/AxChk.lean` — the axiom-census extension [wave VI-3]

Standalone census file (NOT imported by anything; `AxChk_baseline.lean` NOT
edited). Run: `lake env lean LeanUrat/Scaffold/AxChk.lean` at every division
checkpoint (ledger ground rule). Contents: `#print axioms` rows for
(a) every landed `LeanUrat.Scaffold` theorem (VI-H*, VI-S*, VI-B*, VI-N*), and
(b) the corpus-reuse quarry it stands on: `theoremU`, `theoremU_fired`,
`montes_uniform_n2`, `montes_unconditional`, `hExhaust_n2`, `skeleton_finite`,
`runRealizerExists_zmod`, `sigmaV_vertexLaw`, the `ksub` family, the
`O12PoleFree`/`RegPFinite`/`O5CountingB`/`UE_vtxUpper` main rows.
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
| VI-H1 | Scaffold/Hypotheses.lean | `structure RootHyps (n : ℕ)` — 16 fields incl. `stable_implies_k3delta` law field, one-line row docstrings | structure decl, compiles by itself | VI-H0 | MECH | §1.1; ROOT §3.1 rows 1–7 |
| VI-H2 | Scaffold/Hypotheses.lean | `ClauseRHyps`/`ClauseUBHyps` defs + `clauseR_of_clauseUB` | defs; lemma = `fun h => h.1` | VI-H1 | MECH | §1.1; ROOT §1 (ROOT-C) attribution display |
| VI-H3 | Scaffold/Hypotheses.lean | `trivialRootHyps` (all-`True`) + `trivialRootHyps_ub` honesty gate | record literal, `⟨…, trivial…⟩`; `simp [ClauseRHyps, ClauseUBHyps, trivialRootHyps]` | VI-H2 | MECH | §1.1 honesty gate; U10 wave-4-boundary record |
| VI-S1 | Scaffold/Spine.lean | `structure PrimeConclusion` (5 clause fields) | structure decl over MovesU types | — (imports MovesU.Defs/DefsLedger) | MECH | §1.2; U10_theoremU.lean:119–138; 2026-08-01 authority |
| VI-S2 | Scaffold/Spine.lean | `def RootC` (∃ R, pin, Σ = 1, per-(REG-p) `PrimeConclusion`) | def only | VI-S1 | MECH | §1.2; ROOT §1 clauses (0)/(SQ)/(R) |
| VI-S3 | Scaffold/Spine.lean | fidelity display: `RootC_iff_tuple` — RootC unfolds to theoremU's literal conclusion shape | `constructor <;> rintro ⟨R,h1,h2,h3⟩ <;> exact ⟨R,h1,h2, fun p hp hr => …⟩` (clause shuffle) | VI-S2 | EASY | §1.2 fidelity note |
| VI-B1 | Scaffold/CorpusBridge.lean | `rootC_of_theoremU` (signature = theoremU's binder list, conclusion `RootC …`) | `obtain ⟨R,hR,hs,h⟩ := theoremU …; exact ⟨R,hR,hs, fun p hp hr => let t := h p hp hr; ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2⟩⟩` | VI-S2; MovesU.U10_theoremU | EASY | §1.3; ROOT Step 19 |
| VI-B2 | Scaffold/CorpusBridge.lean | `rootC_fired` at (bridgeSolve, mkUInstance family) | `exact rootC_of_theoremU … (inst := fun p hp => mkUInstance …)` via `theoremU_fired`'s route; or VI-B1 applied to `theoremU_fired`'s output shape | VI-B1; MovesU.BridgeMk | MECH | §1.3; BridgeMk IB-F5 |
| VI-B3 | Scaffold/CorpusBridge.lean | `structure SlotAssignment` (13 typed slot faces, sited D-SC defs) | structure decl; E-phase binder resolution per §1.3 duty note | MovesU.SlotsG2–G10, G18 | MECH | §1.3; U10 residual-bare-rows docstring |
| VI-B4 | Scaffold/CorpusBridge.lean | `rootC_fired_at_slots` — VI-B2 with the 13 Props := the sited defs, hypotheses from `SA` | apply VI-B2 with `rel1 := RelRow_rel1 RP` etc., `hrel1 := SA.rel1` … | VI-B2, VI-B3 | MECH | §1.3 |
| VI-N1 | Scaffold/AnchorN2.lean | `AnchorN2` bundle + `anchor_n2` (montes_uniform_n2 repackaged) | `refine ⟨?_, ?_⟩ <;> exact (montes_uniform_n2 σ hσ).…` | VI-S1 (shape only); OM.UniformCapstone | EASY | §1.4; ROOT §1 verified-instances block |
| VI-N2 | Scaffold/AnchorN2.lean | `anchor_n2_drainage` (hExhaust_n2 re-fired) | `exact hExhaust_n2` | OM.SeriesAssembly | MECH | §1.4 |
| VI-N3 | Scaffold/AnchorN2.lean | order-0 value/separation gates re-fired (4 `example`s) | `exact gate_v2_…` each | OM.RealInstanceV2Gates | MECH | §1.4 |
| VI-A1 | Scaffold/AxChk.lean | `#print axioms` census, scaffold decls + quarry (§1.5 list) | `#print axioms` lines only | ALL landed VI units | MECH | §1.5 |

Estimated: 15 waved units (12 MECH, 3 EASY), 0 sorries introduced at any point —
every unit compiles green in isolation; there is NO H-phase debt in this
movement. The genuinely hard integration content (VI-F1) is deliberately future:
it cannot be stated before the divisions' step statements exist.

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
  VI-H2 → VI-H3 (one prover, sequential — single file) ∥ VI-S1 → VI-S2 (second
  prover). Gate: file-level `lake env lean`; announce `RootHyps` field names +
  `RootC` to all division leads on landing.
* **Wave VI-1:** VI-S3, VI-B1 (after VI-0) → VI-B2 → VI-B3 → VI-B4 (B3 can run
  parallel to B1/B2; B4 last). Gate: per-file build + the §1.3 E-phase binder
  resolutions recorded in the module header for Codex audit.
* **Wave VI-2 (parallel to VI-1):** VI-N1, VI-N2, VI-N3 (independent provers).
* **Wave VI-3 (checkpoint):** VI-A1; then division checkpoint = full
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
  field list vs ROOT §3.1 (row-for-row); `ClauseRHyps`/`ClauseUBHyps` vs the
  (ROOT-C) attribution display; `PrimeConclusion`/`RootC` vs theoremU's
  conclusion (no strengthening, no weakening); the §1.3 `SlotAssignment` keying
  resolutions; the §1.5 census list vs the ledger's ~40-unit quarry.
* Standing honesty rule for every consumer: `RootC`-family theorems inherit
  theoremU_fired's conditionality record; `RootHyps` presence is UNPINNED until
  field refinement — no acceptance claim may read either as discharged.
