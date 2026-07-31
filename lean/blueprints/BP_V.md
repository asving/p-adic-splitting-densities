# BP_V — Movement V: THE ASSEMBLY SPINE (ROOT Step 19 + the (ROOT-C) statement)

**Blueprint architect:** movement-V agent of the Lean conversion swarm (authority: ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"AUTHORITY (Asvin, 2026-08-03): THE LEAN
CONVERSION SWARM"; scaffold form per §"AUTHORITY (Asvin, 2026-08-01): THE PROOF SCAFFOLD").
**Source of truth:** `docs/ROOT_ASSEMBLY_2026-08-02.md` at **REVISION 5** — §1 (the
(ROOT-C) display + per-clause hypothesis attribution), §2 Step 19 (the closer), §3.1 (the
[M] rows = (H1)…(H6)). Leaf briefs: `lean/notes/openmath/` (consulted for row content
pins; the spine never transcribes leaf proofs).
**Status of this file:** KEYSTONE blueprint. No BP_I…BP_IV existed at write time
(`lean/blueprints/` created by this file), so §1's interface structures are the CANONICAL
interfaces the other four movements must instantiate; §5 records the reconciliation duty.

## 0. Design summary and ground-rule compliance

**What Movement V builds.** The top-level theorem `LeanUrat.Scaffold.rootC` in Asvin's
scaffold form: fix a degree `n ≥ 2`; per prime `p` the type-τ density is DEFINED as the
limit of level-`k` cylinder counts (the corpus `CountingModel` reading — exactly the
2026-08-01 scaffold authority: "define the p-adic density … as a limit of cylinders …
then prove the squeeze lemma … depending on k"); the theorem takes the §3.1 [M] rows as
NAMED HYPOTHESIS ARROWS `(h1 : …) → … → (h6d : …)` and concludes the four (ROOT-C)
clauses: **(0)** cylinder-limit density, **(SQ)** the level-`k` two-sided squeeze +
drainage + bracket uniqueness, **(R)** `α(n,τ;p) = R_τ(p)` at EVERY prime with
`R_τ ∈ ℛ` and `Σ_τ R_τ = 1` identically, **(UB)** the same `R_τ` at `q ↦ p^δ`.
Per-clause attribution is preserved EXACTLY as ROOT §1 displays it (REVISION 4/5 form):
clauses (0)+(SQ) are theorems with NO hypothesis-row arguments; clause (R) consumes
(H1)–(H3) + (H4a) + (K3-δ) + (H5) + (H6); clause (UB) consumes (H1)–(H3) + (H4a) +
(H4b) + (H5) + (H6). The Σ_τ R_τ = 1 identity is CONCLUDED at the spine (ROOT REVISION
3, finding B3: Step 1 supplies Σ_τ α = 1 + interpolation; Steps 18/18b supply α = R_τ;
the identity lands inside clause (R)'s conditional scope) — units BPV-13…BPV-17.

**Ground rules honored.**
- New modules ONLY under `lean/LeanUrat/Scaffold/`; namespace `LeanUrat.Scaffold`.
- NO existing statement touched; parked items 22–29 untouched; corpus reuse BY IMPORT.
- NO new axioms. The [M] hypotheses enter as named `Prop` fields of `HypRows` (§1.2) —
  the honest conditionality, mirroring the `htameFE` precedent.
- Every unit ≤ ~40 lines; minimality is the design goal (31 units, most MECH/EASY).
- Math-revision sync duty: `HypRows` is the SINGLE point of change if VC6+ revises the
  §3.1 row set; this blueprint's owner folds any ROOT revision delta (§5.3).

**Design decisions a reviewer should check first.**
1. *The density carrier is `LeanUrat.CountingModel.CountingModel q n`* (the existing
   proved squeeze layer: `decidedMeasure`, `undecided`, `countingDensity`,
   `density_isLimit`, `decided_le_density`, `density_le_decided_add_undecided`,
   `decidedMeasure_sum_add_undecided`, `UndecidedVanishes`,
   `countingDensity_is_squeezed_limit`). Clause (0) in the spine is the `Tendsto`
   statement; the Haar-measure identification `μ(L_τ) = lim` (Dfloor's D-1) is Movement
   I's enrichment (§5.1, `PadicMeasure.lean` quarry), NOT a spine obligation — per the
   scaffold authority the spine's density IS the cylinder limit.
2. *ℛ is the corpus `LeanUrat.MovesU.MemRcyc`* (`O12PoleFree.lean`): membership gives
   pole-freeness at every rational ≥ 2, hence at every prime power (`MemRcyc.definedAt`,
   `MemRcyc.eval_ne_zero_of_inv`), and base change `q ↦ q^δ` (`MemRcyc.powSubst`).
3. *Hypothesis rows are `Prop`-valued FIELDS, content-free at the spine.* The spine
   never inspects them; Movements III/IV instantiate them with their real statements
   (§5.2). The (K3-δ) ⊆ (H4b) containment is a structure LAW (`k3d_of_ubx`), so clause
   (R) can consume the fragment while the joint theorem takes only (H4b) — exactly the
   REVISION-4 finding VC4-1 bookkeeping.
4. *(UB) is packaged as data* (`UBWitness`: the `CountingModel (p^δ) n` family over the
   unramified base + its evaluation), delivered by Movement IV as a FUNCTION from the
   hypothesis bundle (`ub : HypUB H → UBWitness …`) — the honest Lean form of a
   conditional deliverable, since even the δ>1 limit existence is conditional content.
5. *The n = 2 instance corollary `rootC_n2` is UNCONDITIONAL* (hypothesis rows
   instantiated to `True`), tying the spine to the existing capstone
   `OM.UniformCapstone.montes_uniform_n2` / `M7` / `hExhaustP` — the spine's
   non-vacuity gate. Its honest scope: clauses (0)+(SQ)+(R) only — the Lean n = 2
   corpus has NO unramified-base layer, so no `UBWitness` at n = 2 (displayed, §1.7).

---

## 1. THE STATEMENT LAYER (exact Lean signature sketches)

Convention: signatures are E-phase sketches — binder/elaboration fixes allowed, MEANING
frozen (statement-fence discipline: any semantic change goes back through this file).
`open LeanUrat.CountingModel LeanUrat.MovesU` is assumed inside `namespace
LeanUrat.Scaffold`; `CountingModel` below means `LeanUrat.CountingModel.CountingModel`,
`FactorizationType` means `LeanUrat.FactorizationType`.

### 1.1 `Scaffold/Defs.lean` — shared foundations (BPV-01)

```lean
namespace LeanUrat.Scaffold

/-- Evaluation of `g ∈ ℚ(q)` at `x : ℚ` — the corpus reading (`RatFunc.eval` along
`RingHom.id ℚ`; junk value at poles, which `MemRcyc.definedAt` fences off ≥ 2). -/
noncomputable def evalQ (g : RatFunc ℚ) (x : ℚ) : ℚ := g.eval (RingHom.id ℚ) x

/-- A splitting type of degree `n`: every `(e, f)` part positive and `Σ eᵢfᵢ = n`
(ROOT §1's τ; the honest quantifier for menu completeness — §1.3, §5.1). -/
def IsSplittingType (n : ℕ) (σ : FactorizationType) : Prop :=
  σ.degree = n ∧ ∀ pr ∈ σ.data, 1 ≤ pr.1 ∧ 1 ≤ pr.2

theorem evalQ_one (x : ℚ) : evalQ 1 x = 1
theorem evalQ_algebraMap (P : Polynomial ℚ) (x : ℚ) :
    evalQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) P) x = P.eval x
```

### 1.2 `Scaffold/Hypotheses.lean` — the (ROOT-C) hypothesis rows (BPV-02..04)

The §3.1 [M] table, one named `Prop` field per row. Field ↔ row ↔ hypothesis map
(displayed; THE sync point for ROOT revisions):

| field      | ROOT §3.1 row                            | (ROOT-C) hypothesis |
|------------|------------------------------------------|---------------------|
| `grB`      | (GR-B) at OM orders ≥ 2                  | (H1)                |
| `fresh`    | (FRESH)                                  | (H2)                |
| `d12r`     | D-12r (TB-CAP (τ-irr) perimeter)         | (H3), row 1         |
| `eN`       | (E-N) (O-1thr Thm 3(c) exhaustion caveat)| (H3), row 2         |
| `adm`      | (ADM), O-9 census FULL attainment (r4)   | (H3), row 3         |
| `r14`      | (R1)–(R4) over `O_δ = W(F_{p^δ})`        | (H4a)               |
| `ubx`      | (UB-X) (a)+(b)+(c), the clause-(UB) residue | (H4b)            |
| `k3d`      | (K3-δ) = (UB-X)(b) at K3-c's realized pools | fragment of (H4b), consumed by clause (R) |
| `pack`     | (PACK), the actual-pack correspondence   | (H5)                |
| `tDec`     | (T-DEC) (CU-2t terminal row, dec+corner) | (H6), row (a1)      |
| `tRead`    | (T-READ) (the (RC-read) supply)          | (H6), row (a2)      |
| `tVerd`    | (T-VERD) (terminal verdict conformance)  | (H6), row (a3)      |
| `fenceVii` | D-11 widened-charge item (vii) (H.6 in-fence conformance) | (H6), row (b) |

```lean
/-- **The (ROOT-C) hypothesis rows** (ROOT §3.1, REVISION 5). Content-free `Prop`
slots at the spine; Movements III/IV pin the real statements (§5.2). The single
law `k3d_of_ubx` records (K3-δ) ⊆ (UB-X) [ROOT finding VC4-1]. -/
structure HypRows (n : ℕ) where
  grB      : Prop
  fresh    : Prop
  d12r     : Prop
  eN       : Prop
  adm      : Prop
  r14      : Prop
  ubx      : Prop
  k3d      : Prop
  k3d_of_ubx : ubx → k3d
  pack     : Prop
  tDec     : Prop
  tRead    : Prop
  tVerd    : Prop
  fenceVii : Prop

/-- Clause (R)'s EXACT hypothesis set: (H1)–(H3) + (H4a) + (K3-δ) + (H5) + (H6)
[ROOT §1, REVISION 5 display]. NOTE: (H4b) itself is ABSENT — only its (K3-δ)
fragment enters clause (R). -/
structure HypR {n : ℕ} (H : HypRows n) : Prop where
  h1  : H.grB
  h2  : H.fresh
  h3a : H.d12r
  h3b : H.eN
  h3c : H.adm
  h4a : H.r14
  hk3 : H.k3d
  h5  : H.pack
  h6a : H.tDec
  h6b : H.tRead
  h6c : H.tVerd
  h6d : H.fenceVii

/-- Clause (UB)'s EXACT hypothesis set: (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6). -/
structure HypUB {n : ℕ} (H : HypRows n) : Prop where
  h1  : H.grB
  h2  : H.fresh
  h3a : H.d12r
  h3b : H.eN
  h3c : H.adm
  h4a : H.r14
  h4b : H.ubx
  h5  : H.pack
  h6a : H.tDec
  h6b : H.tRead
  h6c : H.tVerd
  h6d : H.fenceVii

/-- (UB)'s set covers (R)'s: the (K3-δ) leg via the containment law. -/
theorem HypUB.toHypR {n : ℕ} {H : HypRows n} (h : HypUB H) : HypR H
```

### 1.3 `Scaffold/Interfaces.lean` — Movements I/II/III plug in here (BPV-05)

```lean
/-- **MOVEMENT I output (Steps 1–3): the measure floor.** Per prime the SEMANTIC
counting model (decided/undecided level-k counts, box partition, monotone decided
measures, the decided limit = the density), plus the p-FREE type menu (Step 3
skeleton/menu finiteness). Instances: n = 2 from `OM.UniformCapstone.M7` (§1.7);
general n = BP_I's obligation. -/
structure FloorData (n : ℕ) where
  M : (p : ℕ) → p.Prime → CountingModel p n
  menu : Finset FactorizationType
  menu_eq : ∀ p hp, (M p hp).typeMenu = menu
  menu_degree : ∀ σ ∈ menu, σ.degree = n

/-- OPTIONAL Movement-I enrichment (NOT consumed by `rootC`): the menu contains
every splitting type — carries ROOT §1's "each splitting type τ" quantifier. -/
def MenuComplete {n : ℕ} (F : FloorData n) : Prop :=
  ∀ σ, IsSplittingType n σ → σ ∈ F.menu

/-- **MOVEMENT I (Step 2, T-8) + MOVEMENT II (Steps 4–5) output: the solve values
with the ℛ-discipline.** `R σ` is the τ-entry of the block solve at the intended
family 𝔅_n; `memR` is O-12's pole-freeness packaged through the corpus route
`AbsSolveTable.RcycDiscipline` (BP_II discharges it; the spine only consumes
membership). -/
structure SolveData (n : ℕ) where
  R : FactorizationType → RatFunc ℚ
  memR : ∀ σ, MemRcyc (R σ)

/-- **MOVEMENT III output (Step 13, SEMANTIC layer): drainage at every prime,
UNCONDITIONAL** — `undec(k) → 0` for the semantic classifier (ROOT: clause (SQ)
consumes NO §3.1 row; the classifier-TRANSFER layer is Movement IV territory and
never enters this structure). -/
structure DrainData {n : ℕ} (F : FloorData n) : Prop where
  vanish : ∀ p (hp : p.Prime), UndecidedVanishes (F.M p hp)
```

### 1.4 `Scaffold/ValueIface.lean` — Movement IV plugs in here (BPV-06)

```lean
/-- **The packaged (UB) conclusion**: the counting-model family over the degree-δ
unramified base (residue size `p^δ`), same menu, drained, evaluating to the SAME
`R_τ` at `q = p^δ`. Data (not Prop): the base-change models are part of the claim. -/
structure UBWitness (n : ℕ) (F : FloorData n) (S : SolveData n) where
  Mδ : (p δ : ℕ) → p.Prime → 2 ≤ δ → CountingModel (p ^ δ) n
  menu_eq : ∀ p δ hp hδ, (Mδ p δ hp hδ).typeMenu = F.menu
  vanish : ∀ p δ hp hδ, UndecidedVanishes (Mδ p δ hp hδ)
  eval : ∀ p δ hp hδ, ∀ σ ∈ F.menu,
    (Mδ p δ hp hδ).countingDensity σ = evalQ (S.R σ) ((p ^ δ : ℕ) : ℚ)

/-- **MOVEMENT IV output (Steps 14–18b): the evaluation chain.** `alpha_eq` = the
composed Step-18 (series = R_τ) + Step-18b (α = series) tie, conditional on
EXACTLY clause (R)'s hypothesis set. -/
structure ValueData (n : ℕ) (F : FloorData n) (S : SolveData n) (H : HypRows n) where
  alpha_eq : HypR H → ∀ p (hp : p.Prime), ∀ σ ∈ F.menu,
    (F.M p hp).countingDensity σ = evalQ (S.R σ) (p : ℚ)

/-- Movement IV's full package: the value chain + the conditional (UB) witness
(Step 16's clause at its displayed scope, as a FUNCTION from the hypothesis
bundle — the honest form of a conditional deliverable). -/
structure ValueDataUB (n : ℕ) (F : FloorData n) (S : SolveData n) (H : HypRows n)
    extends ValueData n F S H where
  ub : HypUB H → UBWitness n F S
```

### 1.5 `Scaffold/Conclusions.lean` — the clause bundles (BPV-07)

```lean
/-- **Clauses (0) + (SQ), bundled** (ROOT §1; UNCONDITIONAL — consumes no §3.1 row).
`limit` = clause (0) in the scaffold reading (the density IS the cylinder limit);
`lower`/`upper` = the two-sided level-k squeeze; `drain` = undec(k) → 0; `unique` =
bracket uniqueness (the `montes_uniform_n2` closer shape: any value bracketed at
every level ≥ 1 IS the density). -/
structure ClauseZeroSQ {n : ℕ} (F : FloorData n) : Prop where
  limit : ∀ p hp σ, Filter.Tendsto ((F.M p hp).decidedMeasure σ) Filter.atTop
            (nhds ((F.M p hp).countingDensity σ))
  lower : ∀ p hp σ N, (F.M p hp).decidedMeasure σ N ≤ (F.M p hp).countingDensity σ
  upper : ∀ p hp σ N, (F.M p hp).countingDensity σ
            ≤ (F.M p hp).decidedMeasure σ N + (F.M p hp).undecided N
  drain : ∀ p hp, Filter.Tendsto (F.M p hp).undecided Filter.atTop (nhds 0)
  unique : ∀ p hp σ d,
      (∀ N, 1 ≤ N → (F.M p hp).decidedMeasure σ N ≤ d ∧
        d ≤ (F.M p hp).decidedMeasure σ N + (F.M p hp).undecided N) →
      d = (F.M p hp).countingDensity σ

/-- **Clause (R), bundled**: ℛ-membership, the evaluation `α(n,τ;p) = R_τ(p)` at
EVERY prime (wild included — `p` ranges over ALL primes), and `Σ_τ R_τ = 1`
identically in `ℚ(q)`. -/
structure ClauseR {n : ℕ} (F : FloorData n) (S : SolveData n) : Prop where
  memR : ∀ σ ∈ F.menu, MemRcyc (S.R σ)
  eval : ∀ p (hp : p.Prime), ∀ σ ∈ F.menu,
    (F.M p hp).countingDensity σ = evalQ (S.R σ) (p : ℚ)
  sum : (∑ σ ∈ F.menu, S.R σ) = 1
```

### 1.6 `Scaffold/SqueezeCore.lean`, `Scaffold/SumOne.lean`, `Scaffold/RootC.lean` — the theorems (BPV-08..21)

```lean
-- SqueezeCore.lean (unconditional; pure corpus re-exposure + two small lemmas)
theorem clause_limit {n} (F : FloorData n) : ∀ p hp σ, Filter.Tendsto …      -- BPV-09
theorem clause_lower/clause_upper …                                          -- BPV-08
theorem bracket_unique {q n : ℕ} (M : CountingModel q n)
    (hU : UndecidedVanishes M) (σ : FactorizationType) (d : ℚ)
    (hbr : ∀ N, 1 ≤ N → M.decidedMeasure σ N ≤ d ∧
      d ≤ M.decidedMeasure σ N + M.undecided N) :
    d = M.countingDensity σ                                                  -- BPV-10
/-- **Clauses (0)+(SQ) hold, hypothesis-free** — ROOT finding VC4-4 in Lean. -/
theorem clauseZeroSQ_holds {n} (F : FloorData n) (D : DrainData F) :
    ClauseZeroSQ F                                                           -- BPV-11
/-- Step 1's Σ_τ α = 1 at every prime (counting form). -/
theorem sum_alpha_one {n} (F : FloorData n) (D : DrainData F)
    (p : ℕ) (hp : p.Prime) :
    (∑ σ ∈ F.menu, (F.M p hp).countingDensity σ) = 1                         -- BPV-12

-- SumOne.lean (the Step-19 Σ_τ R_τ = 1 derivation, ROOT finding B3)
theorem memRcyc_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ)
    (h : ∀ i ∈ s, MemRcyc (f i)) : MemRcyc (∑ i ∈ s, f i)                    -- BPV-13
theorem evalQ_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ)
    (h : ∀ i ∈ s, MemRcyc (f i)) {x : ℚ} (hx : 2 ≤ x) :
    evalQ (∑ i ∈ s, f i) x = ∑ i ∈ s, evalQ (f i) x                          -- BPV-14
theorem primesQ_infinite :
    Set.Infinite ((fun p : ℕ => (p : ℚ)) '' {p | p.Prime})                   -- BPV-15
/-- The interpolation closer: an ℛ-element equal to 1 at every prime is 1. -/
theorem memRcyc_eq_one_of_eval_primes {f : RatFunc ℚ} (hf : MemRcyc f)
    (h : ∀ p : ℕ, p.Prime → evalQ f (p : ℚ) = 1) : f = 1                     -- BPV-16
/-- **Σ_τ R_τ = 1 in ℚ(q)** — concluded HERE, inside clause (R)'s scope. -/
theorem sum_R_eq_one {n} {H : HypRows n} (F : FloorData n) (S : SolveData n)
    (D : DrainData F) (V : ValueData n F S H) (h : HypR H) :
    (∑ σ ∈ F.menu, S.R σ) = 1                                                -- BPV-17

-- RootC.lean (the composition; per-clause attribution preserved)
/-- **Clause (R)** from EXACTLY its displayed hypothesis set (named arrows). -/
theorem clauseR_of_hyps {n} {H : HypRows n} (F : FloorData n) (S : SolveData n)
    (D : DrainData F) (V : ValueData n F S H)
    (h1 : H.grB) (h2 : H.fresh) (h3a : H.d12r) (h3b : H.eN) (h3c : H.adm)
    (h4a : H.r14) (hk3 : H.k3d) (h5 : H.pack)
    (h6a : H.tDec) (h6b : H.tRead) (h6c : H.tVerd) (h6d : H.fenceVii) :
    ClauseR F S                                                              -- BPV-18
/-- **Clause (UB)** from exactly its displayed set (with (H4b), not (K3-δ)). -/
theorem clauseUB_of_hyps {n} {H : HypRows n} {F S}
    (V : ValueDataUB n F S H)
    (h1 : H.grB) (h2 : H.fresh) (h3a : H.d12r) (h3b : H.eN) (h3c : H.adm)
    (h4a : H.r14) (h4b : H.ubx) (h5 : H.pack)
    (h6a : H.tDec) (h6b : H.tRead) (h6c : H.tVerd) (h6d : H.fenceVii) :
    Nonempty (UBWitness n F S)                                               -- BPV-19

/-- **(ROOT-C), the composed theorem** — Asvin's form: the hypothesis rows as
named arrows, concluding the cylinder-density squeeze + the R_τ evaluation at
every prime + Σ = 1 + (UB). `_hn` is statement fidelity (ROOT fixes n ≥ 2). -/
theorem rootC {n : ℕ} (_hn : 2 ≤ n) (H : HypRows n)
    (F : FloorData n) (S : SolveData n)
    (D : DrainData F) (V : ValueDataUB n F S H)
    (h1 : H.grB) (h2 : H.fresh)
    (h3a : H.d12r) (h3b : H.eN) (h3c : H.adm)
    (h4a : H.r14) (h4b : H.ubx) (h5 : H.pack)
    (h6a : H.tDec) (h6b : H.tRead) (h6c : H.tVerd) (h6d : H.fenceVii) :
    ClauseZeroSQ F ∧ ClauseR F S ∧ Nonempty (UBWitness n F S)                -- BPV-20

-- Corollaries (BPV-21)
/-- The Σ = 1 corollary, standalone (conditional exactly as clause (R)). -/
theorem rootC_sum_one … : (∑ σ ∈ F.menu, S.R σ) = 1
/-- The hypothesis-free half, standalone: (0)+(SQ) need NO row. -/
theorem rootC_unconditional_half {n} (F : FloorData n) (D : DrainData F) :
    ClauseZeroSQ F
```

### 1.7 `Scaffold/InstanceN2.lean`, `Scaffold/InstanceN3.lean` — the instance corollaries (BPV-22..30)

```lean
-- InstanceN2.lean — ties to the VERIFIED-LEAN capstone (all-primes n = 2)
open LeanUrat.OM.UniformCapstone in
/-- The n = 2 solve values as `ℚ(q)` elements: `R_ram = 1/(q+1)`,
`R_inert = R_split = q/(2(q+1))` (`uniformNum/uniformDen`; 0 off the menu). -/
noncomputable def R2 (σ : FactorizationType) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (uniformNum σ) /
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (uniformDen σ)
theorem memRcyc_R2 (σ : FactorizationType) : MemRcyc (R2 σ)                  -- BPV-22
noncomputable def solveData2 : SolveData 2 := ⟨R2, memRcyc_R2⟩
noncomputable def floorData2 : FloorData 2   -- M := fun p hp => @M7 p ⟨hp⟩  -- BPV-23
theorem drainData2 : DrainData floorData2    -- from hExhaustP               -- BPV-24
theorem alphaEq2 : ∀ p (hp : p.Prime), ∀ σ ∈ floorData2.menu,
    (floorData2.M p hp).countingDensity σ = evalQ (R2 σ) (p : ℚ)             -- BPV-25
/-- All rows True: the n = 2 chain is unconditional. -/
def hypRows2 : HypRows 2      -- every field := True; law := id
noncomputable def valueData2 : ValueData 2 floorData2 solveData2 hypRows2
/-- **THE NON-VACUITY GATE: (ROOT-C) at n = 2, UNCONDITIONAL** — clauses
(0)+(SQ)+(R) of the spine, discharged from the existing capstone. Honest scope:
no `UBWitness` at n = 2 (the Lean corpus has no unramified-base layer). -/
theorem rootC_n2 : ClauseZeroSQ floorData2 ∧ ClauseR floorData2 solveData2   -- BPV-26
-- Gates (BPV-27): Σ_{menu} R2 = 1 via rootC_n2 (consistency with
-- gate_uniform_checksum); the wild prime included: instantiate clauses at p = 2;
-- value spot-check evalQ (R2 ramType2) 2 = 1/3 by norm_num-style evaluation.

-- InstanceN3.lean — statement layer + symbolic gates; the density tie is FUTURE
-- (no Lean n = 3 model exists; the corollary is honestly conditional on BP_I/IV
-- delivering the n = 3 instances).
noncomputable def n3Menu : Finset FactorizationType   -- the five degree-3 types
noncomputable def R3 : FactorizationType → RatFunc ℚ  -- TRANSCRIBED, source-pinned:
  -- the RESUM-n3 five-type symbolic table (verification/openmath/
  -- o11_seriestie_check.py + the RESUM-n3 sealed record); NOT invented here.
theorem memRcyc_R3 (σ : FactorizationType) : MemRcyc (R3 σ)                  -- BPV-29
theorem sum_R3_eq_one : (∑ σ ∈ n3Menu, R3 σ) = 1   -- the symbolic Σ gate     -- BPV-29
/-- The n = 3 corollary SHAPE (MECH once BP_I/BP_IV land their n = 3 data). -/
theorem rootC_n3_of_instances (F : FloorData 3) (hmenu : F.menu = n3Menu)
    (D : DrainData F) {H : HypRows 3} (V : ValueData 3 F ⟨R3, memRcyc_R3⟩ H)
    (h : HypR H) : ClauseZeroSQ F ∧ ClauseR F ⟨R3, memRcyc_R3⟩               -- BPV-30
```

### 1.8 `Scaffold/AxChk.lean` — the axiom census (BPV-31)

`#print axioms` for `rootC`, `rootC_n2`, `sum_R_eq_one`, `clauseZeroSQ_holds`,
`memRcyc_eq_one_of_eval_primes` — expected footprint: Lean core only
(`propext, Classical.choice, Quot.sound`); any regression is stop-the-line.

---

## 2. THE UNIT TABLE

Difficulty: MECH < EASY < MED < HARD. Every unit ≤ ~40 lines of Lean (docstrings
included in spirit, not in the count). "Corpus" column lists imports beyond earlier
units; full names in §3. Source ¶ = ROOT_ASSEMBLY_2026-08-02.md locus.

| id | module | statement (name, §1 sketch) | proof sketch | deps | diff | source ¶ |
|----|--------|------------------------------|--------------|------|------|----------|
| BPV-01 | Defs | `evalQ`, `IsSplittingType`, `evalQ_one`, `evalQ_algebraMap` | defs; `RatFunc.eval` unfold + `Polynomial.eval₂_id`; `eval_one` simp | corpus: MovesU.Defs, Interface, CountingModel | MECH | §1 preamble |
| BPV-02 | Hypotheses | `HypRows` (14 fields incl. law) | structure only, docstrings = the §1.2 table | BPV-01 | MECH | §3.1 all rows |
| BPV-03 | Hypotheses | `HypR` | Prop structure, 12 fields | BPV-02 | MECH | §1 (R)-attribution |
| BPV-04 | Hypotheses | `HypUB` + `HypUB.toHypR` | Prop structure; `toHypR` := fields + `H.k3d_of_ubx h.h4b` | BPV-02,03 | MECH | §1 (UB)-attribution |
| BPV-05 | Interfaces | `FloorData`, `MenuComplete`, `SolveData`, `DrainData` | structures/def only | BPV-01 | MECH | §2 Steps 1–5, 13 |
| BPV-06 | ValueIface | `UBWitness`, `ValueData`, `ValueDataUB` | structures only | BPV-02..05 | MECH | §2 Steps 14–18b, 16 |
| BPV-07 | Conclusions | `ClauseZeroSQ`, `ClauseR` | Prop structures only | BPV-05 | MECH | §1 clauses (0)(SQ)(R) |
| BPV-08 | SqueezeCore | `clause_lower`, `clause_upper` | = `decided_le_density`, `density_le_decided_add_undecided` through `F.M` | BPV-05; corpus: CountingModel | MECH | §1 (SQ) |
| BPV-09 | SqueezeCore | `clause_limit` | = `density_isLimit` through `F.M` | BPV-05 | MECH | §1 (0) |
| BPV-10 | SqueezeCore | `bracket_unique` | `le_antisymm`: lower leg `le_of_tendsto'` of `density_isLimit` against `hbr.1` eventually (N ≥ 1); upper leg `ge_of_tendsto` of `countingDensity_is_squeezed_limit hU` against `hbr.2` | corpus: CountingModel | EASY-MED | §2 Step 19 "squeezes" |
| BPV-11 | SqueezeCore | `clauseZeroSQ_holds` | assemble BPV-08/09/10 + `D.vanish`; `unique` from BPV-10 | BPV-07..10 | MECH | §1 (0)+(SQ) unconditional [VC4-4] |
| BPV-12 | SqueezeCore | `sum_alpha_one` | `tendsto_finset_sum` of `density_isLimit` `.add D.vanish`; constant sequence 1 by `decidedMeasure_sum_add_undecided` + `F.menu_eq`; `tendsto_nhds_unique` | BPV-05; corpus: CountingModel | EASY-MED | §2 Step 1 Delivers; Step 19 Σ-derivation input |
| BPV-13 | SumOne | `memRcyc_sum` | `Finset.cons_induction`; `memRcyc_zero`, `MemRcyc.add` | corpus: O12PoleFree | EASY | §2 Step 19 Σ_τ R_τ = 1 |
| BPV-14 | SumOne | `evalQ_sum` | cons induction; step = mathlib `RatFunc.eval_add` with denom-nonzero sides from `MemRcyc.definedAt hx` + BPV-13 for the partial sum; `Polynomial.eval₂_id` plumbing | BPV-01,13 | MED | same |
| BPV-15 | SumOne | `primesQ_infinite` | `Nat.infinite_setOf_prime.image` + injectivity of `Nat.cast : ℕ → ℚ` | mathlib | MECH | §2 Step 19 "infinitely many prime powers" |
| BPV-16 | SumOne | `memRcyc_eq_one_of_eval_primes` | apply `L7.ratfunc_agree_of_infinite f.num f.denom 1 1` on the prime image set (BPV-15); denom-nonzero from `MemRcyc.definedAt` (each (p:ℚ) ≥ 2); agreement = `evalQ` unfold; conclude `f.num = f.denom` ⇒ `f = 1` via `RatFunc.num_div_denom` | BPV-01,15; corpus: L7, O12PoleFree | MED | §2 Step 19 interpolation [B3] |
| BPV-17 | SumOne | `sum_R_eq_one` | per prime: BPV-12 + `V.alpha_eq h` rewrite gives Σ evalQ (R σ) p = 1; BPV-13/14 package Σ as one ℛ-element evaluating to 1 (note (p:ℚ) ≥ 2 from `hp.two_le`); close with BPV-16 | BPV-12..16, BPV-06 | EASY | §2 Step 19 Σ_τ R_τ = 1 [B3] |
| BPV-18 | RootC | `clauseR_of_hyps` | `HypR.mk` from the 12 arrows; `ClauseR.mk (fun σ _ => S.memR σ) (V.alpha_eq ⟨…⟩) (sum_R_eq_one …)` | BPV-03,06,07,17 | EASY | §1 (R)-attribution |
| BPV-19 | RootC | `clauseUB_of_hyps` | `⟨V.ub ⟨12 arrows⟩⟩` | BPV-04,06 | MECH | §1 (UB)-attribution |
| BPV-20 | RootC | `rootC` | `⟨clauseZeroSQ_holds F D, clauseR_of_hyps … (H.k3d_of_ubx h4b) …, clauseUB_of_hyps …⟩` | BPV-11,18,19 | EASY | §1 (ROOT-C); §2 Step 19 |
| BPV-21 | RootC | `rootC_sum_one`, `rootC_unconditional_half` | projections/aliases of BPV-17/BPV-11 with the named-arrow interface | BPV-11,17 | MECH | §1 (ROOT-C); task charge "Sigma=1 corollary" |
| BPV-22 | InstanceN2 | `R2`, `memRcyc_R2`, `solveData2` | per menu case exhibit (P, s ∈ cycS): ram = (X−1, X²−1), inert/split = ((X²−X)/2 scaled, X²−1) via `Xpow_sub_one_mem_cycS`; off-menu 0/1 by `memRcyc_zero`-type simp; the MemRcyc form is `alg(s)·f = alg(P)` — clear denominators with `RatFunc.algebraMap_ne_zero` | BPV-01,05; corpus: UniformCapstone, O12PoleFree | MED | §1 "Verified instances"; capstone §H |
| BPV-23 | InstanceN2 | `floorData2` | `M := fun p hp => @M7 p ⟨hp⟩`; `menu := typeMenuP`; `menu_eq := rfl`; degree from the M7 field | BPV-05; corpus: UniformCapstone, UniformModelN2 | EASY | capstone §H |
| BPV-24 | InstanceN2 | `drainData2` | `UndecidedVanishes (M7 p)` unfolds to `hExhaustP p` (n·N = 2·N alignment by `show`/`simp`) | BPV-23; corpus: UniformCapstone | MECH-EASY | capstone §E |
| BPV-25 | InstanceN2 | `alphaEq2` | `countingDensity = uniformValueFn σ p` (defeq via `densityVal`); `uniformValueFn_eq_eval`; bridge to `evalQ (R2 σ)` by `MovesU.eval_ratio` with `uniformDen_eval_ne` (0 < p) | BPV-22,23; corpus: UniformCapstone, O12PoleFree | MED | capstone (V) clause |
| BPV-26 | InstanceN2 | `hypRows2`, `valueData2`, `rootC_n2` | all rows `True`; `HypR` by `trivial`s; assemble `clauseZeroSQ_holds floorData2 drainData2` + `clauseR_of_hyps` | BPV-11,18,22..25 | EASY | §1 verified-instances ¶; non-vacuity discipline (repo CLAUDE.md) |
| BPV-27 | InstanceN2 | gates: `gate_sum_R2`, `gate_wild_p2`, `gate_R2_ram_at_2` | project `rootC_n2.2.sum`; instantiate at p = 2 (`Nat.prime_two`); `evalQ (R2 ramType2) 2 = 1/3` by `eval_ratio` + `norm_num` | BPV-26 | MECH | capstone gates ¶ |
| BPV-28 | InstanceN3 | `n3Menu`, `R3` (defs, source-pinned transcription) | transcribe the five degree-3 types + their `ℚ(q)` values from the RESUM-n3 sealed record / `o11_seriestie_check.py` (leaf brief pins exact strings); FIDELITY RISK — falsifier is BPV-29 | BPV-01 | MED | §1 verified-instances ¶ (RESUM-n3 65/65) |
| BPV-29 | InstanceN3 | `memRcyc_R3`, `sum_R3_eq_one` | five MemRcyc witnesses (cyclotomic denominators); Σ = 1 as a `RatFunc ℚ` identity: `field_simp`/`ring` after clearing the five denominators | BPV-13,28 | MED-HARD | same |
| BPV-30 | InstanceN3 | `rootC_n3_of_instances` | instance of BPV-11 + BPV-18 with `hmenu` rewrite | BPV-11,18,28,29 | MECH | §6 next-actions (n = 3 instance) |
| BPV-31 | AxChk | `Scaffold/AxChk.lean` census | `#print axioms` block per §1.8 | BPV-20,26 | MECH | repo axiom policy |

---

## 3. THE CORPUS-REUSE MAP

Which existing PROVED declarations discharge which units (reuse strictly BY IMPORT; no
existing file is edited). Verified against HEAD at blueprint time.

| corpus declaration (full name, module) | discharges / feeds |
|---|---|
| `LeanUrat.CountingModel.CountingModel` + fields (`CountingModel.lean`) | the density carrier of §1.3; BPV-05/06/07 |
| `….CountingModel.decidedMeasure`, `.undecided`, `.countingDensity` | the (0)/(SQ) vocabulary; BPV-07..12 |
| `….CountingModel.density_isLimit` | BPV-09 (clause (0)) |
| `….CountingModel.decided_le_density` | BPV-08 (SQ lower) |
| `….CountingModel.density_le_decided_add_undecided` | BPV-08 (SQ upper) |
| `….CountingModel.decidedMeasure_sum_add_undecided` | BPV-12 (Σ_α = 1) |
| `….CountingModel.UndecidedVanishes`, `.countingDensity_is_squeezed_limit` | BPV-10/11 (drain + uniqueness) |
| `LeanUrat.FactorizationType` (+ `.degree`) (`Interface.lean`) | the τ carrier; BPV-01/05 |
| `LeanUrat.MovesU.MemRcyc` + `.add`, `memRcyc_zero`, `.definedAt`, `.eval_ne_zero_of_inv`, `.powSubst`, `Xpow_sub_one_mem_cycS`, `cycS` (`MovesU/O12PoleFree.lean`) | ℛ; BPV-13/14/16/22/29; `.powSubst` reserved for BP_IV's (UB) chain |
| `LeanUrat.MovesU.eval_ratio` (`O12PoleFree.lean`) | BPV-25/27 (poly-ratio ↔ `RatFunc.eval` bridge) |
| `LeanUrat.MovesU.AbsSolveTable` + `.RcycDiscipline`, `.regAt_primePow` (`O12PoleFree.lean`) | NOT spine-consumed; the CANONICAL route by which **BP_II** discharges `SolveData.memR` (§5.2) |
| `LeanUrat.MovesU.DefinedAt` (`MovesU/Defs.lean`) | BPV-01 vocabulary alignment |
| `LeanUrat.L7.ratfunc_agree_of_infinite` (`L7.lean`) | BPV-16 (THE interpolation principle — already sorry-free, Lean-core) |
| `LeanUrat.OM.UniformCapstone.M7`, `.montes_uniform_n2`, `.hExhaustP`, `.uniformNum/uniformDen/uniformValueFn(+_eq_eval,_off)`, `.uniformDen_eval_ne`; `….UniformModelN2.typeMenuP` | BPV-22..27 (the n = 2 instance; `montes_uniform_n2` is the citation anchor — BPV-25 may route through `uniformValueFn_eq_eval` directly, same perimeter) |
| `LeanUrat.OM.SeriesAssembly.hExhaust_n2` | superseded for spine purposes by the all-`p` `hExhaustP`; listed to prevent re-derivation |
| mathlib: `RatFunc.eval(_add/_one)`, `RatFunc.num_div_denom`, `RatFunc.algebraMap_ne_zero`, `Polynomial.eval₂_id`, `Nat.infinite_setOf_prime`, `tendsto_finset_sum`, `tendsto_nhds_unique`, `le_of_tendsto'`/`ge_of_tendsto` | BPV-10/12/14/15/16 |

**Landed units NOT consumed by the spine** (other movements' quarry; listed so division
leads do not re-assign them here): `MovesV.SkeletonFinite.skeleton_finite` (BP_I Step 3),
`MovesU.RegPFinite.*` (BP_II Step 4 — note the spine's `MemRcyc` route makes (REG-p)
EMPTINESS the operative fact; `regP_cofinite` stays BP_II's fallback display),
`MovesU.KsubGeneral.*`, `MovesU.O5CountingB.*` (BP_IV Steps 12/17), `HC2/HK11a_vertexTransport`,
`HC2/UE_vtxUpper`, `R7_runRealizer`, the D-SC slot layer `MovesU/SlotsG*` (BP_III/IV
dictionary+census kit).

---

## 4. THE WAVE PLAN (dependency-ordered, for the division lead)

Per-file gates during waves (`lake env lean <file>`); `lake build` + AxChk at wave
checkpoints. All waves after V0 can overlap where dep columns allow; the listed order is
the safe serial collapse.

- **Wave V0 — the statement layer (all MECH, fully parallel):** BPV-01, 02, 03, 04, 05,
  06, 07. GATE: every structure compiles; zero `sorry` (no proofs exist yet to sorry);
  Codex plan-review of THIS FILE precedes the wave (the standing plan-level rule).
- **Wave V1 — the unconditional core (parallel after V0):** BPV-08, 09, 10, 11, 12.
  GATE: `clauseZeroSQ_holds` + `sum_alpha_one` Lean-core.
- **Wave V2 — ℛ + interpolation (parallel with V1, after V0):** BPV-13, 14, 15, 16.
  GATE: `memRcyc_eq_one_of_eval_primes` Lean-core.
- **Wave V3 — assembly (after V1+V2):** BPV-17, 18, 19, 20, 21. GATE: `rootC` compiles
  sorry-free; `#print axioms rootC` = Lean core.
- **Wave V4 — the n = 2 instance (BPV-22/23/24 may start after V0; BPV-25/26/27 after
  V3):** BPV-22, 23, 24, 25, 26, 27. GATE: `rootC_n2` Lean-core — THE NON-VACUITY GATE;
  a failure here is a stop-the-line interface bug, not a prover bug.
- **Wave V5 — n = 3 + census (after V3; BPV-28 needs its transcription brief cut from
  the RESUM-n3 record first):** BPV-28, 29, 30, 31. GATE: `sum_R3_eq_one` (the
  transcription falsifier) + the AxChk census clean.

Estimated prover-agent count: 31 units ⇒ ~31 single-unit provers + 6 gate re-runs; the
only units a prover may split further are BPV-16 (a `num/denom` plumbing helper may be
extracted) and BPV-29 (five per-type MemRcyc witnesses = five ≤ 10-line sub-units).

---

## 5. INTERFACE RECONCILIATION DUTY (binding on BP_I..BP_IV; keystone clause)

No other blueprint existed when this file was written. §1.3/§1.4's structures are
therefore CANONICAL: the other architects' signatures must compose here, or their
division lead files a reconciliation diff against THIS file (never a silent fork).

**5.1 BP_I (Movement I — Steps 1–3, measure floor + symbolic engine).** Owes: (a)
`FloorData n` instances at general `n` (per-prime SEMANTIC `CountingModel p n` with the
p-free menu; at n = 2 the spine builds it itself, BPV-23 — BP_I may re-point to it);
(b) the `MenuComplete` enrichment (the "every splitting type" quantifier) per n; (c) the
OPTIONAL Haar enrichment tying `countingDensity` to `μ(L_τ)` (Dfloor D-1; quarry:
`PadicMeasure.lean`, `L6_measureExact`/`LandingCylinderL`) — a NEW structure
`HaarFloor (F : FloorData n)` extending the spine, NOT a spine obligation; (d)
`SolveData.R` (the T-8 block-solve values) jointly with BP_II.

**5.2 BP_II (Movement II — Steps 4–5, regularity).** Owes: `SolveData.memR` — the
canonical route is `AbsSolveTable.RcycDiscipline` at the assembled table +
`Gram.memRcyc`/the `detO*` bank (all proved, `O12PoleFree.lean`); the spine consumes
ONLY `MemRcyc (R σ)`. The (SL≥2) display (every self-loop e ≥ 2, exponent ≥ 2) lives in
BP_II as the discipline's discharge at 𝔅_n; it never surfaces in the spine signature.

**5.3 BP_III (Movement III — Steps 6–13, dictionary).** Owes: `DrainData F` at general
`n` — the SEMANTIC drainage layer ONLY (M05 Lemmas A/C/D + Theorem E + SEM-DRAIN),
which ROOT holds unconditional at every prime; the classifier-TRANSFER layer (O4T,
(AGR)-conditional at general n) feeds BP_IV's counting tie, NOT this structure. If
BP_III needs the transfer layer typed, it extends with a NEW structure (suggested:
`TransferData` carrying the (AGR) row as a field) — reconciliation diff required.

**5.4 BP_IV (Movement IV — Steps 14–18b, value side).** Owes: (a) `ValueData` /
`ValueDataUB` instances — `alpha_eq` is the Step-18 (O-11 SERIES-TIE) ∘ Step-18b (D-11
M2) composition at EXACTLY the `HypR` set; `ub` is Step 16's package; (b) the REAL
`HypRows n` instance: each `Prop` field pinned to the leaf-brief statement it names
(grB ↔ GD23's order-≥2 residue; fresh ↔ O-9's clause (c) form; adm ↔ the O-9 r4 FULL
attainment display; r14 ↔ M14's (R1)–(R4); ubx/k3d ↔ the (UB-X) display; pack ↔ D-11
clause 4; tDec/tRead/tVerd ↔ CUC §9.4/CU-2t R3-R4; fenceVii ↔ D-11 item (vii)) — the
`k3d_of_ubx` law obligates BP_IV to state (K3-δ) as the genuine restriction of its
(UB-X)(b) statement. (c) `MemRcyc.powSubst` is the reserved corpus lever for the
q ↦ q^δ leg of `UBWitness.eval`.

**5.5 Math-revision sync (standing duty).** This blueprint is cut at ROOT **REVISION
5** (hypothesis set (H1)–(H6) = 14 fields incl. the (K3-δ) split and the four-row (H6)
group). When a VC6+ revision changes the §3.1 row set or per-clause attribution, the
BP_V owner: (1) edits `HypRows`/`HypR`/`HypUB` + the §1.2 table in the SAME commit; (2)
notifies all division leads (the bundles are the only cross-movement contract); (3)
re-runs Wave V3's gate. No other spine unit should need touching — that invariance is
the point of the design.

**5.6 Statement-fence note.** Nothing in this blueprint modifies
`montes_uniform_n2`, `montes_unconditional`, or any existing declaration; the spine
IMPORTS them. The eventual capstone-restatement decision (ROOT authority: "the current
theoremU reading-based form maps onto it via D-1/BRACKET — recorded, no statement
change now — parked class") stays PARKED; `rootC_n2` is an ADDITIONAL theorem, not a
restatement.

---

## 6. COMPLIANCE CHECKLIST (division lead signs at each wave close)

- [ ] new files under `lean/LeanUrat/Scaffold/` only; namespace `LeanUrat.Scaffold`
- [ ] zero edits outside `Scaffold/` + this blueprint
- [ ] zero new axioms; zero new `sorry` at wave close (E-phase `sorry`s die in-wave)
- [ ] `#print axioms` census (BPV-31) = Lean core on `rootC`, `rootC_n2`
- [ ] parked items 22–29 untouched; no fenced statement touched (§5.6)
- [ ] ROOT revision watch: blueprint header still says REVISION 5, else §5.5 fires

