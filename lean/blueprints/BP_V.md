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
then prove the squeeze lemma … depending on k"); the theorem takes ONLY the §3.1 [M]
rows as fixed, mathematically typed NAMED HYPOTHESIS ARROWS
`(h1 : RootRows.GR_B n) → … → (h6d : RootRows.FenceVII n)` and concludes the four (ROOT-C)
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
- NO new axioms. The [M] hypotheses are fixed predicates in `RootRows`; `HypRows`
  packages proofs of those predicates and never permits caller-selected propositions.
- Work packages are per-file and dependency-ordered; numbered BPV items are verification
  checkpoints, not separate-agent assignments. Helpers may split at natural lemma boundaries.
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
3. *Hypothesis rows are fixed mathematical predicates, not caller-selected slots.*
   `RootRows.GR_B n` through `RootRows.FenceVII n` are verbatim leaf-row statements
   supplied under `Scaffold/RowStatements.lean`; `HypRows` only packages their proofs.
   The proved theorem `RootRows.k3d_of_ubx : UBX n → K3Delta n` records the genuine
   restriction map, so choosing every row as `True` is impossible.
4. *(UB) is constructed by Movement IV* as
   `canonicalUB : HypUB n → UBWitness n (canonicalFloor n hn) (canonicalSolve n hn)`.
   Its exponent domain is every positive `δ`; the final `rootC` consumes this constructor
   internally rather than assuming a completed witness.
5. *The n = 2 reduced corollary `rootC_n2` is proved directly from the capstone*, without
   pretending that the capstone proves the canonical (H1)–(H6) row predicates, tying the spine
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

### 1.2 `Scaffold/RowStatements.lean`, `Scaffold/Hypotheses.lean` — fixed (ROOT-C) rows (BPV-02)

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
/-- `RootRows.GR_B n`, `Fresh n`, `D12R n`, `EN n`, `ADM n`, `R14 n`, `UBX n`,
`K3Delta n`, `PACK n`, `TDec n`, `TRead n`, `TVerd n`, and `FenceVII n` are
definitions whose bodies are the verbatim mathematical row statements. They live
in `Scaffold/RowStatements.lean`; see the binding cross-BP directive in §5.4. -/

/-- **The (ROOT-C) hypothesis rows** (ROOT §3.1, REVISION 5). Each field proves a
fixed mathematical predicate; no proposition is selected by the caller. -/
structure HypRows (n : ℕ) : Prop where
  grB      : RootRows.GR_B n
  fresh    : RootRows.Fresh n
  d12r     : RootRows.D12R n
  eN       : RootRows.EN n
  adm      : RootRows.ADM n
  r14      : RootRows.R14 n
  ubx      : RootRows.UBX n
  k3d      : RootRows.K3Delta n
  pack     : RootRows.PACK n
  tDec     : RootRows.TDec n
  tRead    : RootRows.TRead n
  tVerd    : RootRows.TVerd n
  fenceVii : RootRows.FenceVII n

theorem RootRows.k3d_of_ubx {n : ℕ} : RootRows.UBX n → RootRows.K3Delta n

/-- Clause (R)'s EXACT hypothesis set: (H1)–(H3) + (H4a) + (K3-δ) + (H5) + (H6)
[ROOT §1, REVISION 5 display]. NOTE: (H4b) itself is ABSENT — only its (K3-δ)
fragment enters clause (R). -/
structure HypR {n : ℕ} (H : HypRows n) : Prop where
  h1  : RootRows.GR_B n
  h2  : RootRows.Fresh n
  h3a : RootRows.D12R n
  h3b : RootRows.EN n
  h3c : RootRows.ADM n
  h4a : RootRows.R14 n
  hk3 : RootRows.K3Delta n
  h5  : RootRows.PACK n
  h6a : RootRows.TDec n
  h6b : RootRows.TRead n
  h6c : RootRows.TVerd n
  h6d : RootRows.FenceVII n

/-- Clause (UB)'s EXACT hypothesis set: (H1)–(H3) + (H4a) + (H4b) + (H5) + (H6). -/
structure HypUB {n : ℕ} (H : HypRows n) : Prop where
  h1  : RootRows.GR_B n
  h2  : RootRows.Fresh n
  h3a : RootRows.D12R n
  h3b : RootRows.EN n
  h3c : RootRows.ADM n
  h4a : RootRows.R14 n
  h4b : RootRows.UBX n
  h5  : RootRows.PACK n
  h6a : RootRows.TDec n
  h6b : RootRows.TRead n
  h6c : RootRows.TVerd n
  h6d : RootRows.FenceVII n

/-- (UB)'s set covers (R)'s via the proved fixed-predicate restriction theorem. -/
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
  menu_sound : ∀ σ ∈ menu, IsSplittingType n σ
  menu_complete : ∀ σ, IsSplittingType n σ → σ ∈ menu

/-- The retained name is now a projection, not an optional strengthening. -/
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
theorem floor_drain {n : ℕ} (F : FloorData n) :
    ∀ p (hp : p.Prime), UndecidedVanishes (F.M p hp)
```

### 1.4 `Scaffold/ValueIface.lean` — Movement IV plugs in here (BPV-06)

```lean
/-- **The packaged (UB) conclusion**: the counting-model family over the degree-δ
unramified base (residue size `p^δ`), same menu, drained, evaluating to the SAME
`R_τ` at `q = p^δ`. Data (not Prop): the base-change models are part of the claim. -/
structure UBWitness (n : ℕ) (F : FloorData n) (S : SolveData n) where
  Mδ : (p δ : ℕ) → p.Prime → 1 ≤ δ → CountingModel (p ^ δ) n
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
`lower`/`upper` = the generic counting-model bounds (intentionally valid for all
factorization types and all levels, a harmless strengthening of ROOT's splitting-type
scope); `drain` = undec(k) → 0; `unique` uses levels `N ≥ 1`, exactly the source
bracket scope. -/
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
theorem clauseZeroSQ_holds {n} (F : FloorData n) :
    ClauseZeroSQ F                                                           -- BPV-11
/-- Step 1's Σ_τ α = 1 at every prime (counting form). -/
theorem sum_alpha_one {n} (F : FloorData n)
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
    (V : ValueData n F S H) (h : HypR H) :
    (∑ σ ∈ F.menu, S.R σ) = 1                                                -- BPV-17

-- RootC.lean (the composition; per-clause attribution preserved)
/-- **Clause (R)** from EXACTLY its displayed hypothesis set (named arrows). -/
theorem clauseR_of_hyps {n} {H : HypRows n} (F : FloorData n) (S : SolveData n)
    (V : ValueData n F S H)
    (h1 : RootRows.GR_B n) (h2 : RootRows.Fresh n)
    (h3a : RootRows.D12R n) (h3b : RootRows.EN n) (h3c : RootRows.ADM n)
    (h4a : RootRows.R14 n) (hk3 : RootRows.K3Delta n) (h5 : RootRows.PACK n)
    (h6a : RootRows.TDec n) (h6b : RootRows.TRead n)
    (h6c : RootRows.TVerd n) (h6d : RootRows.FenceVII n) :
    ClauseR F S                                                              -- BPV-18
/-- **Clause (UB)** from exactly its displayed set (with (H4b), not (K3-δ)). -/
theorem clauseUB_of_hyps {n} {H : HypRows n} {F S}
    (V : ValueDataUB n F S H)
    (h1 : RootRows.GR_B n) (h2 : RootRows.Fresh n)
    (h3a : RootRows.D12R n) (h3b : RootRows.EN n) (h3c : RootRows.ADM n)
    (h4a : RootRows.R14 n) (h4b : RootRows.UBX n) (h5 : RootRows.PACK n)
    (h6a : RootRows.TDec n) (h6b : RootRows.TRead n)
    (h6c : RootRows.TVerd n) (h6d : RootRows.FenceVII n) :
    Nonempty (UBWitness n F S)                                               -- BPV-19

/-- Internal composition lemma; conclusion-bearing movement outputs are explicit here
and this lemma is not advertised as `(ROOT-C)`. -/
theorem rootC_assembly {n : ℕ} (hn : 2 ≤ n) (H : HypRows n)
    (F : FloorData n) (S : SolveData n) (V : ValueDataUB n F S H)
    (h : HypUB H) :
    ClauseZeroSQ F ∧ ClauseR F S ∧ Nonempty (UBWitness n F S)

/-- **(ROOT-C)**: only the fixed named mathematical rows occur as hypotheses.
`canonicalFloor`, `canonicalSolve`, `canonicalValues`, and drainage are proved
movement outputs consumed internally, not conclusion-bearing arguments. -/
theorem rootC {n : ℕ} (hn : 2 ≤ n)
    (h1 : RootRows.GR_B n) (h2 : RootRows.Fresh n)
    (h3a : RootRows.D12R n) (h3b : RootRows.EN n) (h3c : RootRows.ADM n)
    (h4a : RootRows.R14 n) (h4b : RootRows.UBX n) (h5 : RootRows.PACK n)
    (h6a : RootRows.TDec n) (h6b : RootRows.TRead n)
    (h6c : RootRows.TVerd n) (h6d : RootRows.FenceVII n) :
    ClauseZeroSQ (canonicalFloor n hn) ∧
    ClauseR (canonicalFloor n hn) (canonicalSolve n hn) ∧
    Nonempty (UBWitness n (canonicalFloor n hn) (canonicalSolve n hn))        -- BPV-20

-- Corollaries (BPV-21)
/-- The Σ = 1 corollary, standalone (conditional exactly as clause (R)). -/
theorem rootC_sum_one … : (∑ σ ∈ F.menu, S.R σ) = 1
/-- The hypothesis-free half, standalone: (0)+(SQ) need NO row. -/
theorem rootC_unconditional_half {n} (F : FloorData n) :
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
theorem floorDrain2 :
    ∀ p (hp : p.Prime), UndecidedVanishes (floorData2.M p hp)                -- BPV-24
theorem alphaEq2 : ∀ p (hp : p.Prime), ∀ σ ∈ floorData2.menu,
    (floorData2.M p hp).countingDensity σ = evalQ (R2 σ) (p : ℚ)             -- BPV-25
/-- Synthetic private bundle used only by the direct capstone reduction; it is not
`HypRows 2` and makes no claim to establish canonical (H1)–(H6). -/
structure ReducedRows2 : Prop where
  available : True
noncomputable def valueData2 :
    ∀ H : HypRows 2, ValueData 2 floorData2 solveData2 H
/-- **THE NON-VACUITY GATE: the reduced conclusion at n = 2, UNCONDITIONAL** — clauses
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
    {H : HypRows 3} (V : ValueData 3 F ⟨R3, memRcyc_R3⟩ H)
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
| BPV-02 | RowStatements/Hypotheses | fixed `RootRows.*` predicates, `HypRows`, `HypR`, `HypUB`, conversion | one per-file work package; predicate bodies copied verbatim from leaf statements; conversion uses `RootRows.k3d_of_ubx` | BPV-01; BP_IV row module | MED | §3.1 all rows; §1 attribution |
| BPV-05 | Interfaces | `FloorData` with sound/complete splitting-type menu, `SolveData`, `floor_drain` | one per-file work package; drainage theorem proved from the generic semantic model | BPV-01; BP_I/BP_III | MED | §2 Steps 1–5, 13 |
| BPV-06 | ValueIface | `UBWitness`, `ValueData`, `ValueDataUB` | structures only | BPV-02..05 | MECH | §2 Steps 14–18b, 16 |
| BPV-07 | Conclusions | `ClauseZeroSQ`, `ClauseR` | Prop structures only | BPV-05 | MECH | §1 clauses (0)(SQ)(R) |
| BPV-08 | SqueezeCore | `clause_lower`, `clause_upper` | = `decided_le_density`, `density_le_decided_add_undecided` through `F.M` | BPV-05; corpus: CountingModel | MECH | §1 (SQ) |
| BPV-09 | SqueezeCore | `clause_limit` | = `density_isLimit` through `F.M` | BPV-05 | MECH | §1 (0) |
| BPV-10 | SqueezeCore | `bracket_unique` | `le_antisymm`: lower leg `le_of_tendsto'` of `density_isLimit` against `hbr.1` eventually (N ≥ 1); upper leg `ge_of_tendsto` of `countingDensity_is_squeezed_limit hU` against `hbr.2` | corpus: CountingModel | EASY-MED | §2 Step 19 "squeezes" |
| BPV-11 | SqueezeCore | `clauseZeroSQ_holds` | assemble BPV-08/09/10 + `floor_drain F`; `unique` from BPV-10 | BPV-07..10 | MECH | §1 (0)+(SQ) unconditional [VC4-4] |
| BPV-12 | SqueezeCore | `sum_alpha_one` | helper lemmas for finite-sum convergence and the constant sequence; use `floor_drain F`, `decidedMeasure_sum_add_undecided`, `F.menu_eq`, `tendsto_nhds_unique` | BPV-05; corpus: CountingModel | MED | §2 Step 1 Delivers; Step 19 Σ-derivation input |
| BPV-13 | SumOne | `memRcyc_sum` | `Finset.cons_induction`; `memRcyc_zero`, `MemRcyc.add` | corpus: O12PoleFree | EASY | §2 Step 19 Σ_τ R_τ = 1 |
| BPV-14 | SumOne | `evalQ_sum` | first validate the exact local `RatFunc.eval_add` signature; prove its two defined-at premises from `MemRcyc.definedAt hx`, then cons induction | BPV-01,13 | MED | same |
| BPV-15 | SumOne | `primesQ_infinite` | `Nat.infinite_setOf_prime.image` + injectivity of `Nat.cast : ℕ → ℚ` | mathlib | MECH | §2 Step 19 "infinitely many prime powers" |
| BPV-16 | SumOne | `memRcyc_eq_one_of_eval_primes` | validate `#check L7.ratfunc_agree_of_infinite`; adapt through a typed helper matching its actual polynomial/evaluation binders, obtain numerator/denominator equality, then use the checked `RatFunc.num_div_denom` form | BPV-01,15; corpus: L7, O12PoleFree | MED-HARD | §2 Step 19 interpolation [B3] |
| BPV-17 | SumOne | `sum_R_eq_one` | per prime: BPV-12 + `V.alpha_eq h` rewrite gives Σ evalQ (R σ) p = 1; BPV-13/14 package Σ as one ℛ-element evaluating to 1 (note (p:ℚ) ≥ 2 from `hp.two_le`); close with BPV-16 | BPV-12..16, BPV-06 | EASY | §2 Step 19 Σ_τ R_τ = 1 [B3] |
| BPV-18 | RootC | `clauseR_of_hyps` | `HypR.mk` from the 12 arrows; `ClauseR.mk (fun σ _ => S.memR σ) (V.alpha_eq ⟨…⟩) (sum_R_eq_one …)` | BPV-03,06,07,17 | EASY | §1 (R)-attribution |
| BPV-19 | RootC | `clauseUB_of_hyps` | `⟨V.ub ⟨12 arrows⟩⟩` | BPV-04,06 | MECH | §1 (UB)-attribution |
| BPV-20 | RootC | `rootC_assembly`, `rootC` | assembly helper uses explicit packages; advertised theorem builds the fixed `HypRows`, canonical floor/solve/value outputs, and UB witness internally, using `RootRows.k3d_of_ubx h4b` | BPV-11,18,19; canonical outputs from BP_I–IV | EASY | §1 (ROOT-C); §2 Step 19 |
| BPV-21 | RootC | `rootC_sum_one`, `rootC_unconditional_half` | projections/aliases of BPV-17/BPV-11 with the named-arrow interface | BPV-11,17 | MECH | §1 (ROOT-C); task charge "Sigma=1 corollary" |
| BPV-22 | InstanceN2 | `R2`, `memRcyc_R2`, `solveData2` | one file-owned work package; split into private ram/inert/split/off-menu witness helpers before the public theorem; clear denominators only after checking `RatFunc.algebraMap_ne_zero` | BPV-01,05; corpus: UniformCapstone, O12PoleFree | HARD | §1 "Verified instances"; capstone §H |
| BPV-23 | InstanceN2 | `floorData2` | `M := fun p hp => @M7 p ⟨hp⟩`; `menu := typeMenuP`; prove `menu_sound` and `menu_complete` by explicit finite menu cases (no unstated M7 field) | BPV-05; corpus: UniformCapstone, UniformModelN2 | MED | capstone §H |
| BPV-24 | InstanceN2 | `drainData2` | `UndecidedVanishes (M7 p)` unfolds to `hExhaustP p` (n·N = 2·N alignment by `show`/`simp`) | BPV-23; corpus: UniformCapstone | MECH-EASY | capstone §E |
| BPV-25 | InstanceN2 | `alphaEq2` | `countingDensity = uniformValueFn σ p` (defeq via `densityVal`); `uniformValueFn_eq_eval`; bridge to `evalQ (R2 σ)` by `MovesU.eval_ratio` with `uniformDen_eval_ne` (0 < p) | BPV-22,23; corpus: UniformCapstone, O12PoleFree | MED | capstone (V) clause |
| BPV-26 | InstanceN2 | `ReducedRows2`, `valueData2`, `rootC_n2` | direct capstone reduction; assemble unconditional squeeze and evaluation without claiming canonical row proofs | BPV-11,22..25 | EASY | §1 verified-instances ¶; non-vacuity discipline (repo CLAUDE.md) |
| BPV-27 | InstanceN2 | gates: `gate_sum_R2`, `gate_wild_p2`, `gate_R2_ram_at_2` | project `rootC_n2.2.sum`; instantiate at p = 2 (`Nat.prime_two`); `evalQ (R2 ramType2) 2 = 1/3` by `eval_ratio` + `norm_num` | BPV-26 | MECH | capstone gates ¶ |
| BPV-28 | InstanceN3 | `n3Menu`, `R3` (defs, source-pinned transcription) | transcribe the five degree-3 types + their `ℚ(q)` values from the RESUM-n3 sealed record / `o11_seriestie_check.py` (leaf brief pins exact strings); FIDELITY RISK — falsifier is BPV-29 | BPV-01 | MED | §1 verified-instances ¶ (RESUM-n3 65/65) |
| BPV-29 | InstanceN3 | `memRcyc_R3`, `sum_R3_eq_one` | private helper per type, then a separate rational-function identity helper with explicit nonzero denominators; public theorems are wrappers | BPV-13,28 | HARD | same |
| BPV-30 | InstanceN3 | `rootC_n3_of_instances` | assemble BPV-11; use `V.alpha_eq h` for evaluation, `memRcyc_R3` for membership, and rewrite the sum through `hmenu` to close specifically with `sum_R3_eq_one` | BPV-11,28,29 | MECH | §6 next-actions (n = 3 instance) |
| BPV-31 | AxChk | `Scaffold/AxChk.lean` census | `#print axioms` block per §1.8 | BPV-20,26,30 | MECH | repo axiom policy |

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
| mathlib candidates, to be accepted only after in-file `#check`: `RatFunc.eval_add`,
`RatFunc.num_div_denom`, `RatFunc.algebraMap_ne_zero`, `Polynomial.eval₂_id`,
`Nat.infinite_setOf_prime`, `tendsto_finset_sum`, `tendsto_nhds_unique`,
`le_of_tendsto'`, `ge_of_tendsto` | BPV-10/12/14/15/16 |

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

- **Wave V0a — independent foundations:** BPV-01 and the fixed BP_IV row-statements
  transcription may run in parallel. Per-file GATE:
  `lake env lean LeanUrat/Scaffold/Defs.lean` and
  `lake env lean LeanUrat/Scaffold/RowStatements.lean`.
- **Wave V0b — interfaces after V0a:** one owner performs BPV-02, then BPV-05; after
  those compile, BPV-06 and BPV-07 may run in parallel in distinct files. Per-file
  `lake env lean` gates are mandatory; no concurrent edits to one module.
- **Wave V1a — independent core lemmas after V0b:** BPV-08, BPV-09, BPV-10, and BPV-12
  may run in parallel only where files have distinct owners.
- **Wave V1b — core assembly:** BPV-11 runs after BPV-08/09/10. GATE:
  `lake env lean LeanUrat/Scaffold/SqueezeCore.lean`.
- **Wave V2a — ℛ foundations, parallel with V1 after V0b:** BPV-13 and BPV-15.
- **Wave V2b — checked elaboration:** BPV-14 after BPV-13; BPV-16 after BPV-15.
  Before proof work, compile a scratch-free `#check` block for every flagged Mathlib/L7
  declaration, then delete the block. GATE:
  `lake env lean LeanUrat/Scaffold/SumOne.lean`.
- **Wave V3 — assembly (after V1b+V2b and canonical BP_I–IV outputs):** one RootC owner
  performs BPV-17–21 in dependency order. GATE:
  `lake env lean LeanUrat/Scaffold/RootC.lean`; `rootC` compiles sorry-free and its
  only theorem hypotheses are the fixed named rows.
- **Wave V4 — the n = 2 instance (BPV-22/23/24 may start after V0; BPV-25/26/27 after
  V3):** BPV-22, 23, 24, 25, 26, 27. GATE: `rootC_n2` Lean-core — THE NON-VACUITY GATE;
  a failure here is a stop-the-line interface bug, not a prover bug.
- **Wave V5a — n = 3 (after V3):** BPV-28, then BPV-29, then BPV-30; BPV-28 requires
  its transcription brief first. GATE:
  `lake env lean LeanUrat/Scaffold/InstanceN3.lean`, including the
  `sum_R3_eq_one` transcription falsifier consumed by BPV-30.
- **Wave V5b — census (after BOTH V4 and V5a):** BPV-31. GATE:
  `lake env lean LeanUrat/Scaffold/AxChk.lean` and `lake build`.

Assignment count is one owner per module/work package, not one owner per BPV checkpoint.
Within a file, its owner may split BPV-12, BPV-16, BPV-22, or BPV-29 into private
≤40-line helpers. Every file receives its own `lake env lean <file>` gate before a
dependent wave begins; no two owners edit the same module concurrently.

---

## 5. INTERFACE RECONCILIATION DUTY (binding on BP_I..BP_IV; keystone clause)

No other blueprint existed when this file was written. §1.3/§1.4's structures are
therefore CANONICAL: the other architects' signatures must compose here, or their
division lead files a reconciliation diff against THIS file (never a silent fork).

**5.1 BP_I (Movement I — Steps 1–3, measure floor + symbolic engine).** Owes: (a)
`FloorData n` instances at general `n` (per-prime SEMANTIC `CountingModel p n` with the
p-free menu; `menu_sound` and `menu_complete` are mandatory fields, so the theorem
ranges over exactly every splitting type); at n = 2 the spine builds it itself; (b) the
OPTIONAL Haar enrichment tying `countingDensity` to `μ(L_τ)` (Dfloor D-1; quarry:
`PadicMeasure.lean`, `L6_measureExact`/`LandingCylinderL`) — a NEW structure
`HaarFloor (F : FloorData n)` extending the spine, NOT a spine obligation; (d)
`SolveData.R` (the T-8 block-solve values) jointly with BP_II.

**5.2 BP_II (Movement II — Steps 4–5, regularity).** Owes: `SolveData.memR` — the
canonical route is `AbsSolveTable.RcycDiscipline` at the assembled table +
`Gram.memRcyc`/the `detO*` bank (all proved, `O12PoleFree.lean`); the spine consumes
ONLY `MemRcyc (R σ)`. The (SL≥2) display (every self-loop e ≥ 2, exponent ≥ 2) lives in
BP_II as the discipline's discharge at 𝔅_n; it never surfaces in the spine signature.

**5.3 BP_III (Movement III — Steps 6–13, dictionary).** Owes the theorem
`floor_drain {n} (F : FloorData n) : ∀ p (hp : p.Prime),
UndecidedVanishes (F.M p hp)` at general `n` — the SEMANTIC drainage layer ONLY
(M05 Lemmas A/C/D + Theorem E + SEM-DRAIN),
which ROOT holds unconditional at every prime; the classifier-TRANSFER layer (O4T,
(AGR)-conditional at general n) feeds BP_IV's counting tie, NOT this structure. If
BP_III needs the transfer layer typed, it extends with a NEW structure (suggested:
`TransferData` carrying the (AGR) row as a field) — reconciliation diff required.

**5.4 BP_IV (Movement IV — Steps 14–18b, value side).** Owes: (a) the canonical theorem
outputs consumed by `rootC`: `canonicalValues (n : ℕ) (hn : 2 ≤ n) :
ValueDataUB n (canonicalFloor n hn) (canonicalSolve n hn) (canonicalHypRows n)`;
`alpha_eq` is Step-18 ∘ Step-18b and `ub` is Step 16; (b) the FIXED predicate definitions
in `Scaffold/RowStatements.lean`, each with its full mathematical body copied verbatim
from the leaf statement it names
(grB ↔ GD23's order-≥2 residue; fresh ↔ O-9's clause (c) form; adm ↔ the O-9 r4 FULL
attainment display; r14 ↔ M14's (R1)–(R4); ubx/k3d ↔ the (UB-X) display; pack ↔ D-11
clause 4; tDec/tRead/tVerd ↔ CUC §9.4/CU-2t R3-R4; fenceVii ↔ D-11 item (vii)) — the
the theorem `RootRows.k3d_of_ubx {n : ℕ} : RootRows.UBX n →
RootRows.K3Delta n` obligates BP_IV to prove the genuine restriction of (UB-X)(b).
(c) `MemRcyc.powSubst` is the reserved corpus lever for the `q ↦ q^δ` leg of
`UBWitness.eval`, whose exact domain is `1 ≤ δ`.

**CROSS-BP interface signatures.** BP_I must export
`noncomputable def canonicalFloor (n : ℕ) (hn : 2 ≤ n) : FloorData n`;
BP_II must export
`noncomputable def canonicalSolve (n : ℕ) (hn : 2 ≤ n) : SolveData n`;
BP_IV must export
`def canonicalHypRows (n : ℕ) : HypRows n` only when it has proved every fixed row,
and `noncomputable def canonicalValues (n : ℕ) (hn : 2 ≤ n) :
ValueDataUB n (canonicalFloor n hn) (canonicalSolve n hn) (canonicalHypRows n)`.
No `axiom`, `opaque` placeholder, arbitrary `Prop` parameter, or conclusion-bearing
argument may substitute for these proved definitions.

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
- [ ] `#check`-validated exact signatures for `RatFunc.eval_add`,
      `L7.ratfunc_agree_of_infinite`, parent projections, and `RatFunc.num_div_denom`
- [ ] `rootC` has no `FloorData`, `SolveData`, drainage, `ValueData`, or `UBWitness`
      argument; only `n ≥ 2` and the fixed named mathematical row proofs

## REVISION 2 (review fold, 2026-08-03)
1 -> FIXED -> `rootC` now consumes canonical movement outputs internally; the old conclusion-bearing composition is explicitly named `rootC_assembly`.
2 -> FIXED -> `HypRows` fields prove fixed `RootRows.*` predicates; CROSS-BP DIRECTIVE BP_IV: define the verbatim predicates and export `canonicalHypRows (n : ℕ) : HypRows n`.
3 -> FIXED -> `DrainData` is removed from theorem boundaries; unconditional drainage is the general theorem `floor_drain` and is consumed internally.
4 -> FIXED -> `FloorData` now requires `menu_sound` and `menu_complete`, with `IsSplittingType` positivity and degree built into both directions.
5 -> FIXED -> `ClauseZeroSQ` documentation explicitly records the generic all-factorization-type/all-level strengthening and the `N ≥ 1` uniqueness scope.
6 -> FIXED -> `UBWitness.Mδ` now ranges over `1 ≤ δ`, including δ = 1.
7 -> FIXED -> V0 is split into V0a/V0b with actual dependency ordering and distinct-file ownership.
8 -> FIXED -> V1 is split into independent lemma work followed by BPV-11 assembly.
9 -> FIXED -> the census is V5b and explicitly follows both V4 and V5a.
10 -> FIXED -> assignments are consolidated per module; BPV numbers are checkpoints, not 31 separate provers.
11 -> FIXED -> BPV-12/16/22/29 explicitly permit private ≤40-line helpers, with BPV-22 and BPV-29 rated HARD.
12 -> FIXED -> BPV-30 drops drainage, retains `hmenu`, and explicitly consumes `sum_R3_eq_one`, making BPV-29 a genuine transcription dependency.
13 -> FIXED -> `floorData2` proves menu soundness/completeness by explicit finite cases and no longer cites an unstated M7 degree field.
14 -> FIXED -> the n=2 construction is renamed `ReducedRows2` and documented as a direct capstone reduction, not a canonical row instantiation.
15 -> FIXED -> flagged Mathlib/L7 names require compiled `#check` validation; proof sketches no longer assert an unchecked exact application or parent coercion.
