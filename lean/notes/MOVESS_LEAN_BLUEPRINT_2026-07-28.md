# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS) — REV 4

*REV 4, 2026-07-27. Repairs the 6 findings of the fresh-Fable audit
`lean/notes/MOVESS_AUDIT_FABLE_2026-07-28.md` (2 crit / 4 gap) on REV 3, which had
repaired the 20 findings of `MOVESS_AUDIT_CODEX_REV2_2026-07-28.md`; cumulative table
§6. Ground truth: DUAL-ACCEPTED **§S-RESUM rev 6**, `MOVES_2026-07-24.md` ~11557–12430.
Protocol-L; no new axioms; statement-fence; declaration order = spec.*

## H0. REV-4 rulings (on top of R1–R12)

**R13 — the ACT scope is a GUARD, never a zero-row law (Fable C2).** The invented
`act_row` is DELETED (the note displays only entry-INTO-inactive vanishing =
`act_target`, S.7(iv)). `part1`/`rep_indep`/`xhd_sum`/`xhd_no_stray`/`meas_card` are
GUARDED by `activeState q₀ e τ` — the note's own scope: "Scope: realized states only"
(S.4); "Every probabilistic claim … is about K_e restricted per CTS-M(ii) to the
ACTIVE block" (S.0). Wild pools are now instantiable; the ACT apparatus (act_spec,
inactive_vanish, AVAgree, U-21c's empty case) is live code. Ripple: U-9a/U-9b/U-10
carry the activity guard.

**R14 — the per-pool guards are CONSUMED (Fable C1).** U-24a is replaced by the pair
U-24a1 (the measured value IS the active-subsystem solve — derived per pool from
`recursion_meas` + subsystem closure (`inactive_vanish`/`act_target`) + E0/U-21c;
the split legs enter the exit vector as MEASURED values at q₀^δ, pools_closed-typed,
so NO induction and NO leg evaluation is needed) and U-24a2 (the symbolic read-off:
`evalAt q₀ (blockSolve …) = βmeas …` GIVEN `AVAgree` at that entry — the note's
sealed (ii-c) check as an explicit hypothesis; uncancelled wild poles are EXCLUDED by
the guard, not claimed). `RegP` and `AVAgree` are now consumed (U-24a1/2, U-24b,
RS4Chain.legs_reg). U-24b's global identification is CONDITIONAL on an infinite
read-off-valid pool family — the (ii-c) burden stays open and per-pool, as displayed.
VERDICT: U-24a CLOSES under the wired guards (no STUCK report); the former "hard"
strong induction DISSOLVES — the hardness was exactly the unhypothesized burden.

**R15 — gap closures (Fable G1–G4).** `kstep_one`'s target predicate is pinned in its
hK-free existential-cast form; W-1's rfl-conjunct is struck (the symbolic half is
definitional — RS.1-SH's content is the measured clause), binders unshadowed; U-16a
splits into U-16a1/2/3 with the halted-member FACTOR-1/verdict-singleton clause
displayed as bSplit's def-equation; `entCount` gets its event-card tie at the shape's
own level (`entLvl`/`entInst`/`ent_count_card`). New easy lemma U-12b
`powSubst_OKat_evalAt` (OK-membership and evaluation transport along q₀ ↦ q₀^δ).

## H. HEADER — REV-3 design rulings (kept; R7–R12)

**R7 — the counting-native event carrier (ORCHESTRATOR RULING, finding R2-4).** MovesS
gains a MINIMAL event layer in the corpus house style (MovesC's DigitSystem/Nat.card
pattern): per pool q₀ and level N a finite `Box q₀ N`; EVENTS are `Finset (Box q₀ N)`;
disjointness is `Disjoint` of Finsets; masses are EVENTUALLY-EXACT CARD RATIOS
(`mass * card Box = card event` for N ≥ N₀ — the MovesC level-independence idiom).
XHD / D4R.0 / (iv)-MEAS restate the note's disjoint-EVENT conditions over this carrier
— not height-label arithmetic. MovesV instantiates the carrier at wave 4; MovesS does
not wait.

**R8 — RS.2 de-circularized (finding R2-9).** `RS1Bundle` carries NO symbolic β input.
Its measured inputs are `βmeas` (height-indexed, per-pool) + the measured fixpoint
`recursion_meas` + `xrb`. The interpolant is DERIVED: U-24a proves the per-pool
evaluated identity `evalAt q₀ (blockSolve …) = βmeas …` at all-active pools (per-pool
E0/ACT guarding evaluation, exactly S.4's discipline); U-24b proves the interpolant
UNIQUE and FIXED (U-27 infinitude) — that is RS.2's "one fixed rational function" and
RS.1-DEEP's symbolic reading, derived from the note's actual GIVENs.

**R9 — no free index sets** (findings R2-7, R2-8, R2-10, R2-11). `Pools` is pinned to
prime powers and CLOSED under q₀ ↦ q₀^δ (the [2r] (e2) legs); `allActive` is a DEFINED
locus (the all-active states classification), with only its INFINITUDE a burden
((iv)-POLY's cofiniteness face); `PoolHyp.Act` is DETERMINED by the CTS-M(ii)
classification field (`act_spec`, an iff) — never chosen; `SigSet`/`sig_covers` are
DELETED — every σ′ quantifier runs over ALL of `Multiset VType` as the note displays,
finite sums use the roster's verdict-image Finset; RS.4's σ-index is
`Multiset VType` with a Finset `Sigmas` of splitting types (W-1 typechecks).

**R10 — every wave-4 deferral is a PINNED Prop** (finding R2-18): `SyncDefs.lean`
declares W-1/W-1e/W-1m/W-2/W-3/W-4/W-7/W-8/W-10 as Lean `def … : Prop` signatures over
minimal carriers (`TreeIface`, `ReadLedger`, `FiberIface`); no prose deferrals. W-9 is
RETIRED — subsumed by R7's event carrier. Convergence (S.2's unconditional display) is
pinned as W-10.

**R11 — the non-vacuity gate is renamed to its honest claim** (finding R2-20):
U-29 `consistency_n2` inhabits EVERY §2 structure simultaneously with a nontrivial
instance reproducing W6's displayed 1×1 solve (denominator q² + q + 1) — a SCHEMA
CONSISTENCY gate. Inhabitation by the intended CTS instance is MovesV/MovesT's wave-4
instantiation duty (§5 process obligation), and is NOT claimed by any unit.

**R12 — mechanical fatalities** (findings R2-1, R2-2, R2-3, R2-12, R2-13, R2-15,
R2-16, R2-17): the `∨ True` disjunct is DELETED (`memberOf_ne_sel` states the real
inequality); `flank_zero : flankCount = 0 → flankWidth = 0` added (U-4's missing leg);
declaration order fixed everywhere (fields precede uses); U-10's TG/J nonnegativity is
ROUTED (TG on non-split, J on split) and now DERIVED from the ledger, not assumed;
U-22's `e` binder is inside the per-block quantifier; U-21b takes `[Nonempty ι]` (U-21c
handles the empty case via `Matrix.det_isEmpty`); U-7 splits into U-7a/b/c; `bTot`/
`blockSolveTot` define U-25's aggregate; the measured marked total `markedVal` is a
carrier field.

Downstream statement: MovesV/MovesT enter ONLY through §2's hypothesis structures;
owners at every field; instantiable at wave 4.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block 1 ≤ e ≤ n the system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q); the (m, c) CLASSIFICATION routes every outcome to exactly one of {K_e
column, terminal exit, split exit}; (K-TRI) triangularizes the block family; (K-SUB)
gives sub-stochastic rows from PART-1; the solve is adj(I−K_e)b_e/det(I−K_e) (RS.2);
solvability rides ESCAPE(E0) per pool (RS.3, OPEN CL-1); RS.1 ties the solve to R_σ
(DEEP/SH/MARKED); RS.4: Σ_σ R_σ = 1 by the infinitely-many-evaluations argument.

## 1. Mathlib design (all names verified in the pinned cache; = REV 2's D1–D9 plus)

D1 `Qq := RatFunc ℚ` (`RatFunc.instField`) · D2 one matrix per e, vectors per (e, σ′) ·
D3 `Matrix.isUnit_iff_isUnit_det`, `mul_nonsing_inv`/`nonsing_inv_mul`, `inv_def`,
`cramer_eq_adjugate_mulVec`, `mul_adjugate`/`adjugate_mul`,
`det_smul_inv_mulVec_eq_cramer` · D4 partial evaluation `evalAt q₀ : OKat q₀ →+* ℚ`
(`RatFunc.eval_add`/`eval_mul` hypothesis-carrying) · D5
`Polynomial.eq_zero_of_infinite_isRoot` via `ratfunc_eval_infinite` · D6
`powSubst (δ : ℕ+)` via `IsFractionRing.lift` (δ = 0 unrepresentable) · D7 σ′ =
`Multiset VType`, finite sums over roster-image Finsets (SigSet DELETED, R9) · D8
`MuHat` fence · D9 measured values in ℝ, symbolic in Qq, meeting only through
interpolation laws · **D10 (NEW)** events = `Finset (Box q₀ N)`, masses =
eventually-exact card ratios (R7); `Matrix.det_isEmpty` for empty active blocks.

---

## 2. Defs skeleton — `MovesS/Defs.lean` (declaration order = spec; findings R2-3)

### 2.A Combinatorial layer (owner MovesV/MovesSp rosters)

```lean
import Mathlib
namespace LeanUrat.MovesS
open Matrix Polynomial

abbrev Qq := RatFunc ℚ

structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+                       -- ABSOLUTE base-change index ([2r] (e2)); no δ = 0
  status : V ⊕ State size
def Member.continuing (μ : Member V State) : Prop := μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []
def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split deriving DecidableEq
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- Block states + rosters. NO SigSet (R9): σ′ ranges over all of `Multiset VType`;
    finite σ′-sums use `verdictImage` below. -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  Out    : ∀ e, State e → Type
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finO

/-- The finitely many verdict multisets the (e, τ) roster's terminal outcomes emit —
    the index Finset of (K-SUB)'s Σ_{σ′} b^{term,fin} (replaces REV 2's SigSet). -/
def verdictImage (T : TableShape n) (e : ℕ) (τ : T.State e) : Finset (Multiset T.VType) :=
  Finset.image (fun o => (T.odata e τ o).verdicts)
    {o : T.Out e τ | routeOf (T.odata e τ o) = .termFin}.toFinset
```

**(SCS) supply — declaration order fixed (R2-3), the `∨ True` artifact deleted (R2-1),
the flank-zero law added (R2-2).** Owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via SP.2.

```lean
structure SCSData (T : TableShape n) where
  -- data first (R2-3): every field below is declared before first use
  W D ℓ g μsel W' D' : ∀ e τ (o : T.Out e τ), ℕ
  flankCount  : ∀ e τ (o : T.Out e τ), ℕ
  flankWidth  : ∀ e τ (o : T.Out e τ), ℕ
  resFactors  : ∀ e τ (o : T.Out e τ), Finset (ℕ × ℕ)
  selIdx      : ∀ e τ (o : T.Out e τ), Fin (T.odata e τ o).mem.length
  memberOf    : ∀ e τ o, Fin (flankCount e τ o) ⊕
    {x // x ∈ resFactors e τ o ∧ x ≠ (g e τ o, μsel e τ o)} →
    Fin (T.odata e τ o).mem.length
  -- laws
  ℓpos : ∀ e τ o, 1 ≤ ℓ e τ o
  window_comp : ∀ e τ o, W e τ o = e * ℓ e τ o + flankWidth e τ o
    -- SP.1: flank sides = "the horizontal compositions of the window span outside
    -- the read side"
  flank_zero : ∀ e τ o, flankCount e τ o = 0 → flankWidth e τ o = 0   -- (R2-2): no
    -- sides ⟹ no width (the width is the sides' total raw width)
  sel_mem : ∀ e τ o, (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e τ o, ∑ x ∈ resFactors e τ o, x.1 * x.2 = ℓ e τ o     -- "Σ g⁽ⁱ⁾μ⁽ⁱ⁾ = ℓ"
  memberOf_inj : ∀ e τ o, Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e τ o i, memberOf e τ o i ≠ selIdx e τ o        -- (R2-1): the
    -- REAL inequality — every flank side / non-selected residual factor is a member
    -- DISTINCT from the designated one; no disjunct, no vacuous premise
  sel_continuing : ∀ e τ o, routeOf (T.odata e τ o) = .kcol →
    ((T.odata e τ o).mem.get (selIdx e τ o)).continuing
  stage_D : ∀ e τ o, D' e τ o = e * g e τ o * D e τ o                 -- (B1)
  stage_W : ∀ e τ o, W' e τ o = μsel e τ o                            -- (B3)
  cluster_parent : ∀ e τ o, W e τ o * D e τ o = e
  cluster_child : ∀ e τ o (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o

/-- DEG-CONS (CL-11, [1v]): full-roster per-member degree law. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e
```

### 2.B The measured side (R7 event carrier) + the NINE-input ledger (R2-4/5/6 repaired)

Owner [1v] CTS-M / [2b] XHD / [5]. Intended instance: the CTS cell space over the
level-N residue boxes of the O_δ theory (the MovesC counting idiom), wave 4.

```lean
structure MeasuredSide (T : TableShape n) where
  -- pools: prime powers, closed under the base-change legs (R2-7, R2-14)
  Pools : Set ℚ
  pools_prime_pow : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p:ℚ)^(δ:ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀^(δ:ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  -- the counting carrier (R7): level-N boxes, events as Finsets
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- cells, representatives, heights
  Cell : ∀ e, T.State e → Type
  finC : ∀ e τ, Fintype (Cell e τ)
  cellOut : ∀ e τ, Cell e τ → T.Out e τ
  Rep : ∀ e, T.State e → Type          -- concrete states WITH their admissible
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ, Nonempty (Rep e τ)   -- histories (design note:
                                        -- the ∀-x quantifiers below quantify histories)
  Hgt : Type
  HDom : ∀ e τ, Cell e τ → Set Hgt     -- the EXACT height domain (XHD-d)
  gwt : ∀ e τ (c : Cell e τ), Hgt → ℚ → ℝ        -- XHD-w fixed-height weight
  cellEvt : ∀ e τ, Rep e τ → Cell e τ → Hgt → ∀ q₀ N, Finset (Box q₀ N)
    -- the (cell, height) one-step EVENT at level N given the entrance representative
  μcell : ∀ e τ, Rep e τ → Cell e τ → ℚ → ℝ      -- XHD-resummed conditional cell mass
  rowVal : ∀ e τ, T.Out e τ → ℚ → ℝ    -- the MEASURED per-outcome resummed row (the
                                        -- T·G row for non-split, the J cell-sum for
                                        -- split) — RS.0(α)'s object (R2-5)
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ -- measured k-step in-block mass
  activeState : ℚ → ∀ e, T.State e → Prop        -- CTS-M(ii)'s classification (R2-6/8)
  decA : ∀ q₀ e, DecidablePred (activeState q₀ e)
  -- entrance side
  EntShape : ∀ e, T.State e → Type
  finE : ∀ e τ, Fintype (EntShape e τ)
  hent : ∀ e τ, EntShape e τ → ℕ                 -- retained h_ent(ε)
  entEvtH : ∀ e τ, EntShape e τ → Hgt → ∀ q₀ N, Finset (Box q₀ N)  -- fixed-height
  ιDom : ∀ e τ, EntShape e τ → Set Hgt           --   entrance events + exact classes
  ιshH : ∀ e τ, EntShape e τ → Hgt → ℚ → ℝ       -- fixed-height marked mass ((COMP-h))
  ιsh : ∀ e τ, EntShape e τ → ℚ → ℝ              -- resummed per-shape marked mass
  ιval : ∀ e, T.State e → ℚ → ℝ                  -- the ENT-AGG aggregate
  entCount : ∀ e τ, EntShape e τ → ℚ → ℕ         -- the full count I^ent_{ε,β₀}
  entLvl : ∀ e τ, EntShape e τ → ℕ               -- ε's own defining level (a finite
                                                  --   prefix shape) — G4's tie level
  entInst : ∀ e τ, EntShape e τ → ∀ q₀ N, Finset (Box q₀ N)  -- ε-instance events
  markedVal : ∀ e, ℚ → ℝ                          -- the measured μ̂ marked-entrance
                                                  -- total (W-1m's carrier, R2-17)

def allActivePools (M : MeasuredSide T) : Set ℚ :=       -- DEFINED locus (R2-7/R9)
  {q₀ ∈ M.Pools | ∀ e ∈ Finset.Icc 1 n, ∀ τ, M.activeState q₀ e τ}

/-- CL-5, all nine inputs as contentful Props (R2-4/5/6). Notation: `cells o` :=
    `{c | M.cellOut e τ c = o}.toFinset`; `evR x` := eventually-exact card ratio. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  -- ACTIVITY GUARDS THROUGHOUT (R13, Fable C2): every per-(e,τ,q₀) mass claim below
  -- carries `M.activeState q₀ e τ` — the note's "realized states only" scope. NO
  -- zero-row law for inactive sources exists (act_row DELETED — undisplayed).
  -- (1) XHD [2b], guarded; two-sided exactness representative-quantified (R2-4):
  xhd_sum : ∀ e τ x c q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
  xhd_no_stray : ∀ e τ x c (h : M.Hgt), h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀, (M.cellEvt e τ x c h q₀ N).Nonempty
  xhd_no_orphan : ∀ e τ x c (h : M.Hgt), h ∉ M.HDom e τ c →
    ∀ q₀ N, M.cellEvt e τ x c h q₀ N = ∅
  -- (2) D4R.0 (event disjointness needs no realization; unguarded is harmless —
  -- empty events are disjoint):
  d4r0 : ∀ e τ x q₀ N c c' (h h' : M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (M.cellEvt e τ x c h q₀ N) (M.cellEvt e τ x c' h' q₀ N)
  -- (3) (iv)-PART-1 [1v], GUARDED (C2's 0 = 1 collapse is gone — at a wild pool the
  -- inactive rows make NO partition claim):
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ τ x q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
  -- (4) (iv)-REP = RS.0(α) verbatim (weighted grouping), GUARDED:
  rep_indep : ∀ e τ (o : T.Out e τ) (x : M.Rep e τ) q₀, q₀ ∈ M.Pools →
    M.activeState q₀ e τ → M.rowVal e τ o q₀ = ∑ c ∈ cells o, M.μcell e τ x c q₀
  -- (5) (iv)-MEAS counting-native (R7), GUARDED:
  meas_card : ∀ e τ x c (h : M.Hgt), h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.cellEvt e τ x c h q₀ N).card : ℝ)
  -- (6) CTS-M(v) HMC (OPEN) + the base tie, target predicate PINNED hK-FREE (G1):
  kstep_one : ∀ e τ β q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ → M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o | routeOf (T.odata e τ o) = .kcol ∧
      ∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, M.rowVal e τ o q₀
  hmc : ∀ k e τ β q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep (k+1) e τ β q₀ = ∑ γ, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
  -- (7) CTS-M(ii) ACT — ONLY the displayed law (S.7(iv): "the verified vanishing …
  -- of every entry into an inactive cell"); the source-side scope is the guards:
  act_target : ∀ e τ β q₀, q₀ ∈ M.Pools → ¬ M.activeState q₀ e β →
    M.kstep 1 e τ β q₀ = 0
  -- (8) CTS-M(iii) INIT + ENT-COUNT, guarded; the I^ent tie at ε's OWN level (G4):
  init_agg : ∀ e τ q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.ιval e τ q₀ = ∑ ε, M.ιsh e τ ε q₀
  init_count : ∀ e τ ε (h : M.Hgt), h ∈ M.ιDom e τ ε → ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.ιshH e τ ε h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.entEvtH e τ ε h q₀ N).card : ℝ)
  ent_count_card : ∀ e τ ε q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((M.entInst e τ ε q₀ (M.entLvl e τ ε)).card : ℚ) = M.entCount e τ ε q₀
    -- "a full count": I^ent_{ε,β₀} IS the card of the ε-instance event at the
    -- shape's own defining level — the counting tie ι_count's polynomial now means
  -- (9) COMP-TYPING, heights once: (COMP-h) = init_count's fixed-height objects;
  -- (COMP-hΣ) = THE one height sum; (COMP-Σ)'s factorization is hmc's duty:
  comp_once : ∀ e τ ε q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)
```

*(Design note: the ONLY height summations in the corpus are xhd_sum and comp_once —
(COMP-Σ)'s "no further height sum" is structural. kstep_one's target predicate is the
PINNED hK-free existential-cast form above (Fable G1) — no SCSData/DegCons/hK is in
LedgerIV's scope, and none is needed.)*

### 2.C Evaluation, rationality burdens (POLY bounds restored), kernel, pools

```lean
def OKat (q₀ : ℚ) : Subring Qq := sorry             -- {f // f.denom.eval q₀ ≠ 0}; U-19
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ := sorry                       -- U-19

/-- The (iv)-POLY/XHD-s presentation pattern (R2-7): a count POLYNOMIAL with its
    displayed degree bound × a height part with GEOMETRIC denominators. -/
structure PolyGeom where
  count : Polynomial ℚ
  degBound : ℕ
  deg_le : count.natDegree ≤ degBound          -- "degree ≤ W_loc(m)" / "≤ W_state(s)"
  geom : Qq                                     -- the XHD-s height sum G
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣ ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a:ℕ))
    -- "G ∈ ℚ(q) with geometric denominators (1 − q^{−a})" (cleared form)
def PolyGeom.val (P : PolyGeom) : Qq := algebraMap (Polynomial ℚ) Qq P.count * P.geom

/-- The rationality burdens: ℚ(q) data in (iv)-POLY form + interpolation to the
    measured rows. Owners: CL-6 (iv)-POLY [1v] (tgP + tg_interp); (J-RAT) [1v]/[2b]
    (jP + j_interp); INIT-RAT [1v] (ιP + ι_interp); + the cofinite-activity face. -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  tgP : ∀ e τ (o : T.Out e τ), PolyGeom
  jP  : ∀ e τ (o : T.Out e τ), PolyGeom
  ιP  : ∀ e τ (ε : M.EntShape e τ), PolyGeom      -- per-shape ENT-COUNT polynomials,
                                                   -- "degree ≤ W_ent(ε)", XHD-s sums
  tg_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → (tgP e τ o).val ∈ OKat q₀
  j_ok  : ∀ e τ o q₀, q₀ ∈ M.Pools → (jP e τ o).val ∈ OKat q₀
  ι_ok  : ∀ e τ ε q₀, q₀ ∈ M.Pools → (ιP e τ ε).val ∈ OKat q₀
  tg_interp : ∀ e τ o q₀ (h : q₀ ∈ M.Pools), routeOf (T.odata e τ o) ≠ .split →
    (evalAt q₀ ⟨(tgP e τ o).val, tg_ok e τ o q₀ h⟩ : ℝ) = M.rowVal e τ o q₀
    -- "valued correctly at every prime power" — against the MEASURED row (R2-5's
    -- rowVal), for the kernel/terminal columns
  j_interp : ∀ e τ o q₀ (h : q₀ ∈ M.Pools), routeOf (T.odata e τ o) = .split →
    (evalAt q₀ ⟨(jP e τ o).val, j_ok e τ o q₀ h⟩ : ℝ) = M.rowVal e τ o q₀
    -- J = the branching-cell mass, EACH CELL ONCE — never the marked T·G
  ι_interp : ∀ e τ ε q₀ (h : q₀ ∈ M.Pools),
    (evalAt q₀ ⟨(ιP e τ ε).val, ι_ok e τ ε q₀ h⟩ : ℝ) = M.ιsh e τ ε q₀
  ι_count : ∀ e τ ε q₀, q₀ ∈ M.Pools →                    -- ENT-COUNT's polynomial IS
    ((ιP e τ ε).count.eval q₀ : ℚ) = M.entCount e τ ε q₀  -- the full count at pools
  allActive_infinite : (allActivePools M).Infinite
    -- (iv)-POLY's cofiniteness face: "only finitely many primes are roots of some
    -- not-identically-zero cell-size polynomial" ⟹ the DEFINED locus is infinite
abbrev RatBurdens.TG (RB) e τ o : Qq := (RB.tgP e τ o).val
abbrev RatBurdens.J  (RB) e τ o : Qq := (RB.jP e τ o).val
noncomputable def RatBurdens.ι (RB) e : T.State e → Qq := fun τ => ∑ ε, (RB.ιP e τ ε).val

def kTarget (T) e τ (o : T.Out e τ) (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e := sorry   -- U-16a region
def Kmat (T) (RB : RatBurdens T M) (e : ℕ)
    (hK : ∀ τ o hk, ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) :
    Matrix (T.State e) (T.State e) Qq := sorry    -- Σ_{kcol o → β} RB.TG e τ o
def bTerm (T) (RB) (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq := sorry
    -- Σ_{termFin o, v(o) = σ'} RB.TG e τ o  (any σ'; supported on verdictImage)

structure EscapeE0 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1:ℚ))) Filter.atTop (nhds 0)

/-- Per-pool package (S.4). `Act` is DETERMINED by CTS-M(ii)'s classification
    (R2-8: act_spec is an iff — an empty Act needs the NOTE's own no-realized-state
    situation, never a modeling choice). -/
structure PoolHyp (T) (M) (RB : RatBurdens T M) (e : ℕ) (hK) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  act_spec : ∀ τ, τ ∈ Act ↔ M.activeState q₀ e τ            -- (R2-8)
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok _ _ τ.2 β.2⟩
  inactive_vanish : ∀ τ β (hok : Kmat T RB e hK τ β ∈ OKat q₀), τ ∈ Act → β ∉ Act →
    evalAt q₀ ⟨_, hok⟩ = 0
  e0 : EscapeE0 A                                            -- ESCAPE(E0), CL-1, OPEN

/-- CTS-M(ii-c)'s per-pool read-off gate (unchanged from REV 2). -/
def AVAgree (P : PoolHyp T M RB e hK q₀) (v : Qq) (bA : P.Act → ℚ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, evalAt q₀ ⟨v, hok⟩ = ((1 - P.A)⁻¹ *ᵥ bA) τ

```

*(`consumedDeltas`/`RegP` are declared in §2.D AFTER `ShapeFam` — declaration order.)*

### 2.D (BDY), shapes, RS.1/RS.4 interfaces (R2-9/10/11/17/19 repaired)

```lean
structure MuHat where val : Qq                    -- the μ̂ fence (no Add, no coercion)

inductive ReadOwner | entrance | block deriving DecidableEq
def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance

structure Shape (T : TableShape n) where           -- length-matched record (REV 2)
  k    : ℕ
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)
  δOf  : Fin k → ℕ+
  σ0   : Multiset T.VType
structure ShapeFam (T : TableShape n) where
  Sh : Finset (Shape T)                            -- [2a] finiteness; CUT-3's image
                                                   -- is the intended instance (W-7)
def consumedDeltas (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ := sorry -- U-16a:
  -- {1} ∪ the split-leg δ's of every roster outcome ∪ ⋃_{Ŝ ∈ F.Sh} image Ŝ.δOf
def RegP (T M) (RB : RatBurdens T M) (p : ℕ) (hK) (F : ShapeFam T) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp T M RB e (hK e) ((p:ℚ)^(δ:ℕ)))

/-- RS.1's interface — NO symbolic β input (R8/R2-9): measured objects only. -/
structure RS1Bundle (T) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK) where
  βmeas : ∀ e ∈ Finset.Icc 1 n, ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
    -- (h_ent-INDEXED measured conditional subtree value; owner [3t])
  β_bdd : ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools →
    βmeas e he h_ent τ σ' q₀ ∈ Set.Icc (0:ℝ) 1     -- "a positive series bounded by 1"
  xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'   -- (XRB) CL-9, OPEN
    -- (discharge = the pinned W-2, S.1's proof under XHD+(JC-INV)+(SIB)/(JC-multi)
    -- +TB-CAP/VP+REL.2(a)(b)(d)+(ns-null) — measure-side, wave 4)
  recursion_meas : ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools) h_ent,
    βmeas e he h_ent τ σ' q₀
      = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
    -- the measured (R_e-lump) fixpoint, EVERY σ' (R2-10: no SigSet restriction);
    -- legs read at q₀^δ — well-formed by M.pools_closed (R2-14); `evalRe` := U-16a's
    -- evaluated right side. Discharge = pinned W-3 (TREE-EXP+ONE-F+(SIB)+PCI).
  βfull : ∀ e ∈ Finset.Icc 1 n, ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
  nsNull : Prop                                    -- the (ns-null) tag; [3t]-closed
  rexact : nsNull → ∀ e he h_ent τ σ' q₀,          -- (R_e-exact) GIVEN (ns-null)
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀

/-- RS.4's chain — the FULL displayed inherited set as explicit components (R2-19),
    with the σ-index = verdict multisets (R2-11) so W-1 typechecks. -/
structure RS4Chain (T) (M) (RB : RatBurdens T M) (hdc : DegCons T) (hK)
    (F : ShapeFam T) where
  L : LedgerIV T M                                 -- the nine CL-5 inputs
  B : RS1Bundle T M RB hdc hK                      -- RS.1's set (xrb, recursion, …)
  hns : B.nsNull                                   -- (ns-null)'s proof demanded HERE
  pools_e0 : ∀ e ∈ Finset.Icc 1 n, ∀ q₀ ∈ allActivePools M,
    Nonempty (PoolHyp T M RB e (hK e) q₀)          -- the all-active face (feeds U-22)
  legs_reg : ∀ p, (p:ℚ) ∈ PrimePools → RegP T M RB p hK F
    -- CL-1's FULL per-pool quantifier (Fable C1): E0/ACT packages at δ = 1 AND every
    -- consumed base-change leg pool p^δ — wild pools included; their READ-OFF is
    -- still gated per object by AVAgree (W-6), never asserted wholesale
  Sigmas : Finset (Multiset T.VType)               -- the splitting types of degree n
  sig_ne : Sigmas.Nonempty
  WshP : Shape T → PolyGeom                        -- CL-17(ii): W_Ŝ in rational form —
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, (WshP Ŝ).val ∈ OKat q₀   -- the OPEN production
                                                   -- duty rides this presentation
  WshVal : Shape T → ℚ → ℝ                         -- measured shallow-shape masses
  wsh_interp : ∀ Ŝ ∈ F.Sh, ∀ q₀ (h : q₀ ∈ M.Pools),
    (evalAt q₀ ⟨(WshP Ŝ).val, wsh_ok Ŝ ‹_› q₀ h⟩ : ℝ) = WshVal Ŝ q₀
  Rval : Multiset T.VType → ℚ → ℝ                  -- measured densities (owner [3t])
  r_bdd : ∀ σ q₀, q₀ ∈ M.Pools → Rval σ q₀ ∈ Set.Icc (0:ℝ) 1
  PrimePools : Set ℚ
  prime_sub : PrimePools ⊆ M.Pools
  prime_infinite : PrimePools.Infinite
  decidedTotal : ℚ → ℝ                             -- the decided-mass series total
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1  -- X.3's density form — CL-4, OPEN,
                                                   -- owner [5]; pinned as W-4
  rs1_equates : ∀ p ∈ PrimePools, (∑ σ ∈ Sigmas, Rval σ p) = decidedTotal p
    -- "RS.1 equates that series with Σ_σ R_σ(p)" — provenance the PINNED W-1e
    -- (RS.1-SH + ONE-F + W-10 convergence), a deferral, never proved here
  rsh_interp : ∀ σ ∈ Sigmas, ∀ p ∈ PrimePools, ∀ hdet,
    ∃ hok : Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p,
      (evalAt p ⟨_, hok⟩ : ℝ) = Rval σ p
    -- the measured densities are the evaluations of THE symbolic Rsh (U-18's one
    -- fixed rational function) — the evaluated shadow of the PINNED W-1; U-28's
    -- symbolic target is Σ_σ Rsh, never a free R field
```

*(R : the symbolic R_σ is NOT a field — RS.2 for R_σ is DERIVED: `Rsh` (U-18) is the
one fixed rational function, and U-28 consumes Rval through `rs1_equates` + the W-1
interpolation `wsh_interp`/blockSolve chain. No conclusion is a field beyond the
note's displayed GIVENs, each tagged CL-4/CL-8/CL-10/CL-17/CL-5/CL-1/CL-9 above.)*

### 2.E `MovesS/SyncDefs.lean` — the PINNED wave-4 Props (R10; no prose deferrals)

```lean
-- minimal carriers for statements whose native vocabulary is MovesT's:
structure TreeIface (T : TableShape n) where       -- W-7's carrier
  Tree : Type                                       -- complete finite canonical trees
  shapeOf : Tree → Shape T                          -- CUT-3's choice-free assignment
structure FiberIface (T) (M : MeasuredSide T) where -- W-10's carrier
  Fib : ∀ e, T.State e → Multiset T.VType → Type    -- complete finite subtrees w/ leaf
  ctbl : ∀ e τ σ', Countable (Fib e τ σ')           --   multiset of type σ′ (TREE-N)
  fibMass : ∀ e τ σ', Fib e τ σ' → ℕ → ℚ → ℝ        -- per-fiber mass given h_ent
structure ReadLedger where                          -- W-8's carrier (one entered path)
  L fe : ℕ ; hfe : fe ≤ L
  charge : ℕ → ℝ                                    -- per-read mass attribution
  Wcharge βcharge : ℝ                               -- the W_Ŝ-side / β-side totals

-- the pinned deferrals (each cites its owner; NONE is a wave-2 unit):
def W1_RS1SH (C : RS4Chain …) (hdet) : Prop :=      -- RS.1-SH's CONTENT (Fable G2):
  ∀ σ ∈ C.Sigmas, ∀ p ∈ C.PrimePools,               -- the MEASURED density identity.
    ∃ hok : Rsh T M RB hdc hK hdet F C.WshP σ ∈ OKat p,
      (evalAt p ⟨Rsh T M RB hdc hK hdet F C.WshP σ, hok⟩ : ℝ) = C.Rval σ p
  -- The SYMBOLIC half of S.2's display ("R_σ = Σ_Ŝ W_Ŝ · Σ ∏ β…") is DEFINITIONAL
  -- here: U-18 DEFINES Rsh as that right side, so the note's identity reduces to
  -- "the measured density Rval IS Rsh's evaluation" — this Prop. No rfl-conjunct.
  -- (Owners MovesT: TREE-EXP, (CUT-WD), (SIB)/CL-10, PCI/CL-8, XRB/CL-9, CL-17(ii).)
def W1e_equates (C : RS4Chain …) : Prop :=          -- ONE-F + convergence regrouping
  ∀ p ∈ C.PrimePools, (∑ σ ∈ C.Sigmas, C.Rval σ p) = C.decidedTotal p
def W1m_marked (B : RS1Bundle …) (hdet) : Prop :=   -- RS.1-MARKED's identification
  ∀ e (he : e ∈ Finset.Icc 1 n) q₀ (h : q₀ ∈ M.Pools),
    ∃ hok : (markedPairing T M RB hdc hK hdet e he).val ∈ OKat q₀,
      (evalAt q₀ ⟨_, hok⟩ : ℝ) = M.markedVal e q₀
def W2_xrb (B : RS1Bundle …) : Prop :=              -- XRB's discharge target = the
  ∀ e he h h' τ σ', B.βmeas e he h τ σ' = B.βmeas e he h' τ σ'   -- field's statement
def W3_recursion (B : RS1Bundle …) : Prop :=        -- the measured fixpoint's
  ∀ e he τ σ' q₀ h h_ent, B.βmeas e he h_ent τ σ' q₀             -- discharge target
    = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => B.βmeas e' he' h_ent)
def W4_x3 (C : RS4Chain …) : Prop := ∀ p ∈ C.PrimePools, C.decidedTotal p = 1
def W7_shapeFam (F : ShapeFam T) (TI : TreeIface T) : Prop :=
  ∀ t : TI.Tree, TI.shapeOf t ∈ F.Sh                -- CUT-3: every complete tree
                                                    -- carries exactly ONE listed shape
def W8_bdy (RL : ReadLedger) : Prop :=              -- (BDY) consumption: the entering
  RL.Wcharge = ∑ r ∈ Finset.Icc 0 RL.fe, RL.charge r ∧                -- read is W-side
  RL.βcharge = ∑ r ∈ Finset.Icc (RL.fe + 1) RL.L, RL.charge r         -- β charges none
def W10_convergence (B : RS1Bundle …) (FI : FiberIface T M) : Prop :=
  ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools →              -- S.2 CONVERGENCE display: the
    HasSum (fun f : FI.Fib e τ σ' => FI.fibMass e τ σ' f h_ent q₀)   -- fiber series
      (B.βmeas e he h_ent τ σ' q₀)                  -- sums to β — positive, ≤ 1
                                                    -- (β_bdd), Tonelli-rearrangeable
```

W-5 (nsNull's discharge) is the field `RS4Chain.hns` — demanded, not deferred-loose.
W-6 (wild-pool read-off) is the Prop `AVAgree` (§2.C), cited per consumption site.
W-9 is RETIRED (subsumed by the R7 event carrier in LedgerIV). W-11 (instantiation of
every §2 structure by the REAL CTS objects) is a wave-4 PROCESS gate (§5), not a Prop.

---

## 3. The unit DAG — REV 4: 45 units (18 easy / 27 medium / 0 hard)

### Layer S0 — dispatch, (SCS), (BDY) [9]

**U-1 `dispatch_spec` · easy — unchanged from REV 2** (route iff-triple; omega).
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION … (c ≥ 1 with m = 1 forces c = 1)".

**U-2 `ktri` · easy — unchanged** (DegCons + m ≥ 2 ⟹ every member size < e).
moves_ref: "at m ≥ 2 EVERY e_j < e". **U-3 `kcol_agree` · easy — unchanged.**

**U-4 `scs_flank` · medium — hypotheses now SUFFICIENT (R2-1, R2-2).**
`statement`: as REV 2 (flankCount = 0 ∧ resFactors singleton ∧ W = e·ℓ ∧ g·μ = ℓ at
m = 1). moves_ref: "m = 1 forces NO flank side (the read side spans the window:
e·ℓ = W) and a SINGLETON residual shape λ = {(g, μ)}". deps: Defs · hyp: SCSData ·
sketch: m = 1 ⟹ member positions = Fin 1 ⟹ `selIdx` is the only position; `memberOf`
avoids it (`memberOf_ne_sel`, now unconditional) yet is injective into it ⟹ its domain
is EMPTY ⟹ flankCount = 0 AND no non-selected residual factor (so `sel_mem` makes
resFactors the singleton); `flank_zero` gives flankWidth = 0; `window_comp` gives
W = e·ℓ; `res_sum` on the singleton gives g·μ = ℓ. Every step now has its field.

**U-5 `scs_stage` · easy — unchanged** (W′D′ = WD via stage_D/stage_W + U-4).
**U-6 `scs` · medium — unchanged** (kcol ⟹ all member sizes = e; uses
`sel_continuing` + cluster_child/cluster_parent + U-4/U-5; PRODUCES the `hK`
argument of every Kmat consumer).

**U-7a `bdy_edge` · Bdy.lean · easy — split (R2-15).**
`theorem bdy_edge : ∀ fe r, (bdyEdgeOwner fe r = .entrance ↔ r ≤ fe) ∧`
`(bdyEdgeOwner fe r = .block ↔ fe < r)`. moves_ref: "the ENTERING READ of a block
entrance belongs to the ENTRANCE SIDE".

**U-7b `bdy_node_shadow` · BdyNode.lean · easy — split.**
`theorem bdy_node_shadow : ∀ fe, bdyNodeOwner fe fe = .block ∧`
`bdyEdgeOwner fe fe = .entrance ∧ ∀ r ≠ fe, bdyNodeOwner fe r = bdyEdgeOwner fe r`.
moves_ref: "the first entrance node ν is BLOCK-side as a STATE INDEX …, while the
edge INTO ν is entrance-side MASS".

**U-7c `bdy_mass_split` · BdyMass.lean · easy — split.**
`theorem bdy_mass_split (μm : ℕ → ℝ) (L fe) (h : fe ≤ L) :`
`∑ r ∈ Finset.range (L+1), μm r = (∑ r ∈ Finset.Icc 0 fe, μm r) +`
`(∑ r ∈ Finset.Icc (fe+1) L, μm r)`. moves_ref: "no read omitted, none double-charged".

### Layer S1 — (K-SUB) [4]

**U-8 `ksub_regroup` · medium — SigSet replaced by verdictImage (R9, R2-10).**
`statement` (per e ∈ Icc 1 n, τ, hK from U-6):
`(∑ β, Kmat T RB e hK τ β) + (∑ σ' ∈ verdictImage T e τ, bTerm T RB e σ' τ) +`
`(∑ o ∈ splitOuts T e τ, RB.J e τ o) = ∑ o : T.Out e τ, routedMass RB e τ o`
(routedMass := J on split, TG otherwise). moves_ref: "(K-SUB) Σ_β K_e(τ,β) +
Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell one-step mass, per cell once) = 1".
deps: U-1, U-6 · hyp: none beyond structures (verdictImage is exhaustive for the
terminal columns BY CONSTRUCTION — the R2-10 covering defect is gone) · sketch:
partition by routeOf; fiberwise regrouping by kTarget / by verdicts.

**U-9a `ksub_eval` · medium — ACTIVITY-GUARDED (R13).** Per pool, per representative,
AT ACTIVE STATES: `∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → evalAt q₀ (routedMass-sum)
= 1`. deps: U-8, U-19 · hyp: LedgerIV.part1 + rep_indep (both now guarded) +
RB.tg_interp/j_interp — the note's bracket "GIVEN the (iv) ledger + DEG-CONS + the
(m, c) CLASSIFICATION with its (SCS) clause", scoped "restricted per CTS-M(ii) to the
ACTIVE block" · sketch: interp → rowVal; rep_indep → x-grouped cell sum;
`Finset.sum_fiberwise` over cellOut; part1 → 1.

**U-9b `ksub` · medium — locus updated.** The SYMBOLIC (K-SUB) `= 1` in Qq, via U-9a
at every ALL-ACTIVE pool (activity supplied by the locus) + U-27 infinitude on
`RB.allActive_infinite`. deps: U-8, U-9a, U-27.

**U-10 `ksub_pool` · medium — nonnegativity DERIVED and ROUTED (R2-12).**
`statement`: `theorem ksub_pool (L : LedgerIV T M) (P : PoolHyp T M RB e hK q₀)`
`(τA : P.Act) : (∀ βA : P.Act, 0 ≤ P.A τA βA) ∧ (∑ βA : P.Act, P.A τA βA) ≤ 1`
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0 (the
ns-bound tail rides INSIDE the K_e term)". deps: U-9a, U-19 · hyp: LedgerIV +
RatBurdens ONLY — the routed nonnegativity is DERIVED: for non-split o,
eval TG = rowVal = Σ μcell ≥ 0 (tg_interp + rep_indep + a μcell-nonneg lemma from
meas_card's card ratios at heights in the domain + xhd_sum); for split o likewise via
j_interp. NO hypothesis about TG on split outcomes or J on non-split outcomes exists
anywhere (the R2-12 swap is structurally impossible now) · sketch: evaluate U-9a,
drop the nonneg exit sums, restrict along act_spec/inactive_vanish (τA ∈ Act supplies the
activity guard via act_spec — U-9a fires at exactly the note's scope).

### Layer S2 — the ℚ(q) system and its solve [12]

**U-11 `decompFintype` · medium — unchanged** (Fintype on multiset decompositions).
**U-12 `powSubst` · medium — unchanged** (δ : ℕ+; `IsFractionRing.lift`).

**U-12b `powSubst_OKat_evalAt` · PowSubstOK.lean · easy — NEW (serves R14).**
`theorem powSubst_OKat (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ:ℕ))) :`
`powSubst δ f ∈ OKat q₀` and `evalAt q₀ ⟨powSubst δ f, _⟩ = evalAt (q₀^(δ:ℕ)) ⟨f, h⟩`
— OK-membership and evaluation transport along a base-change leg: the denominator of
`powSubst δ f` divides `f.denom.comp (X^δ)`, and `(f.denom.comp (X^δ)).eval q₀ =
f.denom.eval (q₀^δ) ≠ 0`. deps: U-12, U-19 · sketch: `Polynomial.eval_comp` +
divisibility of denominators under ring homs.
**U-13 `solve_iff` · easy — unchanged.** **U-14 `solve_exists_unique` · medium —
unchanged.** **U-15 `solve_cramer` · medium — unchanged** (adjugate/Cramer; RS.2's
conditionality = RatBurdens by construction, now in (iv)-POLY form with degree bounds).

**U-16a1 `bSplit_def` · BSplitDef.lean · medium — SPLIT + the halted-member clause
DISPLAYED (Fable G3).** Defines `kTarget` and `bSplit` (DegCons argument licensing
smaller-block legs via U-2), with the summand's def-equation PINNED:
`bSplit T RB hdc e he βlt σ' τ = ∑ o ∈ splitOuts T e τ, RB.J e τ o *`
`∑ g : {g : Fin (T.odata e τ o).m → Multiset T.VType // σ' = ∑ j, g j},`
`∏ j, legFactor o g j` where, for member μ_j := (T.odata e τ o).mem.get j,
`legFactor = if v : verdict-halted μ_j v then (if g j = {v} then 1 else 0)`
`            else powSubst μ_j.δ (βlt μ_j.size (ktri-bound) (state of μ_j) (g j))`
— "τ-halted members contribute FACTOR 1 with σ_j their verdict value, per §T.4's
leaf convention" (S.0): a halted leg forces its σ_j to the verdict SINGLETON
(indicator), continuing legs are β at q^δ. moves_ref: "b_e^split(τ)(σ′) :=
Σ_{o branching} J_{τ,o}(q) · Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j})
[… the product ranges over ALL branch members]". deps: U-1, U-2, U-11, U-12.

**U-16a2 `evalRe_def` · EvalReDef.lean · medium — split (G3).** Defines `evalRe`, the
per-pool EVALUATED right side of (R_e-lump) that `recursion_meas` cites: eval-K-row ·
β̂ + eval-bTerm + the evaluated split summand with MEASURED legs β̂ at q₀^(δ:ℕ)
(well-typed by `pools_closed`; halted legs the same indicator as U-16a1). deps:
U-16a1, U-19.

**U-16a3 `consumedDeltas_def` · ConsumedDeltas.lean · easy — split (G3).**
`consumedDeltas T F := {1} ∪ (split-leg δ's over the full roster) ∪ ⋃_{Ŝ ∈ F.Sh}
image Ŝ.δOf` — with the docstring duty: these are ABSOLUTE indices ([2r] (e2), the
`Member.δ` convention), so leg-within-leg pools stay inside the roster; an
instantiation recording relative indices MUST close the set multiplicatively (a
statement-fence event). deps: Defs.

**U-16b `blockSolve` · medium — unchanged** (strong recursion on e ∈ Icc 1 n; σ′
UNRESTRICTED per R2-10: the solve is a function of every σ' : Multiset VType).

**U-16c `blockSolveTot` · BlockSolveTot.lean · medium — NEW (R2-17).** The σ′-FREE
totalized triangular solve: `bTot(τ) := Σ_{term o} TG + Σ_{split o} J · ∏_j legTot`
(halted legs 1, continuing legs `powSubst δ (blockSolveTot …)`), and
`blockSolveTot e := (1 - Kmat)⁻¹ *ᵥ bTot` — the exit-total vector the MARKED pairing
consumes. moves_ref: "the scalar output ι_e^T (I − K_e)^{−1} b_e" (ORIENTATION).
deps: U-14, U-16a pattern · sketch: same WF recursion as U-16b, scalar per state.

**U-17a `blockSolve_spec` · medium** — (R_e-lump) defining equation, EVERY σ′
(R2-10: no SigSet). **U-17b `rexact_solve` · medium — unchanged** ((R_e-exact) from
`rexact` + `nsNull`). **U-18 `rsh_def` · medium — unchanged** (shConv/Rsh from the
Shape record + blockSolve; now takes `WshP ·` as the W_Ŝ presentation). **U-18b
`interp_unique` · easy — unchanged** (interpolant uniqueness on infinite OK sets).

### Layer S3 — pools, evaluation, E0 consequences [10]

**U-19 `evalAt` · medium — unchanged.** **U-20 `eval_det` · easy — unchanged**
(INFRA; moves_ref the S.4(ii) "K_e(p) = A" reading). **U-21a `pow_fixed_vector` ·
easy — unchanged.**

**U-21b `mulVec_abs_bound` · medium — [Nonempty ι] added (R2-16).**
`theorem mulVec_abs_bound [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℚ}`
`(hA : ∀ i j, 0 ≤ A i j) (v : ι → ℚ) (k i) : |((A ^ k) *ᵥ v) i| ≤`
`(Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) * ((A ^ k) *ᵥ 1) i`.
deps: U-23b.

**U-21c `e0_det_ne_zero` · medium** — `EscapeE0 A → (1 - A).det ≠ 0`; the EMPTY case
is `Matrix.det_isEmpty` (det = 1 ≠ 0 — an empty active block is vacuously
nonsingular, matching the note's "realized states only" scope); the nonempty case
uses U-21a/b. deps: U-21a, U-21b.

**U-22 `rs3_det_symbolic` · medium — quantifiers FIXED (R2-13).**
`statement`: `theorem rs3_det_symbolic (T M RB hdc) (hK : ∀ e ∈ Finset.Icc 1 n, …)`
`(hact : ∀ e ∈ Finset.Icc 1 n, ∀ q₀ ∈ allActivePools M,`
`Nonempty (PoolHyp T M RB e (hK e ‹_›) q₀)) :`
`∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e ‹_›)).det ≠ 0`
— per-block hypotheses for the per-block conclusion, `e` bound INSIDE both.
moves_ref: "at all-active primes (cofinitely many …) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations
is 0". deps: U-19, U-20, U-21c, U-27 · hyp: RB.allActive_infinite (the (iv)-POLY
cofiniteness face, now over the DEFINED locus) + per-pool packages at that locus ·
sketch: at an all-active pool Act = univ (act_spec + the locus definition); if
det = 0 in Qq its evaluation vanishes there (U-20), contradicting U-21c.

**U-23a `neumann_partial` / U-23b `pow_entry_nonneg` / U-23c `pow_entry_tendsto` ·
easy ×3 — unchanged.** **U-23d `e0_inv_nonneg` · medium — unchanged** (consumer
[4]/SQ.2 only).

### Layer S4 — RS.1-DEEP/RS.2 derivation, the marked pairing, RS.4, the gate [6]

**U-24a1 `active_solve_meas` · ActiveSolve.lean · medium — REDESIGNED (Fable C1;
R14): the measured value IS the active-subsystem solve, PER POOL, guards consumed.**
`statement`: for B : RS1Bundle, L : LedgerIV, e ∈ Icc 1 n, σ', h_ent, ANY relevant
pool q₀ with package `P : PoolHyp T M RB e (hK e) q₀` (RegP-supplied — wild pools
INCLUDED), and any τA : P.Act:
`B.βmeas e he h_ent τA σ' q₀ = ((1 - P.A)⁻¹ *ᵥ bhatMeas P B σ' h_ent) τA`
where `bhatMeas` := the evaluated exit vector with MEASURED legs: eval-bTerm + the
split summand with legs `B.βmeas … (q₀^(δ:ℕ))` (pools_closed-typed).
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)" +
"Every probabilistic claim in S.4/SQ.2 is about K_e restricted per CTS-M(ii) to the
ACTIVE block". deps: U-13, U-14 (over ℚ), U-16a2, U-19, U-21c · hyp: B.recursion_meas
(W-3) + B.xrb + P (E0 inside) + L (act_target + inactive_vanish give SUBSYSTEM
CLOSURE: entries out of Act vanish, so the active restriction of the measured system
is itself linear) · sketch: β̂ := (βmeas ·)_Act satisfies β̂ = Â β̂ + b̂ by
recursion_meas restricted along the closure; (1 − Â) invertible by U-21c on P.e0
(empty Act: both sides live on an empty type — trivial); uniqueness of the evaluated
solution. NO induction, NO leg evaluation, NO hok claim — the legs enter b̂ as
measured values. **CLOSES from the note's own display; the REV-3 hardness was the
unhypothesized (ii-c) burden, now U-24a2's explicit guard.**

**U-24a2 `interp_read_off` · ReadOff.lean · easy — the (ii-c) gate consumed (C1).**
`statement`: additionally GIVEN `hAV : AVAgree P (blockSolve T RB hdc hK hdet e he τA
σ') (bhatMeas P B σ' h_ent) τA` (the note's sealed per-pool read-off check, per
OBJECT): `∃ hok, (evalAt q₀ ⟨blockSolve … e he τA σ', hok⟩ : ℝ) = B.βmeas e he h_ent
τA σ' q₀`. moves_ref: "the sealed check that the evaluated object's q₀-value … equals
the active-subsystem solve there must pass BEFORE it may be read off; a pole
SURVIVING cancellation at a wild pool is (ii-c)'s FAIL" + the (e3)-FENCE. deps:
U-24a1 · sketch: AVAgree supplies hok + the active-solve value; rewrite with U-24a1.
Uncancelled wild poles are EXCLUDED BY HYPOTHESIS — never claimed absent.

**U-24b `rs2_unique_interp` · Rs2Unique.lean · medium — CONDITIONAL identification
(C1).** `statement`: GIVEN an INFINITE pool set S ⊆ M.Pools with, at every q₀ ∈ S,
a package P and the AVAgree read-off for every (e, τA, σ') consumed (the U-24a2
hypotheses — an explicit `hread` bundle): any family f that is OK on S and
interpolates βmeas there equals `blockSolve …` — "every β_{e,τ}(σ′) is ONE FIXED
rational function" (RS.2's fixedness), RS.1-DEEP's symbolic reading. moves_ref:
"every β_{e,τ}(σ′) is one fixed rational function". deps: U-24a1, U-24a2, U-18b,
U-27 · hyp: hread (the per-pool (ii-c) burden, OPEN, quantified over S — provenance
the gates/W-6; allActive_infinite supplies the CANDIDATE locus but activity alone
does not discharge AVAgree at the legs) · sketch: U-24a2 across S gives blockSolve
interpolates on S; U-18b uniqueness. Cramer form via U-15.

**U-25 `marked_def` · easy — aggregate now DEFINED (R2-17).**
`noncomputable def markedPairing … : MuHat := ⟨RB.ι e ⬝ᵥ ((1 - Kmat T RB e (hK e))⁻¹`
`*ᵥ bTot T RB hdc e he)⟩` (bTot from U-16c) + the no-Add/no-coercion fence check.
moves_ref: "(RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed
MARKED-entrance total … NEVER summed into R_σ." Identification with `M.markedVal` =
the PINNED W1m (never claimed here).

**U-27 `ratfunc_eval_infinite` · medium — unchanged** (the shared infinitude engine).

**U-28 `rs4_rational_step` · Rs4.lean · medium — full inherited set (R2-19).**
`statement`: `theorem rs4_rational_step (C : RS4Chain T M RB hdc hK F)`
`(hdet : ∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e ‹_›)).det ≠ 0) :`
`(∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) = 1`
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q … RS.4 inherits EVERY condition of
the block solve". deps: U-18, U-27 · hyp: THE DISPLAYED INHERITED SET, all explicit
in RS4Chain (R2-19): C.L (nine CL-5 inputs) · C.B (RS.1's set: xrb/CL-9,
recursion_meas/CL-10+CL-8 provenance) · C.hns ((ns-null) proof) · C.pools_e0 +
C.legs_reg (ESCAPE(E0)/CL-1 in its FULL per-pool quantifier — REV 4, Fable C1) ·
C.WshP/wsh_ok (CL-17(ii)) · RB in (iv)-POLY form (CL-6)
+ XHD-s geoms + INIT-RAT ιP + (J-RAT) jP · C.x3_total (X.3/CL-4, pinned W-4) ·
C.rs1_equates (pinned W-1e) · C.rsh_interp (pinned W-1's shadow) · sketch:
eval(Σ Rsh − 1) at p ∈ PrimePools = Σ Rval − decidedTotal = 0 (rsh_interp,
rs1_equates, x3_total); prime_infinite + U-27. The docstring lists every tag: the
acceptance fence "may NOT be marked unconditional before those close" verbatim.

**U-29 `consistency_n2` · ConsistencyN2.lean · medium — RENAMED + full coverage
(R2-20, R11).** Constructs, at n = 2, simultaneous instances of ALL §2 structures:
TableShape (one block-2 state, W6's roster), MeasuredSide (boxes = the level-N
residue boxes of the displayed 1×1 instance; synthetic-but-nontrivial cell events),
LedgerIV, RatBurdens (the W6 kernel entry in PolyGeom form), SCSData, DegCons,
PoolHyp at q₀ = 2 (1×1 EscapeE0: the entry < 1, powers → 0 by geometric decay),
ShapeFam (the n = 2 root shapes), RS1Bundle (βmeas := the evaluated solve — then
recursion_meas/xrb hold by construction), RS4Chain (decidedTotal := Σ Rval) — and
CHECKS: the solve's denominator is q² + q + 1 (up to units). CLAIM (honest, R11):
schema consistency — every structure is simultaneously inhabitable by a nontrivial
instance matching the note's displayed n = 2 shadow. NOT claimed: inhabitation by
the intended CTS instance (wave-4 process gate, §5). moves_ref: "The n = 2 instance
is the 1×1 case (W6's geometric series, denominator q² + q + 1)". deps: U-16b/c.

---

## 3c. Full specs for units carried forward (self-contained: REV 2 is retired)

**U-1** `theorem dispatch_spec (o : Outcome V State) (h1 : 1 ≤ o.m) (hc : o.c ≤ o.m) :
(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧
(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)` · sketch: unfold, split_ifs, omega.

**U-2** `theorem ktri (hdc : DegCons T) (he : e ∈ Finset.Icc 1 n) {τ o}
(hm : 2 ≤ (T.odata e τ o).m) : ∀ μ ∈ (T.odata e τ o).mem, μ.size < e` · sketch:
μ.size + (m−1) ≤ Σ sizes ≤ e via size_pos on the other members; omega.

**U-3** `theorem kcol_agree (hdc) (he) (hmem : ∃ μ ∈ mem, μ.continuing ∧ μ.size = e) :
(T.odata e τ o).m = 1` · sketch: contrapose with U-2.

**U-5** `theorem scs_stage (S : SCSData T) (hm : (T.odata e τ o).m = 1) :
S.W' e τ o * S.D' e τ o = S.W e τ o * S.D e τ o` · moves_ref: "W′·D′ = μ·e·g·D =
(g·μ)·e·D = ℓ·e·D = W·D" · sketch: stage_W/stage_D rewrite; U-4's g·μ = ℓ, W = e·ℓ; ring.

**U-6** `theorem scs (S : SCSData T) (hdc : DegCons T) (he) (hk : routeOf (T.odata e τ o)
= .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e` · moves_ref: "(SCS) a (c = 1, m = 1)
outcome's single child inherits the block size: e₁ = e" · sketch: hk + U-1 ⟹ m = 1;
the only member is selIdx, continuing (sel_continuing); cluster_child + U-5 +
cluster_parent: size = W′D′ = WD = e.

**U-11** `instance decompFintype [DecidableEq V] (m σ') :
Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'}` · sketch: induct on m; each g 0 ≤ σ'
ranges over finitely many sub-multisets.

**U-12** `noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq` + `powSubst_X/`_C lemmas ·
moves_ref: "composed with q ↦ q^{δ_j} … ([2r] (e2), δ absolute)" · sketch:
`IsFractionRing.lift` over `aeval (X^(δ:ℕ))`; δ ≥ 1 ⟹ nonzero ↦ nonzero.

**U-13** `theorem solve_iff [Fintype ι] (K : Matrix ι ι Qq) (b β) :
β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b` · sketch: sub_mulVec/one_mulVec; sub_eq_iff.

**U-14** `theorem solve_exists_unique [Fintype ι] [DecidableEq ι] (hdet :
(1 - K).det ≠ 0) : ∃! β, β = K *ᵥ β + b` (witness `(1-K)⁻¹ *ᵥ b`) · Mathlib:
`isUnit_iff_ne_zero` + `Matrix.isUnit_iff_isUnit_det` + `mul_nonsing_inv`/
`nonsing_inv_mul` + `mulVec_mulVec`.

**U-15** `theorem solve_cramer (hdet) : (1 - K)⁻¹ *ᵥ b = fun τ => ((1 - K).det)⁻¹ *
((1 - K).adjugate *ᵥ b) τ` · moves_ref: "β_e = adj(I − K_e) b_e / det(I − K_e)
entrywise" · Mathlib: `Matrix.inv_def`/`cramer_eq_adjugate_mulVec`/
`det_smul_inv_mulVec_eq_cramer`.

**U-16b** `noncomputable def blockSolve (T RB hdc hK hdet) : ∀ e ∈ Finset.Icc 1 n,
T.State e → Multiset T.VType → Qq` — strong recursion on e; body
`(1 - Kmat T RB e (hK e))⁻¹ *ᵥ (bTerm T RB e σ' + bSplit T RB hdc e he βlt σ')` ·
moves_ref: "blocks solve bottom-up, each b_e^split leg already solved".

**U-17a** `theorem blockSolve_spec (e ∈ Icc 1 n) (σ' : Multiset T.VType) :
blockSolve … e he · σ' = Kmat … *ᵥ (blockSolve … e he · σ') + bTerm … σ' +
bSplit … (blockSolve-restriction) σ'` · moves_ref: "(R_e-lump) β_e = K_e β_e +
b_e^{term,fin} + b_e^split [UNCONDITIONAL]".

**U-17b** `theorem rexact_solve (B) (hns : B.nsNull) : ∀ e he h_ent τ σ' q₀,
B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀` · moves_ref: "(R_e-exact)
β_e^full = β_e [GIVEN (ns-null) — CLOSED at [3t] §T.2]" · sketch: fire `rexact`.

**U-18** `noncomputable def shConv (…) (Ŝ : Shape T) (σ) : Qq := ∑ g : {g : Fin Ŝ.k →
Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i}, ∏ i, powSubst (Ŝ.δOf i)
(blockSolve … (Ŝ.eOf i) (Ŝ.eIcc i) (Ŝ.τOf i) (g i))` and `Rsh … (WshP) (σ) :=
∑ Ŝ ∈ F.Sh, (WshP Ŝ).val * shConv … Ŝ σ` · moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) ·
Σ_{σ = σ₀(Ŝ) ⊎ …} ∏ β_{e_i,τ_i}(σ_i)(q^{δ_i})".

**U-18b** `theorem interp_unique (S : Set ℚ) (hS : S.Infinite) (f g : Qq)
(hf hg : ∀ x ∈ S, · ∈ OKat x) (h : ∀ x ∈ S, evalAt x f = evalAt x g) : f = g` ·
sketch: U-27 on f − g.

**U-19** `def OKat (q₀) : Subring Qq` ({f | f.denom.eval q₀ ≠ 0}) +
`noncomputable def evalAt (q₀) : OKat q₀ →+* ℚ` + `evalAt_coe` · sketch: denom
divisibility closure; `RatFunc.eval_add`/`eval_mul` under the membership hypotheses.

**U-20** `theorem eval_det [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (OKat q₀)) :
evalAt q₀ M.det = (M.map (evalAt q₀)).det` · via `RingHom.map_det`.

**U-21a** `theorem pow_fixed_vector (h : A *ᵥ v = v) : ∀ k, (A ^ k) *ᵥ v = v`.

**U-23a** `(1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k` (telescope).
**U-23b** `(∀ i j, 0 ≤ A i j) → ∀ k i j, 0 ≤ (A ^ k) i j` (induction).
**U-23c** `EscapeE0 A → ∀ i j, Tendsto (fun k => (A ^ k) i j) atTop (nhds 0)`
(squeeze between 0 and `((A^k) *ᵥ 1) i`).
**U-23d** `EscapeE0 A → ∀ i j, 0 ≤ (1 - A)⁻¹ i j` · moves_ref: "the Neumann series
converges, and (I − A(q₀))^{−1} ≥ 0" · sketch: `(1-A)⁻¹ = Σ_{m<k} A^m + (1-A)⁻¹ A^k`
(U-23a); nonneg partial sums (U-23b); remainder → 0 (U-23c); closed limit.

**U-27** `theorem ratfunc_eval_infinite (f : Qq) (S : Set ℚ) (hS : S.Infinite)
(hden : ∀ x ∈ S, f.denom.eval x ≠ 0) (hval : ∀ x ∈ S, RatFunc.eval (RingHom.id ℚ) x f
= 0) : f = 0` · moves_ref: "a rational function equal to 1 at infinitely many prime
powers is identically 1" (consumers apply to f − 1) · sketch: num vanishes on S;
`Polynomial.eq_zero_of_infinite_isRoot`; `RatFunc.num_eq_zero_iff`-style closure.

---

## 3b. Load-bearing DAG edges (acyclic)

U-1 → {U-3, U-6, U-8, U-16a1} · U-2 → {U-3, U-16a1} · U-4 → U-5 → U-6 · U-6 ⟹ `hK`
for {U-8, U-16b/c, U-22, U-24a1/a2/b, U-25, U-29} · U-8 → U-9a → {U-9b, U-10} ·
U-11, U-12 → {U-16a1, U-18} · U-12, U-19 → U-12b → {U-24a2 plumbing, W-1 hok} ·
U-13 → U-14 → {U-15, U-16b/c, U-24a1} · U-16a1 → U-16a2 → U-24a1; U-16a1 → U-16b →
{U-17a, U-18, U-29}; U-16a3 → RegP · U-16c → U-25 · U-19 → {U-9a, U-10, U-20, U-22,
U-16a2} · U-23b → U-21b; U-21a, U-21b → U-21c → {U-22, U-23d, U-24a1} · U-23a/b/c →
U-23d · U-27 → {U-9b, U-18b, U-22, U-24b, U-28} · U-24a1 → U-24a2 → U-24b · U-22 →
hdet of {U-16b/c, U-24a2/b, U-25, U-28} · RegP/AVAgree → {U-24a1, U-24a2, U-24b,
RS4Chain.legs_reg} (the guards are CONSUMED — Fable C1's symptom is gone).
CONSUMPTION-DAG discipline: U-24a1/a2/b consume `xrb`/`recursion_meas`; nothing
proves toward `xrb`; no PCI site is consumed by S.1-shaped content.

## 4. Trust surface & audit flags (REV 3)

1. NO `True` fields; NO vacuous disjuncts (R2-1 struck); grep duties at phase E:
   `': True'` and `'∨ True'` both empty on Defs/SyncDefs.
2. `xrb` is the honest XRB interface (open; pinned W-2). `recursion_meas` (pinned
   W-3), `x3_total` (W-4), `rs1_equates` (W-1e), `rsh_interp` (W-1 shadow),
   `wsh_interp`, and `W1m` are the measured GIVENs — each maps to a note tag, none
   is a wave-2 conclusion.
3. The event carrier (R7) is the (iv)-MEAS/D4R.0/XHD trust boundary: masses =
   eventually-exact card ratios; auditor checks the ledger's nine fields against
   S.0's displayed ledger 1:1.
4. `rowVal` is RS.0(α)'s object; `rep_indep` is its weighted-grouping form VERBATIM
   (R2-5) — no cellwise strengthening exists.
5. PART-2's marked surplus row has NO carrier (unconsumable). ESCAPE-UNIF does not
   exist. `Act` is determined by `act_spec` (R2-8). `allActivePools` is a defined
   locus; only its infinitude is a burden.
6. `PolyGeom` restores the (iv)-POLY degree bounds + XHD-s geometric denominators
   (R2-7); `Pools` is pinned to prime powers with the δ-closure law (R2-7/14).
7. U-29's claim is SCHEMA CONSISTENCY (R11) — flag any reading of it as intended-
   instance inhabitation; that is the §5 wave-4 process gate.
8. S.7 / probe roster / (CUT-WD)'s proof / junk determinants: census-side; (BDY) in
   scope as U-7a/b/c + pinned W-8.
9. (REV 4) The ACT scope is GUARDS, not zero rows: `act_row` DELETED (undisplayed);
   part1/rep_indep/xhd_sum/no_stray/meas_card/kstep laws guarded by `activeState` —
   wild pools instantiable; auditor checks no ledger field asserts a mass claim at an
   unrealized source.
10. (REV 4) `RegP` and `AVAgree` are CONSUMED: U-24a1 (packages at every relevant
   pool incl. wild legs), U-24a2 (the per-object (ii-c) read-off hypothesis), U-24b
   (`hread` over an infinite read-off-valid family), `RS4Chain.legs_reg`. Flag any
   future unit that reads a numeric β/R value without citing a package + AVAgree.

## 5. Conventions (phase E / prover fleet) + census

Build per file `lake env lean LeanUrat/MovesS/<file>.lean`; `#print axioms` per unit
(Lean-core only; `sorryAx` flagged). Skeleton `sorry`s (`OKat`/`evalAt` bodies,
`kTarget`, `Kmat`, `bTerm`, `consumedDeltas`) elaborate at phase E BEFORE fan-out;
`bSplit`/`evalRe`/`bTot` live in U-16a/c. Statement changes to §2/§2.E = statement-
fence events. WAVE-4 PROCESS GATE (W-11): before MovesS results are cited by MovesU
with real semantics, MovesV/MovesT must exhibit instances of every §2 structure over
the real CTS objects and discharge W-1/W-1e/W-1m/W-2/W-3/W-4/W-7/W-8/W-10; the
campaign ledger tracks this per structure.

**Census (REV 4): 45 units = 18 easy / 27 medium / 0 hard.** Easy {U-1, U-2, U-3,
U-5, U-7a, U-7b, U-7c, U-12b, U-13, U-16a3, U-18b, U-20, U-21a, U-23a, U-23b, U-23c,
U-24a2, U-25}; medium the remaining 27. NO hard units remain: the REV-3 hard (U-24a's
strong-induction identification) DISSOLVED under the R14 repair — its difficulty was
exactly the unhypothesized per-pool (ii-c)/E0 burden, which the note keeps as open
per-pool hypotheses and REV 4 now consumes as such (RegP/AVAgree in U-24a1/a2/24b).

---

## 6. Findings → repairs (cumulative; REV-2 audit rows kept, REV-3 rows appended)

**Round 1 audit (19c/3g) → REV 2:** all 22 repaired as recorded in the REV-2 table
(True-tags → contentful fields; XRB de-defined; RatBurdens; hK argument; SP.1
carriers; (BDY) halves; sig_covers; PART-1 chain; δ:ℕ+; DegCons in bSplit; Icc 1 n;
U-17b; Shape record; U-22 package; recursion de-malformed; RS.1-SH/MARKED deferred;
RS.4 two inputs; inhabitation batch; U-10 typing; U-20 ref; 3 hards split). REV-2
residuals found by the re-audit are below.

| R2-# | class | REV-3 repair | where |
|---|---|---|---|
| 1 | crit | `∨ True` disjunct DELETED; `memberOf_ne_sel` states the plain inequality | §2.A |
| 2 | crit | `flank_zero : flankCount = 0 → flankWidth = 0` added; U-4's chain complete | §2.A, U-4 |
| 3 | gap | declaration order fixed (data before laws; SplitTy eliminated; consumedDeltas moved after ShapeFam); order = spec | §2 |
| 4 | crit | ORCHESTRATOR RULING: counting-native event carrier (Box/cellEvt/card-ratio masses); XHD two-sided exactness (no_stray/no_orphan), D4R.0 as event disjointness, (iv)-MEAS as meas_card | R7, §2.B |
| 5 | crit | `rowVal` carrier + `rep_indep` = RS.0(α)'s weighted-grouping equality VERBATIM (row-level, not cellwise) | §2.B |
| 6 | crit | `kstep_one` ties kstep to the measured kernel row (kstep ≢ 0 now violates part1); `activeState` classification + act_row/act_target; `entCount`/`init_count` (ENT-COUNT); `ιshH`/comp_once + init_count = the (COMP-h)→(COMP-hΣ) chain, (COMP-Σ) = hmc | §2.B |
| 7 | crit | Pools pinned to prime powers + δ-closure; `allActivePools` a DEFINED locus (infinitude the only burden); `PolyGeom` restores (iv)-POLY degree bounds + XHD-s geometric denominators; ι in ENT-COUNT polynomial form | §2.B/C |
| 8 | crit | `act_spec` (iff) determines Act from CTS-M(ii)'s classification; empty Act only when the note itself has no realized states (U-21c covers it via det_isEmpty) | §2.C, U-21c |
| 9 | crit | βfam/β_ok/β_interp DELETED from RS1Bundle; the interpolant is DERIVED (U-24a per-pool identification, U-24b uniqueness/fixedness) — RS.2 no longer assumed | R8, §2.D, U-24a/b |
| 10 | crit | SigSet/sig_covers DELETED; σ′ unrestricted everywhere (recursion, solve, spec); finite sums via `verdictImage`; U-24b's functional equality now follows on the full domain | R9, §2.A, U-8/17a/24b |
| 11 | crit | RS.4's σ-index := `Multiset VType` + `Sigmas` Finset; W-1 typechecks | §2.D, §2.E |
| 12 | crit | U-10's nonnegativity ROUTED (TG↔non-split, J↔split) and DERIVED from the ledger — no swapped hypotheses exist | U-10 |
| 13 | crit | U-22: `e` bound inside both hypothesis and conclusion (∀ e ∈ Icc 1 n) | U-22 |
| 14 | gap | `pools_closed` (q₀ ↦ q₀^δ) added; U-24a's base-changed legs well-formed | §2.B, U-24a |
| 15 | gap | U-7 split into U-7a/7b/7c, one display each | §3 S0 |
| 16 | gap | U-21b takes `[Nonempty ι]`; empty case isolated in U-21c (`Matrix.det_isEmpty`) | U-21b/c |
| 17 | gap | `bTot`/`blockSolveTot` (U-16c) define U-25's aggregate; `markedVal` carrier added; W-1m pinned and typeable | U-16c, §2.B, §2.E |
| 18 | gap | ALL deferrals pinned as Props over minimal carriers (TreeIface/ReadLedger/FiberIface); convergence pinned as W-10; W-9 retired (subsumed by R7) | §2.E |
| 19 | gap | RS4Chain carries the full inherited set (LedgerIV, RS1Bundle, hns, pools_e0, CL-17(ii) presentation, POLY-form burdens) + the two pinned primewise inputs; U-28's docstring lists every tag | §2.D, U-28 |
| 20 | crit | U-29 → `consistency_n2`: covers ALL §2 structures; claim renamed to schema consistency; intended-instance inhabitation = the W-11 process gate | R11, U-29, §5 |

**Fresh-Fable audit (2 crit / 4 gap) → REV 4:**

| F-# | class | REV-4 repair | where |
|---|---|---|---|
| C1 | crit | U-24a → U-24a1 (measured value = active-subsystem solve, per pool, from recursion_meas + subsystem closure + E0 — no induction, no leg evaluation, no hok claim) + U-24a2 (symbolic read-off GIVEN AVAgree — the (ii-c)/(e3)-FENCE burden as explicit hypothesis); U-24b conditional on an infinite read-off-valid family (`hread`); RegP/AVAgree now CONSUMED; RS4Chain gains `legs_reg` (CL-1's full quantifier); new U-12b transports OK/eval along q₀ ↦ q₀^δ. U-24a CLOSES — no STUCK | R14, U-24a1/a2/b, §2.D |
| C2 | crit | `act_row` DELETED (undisplayed); part1/rep_indep/xhd_sum/xhd_no_stray/meas_card/kstep_one/hmc/init_*/comp_once GUARDED by `activeState` (the note's "realized states only"/"restricted to the ACTIVE block" scope); `act_target` kept (the displayed entry-INTO-inactive vanishing); wild pools instantiable; U-9a/9b/10 carry the guard | R13, §2.B, U-9a/9b/10 |
| G1 | gap | `kstep_one`'s target predicate pinned hK-free: `∃ μ ∈ mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β` | §2.B |
| G2 | gap | W-1's rfl-conjunct STRUCK; W1_RS1SH = the measured density clause only, symbolic half noted definitional; binders unshadowed; `∃ hok` type-ascribed | §2.E |
| G3 | gap | U-16a split → U-16a1 (bSplit with the PINNED def-equation incl. the halted-member factor-1/verdict-singleton indicator, §T.4 cited) / U-16a2 (evalRe) / U-16a3 (consumedDeltas + the δ-ABSOLUTE fence) | §3 S2 |
| G4 | gap | `entLvl`/`entInst` carriers + `ent_count_card`: I^ent = the card of the ε-instance event at the shape's own defining level | §2.B |

STATUS: REV 4 complete, 2026-07-27. Round-2 (Codex) 20/20 repaired; round-3 (Fable)
6/6 repaired, nothing pushed back, no STUCK report — U-24a1/a2 close from the note's
displays once the per-pool guards are hypotheses (R14). 45 units, 18 easy / 27 medium
/ 0 hard. Awaits the parallel dual confirmation.
