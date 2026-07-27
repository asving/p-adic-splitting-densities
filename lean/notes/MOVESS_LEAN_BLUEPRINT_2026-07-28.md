# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS, 2026-07-28)

*Blueprint-architect deliverable for the campaign (`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`,
wave 1). Source of truth: the DUAL-ACCEPTED **§S-RESUM rev 6** of `lean/notes/MOVES_2026-07-24.md`
(lines ~11557–12430; acceptance record "§S-RESUM: DUAL-ACCEPTED (2026-07-27 — Codex pass 7 + the
Fable confirm, both CLEAN on identical rev-6 text)"). Written Protocol-L (agent-facing): verbatim
names, statements re-bound at use, explicit claim DAG. Discipline (parent CLAUDE.md): NO new
axioms; statement-fence holds; every interface structure is a trust boundary flagged for the
semantic audit (§4).*

## H. HEADER — the hypothesis-structure design (read first)

§S-RESUM CONSUMES the wave-4 corpora MovesV (§V-TABLES: the CTS cell space, the count tables
T/G, ι_e, the (iv) ledger) and MovesT (§T-ASSEMBLY: TREE-EXP, TREE-N, ONE-F, (SIB), VP, TB-CAP).
Those corpora do not exist yet. **Design ruling: every consumed MovesV/MovesT object enters
MovesS as a HYPOTHESIS STRUCTURE** — a section-variable bundle with named Prop/data fields —
so MovesS is self-contained NOW and instantiable at wave 4 by substituting the real objects:

- **`TableFamily`** — the table family T over ℚ(q): block states, the per-state outcome roster
  with individuated members ([3t] SIBLING INDEXING), the resummed masses T·G ∈ ℚ(q) ((iv)'s
  licit product), the cell-level branching masses J_{τ,o} ∈ ℚ(q) ((J-RAT)'s object), the
  entrance vectors ι_e (CTS-M(iii)/ENT-AGG/INIT-RAT). Owner: MovesV.
- **`LedgerIV`** — the NINE-input CL-5 conditionality ledger + PART-1's routed partition
  identity, as named Prop fields (opaque at wave 2). Owners: [1v]/[2b].
- **`RS1Bundle` / `RS4TagChain`** — the tree-assembly interface: the measured fixpoint
  (R_e-lump), the shallow expansion per (CUT-WD), the marked pairing, X.3's primewise total.
  Owners: MovesT/[5]/[2r]. Discharged at wave 4; NEVER proved here.

**XRB is baked in BY TYPE** (honesty flag, audit §4): the unknowns β_{e,τ}(σ′) are modeled with
NO h_ent index — exactly the S.0 typing ("HEIGHT-FREE (no h_ent index — exactly XRB, proved at
S.1)"). S.1's proof ((β-1)/(β-2)) is measure-side mathematics over [2b]/[3t] objects and is NOT
a MovesS unit; its conclusion is the model's type discipline, and its hypothesis set rides the
`RS1Bundle` fields. The same for S.2's (CUT-WD) and the S.7 gate (census-side, not Lean).

What IS proved in MovesS (the note's own DERIVED layer): the (m,c) dispatch and its routing
lemma; (K-TRI); the (SCS) derivation chain; (K-SUB)'s regrouping; the block-indexed linear
system over ℚ(q) and its adjugate/Cramer solve (RS.2's engine); the E0 ⟹ det ≠ 0 and Neumann
consequences (E0 itself a named hypothesis — the note's OPEN KERNEL CL-1); the evaluation
machinery and the infinitely-many-evaluations lemma; RS.1's assembly and RS.4's checksum as
CONDITIONAL theorems over the bundles.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block size e ≤ n, the linear system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q), unknowns the entrance-free conditional subtree values β_{e,τ}(σ′); the (m,c)
CLASSIFICATION routes every roster outcome to exactly one of {K_e column, terminal exit,
split exit}; (K-TRI) makes the block family triangular in e (b_e^split consumes strictly
smaller blocks only), (K-SUB) makes K_e's rows sub-stochastic given the (iv) ledger; the solve
is β_e = adj(I−K_e)b_e/det(I−K_e) (RS.2, fixed coefficients in ℚ(q)); solvability rides the
open kernel ESCAPE(E0) per pool q₀ = p^δ (RS.3); RS.1 ties the solve to the density components
R_σ in three clauses (DEEP/SH/MARKED); RS.4 is the checksum Σ_σ R_σ = 1, via "a rational
function equal to 1 at infinitely many prime evaluations is identically 1".

---

## 1. Design decisions (the concrete Mathlib model), with justification

**D1 — ℚ(q) := `RatFunc ℚ`** (`abbrev Qq := RatFunc ℚ`). Field structure: `RatFunc.instField`
(pinned mathlib, `Mathlib/FieldTheory/RatFunc/Basic.lean:480`). So `Matrix τ τ Qq` lives over a
field and the whole `Matrix.det` / `Matrix.adjugate` / nonsingular-inverse API applies verbatim.

**D2 — the block system is ONE matrix per (e), ONE vector per (e, σ′).** K_e's entries do not
depend on σ′ (S.0: K_e is state-to-state; σ′ rides only the exit vectors), so the unknown for
fixed σ′ is `β : State e → Qq` and the system is `β = K.mulVec β + b σ′`. This puts the solve
directly on Mathlib's `Matrix.mulVec` / `Matrix.cramer` API with zero re-plumbing.

**D3 — the solve API (all names verified in the pinned mathlib).**
`Matrix.isUnit_iff_isUnit_det` (NonsingularInverse.lean:127) converts `det(1−K) ≠ 0` (a field,
so `IsUnit ↔ ≠ 0` via `isUnit_iff_ne_zero`) to invertibility; `Matrix.mul_nonsing_inv` (:211) /
`Matrix.nonsing_inv_mul` (:217) give the two-sided inverse; `Matrix.inv_def` (:172) is
`A⁻¹ = A.det⁻¹ʳ • A.adjugate`; `Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245),
`Matrix.mul_adjugate` (:264), `Matrix.adjugate_mul` (:269), and
`Matrix.det_smul_inv_mulVec_eq_cramer` (NonsingularInverse.lean:656) give RS.2's displayed
entrywise form `β = adj(I−K_e) b_e / det(I−K_e)` with no bespoke linear algebra.

**D4 — evaluation at a pool q₀ is PARTIAL, exactly as the note demands.** `RatFunc.eval`
(AsPolynomial.lean:146) is `eval₂ f a num / eval₂ f a denom` and is additive/multiplicative
ONLY where denominators do not vanish (`RatFunc.eval_add`/`eval_mul` carry those hypotheses) —
which is precisely S.4's per-pool discipline ("symbolic det ≠ 0 prevents no zero or uncancelled
pole at an individual q₀ = p^δ"). We package the good locus as the subring `OKat q₀` (denom
nonvanishing at q₀) with a genuine `RingHom` `evalAt q₀ : OKat q₀ →+* ℚ`; matrix determinants
then commute with evaluation via `RingHom.mapMatrix`/`Matrix.det` naturality (`RingHom.map_det`).

**D5 — the infinitude arguments run through `Polynomial.eq_zero_of_infinite_isRoot`**
(Roots.lean:145): a RatFunc vanishing at infinitely many OK points has a numerator with
infinitely many roots, hence is 0. One reusable unit (`ratfunc_eval_infinite`) serves BOTH
RS.3(ii)'s symbolic det ≠ 0 (contrapositive, one witness pool suffices) and RS.4's checksum.

**D6 — base change q ↦ q^δ is a ring hom `powSubst δ : Qq →+* Qq`**, built by
`IsFractionRing.lift` over `Polynomial.aeval (X^δ : ℚ[X])` (nonzero polynomials map to nonzero,
hence to units of the fraction field). [2r]'s BASE-INDEX CONVENTION (δ ABSOLUTE) is a docstring
duty on the field `Member.δ`, not re-derived.

**D7 — verdict-type multisets are literal `Multiset VType`**, with [2a]'s finiteness entering
as a Finset field `SigSet` (the σ′ actually occurring) — never a global Fintype on multisets.
The split convolution's decomposition index `{g : Fin m → Multiset V // ∑ j, g j = σ′}` gets a
constructed `Fintype` instance (unit `decompFintype`); the τ-halted members contribute factor 1
with σ_j their verdict singleton, per §T.4's leaf convention cited at S.0's b_e^split display.

**D8 — the μ̂-type fence is a TYPE.** The marked total ι_e^T(I−K_e)^{−1}b_e is wrapped in a
one-field structure `MuHat` so it CANNOT be summed into a density silently — the note's
RS.1-MARKED fence ("NEVER summed into R_σ"; "equating any μ̂ object with an f-event mass
outside [3t]'s displayed conversion is a TYPE ERROR") enforced by the elaborator.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesS/Defs.lean` (inline, part 1: states/outcomes/dispatch)

Section binder throughout: `variable {n : ℕ}` (the degree; block sizes e ∈ 1..n ride as plain
`ℕ` arguments with hypotheses where needed — states of out-of-range e are empty at wave 4).

```lean
import Mathlib

namespace LeanUrat.MovesS
open Matrix Polynomial

/-- ℚ(q). Field: `RatFunc.instField`. The variable is the note's q. -/
abbrev Qq := RatFunc ℚ

/-- One INDIVIDUATED member of an outcome ([3t] SIBLING INDEXING — member-indexed,
    no order, no symmetry factor). `δ` is the ABSOLUTE base-change index ([2r] (e2)).
    `status`: halted with a verdict type, or continuing into a block-`size` state. -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ
  status : V ⊕ State size

def Member.continuing {V State} (μ : Member V State) : Prop := μ.status.isRight = true

/-- An outcome o at a block-e state: its member list. m := total members, c := continuing. -/
structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length

/-- The (m, c) CLASSIFICATION's three routes (S.0, rev 6 — a DISPLAYED DEFINITION the
    note ADOPTS; the roster supplies the two axes, never the routing itself). -/
inductive Route | kcol | termFin | split
  deriving DecidableEq

/-- The dispatch: (c = 0, any m) → termFin; (c = 1, m = 1) → kcol; (c ≥ 1, m ≥ 2) → split. -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- The verdict multiset v(o) of an ALL-HALTED outcome's members (σ′ = v(o), the FULL
    multiset — multi-member values licit: m_H3 (1,1)³, m_H12 "[1,1]+[1,2]"). -/
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

/-- HYPOTHESIS STRUCTURE (owner MovesV = §V-TABLES; wave-4 discharge): the table family
    T over ℚ(q) — block states, per-state outcome rosters, resummed masses. -/
structure TableFamily (n : ℕ) where
  State  : ℕ → Type            -- block-e states τ (the [1v] CTS-S cells at cluster size e)
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type                 -- verdict types
  deqV   : DecidableEq VType
  SigSet : Finset (Multiset VType)  -- the σ′ occurring (finite by [2a] M1/M5 — HYPOTHESIS)
  Out    : ∀ e, State e → Type  -- the outcome roster at (e, τ)
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
  TG     : ∀ e τ, Out e τ → Qq  -- the one-step resummed mass T·G ((iv): T_{m,o}·G, NO
                                --   source-mass division; licit product per (U-A)+(XHD-u))
  J      : ∀ e τ, Out e τ → Qq  -- the CELL-LEVEL resummed branching mass J_{τ,o}
                                --   ((J-RAT)'s object — NEVER the marked per-branch T·G)
  ι      : ∀ e, State e → Qq    -- CTS-M(iii) ENT-AGG entrance vector (INIT-RAT: cited burden)
  kcolSameSize : ∀ e τ (o : Out e τ), routeOf (odata e τ o) = .kcol →
    ∀ μ ∈ (odata e τ o).mem, μ.size = e
    -- (SCS)'s payload as a FIELD, so `Kmat` typechecks; unit `MovesS.scs` DISCHARGES it
    -- from the deeper SP.1/stage-law fields (SCSData below) — instantiators supply those.

attribute [instance] TableFamily.fin TableFamily.deq TableFamily.deqV TableFamily.finO
```

**The kernel, exit vectors, and the solve target** (Defs part 2 — the (m,c)-routed objects):

```lean
variable {n : ℕ} (T : TableFamily n)

/-- K_e: entries = Σ over (c=1, m=1)-routed outcomes whose continuing member lands in β
    of T·G. Entrance-height-FREE by construction (D8/XRB typing). -/
def Kmat (e : ℕ) : Matrix (T.State e) (T.State e) Qq :=
  fun τ β => ∑ o ∈ {o : T.Out e τ | routeOf (T.odata e τ o) = .kcol ∧
                    kTarget T e τ o = some β}.toFinset, T.TG e τ o
  -- `kTarget` reads the unique continuing member's state, cast along `kcolSameSize`.

/-- b_e^{term,fin}(τ)(σ′): Σ over (c=0)-routed outcomes with v(o) = σ′ of T·G. -/
def bTerm (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq :=
  fun τ => ∑ o ∈ {o | routeOf (T.odata e τ o) = .termFin ∧
                  (T.odata e τ o).verdicts = σ'}.toFinset, T.TG e τ o

/-- b_e^split(τ)(σ′) GIVEN the family of already-solved smaller blocks `βlt`:
    Σ over (c≥1, m≥2)-routed o of J_{τ,o} · Σ_{σ′ = ⊎ σ_j} ∏_j leg(σ_j) — halted members
    factor 1 on σ_j = {verdict} (§T.4 leaf convention, cited); continuing members
    (powSubst μ.δ) (βlt μ.size ⋯ σ_j), sizes < e by (K-TRI). -/
def bSplit (e : ℕ) (βlt : ∀ e' < e, T.State e' → Multiset T.VType → Qq)
    (σ' : Multiset T.VType) : T.State e → Qq := sorry -- skeleton: unit `bSplit_def` elaborates
```

**Defs part 3 — the hypothesis bundles** (each a trust boundary, audit §4):

```lean
/-- DEG-CONS (CL-11, owner [1v]; "per member, from M1's degree identity; the check runs
    over the FULL roster" — halted members INCLUDED): each e_j ≥ 1 and Σ_j e_j ≤ e. -/
structure DegCons (T : TableFamily n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e τ (o : T.Out e τ), ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-- (SCS)'s SUPPLY (owners [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via [2a] SP.2 (B1)/(B3)):
    per (c=1,m=1) outcome, the letter data W, D, ℓ, g, μ, W', D' with the cited laws.
    Fields are the DISPLAYED cites, one each. -/
structure SCSData (T : TableFamily n) where
  W D ℓ g μ W' D' : ∀ e τ (o : T.Out e τ), ℕ           -- per-outcome letter data
  flank_empty : ∀ {e τ o}, (T.odata e τ o).m = 1 → W T e τ o = e * ℓ T e τ o
    -- SP.1: every flank side / non-selected residual factor is a member; m = 1 forces
    -- the read side to span the window (unit `scs_flank` DERIVES this from the finer
    -- member-injection fields if MovesSp lands first; at wave 2 it is the field).
  lam_singleton : ∀ {e τ o}, (T.odata e τ o).m = 1 → g T e τ o * μ T e τ o = ℓ T e τ o
  stage_D : ∀ e τ o, D' T e τ o = e * g T e τ o * D T e τ o    -- (B1): D′ = e·g·D
  stage_W : ∀ e τ o, W' T e τ o = μ T e τ o                     -- (B3): W′ = μ
  cluster_parent : ∀ e τ o, W T e τ o * D T e τ o = e           -- cluster size IS W·D
  cluster_child  : ∀ {e τ o} (h : routeOf (T.odata e τ o) = .kcol),
    ∀ μm ∈ (T.odata e τ o).mem, μm.size = W' T e τ o * D' T e τ o

/-- The NINE-input CL-5 ledger + PART-1's routed partition identity (owners [1v]/[2b];
    items opaque at wave 2 — named so tags are CITABLE, never silently dropped). -/
structure LedgerIV (T : TableFamily n) : Prop where
  xhd : True      -- (1) XHD = M4a-X exact height domains/weights/sums   [placeholder Props:
  d4r0 : True     -- (2) D4R.0 disjointness after height grouping        wave-4 retargeting
  part_meas : True -- (3)(5) (iv)-PART measurability                      replaces each True
  rep : True      -- (4) (iv)-REP = M2(ii); probe STATE-probe-2           by the real
  hmc : True      -- (6) CTS-M(v) HMC (OPEN kernel)                       statement]
  act : True      -- (7) CTS-M(ii) ACT
  init : True     -- (8) CTS-M(iii) INIT + ENT-COUNT
  comp : True     -- (9) (COMP-h)→(COMP-Σ) heights-once typing
  part1 : ∀ e τ, (∑ o : T.Out e τ, oneStepMass T e τ o) = 1
    -- PART-1 in its ROUTED form: oneStepMass := TG on kcol/termFin, J on split —
    -- "the digit-cell partition identity, per representative, countable across heights"

/-- ESCAPE(E0) (OPEN KERNEL, CL-1, owner THIS note; PER-POOL q₀ = p^δ, rev-3 widening):
    the evaluated active matrix escapes. A named HYPOTHESIS, never proved in MovesS. -/
structure EscapeE0 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) Filter.atTop (nhds 0)

/-- The per-pool package (S.4): the active-state set at q₀, entry evaluability into it,
    vanishing into inactive cells, the recorded junk determinants, active-value agreement
    (CTS-M(ii-c), weakened REV-7 form) — all FIELDS. (REG-p) for MovesU := this bundle
    at every relevant pool q₀ = p^δ of the prime p. -/
structure PoolHyp (T : TableFamily n) (e : ℕ) (q₀ : ℚ) where
  Act : Finset (T.State e)                          -- sealed active list
  evalOK : ∀ τ β, τ ∈ Act → β ∈ Act → (Kmat T e τ β).denom.eval q₀ ≠ 0
  A : Matrix Act Act ℚ                              -- the evaluated active submatrix
  A_eval : ∀ τ β, A τ β = RatFunc.eval (RingHom.id ℚ) q₀ (Kmat T e τ.1 β.1)
  inactive_vanish : ∀ τ β, τ ∈ Act → β ∉ Act →
    RatFunc.eval (RingHom.id ℚ) q₀ (Kmat T e τ β) = 0
  e0 : EscapeE0 A                                   -- the open kernel rides HERE
  active_value_agreement : True                     -- (ii-c) per pool; wave-4 statement

def RegP (T : TableFamily n) (p : ℕ) (Δ : Finset ℕ) : Prop :=
  ∀ e ≤ n, ∀ δ ∈ Δ, Nonempty (PoolHyp T e ((p : ℚ) ^ δ))

/-- μ̂-TYPE FENCE (D8): the marked-entrance total, wrapped so it can never be summed
    into a density. RS.1-MARKED's object; consumed by (COMP-AGG)/gates ONLY. -/
structure MuHat where val : Qq

/-- (BDY) BOUNDARY CONVENTION (S.0, pinned ONCE, EDGE-BASED): reads of an entered path
    split as `entrance` (up to AND INCLUDING the entering read) vs `block` (from the
    first in-block read). Abstract model: a path with a first-entrance edge index. -/
inductive ReadOwner | entrance | block
def bdyOwner (firstEntrance : ℕ) (readIdx : ℕ) : ReadOwner :=
  if readIdx ≤ firstEntrance then .entrance else .block
```

**Defs part 4 — the RS.1/RS.4 tree-assembly interfaces** (owners MovesT/[5]/[2r]; wave 4):

```lean
/-- RS.1's hypothesis bundle (S.2's displayed GIVEN-list, one field per named input).
    `SplitTy`/`Shape` abstract the σ and Ŝ index types; finiteness = [2a] fields. -/
structure RS1Bundle (T : TableFamily n) where
  SplitTy : Type; finS : Fintype SplitTy            -- splitting types σ
  Shape : Type;  finSh : Fintype Shape              -- shallow tree shapes Ŝ (CUT-3's image)
  R : SplitTy → Qq                                  -- the density components (the TARGET)
  Wsh : Shape → Qq                                  -- W_Ŝ (CL-17(ii): production OPEN, cited)
  shapeData : Shape → List (Σ e, T.State e) × Multiset T.VType × List ℕ
       -- (block entrances (e_i, τ_i); σ₀(Ŝ); the δ_i legs)
  -- named [3t]/[2r]/CL tags (opaque at wave 2, citable):
  treeExp : True   -- [3t] TREE-EXP fin/ns + TREE-N + ONE-F
  sib : True       -- (SIB)/(SIB-STEP) + (JC-multi), CL-10 OPEN
  tbcapVp : True   -- TB-CAP / VP per their [3t] statuses
  rel2 : True      -- [2r] REL.2 (a)–(e) at every base-changed leg, CL-8 OPEN
  xrbSet : True    -- XRB's displayed hypothesis set (XHD + (JC-INV) + …), CL-9
  nineInputs : LedgerIV T                           -- CL-5 rides RS.1 wholesale
  -- the MEASURED clauses, as the wave-4-dischargeable interface fields:
  recursion : ∀ e ≤ n, ∀ σ' ∈ T.SigSet, ∀ hβ,      -- (R_e-lump): the solve family is
    βfam e σ' = (Kmat T e) *ᵥ βfam e σ' + bTerm T e σ' + bSplit T e hβ σ'
  shallow_expansion : ∀ σ,                          -- (CUT-WD)-regrouped tree expansion:
    R σ = ∑ Ŝ, Wsh Ŝ * shConv T Ŝ σ                 -- shConv := the S.2 convolution DEF
  marked_pairing : ∀ e ≤ n,                         -- RS.1-MARKED's supply
    markedTotal e = MuHat.mk (T.ι e ⬝ᵥ solveVec T e)

/-- RS.4's FULL tag chain (S.5: "RS.4 inherits EVERY condition of the block solve"),
    a hypothesis STRUCTURE — the checksum theorem consumes it whole. -/
structure RS4TagChain (T : TableFamily n) where
  bundle : RS1Bundle T                              -- RS.1's set + CL-5 (via nineInputs)
  e0 : ∀ e ≤ n, ∀ q₀ ∈ relevantPools, Nonempty (PoolHyp T e q₀)   -- ESCAPE(E0), CL-1
  x3 : True                                         -- X.3 (CL-4, [5]) — total-mass identity
  ivPoly : True                                     -- CTS-M(iv)-POLY (CL-6)
  xhdS : True                                       -- XHD-s
  initRat : True                                    -- INIT-RAT ([1v] burden)
  wshRat : True                                     -- CL-17(ii)'s rational W_Ŝ
  jRat : True                                       -- (J-RAT) ([1v]/[2b], rev 2)
  primewise : { S : Set ℚ // S.Infinite ∧ ∀ q₀ ∈ S,
    (∑ σ, bundle.R σ).denom.eval q₀ ≠ 0 ∧
    RatFunc.eval (RingHom.id ℚ) q₀ (∑ σ, bundle.R σ) = 1 }
    -- X.3's primewise decided-mass total = 1, evaluated: the wave-4 discharge point
```

*(Skeleton licenses: `kTarget`, `oneStepMass`, `shConv`, `solveVec`, `markedTotal`,
`relevantPools`, `βfam` are Defs-level definitions elaborated by their owning units below;
`True` placeholders are RETARGETED at wave 4 — each is a named field so no consumer can
compile without citing it, the tag-chain discipline in Lean form.)*

---

## 3. The unit DAG — 4 layers, 28 units (10 easy / 15 medium / 3 hard)

Format per campaign §2. Each unit = one file `lean/LeanUrat/MovesS/<Id>.lean` importing
`MovesS.Defs` + deps. `moves_ref` quotes the rev-6 display (≤ 3 lines).

### Layer S0 — dispatch, arithmetic core, conventions [7 units]

**U1 · `MovesS.dispatch_spec` · Dispatch.lean · easy**
`statement`: `theorem dispatch_spec (o : Outcome V State) (h1 : 1 ≤ o.m) (hc : o.c ≤ o.m) :`
`(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧`
`(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)`
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION: the three predicates partition
{(m, c) : m ≥ 1, 0 ≤ c ≤ m} (c ≥ 1 with m = 1 forces c = 1)."
deps: Defs · hypothesis_fields: none · sketch: unfold `routeOf`; `omega` per branch
(c ≥ 1 ∧ m = 1 ⟹ c = 1 since c ≤ m). Both directions of each iff by `split_ifs`.

**U2 · `MovesS.ktri` · KTri.lean · easy**
`statement`: `theorem ktri (T) (hdc : DegCons T) {e τ o} (hm : 2 ≤ (T.odata e τ o).m) :`
`∀ μ ∈ (T.odata e τ o).mem, μ.size < e`
moves_ref: "each member e_j ≥ 1, Σ_j e_j ≤ e; hence at m ≥ 2 EVERY e_j < e (two same-size
children would need 2e > e; a same-size child with any sibling needs e + 1 > e)."
deps: Defs · hypothesis_fields: DegCons (CL-11, [1v]) · sketch: μ.size + (m−1)·1 ≤ Σ sizes
≤ e via `List.sum` bound over the other members (each ≥ 1 by `size_pos`); `omega`.

**U3 · `MovesS.kcol_agree` · KColAgree.lean · easy**
`statement`: `theorem kcol_agree (T) (hdc : DegCons T) {e τ o} (he : 1 ≤ e)`
`(hmem : ∃ μ ∈ (T.odata e τ o).mem, μ.continuing ∧ μ.size = e) : (T.odata e τ o).m = 1`
moves_ref: "the degree law … gives m ≥ 2 ⟹ every e_j ≤ e − 1 < e ⟹ no member is a block-e
state ⟹ o is NO K_e column. So [1v]'s columns sit inside the (c = 1, m = 1) bucket"
deps: U2 · hypothesis_fields: DegCons · sketch: contrapose: m ≥ 2 + U2 gives size < e,
contradicting size = e. (Agreement check (ii) — the pass-6 missing premise, now derived.)

**U4 · `MovesS.scs_flank` · ScsFlank.lean · medium**
`statement`: `theorem scs_flank (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μ e τ o = S.ℓ e τ o`
moves_ref: "(1) m = 1 LEAVES NO ROOM TO SHRINK … m = 1 forces NO flank side (the read side
spans the window: e·ℓ = W) and a SINGLETON residual shape λ = {(g, μ)}, i.e. g·μ = ℓ."
deps: Defs · hypothesis_fields: SCSData.flank_empty/lam_singleton ([2a] SP.1's letter-field
typing — flank sides and non-selected residual factors ARE members) · sketch: at wave 2 the
two conclusions ARE the fields fired at hm; if MovesSp lands first, restate the fields as
member-injections (each flank side ↪ mem, each residual factor ↪ mem) and derive by counting
(m = 1 leaves no room). FLAG: field-vs-derivation status recorded for the audit.

**U5 · `MovesS.scs_stage` · ScsStage.lean · easy**
`statement`: `theorem scs_stage (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.W' e τ o * S.D' e τ o = S.W e τ o * S.D e τ o`
moves_ref: "W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D equals the parent's — and cluster
size IS the stage product W·D"
deps: U4 · hypothesis_fields: SCSData.stage_D/stage_W (§B2-DEF D.5 "deg Φ̂ = e·g·deg Φ",
D.8/D.10 "the child window is [0, μ]") · sketch: rewrite stage_W, stage_D; U4 gives
g·μ = ℓ and W = e·ℓ; `ring_nf` + substitute: μ·(e·g·D) = (g·μ)·e·D = ℓ·e·D = W·D.

**U6 · `MovesS.scs` · Scs.lean · medium**
`statement`: `theorem scs (T) (S : SCSData T) (hdc : DegCons T) {e τ o}`
`(hk : routeOf (T.odata e τ o) = .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e`
moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child inherits the block size: e₁ = e —
a size-dropping child never comes alone."
deps: U1, U4, U5 · hypothesis_fields: SCSData.cluster_parent/cluster_child (the [1v] CTS-S
datum "cells at cluster size e") · sketch: hk + U1 gives m = 1; cluster_child: size =
W′·D′; U5: = W·D; cluster_parent: = e. DISCHARGES `TableFamily.kcolSameSize` — instantiators
supply SCSData + DegCons instead of the raw field. (The SP-DAG "e = g = 1, μ < W" edge is a
species edge through a (c ≥ 1, m ≥ 2) outcome — fenced by hk, no unit needed.)

**U7 · `MovesS.bdy_partition` · Bdy.lean · medium**
`statement`: `theorem bdy_partition (fe : ℕ) : ∀ r : ℕ, (bdyOwner fe r = .entrance ↔`
`r ≤ fe) ∧ (bdyOwner fe r = .block ↔ fe < r)` — plus
`theorem bdy_no_double (fe r) : ¬(bdyOwner fe r = .entrance ∧ bdyOwner fe r = .block)`
moves_ref: "(BDY) … the ENTERING READ of a block entrance belongs to the ENTRANCE SIDE …
Node shadow: the first entrance node ν is BLOCK-side as a STATE INDEX, while the edge INTO
ν is entrance-side MASS — no read omitted, none double-charged."
deps: Defs · hypothesis_fields: none · sketch: unfold; `split_ifs` + `omega`. The point is
the PINNED DEFINITION (edge-based, entrance-inclusive) consumed by β's conditioning and by
(CUT-WD) at wave 4 — the lemma certifies exhaustive/exclusive read ownership.

### Layer S1 — (K-SUB) sub-stochasticity [3 units]

**U8 · `MovesS.ksub_regroup` · KSubRegroup.lean · medium**
`statement`: `theorem ksub_regroup (T) (e τ) : (∑ o : T.Out e τ, oneStepMass T e τ o) =`
`(∑ β, Kmat T e τ β) + (∑ σ' ∈ T.SigSet, bTerm T e σ' τ) + (∑ o ∈ splitOuts T e τ, T.J e τ o)`
moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell one-step
mass, per cell once) = 1, the third summand being exactly Σ_o J_{τ,o}"
deps: U1 · hypothesis_fields: TableFamily.SigSet covers all occurring v(o) (an
instantiation duty — add field `sig_covers`); kcolSameSize (via Kmat) · sketch: partition
the roster Finset by `routeOf` (U1: exhaustive/exclusive); `Finset.sum_fiberwise_of_maps_to`
regroups kcol terms by target β and termFin terms by verdict multiset; split terms are J by
`oneStepMass` defn. Pure finite regrouping — no measure content.

**U9 · `MovesS.ksub` · KSub.lean · easy**
`statement`: `theorem ksub (T) (L : LedgerIV T) (e τ) : (∑ β, Kmat T e τ β) +`
`(∑ σ' ∈ T.SigSet, bTerm T e σ' τ) + (∑ o ∈ splitOuts T e τ, T.J e τ o) = 1`
moves_ref: "PART-1 (the digit-cell partition identity, per representative, countable across
heights — [1v] V.3(iv)'s route) gives (K-SUB) …"
deps: U8 · hypothesis_fields: LedgerIV.part1 ((iv)-PART-1 + XHD-s, owner [1v] — the routed
form; the NINE CL-5 tags ride the structure) · sketch: U8 ▸ L.part1. CONDITIONALITY note in
docstring: GIVEN the (iv) ledger + DEG-CONS + the (m,c) classification with (SCS) — exactly
the note's rev-6 bracket. PART-2's marked-row surplus is NEVER consumed (no field exists).

**U10 · `MovesS.ksub_pool` · KSubPool.lean · medium**
`statement`: `theorem ksub_pool (T) (L : LedgerIV T) (e τ) (P : PoolHyp T e q₀)`
`(hTG : ∀ o, 0 ≤ evalAt q₀ (T.TG e τ o)) (hJ : ∀ o, 0 ≤ evalAt q₀ (T.J e τ o)) :`
`(∀ β, 0 ≤ P.A ⟨τ,_⟩ ⟨β,_⟩) ∧ (∑ β, P.A ⟨τ,_⟩ ⟨β,_⟩) ≤ 1`
moves_ref: "K_e's rows are genuine sub-distributions with exits typed terminal/split …
every summand ≥ 0 (the ns-bound tail rides INSIDE the K_e term)"
deps: U9, U19 (evalAt) · hypothesis_fields: per-pool nonneg of the evaluated T·G/J masses
(a MovesV evaluation duty) · sketch: evaluate U9 at q₀ via evalAt (a RingHom on OKat);
drop the two nonnegative exit summands; row sum ≤ 1.

### Layer S2 — the block-indexed linear system over ℚ(q) and its solve [8 units]

**U11 · `MovesS.decompFintype` · Decomp.lean · medium**
`statement`: `instance decompFintype (V) [DecidableEq V] (m : ℕ) (σ' : Multiset V) :`
`Fintype { g : Fin m → Multiset V // ∑ j, g j = σ' }`
moves_ref: "Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m … — the MULTISET CONVOLUTION over children's
types"
deps: — · hypothesis_fields: none · sketch: induct on m; m = 0: subsingleton (σ' = 0);
step: a decomposition is (g 0, rest) with g 0 ≤ σ' (finitely many sub-multisets via
`Multiset.toFinset`-bounded counts / `Multiset.Powerset`) and rest decomposing σ' − g 0.
Build via `Fintype.ofSurjective` from the sigma of powerset × recursive instance.

**U12 · `MovesS.powSubst` · PowSubst.lean · medium**
`statement`: `noncomputable def powSubst (δ : ℕ) : Qq →+* Qq` with
`theorem powSubst_X (δ) : powSubst δ (RatFunc.X) = RatFunc.X ^ δ` and
`theorem powSubst_C (δ c) : powSubst δ (RatFunc.C c) = RatFunc.C c`
moves_ref: "each leg is an already-solved block's entry composed with q ↦ q^{δ_j} (which
maps ℚ(q) → ℚ(q)); the ARGUMENT convention is [2r] (e2) (δ absolute)"
deps: — · hypothesis_fields: none (δ ≥ 1 where consumed) · sketch: `IsFractionRing.lift`
(RatFunc ℚ is the fraction field of ℚ[X]) over `(Polynomial.aeval (X^δ)).toRingHom`:
nonzero polynomials map to nonzero (aeval at X^δ on a domain: leading terms can't cancel;
degree multiplies by δ — for δ = 0 restrict or accept constants), hence to units of Qq.

**U13 · `MovesS.solve_iff` · SolveIff.lean · easy**
`statement`: `theorem solve_iff (K : Matrix ι ι Qq) (b β : ι → Qq) [Fintype ι] :`
`β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b`
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split"
deps: — · hypothesis_fields: none · sketch: `sub_mulVec`, `one_mulVec`; both directions by
`funext` + abelian-group rearrangement (`sub_eq_iff_eq_add`).

**U14 · `MovesS.solve_exists_unique` · SolveEU.lean · medium**
`statement`: `theorem solve_exists_unique (K : Matrix ι ι Qq) (b : ι → Qq) [Fintype ι]`
`[DecidableEq ι] (hdet : (1 - K).det ≠ 0) : ∃! β, β = K *ᵥ β + b` — with the witness
`corollary solve_val : ((1 - K)⁻¹ *ᵥ b) = K *ᵥ ((1 - K)⁻¹ *ᵥ b) + b`
moves_ref: "THE SOLVE: GIVEN det(I − K_e) ≠ 0 in ℚ(q) (S.4), Cramer/adjugate gives …
every β_{e,τ}(σ′) is one fixed rational function."
deps: U13 · hypothesis_fields: hdet (supplied by U22 given E0) · sketch: `isUnit_iff_ne_zero`
+ `Matrix.isUnit_iff_isUnit_det` ⟹ IsUnit (1−K); existence: `Matrix.mul_nonsing_inv` +
`Matrix.mulVec_mulVec`; uniqueness: two fixpoints differ by v with (1−K) *ᵥ v = 0, kill via
`Matrix.nonsing_inv_mul` (left-multiply by the inverse).

**U15 · `MovesS.solve_cramer` · SolveCramer.lean · medium**
`statement`: `theorem solve_cramer (K b) [Fintype ι] [DecidableEq ι]`
`(hdet : (1 - K).det ≠ 0) (τ : ι) :`
`(1 - K)⁻¹ *ᵥ b = fun τ => ((1 - K).det)⁻¹ * ((1 - K).adjugate *ᵥ b) τ`
moves_ref: "Cramer/adjugate gives β_e = adj(I − K_e) b_e / det(I − K_e) entrywise —
finitely many +/×/÷ over ℚ(q)"
deps: U14 · hypothesis_fields: hdet · sketch: `Matrix.inv_def` (A⁻¹ = det⁻¹ʳ • adjugate) +
`Matrix.smul_mulVec_assoc`; or `Matrix.det_smul_inv_mulVec_eq_cramer` +
`Matrix.cramer_eq_adjugate_mulVec`. This is RS.2's DISPLAYED form — the adjugate
rationality theorem: entries are ratios of ℤ[entries]-polynomials, so fixed coefficients
⟹ fixed rational functions, p entering ONLY at evaluation q = p (docstring duty).

**U16 · `MovesS.blockSolve` · BlockSolve.lean · hard**
`statement`: `noncomputable def blockSolve (T) (hdc : DegCons T)`
`(hdet : ∀ e ≤ n, (1 - Kmat T e).det ≠ 0) : ∀ e ≤ n, T.State e → Multiset T.VType → Qq`
moves_ref: "b_e^split is multilinear in STRICTLY-SMALLER-BLOCK solutions only, (R_e) stays
LINEAR within block e … blocks solve bottom-up, each b_e^split leg already solved."
deps: U2 (ktri), U11, U12, U14 · hypothesis_fields: DegCons; per-e hdet · sketch: strong
recursion on e (`Nat.strong_induction_on`): given βlt on e' < e, form b := bTerm + bSplit
(bSplit's continuing legs have size < e by U2 — the WF certificate) and set
blockSolve e := (1 - Kmat T e)⁻¹ *ᵥ b, per σ' ∈ SigSet. The (K-TRI) triangularity IS the
recursion's legitimacy. Plumbing-heavy (dependent WF recursion + per-σ' vectors): HARD.

**U17 · `MovesS.blockSolve_spec` · BlockSolveSpec.lean · medium**
`statement`: `theorem blockSolve_spec (T hdc hdet) (e) (he : e ≤ n) (σ' ∈ T.SigSet) :`
`blockSolve T hdc hdet e he · σ' = Kmat T e *ᵥ (blockSolve … e he · σ')`
`+ bTerm T e σ' + bSplit T e (fun e' h' => blockSolve … e' …) σ'`
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split [UNCONDITIONAL — the lump
form]; (R_e-exact) β_e^full = β_e [GIVEN (ns-null) — CLOSED at [3t] §T.2]"
deps: U16, U14 · hypothesis_fields: as U16 · sketch: unfold one recursion layer; U14's
witness equation. (R_e-exact) needs NO unit: (ns-null) is CLOSED and the lump/full split is
measure-side typing — docstring records the discharged tag, per the note's display.

**U18 · `MovesS.rsh_def` · RshDef.lean · easy**
`statement`: `noncomputable def Rsh (T) (B : RS1Bundle T) (σ : B.SplitTy) : Qq :=`
`∑ Ŝ, B.Wsh Ŝ * shConv T Ŝ σ` — with `theorem rsh_mem : True` replaced by the docstring
duty: Rsh is a FINITE ℚ(q)-combination of W_Ŝ, powSubst-legs of blockSolve, and factor-1
leaves — rationality BY TYPE (RS.2's conclusion for R_σ).
moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏_{i=1}^{k(Ŝ)}
β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})"
deps: U11, U12, U16 · hypothesis_fields: RS1Bundle.finSh ([2a] finiteness of
height-forgotten shapes); Wsh's production = CL-17(ii) OPEN (cited, never proved) ·
sketch: definition + `Fintype` sums; the convolution via U11's instance; σ₀(Ŝ) offsets the
multiset per shapeData. INIT-RAT/(J-RAT)/XHD-s ride as RS4TagChain cites, not proofs.

### Layer S3 — pools, evaluation, ESCAPE(E0) consequences [5 units]

**U19 · `MovesS.evalAt` · EvalAt.lean · medium**
`statement`: `def OKat (q₀ : ℚ) : Subring Qq` (elements with `denom.eval q₀ ≠ 0`) and
`noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ` with
`theorem evalAt_coe (q₀ f) : evalAt q₀ f = RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq)`
moves_ref: "EVALUATION IS PER POOL (rev 3): symbolic det ≠ 0 prevents no zero or
uncancelled pole at an individual q₀ = p^δ."
deps: — · hypothesis_fields: none · sketch: closure of the denom-nonvanishing locus under
+/× via `RatFunc.denom_add_dvd`-style divisibility (denom(x∘y) ∣ denom x · denom y; a
divisor of a q₀-nonvanishing product is q₀-nonvanishing over a field); hom laws from
`RatFunc.eval_add`/`eval_mul` (their hypotheses are exactly membership). Mathlib-search
duty: check for an existing localization `Polynomial.Localization`/valuation-subring route.

**U20 · `MovesS.eval_det` · EvalDet.lean · easy**
`statement`: `theorem eval_det (q₀) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (OKat q₀)) :`
`evalAt q₀ M.det = (M.map (evalAt q₀)).det`
moves_ref: "the sealed check that the evaluated object's q₀-value … equals the
active-subsystem solve there" (S.4 (ii), the eval/det compatibility it presupposes)
deps: U19 · hypothesis_fields: none · sketch: `RingHom.map_det` (mathlib) applied to
`evalAt q₀`; `Matrix.det` commutes with `RingHom.mapMatrix`.

**U21 · `MovesS.e0_det_ne_zero` · E0Det.lean · hard**
`statement`: `theorem e0_det_ne_zero {ι} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℚ}`
`(h : EscapeE0 A) : (1 - A).det ≠ 0`
moves_ref: "A(q₀) being a FINITE nonnegative matrix, ρ(A(q₀)) < 1, the Neumann series
converges, and (I − A(q₀))^{−1} ≥ 0" (the det ≠ 0 face; ρ-language not formalized)
deps: — · hypothesis_fields: EscapeE0 (CL-1 — the OPEN KERNEL as hypothesis; this unit is
the "hence", not the kernel) · sketch: contrapositive: det = 0 gives v ≠ 0 with
(1−A) *ᵥ v = 0 (`Matrix.exists_mulVec_eq_zero_iff`), so A *ᵥ v = v, so A^k *ᵥ v = v; bound
|v i| = |(A^k *ᵥ v) i| ≤ ‖v‖∞ · (A^k *ᵥ 1) i (nonneg entries) → 0; v = 0, contradiction.
Entrywise sup-norm estimates over ℚ — fiddly, no topology needed beyond the given Tendsto.

**U22 · `MovesS.rs3_det_symbolic` · Rs3Det.lean · medium**
`statement`: `theorem rs3_det_symbolic (T) (e) (P : PoolHyp T e q₀)`
`(hall : P.Act = Finset.univ) (hOK : ∀ τ β, (Kmat T e τ β) ∈ OKat q₀) :`
`(1 - Kmat T e).det ≠ 0`
moves_ref: "at all-active primes (cofinitely many …) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations is 0,
so det(I − K_e) ≠ 0 in ℚ(q) — the SYMBOLIC block solve is licit."
deps: U19, U20, U21 · hypothesis_fields: PoolHyp at ONE all-active pool (E0 rides inside);
all-activity + entry evaluability = MovesV instantiation duties · sketch: ONE witness
suffices for ≠ 0 (the note's "infinitely many" is the same argument with slack): if
det(1−K) = 0 in Qq then U20 evaluates det(1−A) = 0 at q₀, contradicting U21. Docstring:
per-pool solvability at OTHER pools stays conditional on ITS PoolHyp — the rev-3 widening;
no uniformity in q₀ claimed anywhere (ESCAPE-UNIF is consumed by NOTHING).

**U23 · `MovesS.e0_inv_nonneg` · E0InvNonneg.lean · hard**
`statement`: `theorem e0_inv_nonneg {A : Matrix ι ι ℚ} (h : EscapeE0 A) (i j) :`
`0 ≤ (1 - A)⁻¹ i j`
moves_ref: "the Neumann series converges, and (I − A(q₀))^{−1} ≥ 0."
deps: U21 · hypothesis_fields: EscapeE0 · sketch: algebraic Neumann: with
S_k := Σ_{m<k} A^m, (1−A) S_k = 1 − A^k, so S_k = (1−A)⁻¹(1 − A^k) and (1−A)⁻¹ =
S_k + (1−A)⁻¹ A^k; entries of S_k are ≥ 0 and (1−A)⁻¹A^k → 0 entrywise (fixed matrix times
A^k *ᵥ bounds); limit of nonnegatives. Consumer: [4]/SQ.2 only — NOT on MovesS's own
downstream path; may be deferred without blocking U24–U28.

### Layer S4 — RS.1's three clauses and RS.4's checksum [5 units]

**U24 · `MovesS.rs1_deep` · Rs1Deep.lean · medium**
`statement`: `theorem rs1_deep (T) (B : RS1Bundle T) (hdc hdet) (e) (he : e ≤ n)`
`(σ') (hσ : σ' ∈ T.SigSet) : βfam B e σ' = (1 - Kmat T e)⁻¹ *ᵥ`
`(bTerm T e σ' + bSplit T e (βlt-of βfam) σ')`
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′) — the
ENTRANCE-FREE conditional subtree value (S.0 typing) … solvability of the inverse is
RS.3's (S.4)."
deps: U13, U14, U17 · hypothesis_fields: RS1Bundle.recursion (the measured (R_e-lump)
fixpoint — [3t]/TREE-EXP territory, wave-4 discharge) + hdet (U22 given PoolHyp) · sketch:
B.recursion says βfam solves the fixpoint; U14 uniqueness identifies it with the inverse
witness. The CONSUMPTION-DAG discipline (S.1 status line) holds: nothing here cites PCI.

**U25 · `MovesS.rs1_sh` · Rs1Sh.lean · medium**
`statement`: `theorem rs1_sh (T) (B : RS1Bundle T) (σ : B.SplitTy) :`
`B.R σ = Rsh T B σ`
moves_ref: "(RS.1-SH) THE SHALLOW CONVOLUTION (the base clause): R_σ = Σ_{Ŝ} W_Ŝ(q) ·
Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏ β_{e_i,τ_i}(σ_i)(q^{δ_i})"
deps: U18 · hypothesis_fields: RS1Bundle.shallow_expansion ((CUT-WD)-regrouped TREE-EXP —
the measure-side content, wave 4; (SIB)/CL-10, REL.2/CL-8, XRB/CL-9 tags ride the bundle) ·
sketch: rewrite shallow_expansion against Rsh's definition. HONESTY FLAG (audit §4): at
wave 2 this unit is ASSEMBLY — the field is nearly the display; its VALUE is pinning the
exact convolution shape MovesT must discharge, quantifier-exact.

**U26 · `MovesS.rs1_marked` · Rs1Marked.lean · easy**
`statement`: `theorem rs1_marked (T) (B : RS1Bundle T) (e) (he : e ≤ n) :`
`(markedTotal B e).val = T.ι e ⬝ᵥ ((1 - Kmat T e)⁻¹ *ᵥ bAgg T e)` — `markedTotal : MuHat`
moves_ref: "(RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed
MARKED-entrance total (post-split marks, CTS-M(iii) POST-SPLIT) … NEVER summed into R_σ."
deps: U14 · hypothesis_fields: RS1Bundle.marked_pairing (ENT-AGG/(COMP-AGG), wave 4) ·
sketch: unfold the field. The FENCE is structural: `MuHat` has no coercion to `Qq` and no
`Add MuHat` instance — summing it into a density is a TYPE ERROR, as the note demands.
ORIENTATION duty (docstring): ι acts ONCE on the left; never inserted into K or b.

**U27 · `MovesS.ratfunc_eval_infinite` · EvalInfinite.lean · medium**
`statement`: `theorem ratfunc_eval_infinite (f : Qq) (S : Set ℚ) (hS : S.Infinite)`
`(hden : ∀ x ∈ S, f.denom.eval x ≠ 0) (hval : ∀ x ∈ S, RatFunc.eval (RingHom.id ℚ) x f = 0) :`
`f = 0`
moves_ref: "a rational function equal to 1 at infinitely many prime powers is identically 1"
(S.5; stated at 0 — apply to f − 1)
deps: — · hypothesis_fields: none · sketch: eval = num.eval x / denom.eval x; hden + hval
force `f.num.eval x = 0` on S; `Polynomial.eq_zero_of_infinite_isRoot` (S infinite ⊆ roots)
gives num = 0; `RatFunc.num_eq_zero_iff` (or num/denom reconstruction) gives f = 0.
REUSED by U22's route in its infinitely-many form and by U28 — the note's one argument.

**U28 · `MovesS.rs4` · Rs4.lean · medium**
`statement`: `theorem rs4 (T) (C : RS4TagChain T) : (∑ σ, C.bundle.R σ) = 1`
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q. ROUTE (DERIVED, GIVEN its inherited set):
at each prime p the decided-mass series totals 1 — X.3's density form … RS.1 equates that
series with Σ_σ R_σ(p); a rational function equal to 1 at infinitely many prime powers is
identically 1."
deps: U27 · hypothesis_fields: the FULL RS4TagChain — E0 per-pool (CL-1), the nine CL-5
inputs, RS.1's set (CL-10/CL-17/CL-8 + XRB's), X.3 (CL-4), and the RS.2 rationality chain
(CL-6, XHD-s, INIT-RAT, CL-17(ii), (J-RAT)) — every field CITED by the docstring tag list;
`primewise` is the wave-4 discharge point · sketch: apply U27 to (Σ_σ R σ) − 1 on
C.primewise's infinite set (denominator control from the same field; denom(f−1) = denom f).
Docstring: "may NOT be marked unconditional before those close" — the acceptance fence.

---

## 3b. The claim DAG (load-bearing edges, acyclic by layer)

`U1 → {U3(via U2), U6, U8}` · `U2 → {U3, U16}` · `U4 → U5 → U6` (the (SCS) chain:
flank-fills-window → W′D′ = WD → size inheritance) · `U6 discharges TableFamily.kcolSameSize
→ {Kmat well-typed: U8, U16, U22, U24}` · `U8 → U9 → U10` ((K-SUB) chain) ·
`U11, U12 → {U16, U18}` · `U13 → U14 → {U15, U16, U24, U26}` · `U16 → U17 → U24` ·
`U19 → {U10, U20} ; U20, U21 → U22 → (hdet of U16/U24)` · `U18 → U25` · `U27 → U28`.
No unit cites RS.1's PCI sites from inside U24's proof (the CONSUMPTION-DAG discipline);
U23 hangs off U21 with no MovesS consumer (its consumer is [4]/MovesU).

---

## 4. Honest gaps & audit flags (for the Codex semantic audit — quote-and-classify targets)

1. **The `True` placeholder fields** (LedgerIV items 1–9 except part1; RS1Bundle
   treeExp/sib/tbcapVp/rel2/xrbSet; RS4TagChain x3/ivPoly/xhdS/initRat/wshRat/jRat;
   PoolHyp.active_value_agreement). They are NAMED so tags are citable and droppable-never;
   they carry NO content at wave 2. The audit should verify each maps 1:1 onto a note tag
   and that NO conclusion of a MovesS unit needs the placeholder's content (only part1,
   recursion, shallow_expansion, marked_pairing, primewise, e0 carry load).
2. **XRB baked in by type** (header): β has no h_ent index structurally. S.1's
   PROVED-under-hypotheses status is NOT re-established in Lean at wave 2 — flag any future
   claim that MovesS "proves XRB". Its hypothesis set rides `xrbSet`.
3. **`part1` is the ROUTED form of PART-1** — the note derives the routing ((K-SUB)) and
   CITES the partition; our field fuses "PART-1 + each cell's mass is TG-or-J per its
   route". Audit check: this matches "the third summand being exactly Σ_o J_{τ,o} — the
   (J-RAT) cell-level object supplied by PART-1, never the marked offspring row", and
   PART-2's surplus row has NO field (unconsumable — the rev-1 critical stays fixed).
4. **U4 (scs_flank) is field-vs-derivation** at wave 2 (SP.1's letter fields live in
   MovesSp): the unit fires the fields; the deeper member-injection derivation is a
   recorded UPGRADE path, not a silent strengthening.
5. **U25 (rs1_sh) is assembly-thin** by design; its value is the quantifier-exact pin of
   the convolution MovesT must discharge. Same for U26.
6. **ESCAPE(E0) is a hypothesis structure, NEVER proved** (CL-1, this note's own open
   kernel). U21/U23 are its displayed "hence" consequences. ESCAPE-UNIF does not exist in
   this corpus (consumed by nothing — the note's explicit fence).
7. **(REG-p)** is defined here as the per-pool bundle over all relevant δ; MovesU consumes
   it. The relevant-pool set Δ is a parameter, not computed (the [2r] (e2) δ-roster is a
   MovesT/MovesR duty).
8. **No measure theory anywhere**: every μ̂/density-typed statement enters through bundle
   fields. `MuHat` enforces the type fence structurally (no Add, no coercion).
9. **S.7 (gate RESUM-n3), the probe roster, and (CUT-WD)'s proof** are out of corpus scope
   (census-side / wave-4 measure-side); (BDY) is in scope as the pinned definition (U7).

---

## 5. Conventions for elaboration (phase E) and the prover fleet

Build per file: `lake env lean LeanUrat/MovesS/<file>.lean` (never bare `lake build
LeanUrat`, per repo gotcha). `Defs.lean` must compile sorry-free EXCEPT the four skeleton
`sorry` defs (`kTarget`, `oneStepMass`, `shConv`, `bSplit` body, `βfam`/`markedTotal`
wiring) which the E-phase elaborates BEFORE unit fan-out; end every unit file with
`#print axioms` (Lean-core only; `sorryAx` flagged in docstrings). Statement changes to
ANY structure field = statement-fence event (designer sign-off). Mathlib names verified
against the pinned cache 2026-07-28: `Matrix.isUnit_iff_isUnit_det`,
`Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul`, `Matrix.inv_def`,
`Matrix.cramer_eq_adjugate_mulVec`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`,
`Matrix.det_smul_inv_mulVec_eq_cramer`, `Polynomial.eq_zero_of_infinite_isRoot`,
`RatFunc.instField`, `RatFunc.eval`, `RatFunc.eval_add`/`eval_mul` (hypothesis-carrying),
`IsFractionRing.lift`, `RingHom.map_det`.

**Unit census: 28 units.** Easy {U1,U2,U3,U5,U7,U9,U13,U18,U20,U26} = 10; hard
{U16 blockSolve WF-recursion, U21 e0_det_ne_zero, U23 e0_inv_nonneg} = 3; medium (the
remaining 15: U4,U6,U8,U10,U11,U12,U14,U15,U17,U19,U22,U24,U25,U27,U28). Total 28.

