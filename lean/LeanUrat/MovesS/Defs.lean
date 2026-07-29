/-
MovesS/Defs — shared vocabulary for MOVES §S-RESUM (the depth resummation core).

E-phase transcription of `lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (REV 13,
core accepted by adjudicated closure) §2.A–§2.C + the §2.D Defs-part (MuHat/ReadOwner/
Shape/ShapeFam/consumedDeltas/RegP).  Declaration order = spec.  The skeleton defs the
blueprint displays with `sorry` bodies (OKat/evalAt, kTarget, Kmat, bTerm,
consumedDeltas) are FILLED here per the E-phase discipline (Defs sorry-free); their
LAW units (U-19, U-16a3, …) stay sorried in their own files.  Nothing in this file
asserts mathematics — it fixes the vocabulary §S-RESUM's statements are typed in.
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix Polynomial

/-- D1: the symbolic carrier ℚ(q). -/
abbrev Qq := RatFunc ℚ

variable {n : ℕ}

/-! ## §2.A Combinatorial layer (owner MovesV/MovesSp rosters) -/

/-- A branch member.  `δ` is the base-change FACTOR contributed at this nesting step;
the SEMANTIC index rel. the base prime is the product along the chain (CONVENTION
DELTA-ABS, R17; [2r] (e2)); no δ = 0. -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+
  status : V ⊕ State size

def Member.continuing {V : Type*} {State : ℕ → Type*} (μ : Member V State) : Prop :=
  μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

section OutcomeDefs
variable {V : Type*} {State : ℕ → Type*}

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ :=
  (o.mem.filter (fun μ => μ.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  ((o.mem.filterMap fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split
  deriving DecidableEq

/-- The (m, c) dispatch: exhaustive and exclusive by construction. -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

end OutcomeDefs

/-- Block states + rosters.  NO SigSet (R9): σ′ ranges over all of `Multiset VType`;
finite σ′-sums use `verdictImage` below.  `vEquiv` is the R20 STRUCTURAL PIN: verdict
types ARE the (e, f) pairs of degree e·f ≤ n; `vdeg_spec` reads degree through it.
`Wloc`/`Wstate` are the note's degree-bound data, FIXED here before any burden (R27). -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  finV   : Fintype VType
  vdeg   : VType → ℕ+
  vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ n}
  vdeg_spec : ∀ v, (vdeg v : ℕ) = ((vEquiv v).1.1 : ℕ) * ((vEquiv v).1.2 : ℕ)
  Out    : ∀ e, State e → Type
  finO   : ∀ e (τ : State e), Fintype (Out e τ)
  odata  : ∀ e (τ : State e), Out e τ → Outcome VType State
  Wloc   : ∀ e (τ : State e), Out e τ → ℕ
  Wstate : ∀ e, State e → ℕ

attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finV
  TableShape.finO

open scoped Classical

/-- The finitely many verdict multisets the (e, τ) roster's terminal outcomes emit —
the index Finset of (K-SUB)'s Σ_{σ′} b^{term,fin} (replaces REV 2's SigSet). -/
noncomputable def verdictImage (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (Multiset T.VType) :=
  Finset.image (fun o => (T.odata e τ o).verdicts)
    {o : T.Out e τ | routeOf (T.odata e τ o) = .termFin}.toFinset

/-- (SCS) supply — owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via SP.2.  Data first
(R2-3); `∨ True` artifact deleted (R2-1); `flank_zero` added (R2-2); `resFactors`
a Multiset with position-indexed `memberOf` (REV 10, Codex#6-10). -/
structure SCSData (T : TableShape n) where
  W  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  ℓ  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  g  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  μsel : ∀ e (τ : T.State e), T.Out e τ → ℕ
  W' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankCount : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankWidth : ∀ e (τ : T.State e), T.Out e τ → ℕ
  resFactors : ∀ e (τ : T.State e), T.Out e τ → Multiset (ℕ × ℕ)
  selIdx : ∀ e (τ : T.State e) (o : T.Out e τ), Fin (T.odata e τ o).mem.length
  memberOf : ∀ e (τ : T.State e) (o : T.Out e τ),
    (Fin (flankCount e τ o) ⊕
      Fin ((resFactors e τ o).erase (g e τ o, μsel e τ o)).card) →
    Fin (T.odata e τ o).mem.length
  -- laws
  ℓpos : ∀ e (τ : T.State e) (o : T.Out e τ), 1 ≤ ℓ e τ o
  window_comp : ∀ e (τ : T.State e) (o : T.Out e τ),
    W e τ o = e * ℓ e τ o + flankWidth e τ o
  flank_zero : ∀ e (τ : T.State e) (o : T.Out e τ),
    flankCount e τ o = 0 → flankWidth e τ o = 0
  sel_mem : ∀ e (τ : T.State e) (o : T.Out e τ),
    (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e (τ : T.State e) (o : T.Out e τ),
    ((resFactors e τ o).map (fun x => x.1 * x.2)).sum = ℓ e τ o
  memberOf_inj : ∀ e (τ : T.State e) (o : T.Out e τ),
    Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e (τ : T.State e) (o : T.Out e τ) i,
    memberOf e τ o i ≠ selIdx e τ o
  sel_continuing : ∀ e (τ : T.State e) (o : T.Out e τ),
    routeOf (T.odata e τ o) = .kcol →
    ((T.odata e τ o).mem.get (selIdx e τ o)).continuing
  stage_D : ∀ e (τ : T.State e) (o : T.Out e τ), D' e τ o = e * g e τ o * D e τ o
  stage_W : ∀ e (τ : T.State e) (o : T.Out e τ), W' e τ o = μsel e τ o
  cluster_parent : ∀ e (τ : T.State e) (o : T.Out e τ), W e τ o * D e τ o = e
  cluster_child : ∀ e (τ : T.State e) (o : T.Out e τ)
    (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o

/-- DEG-CONS (CL-11, [1v]): full-roster per-member degree law. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e (τ : T.State e) (o : T.Out e τ),
    ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-! ## §2.B The measured side (R7 event carrier).  Owner [1v] CTS-M / [2b] XHD / [5].
Intended instance: the CTS cell space over the level-N residue boxes of the O_δ
theory (the MovesC counting idiom), wave 4. -/

structure MeasuredSide (T : TableShape n) where
  -- pools: prime powers, closed under the base-change legs (R2-7, R2-14)
  Pools : Set ℚ
  pools_prime_pow : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  -- the counting carrier (R7): level-N boxes, events as Finsets
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- cells, representatives, heights
  Cell : ∀ e, T.State e → Type
  finC : ∀ e (τ : T.State e), Fintype (Cell e τ)
  cellOut : ∀ e (τ : T.State e), Cell e τ → T.Out e τ
  Rep : ∀ e, T.State e → Type
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, Nonempty (Rep e τ)
  cellLvl : ∀ e (τ : T.State e), Cell e τ → ℕ
  cellInst : ∀ e (τ : T.State e), Cell e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  Hgt : Type
  HDom : ∀ e (τ : T.State e), Cell e τ → Set Hgt
  gwt : ∀ e (τ : T.State e) (c : Cell e τ), Hgt → ℚ → ℝ
  cellEvt : ∀ e (τ : T.State e), Rep e τ → Cell e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  μcell : ∀ e (τ : T.State e), Rep e τ → Cell e τ → ℚ → ℝ
  rowVal : ∀ e (τ : T.State e), T.Out e τ → ℚ → ℝ
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ
  activeState : ℚ → ∀ e, T.State e → Prop
  decA : ∀ q₀ e, DecidablePred (activeState q₀ e)
  -- entrance side
  EntShape : ∀ e, T.State e → Type
  finE : ∀ e (τ : T.State e), Fintype (EntShape e τ)
  hent : ∀ e (τ : T.State e), EntShape e τ → ℕ
  Went : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entEvtH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  ιDom : ∀ e (τ : T.State e), EntShape e τ → Set Hgt
  ιshH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ℚ → ℝ
  ιsh : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℝ
  ιval : ∀ e, T.State e → ℚ → ℝ
  entCount : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℕ
  entLvl : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entInst : ∀ e (τ : T.State e), EntShape e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  markedVal : ∀ _e : ℕ, ℚ → ℝ

attribute [instance] MeasuredSide.finB MeasuredSide.finC MeasuredSide.finE
  MeasuredSide.decA

variable {T : TableShape n}

/-- The DEFINED all-active locus (R2-7/R9): only its infinitude is a burden (U-22b). -/
def allActivePools (M : MeasuredSide T) : Set ℚ :=
  {q₀ ∈ M.Pools | ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, M.activeState q₀ e τ}

/-- `cells o` — the outcome's cell fiber (the blueprint's LedgerIV notation). -/
noncomputable def MeasuredSide.cells (M : MeasuredSide T) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Finset (M.Cell e τ) :=
  {c | M.cellOut e τ c = o}.toFinset

/-- CL-5, all nine inputs as contentful Props (R2-4/5/6).  ACTIVITY GUARDS THROUGHOUT
(R13): every per-(e,τ,q₀) mass claim carries `M.activeState q₀ e τ` — the note's
"realized states only" scope; NO zero-row law for inactive sources exists (act_row
DELETED — undisplayed).  The ONLY height summations in the corpus are `xhd_sum` and
`comp_once` — (COMP-Σ)'s "no further height sum" is structural. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  -- (1) XHD [2b], guarded; two-sided exactness representative-quantified (R2-4):
  xhd_sum : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
  xhd_no_stray : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ N₀, ∀ N ≥ N₀, (M.cellEvt e τ x c h q₀ N).Nonempty
  xhd_no_orphan : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∉ M.HDom e τ c → ∀ (q₀ : ℚ) (N : ℕ), M.cellEvt e τ x c h q₀ N = ∅
  -- (2) D4R.0 (event disjointness needs no realization; unguarded is harmless):
  d4r0 : ∀ e (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ) (N : ℕ)
    (c c' : M.Cell e τ) (h h' : M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (M.cellEvt e τ x c h q₀ N) (M.cellEvt e τ x c' h' q₀ N)
  -- (3) (iv)-PART-1 [1v], GUARDED:
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
  -- (4) (iv)-REP = RS.0(α) verbatim (weighted grouping), GUARDED:
  rep_indep : ∀ e (τ : T.State e) (o : T.Out e τ) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.rowVal e τ o q₀ = ∑ c ∈ M.cells e τ o, M.μcell e τ x c q₀
  -- (5) (iv)-MEAS counting-native (R7), GUARDED:
  meas_card : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.cellEvt e τ x c h q₀ N).card : ℝ)
  -- (6) CTS-M(v) HMC (OPEN) + the base tie, target predicate PINNED hK-FREE (G1):
  kstep_one : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : T.Out e τ | routeOf (T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, M.rowVal e τ o q₀
  hmc : ∀ (k : ℕ) e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep (k + 1) e τ β q₀ = ∑ γ : T.State e, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
  -- (7) CTS-M(ii) ACT — ONLY the displayed law (S.7(iv)):
  act_target : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools →
    ¬ M.activeState q₀ e β → M.kstep 1 e τ β q₀ = 0
  -- (8) CTS-M(iii) INIT + ENT-COUNT, guarded; the I^ent tie at ε's OWN level (G4):
  init_agg : ∀ e (τ : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.ιval e τ q₀ = ∑ ε : M.EntShape e τ, M.ιsh e τ ε q₀
  init_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (h : M.Hgt),
    h ∈ M.ιDom e τ ε → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.ιshH e τ ε h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.entEvtH e τ ε h q₀ N).card : ℝ)
  ent_count_card : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    (M.entInst e τ ε q₀ (M.entLvl e τ ε)).card = M.entCount e τ ε q₀
  -- (9) COMP-TYPING, heights once: (COMP-h) = init_count's fixed-height objects;
  -- (COMP-hΣ) = THE one height sum; (COMP-Σ)'s factorization is hmc's duty:
  comp_once : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)

/-! ## §2.C Evaluation, rationality burdens, kernel, pools -/

private theorem eval_ne_zero_of_dvd {p q : Polynomial ℚ} {x : ℚ} (hdvd : p ∣ q)
    (hq : q.eval x ≠ 0) : p.eval x ≠ 0 := by
  intro h0
  obtain ⟨c, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, h0, zero_mul] at hq
  exact hq rfl

/-- The evaluation-regular subring at q₀: {f | f.denom.eval q₀ ≠ 0} (U-19's object;
OKat membership is post-cancellation — RatFunc num/denom are reduced). -/
def OKat (q₀ : ℚ) : Subring Qq where
  carrier := {f : Qq | f.denom.eval q₀ ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_add_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  mul_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  neg_mem' := @fun a ha => by
    simp only [Set.mem_setOf_eq] at *
    have hdvd : (-a).denom ∣ (-1 : Qq).denom * a.denom := by
      simpa [neg_one_mul] using RatFunc.denom_mul_dvd (-1 : Qq) a
    have h1 : (-1 : Qq).denom = 1 := by
      rw [show (-1 : Qq) = algebraMap (Polynomial ℚ) Qq (-1) by simp]
      exact RatFunc.denom_algebraMap _
    exact eval_ne_zero_of_dvd hdvd (by rw [h1, one_mul]; exact ha)

theorem mem_OKat_iff {q₀ : ℚ} {f : Qq} : f ∈ OKat q₀ ↔ f.denom.eval q₀ ≠ 0 :=
  Iff.rfl

private theorem eval₂_denom_ne_zero_of_mem {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) :
    Polynomial.eval₂ (RingHom.id ℚ) q₀ f.denom ≠ 0 := by
  rw [Polynomial.eval₂_id]; exact hf

/-- D4: partial evaluation on the regular subring (RatFunc.eval_add/eval_mul are
hypothesis-carrying; the memberships supply the hypotheses). -/
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ where
  toFun f := RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq)
  map_one' := by simp
  map_mul' a b := by
    push_cast
    exact RatFunc.eval_mul (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)
  map_zero' := by simp
  map_add' a b := by
    push_cast
    exact RatFunc.eval_add (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)

/-- The (iv)-POLY/XHD-s presentation pattern — R30/R31: TWO independently bounded
count polynomials × a height part in the note's OWN denominator class (q-powers
allowed — the §2.C.1 diagnosis: the note's class in q⁻¹, cleared to X = q, is
denom ∣ X^b · ∏ (1 − X^a)). -/
structure PolyGeom where
  countT : Polynomial ℚ
  degBoundT : ℕ
  degT_le : countT.natDegree ≤ degBoundT
  countS : Polynomial ℚ
  degBoundS : ℕ
  degS_le : countS.natDegree ≤ degBoundS
  geom : Qq
  qpow : ℕ
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣
    Polynomial.X ^ qpow * ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a : ℕ))

noncomputable def PolyGeom.val (P : PolyGeom) : Qq :=
  algebraMap (Polynomial ℚ) Qq (P.countT * P.countS) * P.geom

/-- The rationality burdens: ℚ(q) data in (iv)-POLY form + interpolation to the
measured rows.  Owners: CL-6 (iv)-POLY [1v] (tgP + tg_interp); (J-RAT) [1v]/[2b]
(jP + j_interp); INIT-RAT [1v] (ιP + ι_interp); + the cofinite-activity face
(cellP family, R45/R50 — per-cell, `act_iff` keyed to it). -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  tgP : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  jP  : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  ιP  : ∀ e (τ : T.State e), M.EntShape e τ → PolyGeom
  tg_ok : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (tgP e τ o).val ∈ OKat q₀
  j_ok  : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (jP e τ o).val ∈ OKat q₀
  ι_ok  : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (ιP e τ ε).val ∈ OKat q₀
  tg_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) ≠ .split →
    ((evalAt q₀ ⟨(tgP e τ o).val, tg_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  j_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) = .split →
    ((evalAt q₀ ⟨(jP e τ o).val, j_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  ι_interp : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(ιP e τ ε).val, ι_ok e τ ε q₀ h⟩ : ℚ) : ℝ) = M.ιsh e τ ε q₀
  ι_countS_one : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).countS = 1
  ι_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    ((ιP e τ ε).countT.eval q₀ : ℚ) = (M.entCount e τ ε q₀ : ℚ)
  tg_degT : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundT = T.Wloc e τ o
  tg_degS : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundS = T.Wstate e τ
  j_degT  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundT = T.Wloc e τ o
  j_degS  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundS = T.Wstate e τ
  ι_degT  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundT = M.Went e τ ε
  ι_degS  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundS = M.Went e τ ε
  cellP : ∀ e (τ : T.State e), M.Cell e τ → Polynomial ℚ
  cellP_deg : ∀ e (τ : T.State e) (c : M.Cell e τ), (cellP e τ c).natDegree ≤ T.Wstate e τ
  cellP_nonzero : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (c : M.Cell e τ), cellP e τ c ≠ 0
  cellP_count : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((cellP e τ c).eval q₀ : ℚ) = ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)
  act_iff : ∀ q₀ ∈ M.Pools, ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e,
    M.activeState q₀ e τ ↔ ∀ c : M.Cell e τ, (cellP e τ c).eval q₀ ≠ 0
  -- (J-RAT) PER-CELL tables (ratification 2026-07-28 finding 3).  PLAN-SYNC's
  -- deliverable is "the PER-CELL rational tables (per branching digit cell of each
  -- outcome class o at each state τ …) — a deliverable BEYOND PART-1's TOTAL
  -- cell-partition mass"; the note's J display: "J_{τ,o}(q) := the CELL-LEVEL
  -- resummed branching mass — the sum, over the branching digit CELLS of outcome
  -- class o at state τ, of the XHD-resummed conditional cell mass …, EACH CELL
  -- ONCE" (MOVES 11699–11703).  The measured per-cell carrier EXISTS: `M.Cell`
  -- with mass `M.μcell` (representative-quantified exactly as `rep_indep`).
  -- Owner stays [1v]: the tables ride as data/hypotheses, never proved here.
  jPCell : ∀ e (τ : T.State e), M.Cell e τ → PolyGeom
  jcell_ok : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (jPCell e τ c).val ∈ OKat q₀
  jcell_interp : ∀ e (τ : T.State e) (c : M.Cell e τ) (x : M.Rep e τ) (q₀ : ℚ)
    (h : q₀ ∈ M.Pools), routeOf (T.odata e τ (M.cellOut e τ c)) = .split →
    M.activeState q₀ e τ →
    ((evalAt q₀ ⟨(jPCell e τ c).val, jcell_ok e τ c q₀ h⟩ : ℚ) : ℝ)
      = M.μcell e τ x c q₀
  jcell_sum : ∀ e (τ : T.State e) (o : T.Out e τ), routeOf (T.odata e τ o) = .split →
    ∑ c ∈ M.cells e τ o, (jPCell e τ c).val = (jP e τ o).val

/-- (iv)-POLY VALUE LAWS (ratification 2026-07-28 finding 5).  CL-6: "T is one
polynomial of degree ≤ W_loc(m) and each cell size one polynomial of degree
≤ W_state(s), valued correctly at every prime power — CTS-M(iv)-POLY (CL-6, with
V.2's EXPONENT-MAP AUDIT)" (MOVES 12129–12132).  `PolyGeom` alone leaves
`countT`/`countS` arbitrary — only their product is interpolated (`tg_interp`), so
both could be absorbed into `geom`.  This record pins the VALUES: `countS` against
the cell-count carrier MeasuredSide DOES have (`cellInst`/`cellLvl`, the
`cellP_count` carrier), aggregated over the outcome's cell fiber exactly as
`rep_indep` aggregates masses; `countT` against the T-table count carrier `tCount`
— carried HERE as ℕ-valued data because MeasuredSide has no per-outcome T-count
field.  SEAM RESIDUE (recorded, not typed): `tCount`'s event-side identification
with the CTS/[1] count tables and V.2's exponent-map audit needs §V-TABLES
vocabulary — the MovesV seam (wave 4).  Consumed by the `_counted` variants
(CountLaws.lean); never self-supplied. -/
structure PolyGeomLaws (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) where
  tCount : ∀ e (τ : T.State e), T.Out e τ → ℚ → ℕ
  tcount_val : ∀ e (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
    (RB.tgP e τ o).countT.eval q₀ = (tCount e τ o q₀ : ℚ)
  scount_val : ∀ e (τ : T.State e) (o : T.Out e τ), ∀ q₀ ∈ M.Pools,
    M.activeState q₀ e τ →
    (RB.tgP e τ o).countS.eval q₀
      = ∑ c ∈ M.cells e τ o, ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)

variable {M : MeasuredSide T}

noncomputable abbrev RatBurdens.TG (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.tgP e τ o).val
noncomputable abbrev RatBurdens.J (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.jP e τ o).val
noncomputable def RatBurdens.ι (RB : RatBurdens T M) (e : ℕ) : T.State e → Qq :=
  fun τ => ∑ ε : M.EntShape e τ, (RB.ιP e τ ε).val

noncomputable def splitOuts (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (T.Out e τ) :=
  {o : T.Out e τ | routeOf (T.odata e τ o) = .split}.toFinset

section KTarget
variable {V : Type*} {St : ℕ → Type*}

private theorem kcol_route_c_ne (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.c ≠ 0 := by
  intro h
  unfold routeOf at hk
  rw [if_pos h] at hk
  exact Route.noConfusion hk

private theorem kcol_route_m_one (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.m = 1 := by
  have hc := kcol_route_c_ne o hk
  unfold routeOf at hk
  rw [if_neg hc] at hk
  by_contra h
  rw [if_neg h] at hk
  exact Route.noConfusion hk

/-- In a kcol outcome (c ≥ 1, m = 1) the single member is continuing. -/
private theorem kcol_head_isRight (o : Outcome V St) (hk : routeOf o = .kcol) :
    (o.mem.head o.hm).status.isRight = true := by
  have hall : ∀ μ ∈ o.mem, μ.status.isRight = true := by
    have hsub : (o.mem.filter (fun μ => μ.status.isRight)).Sublist o.mem :=
      List.filter_sublist
    have hle : o.c ≤ o.m := hsub.length_le
    have hc := kcol_route_c_ne o hk
    have hm := kcol_route_m_one o hk
    have hlen : (o.mem.filter (fun μ => μ.status.isRight)).length = o.mem.length := by
      have h1 : o.c = (o.mem.filter (fun μ => μ.status.isRight)).length := rfl
      have h2 : o.m = o.mem.length := rfl
      omega
    have heq := hsub.eq_of_length hlen
    intro μ hμ
    have hμf : μ ∈ o.mem.filter (fun μ => μ.status.isRight) := by
      rw [heq]; exact hμ
    exact (List.mem_filter.mp hμf).2
  exact hall _ (List.head_mem o.hm)

private theorem isRight_cast {a b : ℕ} (h : a = b) (x : V ⊕ St a) :
    (h ▸ x : V ⊕ St b).isRight = x.isRight := by
  subst h; rfl

end KTarget

/-- The kcol outcome's target state (the single continuing member's state, cast to
block size e via the SCS-supplied `hK`). -/
noncomputable def kTarget (T : TableShape n) (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e :=
  Sum.getRight
    ((hK ((T.odata e τ o).mem.head (T.odata e τ o).hm)
        (List.head_mem (T.odata e τ o).hm)) ▸
      ((T.odata e τ o).mem.head (T.odata e τ o).hm).status : T.VType ⊕ T.State e)
    (by rw [isRight_cast]; exact kcol_head_isRight _ hk)

/-- The per-block hypothesis U-6 (`scs`) produces: every kcol member has size e. -/
abbrev KmatHyp (T : TableShape n) (e : ℕ) : Prop :=
  ∀ (τ : T.State e) (o : T.Out e τ), routeOf (T.odata e τ o) = .kcol →
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e

/-- K_e: the kernel-column matrix — Σ_{kcol o → β} RB.TG e τ o. -/
noncomputable def Kmat (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) : Matrix (T.State e) (T.State e) Qq :=
  fun τ β => ∑ o : T.Out e τ,
    if hk : routeOf (T.odata e τ o) = .kcol then
      (if kTarget T e τ o hk (hK τ o hk) = β then RB.TG e τ o else 0)
    else 0

/-- b_e^{term,fin}(σ′): Σ_{termFin o, verdicts o = σ'} RB.TG e τ o (any σ';
supported on `verdictImage`). -/
noncomputable def bTerm (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq :=
  fun τ => ∑ o : T.Out e τ,
    if routeOf (T.odata e τ o) = .termFin ∧ (T.odata e τ o).verdicts = σ'
    then RB.TG e τ o else 0

/-- ESCAPE(E0) at an evaluated kernel: nonneg entries + escaping total mass.
`[DecidableEq ι]`: Matrix `1`/`^` need it (Fable#4-F1 batch, R29). -/
structure EscapeE0 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ)))
    Filter.atTop (nhds 0)

/-- Per-pool package (S.4).  `Act` is DETERMINED by CTS-M(ii)'s classification
(R2-8: `act_spec` is an iff — an empty Act needs the note's own no-realized-state
situation, never a modeling choice). -/
structure PoolHyp (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  act_spec : ∀ τ, τ ∈ Act ↔ M.activeState q₀ e τ
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok τ.1 β.1 τ.2 β.2⟩
  inactive_vanish : ∀ τ β (hok : Kmat T RB e hK τ β ∈ OKat q₀), τ ∈ Act → β ∉ Act →
    evalAt q₀ ⟨Kmat T RB e hK τ β, hok⟩ = 0
  e0 : EscapeE0 A

/-- D11's ONE coercion point (R19): the active matrix over ℝ.  Det transported by
`RingHom.map_det` + `Rat.cast_injective` (the E-phase simp lemma `Aℝ_det_iff` lives
with U-24a1's plumbing). -/
noncomputable def Aℝ {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) : Matrix P.Act P.Act ℝ :=
  P.A.map (algebraMap ℚ ℝ)

/-- CTS-M(ii-c)'s per-pool read-off gate, ℝ-typed via Aℝ (R19): "the evaluated
object's q₀-value (after cancellation — OKat membership is post-cancellation)
equals the active-subsystem solve there".  Junk-block determinants stay
census-side: recorded, never required nonzero. -/
def AVAgree {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) (v : Qq) (bA : P.Act → ℝ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, ((evalAt q₀ ⟨v, hok⟩ : ℚ) : ℝ) = ((1 - Aℝ P)⁻¹ *ᵥ bA) τ

/-- The global determinant hypothesis every solve consumer carries (U-22's target). -/
abbrev DetHyp (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0

/-! ## §2.D (BDY), shapes, RegP (the Defs-part; RS1Bundle/RS4Chain/ReadOffBundle
live in `MovesS/Interfaces.lean` per R25/R29 — the §W4-SYNC pins have NO E-phase
file). -/

/-- The μ̂ fence (no Add, no coercion). -/
structure MuHat where val : Qq

inductive ReadOwner | entrance | block
  deriving DecidableEq

def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance

/-- Length-matched shape record (REV 2); `δOf` per CONVENTION DELTA-ABS (R17). -/
structure Shape (T : TableShape n) where
  k    : ℕ
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)
  δOf  : Fin k → ℕ+
  σ0   : Multiset T.VType

/-- [2a] finiteness; CUT-3's image is the intended instance (W-7, seam). -/
structure ShapeFam (T : TableShape n) where
  Sh : Finset (Shape T)

/-- The δ-factor pool: CONSUMED split-leg δ's over the full roster ∪ the shape
legs' δ's.  CONTINUING members only (ratification 2026-07-28 finding 2 — the
over-collection was a silent strengthening): the note's E0 quantifier ranges over
"δ ranging over 1 AND every base-change index a β_{e_j,τ_j}(q^{δ_j}) leg of
b_e^split or RS.1-SH consumes" (MOVES 12165–12166), and b_e^split's display
evaluates β ONLY at block-state members — "τ-halted members contribute FACTOR 1
with σ_j their verdict value … β is evaluated only at block-state members"
(MOVES 11696–11698).  A halted member's δ indexes NO consumed β leg, so it must
not enlarge the E0/ACT pool burden; hence the `status.isRight` filter. -/
noncomputable def deltaFactors (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  ((Finset.Icc 1 n).biUnion fun e =>
    (Finset.univ : Finset (T.State e)).biUnion fun τ =>
      (Finset.univ : Finset (T.Out e τ)).biUnion fun o =>
        if routeOf (T.odata e τ o) = .split
        then (((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).map
          Member.δ).toFinset
        else ∅)
  ∪ F.Sh.biUnion fun Ŝ => Finset.image Ŝ.δOf Finset.univ

/-- MULTIPLICATIVE CLOSURE (R17, DELTA-ABS): all products of AT MOST n factors from
`deltaFactors`, incl. the empty product 1 (finite; (K-TRI) bounds nesting depth by n).
The closure lemma `nested_delta_mem` is U-16a3's spec obligation. -/
noncomputable def consumedDeltas (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  (fun s : Finset ℕ+ => s ∪ Finset.image₂ (· * ·) (deltaFactors T F) s)^[n] {1}

/-- CL-1's per-pool quantifier along one base prime: E0/ACT packages at δ = 1 AND
every consumed base-change leg pool p^δ. -/
def RegP (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M) (p : ℕ)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (F : ShapeFam T) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (δ : ℕ)))

end LeanUrat.MovesS
