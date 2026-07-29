/-
MovesV/Defs — shared vocabulary for MOVES §V-TABLES (the CTS state space, tables,
and the measured theorem CTS-M).

E-phase transcription of `lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md` (REV 9,
the closing revision) §2.A–§2.H.  Declaration order = spec (with the §2.H
reading-order note honored: RouteTag → JCells → CellPolyPack → μcellVal/Jval).
Definitions only — no `sorry`, no axioms; the only proofs are the displayed
Defs-layer obligations (`omem_kcol`, `realized_isSlot`, `gcell_denom_sum` and its
Σ'-packaging, the mechanical ▸-transport wrappers).  Compiler-forced adjustments
are catalogued in `MANIFEST.json` ("deviations").
-/
import Mathlib
import LeanUrat.MovesS.Defs
import LeanUrat.MovesD.Defs
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq PolyGeom OKat evalAt MuHat)

/-! ## §2.A The height apparatus -/

/-- A height point in D ℕ-slots (V.0). -/
abbrev Hpt (D : ℕ) := Fin D → ℕ

/-- concatenation of height points (used by templates and HMC). -/
def Hpt.append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) : Hpt (D₁ + D₂) :=
  Fin.append h₁ h₂

/-- the Fin-append splitters (Codex-18: displayed, closed). -/
def Hpt.take {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₁ :=
  fun i => h (Fin.castAdd D₂ i)
def Hpt.drop {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₂ :=
  fun j => h (Fin.natAdd D₁ j)

/-- prime-power evaluation points (A-7 repair). -/
def IsPP (q₀ : ℚ) : Prop := ∃ (p k : ℕ), p.Prime ∧ 0 < k ∧ q₀ = (p : ℚ) ^ k

/-- (XHD-w)'s exponent: "E affine in h with positive weights".  CHART CONVENTION
(C3, binding): every `AffineE` of this corpus is declared IN COORDINATES WHERE ITS
COEFFICIENTS ARE NATURAL. -/
structure AffineE (D : ℕ) where
  const : ℕ
  coeff : Fin D → ℕ
  pos   : ∀ i, 1 ≤ coeff i

def AffineE.eval {D : ℕ} (E : AffineE D) (h : Hpt D) : ℕ :=
  E.const + ∑ i, E.coeff i * h i

/-- V.0's LINEAR SET L(h₀; P) — bases and periods EXPLICITLY LISTED. -/
structure LinSet (D : ℕ) where
  base    : Hpt D
  periods : List (Hpt D)

def LinSet.Mem {D : ℕ} (L : LinSet D) (h : Hpt D) : Prop :=
  ∃ c : Fin L.periods.length → ℕ,
    h = fun i => L.base i + ∑ j, c j * (L.periods.get j) i

/-- THE DISJOINT-COMPONENT CONVENTION, AS A TYPE: a LISTED PARTITION. -/
structure SemilinPart (D : ℕ) where
  comps : List (LinSet D)
  disj  : comps.Pairwise (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h))

def SemilinPart.Mem {D : ℕ} (S : SemilinPart D) (h : Hpt D) : Prop :=
  ∃ L ∈ S.comps, L.Mem h

/-- Absorbing column labels: (e, f) with e·f ≤ n — MovesS's R20 pin verbatim. -/
abbrev VLabel (n : ℕ) := {ef : ℕ+ × ℕ+ // (ef.1 : ℕ) * (ef.2 : ℕ) ≤ n}

/-! ## §2.B The step system, the (U-A) supply pack, XHD-w and XHD-u -/

/-- The index vocabulary + measured primitives XHD quantifies over (V.0); the
history layer is POOL-INDEXED (REV 4, N-2); non-vacuity per C1/Codex-1; terminal
twins per the §2.B substitution table. -/
structure StepSys (n : ℕ) where
  Cell  : Type
  finC  : Fintype Cell
  cell_ne : Nonempty Cell
  Move  : Cell → Cell → Type
  MoveT : Cell → VLabel n → Type
  finM  : ∀ α β, Fintype (Move α β)
  finMT : ∀ α v, Fintype (MoveT α v)
  dim   : ∀ {α β}, Move α β → ℕ
  dimT  : ∀ {α v}, MoveT α v → ℕ
  Pools : Set ℚ
  pools_ne : Pools.Nonempty
  pools_pp : ∀ q₀ ∈ Pools, IsPP q₀
  pools_gt_one : ∀ q₀ ∈ Pools, (1 : ℚ) < q₀
  Hist  : ℚ → Cell → Type
  hist_ne : ∀ q₀ ∈ Pools, ∀ α, Nonempty (Hist q₀ α)
  zc    : ∀ {q₀ α}, Hist q₀ α → Prop
  zc_ne : ∀ q₀ ∈ Pools, ∀ α, ∃ x : Hist q₀ α, zc x
  Assign : ∀ {α β} (m : Move α β) {q₀}, Hist q₀ α → Hpt (dim m) → Type
  finA   : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) h, Fintype (Assign m x h)
  AssignT : ∀ {α v} (m : MoveT α v) {q₀}, Hist q₀ α → Hpt (dimT m) → Type
  finAT  : ∀ {α v} (m : MoveT α v) {q₀} (x : Hist q₀ α) h, Fintype (AssignT m x h)
  ext : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h : Hpt (dim m)),
    Assign m x h → Hist q₀ β
  ext_zc : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h) (a : Assign m x h),
    zc x → zc (ext m x h a)
  massOf : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h : Hpt (dim m)),
    Assign m x h → ℝ
  massOfT : ∀ {α v} (m : MoveT α v) {q₀} (x : Hist q₀ α) (h : Hpt (dimT m)),
    AssignT m x h → ℝ
  out_ne : ∀ q₀ ∈ Pools, ∀ (α : Cell) (x : Hist q₀ α), zc x →
    (∃ β, ∃ m : Move α β, ∃ h : Hpt (dim m), Nonempty (Assign m x h)) ∨
    (∃ v, ∃ m : MoveT α v, ∃ h : Hpt (dimT m), Nonempty (AssignT m x h))

/-- T(h) from x — a DEF (C2: the count IS the Assign cardinality). -/
def StepSys.cntraw {n} (S : StepSys n) {α β} (m : S.Move α β) {q₀}
    (x : S.Hist q₀ α) (h : Hpt (S.dim m)) : ℕ :=
  @Fintype.card (S.Assign m x h) (S.finA m x h)
def StepSys.cntrawT {n} (S : StepSys n) {α v} (m : S.MoveT α v) {q₀}
    (x : S.Hist q₀ α) (h : Hpt (S.dimT m)) : ℕ :=
  @Fintype.card (S.AssignT m x h) (S.finAT m x h)

/-- (U-A)'s §C supply, TYPED.  Owner §C/HC-2. -/
structure C15Pack (n : ℕ) (S : StepSys n) where
  Inv   : Type
  invOf : ∀ {α β} (m : S.Move α β) {q₀}, S.Hist q₀ α → Hpt (S.dim m) → Inv
  invOfT : ∀ {α v} (m : S.MoveT α v) {q₀}, S.Hist q₀ α → Hpt (S.dimT m) → Inv
  F     : Inv → ℚ → ℝ
  mass_factors : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dim m)) (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a = F (invOf m x h) q₀
  mass_factorsT : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOfT m x h a = F (invOfT m x h) q₀

/-- (XHD-w) WEIGHTS, typed.  Owner [2b]. -/
structure XHDw (n : ℕ) (S : StepSys n) where
  E : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  w_eq : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
    (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a = (q₀ : ℝ) ^ (-((E m).eval h : ℤ))
  wT_eq : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOfT m x h a = (q₀ : ℝ) ^ (-((ET m).eval h : ℤ))

/-- the derived one-step weight g^{α,β}_{m,o}(h)(q₀) — a def, not a field. -/
noncomputable def XHDw.g {n} {S : StepSys n} (X : XHDw n S) {α β}
    (m : S.Move α β) (h : Hpt (S.dim m)) (q₀ : ℚ) : ℝ :=
  (q₀ : ℝ) ^ (-((X.E m).eval h : ℤ))

/-- (XHD-u) UNIFORMITY, typed; SAME-POOL comparisons + zc guards (REV 4).
Owner [2b]; NOT §C-derivable (V1-7's fence). -/
structure XHDu (n : ℕ) (S : StepSys n) where
  u_R_mass : ∀ {α β} (m : S.Move α β) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dim m)) (a : S.Assign m x h) (a' : S.Assign m x' h),
    q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.massOf m x h a = S.massOf m x' h a'
  u_R_cnt : ∀ {α β} (m : S.Move α β) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dim m)), q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.cntraw m x h = S.cntraw m x' h
  u_T : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h h' : Hpt (S.dim m)), q₀ ∈ S.Pools → S.zc x →
    0 < S.cntraw m x h → 0 < S.cntraw m x h' →
    S.cntraw m x h = S.cntraw m x h'
  u_R_massT : ∀ {α v} (m : S.MoveT α v) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) (a : S.AssignT m x h) (a' : S.AssignT m x' h),
    q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.massOfT m x h a = S.massOfT m x' h a'
  u_R_cntT : ∀ {α v} (m : S.MoveT α v) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dimT m)), q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.cntrawT m x h = S.cntrawT m x' h
  u_TT : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h h' : Hpt (S.dimT m)), q₀ ∈ S.Pools → S.zc x →
    0 < S.cntrawT m x h → 0 < S.cntrawT m x h' →
    S.cntrawT m x h = S.cntrawT m x h'

/-! ## §2.C The state space 𝒞_n (CTS-S) and the computed-partition deliverable -/

/-- A SKELETON s (V.2 CTS-S) — EXACTLY MovesSp.Species, catalogue-membered. -/
structure Skeleton (n : ℕ) where
  sp  : MovesSp.Species
  mem : MovesSp.InCatalogue n sp

/-- (D2) generator KIND — a proper inductive (C4/C5). -/
inductive GenKind where
  | anchor (a_eff : ℤ)
  | rel (relPoly : Polynomial ℤ)

def GenKind.twistExp : GenKind → ℤ
  | .anchor a => a
  | .rel _ => 0

/-- ONE (D2) GENERATOR over the per-prime concrete-state carrier (C10; REV-3
rel forcing per Codex-3). -/
structure GenSpec (Carrier : ℚ → Type) where
  idx    : Type
  finI   : Fintype idx
  kind   : GenKind
  base   : ∀ q₀, Carrier q₀ → idx
  twistOf : ∀ q₀, ℤ → Carrier q₀ → Carrier q₀
  twist0 : ∀ q₀, twistOf q₀ 0 = id
  twist_add : ∀ q₀ a b, twistOf q₀ (a + b) = twistOf q₀ a ∘ twistOf q₀ b
  part   : ∀ q₀, Carrier q₀ → idx
  part_eq : ∀ q₀ x, part q₀ x = base q₀ (twistOf q₀ kind.twistExp x)
  Val    : ℚ → Type
  ringV  : ∀ q₀, CommRing (Val q₀)
  relObs : ∀ q₀, Carrier q₀ → Val q₀
  stratOf : ∀ q₀, Val q₀ → idx
  rel_eq : ∀ (P : Polynomial ℤ), kind = .rel P → ∀ q₀ x,
    base q₀ x = stratOf q₀
      (letI := ringV q₀
       ((P.map (Int.castRingHom (Val q₀))).eval (relObs q₀ x)))

/-- the skeleton's BLOCK SIZE e (inventory slot 13). -/
def skBlk {n : ℕ} (s : Skeleton n) : ℕ := s.sp.W * s.sp.D

/-- ONE OUTCOME MEMBER (REV 5, Codex-2): the DEG-CONS tuple datum. -/
structure OMember (n : ℕ) where
  size   : ℕ
  δ      : ℕ+
  status : VLabel n ⊕ Skeleton n

open Classical in
/-- (D1)–(D4) for ONE skeleton — CL-13's COMPUTED-PARTITION DELIVERABLE. -/
structure BlockData (n : ℕ) (s : Skeleton n) where
  Carrier : ℚ → Type
  finCar : ∀ q₀, Fintype (Carrier q₀)
  -- (D1) the menu:
  Letter : Type
  finL   : Fintype Letter
  letterSp : Letter → MovesSp.Species ⊕ MovesSp.Verdict
  letter_menu : ∀ m, letterSp m ∈ MovesSp.Out n s.sp
  Obs     : Letter → ℚ → Type
  evalObs : ∀ (m : Letter) (q₀ : ℚ), Carrier q₀ → Obs m q₀
  -- (D2) the generator list:
  Gen  : Type
  finG : Fintype Gen
  gen  : Gen → GenSpec Carrier
  -- (D3) the meet list:
  Wstate : ℕ
  sizeP  : (∀ g : Gen, (gen g).idx) → Polynomial ℚ
  size_deg : ∀ a, (sizeP a).natDegree ≤ Wstate
  size_count : ∀ (a) (q₀ : ℚ), IsPP q₀ →
    ((sizeP a).eval q₀ : ℚ)
      = (letI := finCar q₀
         (Finset.univ.filter (fun x : Carrier q₀ => ∀ g, (gen g).part q₀ x = a g)).card)
  -- the letter's FULL OUTCOME roster (REV 4, Codex-2):
  Outc : Letter → Type
  finO : ∀ m, Fintype (Outc m)
  -- THE OUTCOME-MEMBER ROSTER (REV 5, Codex-2):
  omem : ∀ m (o : Outc m), List (OMember n)
  omem_ne : ∀ m o, omem m o ≠ []
  omem_size : ∀ m o, ∀ mu ∈ omem m o, ∀ sk : Skeleton n,
    mu.status = Sum.inr sk → skBlk sk = mu.size
  -- (D4) the target data per CONTINUING OUTCOME:
  cont : ∀ m, Outc m → Prop
  decCont : ∀ m, DecidablePred (cont m)
  cont_iff : ∀ m o, cont m o ↔ ∃ mu ∈ omem m o, mu.status.isRight = true
  tgtSk : ∀ m (o : Outc m), cont m o → Skeleton n
  tgt_sp : ∀ m (o : Outc m) (h : cont m o),
    letterSp m = Sum.inl (tgtSk m o h).sp
  omem_sel : ∀ m (o : Outc m) (h : cont m o),
    ∃ mu ∈ omem m o, mu.status = Sum.inr (tgtSk m o h)
    -- THE SELECTED-MEMBER TIE (REV 6, Codex5-22)

/-- `omem_kcol` — the DERIVED length-1 corollary (displayed). -/
theorem BlockData.omem_kcol {n s} (B : BlockData n s) (m) (o : B.Outc m)
    (h : B.cont m o) (h1 : (B.omem m o).length = 1) :
    ((B.omem m o).head (B.omem_ne m o)).status = Sum.inr (B.tgtSk m o h) := by
  obtain ⟨mu, hmem, hst⟩ := B.omem_sel m o h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
  have hae : ∀ x ∈ B.omem m o, x = a := by
    intro x hx; rw [ha] at hx; exact List.eq_of_mem_singleton hx
  rw [hae _ (List.head_mem (B.omem_ne m o)), ← hae mu hmem]
  exact hst

/-- `BlockData.CellIdx` — DECLARED IN DEFS (REV 4, Codex-15): zero-size
deletion encoded. -/
def BlockData.CellIdx {n s} (B : BlockData n s) : Type :=
  {a : ∀ g : B.Gen, (B.gen g).idx // B.sizeP a ≠ 0}

/-- The target index of an OUTCOME (REV 4/5): continuing ⟹ target-block cell;
terminal ⟹ absorbing column label (`term` REQUIRES the outcome terminal). -/
inductive TargetIx (n : ℕ) {s : Skeleton n} (B : BlockData n s)
    (B' : ∀ s', BlockData n s') (m : B.Letter) (o : B.Outc m) where
  | cell (h : B.cont m o) (β : (B' (B.tgtSk m o h)).CellIdx)
  | term (ht : ¬ B.cont m o) (v : VLabel n)

/-- THE TABLE FAMILY over one n (CTS-T): the record the SEAM instantiates into
MovesS.TableShape (V7-3a). -/
structure CtsFamily (n : ℕ) where
  bd : ∀ s : Skeleton n, BlockData n s
  tcell : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (h : (bd s).cont m o),
    (bd s).CellIdx → (bd ((bd s).tgtSk m o h)).CellIdx
  tcellM : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (i : Fin ((bd s).omem m o).length) (sk : Skeleton n),
    (((bd s).omem m o).get i).status = Sum.inr sk →
    (bd s).CellIdx → (bd sk).CellIdx
  tcellM_sel : ∀ (s) (m) (o) (h : (bd s).cont m o),
    ∃ (i : Fin ((bd s).omem m o).length)
      (hs : (((bd s).omem m o).get i).status = Sum.inr ((bd s).tgtSk m o h)),
      tcellM s m o i _ hs = tcell s m o h    -- [tie] (REV 7, C3)
  Wloc : ∀ (s : Skeleton n), (bd s).Letter → ℕ
  T : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (α : (bd s).CellIdx) (β : TargetIx n (bd s) bd m o), Polynomial ℚ
  T_deg : ∀ s m o α β, (T s m o α β).natDegree ≤ Wloc s m
  vlabOf : ∀ (s) (m) (o : (bd s).Outc m), ¬ (bd s).cont m o → VLabel n

/-- The (D4)-typed step data (REV 3/4). -/
structure MoveData (n : ℕ) (C : CtsFamily n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : (C.bd s).Outc m
  hc : (C.bd s).cont m o
  α  : (C.bd s).CellIdx

/-- the datum's source and its tcell-ENFORCED target. -/
def MoveData.src {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx := ⟨d.s, d.α⟩
def MoveData.tgt {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx :=
  ⟨(C.bd d.s).tgtSk d.m d.o d.hc, C.tcell d.s d.m d.o d.hc d.α⟩

structure TermData (n : ℕ) (C : CtsFamily n) (v : VLabel n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : (C.bd s).Outc m
  ht : ¬ (C.bd s).cont m o
  hv : C.vlabOf s m o ht = v
  α  : (C.bd s).CellIdx

/-- THE DATUM'S OWN TABLE INDEX (REV 5, Fable M-1). -/
def MoveData.tix {n C} (d : MoveData n C) :
    TargetIx n (C.bd d.s) C.bd d.m d.o :=
  .cell d.hc (C.tcell d.s d.m d.o d.hc d.α)
def TermData.tix {n C v} (d : TermData n C v) :
    TargetIx n (C.bd d.s) C.bd d.m d.o :=
  .term d.ht v

/-! ## §2.D Entrance shapes ε (V.1(iii)) -/

/-- shape-level eligibility of a (g, μ) pair at a read (the L5 budget). -/
def EligPair (R : MovesD.ShapeRead) (g μ : ℕ) : Prop :=
  1 ≤ g ∧ 1 ≤ μ ∧ g * μ ≤ R.len

/-- a branch SLOT (REV 7, C2): every read that CAN branch has a slot. -/
def IsBranchSlot (R : MovesD.ShapeRead) : Prop := 2 ≤ R.mbar

instance (R : MovesD.ShapeRead) : Decidable (IsBranchSlot R) := by
  unfold IsBranchSlot; infer_instance

/-- ACTUAL branching — THE REALIZED KEY (REV 7, C2; finiteness record REV 8 M1). -/
def RealizedBranching {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (w : ℕ) (ν : MovesC.Node p F) : Prop :=
  2 ≤ Nat.card {q : Polynomial F //
        MovesD.EligibleImage p w ν.g ν.μ (MovesD.RanchImage ν) q}

/-- THE E6/E7 BRIDGE (REV 8, M1): a realized-branching read HAS a slot;
`hcard` is the TYPED HYPOTHESIS ROW (E6/E7, MovesD's PROVED apparatus). -/
theorem realized_isSlot {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (R : MovesD.ShapeRead) (ν : MovesC.Node p F)
    (hcard : Nat.card {q : Polynomial F //
        MovesD.EligibleImage p R.w ν.g ν.μ (MovesD.RanchImage ν) q}
      ≤ R.mbar)
    (hrb : RealizedBranching R.w ν) : IsBranchSlot R :=
  le_trans hrb hcard

-- (`eligibleImage_finite` — the §2.D finiteness obligation — is a REAL
--  obligation of V3-1's file per §8; stated and proved THERE, keeping this
--  Defs layer sorry-free.  Recorded in MANIFEST deviations.)

/-- the i-th slot read's menu card (REV 7, GAP-4: Option-indexed). -/
def branchMenuCard (n : ℕ) (P : MovesD.Shape n) (i : ℕ) : ℕ :=
  ((((P : MovesD.ShapePrefix).reads.filter
    (fun R => decide (IsBranchSlot R)))[i]?).map MovesD.ShapeRead.mbar).getD 0

/-- the i-th slot read of P̂, Option-valued (REV 7, GAP-4). -/
def branchingRead? (n : ℕ) (P : MovesD.Shape n) (i : ℕ) :
    Option MovesD.ShapeRead :=
  ((P : MovesD.ShapePrefix).reads.filter
    (fun R => decide (IsBranchSlot R)))[i]?

/-- the position of the r-th slot read in P̂'s read list (REV 7, GAP-4). -/
def bIdx {n : ℕ} (P : MovesD.Shape n) (r : ℕ) : ℕ :=
  ((List.range (P : MovesD.ShapePrefix).reads.length).filter
    (fun j => (((P : MovesD.ShapePrefix).reads[j]?).map
      (fun R => decide (IsBranchSlot R))).getD false)).getD r 0

/-- the realized node at the r-th branching read of a presented prefix. -/
noncomputable def nodeAt {n : ℕ} {p F} [Fact p.Prime] [Field F] [Finite F]
    {pol : MovesD.CanonPolicy p F} {P : MovesD.Shape n}
    (i : MovesD.PrefIdx n pol P) (r : ℕ) : Option (MovesC.Node p F) :=
  (MovesD.reprOf i).nodes[bIdx P r]?

/-- V.1(iii)'s ENTRANCE SHAPE — the TRIPLE ε := (P̂, b, σ_sel); P̂ IS
MovesD.Shape n (heights retained BY TYPE); ties per REV 2 (C6) / REV 7 (C2). -/
structure EntShapeV (n : ℕ) where
  Phat   : MovesD.Shape n
  hne    : (Phat : MovesD.ShapePrefix).reads ≠ []
  gsel   : ℕ
  musel  : ℕ
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hentry : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    R.g = gsel ∧ R.μ = musel
  helig  : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    EligPair R gsel musel
  selRec : List ℕ
  hlen   : selRec.length =
    ((Phat : MovesD.ShapePrefix).reads.filter
      (fun R => decide (IsBranchSlot R))).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < branchMenuCard n Phat i

/-- THE σ_sel/L11 VALUE TIE — A DEF (REV 6/7): the σ_sel-COMPONENT OF ε-CLASS
MEMBERSHIP, keyed to MovesD's OWN E9 encoding component `selRank w ν % m̄`. -/
def SelMatches {n : ℕ} {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] {pol : MovesD.CanonPolicy p F} (ε : EntShapeV n)
    (i : MovesD.PrefIdx n pol ε.Phat) : Prop :=
  ∀ (r : ℕ) (hr : r < ε.selRec.length) (R : MovesD.ShapeRead)
    (ν : MovesC.Node p F),
    branchingRead? n ε.Phat r = some R → nodeAt i r = some ν →
    ε.selRec.get ⟨r, hr⟩ = MovesD.selRank R.w ν % R.mbar

/-- HEIGHT PROJECTION (rev 4): the (h_r, u*_r) pair vector over P̂'s reads. -/
def EntShapeV.hent {n : ℕ} (ε : EntShapeV n) : List (ℕ × ℚ) :=
  (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))

/-- the standard zigzag code (REV 4, Codex-15: orientation pinned at E-phase). -/
noncomputable abbrev zig : ℤ ≃ ℕ := (Denumerable.eqv ℤ)

/-- the ℕ-code of the retained height data — LENGTH-SEEDED (REV 5, Codex-7/G-2). -/
noncomputable def EntShapeV.hentCode {n : ℕ} (ε : EntShapeV n) : ℕ :=
  Nat.pair (ε.Phat : MovesD.ShapePrefix).reads.length
    (((ε.Phat : MovesD.ShapePrefix).reads.map
      (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0)

/-- ledger exponent A(ε) := §D4-R's A(P̂); pool dimension W_ent(ε) := W(P̂). -/
noncomputable def EntShapeV.A {n : ℕ} (ε : EntShapeV n) : ℕ :=
  (ε.Phat : MovesD.ShapePrefix).A' n
def EntShapeV.Went {n : ℕ} (ε : EntShapeV n) : ℕ := (ε.Phat : MovesD.ShapePrefix).W

/-! ## §2.D (cont.) — the template-side letter vocabulary (REV 9, N-3) -/

/-- the species-tag projection (granularity hatch recorded). -/
def speciesTagOf (s : MovesSp.Species) : MovesC.ReadSpecies :=
  match s.tag with
  | .root => .root
  | .postInc => .increment
  | .postRec => .recentering

/-- the letter's monic reading (keyed to MovesD's `ShapePrefix.MonicTie`). -/
def monicTopOf (n : ℕ) (s : MovesSp.Species) : Bool :=
  decide (s.s0 + MovesSp.Species.wraw s = n)

/-- a (collapsed) self-loop letter — the SP4 characterization. -/
def SelfLoopLetter (n : ℕ) (s : MovesSp.Species) : Bool :=
  decide (s.tag = .postRec ∧ s.e = 1 ∧ s.sel = some (1, s.W))

/-- the letter-side menu bound m̄ (`ShapeRead.mbar`'s template mirror). -/
def letterMbar (s : MovesSp.Species) : ℕ :=
  (s.sel.map (fun gμ => s.ell / (gμ.1 * gμ.2))).getD 0

/-- a branching LETTER — the template-side SLOT layout. -/
def IsBranchingLetter (n : ℕ) (s : MovesSp.Species) : Bool :=
  decide (2 ≤ letterMbar s)

/-- the i-th branching letter's menu card (Option-indexed). -/
def letterMenuCard (n : ℕ) (w : List MovesSp.Species) (i : ℕ) : ℕ :=
  (((w.filter (IsBranchingLetter n))[i]?).map letterMbar).getD 0

/-- the letter one WF read presents — per-index tie clauses. -/
def SpFitsRead (n : ℕ) (i : ℕ) (s : MovesSp.Species)
    (R : MovesD.ShapeRead) : Prop :=
  s.e = R.e ∧ s.s0 = R.s0 ∧ s.ell = R.len ∧ s.w = R.w ∧
  s.sel = some (R.g, R.μ) ∧ (R.g, R.μ) ∈ s.lam ∧
  s.a = R.s0 / R.e ∧ s.d = s.ell + 1 ∧
  s.slots = Finset.Icc s.a (s.a + s.ell) ∧
  (R.species = if i = 0 then .root else speciesTagOf s) ∧
  (R.monicTop = (decide (i = 0) && monicTopOf n s))

def SpWordFits (n : ℕ) (P : MovesD.ShapePrefix)
    (ws : List MovesSp.Species) : Prop :=
  ws.length = P.reads.length ∧
  (∀ i (hw : i < ws.length) (hp : i < P.reads.length),
    SpFitsRead n i (ws.get ⟨i, hw⟩) (P.reads.get ⟨i, hp⟩)) ∧
  (∀ s ∈ ws, MovesSp.InCatalogue n s) ∧
  ws.Chain' (MovesSp.SuccStep n)

open Classical in
/-- the species word behind a shape-prefix — CLOSED IN DEFS at REV 9 (N-3):
checked classical dite; junk [] dead at consumers through V3-3a. -/
noncomputable def spWord (n : ℕ) (P : MovesD.ShapePrefix) :
    List MovesSp.Species :=
  if hc : ∃ ws, SpWordFits n P ws then hc.choose else []

/-- The height-forgetting TEMPLATE εT (REV 2, C12/A-3: intrinsic boundedness). -/
structure EntTemplate (n : ℕ) where
  word   : List MovesSp.Species
  hne    : word ≠ []
  hMem   : ∀ s ∈ word, MovesSp.InCatalogue n s
  hWalk  : word.Chain' (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s')
  gsel : ℕ
  musel : ℕ
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hEntry : ∀ s, word.getLast? = some s → s.sel = some (gsel, musel)
  selRec : List ℕ
  hlen   : selRec.length = (word.filter (IsBranchingLetter n)).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < letterMenuCard n word i

open Classical in
/-- ε's template, Option-valued — RESTRUCTURED at REV 7 (C11): the WF
conjunction CHECKED here; V3-3b's deliverable is the SCOPED
`template_total_of_perimeter` (M1 repair — the unscoped totality is refuted
at `TTNeg.template_total_false`, V3_spword_negWitness3). -/
noncomputable def EntShapeV.template? {n : ℕ} (ε : EntShapeV n) :
    Option (EntTemplate n) :=
  let w := MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix))
  if hw : w ≠ [] ∧ (∀ s ∈ w, MovesSp.InCatalogue n s) ∧
      w.Chain' (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s') ∧
      (∀ s, w.getLast? = some s → s.sel = some (ε.gsel, ε.musel)) ∧
      ε.selRec.length = (w.filter (IsBranchingLetter n)).length ∧
      (∀ i (hi : i < ε.selRec.length),
        ε.selRec.get ⟨i, hi⟩ < letterMenuCard n w i)
  then some { word := w, gsel := ε.gsel, musel := ε.musel,
              selRec := ε.selRec,
              hsel_g := ε.hsel_g, hsel_μ := ε.hsel_μ,
              hne := hw.1, hMem := hw.2.1, hWalk := hw.2.2.1,
              hEntry := hw.2.2.2.1, hlen := hw.2.2.2.2.1,
              hmenu := hw.2.2.2.2.2 }
  else none

/-- the instantiation dimension of a template (V3-5's chart). -/
def EntTemplate.entDim {n : ℕ} (εT : EntTemplate n) : ℕ :=
  2 * εT.word.length + (εT.word.filter (SelfLoopLetter n)).length

/-- the three slot projections + the word expansion, CLOSED (REV 6, Codex5-28). -/
def EntTemplate.pairSlots {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) :
    List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin εT.word.length =>
    (h ⟨2 * i, by have := i.isLt; unfold EntTemplate.entDim; omega⟩,
     h ⟨2 * i + 1, by have := i.isLt; unfold EntTemplate.entDim; omega⟩))
def EntTemplate.depthSlots {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) :
    List ℕ :=
  List.ofFn (fun j : Fin (εT.word.filter (SelfLoopLetter n)).length =>
    h ⟨2 * εT.word.length + j, by
        have := j.isLt; unfold EntTemplate.entDim; omega⟩)

/-- re-expand each collapsed self-loop letter into a run of (depth + 1) copies. -/
def expandRuns (n : ℕ) : List MovesSp.Species → List ℕ → List MovesSp.Species
  | [], _ => []
  | s :: ws, ds =>
    if SelfLoopLetter n s
    then List.replicate (ds.headD 0 + 1) s ++ expandRuns n ws ds.tail
    else s :: expandRuns n ws ds

/-- Defs-local prefix extension + the reads-[] prefix (REV 8, N6). -/
def snocP (P : MovesD.ShapePrefix) (R : MovesD.ShapeRead) :
    MovesD.ShapePrefix := ⟨P.reads ++ [R]⟩
def emptyPrefix : MovesD.ShapePrefix := ⟨[]⟩

open Classical in
/-- the Defs-local Prop pinning a candidate ShapeRead's EVERY field (REV 8, N6). -/
def ReadFits (n : ℕ) (P : MovesD.ShapePrefix) (s : MovesSp.Species)
    (hslot uslot : ℕ) (R : MovesD.ShapeRead) : Prop :=
  R.e = s.e ∧ R.s0 = s.s0 ∧ R.wSide = s.wraw ∧
  (∀ gμ, s.sel = some gμ → R.g = gμ.1 ∧ R.μ = gμ.2) ∧
  R.w = (P.reads.getLast?.elim 1 (fun Rp => Rp.w * Rp.g)) ∧
  R.Dwidth = (P.reads.getLast?.elim 1 MovesD.ShapeRead.childWidthS) ∧
  R.h = hslot ∧ R.gam = zig.symm uslot ∧
  ((R.gam : ℚ) = (R.e : ℚ)
      * (((snocP P R).strS P.reads.length : ℚ) * R.ustar)
    + (((R.s0 + R.wSide) : ℕ) : ℚ) * (R.h : ℚ)) ∧
  ((R.e : ℤ) * R.a = (R.s0 : ℤ) - MovesD.bezT R.e R.h * R.gam) ∧
  R.species = (if P.reads = [] then .root else speciesTagOf s) ∧
  R.monicTop = (decide (P.reads = []) && monicTopOf n s)

open Classical in
/-- the per-letter read reconstruction, Option-valued (REV 7, C11 / REV 8, N6). -/
noncomputable def readOfLetter? (n : ℕ) (P : MovesD.ShapePrefix)
    (s : MovesSp.Species) (hslot uslot : ℕ) : Option MovesD.ShapePrefix :=
  if hc : ∃ R : MovesD.ShapeRead, ReadFits n P s hslot uslot R
  then some (snocP P hc.choose) else none

/-- fold the reconstruction along the expanded word (Option-monadic). -/
noncomputable def shapeOfSlots? (n : ℕ) (ws : List MovesSp.Species)
    (ps : List (ℕ × ℕ)) : Option MovesD.ShapePrefix :=
  (ws.zip ps).foldlM (fun P sp => readOfLetter? n P sp.1 sp.2.1 sp.2.2)
    emptyPrefix

/-- the WF-check abbreviation, DISPLAYED (REV 8, N6). -/
abbrev ShapeWFOf (n : ℕ) (P : MovesD.ShapePrefix) : Prop :=
  MovesD.ShapeWF n P

/-- the five EntShapeV tie clauses at (⟨P, hWF⟩, εT). -/
def EntTiesAt {n : ℕ} (Ph : MovesD.Shape n) (εT : EntTemplate n) : Prop :=
  ((Ph : MovesD.ShapePrefix).reads ≠ []) ∧
  (∀ R, (Ph : MovesD.ShapePrefix).reads.getLast? = some R →
     R.g = εT.gsel ∧ R.μ = εT.musel) ∧
  (∀ R, (Ph : MovesD.ShapePrefix).reads.getLast? = some R →
     EligPair R εT.gsel εT.musel) ∧
  (εT.selRec.length = ((Ph : MovesD.ShapePrefix).reads.filter
     (fun R => decide (IsBranchSlot R))).length) ∧
  (∀ i (hi : i < εT.selRec.length),
     εT.selRec.get ⟨i, hi⟩ < branchMenuCard n Ph i)

open Classical in
/-- write the height/depth point into the template's slots — Option-valued
(REV 7, C11); V3-3d owns `writeHeights_total` and the TOTAL `writeHeights`. -/
noncomputable def writeHeights? {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) : Option (EntShapeV n) :=
  (shapeOfSlots? n (expandRuns n εT.word (εT.depthSlots h))
    (εT.pairSlots h)).bind fun P =>
  if hw : ∃ hWF : ShapeWFOf n P, EntTiesAt ⟨P, hWF⟩ εT
  then some { Phat := ⟨P, hw.choose⟩,
              gsel := εT.gsel, musel := εT.musel, selRec := εT.selRec,
              hsel_g := εT.hsel_g, hsel_μ := εT.hsel_μ,
              hne := hw.choose_spec.1, hentry := hw.choose_spec.2.1,
              helig := hw.choose_spec.2.2.1,
              hlen := hw.choose_spec.2.2.2.1,
              hmenu := hw.choose_spec.2.2.2.2 }
  else none

/-- the TOTAL consumption wrappers (REV 7, C11) — defaults never realized. -/
noncomputable def instA {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) : ℕ :=
  ((writeHeights? εT h).map EntShapeV.A).getD 0
noncomputable def instHentCode {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) : ℕ :=
  ((writeHeights? εT h).map EntShapeV.hentCode).getD 0

/-! ## §2.E The marked space and μ̂ (keying to MovesD; the [3t] fence) -/

/-- ι's counting-native carrier: the ε-REFINED ENTRANCE INDEX (cell-condition
cut; `lands_sel` A FIELD at REV 7, Codex6-C1). -/
structure EntranceCut (n : ℕ) (ε : EntShapeV n) (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (pol : MovesD.CanonPolicy p F) where
  lands : MovesD.PrefIdx n pol ε.Phat → Prop
  decL  : DecidablePred lands
  lands_sel : ∀ i, lands i → SelMatches ε i

/-- The MARKED entrance mass at level N, division-free. -/
noncomputable def iotaCount {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type*}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) : ℕ :=
  ∑ᶠ i ∈ {i | cut.lands i}, Nat.card ↥(S.fiber i)

/-- THE CENSUS↔CUT IDENTIFICATION CARRIER (REV 8, N3; fiber tie REV 9, N-2). -/
structure CutRealization {n : ℕ} (ε : EntShapeV n) {p : ℕ} {F : Type}
    [Fact p.Prime] [Field F] [Finite F] {pol : MovesD.CanonPolicy p F}
    {N m : ℕ}
    (Pr : MovesD.Presented p F n N m pol ε.Phat)
    {B : Type*} (inst : Finset B) where
  cut : EntranceCut n ε p F pol
  encode : {i : MovesD.PrefIdx n pol ε.Phat // cut.lands i} → B
  encode_inj : Function.Injective encode
  encode_mem : ∀ i, encode i ∈ inst
  encode_surj : ∀ b ∈ inst, ∃ i, encode i = b
  toBox : B → MovesD.Box p m
  encode_fiber : ∀ i, toBox (encode i) ∈ Pr.fiber i.1

/-! ## §2.F The counting carrier `CtsMeasured` (the `MeasuredSide` producer's data half) -/

/-- the three ▸-transport helpers (REV 5, Codex-15) — HOISTED before §2.F
(compiler-forced: the structure-field ▸ motives need the named wrappers;
recorded in MANIFEST deviations). -/
def castMove {n} {S : StepSys n} {α α' β β' : S.Cell}
    (hα : α = α') (hβ : β = β') (m : S.Move α β) : S.Move α' β' :=
  hα ▸ hβ ▸ m
def castHpt {D D' : ℕ} (h : D = D') (x : Hpt D) : Hpt D' := h ▸ x
def castAssign {n} {S : StepSys n} {α α' β β' : S.Cell}
    (hα : α = α') (hβ : β = β') {m : S.Move α β} {q₀}
    {x : S.Hist q₀ α} {h : Hpt (S.dim m)} (a : S.Assign m x h) :
    S.Assign (castMove hα hβ m) (hα ▸ x) (by cases hα; cases hβ; exact h) := by
  cases hα; cases hβ; exact a
def castMoveT {n} {S : StepSys n} {α α' : S.Cell} {v : VLabel n}
    (hα : α = α') (m : S.MoveT α v) : S.MoveT α' v := hα ▸ m

/-- REV 7 (C10): the classifier half — boxes, embeddings, digit cells,
per-assignment events. -/
structure CtsCells (n : ℕ) (C : CtsFamily n) (S : StepSys n) where
  toStepCells : S.Cell ≃ Σ s : Skeleton n, (C.bd s).CellIdx
  Pools : Set ℚ
  pools_sub : Pools ⊆ S.Pools
  pools_pp : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  box_card : ∀ q₀ ∈ Pools, ∀ N, ((@Fintype.card (Box q₀ N) (finB q₀ N) : ℚ)) = q₀ ^ (n * N)
  moveOf : ∀ d : MoveData n C,
    S.Move (toStepCells.symm d.src) (toStepCells.symm d.tgt)
  moveOf_bij : ∀ αc : S.Cell, Function.Bijective
    (fun d : {d : MoveData n C // toStepCells.symm d.src = αc} =>
      (⟨toStepCells.symm d.1.tgt, castMove d.2 rfl (moveOf d.1)⟩ : Σ βc, S.Move αc βc))
  moveOfT : ∀ {v : VLabel n} (d : TermData n C v),
    S.MoveT (toStepCells.symm ⟨d.s, d.α⟩) v
  moveOfT_bij : ∀ (αc : S.Cell) (v : VLabel n), Function.Bijective
    (fun d : {d : TermData n C v // toStepCells.symm ⟨d.s, d.α⟩ = αc} =>
      castMoveT d.2 (moveOfT d.1))
  DCellO : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m),
    (C.bd s).CellIdx → Type
  finDO : ∀ s m o α, Fintype (DCellO s m o α)
  cellOfA : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ (toStepCells.symm d.src))
    (h : Hpt (S.dim (moveOf d))),
    S.Assign (moveOf d) x h → DCellO d.s d.m d.o d.α
  cellOfAT : ∀ {v} (d : TermData n C v) {q₀}
    (x : S.Hist q₀ (toStepCells.symm ⟨d.s, d.α⟩))
    (h : Hpt (S.dimT (moveOfT d))),
    S.AssignT (moveOfT d) x h → DCellO d.s d.m d.o d.α
  emult : ∀ {s m o α}, DCellO s m o α → ℕ
  evtOf : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dim mv)), S.Assign mv x h → ∀ N : ℕ, Finset (Box q₀ N)
  evtOfT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dimT mv)), S.AssignT mv x h → ∀ N : ℕ, Finset (Box q₀ N)

/-- one assignment step from (αc, x) — a CLOSED DEF at REV 7 (C10). -/
def AStep {n} (S : StepSys n) (αc : S.Cell) {q₀} (x : S.Hist q₀ αc) : Type :=
  (Σ (β : S.Cell) (mv : S.Move αc β) (h : Hpt (S.dim mv)), S.Assign mv x h)
  ⊕ (Σ (v : VLabel n) (mv : S.MoveT αc v) (h : Hpt (S.dimT mv)),
      S.AssignT mv x h)

/-- the SOURCE-CELL digit-cell carrier at αc — the frozen `MeasuredSide.Cell`
shape at the instance (C10). -/
def CtsCells.CellOf {n C S} (W : CtsCells n C S) (αc : S.Cell) : Type :=
  (Σ d : {d : MoveData n C // W.toStepCells.symm d.src = αc},
     W.DCellO d.1.s d.1.m d.1.o d.1.α)
  ⊕ (Σ v : VLabel n,
     Σ d : {d : TermData n C v // W.toStepCells.symm ⟨d.s, d.α⟩ = αc},
     W.DCellO d.1.s d.1.m d.1.o d.1.α)

/-- ▸-transport wrapper along the invFun surjectivity identity (REV 8, N5). -/
noncomputable def castAssignKey {n C S} (W : CtsCells n C S)
    {αc β : S.Cell} {q₀} {x : S.Hist q₀ αc}
    (d : {d : MoveData n C // W.toStepCells.symm d.src = αc})
    (mv : S.Move αc β) (h : Hpt (S.dim mv)) (a : S.Assign mv x h)
    (hfd : (⟨W.toStepCells.symm d.1.tgt, castMove d.2 rfl (W.moveOf d.1)⟩ :
        Σ βc, S.Move αc βc) = ⟨β, mv⟩) :
    S.Assign (W.moveOf d.1) (d.2.symm ▸ x)
      (by cases d with | mk d hd => cases hd; cases hfd; exact h) := by
  cases d with | mk d hd => cases hd; cases hfd; exact a

/-- terminal twin of `castAssignKey`. -/
noncomputable def castAssignKeyT {n C S} (W : CtsCells n C S)
    {αc : S.Cell} {v : VLabel n} {q₀} {x : S.Hist q₀ αc}
    (d : {d : TermData n C v // W.toStepCells.symm ⟨d.s, d.α⟩ = αc})
    (mv : S.MoveT αc v) (h : Hpt (S.dimT mv)) (a : S.AssignT mv x h)
    (hfd : (castMoveT d.2 (W.moveOfT d.1) : S.MoveT αc v) = mv) :
    S.AssignT (W.moveOfT d.1) (d.2.symm ▸ x)
      (by cases d with | mk d hd => cases hd; cases hfd; exact h) := by
  cases d with | mk d hd => cases hd; cases hfd; exact a

/-- the step's digit-cell key: (classified cell, Σ-embedded height); transport
direction per REV 8 (N5). -/
noncomputable def CtsCells.stepKey {n C S} (W : CtsCells n C S)
    {αc : S.Cell} {q₀} {x : S.Hist q₀ αc} (p : AStep S αc x) :
    W.CellOf αc × Σ D : ℕ, Hpt D :=
  match p with
  | .inl ⟨β, mv, h, a⟩ =>
      let fwd := fun d : {d : MoveData n C // W.toStepCells.symm d.src = αc}
        => (⟨W.toStepCells.symm d.1.tgt, castMove d.2 rfl (W.moveOf d.1)⟩ :
            Σ βc, S.Move αc βc)
      haveI : Nonempty {d : MoveData n C // W.toStepCells.symm d.src = αc} :=
        ⟨((W.moveOf_bij αc).2 ⟨β, mv⟩).choose⟩
      let d := Function.invFun fwd ⟨β, mv⟩
      (Sum.inl ⟨d, W.cellOfA d.1 (d.2.symm ▸ x) _
          (castAssignKey W d mv h a
            (Function.invFun_eq ((W.moveOf_bij αc).2 ⟨β, mv⟩)))⟩,
       ⟨S.dim mv, h⟩)
  | .inr ⟨v, mv, h, a⟩ =>
      let fwdT := fun d : {d : TermData n C v //
          W.toStepCells.symm ⟨d.s, d.α⟩ = αc} => castMoveT d.2 (W.moveOfT d.1)
      haveI : Nonempty {d : TermData n C v //
          W.toStepCells.symm ⟨d.s, d.α⟩ = αc} :=
        ⟨((W.moveOfT_bij αc v).2 mv).choose⟩
      let d := Function.invFun fwdT mv
      (Sum.inr ⟨v, d, W.cellOfAT d.1 (d.2.symm ▸ x) _
          (castAssignKeyT W d mv h a
            (Function.invFun_eq ((W.moveOfT_bij αc v).2 mv)))⟩,
       ⟨S.dimT mv, h⟩)

/-- the step's event (unpacks to evtOf/evtOfT) — closed (C10). -/
def CtsCells.evtOfStep {n C S} (W : CtsCells n C S) {αc} {q₀}
    {x : S.Hist q₀ αc} (p : AStep S αc x) (N : ℕ) : Finset (W.Box q₀ N) :=
  match p with
  | .inl ⟨_, mv, h, a⟩ => W.evtOf mv x h a N
  | .inr ⟨_, mv, h, a⟩ => W.evtOfT mv x h a N

structure CtsMeasured (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    extends CtsCells n C S where
  -- THE DISJOINTNESS LAW — keyed to the DIGIT-CELL KEY (REV 4, Codex-3): [tie]
  evt_disj_cell : ∀ {αc q₀} (x : S.Hist q₀ αc) (p p' : AStep S αc x) (N : ℕ),
    toCtsCells.stepKey p ≠ toCtsCells.stepKey p' →
    Disjoint (toCtsCells.evtOfStep p N) (toCtsCells.evtOfStep p' N)
  -- THE PER-ASSIGNMENT COUNTING LAW (REV 3, F-3/Codex-10): [tie]
  stabLvl : ∀ {αc βc}, S.Move αc βc → ℕ
  stabLvlT : ∀ {αc v}, S.MoveT αc v → ℕ
  evt_card : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc) (h)
    (a : S.Assign mv x h), q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvl mv,
    ((evtOf mv x h a N).card : ℝ)
      = S.massOf mv x h a * ((@Fintype.card _ (finB q₀ N)) : ℝ)
  evt_cardT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc) (h)
    (a : S.AssignT mv x h), q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvlT mv,
    ((evtOfT mv x h a N).card : ℝ)
      = S.massOfT mv x h a * ((@Fintype.card _ (finB q₀ N)) : ℝ)
  -- WITHIN-CELL PER-ASSIGNMENT DISJOINTNESS — carrier [tie] (REV 7, C8):
  evt_disj_assign : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc)
    (h) (a a' : S.Assign mv x h), a ≠ a' →
    ∀ N, Disjoint (evtOf mv x h a N) (evtOf mv x h a' N)
  evt_disj_assignT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc)
    (h) (a a' : S.AssignT mv x h), a ≠ a' →
    ∀ N, Disjoint (evtOfT mv x h a N) (evtOfT mv x h a' N)
  -- listed height domains, AS DATA:
  cdom : ∀ (d : MoveData n C), DCellO d.s d.m d.o d.α → SemilinPart (S.dim (moveOf d))
  cdomT : ∀ {v} (d : TermData n C v), DCellO d.s d.m d.o d.α
    → SemilinPart (S.dimT (moveOfT d))
  mdom : ∀ (d : MoveData n C), SemilinPart (S.dim (moveOf d))
  mdomT : ∀ {v} (d : TermData n C v), SemilinPart (S.dimT (moveOfT d))
  -- activity:
  activeState : ℚ → S.Cell → Prop
  act_size : ∀ q₀ ∈ Pools, ∀ c : S.Cell, activeState q₀ c ↔
    ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀ ≠ 0
  -- THE STATE-INSTANCE CENSUS (REV 3, F-5/Codex-16):
  stLvl : S.Cell → ℕ
  stInst : S.Cell → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  stInst_card : ∀ (c : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ((stInst c q₀ (stLvl c)).card : ℚ)
      = ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀
  -- ENTRANCE SIDE, template×component-keyed (A-1):
  entDom : ∀ εT : EntTemplate n, SemilinPart εT.entDim
  entLands : EntTemplate n → S.Cell → Prop
  decLands : ∀ εT, DecidablePred (entLands εT)
  entEvt : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)
  entLvl : EntTemplate n → ℕ
  -- THE ε-INSTANCE CENSUS (REV 3, F-1/F-2/Codex-7):
  entInst : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)
  -- THE ENTRANCE COUNTING LAW, division-free (F-1): [tie]
  ent_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ∀ N ≥ (ε.template?).elim 0 entLvl,
    ((entEvt ε β₀ q₀ N).card : ℚ) * q₀ ^ (ε.A : ℕ)
      = ((entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl)).card : ℚ)
          * q₀ ^ (n * N)
  -- THE SELECTION-SEPARATION LAW (REV 7, Codex6-C1):
  ent_sel : ∀ (ε ε' : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ε.Phat = ε'.Phat → ε.gsel = ε'.gsel → ε.musel = ε'.musel →
    ε.selRec ≠ ε'.selRec →
    Disjoint (entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl))
      (entInst ε' β₀ q₀ ((ε.template?).elim 0 entLvl))
    -- [E-PHASE DEVIATION: the sibling census read at ε's OWN defining level
    --  (the blueprint's ε'-level literal was type-heterogeneous; siblings
    --  share P̂/(g,μ), so the template level is common by design)]
  -- THE CENSUS↔CUT IDENTIFICATION (REV 8, N3; REV 9, N-2 fiber tie):
  ent_cut : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    (entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl)).Nonempty →
    ∃ (p : ℕ) (hp : Fact p.Prime) (F : Type) (hf : Field F) (hfin : Finite F),
      ∃ (pol : @MovesD.CanonPolicy p hp F hf hfin) (m : ℕ)
        (Pr : @MovesD.Presented p hp F hf hfin n
          ((ε.template?).elim 0 entLvl) m pol ε.Phat),
        (Nat.card F : ℚ) = q₀ ∧
        Nonempty (@CutRealization n ε p F hp hf hfin pol
          ((ε.template?).elim 0 entLvl) m Pr _
          (entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl)))

section CtsMeasuredDefs
variable {n : ℕ} {C : CtsFamily n} {S : StepSys n}

/-- (XHD-d) ENTRANCE FACE's realizability predicate, DISPLAYED (C29;
declared here so the §2.F wrappers can read it — the §2.G reading-order
note honored). -/
def Realizable (V : CtsMeasured n C S) (ε : EntShapeV n)
    (β₀ : S.Cell) : Prop :=
  ∀ q₀ ∈ V.Pools, ∃ N₀, ∀ N ≥ N₀, (V.entEvt ε β₀ q₀ N).Nonempty

open Classical in
/-- fixed-height CELL events := the union of the cell's assignments' events. -/
noncomputable def CtsMeasured.cellEvt (V : CtsMeasured n C S)
    (d : MoveData n C) {q₀} (x : S.Hist q₀ (V.toStepCells.symm d.src))
    (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (N : ℕ) : Finset (V.Box q₀ N) :=
  letI := S.finA (V.moveOf d) x h
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).biUnion (fun a => V.evtOf (V.moveOf d) x h a N)

open Classical in
noncomputable def CtsMeasured.cellEvtT (V : CtsMeasured n C S) {v}
    (d : TermData n C v) {q₀} (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩))
    (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) (N : ℕ) : Finset (V.Box q₀ N) :=
  letI := S.finAT (V.moveOfT d) x h
  (Finset.univ.filter (fun a : S.AssignT (V.moveOfT d) x h =>
    V.cellOfAT d x h a = c)).biUnion (fun a => V.evtOfT (V.moveOfT d) x h a N)

open Classical in
/-- the cell-refined MARKED count T_c(h) from x at x's pool — again a def. -/
noncomputable def CtsMeasured.cntc (V : CtsMeasured n C S) (d : MoveData n C)
    {q₀} (x : S.Hist q₀ (V.toStepCells.symm d.src))
    (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) : ℕ :=
  letI := S.finA (V.moveOf d) x h
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).card

open Classical in
noncomputable def CtsMeasured.cntcT (V : CtsMeasured n C S) {v}
    (d : TermData n C v) {q₀} (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩))
    (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) : ℕ :=
  letI := S.finAT (V.moveOfT d) x h
  (Finset.univ.filter (fun a : S.AssignT (V.moveOfT d) x h =>
    V.cellOfAT d x h a = c)).card

end CtsMeasuredDefs

section MarkedCarrier
variable {n : ℕ} {C : CtsFamily n} {S : StepSys n}

/-- THE MARKED CARRIER's mark count (REV 8, Codex7 N4). -/
noncomputable def CtsMeasured.markCard (V : CtsMeasured n C S) {αc : S.Cell} {q₀}
    {x : S.Hist q₀ αc} (p : AStep S αc x) : ℕ :=
  match (V.toCtsCells.stepKey p).1 with
  | .inl ⟨_, c⟩ => V.emult c
  | .inr _ => 1

/-- a marked step = one AStep point with ONE eligible continuation mark adjoined. -/
def MStep (V : CtsMeasured n C S) (αc : S.Cell) {q₀}
    (x : S.Hist q₀ αc) : Type :=
  Σ p : AStep S αc x, Fin (V.markCard p)

/-- THE READING — a FUNCTION of the marked point ((iv)-MEAS). -/
noncomputable def CtsMeasured.mReading (V : CtsMeasured n C S) {αc : S.Cell} {q₀}
    {x : S.Hist q₀ αc} (mp : MStep V αc x) :
    (V.CellOf αc × Σ D : ℕ, Hpt D) × ℕ :=
  (V.toCtsCells.stepKey mp.1, (mp.2 : ℕ))

open Classical in
/-- the level-N MARKED event: the step's f-event TAGGED by its mark. -/
noncomputable def CtsMeasured.mEvt (V : CtsMeasured n C S) {αc : S.Cell} {q₀}
    {x : S.Hist q₀ αc} (mp : MStep V αc x) (N : ℕ) :
    Finset (V.Box q₀ N × ℕ) :=
  (V.toCtsCells.evtOfStep mp.1 N).image (fun b => (b, (mp.2 : ℕ)))

/-- THE ε-INSTANCE COUNT — a DEF (card of the census at the defining level). -/
noncomputable def CtsMeasured.entCensus (V : CtsMeasured n C S)
    (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  (V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)).card

/-- the REV-7 (C11) total consumption wrappers over `writeHeights?`. -/
noncomputable def CtsMeasured.instCensus (V : CtsMeasured n C S)
    (εT : EntTemplate n) (h : Hpt εT.entDim) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  ((writeHeights? εT h).map (fun ε => V.entCensus ε β₀ q₀)).getD 0
def CtsMeasured.instRealizable (V : CtsMeasured n C S) (εT : EntTemplate n)
    (h : Hpt εT.entDim) (β₀ : S.Cell) : Prop :=
  ∃ ε ∈ writeHeights? εT h, Realizable V ε β₀

/-- THE ENTRANCE INDEX (A-1's carrier). -/
def CtsMeasured.EntIx (V : CtsMeasured n C S) (β₀ : S.Cell) : Type :=
  {p : Σ εT : EntTemplate n, Fin (V.entDom εT).comps.length // V.entLands p.1 β₀}

/-- entrance count per EntIx member := the CENSUS at the component's base
instantiation (F-2/Codex-7). -/
noncomputable def CtsMeasured.entCount (V : CtsMeasured n C S) {β₀ : S.Cell}
    (i : V.EntIx β₀) (q₀ : ℚ) : ℕ :=
  V.instCensus i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base β₀ q₀

end MarkedCarrier

/-! ## §2.G Templates, the two-sided count architecture, XHD-d and XHD-s, the bundle,
HMC, and the COMP typing (V.1(iv)–(vi), V.4) -/

/-- A finite path template γ in block e (V.1(vi)), with the rev-4
TERMINAL-FINAL EXTENSION. -/
inductive Template (n : ℕ) (S : StepSys n) : S.Cell → Type
  | last  {α β} (m : S.Move α β)  : Template n S α
  | lastT {α v} (m : S.MoveT α v) : Template n S α
  | cons  {α β} (m : S.Move α β) (γ : Template n S β) : Template n S α

def Template.D {n S} : ∀ {α}, Template n S α → ℕ
  | _, .last m => S.dim m
  | _, .lastT m => S.dimT m
  | _, .cons m γ => S.dim m + γ.D

/-- THE TABLE-SIDE CHAIN COUNT T_γ(x, h) — A DEF, recursive by definition
(REV-4 SCOPE PER N-1: the TABLE side; H(γ) is process-side). -/
def chainCount {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α) {q₀}, S.Hist q₀ α → Hpt γ.D → ℕ
  | _, .last m,  _, x, h => S.cntraw m x h
  | _, .lastT m, _, x, h => S.cntrawT m x h
  | _, .cons m γ, _, x, h =>
      letI := S.finA m x (Hpt.take h)
      ∑ a : S.Assign m x (Hpt.take h),
        chainCount S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)

/-- THE CHAIN CARRIER (REV 8, Codex7 N1): the fresh-assignment chains from x
along γ at h. -/
def Chains {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α) {q₀}, S.Hist q₀ α → Hpt γ.D → Type
  | _, .last m,  _, x, h => S.Assign m x h
  | _, .lastT m, _, x, h => S.AssignT m x h
  | _, .cons m γ, _, x, h =>
      Σ a : S.Assign m x (Hpt.take h),
        Chains S γ (S.ext m x (Hpt.take h) a) (Hpt.drop h)

/-- THE PROCESS-SIDE MARKED-EVENT CARRIER (REV 4, N-1; mark facts typed at
REV 7 (C6) and REV 8 (N1)). -/
structure TmplEvents (n : ℕ) (S : StepSys n) where
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  tevt : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α),
    Hpt γ.D → ∀ N : ℕ, Finset (Box q₀ N)
  tinst : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α),
    Hpt γ.D → ∀ N : ℕ, Finset (Box q₀ N)
  tmplLvl : ∀ {α}, Template n S α → ℕ
  -- THE LENGTH-1 TIE [tie]:
  tevt_last_iff : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    ((∃ N₀, ∀ N ≥ N₀, (tevt (.last m) x h N).Nonempty) ↔ 0 < S.cntraw m x h)
  tevt_lastT_iff : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    ((∃ N₀, ∀ N ≥ N₀, (tevt (.lastT m) x h N).Nonempty) ↔ 0 < S.cntrawT m x h)
  -- THE MARK FACTS [tie]:
  real_marks : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x → (∃ N₀, ∀ N ≥ N₀, (tevt γ x h N).Nonempty) →
    0 < (tinst γ x h (tmplLvl γ)).card
  tmark : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    {b // b ∈ tinst γ x h (tmplLvl γ)} → Chains S γ x h
  tmark_inj : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x → Function.Injective (tmark γ x h)
  tmark_last_surj : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    Function.Surjective (tmark (.last m) x h)
  tmark_lastT_surj : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    Function.Surjective (tmark (.lastT m) x h)
  marks_realize : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x → 0 < (tinst γ x h (tmplLvl γ)).card →
    ∃ N₀, ∀ N ≥ N₀, (tevt γ x h N).Nonempty

/-- THE NOTE'S OWN T_γ — the MARK CENSUS CARD at the defining level (REV 7, C6). -/
def Tgam {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) : ℕ :=
  (TE.tinst γ x h (TE.tmplLvl γ)).card

/-- realization of a CHAIN — definitional through the mark reading. -/
def RealizesC {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) (c : Chains S γ x h) : Prop :=
  ∃ b, TE.tmark γ x h b = c

/-- PROCESS REALIZATION — DERIVED notion (REV 7, C6). -/
def TReal {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) : Prop :=
  ∃ N₀, ∀ N ≥ N₀, (TE.tevt γ x h N).Nonempty

/-- (XHD-d) DOMAINS, typed — RE-KEYED at REV 7 (C6) at the note's own
T_γ = `Tgam`.  Owner [2b]. -/
structure XHDd (n : ℕ) (S : StepSys n) (TE : TmplEvents n S) where
  dom : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  no_orphan : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → 0 < Tgam TE γ x h → (dom γ).Mem h
  no_stray : ∀ {α} (γ : Template n S α) (h : Hpt γ.D),
    (dom γ).Mem h → ∀ {q₀}, q₀ ∈ S.Pools → ∀ x : S.Hist q₀ α, S.zc x →
    0 < Tgam TE γ x h

/-- THE mdom COHERENCE TIE (REV 4, Codex-5). -/
structure MDomTie {n} {S : StepSys n} {C : CtsFamily n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) (D : XHDd n S TE) : Prop where
  mdom_eq : ∀ (d : MoveData n C), D.dom (.last (V.moveOf d)) = V.mdom d
  mdomT_eq : ∀ {v} (d : TermData n C v), D.dom (.lastT (V.moveOfT d)) = V.mdomT d

/-- ∏ᵢ g_i(h_i): the fixed-height template weight (TABLE side). -/
noncomputable def gProd {n S} (W : XHDw n S) :
    ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ
  | _, .last m,  h, q₀ => (q₀ : ℝ) ^ (-((W.E m).eval h : ℤ))
  | _, .lastT m, h, q₀ => (q₀ : ℝ) ^ (-((W.ET m).eval h : ℤ))
  | _, .cons m γ, h, q₀ =>
      (q₀ : ℝ) ^ (-((W.E m).eval (Hpt.take h) : ℤ)) * gProd W γ (Hpt.drop h) q₀

/-- (XHD-s) SUMS, template face, typed.  Owner [2b]. -/
structure XHDs (n : ℕ) (S : StepSys n) (W : XHDw n S) {TE : TmplEvents n S}
    (D : XHDd n S TE) where
  Gc : ∀ {α} (γ : Template n S α), Fin (D.dom γ).comps.length → Qq
  Gc_denom : ∀ {α} (γ : Template n S α) (j), ∃ (b : ℕ) (as : Finset ℕ+),
    (Gc γ j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))
  Gc_ok : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
    Gc γ j ∈ OKat q₀
  Gc_hasSum : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((D.dom γ).comps.get j).Mem h} =>
        gProd W γ h.1 q₀)
      ((evalAt q₀ ⟨Gc γ j, Gc_ok γ j q₀ hq⟩ : ℚ) : ℝ)

/-- THE CELL D-FACE (REV 3, F-3).  Owner [2b]. -/
structure XHDdC (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  no_orphanC : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ (V.toStepCells.symm d.src))
    (c : V.DCellO d.s d.m d.o d.α) (h : Hpt (S.dim (V.moveOf d))),
    q₀ ∈ V.Pools → S.zc x → 0 < V.cntc d x c h → (V.cdom d c).Mem h
  no_strayC : ∀ (d : MoveData n C) (c) (h), (V.cdom d c).Mem h →
    ∀ {q₀}, q₀ ∈ V.Pools → ∀ x : S.Hist q₀ (V.toStepCells.symm d.src),
    S.zc x → 0 < V.cntc d x c h
  no_orphanCT : ∀ {v} (d : TermData n C v) {q₀}
    (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩)) (c) (h),
    q₀ ∈ V.Pools → S.zc x → 0 < V.cntcT d x c h → (V.cdomT d c).Mem h
  no_strayCT : ∀ {v} (d : TermData n C v) (c) (h), (V.cdomT d c).Mem h →
    ∀ {q₀}, q₀ ∈ V.Pools → ∀ x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩),
    S.zc x → 0 < V.cntcT d x c h

/-- (XHD-s) CELL FACE — WEIGHT-ONLY at REV 3 (F-4/Codex-9).  Owner [2b]. -/
structure XHDsC (n : ℕ) (S : StepSys n) (W : XHDw n S) {TE : TmplEvents n S}
    (D : XHDd n S TE) {C : CtsFamily n} (V : CtsMeasured n C S)
    (Xs : XHDs n S W D) where
  Gcell : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length), Qq
  Gcell_denom : ∀ d c j, ∃ (b : ℕ) (as : Finset ℕ+),
    (Gcell d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gcell_ok : ∀ d c j (q₀ : ℚ), q₀ ∈ S.Pools → Gcell d c j ∈ OKat q₀
  Gcell_hasSum : ∀ (d) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
        W.g (V.moveOf d) h.1 q₀)
      ((evalAt q₀ ⟨Gcell d c j, Gcell_ok d c j q₀ hq⟩ : ℚ) : ℝ)
  GcellT : ∀ {v} (d : TermData n C v) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdomT d c).comps.length), Qq
  GcellT_denom : ∀ {v} (d : TermData n C v) (c) (j), ∃ (b : ℕ) (as : Finset ℕ+),
    (GcellT d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  GcellT_ok : ∀ {v} (d : TermData n C v) (c) (j) (q₀ : ℚ),
    q₀ ∈ S.Pools → GcellT d c j ∈ OKat q₀
  GcellT_hasSum : ∀ {v} (d : TermData n C v) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdomT d c).comps.get j).Mem h} =>
        (q₀ : ℝ) ^ (-((W.ET (V.moveOfT d)).eval h.1 : ℤ)))
      ((evalAt q₀ ⟨GcellT d c j, GcellT_ok d c j q₀ hq⟩ : ℚ) : ℝ)

/-- (XHD-s) ENTRANCE FACE — WEIGHT-ONLY at REV 3 (Codex-8).  Owner [2b]. -/
structure XHDsEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  Gent : ∀ (β₀ : S.Cell) (i : V.EntIx β₀), Qq
  Gent_denom : ∀ β₀ i, ∃ (b : ℕ) (as : Finset ℕ+),
    (Gent β₀ i).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gent_ok : ∀ β₀ i (q₀ : ℚ), q₀ ∈ V.Pools → Gent β₀ i ∈ OKat q₀
  Gent_hasSum : ∀ β₀ (i : V.EntIx β₀) (q₀) (hq : q₀ ∈ V.Pools),
    HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        (q₀ : ℝ) ^ (-((instA i.1.1 h.1 : ℕ) : ℤ)))
      ((evalAt q₀ ⟨Gent β₀ i, Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)

/-- (XHD-d) ENTRANCE FACE (REV 3 landing law; REV 7, C11 wrappers).
Owner [2b]. -/
structure XHDdEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  no_orphanE : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim) (β₀ : S.Cell),
    V.instRealizable εT h β₀ → (V.entDom εT).Mem h
  no_strayE : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim) (β₀ : S.Cell),
    V.entLands εT β₀ → (V.entDom εT).Mem h → V.instRealizable εT h β₀
  lands_of_realizable : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim) (β₀ : S.Cell),
    V.instRealizable εT h β₀ → V.entLands εT β₀

/-- the per-instantiation ℝ-valued entrance mass — RE-KEYED at REV 3 (F-1):
ιshH := CENSUS · q^{−A}.  Gate check: 2·2⁻³ = 1/4; (1/4)·512 = 128. -/
noncomputable def ιshH {n C S} (V : CtsMeasured n C S) (εT : EntTemplate n)
    (h : Hpt εT.entDim) (β₀ : S.Cell) (q₀ : ℚ) : ℝ :=
  (V.instCensus εT h β₀ q₀ : ℝ)
    * (q₀ : ℝ) ^ (-((instA εT h : ℕ) : ℤ))

/-- THE XHD PACKAGE (V.0), one record — DECLARED AFTER ITS COMPONENTS (C4). -/
structure XHD (n : ℕ) (S : StepSys n) (TE : TmplEvents n S)
    {C : CtsFamily n} (V : CtsMeasured n C S) where
  w : XHDw n S
  u : XHDu n S
  d : XHDd n S TE
  dC : XHDdC n S V
  s : XHDs n S w d
  sC : XHDsC n S w d V s
  sEnt : XHDsEnt n S V
  dEnt : XHDdEnt n S V

/-- (v) HMC — THE OPEN KERNEL (MOVES 8198–8204): membership-factorization of
the LISTED presentation of the process-side domain.  NEVER proved in this
corpus; consumed by (COMP-Σ)/V5-5 and V4-12(a). -/
def HMC {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) (D : XHDd n S TE) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (h₁ : Hpt (S.dim m))
    (h₂ : Hpt γ.D),
    (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂

/-! ## §2.G (cont.) — (HMC-AUG)'s refinement carrier.
E-PHASE RESTRUCTURING (recorded): the blueprint's one `Refinement` record is
split into `RefinementCore` (data + projection laws) + `Refinement extends
RefinementCore` (the two partition covers), so the cover Σ-domains/functions
are CLOSED defs (`CoverDom`/`coverFn` and twins) — the blueprint's inline
`castHpt m'.2 (dim_eq m'.1) h` pseudo-display is realized by the displayed
`coverDim` equality chain; `▸`-transports are uniformly the named `cast*`
wrappers (motive-safe); `histFib_proj`/`histFib_complete` take the
blueprint-sanctioned cast/∃-forms.  Zero design content changed. -/

theorem dim_castMove {n} {S : StepSys n} {α α' β β' : S.Cell}
    (hα : α = α') (hβ : β = β') (m : S.Move α β) :
    S.dim (castMove hα hβ m) = S.dim m := by cases hα; cases hβ; rfl

theorem dimT_castMoveT {n} {S : StepSys n} {α α' : S.Cell} {v : VLabel n}
    (hα : α = α') (m : S.MoveT α v) :
    S.dimT (castMoveT hα m) = S.dimT m := by cases hα; rfl

theorem castHpt_eq_cast {D D' : ℕ} (h : D = D') (x : Hpt D) :
    castHpt h x = cast (congrArg Hpt h) x := by cases h; rfl

theorem castHpt_trans {D₁ D₂ D₃ : ℕ} (e1 : D₁ = D₂) (e2 : D₂ = D₃)
    (x : Hpt D₁) : castHpt e2 (castHpt e1 x) = castHpt (e1.trans e2) x := by
  cases e1; cases e2; rfl

theorem castHpt_self {D : ℕ} (e : D = D) (x : Hpt D) : castHpt e x = x := by
  rw [castHpt_eq_cast]; exact cast_eq _ x

/-- height-congruence transport on assignment fibers (mechanical). -/
def assign_congrHpt {n} {S : StepSys n} {α β : S.Cell} (m : S.Move α β) {q₀}
    (x : S.Hist q₀ α) {h h' : Hpt (S.dim m)} (e : h = h')
    (a : S.Assign m x h) : S.Assign m x h' := e ▸ a
def assignT_congrHpt {n} {S : StepSys n} {α : S.Cell} {v : VLabel n}
    (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) {h h' : Hpt (S.dimT m)}
    (e : h = h') (a : S.AssignT m x h) : S.AssignT m x h' := e ▸ a

structure RefinementCore (n : ℕ) (S : StepSys n) where
  B : S.Cell → Type
  finB : ∀ α, Fintype (B α)
  S' : StepSys n
  cellEq : S'.Cell ≃ Σ α : S.Cell, B α
  histOf : ∀ (α' : S'.Cell) {q₀}, S'.Hist q₀ α' → S.Hist q₀ (cellEq α').1
  histFib : ∀ {α : S.Cell} {q₀} (x : S.Hist q₀ α),
    Finset (Σ b : B α, S'.Hist q₀ (cellEq.symm ⟨α, b⟩))
  histFib_proj : ∀ {α : S.Cell} {q₀} (x : S.Hist q₀ α)
    (p : Σ b : B α, S'.Hist q₀ (cellEq.symm ⟨α, b⟩)), p ∈ histFib x →
    cast (congrArg (S.Hist q₀)
        (congrArg Sigma.fst (cellEq.apply_symm_apply ⟨α, p.1⟩)))
      (histOf (cellEq.symm ⟨α, p.1⟩) p.2) = x
  histFib_complete : ∀ (α' : S'.Cell) {q₀} (x' : S'.Hist q₀ α'),
    ∃ p ∈ histFib (histOf α' x'), p.1 = (cellEq α').2 ∧ HEq p.2 x'
  moveProj : ∀ {α' β'}, S'.Move α' β' → S.Move (cellEq α').1 (cellEq β').1
  dim_eq : ∀ {α' β'} (m' : S'.Move α' β'), S'.dim m' = S.dim (moveProj m')
  assignOf : ∀ {α' β'} (m' : S'.Move α' β') {q₀} (x' : S'.Hist q₀ α')
    (h : Hpt (S'.dim m')),
    S'.Assign m' x' h
      → S.Assign (moveProj m') (histOf α' x') (castHpt (dim_eq m') h)
  mass_eq : ∀ {α' β'} (m' : S'.Move α' β') {q₀} (x' : S'.Hist q₀ α') (h) (a'),
    S'.massOf m' x' h a'
      = S.massOf (moveProj m') (histOf α' x') (castHpt (dim_eq m') h)
          (assignOf m' x' h a')
  moveProjT : ∀ {α'} {v : VLabel n}, S'.MoveT α' v → S.MoveT (cellEq α').1 v
  dimT_eq : ∀ {α' v} (m' : S'.MoveT α' v), S'.dimT m' = S.dimT (moveProjT m')
  assignOfT : ∀ {α' v} (m' : S'.MoveT α' v) {q₀} (x' : S'.Hist q₀ α')
    (h : Hpt (S'.dimT m')),
    S'.AssignT m' x' h
      → S.AssignT (moveProjT m') (histOf α' x') (castHpt (dimT_eq m') h)
  massT_eq : ∀ {α' v} (m' : S'.MoveT α' v) {q₀} (x' : S'.Hist q₀ α') (h) (a'),
    S'.massOfT m' x' h a'
      = S.massOfT (moveProjT m') (histOf α' x') (castHpt (dimT_eq m') h)
          (assignOfT m' x' h a')

namespace RefinementCore
variable {n : ℕ} {S : StepSys n}

theorem coverDim (R : RefinementCore n S)
    {α β : S.Cell} {m : S.Move α β} {α' : R.S'.Cell}
    (hα : (R.cellEq α').1 = α) {β' : R.S'.Cell} (hβ : (R.cellEq β').1 = β)
    {m' : R.S'.Move α' β'} (hm : castMove hα hβ (R.moveProj m') = m) :
    S.dim m = R.S'.dim m' := by
  subst hm; rw [dim_castMove]; exact (R.dim_eq m').symm

theorem coverDimT (R : RefinementCore n S)
    {α : S.Cell} {v : VLabel n} {m : S.MoveT α v} {α' : R.S'.Cell}
    (hα : (R.cellEq α').1 = α) {m' : R.S'.MoveT α' v}
    (hm : castMoveT hα (R.moveProjT m') = m) :
    S.dimT m = R.S'.dimT m' := by
  subst hm; rw [dimT_castMoveT]; exact (R.dimT_eq m').symm

/-- the assign_cover Σ-domain, CLOSED (the refined data over one coarse step). -/
def CoverDom (R : RefinementCore n S) {α β : S.Cell} (m : S.Move α β)
    (α' : R.S'.Cell) (hα : (R.cellEq α').1 = α) {q₀} (x' : R.S'.Hist q₀ α')
    (h : Hpt (S.dim m)) : Type :=
  Σ' (β' : R.S'.Cell) (hβ : (R.cellEq β').1 = β)
    (m' : R.S'.Move α' β') (hm : castMove hα hβ (R.moveProj m') = m),
    R.S'.Assign m' x' (castHpt (R.coverDim hα hβ hm) h)

/-- the cover map into the coarse fiber. -/
noncomputable def coverFn (R : RefinementCore n S) {α β : S.Cell}
    (m : S.Move α β) (α' : R.S'.Cell) (hα : (R.cellEq α').1 = α) {q₀}
    (x' : R.S'.Hist q₀ α') (h : Hpt (S.dim m))
    (p : R.CoverDom m α' hα x' h) :
    S.Assign m (cast (congrArg (S.Hist q₀) hα) (R.histOf α' x')) h := by
  obtain ⟨β', hβ, m', hm, a'⟩ := p
  have a2 := R.assignOf m' x' _ a'
  subst hm; cases hα; cases hβ
  rw [castHpt_trans] at a2
  exact assign_congrHpt _ _ (castHpt_self _ _) a2

/-- the terminal cover Σ-domain. -/
def CoverDomT (R : RefinementCore n S) {α : S.Cell} {v : VLabel n}
    (m : S.MoveT α v) (α' : R.S'.Cell) (hα : (R.cellEq α').1 = α) {q₀}
    (x' : R.S'.Hist q₀ α') (h : Hpt (S.dimT m)) : Type :=
  Σ' (m' : R.S'.MoveT α' v) (hm : castMoveT hα (R.moveProjT m') = m),
    R.S'.AssignT m' x' (castHpt (R.coverDimT hα hm) h)

noncomputable def coverFnT (R : RefinementCore n S) {α : S.Cell} {v : VLabel n}
    (m : S.MoveT α v) (α' : R.S'.Cell) (hα : (R.cellEq α').1 = α) {q₀}
    (x' : R.S'.Hist q₀ α') (h : Hpt (S.dimT m))
    (p : R.CoverDomT m α' hα x' h) :
    S.AssignT m (cast (congrArg (S.Hist q₀) hα) (R.histOf α' x')) h := by
  obtain ⟨m', hm, a'⟩ := p
  have a2 := R.assignOfT m' x' _ a'
  subst hm; cases hα
  rw [castHpt_trans] at a2
  exact assignT_congrHpt _ _ (castHpt_self _ _) a2

end RefinementCore

/-- (HMC-AUG)'s refinement carrier — FULLY TYPED (REV 3, Codex-13; REV 8, N2
histFib; the cover laws through the CLOSED CoverDom/coverFn defs above). -/
structure Refinement (n : ℕ) (S : StepSys n) extends RefinementCore n S where
  assign_cover : ∀ {α β} (m : S.Move α β) (α' : S'.Cell)
    (hα : (cellEq α').1 = α) {q₀} (x' : S'.Hist q₀ α') (h : Hpt (S.dim m)),
    Function.Bijective (toRefinementCore.coverFn m α' hα x' h)
  assign_coverT : ∀ {α v} (m : S.MoveT α v) (α' : S'.Cell)
    (hα : (cellEq α').1 = α) {q₀} (x' : S'.Hist q₀ α') (h : Hpt (S.dimT m)),
    Function.Bijective (toRefinementCore.coverFnT m α' hα x' h)

open Classical in
/-- the refined-template roster over a coarse template (REV 5, M-2's carrier). -/
noncomputable def refTmpls {n} {S : StepSys n} (R : RefinementCore n S) :
    ∀ (α' : R.S'.Cell) {α}, (R.cellEq α').1 = α →
    ∀ γ : Template n S α, List (Σ' γ' : Template n R.S' α', γ'.D = γ.D)
  | α', α, hα, .last (β := β) m =>
      letI := R.S'.finC
      letI := fun β' => R.S'.finM α' β'
      (Finset.univ (α := Σ β', R.S'.Move α' β')).toList.filterMap fun p =>
        if h : ∃ hβ : (R.cellEq p.1).1 = β,
            castMove hα hβ (R.moveProj p.2) = m
        then some ⟨.last p.2, by
          obtain ⟨hβ, hm⟩ := h
          subst hm
          show R.S'.dim p.2 = S.dim (castMove hα hβ (R.moveProj p.2))
          rw [dim_castMove]; exact R.dim_eq p.2⟩
        else none
  | α', α, hα, .lastT (v := v) m =>
      letI := R.S'.finMT α' v
      (Finset.univ (α := R.S'.MoveT α' v)).toList.filterMap fun m' =>
        if h : castMoveT hα (R.moveProjT m') = m
        then some ⟨.lastT m', by
          subst h
          show R.S'.dimT m' = S.dimT (castMoveT hα (R.moveProjT m'))
          rw [dimT_castMoveT]; exact R.dimT_eq m'⟩
        else none
  | α', α, hα, .cons (β := β) m γ =>
      letI := R.S'.finC
      letI := fun β' => R.S'.finM α' β'
      ((Finset.univ (α := Σ β', R.S'.Move α' β')).toList.filterMap fun p =>
        if h : ∃ hβ : (R.cellEq p.1).1 = β,
            castMove hα hβ (R.moveProj p.2) = m
        then some (⟨p, h⟩ : Σ' p : (Σ β', R.S'.Move α' β'),
          ∃ hβ : (R.cellEq p.1).1 = β, castMove hα hβ (R.moveProj p.2) = m)
        else none).flatMap fun ph =>
          (refTmpls R ph.1.1 ph.2.choose γ).map fun q =>
            ⟨.cons ph.1.2 q.1, by
              show R.S'.dim ph.1.2 + q.1.D = S.dim m + γ.D
              have hd : R.S'.dim ph.1.2 = S.dim m := by
                clear q
                obtain ⟨⟨β', m'⟩, hβ, hm⟩ := ph
                show R.S'.dim m' = S.dim m
                rw [← hm, dim_castMove]
                exact R.dim_eq m'
              have hq := q.2
              omega⟩

open Classical in
/-- THE REFINED-EVENT TRANSPORT (REV 5, M-2; fiber-union covers REV 8, N2;
projection identities inlined REV 9). -/
structure RefEvents {n : ℕ} {S : StepSys n} (R : Refinement n S)
    (TE : TmplEvents n S) where
  TE' : TmplEvents n R.S'
  boxEq : ∀ q₀ N, TE'.Box q₀ N ≃ TE.Box q₀ N
  tevt_cover : ∀ {α : S.Cell} {q₀} (x : S.Hist q₀ α)
    (γ : Template n S α) (h : Hpt γ.D) (N : ℕ), q₀ ∈ S.Pools →
    TE.tevt γ x h N
      = ((R.histFib x).toList.flatMap (fun p =>
          (refTmpls R.toRefinementCore (R.cellEq.symm ⟨α, p.1⟩)
            (congrArg Sigma.fst (R.cellEq.apply_symm_apply ⟨α, p.1⟩))
            γ).map (fun q =>
            (TE'.tevt q.1 p.2 (castHpt q.2.symm h) N).image (boxEq q₀ N)))
        ).foldr (· ∪ ·) ∅
  tinst_cover : ∀ {α : S.Cell} {q₀} (x : S.Hist q₀ α)
    (γ : Template n S α) (h : Hpt γ.D), q₀ ∈ S.Pools →
    (TE.tinst γ x h (TE.tmplLvl γ)).card
      = ((R.histFib x).toList.flatMap (fun p =>
          (refTmpls R.toRefinementCore (R.cellEq.symm ⟨α, p.1⟩)
            (congrArg Sigma.fst (R.cellEq.apply_symm_apply ⟨α, p.1⟩))
            γ).map (fun q =>
            (TE'.tinst q.1 p.2 (castHpt q.2.symm h)
              (TE'.tmplLvl q.1)).card))
        ).sum

/-- (HMC-AUG) — TE a PARAMETER (REV 5, M-2); satisfiable via V4-13; the REV-9
separation record and the forcing chain live at the blueprint §2.G record;
consumed by nothing, assumed nowhere. -/
def HMCAug {n : ℕ} (S : StepSys n) (TE : TmplEvents n S) : Prop :=
  ∃ (R : Refinement n S) (RE : RefEvents R TE)
    (D' : XHDd n R.S' RE.TE'), HMC RE.TE' D'

/-- (ENT-U)'s affine-A face (M4a), DISPLAYED (C29). -/
structure AffEnt (n : ℕ) where
  AE : ∀ εT : EntTemplate n, AffineE εT.entDim
  A_eq : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim),
    instA εT h = (AE εT).eval h

/-- (iv)-REP's per-species proviso, DISPLAYED (C29). -/
def ObsCheck {n : ℕ} {s : Skeleton n} (B : BlockData n s) : Prop :=
  ∀ (m : B.Letter) (q₀ : ℚ) (x x' : B.Carrier q₀),
    (∀ g, (B.gen g).part q₀ x = (B.gen g).part q₀ x') →
    B.evalObs m q₀ x = B.evalObs m q₀ x'

/-- cofinite activity (V7-5 leg (c)'s premise carrier, DISPLAYED — C29). -/
def CofinAct {n C S} (V : CtsMeasured n C S) : Prop :=
  ∀ c : S.Cell, {q₀ ∈ V.Pools | ¬ V.activeState q₀ c}.Finite

/-! ## §2.H The J tables ((J-RAT)/CL-18's carrier) — ROUTE-keyed (F-6).
Declaration order per the blueprint's own note: RouteTag → JCells →
CellPolyPack → μcellVal/Jval (CellPolyPack precedes its consumers). -/

/-- the (K-SUB) route classification of an outcome — the (m, c) row datum. -/
inductive RouteTag | kcol | split | term
  deriving DecidableEq

/-- THE J-CELL ROSTER — RE-KEYED at REV 3 (F-6); carrier read through
`C.bd s` (REV 9, N-6). -/
structure JCells (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  route : ∀ (s : Skeleton n) (m : (C.bd s).Letter), (C.bd s).Outc m → RouteTag
  route_cont : ∀ (s) (m) (o : (C.bd s).Outc m),
    route s m o = .split → (C.bd s).cont m o
  bcells : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m)
    (α : (C.bd s).CellIdx), Finset (V.DCellO s m o α)
  roster_tie : ∀ s m o α (c : V.DCellO s m o α),
    c ∈ bcells s m o α ↔ route s m o = .split

/-- the per-cell count-polynomial pack ((J-RAT)'s [1v] face) — CLOSED at REV 3. -/
structure CellPolyPack (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  P : ∀ (s) (m) (o : (C.bd s).Outc m) (α), V.DCellO s m o α → Polynomial ℚ
  deg : ∀ s m o α c, (P s m o α c).natDegree ≤ C.Wloc s m
  count : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    {q₀} (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x),
    q₀ ∈ V.Pools → ∀ h, (V.cdom d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntc d x c h
  countT : ∀ {v} (d : TermData n C v) (c : V.DCellO d.s d.m d.o d.α)
    {q₀} (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩)) (hzc : S.zc x),
    q₀ ∈ V.Pools → ∀ h, (V.cdomT d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntcT d x c h

open Classical in
/-- the per-cell conditional mass value — a CLOSED def at REV 8 (Codex7 N7). -/
noncomputable def μcellVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (cp : CellPolyPack n C S V) (XsC : XHDsC n S W D V Xs)
    (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α) (q₀ : ℚ) : ℝ :=
  if hq : q₀ ∈ S.Pools then
    (((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
      * ∑ j, ((evalAt q₀ ⟨XsC.Gcell d c j, XsC.Gcell_ok d c j q₀ hq⟩ : ℚ) : ℝ)
  else 0

/-- J_{τ,o}(q₀) as a MEASURED value: Σ over ALL cells of the split-route
(τ, o), EACH ONCE (F-6). -/
noncomputable def Jval {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (cp : CellPolyPack n C S V)
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C) (q₀ : ℚ) : ℝ :=
  ∑ c ∈ J.bcells d.s d.m d.o d.α, μcellVal cp XsC d c q₀

/-! the SUMMED-DENOMINATOR CLOSURE — ONE HOME (REV 9, N-4); the §8-listed
Defs-local obligation, PROVED here. -/

private theorem geomClass_ne_zero (b : ℕ) (as : Finset ℕ+) :
    (Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) : Polynomial ℚ) ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have hc : (1 - Polynomial.X ^ (a : ℕ) : Polynomial ℚ).coeff (a : ℕ) = 0 := by
    rw [h]; simp
  rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  simp at hc

private theorem geomClass_dvd_of_le {b b' : ℕ} {as as' : Finset ℕ+}
    (hb : b ≤ b') (hs : as ⊆ as') :
    (Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) : Polynomial ℚ)
      ∣ Polynomial.X ^ b' * ∏ a ∈ as', (1 - Polynomial.X ^ (a : ℕ)) :=
  mul_dvd_mul (pow_dvd_pow _ hb) (Finset.prod_dvd_prod_of_subset _ _ _ hs)

private theorem denom_dvd_of_add {x y : Qq} {L : Polynomial ℚ} (hL : L ≠ 0)
    (hx : x.denom ∣ L) (hy : y.denom ∣ L) : (x + y).denom ∣ L := by
  obtain ⟨px, hpx⟩ := (RatFunc.denom_dvd hL).mp hx
  obtain ⟨py, hpy⟩ := (RatFunc.denom_dvd hL).mp hy
  exact (RatFunc.denom_dvd hL).mpr
    ⟨px + py, by rw [hpx, hpy, map_add]; ring⟩

private theorem denom_sum_dvd {ι : Type*} {L : Polynomial ℚ} (hL : L ≠ 0) :
    ∀ (s : Finset ι) (f : ι → Qq), (∀ i ∈ s, (f i).denom ∣ L) →
    (∑ i ∈ s, f i).denom ∣ L := by
  classical
  intro s
  induction s using Finset.cons_induction with
  | empty => intro f _; simp
  | cons a s ha ih =>
      intro f hf
      rw [Finset.sum_cons]
      exact denom_dvd_of_add hL (hf a (Finset.mem_cons_self a s))
        (ih f fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))

theorem gcell_denom_sum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) :
    ∃ (b : ℕ) (as : Finset ℕ+),
      (∑ j, XsC.Gcell d c j).denom
        ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) := by
  classical
  refine ⟨Finset.univ.sup (fun j : Fin (V.cdom d c).comps.length =>
      (XsC.Gcell_denom d c j).choose),
    Finset.univ.biUnion (fun j : Fin (V.cdom d c).comps.length =>
      (XsC.Gcell_denom d c j).choose_spec.choose),
    denom_sum_dvd (geomClass_ne_zero _ _) _ _ (fun j _ => ?_)⟩
  exact dvd_trans (XsC.Gcell_denom d c j).choose_spec.choose_spec
    (geomClass_dvd_of_le
      (Finset.le_sup (f := fun j : Fin (V.cdom d c).comps.length =>
        (XsC.Gcell_denom d c j).choose) (Finset.mem_univ j))
      (Finset.subset_biUnion_of_mem
        (fun j : Fin (V.cdom d c).comps.length =>
          (XsC.Gcell_denom d c j).choose_spec.choose) (Finset.mem_univ j)))

open Classical in
/-- the PSigma witness `gcell_denom_sum`'s choose packages (REV 9, N-4). -/
noncomputable def gcellDenom {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) :
    Σ' (b : ℕ) (as : Finset ℕ+),
      (∑ j, XsC.Gcell d c j).denom
        ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) :=
  ⟨(gcell_denom_sum XsC d c).choose,
   (gcell_denom_sum XsC d c).choose_spec.choose,
   (gcell_denom_sum XsC d c).choose_spec.choose_spec⟩

/-- the per-cell PolyGeom — a CLOSED def at REV 8 (Codex7 N7), checked
field-for-field against the BUILT `MovesS.PolyGeom`. -/
noncomputable def jcellPG {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (cp : CellPolyPack n C S V) (XsC : XHDsC n S W D V Xs)
    (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α) : MovesS.PolyGeom :=
  { countT := cp.P d.s d.m d.o d.α c
    degBoundT := C.Wloc d.s d.m
    degT_le := cp.deg d.s d.m d.o d.α c
    countS := 1
    degBoundS := 0
    degS_le := by simp
    geom := ∑ j, XsC.Gcell d c j
    qpow := (gcellDenom XsC d c).1
    geomDenoms := (gcellDenom XsC d c).2.1
    geom_denom_dvd := (gcellDenom XsC d c).2.2 }

end LeanUrat.MovesV
