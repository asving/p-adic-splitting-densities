/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# MovesU/Defs — shared vocabulary for §U-SQUEEZE (Theorem U, conditional form)

E-phase transcription of `lean/notes/MOVESU_LEAN_BLUEPRINT_2026-07-28.md` §2 (rev 7,
dual-accepted). NO ledger in this file — the D11 three-file order (Defs ← U0b ←
DefsLedger) is load-bearing (the rev-3 circularity fix: the ledger's `∑ σ` needs U0b's
`Fintype (SplittingType n)`). Every structure field is a trust surface for the Codex
semantic audit (blueprint §4). The hypothesis structures are owner-instantiated later
(D9: `ClassifierSpec`/`FiberSeries` ← MovesD/HC-2/[3t], `SolveData`/`RegData` ← MovesS,
`MenuData` ← [2a]/[1v]); nothing here asserts mathematics — this file fixes the
vocabulary Theorem U's conditional statement is typed in.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology ENNReal Polynomial

/-- A splitting type of degree n: "a multiset of pairs (e_i, f_i) with Σ e_i·f_i = n"
    (SQ.4, verbatim; entries ≥ 1). CONCRETE — F11's repair. Fintype: unit U0b. -/
def SplittingType (n : ℕ) : Type :=
  {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 1 ≤ x.1 ∧ 1 ≤ x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n}

/-- The level-N box, CONCRETE (ruling (A)): the n free coefficients of a monic
    degree-n polynomial mod p^N (p^{nN} classes; a real Fintype). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- The monic polynomial a box point denotes: X^n + Σ_i C (f i) · X^i — THE
    polynomial space behind every count (rev-2 criticals 1/2's space objection). -/
noncomputable def Box.toPoly {p n N : ℕ} (f : Box p n N) : Polynomial (ZMod (p ^ N)) :=
  X ^ n + ∑ i : Fin n, C (f i) * X ^ (i : ℕ)

/-- The level reduction Box p n N' → Box p n N for N ≤ N' (`ZMod.castHom`, p^N ∣ p^N'). -/
noncomputable def boxProj (p n : ℕ) {N N' : ℕ} (h : N ≤ N') : Box p n N' → Box p n N :=
  fun f i => ZMod.castHom (pow_dvd_pow p h) _ (f i)

/-- The base digit section policy (D4R0K S1.4 (B4)/O3 — gap 6). -/
inductive BaseSection | teichmuller | unspecified
  deriving DecidableEq

/-- THE CLASSIFIER INTERFACE (rulings (A)/(B); replaces Census). HYPOTHESIS
    STRUCTURE, owner MovesD + HC-2 — the MovesC `JetSetup` precedent.
    `canonical`: T_can^τ's verdict-type map — "T_can^τ is a CHOICE-FREE function of f"
    ([1] L2 + VP; [3t] ONE-F); `some σ` = complete finite realizable tree, all leaves
    (τ-irr)/(τ-hen), certified at level N (thr ≤ N). `trueType`: the
    true-factorization-type field of the level-N class — constrained on the concrete
    box by `VPSound` (a LEDGER field, D10), its ℤ_p fidelity HC-2's declared bridge
    (D9); NOT a baked-in soundness law (rev-2 critical 1: soundness is an OPEN
    kernel, so it is a hypothesis, never an interface axiom). `canonical_stable`:
    TREE-N's join / Thm 2.1 decision stability. `baseSection`: the O3 pin datum
    (the ledger requires `= .teichmuller`). -/
structure ClassifierSpec (n p : ℕ) where
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  trueType : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ
  baseSection : BaseSection

/-- VP-SOUND at interface strength, TYPED over the concrete box (ruling (B); never a
    bare Prop slot): every decided-σ class has true factorization type σ. An OPEN
    kernel (CL-10's VP + VP-SOUND citation duty) — consumed as a ledger field. -/
def VPSound {n p : ℕ} (X : ClassifierSpec n p) : Prop :=
  ∀ N (f : Box p n N) σ, X.canonical N f = some σ → X.trueType N f = some σ

/-- decided_σ(N) — DEFINED from the canonical map (never a free field). -/
noncomputable def ClassifierSpec.decided {n p : ℕ} (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = some σ}

/-- undec(N) := #Undec(N). -/
noncomputable def ClassifierSpec.undec {n p : ℕ} (X : ClassifierSpec n p) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.canonical N f = none}

/-- env(N) := undec(N)/p^{nN} (the measured envelope). -/
noncomputable def ClassifierSpec.env {n p : ℕ} (X : ClassifierSpec n p) (N : ℕ) : ℝ :=
  (X.undec N : ℝ) / (p : ℝ) ^ (n * N)

/-- d_σ(N) := decided_σ(N)/p^{nN}. -/
noncomputable def ClassifierSpec.dmass {n p : ℕ} (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℝ :=
  (X.decided σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- The TRUE-type count (clause (ii)'s object, D10): #{f : trueType N f = some σ}. -/
noncomputable def ClassifierSpec.trueCount {n p : ℕ} (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // X.trueType N f = some σ}

/-- The true-type mass trueCount_σ(N)/p^{nN}. -/
noncomputable def ClassifierSpec.trueDmass {n p : ℕ} (X : ClassifierSpec n p)
    (σ : SplittingType n) (N : ℕ) : ℝ :=
  (X.trueCount σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- HYPOTHESIS STRUCTURE (MovesS interface): the fixed p-independent rational output.
    R_σ := RS.1-SH's object — "the ONLY density-typed output of the solve" (§S type
    fence: no μ̂-typed marked total appears anywhere in MovesU). -/
structure SolveData (n : ℕ) where
  R : SplittingType n → RatFunc ℚ

/-- Literal evaluation of R_σ at q = p (Mathlib `RatFunc.eval`; junk 0 at poles —
    consumed ONLY under RegP, D6). -/
noncomputable def evalℝ {n : ℕ} (S : SolveData n) (σ : SplittingType n) (p : ℕ) : ℝ :=
  ((S.R σ).eval (RingHom.id ℚ) (p : ℚ) : ℚ)

/-- "The fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED (q₀ not a pole)". -/
def DefinedAt (g : RatFunc ℚ) (q₀ : ℚ) : Prop := g.denom.eval q₀ ≠ 0

/-- HYPOTHESIS STRUCTURE (MovesS/§S S.4 interface; F4/F10 repair): the (REG-p) bundle.
    Q(p) = EXACTLY the image of the base-change depths (δ = 1 required — nonempty, never
    an arbitrary Finset); Block nonempty; K_e as literal matrices; ALL SEVEN displayed
    entry families as data (b_e BOTH components, per-cell J (CL-18), ι_e, W_Ŝ, every
    β_{e,τ} leg); ACT abstract (CTS-M(ii), owner [1v]). REV 4 (F3-G3): J/W/leg families
    pinned BY EQUATION ONLY — no positivity ((K-TRI) minimal blocks may have zero
    branching cells/shapes); `instBiNe`/`blockDim_pos` are the only positivity pins. -/
structure RegData (p : ℕ) where
  /-- base-change depths δ of RS.1-SH (owner MovesS) -/
  depthSet : Finset ℕ
  /-- δ = 1 (the shallow pool) always arises -/
  one_mem_depthSet : 1 ∈ depthSet
  /-- Q(p) -/
  Pool : Finset ℕ
  /-- Q(p) IS the depth image -/
  pool_eq : Pool = depthSet.image (p ^ ·)
  Block : Type
  instB : Fintype Block
  /-- the top block exists -/
  instNe : Nonempty Block
  -- per-block state indices: size PINNED to the table's row count (ruling (C))
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  /-- kills the empty-det = 1 dodge -/
  instBiNe : ∀ e, Nonempty (bidx e)
  /-- the block table's row count (owner [1v]/[3]) -/
  blockDim : Block → ℕ
  blockDim_pos : ∀ e, 0 < blockDim e
  bidx_card : ∀ e, Fintype.card (bidx e) = blockDim e
  /-- {each entry of K_e} -/
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)
  /-- b_e^{term,fin} -/
  bterm : ∀ e : Block, bidx e → RatFunc ℚ
  /-- b_e^split -/
  bsplit : ∀ e : Block, bidx e → RatFunc ℚ
  /-- {each entry of ι_e} -/
  iota : ∀ e : Block, bidx e → RatFunc ℚ
  -- per-cell J entries (CL-18): |Jcell e| = the table's branching-cell count.
  cellCount : Block → ℕ
  JIdx : Block → Type
  instJ : ∀ e, Fintype (JIdx e)
  JIdx_card : ∀ e, Fintype.card (JIdx e) = cellCount e
  Jcell : ∀ e : Block, JIdx e → RatFunc ℚ
  -- W_Ŝ coefficients (CL-17): one per shallow shape (equation pin only, F3-G3)
  shapeCount : ℕ
  WIdx : Type
  instW : Fintype WIdx
  WIdx_card : Fintype.card WIdx = shapeCount
  Wcoef : WIdx → RatFunc ℚ
  -- β legs: per (leg, depth δ); entryList covers EVERY δ ∈ depthSet (per-pool coverage)
  legCount : Block → ℕ
  legIdx : Block → Type
  instL : ∀ e, Fintype (legIdx e)
  legIdx_card : ∀ e, Fintype.card (legIdx e) = legCount e
  betaLeg : ∀ e : Block, legIdx e → ℕ → RatFunc ℚ
  /-- ACT active value at a pool -/
  act : RatFunc ℚ → ℕ → ℚ

/-- E(e) — a DEFINITION, verbatim the union SQ.4 displays; every family index-typed
    and cardinality-pinned (ruling (C)), the β images taken at EVERY depth of
    `depthSet`. (Classical DecidableEq on RatFunc ℚ for the images.) -/
noncomputable def RegData.entryList {p : ℕ} (D : RegData p) (e : D.Block) :
    Finset (RatFunc ℚ) :=
  letI := Classical.decEq (RatFunc ℚ)
  letI := D.instBi e; letI := D.instBd e; letI := D.instJ e
  letI := D.instW; letI := D.instL e
  (Finset.univ.image fun ij : D.bidx e × D.bidx e => D.K e ij.1 ij.2)
    ∪ (Finset.univ.image (D.bterm e)) ∪ (Finset.univ.image (D.bsplit e))
    ∪ (Finset.univ.image (D.Jcell e)) ∪ (Finset.univ.image (D.iota e))
    ∪ (Finset.univ.image D.Wcoef)
    ∪ D.depthSet.biUnion (fun δ => Finset.univ.image (fun l => D.betaLeg e l δ))

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every member of the DEFINED E(e)
    (all seven displayed families, cardinality-pinned) defined at q₀ AND literal =
    ACT active value ((ii-c) agreement); PLUS the EVALUABILITY clause (ruling (D),
    rev-2 critical 4): the literal R_σ(p) is DEFINED — "UNDER (REG-p), the literal
    evaluation R_σ(p) of the fixed element of ℚ(q) is DEFINED and IS the active
    value". Neither implies nor is implied by E0/CL-1 or ACT/CL-5 (D5). Never
    vacuous: Pool ∋ p^1, Block nonempty, every index family nonempty-pinned. -/
def RegP {n p : ℕ} (S : SolveData n) (D : RegData p) : Prop :=
  (∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀) ∧
  (∀ σ : SplittingType n, DefinedAt (S.R σ) (p : ℚ))

/-- HYPOTHESIS STRUCTURE (MovesD/[3t] interface; F2 repair): the tree-fiber series.
    `Tree σ` = the complete finite realizable canonical trees of verdict-type σ (owner
    MovesD); `thr` = TREE-N's decision threshold; `mem_slice_iff` CHARACTERIZES the
    slice as the thr ≤ N slice (no arbitrary Finset family). The Finset TYPE of
    `thrSlice` is CL-7's finiteness riding the instantiation (D4 — TRACK-COUNT + D(n)
    + genuine-increment, OPEN upstream, named in KernelStatements). The tie to the
    classifier's counts is the ledger's `finiteness_stack` IDENTITY (TREE-N):
    an empty `Tree σ` forces decided_σ ≡ 0 — nothing degenerate satisfiable (D4). -/
structure FiberSeries (n p : ℕ) (X : ClassifierSpec n p) where
  Tree : SplittingType n → Type
  /-- gap 7: needed to build the Finsets -/
  instTreeDeq : ∀ σ, DecidableEq (Tree σ)
  /-- μ(fiber T): RS.1's positive series -/
  mass : ∀ σ, Tree σ → ℝ≥0∞
  /-- TREE-N's threshold -/
  thr : ∀ σ, Tree σ → ℕ
  thrSlice : ∀ σ : SplittingType n, ℕ → Finset (Tree σ)
  mem_slice_iff : ∀ σ N (T : Tree σ), T ∈ thrSlice σ N ↔ thr σ T ≤ N
  /-- definitional corollary, kept explicit (F2) -/
  slice_exhausts : ∀ σ (T : Tree σ), T ∈ thrSlice σ (thr σ T)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {n p : ℕ} {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (σ : SplittingType n) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

/-- One menu outcome, minimal concrete vocabulary (ruling (E), rev-2 gap 5):
    m members, c continuations, whether it stays at equal block size, and its
    target state (`none` = halt — the (BDY)/empty-continuation reading). -/
structure MenuEntry (State : Type) where
  m : ℕ
  c : ℕ
  sameSize : Bool
  target : Option State
  deriving DecidableEq

/-- The move-menu vocabulary (CL-13/CL-11's MovesU-visible face; owner [1v]/[2a]):
    the ONE fixed finite state set with per-state outcome menus AS FINSETS — bound at
    the p-UNIFORM layer (before ∀ p; F3-C2/G4). REV 4 pin (F3-G1): per-state outcome
    counts are catalogue DATA with a card equation, and menus are not ALL empty
    (a single empty menu = the halt convention and stays allowed). -/
structure MenuData where
  State : Type
  instState : Fintype State
  instStateDeq : DecidableEq State
  instStateNe : Nonempty State
  menu : State → Finset (MenuEntry State)
  /-- the catalogue's per-state outcome count -/
  menuCount : State → ℕ
  menu_card : ∀ s, (menu s).card = menuCount s
  /-- kills the all-∅ vacuity dodge (F3-G1) -/
  menu_not_all_empty : ∃ s, menuCount s ≠ 0

/-- The (K-SUB) m = 1 classification as a REAL Prop over menus. REV 4 (F3-C1):
    binds same-size CONTINUATIONS ONLY — "equal-e CONTINUATION rides EXCLUSIVELY in
    K_e's (c = 1, m = 1) rows" (the same-size single-child direction). Same-size
    HALTS (c = 0, the b_e^{term,fin} leaves) are generic and EXEMPT: without the
    `o.c ≠ 0` guard the faithful catalogue would falsify the Prop. -/
def KsubM1C1 (M : MenuData) : Prop :=
  ∀ s, ∀ o ∈ M.menu s, o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1

/-- CL-13's menu well-formedness FACE (the typed trace, asserted BESIDE the
    full-statement slot `ctsmSyntax` in `cl13` — F3-C2): every outcome has ≥ 1
    member, ≤ m continuations, and PER-ENTRY TARGET TOTALITY on continuing outcomes
    (honest label — this is NOT the global compatibility of the target-cell maps,
    which lives in the `ctsmSyntax` slot with the cell predicates and
    p-independence); the empty menu is the halt convention. -/
def MenuWF (M : MenuData) : Prop :=
  ∀ s, ∀ o ∈ M.menu s, 1 ≤ o.m ∧ o.c ≤ o.m ∧ (o.c ≠ 0 → o.target.isSome)

end LeanUrat.MovesU
