/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.U0b_splitTypeFintype
import LeanUrat.MovesU.DefsCarriers

/-!
# MovesU/DefsLedger — THE TYPED CAPSTONE LEDGER (MOVESU RETYPE, 2026-07-30)

STATEMENT-CHANGE WARRANT: `lean/notes/MOVESU_RATIFY_CODEX_2026-07-30.md` (REJECT 7/2,
every finding accepted). This file executes the retype's Stages 1–2 against that
verdict, per the C9 CL-map:

* CRITICAL 1 (bare-`Prop` slots): the 35-slot `KernelStatements` pack is RETIRED.
  Rows whose owner vocabulary is BUILT are now typed over the real carriers:
  CL-1 = `UCarriers.cl1` (`MovesS.RegP`, derived); CL-4 = `cl4_env_tendsto` (its
  qualitative form, typed); CL-5's NINE = `C.chain.L : MovesS.LedgerIV` (each of the
  nine a contentful Prop of the built §S corpus — the MovesV units are the discharge
  candidates per C9); CL-6 = `cl6 : Nonempty (MovesS.PolyGeomLaws …)` (the value+degree
  law package); CL-7's conclusion = `cl7_bound` (the finite decided family with an
  explicit bound — SQ.0's conclusion form); CL-9(β)/XRB = `C.chain.B.xrb` (typed,
  carried); CL-10's VP-SOUND = `cl10_vpsound : VPSound X`, its TREE-N operative
  content = `TreeSeam` (below); CL-11 = `C.hdc : MovesS.DegCons` + `cl11_ksub :
  KsubM1C1 M`; CL-17 = `cl17 : C.chain.wsh17_pin` (the OPEN production burden, typed
  projection); CL-18 = the `jPCell`/`jcell_interp`/`jcell_sum` law fields of the
  carried `C.RB : MovesS.RatBurdens`; CL-19's representative-invariance face =
  `cl19_rep` (typed over the real measured carrier; the h_ent/history face is
  disclosed residual). CTS-M(ii-c)'s consumed-leg gate = `C.chain.legs_read` (typed,
  carried).
  RESIDUAL BARE ROWS (disclosed, fenced — owner corpus ABSENT in Lean, so no
  non-vacuous typing exists at this seam): `UpstreamKernelStatements` below.
* CRITICAL 2 (assumed `finiteness_stack`/`solve_stack`): BOTH DERIVED.
  `TreeSeam.finiteness_stack` proves the TREE-N partition identity from the typed
  seam rows (the canonical-tree assignment + the per-tree exact count tie — the
  note's own open premises, named); `SolveSeam.solve_stack` proves finiteness +
  identification + RS.3 positivity from the REAL solve (`MovesS.Rsh` via
  `r_is_solve`), the chain's `rsh_interp`/`r_bdd`, and the `RegPin`-transported
  determinant gate — the MovesS solve laws genuinely reach it.
* CRITICAL 3: `S.R` is PINNED to the Cramer/RS.1-SH solve output (`r_is_solve`);
  `FiberSeries`' sum is pinned to the chain's measured `Rval` (`series_tie`, the
  named open [3t] premise); the classifier's `trueType` is pinned by `ZpBridge`.
* CRITICAL 4: `RegPin` re-keys `RegData` to the REAL block system (Stage 3).
* CRITICAL 7: `ZpBridge` — the NAMED HC-2 premise typing `trueType` against genuine
  ℤ_p objects (monic `Polynomial ℤ_[p]` lifts through `PadicInt.toZModPow`, with the
  ℚ_p-factorization law at degree level; the finer e/f ramification-residue refinement
  is the disclosed HC-2 residue, recorded in the docstring).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology ENNReal LeanUrat

/-! ## The residual bare rows (disclosed and fenced)

Every slot below is STILL a bare `Prop` — retained ONLY because its owner vocabulary
has no Lean corpus at this seam ([5] X-side histories/discs, [2r] REL measures, [2a]
species catalogue, [1v] cell-predicate syntax), so any "typed" version would carry
instance-selectable invented carriers — the same defect with extra steps. This is the
FENCED bare surface (15 rows, down from 35); each row names its owner. Filling a slot
with `True` remains an instantiation-fidelity violation adjudicated at the owner's
audit. -/
structure UpstreamKernelStatements where
  /-- CL-2 [5]: X.1b WEIGHT-CHARGE — #{recentering nodes of H} ≤ s(n)·v_p(disc f)
      (MOVES 11153–11160); owner [5], history/disc vocabulary absent. -/
  weightCharge : Prop
  /-- CL-3 [5]+[2b]: X.2 PROGRESS — (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/(X2-TAILS) with
      c₃(n), c₄(n), s(n); owner [5]. -/
  progressX2 : Prop
  /-- CL-7a [4]: TRACK-COUNT — ≤ L(n) track-opening events per history (MOVES
      13040–13048); its CONCLUSION form is typed at `cl7_bound`. -/
  trackCount : Prop
  /-- CL-7b [4]: the D(n) common-denominator duty (candidate n!, underived). -/
  dnDuty : Prop
  /-- CL-7c [4]: the positive genuine-increment sub-claim. -/
  genuineIncrement : Prop
  /-- CL-8 [2r]: REL.1 re-scoped. -/
  rel1 : Prop
  /-- CL-8 [2r]: REL.2(a). -/
  rel2a : Prop
  /-- CL-8 [2r]: REL.2(b). -/
  rel2b : Prop
  /-- CL-8 [2r]: REL.2(d). -/
  rel2d : Prop
  /-- CL-8 [2r]: REL.2(e), the β-typing (e1)–(e5) leg (operative trace at this seam:
      `chain.legs_read`'s AVAgree gate, typed and carried). -/
  rel2e : Prop
  /-- CL-8 [2r]: REL.3 over O_δ. -/
  rel3 : Prop
  /-- CL-9(α) [3]: RS.0 lumpability ((β) = XRB is TYPED: `chain.B.xrb`, carried). -/
  rs0Lump : Prop
  /-- CL-10 [3t]: (SIB)/(SIB-STEP) measure-level joint form + (JC-multi) — the built
      MovesT Props (`SibCount`/`SibCountAt`/`JCmultiAt`) are per-model laws; their
      assertion AT the real classifier's tree model is the [3t] seam instantiation,
      not statable over this file's carriers yet. TREE-N's operative content IS
      typed: `TreeSeam`. -/
  sibJcMulti : Prop
  /-- CL-13 [1v]: the FULL CTS-M(i) statement (displayed cell predicates + globally
      compatible target-cell maps); the typed faces `MenuWF M`/`KsubM1C1 M` ride in
      the ledger. -/
  ctsmSyntax : Prop
  /-- CL-14 [2a] (CLOSED upstream; echo) + CL-15 [5] X.1a dictionary + CL-16 [1v]/[2b]
      M4b constancy/equivariance + CL-19's h_ent/history-invariance residue beyond
      the typed `cl19_rep` face — bundled echo row; owners [2a]/[5]/[1v]/[2b]. -/
  m1m5X1aM4bJcInv : Prop

/-! ## The TREE-N seam (CL-7/CL-10's operative content, typed — Stage 2, fin side) -/

/-- THE TREE-N SEAM (typed rows replacing the ASSUMED `finiteness_stack` field —
    ratification CRITICAL 2). The note's own open premises, named:
    `treeOf` — the canonical-tree assignment of every decided-σ class (T_can^τ's
    verdict-tree read at level N); `thr_le` — decided at N means threshold ≤ N
    (decision stability's read); `count_tie` — TREE-N's EXACT per-tree fiber count:
    μ(fiber T)·p^{nN} = #{decided-σ classes whose canonical tree is T} (the [3t]
    discharge candidate is `MovesT.treeN` — E8's `treeExp` at m = n·N — per the C9
    map; its instantiation at the real classifier is the remaining [3t] seam).
    From THESE the partition identity is DERIVED (`finiteness_stack` below). -/
structure TreeSeam (n p : ℕ) (X : ClassifierSpec n p) (F : FiberSeries n p X) where
  treeOf : ∀ (σ : SplittingType n) (N : ℕ)
    (f : {f : Box p n N // X.canonical N f = some σ}), F.Tree σ
  thr_le : ∀ σ N f, F.thr σ (treeOf σ N f) ≤ N
  count_tie : ∀ (σ : SplittingType n) (N : ℕ) (T : F.Tree σ), F.thr σ T ≤ N →
    F.mass σ T * (p : ℝ≥0∞) ^ (n * N)
      = (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
          treeOf σ N f = T} : ℝ≥0∞)

/-- The finiteness stack, DERIVED (was an assumed field — ratification CRITICAL 2):
    decided_σ(N) = p^{nN} · Σ_{thr(T) ≤ N} μ(fiber T), by partitioning the decided-σ
    classes along `treeOf` and summing `count_tie` over the slice. -/
theorem TreeSeam.finiteness_stack {n p : ℕ} [NeZero p] {X : ClassifierSpec n p}
    {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞)
      = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T := by
  classical
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (NeZero.ne p)⟩
  letI : Fintype {f : Box p n N // X.canonical N f = some σ} :=
    Fintype.ofFinite _
  -- ℕ-level partition of the decided-σ classes along the canonical-tree assignment.
  have hpart : X.decided σ N = ∑ T ∈ F.thrSlice σ N,
      Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
        seam.treeOf σ N f = T} := by
    have h1 : X.decided σ N
        = (Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).card := by
      rw [ClassifierSpec.decided, Nat.card_eq_fintype_card, Finset.card_univ]
    have h2 : (Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).card
        = ∑ T ∈ F.thrSlice σ N,
            ((Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).filter
              fun f => seam.treeOf σ N f = T).card :=
      Finset.card_eq_sum_card_fiberwise fun f _ =>
        (F.mem_slice_iff σ N _).mpr (seam.thr_le σ N f)
    have h3 : ∀ T : F.Tree σ,
        Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
            seam.treeOf σ N f = T}
          = ((Finset.univ : Finset {f : Box p n N // X.canonical N f = some σ}).filter
              fun f => seam.treeOf σ N f = T).card := by
      intro T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, h2]
    exact Finset.sum_congr rfl fun T _ => (h3 T).symm
  calc (X.decided σ N : ℝ≥0∞)
      = ∑ T ∈ F.thrSlice σ N,
          (Nat.card {f : {f : Box p n N // X.canonical N f = some σ} //
            seam.treeOf σ N f = T} : ℝ≥0∞) := by
        rw [hpart]; push_cast; rfl
    _ = ∑ T ∈ F.thrSlice σ N, F.mass σ T * (p : ℝ≥0∞) ^ (n * N) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [seam.count_tie σ N T ((F.mem_slice_iff σ N T).mp hT)]
    _ = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T := by
        rw [← Finset.sum_mul, mul_comm]

/-! ## The RegData re-key (Stage 3 — ratification CRITICAL 4) -/

/-- THE ROSTER PIN (ratification CRITICAL 4: "(REG-p) quantifies over an
    instance-chosen surrogate roster"): every `RegData` index family and count is
    EQUATED to the real §S block system. `blk`/`st` identify the blocks with the
    working degrees e ∈ [1, n] and the per-block states with the REAL table states;
    `depth_pin` pins the depth set to the consumed-deltas closure; `K_pin`/`iota_pin`
    pin the matrix and ι entries to the REAL `Kmat`/ι tables; `bterm_pin` pins each
    b^{term,fin} entry to a real verdict-multiset column; `Jcell_pin`/`W_pin` pin the
    per-cell J and W_Ŝ entry IMAGES to the real per-cell tables and shape
    presentation values; the counts (`blockDim_pin`/`cell_pin`/`shape_pin`/`leg_pin`)
    equate to the real tables' cardinalities. The β-leg ENTRY tie (beyond the count)
    rides the [3] leg vocabulary (`chain.legs_read`); recorded residual. -/
structure RegPin {n : ℕ} (C : UCarriers n) {p : ℕ} (D : RegData p) where
  blk : D.Block ≃ {e : ℕ // e ∈ Finset.Icc 1 n}
  st : ∀ b : D.Block, D.bidx b ≃ C.T.State (blk b).1
  depth_pin : D.depthSet
    = (MovesS.consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))
  K_pin : ∀ (b : D.Block) (i j : D.bidx b),
    D.K b i j
      = MovesS.Kmat C.T C.RB (blk b).1 (C.hK (blk b).1 (blk b).2) (st b i) (st b j)
  iota_pin : ∀ (b : D.Block) (i : D.bidx b),
    D.iota b i = C.RB.ι (blk b).1 (st b i)
  bterm_pin : ∀ (b : D.Block) (i : D.bidx b), ∃ σ' ∈ C.chain.Sigmas,
    D.bterm b i = MovesS.bTerm C.T C.RB (blk b).1 σ' (st b i)
  blockDim_pin : ∀ b, D.blockDim b = Fintype.card (C.T.State (blk b).1)
  cell_pin : ∀ b, D.cellCount b
    = ∑ τ : C.T.State (blk b).1, ∑ o ∈ MovesS.splitOuts C.T (blk b).1 τ,
        (C.MS.cells (blk b).1 τ o).card
  Jcell_pin : ∀ b,
    (letI := D.instJ b; letI := Classical.decEq (RatFunc ℚ)
     Finset.univ.image (D.Jcell b))
      = (letI := Classical.decEq (RatFunc ℚ)
         (Finset.univ : Finset (C.T.State (blk b).1)).biUnion fun τ =>
           (MovesS.splitOuts C.T (blk b).1 τ).biUnion fun o =>
             (C.MS.cells (blk b).1 τ o).image fun c =>
               (C.RB.jPCell (blk b).1 τ c).val)
  shape_pin : D.shapeCount = C.Fam.Sh.card
  W_pin : (letI := D.instW; letI := Classical.decEq (RatFunc ℚ)
      Finset.univ.image D.Wcoef)
    = (letI := Classical.decEq (RatFunc ℚ)
       C.Fam.Sh.image fun Ŝ => (C.chain.WshP Ŝ).val)
  leg_pin : ∀ b, D.legCount b
    = ∑ τ : C.T.State (blk b).1, ∑ o ∈ MovesS.splitOuts C.T (blk b).1 τ,
        MovesS.Outcome.c (C.T.odata (blk b).1 τ o)

/-- The determinant gate TRANSPORTS through the pin: (REG-p)'s (r1) — the full
    determinant nonzero at the pool value p — forces the REAL symbolic determinant
    hypothesis `MovesS.DetHyp` (a zero rational function evaluates to zero). -/
theorem RegPin.detHyp {n : ℕ} {C : UCarriers n} {p : ℕ} {S : SolveData n}
    {D : RegData p} (P : RegPin C D) (hreg : RegP S D) :
    MovesS.DetHyp C.T C.RB C.hK := by
  have key : ∀ b : D.Block,
      (1 - MovesS.Kmat C.T C.RB (P.blk b).1
        (C.hK (P.blk b).1 (P.blk b).2)).det ≠ 0 := by
    intro b
    letI := D.instBi b; letI := D.instBd b
    have hpool : p ∈ D.Pool := by
      rw [D.pool_eq]
      exact Finset.mem_image.mpr ⟨1, D.one_mem_depthSet, pow_one p⟩
    have h1 := (hreg.1 p hpool b).1.2
    have hmat : (1 - D.K b)
        = (1 - MovesS.Kmat C.T C.RB (P.blk b).1
            (C.hK (P.blk b).1 (P.blk b).2)).submatrix (P.st b) (P.st b) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply,
        P.K_pin b i j, EmbeddingLike.apply_eq_iff_eq]
    have hdet : (Matrix.det (1 - D.K b))
        = (1 - MovesS.Kmat C.T C.RB (P.blk b).1
            (C.hK (P.blk b).1 (P.blk b).2)).det := by
      rw [hmat, Matrix.det_submatrix_equiv_self]
    intro h0
    rw [hdet, h0] at h1
    simp at h1
  intro e he
  have h := key (P.blk.symm ⟨e, he⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-! ## The solve seam (Stage 2, solve side — CRITICAL 2/3 and GAP 2's substrate) -/

/-- THE SOLVE SEAM (typed rows replacing the ASSUMED `solve_stack` field —
    ratification CRITICAL 2/CRITICAL 3): `r_is_solve` pins `S.R` to THE real solve
    output `MovesS.Rsh` (RS.1-SH's shallow convolution over the blockSolve = the
    Cramer/adjugate route — CRITICAL 3's "S.R is the Cramer/adjugate solution of
    (R_e)", now a typed equation); `series_tie` pins the tree-fiber series sum to the
    chain's MEASURED per-σ value `Rval` — the named open [3t] premise (Haar mass of
    the canonical fibers vs the measured chain). -/
structure SolveSeam (n p : ℕ) (C : UCarriers n) {X : ClassifierSpec n p}
    (F : FiberSeries n p X) (S : SolveData n) : Prop where
  series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
  r_is_solve : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK) (σ : SplittingType n),
    S.R σ = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ)

/-- Under (REG-p), the literal evaluation equals the chain's measured value:
    `evalℝ S σ p = Rval (vmap σ) p` — through `r_is_solve` + `rsh_interp`. -/
theorem SolveSeam.evalℝ_eq_Rval {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP S D) (hp : p.Prime)
    (σ : SplittingType n) :
    evalℝ S σ p = C.chain.Rval (vmap C.T σ) (p : ℚ) := by
  have hdet : MovesS.DetHyp C.T C.RB C.hK := P.detHyp hreg
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  obtain ⟨hok, heval⟩ :=
    C.chain.rsh_interp (vmap C.T σ) (C.vmap_mem_Sigmas σ) (p : ℚ) hpP hdet
  rw [show evalℝ S σ p
      = ((MovesS.evalAt (p : ℚ)
          ⟨MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP (vmap C.T σ),
           hok⟩ : ℚ) : ℝ) from ?_]
  · exact heval
  · unfold evalℝ
    rw [ss.r_is_solve hdet σ]
    rfl

/-- The solve stack, DERIVED (was an assumed field — ratification CRITICAL 2): under
    (REG-p) the extended-value series sum is finite, IS the literal R_σ(p), and
    R_σ(p) ≥ 0 (RS.3's positivity through the chain's `r_bdd`). The reach is the
    REAL MovesS solve laws (`rsh_interp` at the prime pool) through the RegPin
    determinant transport. -/
theorem SolveSeam.solve_stack {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p}
    (ss : SolveSeam n p C F S) (P : RegPin C D) (hreg : RegP S D) (hp : p.Prime) :
    ∀ σ : SplittingType n,
      F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p) ∧
      0 ≤ evalℝ S σ p := by
  intro σ
  have heq := ss.evalℝ_eq_Rval P hreg hp σ
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  have hbdd := C.chain.r_bdd (vmap C.T σ) (p : ℚ) (C.chain.prime_sub hpP)
  refine ⟨?_, ?_, ?_⟩
  · rw [ss.series_tie σ]; exact ENNReal.ofReal_ne_top
  · rw [ss.series_tie σ, heq]
  · rw [heq]; exact hbdd.1

/-! ## The ℤ_p bridge (Stage 4's identification substrate — CRITICAL 7) -/

section ZpBridgeSection
variable (n p : ℕ) [Fact p.Prime]

/-- The ℤ_p reading predicate: the level-N class `f` reads σ iff EVERY monic
    degree-n ℤ_p lift of `f` (through `PadicInt.toZModPow`) has ℤ_p factorization
    type σ under the bridge's reading `zf`. -/
def ZpReads (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ)
    (f : Box p n N) (σ : SplittingType n) : Prop :=
  ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    g.map (PadicInt.toZModPow N) = f.toPoly → zf g = σ.1

/-- THE NAMED HC-2 ℤ_p BRIDGE (ratification CRITICAL 7: "clause (ii) proves equality
    with an instance-chosen label density, not the note's splitting density").
    `trueType` is now pinned against GENUINE ℤ_p objects: `lift_exists` — every
    level-N box class is the reduction of a monic degree-n `Polynomial ℤ_[p]`;
    `zf_factor` — the reading `zfType` is realized by an actual monic-irreducible
    factorization over ℚ_p whose factor degrees are the (e·f)-products of the read
    multiset (entries positive by `zf_pos`); `lift_true` — `trueType N f = some σ`
    IFF every lift reads σ. DISCLOSED RESIDUE (HC-2, recorded): the refinement of
    each factor's degree e·f into its ramification index e and residue degree f
    (valuation-theoretic invariants of ℚ_p[X]/(h)) is not yet typed — the bridge
    pins the factorization SHAPE, the owner corpus (HC-2) owes the e/f split. -/
structure ZpBridge (X : ClassifierSpec n p) where
  zfType : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)
  zf_pos : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∀ ef ∈ zfType g, 1 ≤ ef.1 ∧ 1 ≤ ef.2
  zf_factor : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∃ factors : Multiset (Polynomial ℚ_[p]),
      g.map (PadicInt.Coe.ringHom) = factors.prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible h) ∧
      (zfType g).map (fun ef => ef.1 * ef.2) = factors.map Polynomial.natDegree
  lift_exists : ∀ (N : ℕ) (f : Box p n N), ∃ g : Polynomial ℤ_[p],
    g.Monic ∧ g.natDegree = n ∧ g.map (PadicInt.toZModPow N) = f.toPoly
  lift_true : ∀ (N : ℕ) (f : Box p n N) (σ : SplittingType n),
    X.trueType N f = some σ ↔ ZpReads n p zfType N f σ

variable {n p} {X : ClassifierSpec n p}

/-- The ℤ_p-read count: #{level-N classes every monic lift of which reads σ}. -/
noncomputable def ZpBridge.zpCount (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // ZpReads n p B.zfType N f σ}

/-- The ℤ_p-read density at level N. -/
noncomputable def ZpBridge.zpDmass (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : ℝ :=
  (B.zpCount σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- Under the bridge, the ℤ_p-read count IS the classifier's true-type count. -/
theorem ZpBridge.zpCount_eq_trueCount (B : ZpBridge n p X) (σ : SplittingType n)
    (N : ℕ) : B.zpCount σ N = X.trueCount σ N :=
  Nat.card_congr (Equiv.subtypeEquivRight fun f => (B.lift_true N f σ).symm)

/-- Under the bridge, the ℤ_p-read density IS the true-type density. -/
theorem ZpBridge.zpDmass_eq_trueDmass (B : ZpBridge n p X) (σ : SplittingType n) :
    B.zpDmass σ = X.trueDmass σ := by
  funext N
  rw [ZpBridge.zpDmass, ZpBridge.zpCount_eq_trueCount]
  rfl

end ZpBridgeSection

/-! ## The capstone ledger (retyped) -/

/-- THE CAPSTONE LEDGER (RETYPED per the 2026-07-30 ratification): the typed rows
    over the real carriers + the derived-stack seams + the residual-row assertions.
    The S-side rows CL-1/CL-5/CL-9(β)/(ii-c)/CL-18 are carried TYPED by
    `C : UCarriers n` (see `DefsCarriers`); CL-11's DEG-CONS is `C.hdc`; (REG-p) is
    NOT a field (the ONE explicit hypothesis, D5/D8). CL-12 is CLOSED — no slot. -/
structure CapstoneLedger (n p : ℕ) (C : UCarriers n) (X : ClassifierSpec n p)
    (F : FiberSeries n p X) (S : SolveData n) (D : RegData p) (M : MenuData)
    (KR : UpstreamKernelStatements) where
  /-- CL-2 (residual bare row, fenced — see `UpstreamKernelStatements`). -/
  cl2 : KR.weightCharge
  /-- CL-3 (residual bare row, fenced). -/
  cl3 : KR.progressX2
  /-- CL-7's mechanics rows (residual bare, fenced); the CONCLUSION is `cl7_bound`. -/
  cl7 : KR.trackCount ∧ KR.dnDuty ∧ KR.genuineIncrement
  /-- CL-8's six REL rows (residual bare, fenced; (e)'s operative trace is
      `C.chain.legs_read`, typed and carried). -/
  cl8 : KR.rel1 ∧ KR.rel2a ∧ KR.rel2b ∧ KR.rel2d ∧ KR.rel2e ∧ KR.rel3
  /-- CL-9(α) (residual bare row; (β) = XRB is TYPED at `C.chain.B.xrb`). -/
  cl9 : KR.rs0Lump
  /-- CL-10's (SIB)/(JC-multi) rows (residual bare, fenced; TREE-N typed at `seam`). -/
  cl10_sib : KR.sibJcMulti
  /-- CL-13's full-statement row (residual bare; typed faces below). -/
  cl13 : KR.ctsmSyntax
  /-- CL-14/CL-15/CL-16 + CL-19's history residue (residual bare echo row). -/
  cl14_16 : KR.m1m5X1aM4bJcInv
  /-- CL-4, TYPED (qualitative form — the note's own operative trace; the a.e.
      ℤ_p reading rides the bridge): env(N) → 0. -/
  cl4_env_tendsto : Tendsto X.env atTop (𝓝 0)
  /-- CL-6, TYPED: the (iv)-POLY value+degree law package over the real carriers
      (`tcount_val`/`scount_val`/`tcount_deg`/`scount_deg`). -/
  cl6 : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)
  /-- CL-7's CONCLUSION, TYPED over the real slice: the decided family at threshold
      ≤ N is finite with an explicit bound (SQ.0's conclusion form; the (c1)–(c3)
      mechanics stay at the fenced rows). -/
  cl7_bound : ∃ B : ℕ → ℕ, ∀ (σ : SplittingType n) (N : ℕ),
    (F.thrSlice σ N).card ≤ B N
  /-- CL-10's VP-SOUND leg, TYPED over the concrete box (ruling (B)). -/
  cl10_vpsound : VPSound X
  /-- CL-11's (K-SUB) m = 1 classification, TYPED (DEG-CONS is `C.hdc`, carried). -/
  cl11_ksub : KsubM1C1 M
  /-- CL-13's menu well-formedness FACE, TYPED (the full statement is `cl13`). -/
  cl13_wf : MenuWF M
  /-- CL-17's production burden, TYPED as the chain's OPEN projection (W17ii at the
      chain's own carriers — never instance-suppliable data). -/
  cl17 : C.chain.wsh17_pin
  /-- CL-19's representative-invariance FACE, TYPED over the real measured carrier:
      the per-cell conditional mass is ONE function of the retained state —
      invariant across representatives (the history/h_ent face is fenced). -/
  cl19_rep : ∀ e (τ : C.T.State e) (x x' : C.MS.Rep e τ) (c : C.MS.Cell e τ)
    (q₀ : ℚ), q₀ ∈ C.MS.Pools → C.MS.activeState q₀ e τ →
    C.MS.μcell e τ x c q₀ = C.MS.μcell e τ x' c q₀
  /-- The O3 BASE-PIN DECLARATION (SQ.4's display duty): Teichmüller. -/
  o3_teichmuller : X.baseSection = BaseSection.teichmuller
  /-- THE TREE-N SEAM (replaces the assumed `finiteness_stack`; CRITICAL 2). -/
  seam : TreeSeam n p X F
  /-- THE SOLVE SEAM (replaces the assumed `solve_stack`; CRITICAL 2/3). -/
  ssrc : SolveSeam n p C F S
  /-- RS.4's checksum (§S S.5), the ℚ(q) identity — with `ssrc.r_is_solve` this is
      now a claim about THE real solve family, not a free `S.R`. -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) (E-phase note: derivable from
      `rs4_checksum` + (r2)-definedness via RatFunc eval-hom side conditions;
      carried as a field until that unit lands). -/
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1

/-- The derived finiteness stack, at the ledger (projection to `TreeSeam`'s). -/
theorem CapstoneLedger.finiteness_stack {n p : ℕ} [NeZero p] {C : UCarriers n}
    {X : ClassifierSpec n p} {F : FiberSeries n p X} {S : SolveData n}
    {D : RegData p} {M : MenuData} {KR : UpstreamKernelStatements}
    (L : CapstoneLedger n p C X F S D M KR) (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞)
      = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T :=
  L.seam.finiteness_stack σ N

/-- (U-n)-LOWER's ADDITIONAL slice (D12): RS.4's checksum forms. -/
structure LowerStack (n p : ℕ) (S : SolveData n) (D : RegData p) : Prop where
  rs4_checksum : ∑ σ, S.R σ = 1
  rs4_eval : RegP S D → ∑ σ, evalℝ S σ p = 1

/-- Field-selection projection (D12/G9), the lower-stack slice. -/
def CapstoneLedger.lowerStack {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p}
    {F : FiberSeries n p X} {S : SolveData n} {D : RegData p} {M : MenuData}
    {KR : UpstreamKernelStatements} (L : CapstoneLedger n p C X F S D M KR) :
    LowerStack n p S D := ⟨L.rs4_checksum, L.rs4_eval⟩

/-- THE PER-p INSTANTIATION BUNDLE (U10's quantifier shape) over the FIXED p-uniform
    data (C, S, M, KR). NEW at the retype: `Dpin` — the (REG-p) roster is pinned to
    the real block system (CRITICAL 4); `bridge` — the NAMED HC-2 ℤ_p premise
    (CRITICAL 7; never a free function). -/
structure UInstance (n : ℕ) (C : UCarriers n) (S : SolveData n) (M : MenuData)
    (KR : UpstreamKernelStatements) (p : ℕ) (hp : p.Prime) where
  X : ClassifierSpec n p
  F : FiberSeries n p X
  D : RegData p
  L : CapstoneLedger n p C X F S D M KR
  Dpin : RegPin C D
  bridge : @ZpBridge n p ⟨hp⟩ X

end LeanUrat.MovesU
