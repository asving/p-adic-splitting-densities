/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.KCutK1Tie
import LeanUrat.MovesS.N2Det
import LeanUrat.MovesS.N2Sigmas
import LeanUrat.MovesT.G1_toyGate

/-! # PoolDictProbe — POOL-DICT ((H8′)(iii)) DECIDED at the compiled n2 instance

POOL-DICT ATTEMPT unit (synthesis pass 5 F1 target (iii) = pass-4 F2a), the
countermodel-first entry.  The (H8′)(iii) row (ROOT §3.1): "the node-level τ/δ
pool dictionary — a typed read-off for C3's pool rows beyond the pinned `e_key`;
`vBridge` constrained only by keying/injectivity/support — plus `blockTotal_tie`'s
instantiation at the intended member."  Pass-4 F2a's derivation hope: derive the
node-level τ/δ read-off from the compiled K-CUT laws (`kcut_reduce` ownership +
`massFactor` support) before treating it as blocked on [2r]/CL-8.

## VERDICT: REFUTED (compiled) — the pool rows are UNDERDETERMINED

This file exhibits, over ONE fixed compiled carrier pack — the REAL n2 ledger
instance (`n2T`/`n2M`/`n2RB`/`n2hdc`/`n2hK`/`n2F`/`n2Chain`, packed as `pdC :
UCarriers 2`, with the PROVED `n2hdet`) and ONE fixed extraction re-key pack
`pdR : KCutReKeys` — TWO `KCutK1Tie` instances (`pdTIE 1`, `pdTIE 2`) that agree
on `eOf`, `τOf`, and `vBridge` and differ in the pool-transport row `δOf`
(δ ≡ 1 vs δ ≡ 2), BOTH satisfying every C3 row including the NON-VACUOUS
grammar-total tie `blockTotal_tie` (the chain's `Sigmas` has three members; the
tie binds at each).  Display: `pooldict_delta_underdetermined`.

The mechanism: at the n2 table the e = 1 block is all-termFin with the single
verdict multiset {(1,1)} of degree 1, so its σ′-keyed solve VANISHES at every
degree-2 σ′ (`pd_blockSolve1_zero` — the honest e = 1 analogue of the landed
`n2_blockSolve_v21`), and `powSubst δ 0 = 0` for EVERY δ: the tie equation
0 = 0 cannot see δ.  Since the two instances share every ambient object
(`pdC`, `pdR`, `pdHdet`), NO law stated over the carrier pack — `kcut_reduce`'s
binder rows, `massFactor`'s factorwise support, anything — can separate them:
the τ/δ pool dictionary is NOT derivable from the compiled K-CUT laws.

## What is and is NOT claimed (the honesty display)

* REFUTED: pass-4 F2a's derive-from-wiring route for (H8′)(iii).  The pool rows
  `τOf`/`δOf` are genuinely NEW interface content; the (H8′)(iii) pricing
  (node-level read-off pins against `BlockDeriv.iface`, blocked on the [2r]/CL-8
  REL.2 dictionary + continuation memorylessness) STANDS as displayed.
* The compiled countermodel pins the δ-LEG.  The τ-leg is trivial at every
  compiled table on file (`n2T` and the B15a countermodel table both carry
  `State ≡ Unit`, so `τOf` has a unique value HERE); the same construction
  floats `τOf` at any table with two states whose measured rows agree, but no
  such table is compiled — the τ-leg refutation is same-genre, NOT compiled.
* The tree legs of `pdR` are deliberately EMPTY (`Tree σ = Empty`): the decision
  concerns the POOL rows' slack against the S-side solve, which is non-vacuous
  (three `Sigmas` members, real `blockSolve`, real `n2hdet`); nothing here
  claims tree realization content.
* `e_key` is NON-vacuous here (`Deriv = PUnit`, `dcar` lands on a real
  `BlockDeriv` headed by the G1 toy node with `entE = 1`) — the e-leg stays
  pinned exactly as (H8′)(iii) says, and the countermodel respects it: only the
  UNPINNED rows float.
* Nothing here discharges (H8′)(iii); this unit DECIDES its status (refutation
  of derivability), per the F1 countermodel-first protocol.

Deps: H8-C3 (`KCutK1Tie`), the n2 ledger instance (MovesS/N2*), the G1 toy node
(MovesT/G1_toyGate).  Record: `lean/notes/openmath/POOLDICT_2026-08-08.md`. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesS LeanUrat.MovesU LeanUrat.MovesC Matrix
open scoped ENNReal

/-! ## §1 The ambient compiled instance: the n2 ledger pack -/

/-- The REAL n2 carrier pack (every component the landed public n2 object). -/
noncomputable def pdC : LeanUrat.MovesU.UCarriers 2 :=
  ⟨n2T, n2M, n2RB, n2hdc, n2hK, n2F, n2Chain⟩

/-- `DetHyp` at the pack — definitionally the landed `n2hdet`. -/
theorem pdHdet : LeanUrat.MovesS.DetHyp pdC.T pdC.RB pdC.hK := n2hdet

/-! ## §2 The e = 1 solve vanishes at every σ′ ≠ {(1,1)}
(the honest e = 1 analogue of the landed `n2_blockSolve_v21`) -/

private lemma pd_bTerm1_zero (σ' : Multiset n2T.VType) (hne : σ' ≠ {n2v11})
    (τ' : n2T.State 1) : bTerm n2T n2RB 1 σ' τ' = 0 := by
  unfold bTerm
  apply Finset.sum_eq_zero
  intro o _
  rw [if_neg]
  rintro ⟨-, hv⟩
  exact hne (hv.symm.trans (rfl : (n2T.odata 1 τ' o).verdicts = {n2v11}))

private lemma pd_splitOuts1 (τ : n2T.State 1) : splitOuts n2T 1 τ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro o
  simp only [splitOuts, Set.mem_toFinset, Set.mem_setOf_eq]
  intro hr
  exact Route.noConfusion
    ((show routeOf (n2T.odata 1 τ o) = Route.termFin from rfl).symm.trans hr)

/-- The e = 1 solve is 0 at every σ′ other than the degree-1 exit {(1,1)}:
the block-1 layer is all-termFin with verdicts {(1,1)} (so `bTerm` has empty
support off {(1,1)}) and has no split outcomes (so `bSplit = 0`). -/
theorem pd_blockSolve1_zero (hdet : DetHyp n2T n2RB n2hK)
    (he : 1 ∈ Finset.Icc 1 2) (τ : n2T.State 1) (σ' : Multiset n2T.VType)
    (hne : σ' ≠ {n2v11}) :
    blockSolve n2T n2RB n2hdc n2hK hdet 1 he τ σ' = 0 := by
  rw [blockSolve_eq]
  have hb : (fun τ' => bTerm n2T n2RB 1 σ' τ' +
      bSplit n2T n2RB n2hdc 1 he
        (fun e' _ τ' σ'' =>
          if he' : e' ∈ Finset.Icc 1 2 then
            blockSolve n2T n2RB n2hdc n2hK hdet e' he' τ' σ''
          else 0) σ' τ')
      = (0 : n2T.State 1 → Qq) := by
    funext τ'
    rw [pd_bTerm1_zero σ' hne τ', bSplit_def, pd_splitOuts1 τ', Finset.sum_empty,
      add_zero]
    rfl
  show ((1 - Kmat n2T n2RB 1 (n2hK 1 he))⁻¹ *ᵥ
      (bTerm n2T n2RB 1 σ' +
        bSplit n2T n2RB n2hdc 1 he _ σ')) τ = 0
  rw [show (bTerm n2T n2RB 1 σ' +
      bSplit n2T n2RB n2hdc 1 he
        (fun e' _ τ' σ'' =>
          if he' : e' ∈ Finset.Icc 1 2 then
            blockSolve n2T n2RB n2hdc n2hK hdet e' he' τ' σ''
          else 0) σ') = 0 from hb, Matrix.mulVec_zero]
  rfl

/-- Every chain-Sigmas member has verdict degree 2, hence differs from the
degree-1 exit {(1,1)} (via `sig_exact` — no private enumeration consumed). -/
private lemma pd_sigmas_ne (σ' : Multiset n2T.VType)
    (hσ' : σ' ∈ pdC.chain.Sigmas) : σ' ≠ {n2v11} := by
  intro heq
  have hsum : (σ'.map fun v => ((n2T.vdeg v : ℕ))).sum = 2 :=
    (pdC.chain.sig_exact σ').mp hσ'
  rw [heq] at hsum
  have h1 : ((n2T.vdeg n2v11 : ℕ)) = 1 := rfl
  simp [h1] at hsum

/-- Restatement of the zero solve over the pack's own projections (defeq; kept
separate so `rw` has the pack-syntax form the C3 rows display). -/
private lemma pd_bs0 (he : (1 : ℕ) ∈ Finset.Icc 1 2) (σ' : Multiset n2T.VType)
    (hne : σ' ≠ {n2v11}) (τ : n2T.State 1) :
    LeanUrat.MovesS.blockSolve pdC.T pdC.RB pdC.hdc pdC.hK pdHdet 1 he τ σ' = 0 :=
  pd_blockSolve1_zero pdHdet he τ σ' hne

/-! ## §3 The probe carriers: history, block datum, trivial classifier/fiber -/

/-- One-node history over the G1 toy head read (species root, `e = 1`). -/
noncomputable def pdH0 : History 2 (ZMod 2) :=
  ⟨[LeanUrat.MovesT.toyHead], List.cons_ne_nil _ _, by
    intro j hj
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst hj0
    exact ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- The probe block datum: headed by `pdH0`, empty layer — a REAL `BlockDeriv`
with interface node the toy head, so `entE = 1` non-vacuously. -/
noncomputable def pdD0 : BlockDeriv 2 (ZMod 2) := ⟨pdH0, ⟨∅, ∅, ∅⟩⟩

lemma pdD0_entE : pdD0.entE = 1 := rfl

/-- Trivial classifier spec (everything undecided — the tree side carries no
content in this probe; see the honesty display). -/
noncomputable def pdX : ClassifierSpec 2 2 where
  canonical := fun _ _ => none
  trueType := fun _ _ => none
  canonical_stable := fun _ _ _ hc => nomatch hc
  baseSection := .teichmuller

/-- Empty tree-fiber series (no realized trees; all tree-leg rows vacuous). -/
noncomputable def pdFb : FiberSeries 2 2 pdX where
  Tree := fun _ => Empty
  instTreeDeq := fun _ a _ => a.elim
  mass := fun _ T => T.elim
  thr := fun _ T => T.elim
  thrSlice := fun _ _ => ∅
  mem_slice_iff := fun _ _ T => T.elim
  slice_exhausts := fun _ T => T.elim

/-- The entrance predicate (irrelevant to the pool-row decision). -/
def pdE : History 2 (ZMod 2) → Prop := fun _ => False

/-! ## §4 The verdict-vocabulary bridge -/

/-- The literal (e, f) read-off of a verdict type through the R20 structural pin. -/
noncomputable def pdBridgeFn : n2T.VType → ℕ × ℕ :=
  fun v => (((n2T.vEquiv v).1.1 : ℕ), ((n2T.vEquiv v).1.2 : ℕ))

lemma pdBridgeFn_injective : Function.Injective pdBridgeFn := by
  intro v w hvw
  simp only [pdBridgeFn, Prod.mk.injEq] at hvw
  have h1 : (n2T.vEquiv v).1.1 = (n2T.vEquiv w).1.1 := PNat.coe_injective hvw.1
  have h2 : (n2T.vEquiv v).1.2 = (n2T.vEquiv w).1.2 := PNat.coe_injective hvw.2
  exact n2T.vEquiv.injective (Subtype.ext (Prod.ext h1 h2))

/-! ## §5 The shared extraction re-key pack -/

/-- THE ONE SHARED `KCutReKeys` PACK: one shape (a single entrance at `pdH0`),
one slot, `Deriv = PUnit` carried by the real block datum `pdD0`, weights 0.
Both TIE instances below consume THIS pack unchanged. -/
noncomputable def pdR : KCutReKeys pdFb pdE where
  supplyDec := fun _ => instDecidableFalse
  real := fun _ T => T.elim
  vOf := fun σ => Multiset.map pdBridgeFn (vmap n2T σ)
  verdict_key := fun _ T => T.elim
  ShL := PUnit
  ctblS := inferInstance
  shape := fun _ => ⟨⟨∅, ∅, ∅⟩, {pdH0}, 0⟩
  k := fun _ => 1
  k_card := fun _ => rfl
  ent := fun _ _ => pdH0
  ent_inj := fun _ a b _ => Subsingleton.elim a b
  ent_mem := fun _ _ => Finset.mem_singleton_self _
  Deriv := fun _ _ => PUnit
  ctblD := fun _ _ => inferInstance
  dcar := fun _ _ _ => pdD0
  W := fun _ => 1
  weight := fun _ _ _ => 0
  shIdx := fun _ T => T.elim
  shIdx_eq := fun _ T => T.elim
  cutBlk := fun _ T => T.elim
  cutBlk_car := fun _ T => T.elim

private lemma pd_blockTotal_zero (Ŝ : pdR.ShL) (i : Fin (pdR.k Ŝ))
    (v : Multiset (ℕ × ℕ)) : pdR.blockTotal Ŝ i v = 0 :=
  tsum_zero

/-- Evaluation of a zero element of `OKat` contributes 0 to the tie's RHS. -/
private lemma pd_eval_zero {q : ℚ} (x : Qq) (hx : x = 0) (hok : x ∈ OKat q) :
    ENNReal.ofReal ((evalAt q ⟨x, hok⟩ : ℚ) : ℝ) = 0 := by
  subst hx
  have h0 : (⟨(0 : Qq), hok⟩ : OKat q) = 0 := rfl
  rw [h0, map_zero]
  simp

/-! ## §6 THE TWO TIE INSTANCES (identical except `δOf`) -/

/-- A full `KCutK1Tie` instance at ANY pool transport δ: the e-leg pinned
(`e_key` against the real `pdD0`), the bridge keyed/injective, and the
grammar-total tie holding NON-VACUOUSLY at each of the chain's three Sigmas
members — because the e = 1 solve is 0 there and `powSubst δ 0 = 0` for every δ. -/
noncomputable def pdTIE (δ : ℕ+) : KCutK1Tie pdC pdR pdHdet where
  eOf := fun _ _ => ⟨1, by decide⟩
  τOf := fun _ _ => ()
  δOf := fun _ _ => δ
  e_key := fun _ _ _ => rfl
  vBridge := fun m => m.map pdBridgeFn
  vBridge_vOf := fun _ => rfl
  vBridge_inj := (Multiset.map_injective pdBridgeFn_injective).injOn
  bOK := fun Ŝ i σ' hσ' => by
    have hz : LeanUrat.MovesS.blockSolve pdC.T pdC.RB pdC.hdc pdC.hK pdHdet
        1 (by decide) () σ' = 0 :=
      pd_bs0 (by decide) σ' (pd_sigmas_ne σ' hσ') ()
    exact (congrArg (powSubst δ) hz).trans (map_zero _) ▸ zero_mem _
  blockTotal_tie := fun Ŝ i σ' hσ' =>
    (pd_blockTotal_zero Ŝ i _).trans
      ((pd_eval_zero _
        ((congrArg (powSubst δ)
          (pd_bs0 _ σ' (pd_sigmas_ne σ' hσ') _)).trans (map_zero _)) _).symm)
  blockTotal_supp := fun Ŝ i v _ => pd_blockTotal_zero Ŝ i v

/-! ## §7 THE REFUTATION DISPLAY -/

/-- **POOL-DICT UNDERDETERMINATION (the (H8′)(iii) decision, compiled).**
Over ONE fixed compiled carrier pack (`pdC` = the real n2 ledger instance,
`pdR`, `pdHdet` = the proved `n2hdet`) there are TWO `KCutK1Tie` instances
agreeing on `eOf`, `τOf`, `vBridge` and differing in the pool row `δOf`:
the compiled K-CUT laws do NOT pin the node-level pool dictionary — the
derive-from-wiring route for (H8′)(iii) is REFUTED, and the row's displayed
pricing (a node-level read-off pinned against `BlockDeriv.iface`, blocked on
[2r]/CL-8) stands as the honest statement. -/
theorem pooldict_delta_underdetermined :
    ∃ T1 T2 : KCutK1Tie pdC pdR pdHdet,
      T1.eOf = T2.eOf ∧ T1.τOf = T2.τOf ∧ T1.vBridge = T2.vBridge ∧
      T1.δOf ≠ T2.δOf := by
  refine ⟨pdTIE 1, pdTIE 2, rfl, rfl, rfl, fun h => ?_⟩
  have h2 : (1 : ℕ+) = 2 :=
    congrFun (congrFun h PUnit.unit) (⟨0, Nat.one_pos⟩ : Fin (pdR.k PUnit.unit))
  exact absurd h2 (by decide)

#print axioms pd_blockSolve1_zero
#print axioms pooldict_delta_underdetermined

end LeanUrat.Scaffold.HDischarge.H8
