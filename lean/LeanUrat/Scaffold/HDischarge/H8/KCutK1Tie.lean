/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.KCutReduce
import LeanUrat.Scaffold.HDischarge.H8.KCutMassFactor
import LeanUrat.MovesU.DefsLedger

/-! # H8-C3 `KCutK1Tie.lean` — (K-CUT-K1-tie): the Step-18 K1 exact-form
consumption tie with the (e_i, τ_i, δ_i) pool structure

Blueprint: `lean/blueprints/HDISCHARGE_H8.md` §4 Wave 7 (specced 2026-08-05 at
the KCUT pass, finding 7 + the closing-residue item; statements compile-probed
green at b08b6dd, `/tmp/openmath/H8_wave7_probe.lean`).  Statements below are
VERBATIM from that probe; this unit lands them and proves the consumption
display `kcut_k1_form`.

## What is and is NOT claimed (the honesty display)

* `KCutK1Tie` is the TYPED form of finding 7's missing content: per-slot
  entrance pool data (`eOf`/`τOf`/`δOf`) read at grammar vocabulary, the e-leg
  pinned to the concrete interface node (`e_key` against `BlockDeriv.entE`),
  the verdict-vocabulary bridge (`vBridge` with its `vmap` keying and
  injectivity on the chain's σ-index), and THE GRAMMAR-TOTAL TIE
  (`blockTotal_tie`): each slot's `blockTotal` IS the evaluated
  `powSubst δ`-transported real `blockSolve` at the prime pool.
* HONESTY (i): the τ/δ pool rows (`τOf`/`δOf`) are DATA whose node-level
  read-off pins against the interface node (the W7 boundary-data clause) are
  part of the unit's own instantiation obligation — only the e-leg has a
  landed concrete read-off (`entE = iface.e`), so `e_key` is the one pinnable
  conformance row today.
* HONESTY (ii): `blockTotal_tie` is exactly the closing-residue item "the
  onward identification of `R.blockTotal` with the actual Step-18 block
  totals", and instantiating it needs the REL.2 pool dictionary ([2r]/CL-8,
  open) + continuation memorylessness ((K-CUT-g)'s semantic core).  The
  structure is an UNPINNED assumption package: NOTHING here discharges a seam
  field, and supplying an instance is the owner rows' work.
* HONESTY (iii): the W-leg is deliberately ABSENT — full-data W(Ŝ) vs the
  resummed `WshP` is the §1.1 granularity seam, priced at CL-17(ii)/`W17ii`,
  never here.
* HONESTY (iv): `kcut_k1_form` IS proved (sorry-free) from `kcut_reduce` +
  tie/supp/inj — the CONTENT is the structure's instantiation.  Proof: fire
  `kcut_reduce`, then identify each slot's abstract `blockTotal` with the
  σ'-indexed evaluated-solve sum (`KCutK1Tie.blockTotal_eq_tsum`): on verdicts
  hit by the bridge the fiber is a `vBridge_inj`-singleton and `blockTotal_tie`
  gives its value; off the bridge image `blockTotal_supp` and `tsum_empty`
  match 0 = 0.

Deps: H8-C1 (`KCutReduce`: `KCutReKeys`/`blockTotal`/`CompatTuple`/`cutFun`/
`kcut_reduce`), H8-C2 (`KCutMassFactor`: NOT needed by `kcut_k1_form` itself —
its `mass_eq` binder is `kcut_reduce`'s aggregate row verbatim — but consumed
by the task-directed wire `kcut_k1_form_of_massFactor` at the end of this
file, where `massFactor_mass_eq` supplies that binder), BP_V carriers through
`MovesU.DefsLedger`/`DefsCarriers` (`UCarriers`, `vmap`) and `MovesS`
(`DetHyp`/`blockSolve`/`powSubst`/`OKat`/`evalAt`), [2r]/CL-8 REL.2 dictionary
+ M04 K3: owner rows of the instantiation, cited not consumed. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- H8-C3 (K-CUT-K1-tie): the Step-18 K1 exact-form consumption tie. -/
structure KCutK1Tie {n : ℕ} (C : LeanUrat.MovesU.UCarriers n)
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E)
    (hdet : LeanUrat.MovesS.DetHyp C.T C.RB C.hK) where
  eOf : ∀ Ŝ : R.ShL, Fin (R.k Ŝ) → {e : ℕ // e ∈ Finset.Icc 1 n}
  τOf : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)), C.T.State (eOf Ŝ i).1
  δOf : ∀ Ŝ : R.ShL, Fin (R.k Ŝ) → ℕ+
  e_key : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (D : R.Deriv Ŝ i),
    (R.dcar Ŝ i D).entE = (eOf Ŝ i).1
  vBridge : Multiset C.T.VType → Multiset (ℕ × ℕ)
  vBridge_vOf : ∀ σ : LeanUrat.MovesU.SplittingType n,
    vBridge (LeanUrat.MovesU.vmap C.T σ) = R.vOf σ
  vBridge_inj : Set.InjOn vBridge (C.chain.Sigmas : Set (Multiset C.T.VType))
  bOK : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (σ' : Multiset C.T.VType),
    σ' ∈ C.chain.Sigmas →
    LeanUrat.MovesS.powSubst (δOf Ŝ i)
        (LeanUrat.MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
          (eOf Ŝ i).1 (eOf Ŝ i).2 (τOf Ŝ i) σ')
      ∈ LeanUrat.MovesS.OKat (p : ℚ)
  blockTotal_tie : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (σ' : Multiset C.T.VType)
      (hσ' : σ' ∈ C.chain.Sigmas),
    R.blockTotal Ŝ i (vBridge σ')
      = ENNReal.ofReal
          ((LeanUrat.MovesS.evalAt (p : ℚ) ⟨_, bOK Ŝ i σ' hσ'⟩ : ℚ) : ℝ)
  blockTotal_supp : ∀ (Ŝ : R.ShL) (i : Fin (R.k Ŝ)) (v : Multiset (ℕ × ℕ)),
    (∀ σ' ∈ C.chain.Sigmas, vBridge σ' ≠ v) → R.blockTotal Ŝ i v = 0

namespace KCutK1Tie

variable {n : ℕ} {C : LeanUrat.MovesU.UCarriers n}
  {X : LeanUrat.MovesU.ClassifierSpec n p}
  {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
  {R : KCutReKeys Fb E} {hdet : LeanUrat.MovesS.DetHyp C.T C.RB C.hK}

/-- THE PER-SLOT IDENTIFICATION (the proof core of `kcut_k1_form`): at every
verdict multiset `v`, the abstract slot total `R.blockTotal Ŝ i v` IS the sum
of the evaluated `powSubst δ`-transported real `blockSolve` values over the
`vBridge`-fiber of `v` in the chain's σ-index.  On-image the fiber is a
singleton (`vBridge_inj`) whose value `blockTotal_tie` supplies; off-image
both sides vanish (`blockTotal_supp`; empty `tsum`). -/
theorem blockTotal_eq_tsum (TIE : KCutK1Tie C R hdet) (Ŝ : R.ShL)
    (i : Fin (R.k Ŝ)) (v : Multiset (ℕ × ℕ)) :
    R.blockTotal Ŝ i v
      = ∑' σ' : {σ' : Multiset C.T.VType //
            σ' ∈ C.chain.Sigmas ∧ TIE.vBridge σ' = v},
          ENNReal.ofReal
            ((LeanUrat.MovesS.evalAt (p : ℚ)
              ⟨_, TIE.bOK Ŝ i σ'.1 σ'.2.1⟩ : ℚ) : ℝ) := by
  classical
  by_cases hex : ∃ σ₀ ∈ C.chain.Sigmas, TIE.vBridge σ₀ = v
  · -- on-image: the fiber is the `vBridge_inj`-singleton at σ₀
    obtain ⟨σ₀, hσ₀, rfl⟩ := hex
    refine (TIE.blockTotal_tie Ŝ i σ₀ hσ₀).trans ?_
    symm
    exact tsum_eq_single
      (⟨σ₀, hσ₀, rfl⟩ : {σ' : Multiset C.T.VType //
          σ' ∈ C.chain.Sigmas ∧ TIE.vBridge σ' = TIE.vBridge σ₀})
      fun b' hb' =>
        absurd (Subtype.ext (TIE.vBridge_inj b'.2.1 hσ₀ b'.2.2)) hb'
  · -- off-image: `blockTotal_supp` ⊔ empty fiber
    haveI : IsEmpty {σ' : Multiset C.T.VType //
        σ' ∈ C.chain.Sigmas ∧ TIE.vBridge σ' = v} :=
      ⟨fun b => hex ⟨b.1, b.2.1, b.2.2⟩⟩
    rw [tsum_empty]
    exact TIE.blockTotal_supp Ŝ i v fun σ' hσ' hv => hex ⟨σ', hσ', hv⟩

end KCutK1Tie

/-- H8-C3 consumption display: the K1 regroup at the REAL transported β totals. -/
theorem kcut_k1_form {n : ℕ} (C : LeanUrat.MovesU.UCarriers n)
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E) (hdet : LeanUrat.MovesS.DetHyp C.T C.RB C.hK)
    (TIE : KCutK1Tie C R hdet)
    (graft : ∀ σ, R.CompatTuple σ → Fb.Tree σ)
    (graft_cut : ∀ σ (T : Fb.Tree σ), graft σ (R.cutFun σ T) = T)
    (cut_graft : ∀ σ (x : R.CompatTuple σ), R.cutFun σ (graft σ x) = x)
    (mass_eq : ∀ σ (T : Fb.Tree σ), Fb.mass σ T
      = R.W (R.shIdx σ T) * ∏ i, R.weight (R.shIdx σ T) i (R.cutBlk σ T i))
    (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : R.ShL, R.W Ŝ *
          ∑' vt : {vt : Fin (R.k Ŝ) → Multiset (ℕ × ℕ) //
              (R.shape Ŝ).σ0 + ∑ i, vt i = R.vOf σ},
            ∏ i, ∑' σ' : {σ' : Multiset C.T.VType //
                σ' ∈ C.chain.Sigmas ∧ TIE.vBridge σ' = vt.1 i},
              ENNReal.ofReal
                ((LeanUrat.MovesS.evalAt (p : ℚ)
                  ⟨_, TIE.bOK Ŝ i σ'.1 σ'.2.1⟩ : ℚ) : ℝ) :=
  (kcut_reduce R graft graft_cut cut_graft mass_eq σ).trans <|
    tsum_congr fun Ŝ =>
      congrArg (fun z => R.W Ŝ * z) <|
        tsum_congr fun vt =>
          Finset.prod_congr rfl fun i _ =>
            TIE.blockTotal_eq_tsum Ŝ i (vt.1 i)

/-- C2→C3 WIRE (task-directed, H8-C2 landed during this unit's run): an H8-C2
factorwise mass law (`KCutMassFactor`) SUPPLIES `kcut_k1_form`'s `mass_eq`
binder via `massFactor_mass_eq`, so the exact-form K1 regroup fires from the
factorwise law directly.  Statement = `kcut_k1_form` verbatim with the
`mass_eq` row replaced by `MF`; proof = pure composition, no new content. -/
theorem kcut_k1_form_of_massFactor {n : ℕ} (C : LeanUrat.MovesU.UCarriers n)
    {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} {E : History p F → Prop}
    (R : KCutReKeys Fb E) (hdet : LeanUrat.MovesS.DetHyp C.T C.RB C.hK)
    (TIE : KCutK1Tie C R hdet) (MF : KCutMassFactor R)
    (graft : ∀ σ, R.CompatTuple σ → Fb.Tree σ)
    (graft_cut : ∀ σ (T : Fb.Tree σ), graft σ (R.cutFun σ T) = T)
    (cut_graft : ∀ σ (x : R.CompatTuple σ), R.cutFun σ (graft σ x) = x)
    (σ : LeanUrat.MovesU.SplittingType n) :
    Fb.seriesSum σ
      = ∑' Ŝ : R.ShL, R.W Ŝ *
          ∑' vt : {vt : Fin (R.k Ŝ) → Multiset (ℕ × ℕ) //
              (R.shape Ŝ).σ0 + ∑ i, vt i = R.vOf σ},
            ∏ i, ∑' σ' : {σ' : Multiset C.T.VType //
                σ' ∈ C.chain.Sigmas ∧ TIE.vBridge σ' = vt.1 i},
              ENNReal.ofReal
                ((LeanUrat.MovesS.evalAt (p : ℚ)
                  ⟨_, TIE.bOK Ŝ i σ'.1 σ'.2.1⟩ : ℚ) : ℝ) :=
  kcut_k1_form C R hdet TIE graft graft_cut cut_graft
    (fun σ T => massFactor_mass_eq R MF σ T) σ

#print axioms kcut_k1_form
#print axioms KCutK1Tie.blockTotal_eq_tsum
#print axioms kcut_k1_form_of_massFactor

end LeanUrat.Scaffold.HDischarge.H8
