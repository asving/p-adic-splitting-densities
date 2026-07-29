/-  MovesV unit V2-5 `val_b_chain` (RESTATED C2/C9) — VAL(b) GIVEN (XHD-u)'s
    count face over the DEFINED chainCount.  `dataOf`/`tblOf`/`pathProdPoly`
    are DISPLAYED here (V-keyed: an abstract move's datum is recovered through
    `moveOf_bij` — recorded deviation: the blueprint's `pathProdPoly C γ`
    notation reads the family through V's bijections). -/
import LeanUrat.MovesV.V1_xhdd
import LeanUrat.MovesV.V2_valA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the datum behind a bare continuing move (the inverse of `moveOf_bij`). -/
noncomputable def dataOf {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc βc : S.Cell} (mv : S.Move αc βc) :
    {d : MoveData n C // V.toStepCells.symm d.src = αc} :=
  haveI : Nonempty {d : MoveData n C // V.toStepCells.symm d.src = αc} :=
    ⟨((V.moveOf_bij αc).2 ⟨βc, mv⟩).choose⟩
  Function.invFun
    (fun d : {d : MoveData n C // V.toStepCells.symm d.src = αc} =>
      (⟨V.toStepCells.symm d.1.tgt, castMove d.2 rfl (V.moveOf d.1)⟩ :
        Σ β, S.Move αc β)) ⟨βc, mv⟩

/-- the datum behind a bare terminal move. -/
noncomputable def dataOfT {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {v : VLabel n} (mv : S.MoveT αc v) :
    {d : TermData n C v // V.toStepCells.symm ⟨d.s, d.α⟩ = αc} :=
  haveI : Nonempty {d : TermData n C v // V.toStepCells.symm ⟨d.s, d.α⟩ = αc} :=
    ⟨((V.moveOfT_bij αc v).2 mv).choose⟩
  Function.invFun
    (fun d : {d : TermData n C v // V.toStepCells.symm ⟨d.s, d.α⟩ = αc} =>
      castMoveT d.2 (V.moveOfT d.1)) mv

/-- the datum's table polynomial at a bare move (NAME→HOME: `tblOf`). -/
noncomputable def tblOf {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc βc : S.Cell} (mv : S.Move αc βc) :
    Polynomial ℚ :=
  C.T (dataOf V mv).1.s (dataOf V mv).1.m (dataOf V mv).1.o (dataOf V mv).1.α
    (dataOf V mv).1.tix

noncomputable def tblOfT {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {v : VLabel n} (mv : S.MoveT αc v) :
    Polynomial ℚ :=
  C.T (dataOfT V mv).1.s (dataOfT V mv).1.m (dataOfT V mv).1.o
    (dataOfT V mv).1.α (dataOfT V mv).1.tix

/-- THE PATH PRODUCT C_γ(q) = ∏ᵢ T (the TABLE polynomials' product). -/
noncomputable def pathProdPoly {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : ∀ {α}, Template n S α → Polynomial ℚ
  | _, .last mv => tblOf V mv
  | _, .lastT mv => tblOfT V mv
  | _, .cons mv γ => tblOf V mv * pathProdPoly V γ

/-- the template weight bound W(γ) (NAME→HOME: `Wtmpl`, V5-3's key). -/
noncomputable def Wtmpl {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : ∀ {α}, Template n S α → ℕ
  | _, .last mv => C.Wloc (dataOf V mv).1.s (dataOf V mv).1.m
  | _, .lastT mv => C.Wloc (dataOfT V mv).1.s (dataOfT V mv).1.m
  | _, .cons mv γ => C.Wloc (dataOf V mv).1.s (dataOf V mv).1.m + Wtmpl V γ

/-- (a) the (u-R)-resolved chain count is representative-uniform (the
state-only-factors content, rep-independence form — deviation recorded:
the per-step `hProd` product presentation is deferred to the prover). -/
theorem chain_resolved {n} {S : StepSys n} (U : XHDu n S) {α}
    (γ : Template n S α) {q₀} (hq : q₀ ∈ S.Pools)
    (x x' : S.Hist q₀ α) (hzc : S.zc x) (hzc' : S.zc x') (h : Hpt γ.D) :
    chainCount S γ x h = chainCount S γ x' h := by
  induction γ with
  | last m => exact U.u_R_cnt m x x' h hq hzc hzc'
  | lastT m => exact U.u_R_cntT m x x' h hq hzc hzc'
  | cons m γ ih =>
    obtain ⟨z, hz⟩ := S.zc_ne q₀ hq _
    have key : ∀ (y : S.Hist q₀ _) (hy : S.zc y),
        chainCount S (.cons m γ) y h
          = S.cntraw m y (Hpt.take h) • chainCount S γ z (Hpt.drop h) := by
      intro y hy
      have hconst : ∀ a : S.Assign m y (Hpt.take h),
          chainCount S γ (S.ext m y (Hpt.take h) a) (Hpt.drop h)
            = chainCount S γ z (Hpt.drop h) :=
        fun a => ih (S.ext m y (Hpt.take h) a) z
          (S.ext_zc m y (Hpt.take h) a hy) hz (Hpt.drop h)
      simp only [chainCount, hconst, Finset.sum_const, Finset.card_univ,
        StepSys.cntraw]
    rw [key x hzc, key x' hzc', U.u_R_cnt m x x' (Hpt.take h) hq hzc hzc']

/-- (b) VAL(b): the linked count EQUALS the path product, GIVEN ValA +
(XHD-u) + XHD-d + MDomTie. -/
theorem valB {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (h : Hpt γ.D) (hmem : (D.dom γ).Mem h) :
    (chainCount S γ x h : ℚ) = (pathProdPoly V γ).eval q₀ := by
  sorry

/-- (c) the degree bound (RE-SCOPED C9): a POLYNOMIAL-degree statement. -/
theorem pathProd_deg {n} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {α} (γ : Template n S α) :
    (pathProdPoly V γ).natDegree ≤ Wtmpl V γ := by
  induction γ with
  | last mv => exact C.T_deg _ _ _ _ _
  | lastT mv => exact C.T_deg _ _ _ _ _
  | cons mv γ ih =>
    refine (Polynomial.natDegree_mul_le).trans ?_
    exact Nat.add_le_add (C.T_deg _ _ _ _ _) ih

end LeanUrat.MovesV
