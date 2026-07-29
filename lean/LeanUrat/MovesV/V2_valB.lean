/-  MovesV unit V2-5 `val_b_chain` (RESTATED C2/C9; M2-ADJUDICATED at the
    final-ratification repair, 2026-07-29) — the TABLE-SIDE product lemma
    `val_b_table` (chainCount = path product; formerly misnamed `valB`),
    PLUS the note's VAL(b) `val_b` (Tgam-keyed) behind the NAMED
    `RealizationComplete` row (owner XHD/[2b]; content witnessed by the
    coupling toy).  `dataOf`/`tblOf`/`pathProdPoly` are DISPLAYED here
    (V-keyed: an abstract move's datum is recovered through `moveOf_bij` —
    recorded deviation: the blueprint's `pathProdPoly C γ` notation reads
    the family through V's bijections). -/
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

/-- a component's own base is a member of that linear set (the zero-coefficient
witness). -/
theorem LinSet.base_mem {D : ℕ} (L : LinSet D) : L.Mem L.base :=
  ⟨fun _ => 0, by funext i; simp⟩

/-- the count at a bare CONTINUING move, VALUED by the datum's table entry, GIVEN
the move is realized (positive count).  The datum-keyed core: `dd` is the inverse
image under `moveOf_bij`, and the `cases hd`/`cases hfd` idiom collapses the
cell/move casts (mirrors `castAssignKey`). -/
theorem cntraw_datum {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {αc βc : S.Cell}
    (d : MoveData n C) (hsrc : V.toStepCells.symm d.src = αc)
    (m : S.Move αc βc) {q₀} (x : S.Hist q₀ αc) (h : Hpt (S.dim m))
    (hfd : (⟨V.toStepCells.symm d.tgt, castMove hsrc rfl (V.moveOf d)⟩ :
        Σ βc, S.Move αc βc) = ⟨βc, m⟩)
    (hzc : S.zc x) (hq : q₀ ∈ V.Pools) (hpos : 0 < S.cntraw m x h) :
    (S.cntraw m x h : ℚ)
      = (C.T d.s d.m d.o d.α d.tix).eval q₀ := by
  subst hsrc
  dsimp only [castMove] at hfd
  cases hfd
  have hq' : q₀ ∈ S.Pools := V.pools_sub hq
  -- h is a realized point of the datum's mdom:
  have hMem_h : (V.mdom d).Mem h := by
    rw [← hTie.mdom_eq d]
    refine D.no_orphan (.last (V.moveOf d)) x h hq' hzc ?_
    rw [tgam_last TE (V.moveOf d) x h hq' hzc]; exact hpos
  obtain ⟨L, hL, -⟩ := hMem_h
  obtain ⟨j, hj⟩ := List.get_of_mem hL
  -- the base of that component is realized too:
  have hpos_base : 0 < S.cntraw (V.moveOf d) x (((V.mdom d).comps.get j).base) := by
    have hmb : (D.dom (.last (V.moveOf d))).Mem (((V.mdom d).comps.get j).base) := by
      rw [hTie.mdom_eq d]
      exact ⟨(V.mdom d).comps.get j, List.get_mem _ _, LinSet.base_mem _⟩
    have hb := D.no_stray (.last (V.moveOf d)) _ hmb hq' x hzc
    rwa [tgam_last TE (V.moveOf d) x _ hq' hzc] at hb
  -- transport the count to the base point and value it:
  rw [U.u_T (V.moveOf d) x h (((V.mdom d).comps.get j).base) hq' hzc hpos hpos_base]
  exact (hVA.tbl_count d x hzc hq j).symm

/-- terminal twin of `cntraw_datum`. -/
theorem cntrawT_datum {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {αc : S.Cell} {v : VLabel n}
    (d : TermData n C v) (hsrc : V.toStepCells.symm ⟨d.s, d.α⟩ = αc)
    (m : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc) (h : Hpt (S.dimT m))
    (hfd : (castMoveT hsrc (V.moveOfT d) : S.MoveT αc v) = m)
    (hzc : S.zc x) (hq : q₀ ∈ V.Pools) (hpos : 0 < S.cntrawT m x h) :
    (S.cntrawT m x h : ℚ)
      = (C.T d.s d.m d.o d.α d.tix).eval q₀ := by
  subst hsrc
  dsimp only [castMoveT] at hfd
  cases hfd
  have hq' : q₀ ∈ S.Pools := V.pools_sub hq
  have hMem_h : (V.mdomT d).Mem h := by
    rw [← hTie.mdomT_eq d]
    refine D.no_orphan (.lastT (V.moveOfT d)) x h hq' hzc ?_
    rw [tgam_lastT TE (V.moveOfT d) x h hq' hzc]; exact hpos
  obtain ⟨L, hL, -⟩ := hMem_h
  obtain ⟨j, hj⟩ := List.get_of_mem hL
  have hpos_base : 0 < S.cntrawT (V.moveOfT d) x (((V.mdomT d).comps.get j).base) := by
    have hmb : (D.dom (.lastT (V.moveOfT d))).Mem (((V.mdomT d).comps.get j).base) := by
      rw [hTie.mdomT_eq d]
      exact ⟨(V.mdomT d).comps.get j, List.get_mem _ _, LinSet.base_mem _⟩
    have hb := D.no_stray (.lastT (V.moveOfT d)) _ hmb hq' x hzc
    rwa [tgam_lastT TE (V.moveOfT d) x _ hq' hzc] at hb
  rw [U.u_TT (V.moveOfT d) x h (((V.mdomT d).comps.get j).base) hq' hzc hpos hpos_base]
  exact (hVA.tbl_countT d x hzc hq j).symm

/-- the count at a bare CONTINUING move EQUALS its table polynomial's value,
whenever the move is realized (positive count). -/
theorem base_eq {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {αc βc : S.Cell} (m : S.Move αc βc) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dim m)) (hzc : S.zc x) (hq : q₀ ∈ V.Pools)
    (hpos : 0 < S.cntraw m x h) :
    (S.cntraw m x h : ℚ) = (tblOf V m).eval q₀ := by
  haveI : Nonempty {d : MoveData n C // V.toStepCells.symm d.src = αc} :=
    ⟨((V.moveOf_bij αc).2 ⟨βc, m⟩).choose⟩
  have hfd : (⟨V.toStepCells.symm (dataOf V m).1.tgt,
        castMove (dataOf V m).2 rfl (V.moveOf (dataOf V m).1)⟩ :
        Σ βc, S.Move αc βc) = ⟨βc, m⟩ :=
    Function.invFun_eq ((V.moveOf_bij αc).2 ⟨βc, m⟩)
  exact cntraw_datum hVA U hTie (dataOf V m).1 (dataOf V m).2 m x h hfd hzc hq hpos

/-- terminal twin of `base_eq`. -/
theorem base_eqT {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {αc : S.Cell} {v : VLabel n} (m : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dimT m)) (hzc : S.zc x) (hq : q₀ ∈ V.Pools)
    (hpos : 0 < S.cntrawT m x h) :
    (S.cntrawT m x h : ℚ) = (tblOfT V m).eval q₀ := by
  haveI : Nonempty {d : TermData n C v // V.toStepCells.symm ⟨d.s, d.α⟩ = αc} :=
    ⟨((V.moveOfT_bij αc v).2 m).choose⟩
  have hfd : (castMoveT (dataOfT V m).2 (V.moveOfT (dataOfT V m).1) : S.MoveT αc v) = m :=
    Function.invFun_eq ((V.moveOfT_bij αc v).2 m)
  exact cntrawT_datum hVA U hTie (dataOfT V m).1 (dataOfT V m).2 m x h hfd hzc hq hpos

/-- (b′) VAL(b) over POSITIVE chain counts (the induction carrier): the count
decomposes stepwise, each factor valued by `base_eq`, rep-independence collapsing
the tail sum (via `chain_resolved`). -/
theorem valB_aux {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {α} (γ : Template n S α) {q₀} (hq : q₀ ∈ V.Pools) :
    ∀ (x : S.Hist q₀ α) (_ : S.zc x) (h : Hpt γ.D),
      0 < chainCount S γ x h →
      (chainCount S γ x h : ℚ) = (pathProdPoly V γ).eval q₀ := by
  induction γ with
  | last m => intro x hzc h hpos; exact base_eq hVA U hTie m x h hzc hq hpos
  | lastT m => intro x hzc h hpos; exact base_eqT hVA U hTie m x h hzc hq hpos
  | cons m γ' ih =>
    intro x hzc h hpos
    have hq' : q₀ ∈ S.Pools := V.pools_sub hq
    letI : Fintype (S.Assign m x (Hpt.take h)) := S.finA m x (Hpt.take h)
    have hposS : 0 < ∑ a : S.Assign m x (Hpt.take h),
        chainCount S γ' (S.ext m x (Hpt.take h) a) (Hpt.drop h) := hpos
    obtain ⟨a₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hposS.ne'
    have hconst : ∀ a : S.Assign m x (Hpt.take h),
        chainCount S γ' (S.ext m x (Hpt.take h) a) (Hpt.drop h)
          = chainCount S γ' (S.ext m x (Hpt.take h) a₀) (Hpt.drop h) := fun a =>
      chain_resolved U γ' hq' _ _
        (S.ext_zc m x (Hpt.take h) a hzc) (S.ext_zc m x (Hpt.take h) a₀ hzc) (Hpt.drop h)
    have hsum : chainCount S (Template.cons m γ') x h
        = S.cntraw m x (Hpt.take h)
          * chainCount S γ' (S.ext m x (Hpt.take h) a₀) (Hpt.drop h) := by
      conv_lhs => rw [chainCount]
      rw [Finset.sum_congr rfl (fun a _ => hconst a), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
      rfl
    have hK : 0 < S.cntraw m x (Hpt.take h) := by
      rcases Nat.eq_zero_or_pos (S.cntraw m x (Hpt.take h)) with h0 | hp
      · rw [hsum, h0, Nat.zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact hp
    have hT : 0 < chainCount S γ' (S.ext m x (Hpt.take h) a₀) (Hpt.drop h) := by
      rcases Nat.eq_zero_or_pos
        (chainCount S γ' (S.ext m x (Hpt.take h) a₀) (Hpt.drop h)) with h0 | hp
      · rw [hsum, h0, Nat.mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact hp
    have hbase := base_eq hVA U hTie m x (Hpt.take h) hzc hq hK
    have htail := ih (S.ext m x (Hpt.take h) a₀)
      (S.ext_zc m x (Hpt.take h) a₀ hzc) (Hpt.drop h) hT
    rw [hsum]
    simp only [pathProdPoly, Polynomial.eval_mul, Nat.cast_mul]
    rw [hbase, htail]

/-- (b-table) the table-side product lemma — INTERNAL as of the round-4 M2
re-key (2026-07-29): NOT a capstone export; the capstone's `ValB_Stmt` is
the Tgam-keyed `val_b` below, and this lemma is its table-side half.  The
ASSIGNMENT-CHAIN count `chainCount` equals the path product, GIVEN ValA +
(XHD-u) + XHD-d + MDomTie.  This is NOT the note's VAL(b) — the note's
T_γ(x, h) counts chains REALIZING (γ, h), i.e. `Tgam`/the `RealizesC`
subtype, and only `Tgam ≤ chainCount` (`marks_chains`) is unconditional;
the bridge is the named `RealizationComplete` row below.
(Old name `valB`; renamed at the M2 repair.) -/
theorem val_b_table {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (h : Hpt γ.D) (hmem : (D.dom γ).Mem h) :
    (chainCount S γ x h : ℚ) = (pathProdPoly V γ).eval q₀ :=
  valB_aux hVA U hTie γ hq x hzc h
    (mem_chainCount_pos D γ h hmem (V.pools_sub hq) x hzc)

/-- REALIZATION COMPLETENESS (M2, THE NAMED OPEN ROW — owner XHD/[2b]; a
`CtsmLedger` field as of the round-4 re-key): every assignment chain is
process-realized by a mark, i.e. the mark reading `tmark` is SURJECTIVE
onto `Chains` at zc histories over pools.  The premise HAS CONTENT: the
coupling toy (`coupling_signature`, V4_hmc) exhibits a (TmplEvents, point)
with `0 < chainCount` and `Tgam = 0`, so no unconditional proof exists.
OWNERSHIP (round-4 verdict fix): the entrance face's no-stray laws do NOT
discharge this row — no-stray/positivity yields only that at least one
realized mark exists at each in-domain point (`0 < Tgam`), NOT that `tmark`
is surjective onto every combinatorial `Chains` element; the Phase-B
discharge needs a genuine mark-per-chain construction at the real instance
(owner XHD/[2b]). -/
def RealizationComplete {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) : Prop :=
  ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → Function.Surjective (TE.tmark γ x h)

/-- under REALIZATION COMPLETENESS the two counts coincide (tmark bijective:
`tmark_inj` + the row). -/
theorem tgam_eq_chainCount_of_complete {n} {S : StepSys n}
    (TE : TmplEvents n S) (hRC : RealizationComplete TE) {α}
    (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE γ x h = chainCount S γ x h := by
  have hinj := TE.tmark_inj γ x h hq hzc
  have hsurj := hRC γ x h hq hzc
  rw [Tgam, ← chains_card S γ x h,
    ← Fintype.card_coe (TE.tinst γ x h (TE.tmplLvl γ))]
  exact Fintype.card_congr (Equiv.ofBijective (TE.tmark γ x h) ⟨hinj, hsurj⟩)

/-- (b) THE NOTE'S VAL(b), Tgam-keyed (M2 adjudication): the REALIZED count
T_γ = `Tgam` equals the path product — the table-side lemma THROUGH the
`RealizationComplete` premise. -/
theorem val_b {n} {C : CtsFamily n} {S : StepSys n} {V : CtsMeasured n C S}
    {TE : TmplEvents n S} {D : XHDd n S TE}
    (hVA : ValA n C S V) (U : XHDu n S) (hTie : MDomTie V TE D)
    (hRC : RealizationComplete TE)
    {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (h : Hpt γ.D) (hmem : (D.dom γ).Mem h) :
    (Tgam TE γ x h : ℚ) = (pathProdPoly V γ).eval q₀ := by
  rw [tgam_eq_chainCount_of_complete TE hRC γ x h (V.pools_sub hq) hzc]
  exact val_b_table hVA U hTie γ x hzc hq h hmem

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
