/-  TV-F1 (BRIDGE BP3, cluster c2; E-phase skeleton) — the RatBurdens PolyGeom
    DATA MAP in the CTS vocabulary.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F1).
    deps: none.  Consumers: TV-F2 (co-design seam), TV-F3 (interp/degree laws),
    TV-F4 (cellP wiring, Q5-ruled per-cell cp.count), TV-F5 (assembly at the
    shared measuredOf witness).
    Legs per the blueprint sketch:
      (a) tgP packs "from cp via dataOf/tblOf/pathProdPoly (V2-5)" — DATUM-keyed
          here (minimal resolution, recorded: an outcome of tableShape_inst's
          table is exactly a (s, m, o, α) tuple + a cont/terminal case split,
          i.e. a `MoveData`/`TermData`; the V2-5 `dataOf`/`tblOf` route recovers
          the same datum from a bare move through `moveOf_bij`, so keying the
          pack by the datum is the equivalent move-free form);
      (b) jP packs at split routes — the CELL SUM (jcell_sum forces
          jP := Σ_cells jPCell; the val-spec is displayed as `jPGof_val`);
      (c) jPCell := `jcellPG` (V5-7b) — PRESCRIBED BODY, transcribed verbatim;
          its countS = 1 leg is rfl (V7_rbA precedent, restated here);
      (d) ιP := choice over `ratBurdens_iota`'s ∃ (V7_rbB, proved) — PRESCRIBED
          BODY, transcribed verbatim with its two spec projections.
    CO-DESIGN PINS (recorded): `tgPGof_countT`/`tgPGofT_countT`/`jPGof_val` are
    F1-local typing-time pins on the sorried defs; the TV-F2 seam may adjust
    them (any adjustment is a statement change on THESE spec lemmas only, to be
    recorded at the F2 gate — never on the RatBurdens interface). -/
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V7_rbB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-! PROVER-LOCAL closure helpers (as-built record): duplicates of the PRIVATE
summed-denominator lemmas of MovesV/Defs.lean (`geomClass_ne_zero`,
`denom_dvd_of_add`, `denom_sum_dvd`, `geomClass_dvd_of_le`) and V5_jrat.lean
(`jrat_*`) — private in both homes, hence not importable; third local copy
recorded (the roll-up owner may hoist all three to one public home). -/

private theorem f1_geomClass_ne_zero (b : ℕ) (as : Finset ℕ+) :
    (Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) : Polynomial ℚ) ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have hc : (1 - Polynomial.X ^ (a : ℕ) : Polynomial ℚ).coeff (a : ℕ) = 0 := by
    rw [h]; simp
  rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  simp at hc

private theorem f1_geomClass_dvd_of_le {b b' : ℕ} {as as' : Finset ℕ+}
    (hb : b ≤ b') (hs : as ⊆ as') :
    (Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) : Polynomial ℚ)
      ∣ Polynomial.X ^ b' * ∏ a ∈ as', (1 - Polynomial.X ^ (a : ℕ)) :=
  mul_dvd_mul (pow_dvd_pow _ hb) (Finset.prod_dvd_prod_of_subset _ _ _ hs)

private theorem f1_denom_dvd_of_add {x y : MovesS.Qq} {L : Polynomial ℚ}
    (hL : L ≠ 0) (hx : x.denom ∣ L) (hy : y.denom ∣ L) : (x + y).denom ∣ L := by
  obtain ⟨px, hpx⟩ := (RatFunc.denom_dvd hL).mp hx
  obtain ⟨py, hpy⟩ := (RatFunc.denom_dvd hL).mp hy
  exact (RatFunc.denom_dvd hL).mpr ⟨px + py, by rw [hpx, hpy, map_add]; ring⟩

private theorem f1_denom_sum_dvd {ι : Type*} {L : Polynomial ℚ} (hL : L ≠ 0) :
    ∀ (s : Finset ι) (f : ι → MovesS.Qq), (∀ i ∈ s, (f i).denom ∣ L) →
    (∑ i ∈ s, f i).denom ∣ L := by
  classical
  intro s
  induction s using Finset.cons_induction with
  | empty => intro f _; simp
  | cons a s ha ih =>
      intro f hf
      rw [Finset.sum_cons]
      exact f1_denom_dvd_of_add hL (hf a (Finset.mem_cons_self a s))
        (ih f (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))))

open Classical in
/-- the PSigma packaging of `XHDs.Gc_denom`'s choose data (the `gcellDenom`
pattern of Defs, at the TEMPLATE face). -/
private noncomputable def f1_gcDenom {n : ℕ} {S : StepSys n} {W : XHDw n S}
    {TE : TmplEvents n S} {D : XHDd n S TE} (Xs : XHDs n S W D)
    {α : S.Cell} (γ : Template n S α) (j : Fin (D.dom γ).comps.length) :
    Σ' (b : ℕ) (as : Finset ℕ+),
      (Xs.Gc γ j).denom
        ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) :=
  ⟨(Xs.Gc_denom γ j).choose, (Xs.Gc_denom γ j).choose_spec.choose,
   (Xs.Gc_denom γ j).choose_spec.choose_spec⟩

open Classical in
/-- the summed template-face height pack: countT/countS as given, geom := the
`Gc`-component sum of the one-step template γ (the `gcell_denom_sum` closure
pattern at the template face). -/
private noncomputable def f1_tmplPack {n : ℕ} {S : StepSys n} {W : XHDw n S}
    {TE : TmplEvents n S} {D : XHDd n S TE} (Xs : XHDs n S W D)
    {α : S.Cell} (γ : Template n S α)
    (countT : Polynomial ℚ) (degBoundT : ℕ) (degT_le : countT.natDegree ≤ degBoundT)
    (degBoundS : ℕ) : MovesS.PolyGeom :=
  { countT := countT
    degBoundT := degBoundT
    degT_le := degT_le
    countS := 1
    degBoundS := degBoundS
    degS_le := by simp
    geom := ∑ j, Xs.Gc γ j
    qpow := Finset.univ.sup (fun j : Fin (D.dom γ).comps.length =>
      (f1_gcDenom Xs γ j).1)
    geomDenoms := Finset.univ.biUnion (fun j : Fin (D.dom γ).comps.length =>
      (f1_gcDenom Xs γ j).2.1)
    geom_denom_dvd := f1_denom_sum_dvd (f1_geomClass_ne_zero _ _) _ _
      (fun j _ => dvd_trans (f1_gcDenom Xs γ j).2.2
        (f1_geomClass_dvd_of_le
          (Finset.le_sup (f := fun j : Fin (D.dom γ).comps.length =>
            (f1_gcDenom Xs γ j).1) (Finset.mem_univ j))
          (Finset.subset_biUnion_of_mem
            (fun j : Fin (D.dom γ).comps.length =>
              (f1_gcDenom Xs γ j).2.1) (Finset.mem_univ j)))) }

/-- TV-F1(a) [tg pack, continuing datum]: the (iv)-POLY pack presenting the
measured row value of the continuing outcome datum `d` (consumed by
`tg_interp` at non-split routes).  countT = the datum's own T-table entry
(the `tblOf` reading, pinned by `tgPGof_countT` below); countS = the
state-count leg and geom = the XHD-s height-sum leg are co-designed with
`rowVal` at the TV-F2 seam.  Sketch: transcribe `jcellPG`'s pack pattern at
the outcome level, with `cp`'s count polynomial aggregated over the outcome's
cell fiber and the `Gcell` height sums summed per `gcell_denom_sum`.
deps: none (V2-5 + V5-7b machinery, all proved). -/
noncomputable def tgPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C) : MovesS.PolyGeom :=
  -- AS-BUILT (recorded deviation from the docstring's sketch line, per the
  -- blueprint §4 TV-F1 "tgP … via dataOf/tblOf/pathProdPoly (V2-5)"): the
  -- T-count leg is the datum's TABLE polynomial (the `tblOf` reading — the
  -- `tgPGof_countT` pin, rfl) and the height leg is the MOVE-level template
  -- sum Σⱼ Gc(.last (moveOf d)) — NOT the cell-fiber Gcell aggregate: pairing
  -- the fiber's per-cell counts with per-cell height sums cannot factor
  -- through PolyGeom's countT·countS·geom product with countT pinned to C.T
  -- (it would double-count), while C.T · Σⱼ Gc IS the row value's T-poly
  -- reading (val_b/V2-5); its tie to E2's μcell-sum `rowVal` is the E5a-genre
  -- bridge, owned by the TV-F2 seam laws at the shared witness.
  f1_tmplPack X.s (.last (V.moveOf d))
    (C.T d.s d.m d.o d.α d.tix) (C.Wloc d.s d.m)
    (C.T_deg d.s d.m d.o d.α d.tix) ((C.bd d.s).Wstate)

/-- TV-F1(a′) [tg pack, terminal datum]: the terminal twin of `tgPGof`
(`tblOfT` reading, `GcellT` height sums). -/
noncomputable def tgPGofT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {v : VLabel n} (d : TermData n C v) :
    MovesS.PolyGeom :=
  f1_tmplPack X.s (.lastT (V.moveOfT d))
    (C.T d.s d.m d.o d.α d.tix) (C.Wloc d.s d.m)
    (C.T_deg d.s d.m d.o d.α d.tix) ((C.bd d.s).Wstate)

/-- TV-F1 pin: `tgPGof`'s T-count leg IS the datum's table entry (the
`tblOf`/`dataOf` reading collapsed through `moveOf_bij` to the datum key).
CO-DESIGN PIN — adjustable only at the TV-F2 seam, with a record. -/
theorem tgPGof_countT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C) :
    (tgPGof V X cp d).countT = C.T d.s d.m d.o d.α d.tix :=
  rfl

/-- TV-F1 pin, terminal twin. -/
theorem tgPGofT_countT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) {v : VLabel n} (d : TermData n C v) :
    (tgPGofT V X cp d).countT = C.T d.s d.m d.o d.α d.tix :=
  rfl

/-- TV-F1(c) [jPCell wiring]: PRESCRIBED BODY — "jPCell := jcellPG" (blueprint
§3.E; V5-7b's per-cell pack through `cp` and the XHD-s cell face). -/
noncomputable def jCellPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) : MovesS.PolyGeom :=
  jcellPG cp X.sC d c

/-- TV-F1(c) countS = 1 leg (the V7_rbA `ratBurdens_tg_j` precedent, restated
at the F1 wiring; rfl at `jcellPG`'s literal countS := 1 field). -/
theorem jCellPGof_countS_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (d : MoveData n C)
    (c : V.DCellO d.s d.m d.o d.α) :
    (jCellPGof X cp d c).countS = 1 :=
  rfl

/-- TV-F1(b) [j pack, split route]: the per-outcome J pack — jcell_sum FORCES
its val to be the cell sum, so it is DEFINED as (a pack presenting) that sum;
the val-spec is `jPGof_val`.  Sketch: common-denominator assembly over the
outcome's `J.bcells` roster via `gcell_denom_sum`'s closure pattern (the
summed-denominator lemma already proved in Defs). -/
noncomputable def jPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V) (d : MoveData n C) :
    MovesS.PolyGeom :=
  -- the V5-7b `jRat` pack, made DEFINITIONAL (the ∃-witness of jRat is a
  -- choice-opaque term; the gate deliverable wants `jcell_sum` rfl-genre, so
  -- the same literal is re-materialized here): geom := the bcells-roster sum
  -- of the per-cell pack values (empty at non-split routes by `roster_tie`,
  -- making `jPGof_val` total).
  { countT := 1
    degBoundT := C.Wloc d.s d.m
    degT_le := by simp
    countS := 1
    degBoundS := (C.bd d.s).Wstate
    degS_le := by simp
    geom := ∑ c ∈ J.bcells d.s d.m d.o d.α, (jCellPGof X cp d c).val
    qpow := (J.bcells d.s d.m d.o d.α).sup
      (fun c => (jCellPGof X cp d c).qpow)
    geomDenoms := (J.bcells d.s d.m d.o d.α).biUnion
      (fun c => (jCellPGof X cp d c).geomDenoms)
    geom_denom_dvd := f1_denom_sum_dvd (f1_geomClass_ne_zero _ _) _ _
      (fun c hc => by
        refine dvd_trans (dvd_trans ?_ (jCellPGof X cp d c).geom_denom_dvd)
          (f1_geomClass_dvd_of_le
            (Finset.le_sup (f := fun c => (jCellPGof X cp d c).qpow) hc)
            (Finset.subset_biUnion_of_mem
              (fun c => (jCellPGof X cp d c).geomDenoms) hc))
        have hh := RatFunc.denom_mul_dvd
          (algebraMap (Polynomial ℚ) MovesS.Qq (cp.P d.s d.m d.o d.α c * 1))
          (jCellPGof X cp d c).geom
        rw [RatFunc.denom_algebraMap, one_mul] at hh
        exact hh) }

/-- TV-F1(b) val-spec: `jPGof`'s value IS the cell sum of the jPCell values
over the split-route roster (the jcell_sum candidate, displayed at F1 and
type-checked here per the TV-F2 gate deliverable; blueprint §3.E "jcell_sum
forces jP := the cell sum — co-design jP as that sum").
CO-DESIGN PIN — adjustable only at the TV-F2 seam, with a record. -/
theorem jPGof_val {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V) (d : MoveData n C) :
    (jPGof V X cp J d).val
      = ∑ c ∈ J.bcells d.s d.m d.o d.α, (jCellPGof X cp d c).val := by
  simp only [MovesS.PolyGeom.val, jPGof, mul_one, map_one, one_mul]

/-- TV-F1(d) [ιP]: PRESCRIBED BODY — "ιP := choice over ratBurdens_iota's ∃"
(blueprint §4 TV-F1; the ∃ is PROVED at V7_rbB from `initRat_comp`). -/
noncomputable def iotaPGof {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    MovesS.PolyGeom :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose

/-- TV-F1(d) spec, countS leg (choose_spec projection of the proved ∃). -/
theorem iotaPGof_countS_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    (iotaPGof V X hEU hEC hA hdom β₀ i).countS = 1 :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose_spec.1

/-- TV-F1(d) spec, geom leg: the weight-only entrance geometry `Gent`. -/
theorem iotaPGof_geom {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (hdom : EntDomOrder0 V) (β₀ : S.Cell) (i : V.EntIx β₀) :
    (iotaPGof V X hEU hEC hA hdom β₀ i).geom = X.sEnt.Gent β₀ i :=
  (ratBurdens_iota V X hEU hEC hA hdom β₀ i).choose_spec.2

end LeanUrat.MovesV
