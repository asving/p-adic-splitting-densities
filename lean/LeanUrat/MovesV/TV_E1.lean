/-  TV-E1 (BRIDGE BP3, cluster c4; E-phase skeleton) — `measuredOf` DATA
    BLOCK 1: the shared (V, X, cp)-keyed `MovesS.MeasuredSide` construction
    over the LITERAL tableShape_inst table.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E1).
    deps: none.  Consumers: TV-E2 (data block 2), TV-E3/E4/E5a/E5b/E6 (the
    LedgerIV law groups), TV-E7 (assembly), TV-E8 (non-vacuity gate), and
    cluster F (TV-F2/F5 — the Q5-RULED SHARED witness).
    E-PHASE RESOLUTIONS (recorded per the statement-writer charge):
    (1) `tableShape_inst` (V7_ts:69) is an ∃-THEOREM, but the §3.E field map
        reads the table DEFINITIONALLY ("τ : T.State e = StateOf n C e =
        ⟨⟨s, α⟩, hblk⟩ and T.Out e τ = Σ m, Outc m — the tableShape_inst
        witness is literal, all equivs Equiv.refl").  A choice-extracted
        witness has no definitional face, so the witness is re-materialized
        VERBATIM as the def `ctsTable` below (body = tableShape_inst's own
        structure literal, V7_ts:100-131); `ctsTable_pins` restates its
        proved TablePins bundle.  Additive only — V7_ts is untouched.
    (2) `measuredOf` spans BOTH data blocks (a structure literal cannot be
        split across units): TV-E1 owns the def + the block-1 field pins;
        TV-E2 pins block 2 (entrance/kstep/activity) on the SAME def.
    (3) The prescribed field values ride as CO-DESIGN PIN lemmas (sorried,
        rfl-genre at the intended literal — the TV-F1 precedent); pins whose
        statement needs a cast across a pinned carrier equality (cellOut,
        μcell, cellEvt, Rep, cellLvl/cellInst, HDom) are NOT pre-typed:
        [REV 2, finding 13] the transport/equality lemma layer (Sigma-cell
        casts, double-dite definedness case lemmas, toStepCells transport)
        is the E-fleet's execution deliverable, with the pre-authorized
        E1a (carriers) / E1b (transport lemmas) split if over budget. -/
import LeanUrat.MovesV.V7_ts
import LeanUrat.MovesV.V4_part1A
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV

/-- TV-E1 [table carrier]: THE literal `tableShape_inst` witness as a DEF —
`State := StateOf n C` (the CellIdx-carrying block-e slice), `Out :=
Σ letter, outcome`, the REAL bounds `Wloc := C.Wloc` / `Wstate :=
(C.bd s).Wstate`, odata rosters through the attach map (all transcribed
verbatim from V7_ts:100-131, which compiled green).  `T := ctsTable C hfin`
is the ONE table every E/F-cluster unit shares (Q5 ruling).  deps: none. -/
noncomputable def ctsTable {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) : MovesS.TableShape n where
  State := StateOf n C
  fin := fun e => by
    haveI := hfin
    have : Finite (StateOf n C e) := by unfold StateOf; infer_instance
    exact Fintype.ofFinite _
  deq := fun e => Classical.decEq _
  VType := VLabel n
  deqV := inferInstance
  finV := by
    haveI := hfin
    apply Fintype.ofInjective
      (β := Fin (n + 1) × Fin (n + 1))
      (fun v : VLabel n =>
        (⟨(v.1.1 : ℕ), by
            have h1 : ((v.1.1 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_right _ v.1.2.pos
            have := v.2; omega⟩,
         ⟨(v.1.2 : ℕ), by
            have h2 : ((v.1.2 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_left _ v.1.1.pos
            have := v.2; omega⟩))
    intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    apply Subtype.ext
    apply Prod.ext
    · exact PNat.coe_injective hab.1
    · exact PNat.coe_injective hab.2
  vdeg := fun v => v.1.1 * v.1.2
  vEquiv := Equiv.refl _
  vdeg_spec := by intro v; simp [PNat.mul_coe]
  Out := fun _ τ => Σ m : (C.bd τ.1.1).Letter, (C.bd τ.1.1).Outc m
  finO := by
    intro e τ
    haveI := (C.bd τ.1.1).finL
    haveI := (C.bd τ.1.1).finO
    infer_instance
  odata := fun _ τ o =>
    { mem := ((C.bd τ.1.1).omem o.1 o.2).attach.map (fun x =>
        { size := x.1.size
          δ := x.1.δ
          status := match hs : x.1.status with
            | Sum.inl v => Sum.inl v
            | Sum.inr sk => Sum.inr
                ⟨⟨sk, memberTgtCell C τ.1.2 x.1 x.2 hs⟩,
                  (C.bd τ.1.1).omem_size o.1 o.2 x.1 x.2 sk hs⟩ })
      hm := by
        have hne := (C.bd τ.1.1).omem_ne o.1 o.2
        intro hcontra
        apply hne
        simpa using hcontra }
  Wloc := fun _ τ o => C.Wloc τ.1.1 o.1
  Wstate := fun _ τ => (C.bd τ.1.1).Wstate

/-- TV-E1 [table pins]: `TablePins C (ctsTable C hfin)` — the proved bundle of
`tableShape_inst`, restated at the def.  Sketch: verbatim the first bullet of
tableShape_inst's proof (every equiv `Equiv.refl`, weight ties `rfl`, odata
tie through the attach map; V7_ts:132-147).  Supplies TV-E7's TablePins
conjunct.  deps: ctsTable. -/
theorem ctsTable_pins {n : ℕ} (C : CtsFamily n) (hfin : Finite (Skeleton n)) :
    TablePins C (ctsTable C hfin) := by
  refine ⟨Equiv.refl _, fun e => Equiv.refl _, fun e τ => rfl,
    fun e τ => ⟨Equiv.refl _, fun o => rfl, fun o => ?_⟩⟩
  simp only [Equiv.coe_refl, id_eq]
  show (((C.bd τ.1.1).omem o.1 o.2).attach.map _).map _ = _
  rw [List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_attach]; rfl
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_attach, Function.comp_apply]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    -- the status component: cases on the roster member's status
    split
    · next v heq => simp only [Sum.map_inl, id_eq]; exact heq.symm
    · next sk heq => simp only [Sum.map_inr]; exact heq.symm

/-- TV-E1 [roster nonemptiness]: the odata rosters of `ctsTable` are nonempty
(the second conjunct of `tableShape_inst`; proof = each odata's own `hm`). -/
theorem ctsTable_odata_ne {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e) (o : (ctsTable C hfin).Out e τ),
      ((ctsTable C hfin).odata e τ o).mem ≠ [] :=
  fun e τ o => ((ctsTable C hfin).odata e τ o).hm

/-- TV-E1 [the cell carrier, §3.E display]: `Cell e τ := Σ o : T.Out e τ,
DCellO s o.1 o.2 α` at τ = ⟨⟨s, α⟩, hblk⟩ — the per-outcome digit-cell fibers
of the CTS classifier (`cellOut := Sigma.fst` across this carrier). -/
def measCell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hfin : Finite (Skeleton n))
    (e : ℕ) (τ : (ctsTable C hfin).State e) : Type :=
  Σ o : (ctsTable C hfin).Out e τ, V.DCellO τ.1.1 o.1 o.2 τ.1.2

/-! ### The transport/equality helper layer [REV 2, finding 13 — the E-fleet
execution deliverable].  Everything below is keyed to (V, X, cp) only — the
Q5 SHARED witness discipline.  Design records (prover phase, 2026-07-30):
(i) `toCellAll` keys a measured cell to the all-outcomes carrier `DCellAll`
    (V4-6a) by the classical continuing/terminal case split; the MoveData/
    TermData literals have source `τ.1` DEFINITIONALLY (Sigma eta), so the
    carrier subtype proofs are `rfl`.
(ii) `μcellOf` is deliberately x-FREE: the per-(cell, height) weight is the
    `cp.count` POLYNOMIAL evaluation (`gwtAll`, the μcellH shape with cntc
    replaced by cp.P — x-free by cp's own law), so `rowVal := Σ_cells μcell`
    makes rep_indep near-rfl exactly as §3.E prescribes ("FORCED up to
    rep_indep; define it as that sum").
(iii) `Rep` is the per-pool zc-history family (REV 5 M-3): a representative
    IS a choice of zero-condition history at every pool point; `rep_ne` is
    `S.zc_ne` under `V.pools_sub`.
(iv) cellLvl/cellInst: the Q5 per-cell cp.count wiring demands a per-cell
    Box census carrier which `CtsMeasured` does NOT expose (cp.count counts
    ASSIGNMENTS, not box points; the state census stInst is the RETIRED
    coarse carrier).  Wired ∅/0 here as the disclosed seam placeholder —
    TV-F2 owns the co-design adjustment ("changes land in E1/E2's defs",
    §4 TV-F2); no E-cluster pin or LedgerIV law reads these fields. -/

open Classical in
/-- [transport] a measured cell as a point of the all-outcomes digit-cell
carrier `DCellAll V (toStepCells.symm τ.1)` (V4-6a's Σ-carrier). -/
noncomputable def toCellAll {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hfin : Finite (Skeleton n))
    {e : ℕ} (τ : (ctsTable C hfin).State e) (c : measCell V hfin e τ) :
    DCellAll V (V.toStepCells.symm τ.1) :=
  if hc : (C.bd τ.1.1).cont c.1.1 c.1.2 then
    Sum.inl ⟨⟨⟨τ.1.1, c.1.1, c.1.2, hc, τ.1.2⟩, rfl⟩, c.2⟩
  else
    Sum.inr ⟨C.vlabOf τ.1.1 c.1.1 c.1.2 hc,
      ⟨⟨τ.1.1, c.1.1, c.1.2, hc, rfl, τ.1.2⟩, rfl⟩, c.2⟩

/-- [transport] the measured cell's listed height domain — the Σ-embedded
`cdomAllMem` at its all-outcomes key. -/
def hdomOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hfin : Finite (Skeleton n))
    {e : ℕ} (τ : (ctsTable C hfin).State e) (c : measCell V hfin e τ) :
    Set (Σ D : ℕ, Hpt D) :=
  {h | cdomAllMem V (toCellAll V hfin τ c) h}

open Classical in
/-- [transport] the x-FREE fixed-height weight: the `μcellH` shape with the
cell count read through its `cp.count` polynomial (x-free by cp's law). -/
noncomputable def gwtAll {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    {αc : S.Cell} :
    DCellAll V αc → (Σ D : ℕ, Hpt D) → ℚ → ℝ
  | .inl ⟨d, c⟩, ⟨D, h⟩, q₀ =>
      if e : D = S.dim (V.moveOf d.1) then
        (((cp.P d.1.s d.1.m d.1.o d.1.α c).eval q₀ : ℚ) : ℝ)
          * (q₀ : ℝ) ^ (-(((X.E (V.moveOf d.1)).eval (castHpt e h) : ℕ) : ℤ))
      else 0
  | .inr ⟨_, d, c⟩, ⟨D, h⟩, q₀ =>
      if e : D = S.dimT (V.moveOfT d.1) then
        (((cp.P d.1.s d.1.m d.1.o d.1.α c).eval q₀ : ℚ) : ℝ)
          * (q₀ : ℝ) ^ (-(((X.ET (V.moveOfT d.1)).eval (castHpt e h) : ℕ) : ℤ))
      else 0

/-- [transport] ON THE LISTED DOMAIN the x-free cp weight IS the x-keyed
μcellH mass, at any zero-condition pool history (cp.count/countT — the
x-freeness bridge every E3/E4 law crosses). -/
theorem gwtAll_eq_μcellH {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    {αc : S.Cell} {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (x : S.Hist q₀ αc) (hzc : S.zc x)
    (ca : DCellAll V αc) (H : Σ D : ℕ, Hpt D) (hmem : cdomAllMem V ca H) :
    gwtAll V X cp ca H q₀ = μcellH V X x ca H := by
  classical
  obtain ⟨D, h⟩ := H
  cases ca with
  | inl dc =>
      obtain ⟨⟨d, hd⟩, c⟩ := dc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      simp only [gwtAll, μcellH, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      rw [show ((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ)
          = (V.cntc d x c (castHpt e h) : ℚ) from
        cp.count d c x hzc hq (castHpt e h) hmm]
      norm_cast
  | inr vdc =>
      obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      simp only [gwtAll, μcellH, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      rw [show ((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ)
          = (V.cntcT d x c (castHpt e h) : ℚ) from
        cp.countT d c x hzc hq (castHpt e h) hmm]
      norm_cast

/-- [transport] OFF the listed domain the x-keyed μcellH mass VANISHES at any
zero-condition pool history (the XHD-d cell face `no_orphanC`/`no_orphanCT`
contrapositive — the off-domain leg of part1's subtype extension). -/
theorem μcellH_eq_zero_off_dom {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    {αc : S.Cell} {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (x : S.Hist q₀ αc) (hzc : S.zc x)
    (ca : DCellAll V αc) (H : Σ D : ℕ, Hpt D)
    (hmem : ¬ cdomAllMem V ca H) :
    μcellH V X.w x ca H = 0 := by
  classical
  obtain ⟨D, h⟩ := H
  cases ca with
  | inl dc =>
      obtain ⟨⟨d, hd⟩, c⟩ := dc
      subst hd
      simp only [μcellH]
      split
      · next e =>
          rw [eq_of_heq (cast_heq _ x)]
          have hz : V.cntc d x c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos (fun hpos =>
              hmem ⟨e, X.dC.no_orphanC d x c _ hq hzc hpos⟩)
          rw [hz]; simp
      · rfl
  | inr vdc =>
      obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
      subst hd
      simp only [μcellH]
      split
      · next e =>
          rw [eq_of_heq (cast_heq _ x)]
          have hz : V.cntcT d x c (castHpt e h) = 0 :=
            Nat.eq_zero_of_not_pos (fun hpos =>
              hmem ⟨e, X.dC.no_orphanCT d x c _ hq hzc hpos⟩)
          rw [hz]; simp
      · rfl

/-- [transport] the level-N cell event at a history — the REV-6 double dite
over `V.cellEvt`/`V.cellEvtT` through the all-outcomes key. -/
noncomputable def evtAll {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ αc) (N : ℕ) :
    DCellAll V αc → (Σ D : ℕ, Hpt D) → Finset (V.Box q₀ N)
  | .inl ⟨d, c⟩, ⟨D, h⟩ =>
      if e : D = S.dim (V.moveOf d.1) then
        V.cellEvt d.1 (cast (congrArg (S.Hist q₀) d.2.symm) x) c (castHpt e h) N
      else ∅
  | .inr ⟨_, d, c⟩, ⟨D, h⟩ =>
      if e : D = S.dimT (V.moveOfT d.1) then
        V.cellEvtT d.1 (cast (congrArg (S.Hist q₀) d.2.symm) x) c (castHpt e h) N
      else ∅

/-- [E1 field] the per-pool representative family (REV 5, M-3): one
zero-condition history per pool point. -/
def repOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (β₀ : S.Cell) : Type :=
  ∀ q₀ : ℚ, q₀ ∈ V.Pools → {x : S.Hist q₀ β₀ // S.zc x}

/-- the measured-cell Fintype (letters × outcomes × digit-cell fibers). -/
noncomputable instance measCellFintype {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (hfin : Finite (Skeleton n))
    (e : ℕ) (τ : (ctsTable C hfin).State e) : Fintype (measCell V hfin e τ) := by
  haveI := (C.bd τ.1.1).finL
  haveI := (C.bd τ.1.1).finO
  haveI : ∀ o : (ctsTable C hfin).Out e τ,
      Fintype (V.DCellO τ.1.1 o.1 o.2 τ.1.2) := fun o => V.finDO _ _ _ _
  have hfin' : Finite (measCell V hfin e τ) := by
    unfold measCell; infer_instance
  exact Fintype.ofFinite _

open Classical in
/-- [E1 field] the x-FREE per-cell conditional mass: the height sum of the
cp-polynomial weights over the listed domain (pool-guarded dite). -/
noncomputable def μcellOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) {e : ℕ} (τ : (ctsTable C hfin).State e)
    (c : measCell V hfin e τ) (q₀ : ℚ) : ℝ :=
  if _ : q₀ ∈ V.Pools then
    ∑' h : {h : Σ D : ℕ, Hpt D // h ∈ hdomOf V hfin τ c},
      gwtAll V X cp (toCellAll V hfin τ c) h.1 q₀
  else 0

open Classical in
/-- [E2 field] the per-outcome row value := the μcell sum over the outcome's
cell fiber (§3.E: "FORCED up to rep_indep; define it as that sum"). -/
noncomputable def rowValOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) {e : ℕ} (τ : (ctsTable C hfin).State e)
    (o : (ctsTable C hfin).Out e τ) (q₀ : ℚ) : ℝ :=
  ∑ c ∈ {c : measCell V hfin e τ | c.1 = o}.toFinset,
    μcellOf V X cp hfin τ c q₀

open Classical in
/-- [E2 field] kstep case 1 — the transcribed kstep_one RHS (§3.E REV 2),
TARGET-ACTIVITY GUARDED.  [PROVER RECORD, kstep-1 co-design pin adjustment,
2026-07-30 (the E5a-header-sanctioned resolution of the inactive-SOURCE
residual of act_target): the unguarded Σ makes `act_target` UNPROVABLE at an
inactive source (no CtsMeasured law kills cntc there — tgt_supported and
no_entry are source-activity-guarded), while the guard makes act_target
rfl-genre and relocates the bridge into kstep_one's inactive-β case, which
the PROVED TV-E5a bridge closes (source activity is kstep_one's own guard).
The TV-E2 pin `measuredOf_kstep_one_def` is adjusted to the guarded display
per its own adjustability clause; the LedgerIV-facing statements (TV-E5b)
are untouched.] -/
noncomputable def kstepOne {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) (e : ℕ)
    (τ β : (ctsTable C hfin).State e) (q₀ : ℚ) : ℝ :=
  if V.activeState q₀ (V.toStepCells.symm β.1) then
    ∑ o ∈ {o : (ctsTable C hfin).Out e τ |
          MovesS.routeOf ((ctsTable C hfin).odata e τ o) = .kcol ∧
          ∃ μ ∈ ((ctsTable C hfin).odata e τ o).mem,
            ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
        }.toFinset,
      rowValOf V X cp hfin τ o q₀
  else 0

/-- [E2 field] THE three-case kstep recursion (§3.E REV 2 display): case 0 the
Kronecker delta (forced by hmc at k = 0), case 1 the transcribed kstep_one
RHS, case (k+2) the γ-sum recursion. -/
noncomputable def kstepOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ℕ → ∀ e, (ctsTable C hfin).State e → (ctsTable C hfin).State e → ℚ → ℝ
  | 0 => fun _ τ β _ => if τ = β then 1 else 0
  | 1 => kstepOne V X cp hfin
  | (k + 2) => fun e τ β q₀ =>
      ∑ γ : (ctsTable C hfin).State e,
        kstepOf V X cp hfin (k + 1) e τ γ q₀ * kstepOne V X cp hfin e γ β q₀

/-- [E2 field] the per-EntIx entrance level (the census defining level at the
component's base instantiation, Option-totalized). -/
noncomputable def entLvlOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀) : ℕ :=
  ((writeHeights? i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base).map
    (fun ε => (ε.template?).elim 0 V.entLvl)).getD 0

/-- [E2 field] the per-EntIx instance census carrier at the base
instantiation (Option-totalized; `none` ⟹ ∅, matching instCensus's getD 0). -/
noncomputable def entInstOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀)
    (q₀ : ℚ) (N : ℕ) : Finset (V.Box q₀ N) :=
  ((writeHeights? i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base).map
    (fun ε => V.entInst ε β₀ q₀ N)).getD ∅

/-- [E2 field] the per-EntIx fixed-height entrance event (the h-instantiated
`V.entEvt`, Σ-embedded and Option-totalized). -/
noncomputable def entEvtHOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀)
    (H : Σ D : ℕ, Hpt D) (q₀ : ℚ) (N : ℕ) : Finset (V.Box q₀ N) :=
  if e : H.1 = i.1.1.entDim then
    ((writeHeights? i.1.1 (castHpt e H.2)).map
      (fun ε => V.entEvt ε β₀ q₀ N)).getD ∅
  else ∅

/-- [E2 field] the per-EntIx listed height domain (the Σ-embedded component
domain — the `cdomAllMem` pattern at the entrance face). -/
def iDomOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀) :
    Set (Σ D : ℕ, Hpt D) :=
  {p | ∃ e : p.1 = i.1.1.entDim,
    ((V.entDom i.1.1).comps.get i.1.2).Mem (castHpt e p.2)}

/-- [E2 field] the per-EntIx fixed-height entrance mass (the §2.G `ιshH`,
Σ-embedded). -/
noncomputable def ishHOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀)
    (H : Σ D : ℕ, Hpt D) (q₀ : ℚ) : ℝ :=
  if e : H.1 = i.1.1.entDim then ιshH V i.1.1 (castHpt e H.2) β₀ q₀ else 0

open Classical in
/-- TV-E1 (+ TV-E2 block 2): `measuredOf V X cp hfin` — THE real MeasuredSide
field map replacing the degenerate A28 core (V7_msA), keyed to (V, X, cp)
ONLY (the Q5 SHARED witness).  BLOCK 1 (this unit): `Pools := V.Pools` (the
three MeasuredSide pool laws ARE CtsCells' pools_pp/pools_closed/
pools_infinite, MovesV/Defs:685-689); `Box := V.Box`, `finB := V.finB`,
`boxpos := V.boxpos` (the guarded |Box| card tie becomes rfl-genre);
`Cell := measCell` with `cellOut := Sigma.fst`; `Hgt := Σ D : ℕ, Hpt D`;
`HDom` from the LISTED domains `V.cdom`/`V.cdomT` (the `cdomAllMem`
Σ-embedding pattern, V4_part1A); `μcell` := the μcellH carrier (V4-6,
V4_part1A:28); `cellEvt` := the REV-6 double-dite over `V.cellEvt`/
`V.cellEvtT` (definedness casing by route and assignment); `Rep` := the
REV-5 per-pool representative family (the E-phase notes in V7_msA's header
own the exact shape); `cellLvl`/`cellInst` wired per the Q5 RULING
(per-cell `cp.count` — adjudicated; the coarse sizeP/stInst option is
RETIRED).  BLOCK 2 (TV-E2): entrance block, activeState, rowVal, kstep,
markedVal/gwt residue fields.  The prescribed values are pinned by the
CO-DESIGN PIN lemmas here and in TV-E2; the cast-dependent pins are the
E-fleet's transport-layer deliverable [REV 2, finding 13].
deps: ctsTable, measCell. -/
noncomputable def measuredOf {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    MovesS.MeasuredSide (ctsTable C hfin) where
  Pools := V.Pools
  pools_prime_pow := V.pools_pp
  pools_closed := V.pools_closed
  pools_infinite := V.pools_infinite
  Box := V.Box
  finB := V.finB
  boxpos := V.boxpos
  Cell := measCell V hfin
  finC := fun e τ => measCellFintype V hfin e τ
  cellOut := fun _ _ c => c.1
  Rep := fun _ τ => repOf V (V.toStepCells.symm τ.1)
  rep_ne := fun _ _ τ =>
    ⟨fun q₀ hq => ⟨(S.zc_ne q₀ (V.pools_sub hq) _).choose,
      (S.zc_ne q₀ (V.pools_sub hq) _).choose_spec⟩⟩
  cellLvl := fun _ _ _ => 0
  cellInst := fun _ _ _ _ _ => ∅
  Hgt := Σ D : ℕ, Hpt D
  HDom := fun _ τ c => hdomOf V hfin τ c
  gwt := fun _ τ c h q₀ => gwtAll V X.w cp (toCellAll V hfin τ c) h q₀
  cellEvt := fun _ τ r c h q₀ N =>
    if hq : q₀ ∈ V.Pools then evtAll V (r q₀ hq).1 N (toCellAll V hfin τ c) h
    else ∅
  μcell := fun _ τ _ c q₀ => μcellOf V X.w cp hfin τ c q₀
  rowVal := fun _ τ o q₀ => rowValOf V X.w cp hfin τ o q₀
  kstep := kstepOf V X.w cp hfin
  activeState := fun q₀ _ τ => V.activeState q₀ (V.toStepCells.symm τ.1)
  decA := fun _ _ _ => Classical.propDecidable _
  EntShape := fun _ τ => V.EntIx (V.toStepCells.symm τ.1)
  finE := fun e τ => by
    haveI : Finite (EntTemplate n) := template_finite n
    haveI : Finite (V.EntIx (V.toStepCells.symm τ.1)) := by
      unfold CtsMeasured.EntIx; exact Subtype.finite
    exact Fintype.ofFinite _
  hent := fun _ _ i =>
    instHentCode i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base
  Went := fun _ _ i =>
    ((writeHeights? i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base).map
      EntShapeV.Went).getD 0
  entEvtH := fun _ _ i h q₀ N => entEvtHOf V i h q₀ N
  ιDom := fun _ _ i => iDomOf V i
  ιshH := fun _ _ i h q₀ => ishHOf V i h q₀
  ιsh := fun _ _ i q₀ => iotaShV V X.sEnt i q₀
  ιval := fun _ τ q₀ => iotaValV V X.sEnt (V.toStepCells.symm τ.1) q₀
  entCount := fun _ _ i q₀ => V.entCount i q₀
  entLvl := fun _ _ i => entLvlOf V i
  entInst := fun _ _ i q₀ N => entInstOf V i q₀ N
  markedVal := fun _ _ => 0

/-- TV-E1 CO-DESIGN PIN: `Pools := V.Pools` (rfl-genre at the intended
literal; adjustable only with a record — the TV-F1 pin discipline). -/
theorem measuredOf_pools {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Pools = V.Pools := rfl

/-- TV-E1 CO-DESIGN PIN: `Box := V.Box` (rfl-genre; makes TV-E7's guarded
|Box| cardinality tie rfl-genre modulo Fintype-instance transport). -/
theorem measuredOf_box {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Box = V.Box := rfl

/-- TV-E1 CO-DESIGN PIN: `Hgt := Σ D : ℕ, Hpt D` (the Σ-embedded height
carrier of the μcellH/cdomAllMem pattern). -/
theorem measuredOf_hgt {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    (measuredOf V X cp hfin).Hgt = (Σ D : ℕ, Hpt D) := rfl

/-- TV-E1 CO-DESIGN PIN: `Cell e τ = measCell V hfin e τ` (the §3.E cell
carrier; the downstream cast layer across this equality is the E-fleet's
transport deliverable, finding 13). -/
theorem measuredOf_cell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e),
      (measuredOf V X cp hfin).Cell e τ = measCell V hfin e τ :=
  fun _ _ => rfl

end LeanUrat.MovesV
