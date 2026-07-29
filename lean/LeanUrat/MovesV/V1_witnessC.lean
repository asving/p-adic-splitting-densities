/-  MovesV unit V1-8c `measured_faces_realized` (SPLIT Codex-19) — the FULL
    XHD bundle realized over a one-cell/one-template CtsMeasured toy
    (ent_cut VACUOUS at the ∅-census device — the law's nonemptiness guard). -/
import LeanUrat.MovesV.V1_witnessB
import LeanUrat.MovesSp.SP6_n1singleton

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

/-! ### The pool: all positive powers of 2 (infinite, power-closed, prime-power). -/

/-- the V1-8c pool: `{2^k | k ≥ 1}`. -/
def pow2 : Set ℚ := {q₀ | ∃ k : ℕ, 0 < k ∧ q₀ = (2 : ℚ) ^ k}

lemma two_mem_pow2 : (2 : ℚ) ∈ pow2 := ⟨1, one_pos, (pow_one 2).symm⟩

lemma pow2_pp : ∀ q₀ ∈ pow2, IsPP q₀ := by
  rintro q₀ ⟨k, hk, rfl⟩
  exact ⟨2, k, Nat.prime_two, hk, by norm_num⟩

lemma pow2_gt_one : ∀ q₀ ∈ pow2, (1 : ℚ) < q₀ := by
  rintro q₀ ⟨k, hk, rfl⟩
  exact one_lt_pow₀ one_lt_two hk.ne'

lemma pow2_closed : ∀ q₀ ∈ pow2, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ pow2 := by
  rintro q₀ ⟨k, hk, rfl⟩ δ
  exact ⟨k * δ, Nat.mul_pos hk δ.pos, (pow_mul 2 k δ).symm⟩

lemma pow2_infinite : pow2.Infinite := by
  have hmono : StrictMono (fun n : ℕ => (2 : ℚ) ^ (n + 1)) := fun a b h =>
    pow_lt_pow_right₀ one_lt_two (by omega)
  exact Set.infinite_of_injective_forall_mem hmono.injective
    (fun n => ⟨n + 1, n.succ_pos, rfl⟩)

/-- the level-N box cardinality identity at pool points. -/
lemma boxC_card (q₀ : ℚ) (hq : q₀ ∈ pow2) (N : ℕ) :
    ((max 1 (q₀.num.toNat ^ N) : ℕ) : ℚ) = q₀ ^ (1 * N) := by
  obtain ⟨k, hk, rfl⟩ := hq
  have hnum : ((2 : ℚ) ^ k).num = (2 : ℤ) ^ k := by
    rw [Rat.num_pow]; norm_num
  have htn : ((2 : ℚ) ^ k).num.toNat = 2 ^ k := by
    rw [hnum, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, ← Nat.cast_pow,
      Int.toNat_natCast]
  rw [htn, Nat.max_eq_right (Nat.one_le_pow _ _ (pow_pos two_pos k)),
    one_mul]
  push_cast
  ring

/-! ### The n = 1 catalogue is a singleton: `Skeleton 1` and `VLabel 1` collapse. -/

/-- the unique n = 1 skeleton (the confirming root letter). -/
def sk1 : Skeleton 1 := ⟨MovesSp.confirmingRoot1, (MovesSp.SnRaw1_eq _).mpr rfl⟩

lemma skeleton1_eq (s : Skeleton 1) : s = sk1 := by
  obtain ⟨sp, mem⟩ := s
  have h := (MovesSp.SnRaw1_eq sp).mp mem
  subst h
  rfl

instance : Subsingleton (Skeleton 1) :=
  ⟨fun a b => (skeleton1_eq a).trans (skeleton1_eq b).symm⟩

/-- the unique n = 1 absorbing column label: (e, f) = (1, 1). -/
def vlab1 : VLabel 1 := ⟨(1, 1), le_refl 1⟩

instance : Subsingleton (VLabel 1) := ⟨by
  rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩
  have hab : (a : ℕ) ≤ 1 := le_trans (Nat.le_mul_of_pos_right _ b.pos) h
  have hba : (b : ℕ) ≤ 1 := le_trans (Nat.le_mul_of_pos_left _ a.pos) h
  have hcd : (c : ℕ) ≤ 1 := le_trans (Nat.le_mul_of_pos_right _ d.pos) h'
  have hdc : (d : ℕ) ≤ 1 := le_trans (Nat.le_mul_of_pos_left _ c.pos) h'
  have ha := a.pos; have hb := b.pos; have hc := c.pos; have hd := d.pos
  have h1 : a = c := PNat.coe_injective (by omega)
  have h2 : b = d := PNat.coe_injective (by omega)
  subst h1; subst h2
  rfl⟩

/-! ### The block data and the table family (empty generator list, one terminal
letter with a one-member `Sum.inl` roster — no continuing outcome anywhere). -/

/-- the uniform n = 1 block data: `Carrier = Unit`, no generators, one letter
whose single outcome is TERMINAL with the one-member `vlab1` roster. -/
noncomputable def blockToy (s : Skeleton 1) : BlockData 1 s where
  Carrier _ := Unit
  finCar _ := inferInstance
  Letter := Unit
  finL := inferInstance
  letterSp _ := Sum.inr MovesSp.Verdict.z
  letter_menu _ := Set.mem_union_right _ ⟨MovesSp.Verdict.z, Set.mem_univ _, rfl⟩
  Obs _ _ := Unit
  evalObs _ _ _ := ()
  Gen := Empty
  finG := inferInstance
  gen g := g.elim
  Wstate := 0
  sizeP _ := 1
  size_deg a := by simp
  size_count := by
    intro a q₀ hpp
    classical
    rw [Finset.filter_true_of_mem (fun x _ => fun g => g.elim)]
    simp
  Outc _ := Unit
  finO _ := inferInstance
  omem _ _ := [⟨0, 1, Sum.inl vlab1⟩]
  omem_ne _ _ := by simp
  omem_size := by
    intro m o mu hmu sk hst
    rw [List.eq_of_mem_singleton hmu] at hst
    simp at hst
  cont _ _ := False
  decCont _ _ := Decidable.isFalse fun h => h
  cont_iff := by
    intro m o
    constructor
    · exact False.elim
    · rintro ⟨mu, hmu, hR⟩
      rw [List.eq_of_mem_singleton hmu] at hR
      simp at hR
  tgtSk _ _ h := h.elim
  tgt_sp _ _ h := h.elim
  omem_sel _ _ h := h.elim

/-- the V1-8c table family over `blockToy`. -/
noncomputable def Ctoy : CtsFamily 1 where
  bd := blockToy
  tcell _ _ _ h := h.elim
  tcellM := fun s m o i sk hst => False.elim (by
    have h1 : ((blockToy s).omem m o).get i = ⟨0, 1, Sum.inl vlab1⟩ :=
      List.eq_of_mem_singleton (List.get_mem _ _)
    rw [h1] at hst
    simp at hst)
  tcellM_sel _ _ _ h := h.elim
  Wloc _ _ := 0
  T _ _ _ _ _ := 0
  T_deg := by intro s m o α β; simp
  vlabOf _ _ _ _ := vlab1

lemma cellIdx_eq (s : Skeleton 1) (a b : (Ctoy.bd s).CellIdx) : a = b := by
  apply Subtype.ext
  funext g
  exact g.elim

instance (s : Skeleton 1) : Subsingleton ((Ctoy.bd s).CellIdx) :=
  ⟨cellIdx_eq s⟩

/-- the unique cell index of a block. -/
noncomputable def cId (s : Skeleton 1) : (Ctoy.bd s).CellIdx :=
  ⟨fun g => g.elim, one_ne_zero⟩

/-- `Unit` enumerates the (singleton) state space of `Ctoy`. -/
noncomputable def cellEquiv : Unit ≃ Σ s : Skeleton 1, (Ctoy.bd s).CellIdx where
  toFun _ := ⟨sk1, cId sk1⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv := by
    rintro ⟨s, c⟩
    obtain rfl := skeleton1_eq s
    exact congrArg (Sigma.mk sk1) (cellIdx_eq sk1 _ c)

/-! ### The step system: one cell, NO continuing moves, one terminal move. -/

/-- the V1-8c step system: `Move = Empty` (the toy's roster is all-terminal),
`MoveT = Unit`, pool `pow2`, everything else `Unit`-trivial. -/
noncomputable def mcS : StepSys 1 where
  Cell := Unit
  finC := inferInstance
  cell_ne := ⟨()⟩
  Move _ _ := Empty
  MoveT _ _ := Unit
  finM _ _ := inferInstance
  finMT _ _ := inferInstance
  dim := by intro α β m; exact 0
  dimT := by intro α v m; exact 0
  Pools := pow2
  pools_ne := ⟨2, two_mem_pow2⟩
  pools_pp := pow2_pp
  pools_gt_one := pow2_gt_one
  Hist _ _ := Unit
  hist_ne _ _ _ := ⟨()⟩
  zc _ := True
  zc_ne _ _ _ := ⟨(), trivial⟩
  Assign := by intro α β m; exact m.elim
  finA := by intro α β m; exact m.elim
  AssignT := by intro α v m q₀ x h; exact Unit
  finAT := by intro α v m q₀ x h; exact inferInstance
  ext := by intro α β m; exact m.elim
  ext_zc := by intro α β m; exact m.elim
  massOf := by intro α β m; exact m.elim
  massOfT := by intro α v m q₀ x h a; exact (1 : ℝ)
  out_ne := by
    intro q₀ hq α x hzc
    exact Or.inr ⟨vlab1, (), (fun _ => 0), ⟨()⟩⟩

/-- terminal data over `Ctoy` is propositionally unique. -/
lemma termData_eq {v : VLabel 1} (d d' : TermData 1 Ctoy v) : d = d' := by
  obtain ⟨s, m, o, ht, hv, α⟩ := d
  obtain ⟨s', m', o', ht', hv', α'⟩ := d'
  obtain rfl := skeleton1_eq s
  obtain rfl := skeleton1_eq s'
  obtain rfl : m = m' := rfl
  obtain rfl : o = o' := rfl
  obtain rfl := cellIdx_eq sk1 α α'
  rfl

instance {v : VLabel 1} : Subsingleton (TermData 1 Ctoy v) := ⟨termData_eq⟩

/-- all assignment steps of `mcS` coincide (no continuing moves; the terminal
Σ-data is `Unit`/subsingleton throughout). -/
lemma astep_eq {αc : mcS.Cell} {q₀} {x : mcS.Hist q₀ αc}
    (p p' : AStep mcS αc x) : p = p' :=
  match p, p' with
  | .inl ⟨_, mv, _, _⟩, _ => mv.elim
  | _, .inl ⟨_, mv, _, _⟩ => mv.elim
  | .inr ⟨v, mv, h, a⟩, .inr ⟨v', mv', h', a'⟩ => by
      obtain rfl : v = v' := Subsingleton.elim v v'
      obtain rfl : mv = mv' := rfl
      obtain rfl : h = h' := funext fun i => i.elim0
      obtain rfl : a = a' := rfl
      rfl

/-! ### The classifier half (CtsCells) and the measured carrier (CtsMeasured). -/

/-- the V1-8c classifier half: boxes `Fin (max 1 (num^N))`, full events on the
terminal side, no continuing side. -/
noncomputable def mcCells : CtsCells 1 Ctoy mcS where
  toStepCells := cellEquiv
  Pools := pow2
  pools_sub := fun _ hq => hq
  pools_pp := by
    rintro q₀ ⟨k, hk, rfl⟩
    exact ⟨2, Nat.prime_two, ⟨k, hk⟩, by norm_num⟩
  pools_closed := pow2_closed
  pools_infinite := pow2_infinite
  Box q₀ N := Fin (max 1 (q₀.num.toNat ^ N))
  finB _ _ := inferInstance
  boxpos _ _ := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩
  box_card := by
    intro q₀ hq N
    rw [Fintype.card_fin]
    exact boxC_card q₀ hq N
  moveOf d := d.hc.elim
  moveOf_bij := by
    intro αc
    constructor
    · intro d d' _
      exact d.1.hc.elim
    · rintro ⟨βc, mv⟩
      exact mv.elim
  moveOfT _ := ()
  moveOfT_bij := by
    intro αc v
    constructor
    · intro d d' _
      exact Subtype.ext (termData_eq d.1 d'.1)
    · intro mv
      exact ⟨⟨⟨sk1, (), (), fun h => h, Subsingleton.elim vlab1 v, cId sk1⟩,
        rfl⟩, rfl⟩
  DCellO _ _ _ _ := Unit
  finDO _ _ _ _ := inferInstance
  cellOfA d := d.hc.elim
  cellOfAT := by intro v d q₀ x h a; exact ()
  emult := by intro s m o α c; exact 1
  evtOf := by intro αc βc mv; exact mv.elim
  evtOfT := by intro αc v mv q₀ x h a N; exact Finset.univ

/-- the V1-8c measured carrier: the REV-3 census/tie laws hold with the
∅-census entrance device (ent_cut vacuous at its nonemptiness guard). -/
noncomputable def mcV : CtsMeasured 1 Ctoy mcS where
  toCtsCells := mcCells
  evt_disj_cell := by
    intro αc q₀ x p p' N hne
    exact absurd (congrArg mcCells.stepKey (astep_eq p p')) hne
  stabLvl _ := 0
  stabLvlT _ := 0
  evt_card := by intro αc βc mv; exact mv.elim
  evt_cardT := by
    intro αc v mv q₀ x h a hq hzc N hN
    letI : Fintype (mcCells.Box q₀ N) := mcCells.finB q₀ N
    change ((@Finset.univ (mcCells.Box q₀ N) (mcCells.finB q₀ N)).card : ℝ)
      = mcS.massOfT mv x h a
        * ((@Fintype.card (mcCells.Box q₀ N) (mcCells.finB q₀ N)) : ℝ)
    rw [Finset.card_univ, show mcS.massOfT mv x h a = 1 from rfl, one_mul]
  evt_disj_assign := by intro αc βc mv; exact mv.elim
  evt_disj_assignT := by
    intro αc v mv q₀ x h a a' hne N
    exact absurd rfl hne
  cdom d := d.hc.elim
  cdomT _ _ := zeroPart _
  mdom d := d.hc.elim
  mdomT _ := zeroPart _
  activeState _ _ := True
  act_size := by
    intro q₀ hq c
    change True ↔ (1 : Polynomial ℚ).eval q₀ ≠ 0
    simp
  stLvl _ := 0
  stInst := fun c q₀ N => @Finset.univ _ (mcCells.finB q₀ N)
  stInst_card := by
    intro c q₀ hq
    letI : Fintype (mcCells.Box q₀ 0) := mcCells.finB q₀ 0
    rw [Finset.card_univ]
    change ((Fintype.card (Fin (max 1 (q₀.num.toNat ^ 0))) : ℚ))
      = (1 : Polynomial ℚ).eval q₀
    simp
  entDom _ := ⟨[], List.Pairwise.nil⟩
  entLands _ _ := False
  decLands _ _ := Decidable.isFalse fun h => h
  entEvt _ _ _ _ := ∅
  entLvl _ := 0
  entInst _ _ _ _ := ∅
  ent_card := by
    intro ε β₀ q₀ hq N hN
    simp
  ent_sel := by
    intro ε ε' β₀ q₀ hq _ _ _ _
    exact Finset.disjoint_empty_left _
  ent_cut := by
    intro ε β₀ q₀ hq hne
    exact absurd hne Finset.not_nonempty_empty

/-! ### The process-side carrier over `mcS` (only `.lastT` templates exist). -/

lemma mcS_tmpl_dim_zero : ∀ {α} (γ : Template 1 mcS α), γ.D = 0
  | _, .last m => m.elim
  | _, .lastT _ => rfl
  | _, .cons m _ => m.elim

/-- the default chain (terminal templates only). -/
noncomputable def mcChain : ∀ {α} (γ : Template 1 mcS α) {q₀}
    (x : mcS.Hist q₀ α) (h : Hpt γ.D), Chains mcS γ x h
  | _, .last m, _, _, _ => m.elim
  | _, .lastT _, _, _, _ => ()
  | _, .cons m _, _, _, _ => m.elim

lemma mcChain_eq : ∀ {α} (γ : Template 1 mcS α) {q₀} (x : mcS.Hist q₀ α)
    (h : Hpt γ.D) (c c' : Chains mcS γ x h), c = c'
  | _, .last m, _, _, _, _, _ => m.elim
  | _, .lastT _, _, _, _, _, _ => rfl
  | _, .cons m _, _, _, _, _, _ => m.elim

instance {α} (γ : Template 1 mcS α) {q₀} (x : mcS.Hist q₀ α) (h : Hpt γ.D) :
    Subsingleton (Chains mcS γ x h) := ⟨mcChain_eq γ x h⟩

/-- the V1-8c marked-event toy over `mcS`: one box, full censuses at level 0. -/
noncomputable def mcTE : TmplEvents 1 mcS where
  Box _ _ := Unit
  finB _ _ := inferInstance
  tevt := fun γ _ x h _ => Finset.univ
  tinst := fun γ _ x h _ => Finset.univ
  tmplLvl _ := 0
  tevt_last_iff := by intro α β m; exact m.elim
  tevt_lastT_iff := by
    intro α v m q₀ x h _ _
    constructor
    · intro _
      simp [mcS, StepSys.cntrawT]
    · intro _
      exact ⟨0, fun N _ => ⟨(), Finset.mem_univ _⟩⟩
  real_marks := by
    intro α γ q₀ x h _ _ _
    simp
  tmark γ _ x h _ := mcChain γ x h
  tmark_inj := by
    intro α γ q₀ x h _ _ a b _
    exact Subsingleton.elim a b
  tmark_last_surj := by intro α β m; exact m.elim
  tmark_lastT_surj := by
    intro α v m q₀ x h _ _ c
    exact ⟨⟨(), Finset.mem_univ _⟩, Subsingleton.elim _ _⟩
  marks_realize := by
    intro α γ q₀ x h _ _ _
    exact ⟨0, fun N _ => ⟨(), Finset.mem_univ _⟩⟩

/-! ### The eight XHD faces and the bundle. -/

/-- (XHD-w): terminal weight = the zero affine form (mass 1 = q₀⁰). -/
noncomputable def mcXw : XHDw 1 mcS where
  E := by intro α β m; exact m.elim
  ET := by intro α v m; exact ⟨0, Fin.elim0, fun i => i.elim0⟩
  w_eq := by intro α β m; exact m.elim
  wT_eq := by
    intro α v m q₀ x h a hq hzc
    simp [mcS, AffineE.eval]

/-- (XHD-u): all comparisons are between literal `1`s. -/
noncomputable def mcXu : XHDu 1 mcS where
  u_R_mass := by intro α β m; exact m.elim
  u_R_cnt := by intro α β m; exact m.elim
  u_T := by intro α β m; exact m.elim
  u_R_massT := by intro α v m q₀ x x' h a a' hq hz hz'; rfl
  u_R_cntT := by intro α v m q₀ x x' h hq hz hz'; rfl
  u_TT := by intro α v m q₀ x h h' hq hz h1 h2; rfl

/-- (XHD-d): one-point domains, exact against the full census. -/
noncomputable def mcXd : XHDd 1 mcS mcTE where
  dom γ := zeroPart γ.D
  no_orphan := by
    intro α γ q₀ x h _ _ _
    exact zeroPart_mem_of_dim0 (mcS_tmpl_dim_zero γ) h
  no_stray := by
    intro α γ h _ q₀ _ x _
    simp [Tgam, mcTE]

lemma mcS_gProd_one : ∀ {α} (γ : Template 1 mcS α) (h : Hpt γ.D) (q₀ : ℚ),
    gProd mcXw γ h q₀ = 1
  | _, .last m, _, _ => m.elim
  | _, .lastT m, h, q₀ => by simp [gProd, mcS, mcXw, AffineE.eval]
  | _, .cons m _, _, _ => m.elim

/-- (XHD-s), template face: each one-point component sums to the constant 1. -/
noncomputable def mcXs : XHDs 1 mcS mcXw mcXd where
  Gc _ _ := 1
  Gc_denom _ _ := one_denom_dvd
  Gc_ok _ _ _ _ := one_mem _
  Gc_hasSum := by
    intro α γ j q₀ hq
    have hj : (mcXd.dom γ).comps.get j = zeroL γ.D :=
      List.eq_of_mem_singleton (List.get_mem _ _)
    have hmem : ((mcXd.dom γ).comps.get j).Mem (fun _ => 0) := by
      rw [hj]; exact zeroL_mem_zero γ.D
    have key : HasSum
        (fun h : {h // ((mcXd.dom γ).comps.get j).Mem h} =>
          gProd mcXw γ h.1 q₀)
        (gProd mcXw γ (fun _ => 0) q₀) :=
      hasSum_of_unique _ ⟨fun _ => 0, hmem⟩ fun b =>
        Subtype.ext (hpt_eq_of_dim0 (mcS_tmpl_dim_zero γ) b.1 _)
    rw [mcS_gProd_one γ (fun _ => 0) q₀] at key
    rw [show ((evalAt q₀ ⟨(1 : Qq), one_mem _⟩ : ℚ) : ℝ) = 1 from by
      rw [evalAt_one]; norm_num]
    exact key

/-- (XHD-d), cell face: no continuing data; terminal counts are full. -/
noncomputable def mcXdC : XHDdC 1 mcS mcV where
  no_orphanC d := d.hc.elim
  no_strayC d := d.hc.elim
  no_orphanCT := by
    intro v d q₀ x c h hq hzc hpos
    exact zeroPart_mem_of_dim0 rfl h
  no_strayCT := by
    intro v d c h hmem q₀ hq x hzc
    letI := mcS.finAT (mcV.moveOfT d) x h
    classical
    exact Finset.card_pos.mpr
      ⟨(), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- (XHD-s), cell face: the terminal sums are the same one-point sums. -/
noncomputable def mcXsC : XHDsC 1 mcS mcXw mcXd mcV mcXs where
  Gcell d := d.hc.elim
  Gcell_denom d := d.hc.elim
  Gcell_ok d := d.hc.elim
  Gcell_hasSum d := d.hc.elim
  GcellT := by intro v d c j; exact 1
  GcellT_denom := by intro v d c j; exact one_denom_dvd
  GcellT_ok := by intro v d c j q₀ hq; exact one_mem _
  GcellT_hasSum := by
    intro v d c j q₀ hq
    have hj : (mcV.cdomT d c).comps.get j = zeroL _ :=
      List.eq_of_mem_singleton (List.get_mem _ _)
    have hmem : ((mcV.cdomT d c).comps.get j).Mem (fun _ => 0) := by
      rw [hj]; exact zeroL_mem_zero _
    have key : HasSum
        (fun h : {h // ((mcV.cdomT d c).comps.get j).Mem h} =>
          (q₀ : ℝ) ^ (-(((mcXw.ET (mcV.moveOfT d)).eval h.1) : ℤ)))
        ((q₀ : ℝ) ^ (-(((mcXw.ET (mcV.moveOfT d)).eval (fun _ => 0)) : ℤ))) :=
      hasSum_of_unique _ ⟨fun _ => 0, hmem⟩ fun b =>
        Subtype.ext (hpt_eq_of_dim0 rfl b.1 _)
    have hg : ((q₀ : ℝ) ^ (-(((mcXw.ET (mcV.moveOfT d)).eval
        (fun _ => 0 : Hpt (mcS.dimT (mcV.moveOfT d)))) : ℤ))) = 1 := by
      simp [mcXw, mcS, AffineE.eval]
    rw [hg] at key
    rw [show ((evalAt q₀ ⟨(1 : Qq), one_mem _⟩ : ℚ) : ℝ) = 1 from by
      rw [evalAt_one]; norm_num]
    exact key

/-- (XHD-s), entrance face: the entrance index is EMPTY (∅-census device). -/
noncomputable def mcXsEnt : XHDsEnt 1 mcS mcV where
  Gent _ i := i.2.elim
  Gent_denom _ i := i.2.elim
  Gent_ok _ i := i.2.elim
  Gent_hasSum _ i := i.2.elim

/-- no entrance instantiation is realizable: the entrance events are ∅. -/
lemma not_instReal (εT : EntTemplate 1) (h : Hpt εT.entDim)
    (β₀ : mcS.Cell) : ¬ mcV.instRealizable εT h β₀ := by
  rintro ⟨ε, hε, hreal⟩
  obtain ⟨N₀, hN⟩ := hreal 2 two_mem_pow2
  exact Finset.not_nonempty_empty (hN N₀ le_rfl)

/-- (XHD-d), entrance face: vacuous at the ∅-census device. -/
noncomputable def mcXdEnt : XHDdEnt 1 mcS mcV where
  no_orphanE εT h β₀ hr := (not_instReal εT h β₀ hr).elim
  no_strayE _ _ _ hl _ := hl.elim
  lands_of_realizable εT h β₀ hr := (not_instReal εT h β₀ hr).elim

/-- THE FULL BUNDLE. -/
noncomputable def mcXHD : XHD 1 mcS mcTE mcV where
  w := mcXw
  u := mcXu
  d := mcXd
  dC := mcXdC
  s := mcXs
  sC := mcXsC
  sEnt := mcXsEnt
  dEnt := mcXdEnt

theorem measured_faces_realized :
    ∃ (C : CtsFamily 1) (S : StepSys 1) (V : CtsMeasured 1 C S)
      (TE : TmplEvents 1 S), Nonempty (XHD 1 S TE V) :=
  ⟨Ctoy, mcS, mcV, mcTE, ⟨mcXHD⟩⟩

end LeanUrat.MovesV
