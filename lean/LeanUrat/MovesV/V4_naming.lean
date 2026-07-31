/-  MovesV unit V4-12 `comp_naming` (RESTATED REV 4 at the note's exact
    quantifier) — (a) the IF leg (proved-under-hypotheses shape); (b) the
    ONLY-IF leg as a NAMED STATEMENT, consumed by nothing, claimed neither
    way; (b′) the machine-checked sum-level coincidence; (c) the fence. -/
import LeanUrat.MovesV.V4_hmc
import LeanUrat.MovesV.V0_partition

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the factorization identity AT THE FIXED XHD weight system. -/
def Factorizes {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    (X : XHDw n S) (D : XHDd n S TE) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (q₀ : ℚ), q₀ ∈ S.Pools →
    ∀ (a b c : ℝ),
      HasSum (fun h : {h // (D.dom (.cons m γ)).Mem h} =>
        gProd X (.cons m γ) h.1 q₀) a →
      HasSum (fun h : {h // (D.dom (.last m)).Mem h} => X.g m h.1 q₀) b →
      HasSum (fun h : {h // (D.dom γ).Mem h} => gProd X γ h.1 q₀) c →
      a = b * c

/-- append/take/drop round-trip lemmas (the Fin.append coordinates).
[SYN2-S1 SWEEP-6, 2026-07-31: `hpt_take_append`/`hpt_drop_append` DE-PRIVATIZED as the
family SURVIVORS (the originals — the Kernels KC2b/KC6 copies existed only because
these were `private`, per their own docstrings); Kernels copies deleted, re-pointed
here.  `hpt_append_take_drop` below stays private (no twin).] -/
lemma hpt_take_append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) :
    Hpt.take (Hpt.append h₁ h₂) = h₁ := by
  funext i; simp only [Hpt.take, Hpt.append, Fin.append_left]

lemma hpt_drop_append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) :
    Hpt.drop (Hpt.append h₁ h₂) = h₂ := by
  funext j; simp only [Hpt.drop, Hpt.append, Fin.append_right]

private lemma hpt_append_take_drop {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) :
    Hpt.append (Hpt.take h) (Hpt.drop h) = h := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [Hpt.append, Fin.append_left, Hpt.take]
  · simp only [Hpt.append, Fin.append_right, Hpt.drop]

/-- the HMC-supplied index equivalence: the composite domain factors as the
product of the one-step domain and the template domain, under `append`. -/
private def compEquiv {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    {D : XHDd n S TE} (hHMC : HMC TE D) {α β} (m : S.Move α β)
    (γ : Template n S β) :
    {h₁ // (D.dom (.last m)).Mem h₁} × {h₂ // (D.dom γ).Mem h₂}
      ≃ {h // (D.dom (.cons m γ)).Mem h} where
  toFun p := ⟨Hpt.append p.1.1 p.2.1, (hHMC m γ p.1.1 p.2.1).mpr ⟨p.1.2, p.2.2⟩⟩
  invFun q :=
    (⟨Hpt.take q.1, ((hHMC m γ (Hpt.take q.1) (Hpt.drop q.1)).mp
        (by rw [hpt_append_take_drop]; exact q.2)).1⟩,
     ⟨Hpt.drop q.1, ((hHMC m γ (Hpt.take q.1) (Hpt.drop q.1)).mp
        (by rw [hpt_append_take_drop]; exact q.2)).2⟩)
  left_inv := by
    rintro ⟨⟨h₁, h1m⟩, ⟨h₂, h2m⟩⟩
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨hpt_take_append h₁ h₂, hpt_drop_append h₁ h₂⟩
  right_inv := by
    rintro ⟨h, hm⟩
    exact Subtype.ext (hpt_append_take_drop h)

/-- (a) THE IF LEG: HMC upgrades (COMP-hΣ) to the factored form. -/
theorem comp_upgrade {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    (X : XHDw n S) (D : XHDd n S TE) (Xs : XHDs n S X D)
    (hHMC : HMC TE D) : Factorizes X D := by
  intro α β m γ q₀ hq a b c ha hb hc
  -- reindex the composite series through the HMC equivalence
  have ha' : HasSum
      (fun p : {h₁ // (D.dom (.last m)).Mem h₁} × {h₂ // (D.dom γ).Mem h₂} =>
        X.g m p.1.1 q₀ * gProd X γ p.2.1 q₀) a := by
    have h0 := (Equiv.hasSum_iff (compEquiv hHMC m γ)).mpr ha
    convert h0 using 1
    funext p
    simp only [Function.comp_apply, compEquiv, Equiv.coe_fn_mk, XHDw.g, gProd,
      hpt_take_append, hpt_drop_append]
  -- the product series is summable, so HasSum.mul applies
  have hsummable : Summable
      (fun p : {h₁ // (D.dom (.last m)).Mem h₁} × {h₂ // (D.dom γ).Mem h₂} =>
        X.g m p.1.1 q₀ * gProd X γ p.2.1 q₀) := ⟨a, ha'⟩
  exact ha'.unique (hb.mul hc hsummable)

/-- (b) THE ONLY-IF LEG at the note's exact quantifier — a NAMED statement,
status RECORDED (interface-derivability OPEN, CLAIMED NEITHER WAY);
consumed by NO unit. -/
def UpgradeOnlyIf {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (X : XHDw n S) (D : XHDd n S TE) : Prop :=
  Factorizes X D → HMC TE D

/-- (b′) the MACHINE-CHECKED SUM-LEVEL COINCIDENCE: two DIFFERENT listed
sets with IDENTICAL fixed-system weight sums under E = h₁ + h₂. -/
theorem sum_not_membership (q₀ : ℝ) (hq : q₀ ≠ 0) :
    (([(0,0),(1,0),(0,1),(2,0)] : List (ℕ × ℕ)).map
        (fun h => q₀ ^ (-(h.1 + h.2 : ℤ)))).sum
      = (([(0,0),(1,0),(0,1),(1,1)] : List (ℕ × ℕ)).map
        (fun h => q₀ ^ (-(h.1 + h.2 : ℤ)))).sum ∧
    ([(0,0),(1,0),(0,1),(2,0)] : List (ℕ × ℕ)) ≠ [(0,0),(1,0),(0,1),(1,1)] := by
  constructor
  · norm_num
  · decide

/-! ### The fence toy (built over `witS`, the dim-0 witness that carries a real
`XHDw`): one-step domain FULL, composite domain EMPTY, so `no_orphan`/`no_stray`
stay consistent (census 0 on composites) while HMC and the factored identity both
fail. -/
namespace FenceToy

/-- the empty listed partition — nothing is a member. -/
def emptyPart (D : ℕ) : SemilinPart D := ⟨[], List.Pairwise.nil⟩

lemma emptyPart_not_mem {D : ℕ} {h : Hpt D} : ¬ (emptyPart D).Mem h := by
  rintro ⟨L, hL, -⟩; nomatch hL

/-- the coupled event: FULL (`univ`) at one-step templates, EMPTY at composites. -/
noncomputable def evt : ∀ {α} (γ : Template 1 witS α) {q₀} (_ : witS.Hist q₀ α)
    (_ : Hpt γ.D) (_ : ℕ), Finset (Fin 1)
  | _, .last _,  _, _, _, _ => Finset.univ
  | _, .lastT m, _, _, _, _ => m.elim
  | _, .cons _ _, _, _, _, _ => ∅

/-- the mark reading: identity into the (unit) one-step chains; empty at composites. -/
noncomputable def mk : ∀ {α} (γ : Template 1 witS α) {q₀} (x : witS.Hist q₀ α)
    (h : Hpt γ.D), {b // b ∈ evt γ x h 0} → Chains witS γ x h
  | _, .last _,  _, _, _, _ => ()
  | _, .lastT m, _, _, _, _ => m.elim
  | _, .cons _ _, _, _, _, b => absurd b.2 (Finset.notMem_empty _)

/-- the toy event carrier over `witS`. -/
noncomputable def FTE : TmplEvents 1 witS where
  Box _ _ := Fin 1
  finB _ _ := inferInstance
  tevt := fun γ _ x h N => evt γ x h N
  tinst := fun γ _ x h N => evt γ x h N
  tmplLvl _ := 0
  tevt_last_iff := by
    intro α β m q₀ x h _ _
    refine ⟨fun _ => ?_, fun _ => ⟨0, fun N _ => Finset.univ_nonempty⟩⟩
    show 0 < witS.cntraw m x h
    rw [show witS.cntraw m x h = 1 from rfl]; exact one_pos
  tevt_lastT_iff := by intro α v m; exact m.elim
  real_marks := by
    intro α γ q₀ x h _ _ hR
    cases γ with
    | last m => exact Finset.card_pos.mpr Finset.univ_nonempty
    | lastT m => exact m.elim
    | cons m γ' =>
      obtain ⟨N₀, hN⟩ := hR
      exact absurd (hN N₀ le_rfl) Finset.not_nonempty_empty
  tmark := fun γ _ x h => mk γ x h
  tmark_inj := by
    intro α γ q₀ x h _ _
    cases γ with
    | last m => intro a b _; exact Subtype.ext (Subsingleton.elim a.1 b.1)
    | lastT m => exact m.elim
    | cons m γ' => intro a _ _; exact absurd a.2 (Finset.notMem_empty _)
  tmark_last_surj := by
    intro α β m q₀ x h _ _ c
    exact ⟨⟨0, Finset.mem_univ 0⟩, rfl⟩
  tmark_lastT_surj := by intro α v m; exact m.elim
  marks_realize := by
    intro α γ q₀ x h _ _ hpos
    cases γ with
    | last m => exact ⟨0, fun N _ => Finset.univ_nonempty⟩
    | lastT m => exact m.elim
    | cons m γ' => exact absurd hpos (lt_irrefl 0)

/-- the toy domains: one-step FULL, composites EMPTY. -/
noncomputable def domF : ∀ {α} (γ : Template 1 witS α), SemilinPart γ.D
  | _, .last _  => HmcToy.fullPart 0
  | _, .lastT m => m.elim
  | _, .cons _ _ => emptyPart _

/-- the toy XHD-d over `witS`: coupled to the FULL/EMPTY census. -/
noncomputable def FD : XHDd 1 witS FTE where
  dom := domF
  no_orphan := by
    intro α γ q₀ x h _ _ hpos
    cases γ with
    | last m => exact HmcToy.fullPart_mem _ _
    | lastT m => exact m.elim
    | cons m γ' =>
      exact absurd hpos (lt_irrefl 0)
  no_stray := by
    intro α γ h hm q₀ _ x _
    cases γ with
    | last m =>
      have hcard : Tgam FTE (Template.last m) x h = (Finset.univ : Finset (Fin 1)).card := rfl
      rw [hcard]; decide
    | lastT m => exact m.elim
    | cons m γ' => exact absurd hm emptyPart_not_mem

end FenceToy

/-- (c) THE FENCE (re-keyed to the process side, N-1): an instance where
¬HMC ∧ ¬Factorizes — no unconditional upgrade theorem can exist. -/
theorem comp_upgrade_fails :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE) (X : XHDw 1 S),
      ¬ HMC TE D ∧ ¬ Factorizes X D := by
  refine ⟨witS, FenceToy.FTE, FenceToy.FD, witXHDw, ?_, ?_⟩
  · -- ¬ HMC: composite domain empty, one-step domains full
    intro hH
    let m0 : witS.Move () () := ()
    have h := (hH m0 (Template.last m0) 0 0).mpr
      ⟨by show (HmcToy.fullPart 0).Mem (0 : Hpt 0); exact HmcToy.fullPart_mem 0 0,
       by show (HmcToy.fullPart 0).Mem (0 : Hpt 0); exact HmcToy.fullPart_mem 0 0⟩
    exact FenceToy.emptyPart_not_mem h
  · -- ¬ Factorizes: a = 0 (empty composite) but b*c > 0 (full one-step)
    intro hFac
    let m0 : witS.Move () () := ()
    haveI hss : Subsingleton {h // (FenceToy.FD.dom (Template.last m0)).Mem h} :=
      ⟨fun a b => Subtype.ext (funext fun i =>
        (finCongr (show (Template.last m0).D = 0 from rfl) i).elim0)⟩
    haveI hne : Nonempty {h // (FenceToy.FD.dom (Template.last m0)).Mem h} :=
      ⟨⟨0, by show (HmcToy.fullPart 0).Mem (0 : Hpt 0); exact HmcToy.fullPart_mem 0 0⟩⟩
    haveI hfin : Fintype {h // (FenceToy.FD.dom (Template.last m0)).Mem h} :=
      Fintype.ofSubsingleton
        ⟨0, by show (HmcToy.fullPart 0).Mem (0 : Hpt 0); exact HmcToy.fullPart_mem 0 0⟩
    haveI hIE : IsEmpty {h // (FenceToy.FD.dom (Template.cons m0 (Template.last m0))).Mem h} :=
      ⟨fun x => FenceToy.emptyPart_not_mem x.2⟩
    haveI hfin2 : Fintype {h // (FenceToy.FD.dom (Template.cons m0 (Template.last m0))).Mem h} :=
      Fintype.ofIsEmpty
    -- the composite series sums to 0
    have ha : HasSum (fun h : {h // (FenceToy.FD.dom
        (Template.cons m0 (Template.last m0))).Mem h} =>
        gProd witXHDw (Template.cons m0 (Template.last m0)) h.1 2) 0 := by
      simpa using hasSum_fintype (fun h : {h // (FenceToy.FD.dom
        (Template.cons m0 (Template.last m0))).Mem h} =>
        gProd witXHDw (Template.cons m0 (Template.last m0)) h.1 2)
    -- the one-step series and template series are positive
    have hb : HasSum (fun h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h} =>
        witXHDw.g m0 h.1 2)
        (∑ h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h}, witXHDw.g m0 h.1 2) :=
      hasSum_fintype _
    have hc : HasSum (fun h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h} =>
        gProd witXHDw (Template.last m0) h.1 2)
        (∑ h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h},
          gProd witXHDw (Template.last m0) h.1 2) := hasSum_fintype _
    have hbpos : 0 < ∑ h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h},
        witXHDw.g m0 h.1 2 :=
      Finset.sum_pos (fun i _ => by simp only [XHDw.g]; exact zpow_pos (by norm_num) _)
        Finset.univ_nonempty
    have hcpos : 0 < ∑ h : {h // (FenceToy.FD.dom (Template.last m0)).Mem h},
        gProd witXHDw (Template.last m0) h.1 2 :=
      Finset.sum_pos (fun i _ => by simp only [gProd]; exact zpow_pos (by norm_num) _)
        Finset.univ_nonempty
    have key := hFac m0 (Template.last m0) 2 (by simp [witS]) 0 _ _ ha hb hc
    have hpos := mul_pos hbpos hcpos
    rw [← key] at hpos
    exact absurd hpos (lt_irrefl 0)

end LeanUrat.MovesV
