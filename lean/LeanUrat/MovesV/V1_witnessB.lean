/-  MovesV unit V1-8b `xhdds_realized` (SPLIT Codex-19; REV 4 process side) —
    a TmplEvents toy with all SEVEN ties + XHDd + XHDs; at THIS toy HMC is
    TRUE (with V4-11's false-HMC toy they bracket the kernel). -/
import LeanUrat.MovesV.V1_witnessA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

/-! ### The dimension-0 semilinear toolbox (shared with V1-8c).
Every template of the V1-8a system `witS` has height dimension 0, so its
listed domains are the ONE-POINT partition `zeroPart` and every component
subtype is a singleton — the XHD-s sums are one-term sums. -/

/-- the one-point linear set: base 0, NO periods. -/
def zeroL (D : ℕ) : LinSet D := ⟨fun _ => 0, []⟩

/-- the one-component partition [zeroL]. -/
def zeroPart (D : ℕ) : SemilinPart D := ⟨[zeroL D], List.pairwise_singleton _ _⟩

/-- the base point belongs to `zeroL` (any dimension). -/
lemma zeroL_mem_zero (D : ℕ) : (zeroL D).Mem (fun _ => 0) :=
  ⟨fun _ => 0, funext fun i => by simp [zeroL]⟩

/-- at dimension 0 any two height points agree. -/
lemma hpt_eq_of_dim0 {D : ℕ} (hD : D = 0) (h h' : Hpt D) : h = h' := by
  subst hD
  exact funext fun i => i.elim0

/-- at dimension 0 every height point lies in `zeroPart`. -/
lemma zeroPart_mem_of_dim0 {D : ℕ} (hD : D = 0) (h : Hpt D) :
    (zeroPart D).Mem h := by
  subst hD
  exact ⟨zeroL 0, List.mem_singleton_self _,
    fun _ => 0, funext fun i => i.elim0⟩

/-- one-term `HasSum` over a pointed subsingleton index. -/
lemma hasSum_of_unique {ι : Type*} (f : ι → ℝ) (i₀ : ι)
    (huniq : ∀ i : ι, i = i₀) : HasSum f (f i₀) :=
  hasSum_single i₀ fun b hb => absurd (huniq b) hb

/-- the `OKat` evaluation of the constant `1` is `1` (any membership proof). -/
lemma evalAt_one (q₀ : ℚ) (pf : (1 : Qq) ∈ OKat q₀) :
    (evalAt q₀ ⟨(1 : Qq), pf⟩ : ℚ) = 1 := by
  rw [show (⟨(1 : Qq), pf⟩ : OKat q₀) = 1 from rfl, map_one]

/-- the `PolyGeom`-class denominator witness for the constant `1`. -/
lemma one_denom_dvd : ∃ (b : ℕ) (as : Finset ℕ+),
    (1 : Qq).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) := by
  refine ⟨0, ∅, ?_⟩
  rw [RatFunc.denom_one]
  simp

/-! ### The V1-8a system's template layer: dimensions, domains, chains. -/

/-- every template over `witS` has height dimension 0. -/
lemma witS_tmpl_dim_zero : ∀ {α} (γ : Template 1 witS α), γ.D = 0
  | _, .last _ => rfl
  | _, .lastT m => m.elim
  | _, .cons m γ => by
      change witS.dim m + γ.D = 0
      rw [witS_tmpl_dim_zero γ]
      rfl

/-- the default chain of the toy (every carrier is `Unit`-like). -/
noncomputable def witChain : ∀ {α} (γ : Template 1 witS α) {q₀} (x : witS.Hist q₀ α)
    (h : Hpt γ.D), Chains witS γ x h
  | _, .last _, _, _, _ => ()
  | _, .lastT m, _, _, _ => m.elim
  | _, .cons m γ', _, x, h =>
      ⟨(), witChain γ' (witS.ext m x (Hpt.take h) ()) (Hpt.drop h)⟩

/-- all chains of the toy coincide. -/
lemma witChain_eq : ∀ {α} (γ : Template 1 witS α) {q₀} (x : witS.Hist q₀ α)
    (h : Hpt γ.D) (c c' : Chains witS γ x h), c = c'
  | _, .last _, _, _, _, _, _ => rfl
  | _, .lastT m, _, _, _, _, _ => m.elim
  | _, .cons m γ', _, x, h, c, c' => by
      obtain ⟨a, r⟩ := c
      obtain ⟨a', r'⟩ := c'
      cases a; cases a'
      exact congrArg _ (witChain_eq γ' _ _ r r')

instance {α} (γ : Template 1 witS α) {q₀} (x : witS.Hist q₀ α) (h : Hpt γ.D) :
    Subsingleton (Chains witS γ x h) := ⟨witChain_eq γ x h⟩

/-- the toy's fixed-height weights are all `1` (E is the zero affine form). -/
lemma witS_gProd_one : ∀ {α} (γ : Template 1 witS α) (h : Hpt γ.D) (q₀ : ℚ),
    gProd witXHDw γ h q₀ = 1
  | _, .last m, h, q₀ => by simp [gProd, witS, witXHDw, AffineE.eval]
  | _, .lastT m, _, _ => m.elim
  | _, .cons m γ', h, q₀ => by
      change (q₀ : ℝ) ^ (-(((witXHDw.E m).eval (Hpt.take h)) : ℤ))
          * gProd witXHDw γ' (Hpt.drop h) q₀ = 1
      rw [witS_gProd_one γ' (Hpt.drop h) q₀]
      simp [witS, witXHDw, AffineE.eval]

/-! ### The process-side carrier, domains, and sums. -/

/-- the V1-8b marked-event toy: one box, full censuses at level 0. -/
noncomputable def witTE : TmplEvents 1 witS where
  Box _ _ := Unit
  finB _ _ := inferInstance
  tevt := fun γ _ x h _ => Finset.univ
  tinst := fun γ _ x h _ => Finset.univ
  tmplLvl _ := 0
  tevt_last_iff := by
    intro α β m q₀ x h _ _
    constructor
    · intro _
      simp [witS, StepSys.cntraw]
    · intro _
      exact ⟨0, fun N _ => ⟨(), Finset.mem_univ _⟩⟩
  tevt_lastT_iff := by intro α v m; exact m.elim
  real_marks := by
    intro α γ q₀ x h _ _ _
    simp
  tmark γ _ x h _ := witChain γ x h
  tmark_inj := by
    intro α γ q₀ x h _ _ a b _
    exact Subsingleton.elim a b
  tmark_last_surj := by
    intro α β m q₀ x h _ _ c
    exact ⟨⟨(), Finset.mem_univ _⟩, Subsingleton.elim _ _⟩
  tmark_lastT_surj := by intro α v m; exact m.elim
  marks_realize := by
    intro α γ q₀ x h _ _ _
    exact ⟨0, fun N _ => ⟨(), Finset.mem_univ _⟩⟩

/-- the V1-8b domain face: every template's domain is the one-point partition
(exact against the toy's everywhere-positive `Tgam`). -/
noncomputable def witD : XHDd 1 witS witTE where
  dom γ := zeroPart γ.D
  no_orphan := by
    intro α γ q₀ x h _ _ _
    exact zeroPart_mem_of_dim0 (witS_tmpl_dim_zero γ) h
  no_stray := by
    intro α γ h _ q₀ _ x _
    simp [Tgam, witTE]

/-- HMC HOLDS at this toy: all three memberships are unconditionally true. -/
theorem witHMC : HMC witTE witD := by
  intro α β m γ h₁ h₂
  constructor
  · intro _
    exact ⟨zeroPart_mem_of_dim0 (witS_tmpl_dim_zero (.last m)) h₁,
      zeroPart_mem_of_dim0 (witS_tmpl_dim_zero γ) h₂⟩
  · intro _
    exact zeroPart_mem_of_dim0 (witS_tmpl_dim_zero (.cons m γ)) (Hpt.append h₁ h₂)

/-- the V1-8b sum face: each (one-point) component sums to the constant `1`. -/
noncomputable def witXs : XHDs 1 witS witXHDw witD where
  Gc _ _ := 1
  Gc_denom _ _ := one_denom_dvd
  Gc_ok _ _ _ _ := one_mem _
  Gc_hasSum := by
    intro α γ j q₀ hq
    have hj : (witD.dom γ).comps.get j = zeroL γ.D :=
      List.eq_of_mem_singleton (List.get_mem _ _)
    have hmem : ((witD.dom γ).comps.get j).Mem (fun _ => 0) := by
      rw [hj]; exact zeroL_mem_zero γ.D
    have key : HasSum
        (fun h : {h // ((witD.dom γ).comps.get j).Mem h} =>
          gProd witXHDw γ h.1 q₀)
        (gProd witXHDw γ (fun _ => 0) q₀) :=
      hasSum_of_unique _ ⟨fun _ => 0, hmem⟩ fun b =>
        Subtype.ext (hpt_eq_of_dim0 (witS_tmpl_dim_zero γ) b.1 _)
    rw [witS_gProd_one γ (fun _ => 0) q₀] at key
    have hval : ((evalAt q₀ ⟨(1 : Qq), one_mem _⟩ : ℚ) : ℝ) = 1 := by
      rw [evalAt_one]; norm_num
    rw [show ((evalAt q₀ ⟨(1 : Qq), one_mem _⟩ : ℚ) : ℝ) = 1 from hval]
    exact key

theorem xhdds_realized :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE)
      (X : XHDw 1 S), Nonempty (XHDs 1 S X D) ∧ HMC TE D :=
  ⟨witS, witTE, witD, witXHDw, ⟨witXs⟩, witHMC⟩

end LeanUrat.MovesV
