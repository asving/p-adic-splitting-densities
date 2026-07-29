/-
Unit `n2_sigmas` (easy; S5 chain batch) — THE FULL RS4Chain instance (R46,
Codex#7-2 = Fable#8-F2: no partial structures; every field listed at its owning
unit; the device shallow data enter via n2_wshp_device/n2_sh_events/n2_sh_laws).
This unit's display: sig_exact forces Sigmas = {(1,1)², (1,2), (2,1)}, the three
degree-2 multisets.
-/
import LeanUrat.MovesS.N2Beta
import LeanUrat.MovesS.N2ShapeFam
import LeanUrat.MovesS.N2Rexact
import LeanUrat.MovesS.N2Pools
import LeanUrat.MovesS.N2SolveVals

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

-- The abstract box carrier has no computable equality; the `shevt_grouping` fill's
-- biUnion takes the classical one (as at Interfaces; proof-irrelevant, last-resort).
attribute [local instance 0] Classical.decEq

open Polynomial Matrix

/-! ### A. Pool arithmetic: every pool is a natural number ≥ 2. -/

private lemma n2_pool_nat {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools) :
    ∃ m : ℕ, 2 ≤ m ∧ q₀ = (m : ℚ) := by
  rw [n2_pools] at hq
  obtain ⟨p, hp, δ, rfl⟩ := hq
  refine ⟨p ^ (δ : ℕ), ?_, by push_cast; ring⟩
  calc 2 ≤ p := hp.two_le
    _ ≤ p ^ (δ : ℕ) := Nat.le_self_pow δ.pos.ne' p

private lemma n2_pool_toNat {m : ℕ} : ((m : ℚ)).num.toNat = m := by
  rw [Rat.num_natCast, Int.toNat_natCast]

private lemma n2_pool_pos {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools) : 2 ≤ q₀ := by
  obtain ⟨m, hm, rfl⟩ := n2_pool_nat hq
  exact_mod_cast hm

/-! ### B. Card counts for the interval events on `Fin M`. -/

private lemma card_filter_fin_lt {M a : ℕ} (ha : a ≤ M) :
    (Finset.univ.filter (fun x : Fin M => x.1 < a)).card = a := by
  have h : Finset.univ.filter (fun x : Fin M => x.1 < a)
      = (Finset.range a).attachFin
          (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) ha) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_range]
  rw [h, Finset.card_attachFin, Finset.card_range]

private lemma card_filter_fin_ge (M b : ℕ) :
    (Finset.univ.filter (fun x : Fin M => b ≤ x.1)).card = M - b := by
  have h : Finset.univ.filter (fun x : Fin M => b ≤ x.1)
      = (Finset.Ico b M).attachFin (fun m hm => (Finset.mem_Ico.mp hm).2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
      Finset.mem_Ico]
    exact ⟨fun hb => ⟨hb, x.2⟩, fun h => h.1⟩
  rw [h, Finset.card_attachFin, Nat.card_Ico]

private lemma card_filter_fin_mid {M a b : ℕ} (hb : b ≤ M) :
    (Finset.univ.filter (fun x : Fin M => a ≤ x.1 ∧ x.1 < b)).card = b - a := by
  have h : Finset.univ.filter (fun x : Fin M => a ≤ x.1 ∧ x.1 < b)
      = (Finset.Ico a b).attachFin
          (fun m hm => lt_of_lt_of_le (Finset.mem_Ico.mp hm).2 hb) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [h, Finset.card_attachFin, Nat.card_Ico]

private lemma n2_box_card (q₀ : ℚ) (N : ℕ) :
    Fintype.card (n2M.Box q₀ N) = max 1 (q₀.num.toNat ^ 3) :=
  Fintype.card_fin _

private lemma n2_box_filter_lt (q₀ : ℚ) (N : ℕ) {a : ℕ}
    (ha : a ≤ max 1 (q₀.num.toNat ^ 3)) :
    (Finset.univ.filter (fun y : n2M.Box q₀ N => y.1 < a)).card = a :=
  card_filter_fin_lt ha

private lemma n2_box_filter_ge (q₀ : ℚ) (N : ℕ) (b : ℕ) :
    (Finset.univ.filter (fun y : n2M.Box q₀ N => b ≤ y.1)).card
      = max 1 (q₀.num.toNat ^ 3) - b :=
  card_filter_fin_ge _ b

private lemma n2_box_filter_mid (q₀ : ℚ) (N : ℕ) {a b : ℕ}
    (hb : b ≤ max 1 (q₀.num.toNat ^ 3)) :
    (Finset.univ.filter (fun y : n2M.Box q₀ N => a ≤ y.1 ∧ y.1 < b)).card = b - a :=
  card_filter_fin_mid hb

/-! ### C. The σ-roster: the three degree-2 verdict multisets. -/

private noncomputable def n2SigmasSet : Finset (Multiset n2T.VType) :=
  {{n2v11, n2v11}, {n2v12}, {n2v21}}

private lemma n2v_ne_12_21 : n2v12 ≠ n2v21 := by
  intro h
  have h1 := congrArg (fun v : n2T.VType => ((v.1.1 : ℕ), (v.1.2 : ℕ))) h
  simp only [n2v12, n2v21] at h1
  exact absurd h1 (by decide)

private lemma n2v_ne_11_12 : n2v11 ≠ n2v12 := by
  intro h
  have h1 := congrArg (fun v : n2T.VType => ((v.1.1 : ℕ), (v.1.2 : ℕ))) h
  simp only [n2v11, n2v12] at h1
  exact absurd h1 (by decide)

private lemma n2v_ne_11_21 : n2v11 ≠ n2v21 := by
  intro h
  have h1 := congrArg (fun v : n2T.VType => ((v.1.1 : ℕ), (v.1.2 : ℕ))) h
  simp only [n2v11, n2v21] at h1
  exact absurd h1 (by decide)

/-- Degree classification on the n = 2 verdict carrier: degree 1 forces (1,1);
degree 2 forces (1,2) or (2,1); nothing has degree 0 or ≥ 3. -/
private lemma n2_vdeg_cases (v : n2T.VType) :
    ((n2T.vdeg v : ℕ) = 1 ∧ v = n2v11) ∨
    ((n2T.vdeg v : ℕ) = 2 ∧ (v = n2v12 ∨ v = n2v21)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := v
  have ha := a.one_le
  have hb := b.one_le
  have hd : (n2T.vdeg ⟨(a, b), hab⟩ : ℕ) = (a : ℕ) * (b : ℕ) :=
    n2T.vdeg_spec ⟨(a, b), hab⟩
  have hab' : (a : ℕ) * (b : ℕ) ≤ 2 := hab
  have hcases : ((a : ℕ) = 1 ∧ (b : ℕ) = 1) ∨ ((a : ℕ) = 1 ∧ (b : ℕ) = 2) ∨
      ((a : ℕ) = 2 ∧ (b : ℕ) = 1) := by
    have h1 : 1 ≤ (a : ℕ) := ha
    have h2 : 1 ≤ (b : ℕ) := hb
    rcases Nat.lt_or_ge (a : ℕ) 2 with hlt | hge
    · have ha1 : (a : ℕ) = 1 := by omega
      rw [ha1, one_mul] at hab'
      omega
    · have hb1 : (b : ℕ) = 1 := by nlinarith
      rw [hb1, mul_one] at hab'
      omega
  have hv11 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hv2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hA : a = 1 := PNat.coe_injective (by rw [h1, hv11])
    have hB : b = 1 := PNat.coe_injective (by rw [h2, hv11])
    subst hA; subst hB
    exact ⟨by rw [hd]; decide, rfl⟩
  · right
    have hA : a = 1 := PNat.coe_injective (by rw [h1, hv11])
    have hB : b = 2 := PNat.coe_injective (by rw [h2, hv2])
    subst hA; subst hB
    exact ⟨by rw [hd]; decide, Or.inl rfl⟩
  · right
    have hA : a = 2 := PNat.coe_injective (by rw [h1, hv2])
    have hB : b = 1 := PNat.coe_injective (by rw [h2, hv11])
    subst hA; subst hB
    exact ⟨by rw [hd]; decide, Or.inr rfl⟩

private lemma n2_vdeg_pos (v : n2T.VType) : 1 ≤ (n2T.vdeg v : ℕ) :=
  (n2T.vdeg v).one_le

/-- sig_exact at the instance: a verdict multiset has degree-sum 2 iff it is one
of {(1,1)²}, {(1,2)}, {(2,1)}. -/
private lemma n2_sig_exact (σ : Multiset n2T.VType) :
    σ ∈ n2SigmasSet ↔ (σ.map fun v => ((n2T.vdeg v : ℕ))).sum = 2 := by
  constructor
  · -- forward: compute the three degree sums
    intro hσ
    simp only [n2SigmasSet, Finset.mem_insert, Finset.mem_singleton] at hσ
    have h11 : (n2T.vdeg n2v11 : ℕ) = 1 := by
      rcases n2_vdeg_cases n2v11 with ⟨h, _⟩ | ⟨_, hv | hv⟩
      · exact h
      · exact absurd hv n2v_ne_11_12
      · exact absurd hv n2v_ne_11_21
    rcases hσ with rfl | rfl | rfl
    · rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton, h11]
    · rcases n2_vdeg_cases n2v12 with ⟨_, h⟩ | ⟨hd, _⟩
      · exact absurd h.symm n2v_ne_11_12
      · rw [Multiset.map_singleton, Multiset.sum_singleton, hd]
    · rcases n2_vdeg_cases n2v21 with ⟨_, h⟩ | ⟨hd, _⟩
      · exact absurd h.symm n2v_ne_11_21
      · rw [Multiset.map_singleton, Multiset.sum_singleton, hd]
  · -- backward: degree-sum 2 forces one of the three rosters
    intro hσ
    have hcard : σ.card ≤ 2 := by
      have hle : σ.card ≤ (σ.map fun v => ((n2T.vdeg v : ℕ))).sum := by
        clear hσ
        induction σ using Multiset.induction_on with
        | empty => simp
        | cons v σ' ih =>
          rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
          have := n2_vdeg_pos v
          omega
      omega
    have h012 : σ.card = 0 ∨ σ.card = 1 ∨ σ.card = 2 := by omega
    rcases h012 with hc | hc | hc
    · -- card 0: degree sum 0 ≠ 2
      rw [Multiset.card_eq_zero] at hc
      subst hc
      simp at hσ
    · -- card 1: a single degree-2 verdict
      rw [Multiset.card_eq_one] at hc
      obtain ⟨v, rfl⟩ := hc
      rw [Multiset.map_singleton, Multiset.sum_singleton] at hσ
      rcases n2_vdeg_cases v with ⟨hd, _⟩ | ⟨_, hv⟩
      · omega
      · rcases hv with rfl | rfl <;> simp [n2SigmasSet]
    · -- card 2: two degree-1 verdicts, both (1,1)
      rw [Multiset.card_eq_two] at hc
      obtain ⟨v, w, rfl⟩ := hc
      rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton] at hσ
      have hv1 : (n2T.vdeg v : ℕ) = 1 := by
        have := n2_vdeg_pos v; have := n2_vdeg_pos w; omega
      have hw1 : (n2T.vdeg w : ℕ) = 1 := by
        have := n2_vdeg_pos v; omega
      have hv : v = n2v11 := by
        rcases n2_vdeg_cases v with ⟨_, h⟩ | ⟨hd, _⟩
        · exact h
        · omega
      have hw : w = n2v11 := by
        rcases n2_vdeg_cases w with ⟨_, h⟩ | ⟨hd, _⟩
        · exact h
        · omega
      subst hv; subst hw
      simp [n2SigmasSet]

/-! ### D. Base-prime pools, the decided values Rval, and their laws. -/

private def n2PrimePools : Set ℚ := {q₀ : ℚ | ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)}

private lemma n2_prime_sub : n2PrimePools ⊆ n2M.Pools := by
  rintro q₀ ⟨p, hp, rfl⟩
  rw [n2_pools]
  exact ⟨p, hp, 1, by rw [PNat.one_coe, pow_one]⟩

/-- The decided per-σ values: the two note-displayed solve evaluations and 0 on
every other multiset (in particular on {(2,1)}, whose exit vector vanishes). -/
private noncomputable def n2RvalF : Multiset n2T.VType → ℚ → ℝ := fun σ q₀ =>
  if σ = {n2v12} then (((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ)
  else if σ = {n2v11, n2v11} then ((q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ)
  else 0

private lemma n2_den_pos {q₀ : ℚ} (hq : 2 ≤ q₀) : 0 < q₀ ^ 2 + q₀ + 1 := by
  nlinarith

private lemma n2_r_bdd : ∀ σ (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2RvalF σ q₀ ∈ Set.Icc (0 : ℝ) 1 := by
  intro σ q₀ hq
  have h2 : (2 : ℚ) ≤ q₀ := n2_pool_pos hq
  have hden := n2_den_pos h2
  unfold n2RvalF
  split_ifs with h1 h2'
  · constructor
    · have : (0 : ℚ) ≤ (q₀ + 1) / (q₀ ^ 2 + q₀ + 1) :=
        div_nonneg (by linarith) hden.le
      exact_mod_cast this
    · have : (q₀ + 1) / (q₀ ^ 2 + q₀ + 1) ≤ 1 :=
        (div_le_one hden).mpr (by nlinarith)
      exact_mod_cast this
  · constructor
    · have : (0 : ℚ) ≤ q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) :=
        div_nonneg (by positivity) hden.le
      exact_mod_cast this
    · have : q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) ≤ 1 :=
        (div_le_one hden).mpr (by nlinarith)
      exact_mod_cast this
  · exact ⟨le_refl 0, zero_le_one⟩

/-- The three roster elements are pairwise distinct as multisets. -/
private lemma n2_sigma_ne_1 : ({n2v11, n2v11} : Multiset n2T.VType) ≠ {n2v12} := by
  intro h
  have := congrArg Multiset.card h
  simp at this

private lemma n2_sigma_ne_2 : ({n2v11, n2v11} : Multiset n2T.VType) ≠ {n2v21} := by
  intro h
  have := congrArg Multiset.card h
  simp at this

private lemma n2_sigma_ne_3 : ({n2v12} : Multiset n2T.VType) ≠ {n2v21} := by
  intro h
  exact n2v_ne_12_21 (Multiset.singleton_inj.mp h)

/-- The checksum: the decided values sum to 1 at every pool ≥ 2 (in particular at
every base prime). -/
private lemma n2_rval_sum {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools) :
    (∑ σ ∈ n2SigmasSet, n2RvalF σ q₀) = 1 := by
  have h2 : (2 : ℚ) ≤ q₀ := n2_pool_pos hq
  have hden := n2_den_pos h2
  have hsum : (∑ σ ∈ n2SigmasSet, n2RvalF σ q₀)
      = n2RvalF {n2v11, n2v11} q₀ + (n2RvalF {n2v12} q₀ + n2RvalF {n2v21} q₀) := by
    unfold n2SigmasSet
    rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact n2_sigma_ne_1 h
      · exact n2_sigma_ne_2 h)]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact n2_sigma_ne_3)]
    rw [Finset.sum_singleton]
  rw [hsum]
  unfold n2RvalF
  rw [if_neg n2_sigma_ne_1, if_pos rfl, if_pos rfl,
    if_neg (fun h => n2_sigma_ne_3 h.symm),
    if_neg (fun h => n2_sigma_ne_2 h.symm), add_zero]
  have hq1 : (q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) + ((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hden.ne']
    ring
  exact_mod_cast hq1

/-- The gate's `prime_base` in the exact field form. -/
private lemma n2_prime_base : ∀ q₀, q₀ ∈ n2PrimePools ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ) :=
  fun _ => Iff.rfl

/-! ### D'. pools_e0 / legs_reg via the upstream per-prime packages. -/

private lemma n2_pools_e0 : ∀ e (he : e ∈ Finset.Icc 1 2),
    ∀ q₀ ∈ n2PrimePools ∩ allActivePools n2M,
    Nonempty (PoolHyp n2T n2M n2RB e (n2hK e he) q₀) := by
  intro e he q₀ hq₀
  exact n2_pools_all.2 e he q₀ hq₀.1

private lemma n2_legs_reg : ∀ p : ℕ, (p : ℚ) ∈ n2PrimePools →
    RegP n2T n2M n2RB p n2hK n2F := by
  intro p hp
  obtain ⟨p', hp', hpp⟩ := hp
  have hpe : p' = p := Nat.cast_injective hpp.symm
  rw [← hpe]
  exact n2_pools_all.1 p' hp'

/-! ### E0. Term-mode reduction lemmas for the concrete `n2M` fields (never
rewrite the shared `if e = 2` — it also indexes the cell Fin types). -/

private lemma n2M_μcell2 (τ : n2T.State 2) (x : n2M.Rep 2 τ)
    (c : n2M.Cell 2 τ) (q₀ : ℚ) :
    n2M.μcell 2 τ x c q₀
      = if c.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
        else if c.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
        else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 := rfl

private lemma n2M_μcell_ne {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (q₀ : ℚ) : n2M.μcell e τ x c q₀ = 1 := if_neg he

private lemma n2M_gwt2 (τ : n2T.State 2) (c : n2M.Cell 2 τ) (q₀ : ℚ) :
    n2M.gwt 2 τ c (0 : ℕ) q₀
      = if c.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
        else if c.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
        else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 := rfl

private lemma n2M_gwt_ne {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (c : n2M.Cell e τ)
    (q₀ : ℚ) : n2M.gwt e τ c (0 : ℕ) q₀ = 1 := if_neg he

private lemma n2M_rowVal2 (τ : n2T.State 2) (o : n2T.Out 2 τ) (q₀ : ℚ) :
    n2M.rowVal 2 τ o q₀
      = if o.1 = 0 then ((q₀ : ℝ))⁻¹ ^ 3
        else if o.1 = 1 then 1 - ((q₀ : ℝ))⁻¹
        else ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 := rfl

private lemma n2M_rowVal_ne {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (o : n2T.Out e τ)
    (q₀ : ℚ) : n2M.rowVal e τ o q₀ = if o.1 = 0 then 1 else 0 := if_neg he

private lemma n2M_kstep_def (k e : ℕ) (τ β : n2T.State e) (q₀ : ℚ) :
    n2M.kstep k e τ β q₀ = (if e = 2 then ((q₀ : ℝ))⁻¹ ^ 3 else 0) ^ k := rfl

private lemma n2M_kstep2 (k : ℕ) (τ β : n2T.State 2) (q₀ : ℚ) :
    n2M.kstep k 2 τ β q₀ = (((q₀ : ℝ))⁻¹ ^ 3) ^ k := rfl

private lemma n2M_kstep_ne {e : ℕ} (he : e ≠ 2) (k : ℕ) (τ β : n2T.State e)
    (q₀ : ℚ) : n2M.kstep k e τ β q₀ = 0 ^ k :=
  congrArg (· ^ k) (if_neg he)

private lemma n2M_cellEvt2 (τ : n2T.State 2) (x : n2M.Rep 2 τ) (c : n2M.Cell 2 τ)
    (q₀ : ℚ) (N : ℕ) :
    n2M.cellEvt 2 τ x c (0 : ℕ) q₀ N
      = if c.1 = 0 then Finset.univ.filter (fun y : n2M.Box q₀ N => y.1 < 1)
        else if c.1 = 1 then
          Finset.univ.filter (fun y : n2M.Box q₀ N => max 1 (q₀.num.toNat ^ 2) ≤ y.1)
        else Finset.univ.filter
          (fun y : n2M.Box q₀ N => 1 ≤ y.1 ∧ y.1 < max 1 (q₀.num.toNat ^ 2)) := rfl

private lemma n2M_cellEvt_ne {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (q₀ : ℚ) (N : ℕ) :
    n2M.cellEvt e τ x c (0 : ℕ) q₀ N = Finset.univ := if_neg he

private lemma n2M_cellEvt_ne0 (e : ℕ) (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) {h : ℕ} (hne : h ≠ 0) (q₀ : ℚ) (N : ℕ) :
    n2M.cellEvt e τ x c h q₀ N = ∅ := if_neg hne

private lemma n2M_cellOut_def (e : ℕ) (τ : n2T.State e) (c : n2M.Cell e τ) :
    n2M.cellOut e τ c = (⟨c.1 % 3, by omega⟩ : Fin 3) := rfl

private lemma n2M_cell_lt2 {τ : n2T.State 2} (c : n2M.Cell 2 τ) : c.1 < 3 := c.2

private lemma n2M_cell_eq0 {e : ℕ} (he : e ≠ 2) {τ : n2T.State e}
    (c : n2M.Cell e τ) : c.1 = 0 := by
  have h : c.1 < if e = 2 then 3 else 1 := c.2
  have h1 : (if e = 2 then 3 else 1) = 1 := if_neg he
  omega

private lemma n2T_out_lt {e : ℕ} {τ : n2T.State e} (o : n2T.Out e τ) : o.1 < 3 :=
  o.2

private lemma n2M_cell_card2 (τ : n2T.State 2) : Fintype.card (n2M.Cell 2 τ) = 3 :=
  Fintype.card_fin _

private lemma n2M_cell_card_ne {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) :
    Fintype.card (n2M.Cell e τ) = 1 := by
  rw [show Fintype.card (n2M.Cell e τ) = if e = 2 then 3 else 1 from Fintype.card_fin _,
    if_neg he]

private lemma n2M_HDom_mem {e : ℕ} {τ : n2T.State e} {c : n2M.Cell e τ}
    {h : ℕ} (hh : h ∈ n2M.HDom e τ c) : h = 0 := hh

private lemma n2M_ιDom_mem {e : ℕ} {τ : n2T.State e} {ε : n2M.EntShape e τ}
    {h : ℕ} (hh : h ∈ n2M.ιDom e τ ε) : h = 0 := hh

/-- Canonical block-2 outcome/cell constructors typed at the PROJECTIONS (keeps
the Membership/Singleton instances aligned — a raw `Fin.mk` pins them at `Fin 3`). -/
private def n2OutAt (τ : n2T.State 2) (k : ℕ) (h : k < 3) : n2T.Out 2 τ := ⟨k, h⟩

private def n2CellAt (τ : n2T.State 2) (k : ℕ) (h : k < 3) : n2M.Cell 2 τ := ⟨k, h⟩

/-- Elimination for membership in the three-way block-2 event split. -/
private lemma n2_evt_cases {q₀ : ℚ} {N : ℕ} (k : ℕ) (a : n2M.Box q₀ N)
    (ha : a ∈ (if k = 0 then Finset.univ.filter (fun y : n2M.Box q₀ N => y.1 < 1)
      else if k = 1 then
        Finset.univ.filter (fun y : n2M.Box q₀ N => max 1 (q₀.num.toNat ^ 2) ≤ y.1)
      else Finset.univ.filter
        (fun y : n2M.Box q₀ N => 1 ≤ y.1 ∧ y.1 < max 1 (q₀.num.toNat ^ 2)))) :
    (k = 0 ∧ a.1 < 1) ∨ (k = 1 ∧ max 1 (q₀.num.toNat ^ 2) ≤ a.1) ∨
    (k ≠ 0 ∧ k ≠ 1 ∧ 1 ≤ a.1 ∧ a.1 < max 1 (q₀.num.toNat ^ 2)) := by
  by_cases h0 : k = 0
  · rw [if_pos h0] at ha
    exact Or.inl ⟨h0, (Finset.mem_filter.mp ha).2⟩
  · rw [if_neg h0] at ha
    by_cases h1 : k = 1
    · rw [if_pos h1] at ha
      exact Or.inr (Or.inl ⟨h1, (Finset.mem_filter.mp ha).2⟩)
    · rw [if_neg h1] at ha
      exact Or.inr (Or.inr ⟨h0, h1, (Finset.mem_filter.mp ha).2⟩)

/-! ### E1. The ledger: LedgerIV at the concrete instance, field by field. -/

private lemma n2_ledger_xhd_sum : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.HDom e τ c => n2M.gwt e τ c h q₀) (n2M.μcell e τ x c q₀) := by
  intro e τ x c q₀ _ _
  refine hasSum_single (f := fun h : n2M.HDom e τ c => n2M.gwt e τ c h q₀)
    ⟨(0 : ℕ), rfl⟩ ?_
  intro b hb
  exact absurd (Subtype.ext (n2M_HDom_mem b.2)) hb

private lemma n2_ledger_xhd_no_stray : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∈ n2M.HDom e τ c → ∀ q₀ ∈ n2M.Pools,
    n2M.activeState q₀ e τ →
    ∃ N₀, ∀ N ≥ N₀, (n2M.cellEvt e τ x c h q₀ N).Nonempty := by
  intro e τ x c h hh q₀ hq _
  obtain ⟨m, hm2, rfl⟩ := n2_pool_nat hq
  obtain rfl : h = (0 : ℕ) := n2M_HDom_mem hh
  refine ⟨0, fun N _ => ?_⟩
  by_cases he : e = 2
  · subst he
    rw [n2M_cellEvt2]
    set Q := ((m : ℚ)).num.toNat with hQdef
    have hQ2 : 2 ≤ Q := by rw [hQdef, n2_pool_toNat]; exact hm2
    by_cases hc0 : c.1 = 0
    · rw [if_pos hc0]
      exact ⟨⟨0, lt_of_lt_of_le Nat.one_pos (le_max_left 1 (Q ^ 3))⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.one_pos⟩⟩
    · rw [if_neg hc0]
      by_cases hc1 : c.1 = 1
      · rw [if_pos hc1]
        refine ⟨⟨Q ^ 2, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) (by omega))
            (le_max_right 1 (Q ^ 3))
        · exact max_le (Nat.one_le_pow _ _ (by omega)) (le_refl _)
      · rw [if_neg hc1]
        refine ⟨⟨1, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨le_refl 1, ?_⟩⟩⟩
        · refine lt_of_lt_of_le ?_ (le_max_right 1 (Q ^ 3))
          calc 1 < Q := by omega
            _ ≤ Q ^ 3 := Nat.le_self_pow (by omega) Q
        · refine lt_of_lt_of_le ?_ (le_max_right 1 (Q ^ 2))
          calc 1 < Q := by omega
            _ ≤ Q ^ 2 := Nat.le_self_pow (by omega) Q
  · rw [n2M_cellEvt_ne he]
    haveI := n2M.boxpos (m : ℚ) N
    exact Finset.univ_nonempty

private lemma n2_ledger_xhd_no_orphan : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∉ n2M.HDom e τ c → ∀ (q₀ : ℚ) (N : ℕ),
    n2M.cellEvt e τ x c h q₀ N = ∅ := by
  intro e τ x c h hh q₀ N
  exact n2M_cellEvt_ne0 e τ x c (fun h0 => hh h0) q₀ N

private lemma n2_ledger_d4r0 : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ) (q₀ : ℚ)
    (N : ℕ) (c c' : n2M.Cell e τ) (h h' : n2M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (n2M.cellEvt e τ x c h q₀ N) (n2M.cellEvt e τ x c' h' q₀ N) := by
  intro e τ x q₀ N c c' h h' hne
  by_cases hh : h = (0 : ℕ)
  · by_cases hh' : h' = (0 : ℕ)
    · subst hh; subst hh'
      have hcc : c ≠ c' := fun hc => hne (by rw [hc])
      by_cases he : e = 2
      · subst he
        rw [n2M_cellEvt2, n2M_cellEvt2]
        have hc3 := n2M_cell_lt2 c
        have hc3' := n2M_cell_lt2 c'
        have hv : c.1 ≠ c'.1 := fun hv => hcc (Fin.ext hv)
        have hmax : 1 ≤ max 1 (q₀.num.toNat ^ 2) := le_max_left _ _
        rw [Finset.disjoint_left]
        intro a ha ha'
        rcases n2_evt_cases c.1 a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ <;>
          rcases n2_evt_cases c'.1 a ha' with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2, g3, g4⟩ <;>
          omega
      · exact absurd (Fin.ext ((n2M_cell_eq0 he c).trans (n2M_cell_eq0 he c').symm)) hcc
    · rw [n2M_cellEvt_ne0 e τ x c' hh' q₀ N]
      exact Finset.disjoint_empty_right _
  · rw [n2M_cellEvt_ne0 e τ x c hh q₀ N]
    exact Finset.disjoint_empty_left _

private lemma n2_ledger_part1 : ∀ e ∈ Finset.Icc 1 2, ∀ (τ : n2T.State e)
    (x : n2M.Rep e τ) (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    ∑ c : n2M.Cell e τ, n2M.μcell e τ x c q₀ = 1 := by
  intro e he τ x q₀ hq _
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp he
  interval_cases e
  · -- block 1: the single mass-1 cell
    have hval : ∀ c : n2M.Cell 1 τ, n2M.μcell 1 τ x c q₀ = 1 :=
      fun c => n2M_μcell_ne (by decide) τ x c q₀
    rw [Finset.sum_congr rfl (fun c _ => hval c), Finset.sum_const, Finset.card_univ,
      n2M_cell_card_ne (by decide) τ, one_smul]
  · -- block 2: q₀⁻³ + (1 − q₀⁻¹) + (q₀⁻¹ − q₀⁻³) = 1
    show ∑ c : Fin 3, n2M.μcell 2 τ x c q₀ = 1
    rw [Fin.sum_univ_three]
    have h0 : n2M.μcell 2 τ x ((0 : Fin 3) : n2M.Cell 2 τ) q₀ = ((q₀ : ℝ))⁻¹ ^ 3 := rfl
    have hone : n2M.μcell 2 τ x ((1 : Fin 3) : n2M.Cell 2 τ) q₀ = 1 - ((q₀ : ℝ))⁻¹ := rfl
    have htwo : n2M.μcell 2 τ x ((2 : Fin 3) : n2M.Cell 2 τ) q₀
        = ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 := rfl
    rw [h0, hone, htwo]
    ring

private lemma n2_ledger_rep_indep : ∀ e (τ : n2T.State e) (o : n2T.Out e τ)
    (x : n2M.Rep e τ) (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    n2M.rowVal e τ o q₀ = ∑ c ∈ n2M.cells e τ o, n2M.μcell e τ x c q₀ := by
  intro e τ o x q₀ _ _
  by_cases he : e = 2
  · subst he
    have hmem : n2CellAt τ o.1 (n2T_out_lt o) ∈ n2M.cells 2 τ o := by
      apply Set.mem_toFinset.mpr
      show n2M.cellOut 2 τ (n2CellAt τ o.1 (n2T_out_lt o)) = o
      apply Fin.ext
      show o.1 % 3 = o.1
      exact Nat.mod_eq_of_lt (n2T_out_lt o)
    have h0 : ∀ b ∈ n2M.cells 2 τ o, b ≠ n2CellAt τ o.1 (n2T_out_lt o) →
        n2M.μcell 2 τ x b q₀ = 0 := by
      intro b hb hbne
      exfalso
      apply hbne
      have hco0 := Set.mem_toFinset.mp hb
      have hco : n2M.cellOut 2 τ b = o := hco0
      have hval : b.1 % 3 = o.1 := congrArg Fin.val hco
      have hb3 := n2M_cell_lt2 b
      apply Fin.ext
      show b.1 = o.1
      omega
    calc n2M.rowVal 2 τ o q₀
        = n2M.μcell 2 τ x (n2CellAt τ o.1 (n2T_out_lt o)) q₀ := by
          rw [n2M_rowVal2]
          exact (n2M_μcell2 τ x (n2CellAt τ o.1 (n2T_out_lt o)) q₀).symm
      _ = ∑ c ∈ n2M.cells 2 τ o, n2M.μcell 2 τ x c q₀ :=
          (Finset.sum_eq_single_of_mem _ hmem h0).symm
  · have hval : ∀ c : n2M.Cell e τ, n2M.μcell e τ x c q₀ = 1 :=
      fun c => n2M_μcell_ne he τ x c q₀
    rw [Finset.sum_congr rfl (fun c _ => hval c), Finset.sum_const, n2M_rowVal_ne he]
    by_cases ho : o.1 = 0
    · rw [if_pos ho]
      have hcells : n2M.cells e τ o = Finset.univ := by
        ext c
        simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
          Finset.mem_univ, iff_true, n2M_cellOut_def]
        exact Fin.ext (show c.1 % 3 = o.1 by rw [n2M_cell_eq0 he c, ho])
      rw [hcells, Finset.card_univ, n2M_cell_card_ne he, one_smul]
    · rw [if_neg ho]
      have hcells : n2M.cells e τ o = ∅ := by
        ext c
        simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
          Finset.notMem_empty, iff_false, n2M_cellOut_def]
        intro hco
        have hval' : c.1 % 3 = o.1 := congrArg Fin.val hco
        have := n2M_cell_eq0 he c
        omega
      rw [hcells, Finset.card_empty, zero_smul]

private lemma n2_ledger_meas_card : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∈ n2M.HDom e τ c → ∀ q₀ ∈ n2M.Pools,
    n2M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    n2M.gwt e τ c h q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = ((n2M.cellEvt e τ x c h q₀ N).card : ℝ) := by
  intro e τ x c h hh q₀ hq _
  obtain ⟨m, hm2, rfl⟩ := n2_pool_nat hq
  obtain rfl : h = (0 : ℕ) := n2M_HDom_mem hh
  refine ⟨0, fun N _ => ?_⟩
  have hQm : ((m : ℚ)).num.toNat = m := n2_pool_toNat
  have hm0 : 0 < m := by omega
  have hb3 : max 1 (m ^ 3) = m ^ 3 := max_eq_right (Nat.one_le_pow _ _ hm0)
  have hb2 : max 1 (m ^ 2) = m ^ 2 := max_eq_right (Nat.one_le_pow _ _ hm0)
  have hcast : ((m : ℚ) : ℝ) = (m : ℝ) := by push_cast; rfl
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  by_cases he : e = 2
  · subst he
    rw [n2M_gwt2, n2M_cellEvt2, n2_box_card]
    by_cases hc0 : c.1 = 0
    · rw [if_pos hc0, if_pos hc0, n2_box_filter_lt (m : ℚ) N (le_max_left _ _), hQm,
        hb3, hcast]
      push_cast
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hmne)]
    · rw [if_neg hc0, if_neg hc0]
      by_cases hc1 : c.1 = 1
      · rw [if_pos hc1, if_pos hc1, n2_box_filter_ge, hQm, hb3, hb2, hcast]
        have hle : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.cast_sub hle]
        push_cast
        field_simp
        try ring
      · have hbb : max 1 (((m : ℚ)).num.toNat ^ 2) ≤ max 1 (((m : ℚ)).num.toNat ^ 3) := by
          rw [hQm, hb2, hb3]
          exact Nat.pow_le_pow_right (by omega) (by omega)
        rw [if_neg hc1, if_neg hc1, n2_box_filter_mid (m : ℚ) N hbb, hQm, hb3, hb2,
          hcast]
        have hle : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm0
        rw [Nat.cast_sub hle]
        push_cast
        field_simp
        try ring
  · rw [n2M_gwt_ne he, n2M_cellEvt_ne he, one_mul, Finset.card_univ]

/-- Reduction of the roster at blocks ≠ 2 to the canonical level-0 outcome
(N2ScsData's idiom: the block-1 outcome carriers are private in N2Shape). -/
private lemma n2_odata_const {e : ℕ} (he : e ≠ 2) (τ : n2T.State e) (o : n2T.Out e τ) :
    n2T.odata e τ o
      = n2T.odata 0 (() : n2T.State 0) ((0 : Fin 3) : n2T.Out 0 (() : n2T.State 0)) := by
  show (if e = 2 then _ else _) = _
  rw [if_neg he]
  rfl

private lemma n2_ledger_kstep_one : ∀ e (τ β : n2T.State e) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    n2M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : n2T.Out e τ | routeOf (n2T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (n2T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, n2M.rowVal e τ o q₀ := by
  intro e τ β q₀ _ _
  by_cases he : e = 2
  · subst he
    refine Eq.symm ((Finset.sum_eq_single_of_mem (n2OutAt τ 0 (by omega)) ?_ ?_).trans ?_)
    · -- membership of the o_K slot (instances inherited from the goal)
      apply Set.mem_toFinset.mpr
      exact ⟨rfl, ⟨2, 1, Sum.inr ()⟩, List.mem_singleton_self _, rfl, rfl⟩
    · -- every other outcome contributes 0 (vacuously: the set pins b = o_K)
      intro b hb hbne
      exfalso
      have hb0 := Set.mem_toFinset.mp hb
      obtain ⟨hr, -⟩ := hb0
      obtain ⟨v, hv⟩ := b
      interval_cases v
      · apply hbne
        apply Fin.ext
        rfl
      · exact Route.noConfusion ((show routeOf (n2T.odata 2 τ (⟨1, hv⟩ : Fin 3))
          = Route.termFin from rfl).symm.trans hr)
      · exact Route.noConfusion ((show routeOf (n2T.odata 2 τ (⟨2, hv⟩ : Fin 3))
          = Route.termFin from rfl).symm.trans hr)
    · -- the o_K row mass is the kernel entry
      rw [n2M_rowVal2, n2M_kstep2, pow_one]
      rfl
  · have hset : ({o : n2T.Out e τ | routeOf (n2T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (n2T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      } : Set (n2T.Out e τ)).toFinset = ∅ := by
      ext o
      rw [Set.mem_toFinset, Set.mem_setOf_eq]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨hr, -⟩
      rw [n2_odata_const he] at hr
      exact absurd hr (by decide)
    rw [n2M_kstep_ne he, hset, Finset.sum_empty, pow_one]

private lemma n2_ledger_hmc : ∀ (k : ℕ) e (τ β : n2T.State e) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    n2M.kstep (k + 1) e τ β q₀
      = ∑ γ : n2T.State e, n2M.kstep k e τ γ q₀ * n2M.kstep 1 e γ β q₀ := by
  intro k e τ β q₀ _ _
  haveI : Unique (n2T.State e) := ⟨⟨τ⟩, fun _ => rfl⟩
  rw [Fintype.sum_unique, n2M_kstep_def, n2M_kstep_def, n2M_kstep_def, ← pow_add]

private lemma n2_ledger_act_target : ∀ e (τ β : n2T.State e) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → ¬ n2M.activeState q₀ e β → n2M.kstep 1 e τ β q₀ = 0 :=
  fun _ _ _ _ _ hβ => absurd trivial hβ

private lemma n2_ledger_init_agg : ∀ e (τ : n2T.State e) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    n2M.ιval e τ q₀ = ∑ ε : n2M.EntShape e τ, n2M.ιsh e τ ε q₀ := by
  intro e τ q₀ _ _
  haveI : Unique (n2M.EntShape e τ) := ⟨⟨()⟩, fun _ => rfl⟩
  rw [Fintype.sum_unique]
  rfl

private lemma n2_ledger_init_count : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ)
    (h : n2M.Hgt), h ∈ n2M.ιDom e τ ε → ∀ q₀ ∈ n2M.Pools,
    n2M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    n2M.ιshH e τ ε h q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = ((n2M.entEvtH e τ ε h q₀ N).card : ℝ) := by
  intro e τ ε h hh q₀ _ _
  obtain rfl : h = (0 : ℕ) := n2M_ιDom_mem hh
  refine ⟨0, fun N _ => ?_⟩
  show (1 : ℝ) * (Fintype.card (n2M.Box q₀ N) : ℝ)
    = (((Finset.univ : Finset (n2M.Box q₀ N))).card : ℝ)
  rw [one_mul, Finset.card_univ]

private lemma n2_ledger_ent_count_card : ∀ e (τ : n2T.State e)
    (ε : n2M.EntShape e τ) (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    (n2M.entInst e τ ε q₀ (n2M.entLvl e τ ε)).card = n2M.entCount e τ ε q₀ :=
  fun e τ ε q₀ _ _ => Finset.card_singleton _

private lemma n2_ledger_comp_once : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ)
    (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.ιDom e τ ε => n2M.ιshH e τ ε h q₀) (n2M.ιsh e τ ε q₀) := by
  intro e τ ε q₀ _ _
  refine hasSum_single (f := fun h : n2M.ιDom e τ ε => n2M.ιshH e τ ε h q₀)
    ⟨(0 : ℕ), rfl⟩ ?_
  intro b hb
  exact absurd (Subtype.ext (n2M_ιDom_mem b.2)) hb

/-- THE ledger. -/
private theorem n2Ledger : LedgerIV n2T n2M :=
  { xhd_sum := n2_ledger_xhd_sum
    xhd_no_stray := n2_ledger_xhd_no_stray
    xhd_no_orphan := n2_ledger_xhd_no_orphan
    d4r0 := n2_ledger_d4r0
    part1 := n2_ledger_part1
    rep_indep := n2_ledger_rep_indep
    meas_card := n2_ledger_meas_card
    kstep_one := n2_ledger_kstep_one
    hmc := n2_ledger_hmc
    act_target := n2_ledger_act_target
    init_agg := n2_ledger_init_agg
    init_count := n2_ledger_init_count
    ent_count_card := n2_ledger_ent_count_card
    comp_once := n2_ledger_comp_once }

/-- The DEVICE 1-presentation (the chain fields `WshP`/`WshVal`/`wsh_ok`/
`wsh_interp` are OWNED by unit `n2_wshp_device` per blueprint §2.D "chain field
owned", R46/R52; the data live here because they are `n2ChainCore` fields):
countT = countS = 1, geom = 1, qpow = 0 — the trivial-denominator PolyGeom whose
value is 1, evaluating to 1 at every pool. -/
noncomputable def n2OnePG : PolyGeom where
  countT := 1
  degBoundT := 0
  degT_le := by simp
  countS := 1
  degBoundS := 0
  degS_le := by simp
  geom := 1
  qpow := 0
  geomDenoms := ∅
  geom_denom_dvd := by
    have h1 : (1 : Qq).denom = 1 := by
      rw [show (1 : Qq) = algebraMap (Polynomial ℚ) Qq 1 by simp]
      exact RatFunc.denom_algebraMap _
    simp [h1]

theorem n2OnePG_val : n2OnePG.val = 1 := by
  simp [n2OnePG, PolyGeom.val]

theorem n2OnePG_val_mem (q₀ : ℚ) : n2OnePG.val ∈ OKat q₀ := by
  rw [n2OnePG_val]; exact one_mem _

theorem n2OnePG_evalAt (q₀ : ℚ) (h : n2OnePG.val ∈ OKat q₀) :
    evalAt q₀ ⟨n2OnePG.val, h⟩ = 1 := by
  have hval : (⟨n2OnePG.val, h⟩ : OKat q₀) = 1 := Subtype.ext (by simp [n2OnePG_val])
  rw [hval, map_one]

/-! ### F. The symbolic R_σ at the gate: Rsh reduces to the block-2 solve. -/

/-- `powSubst δ` on a polynomial image is the polynomial base-change (local copy of
the PowSubstOK idiom). -/
private lemma n2_powSubst_algebraMap (δ : ℕ+) (p : Polynomial ℚ) :
    powSubst δ (algebraMap (Polynomial ℚ) Qq p)
      = algebraMap (Polynomial ℚ) Qq (p.comp (X ^ (δ : ℕ))) := by
  have hFG : (powSubst δ).comp (algebraMap (Polynomial ℚ) Qq)
      = (algebraMap (Polynomial ℚ) Qq).comp
          (Polynomial.eval₂RingHom Polynomial.C (X ^ (δ : ℕ))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        RatFunc.algebraMap_C, powSubst_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        powSubst_X]
  have h := RingHom.congr_fun hFG p
  simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.comp] using h

/-- δ = 1 substitution is the identity. -/
private lemma n2_powSubst_one (f : Qq) : powSubst 1 f = f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, n2_powSubst_algebraMap, n2_powSubst_algebraMap]
  simp [RatFunc.num_div_denom]

/-- Rsh at the device presentation = the block-2 solve (the root shape's single
δ = 1 leg; the decomposition subtype collapses at σ₀ = 0). -/
private lemma n2_Rsh_eq (hdet : DetHyp n2T n2RB n2hK) (σ : Multiset n2T.VType)
    (he : 2 ∈ Finset.Icc 1 2) :
    Rsh n2T n2M n2RB n2hdc n2hK hdet n2F (fun _ => n2OnePG) σ
      = blockSolve n2T n2RB n2hdc n2hK hdet 2 he n2τ σ := by
  have hconv : shConv n2T n2M n2RB n2hdc n2hK hdet n2RootShape σ
      = powSubst 1 (blockSolve n2T n2RB n2hdc n2hK hdet 2 he n2τ σ) := by
    unfold shConv
    have hsumF : ∀ F : Fin n2RootShape.k → Multiset n2T.VType,
        (∑ i, F i) = F (0 : Fin 1) := fun F => Fin.sum_univ_one F
    have hprop : σ = n2RootShape.σ0 + ∑ i : Fin n2RootShape.k,
        (fun _ => σ) i := by
      rw [hsumF]
      show σ = 0 + σ
      rw [zero_add]
    refine Eq.trans (Fintype.sum_eq_single ⟨fun _ => σ, hprop⟩ ?_) ?_
    · rintro ⟨g, hg⟩ hne
      exfalso
      apply hne
      have hg0 : g (0 : Fin 1) = σ := by
        have h2 := hg
        rw [hsumF] at h2
        have h3 : σ = 0 + g (0 : Fin 1) := h2
        rw [zero_add] at h3
        exact h3.symm
      apply Subtype.ext
      funext i
      have hi : i = ((0 : Fin 1) : Fin n2RootShape.k) := by
        haveI hs : Subsingleton (Fin n2RootShape.k) := by
          have hk : n2RootShape.k = 1 := rfl
          rw [hk]; infer_instance
        exact Subsingleton.elim i _
      rw [hi]
      exact hg0
    · have hprodF : ∀ F : Fin n2RootShape.k → Qq, (∏ i, F i) = F (0 : Fin 1) :=
        fun F => Fin.prod_univ_one F
      rw [hprodF]
      rfl
  unfold Rsh
  rw [show n2F.Sh = {n2RootShape} from rfl, Finset.sum_singleton]
  show n2OnePG.val * shConv n2T n2M n2RB n2hdc n2hK hdet n2RootShape σ = _
  rw [n2OnePG_val, one_mul, hconv, n2_powSubst_one]

private lemma n2_splitOuts_empty' (τ : n2T.State 2) : splitOuts n2T 2 τ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro o
  simp only [splitOuts, Set.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨v, hv⟩ := o
  interval_cases v
  · exact fun hr => Route.noConfusion ((show routeOf (n2T.odata 2 τ (⟨0, hv⟩ : Fin 3))
      = Route.kcol from rfl).symm.trans hr)
  · exact fun hr => Route.noConfusion ((show routeOf (n2T.odata 2 τ (⟨1, hv⟩ : Fin 3))
      = Route.termFin from rfl).symm.trans hr)
  · exact fun hr => Route.noConfusion ((show routeOf (n2T.odata 2 τ (⟨2, hv⟩ : Fin 3))
      = Route.termFin from rfl).symm.trans hr)

/-- The (2,1) exit vector vanishes: no terminal outcome emits {(2,1)}. -/
private lemma n2_bTerm_v21 (τ' : n2T.State 2) :
    bTerm n2T n2RB 2 {n2v21} τ' = 0 := by
  unfold bTerm
  apply Finset.sum_eq_zero
  intro o _
  rw [if_neg]
  rintro ⟨hr, hv⟩
  obtain ⟨v, hvlt⟩ := o
  interval_cases v
  · exact Route.noConfusion ((show routeOf (n2T.odata 2 τ' (⟨0, hvlt⟩ : Fin 3))
      = Route.kcol from rfl).symm.trans hr)
  · have hv' : ({n2v11, n2v11} : Multiset n2T.VType) = {n2v21} := hv
    exact n2_sigma_ne_2 hv'
  · have hv' : ({n2v12} : Multiset n2T.VType) = {n2v21} := hv
    exact n2_sigma_ne_3 hv'

/-- The solve at {(2,1)} is 0 (zero exit vector, no split legs). -/
private lemma n2_blockSolve_v21 (hdet : DetHyp n2T n2RB n2hK)
    (he : 2 ∈ Finset.Icc 1 2) :
    blockSolve n2T n2RB n2hdc n2hK hdet 2 he n2τ {n2v21} = 0 := by
  rw [blockSolve_eq]
  have hb : (fun τ' => bTerm n2T n2RB 2 {n2v21} τ' +
      bSplit n2T n2RB n2hdc 2 he
        (fun e' _ τ' σ'' =>
          if he' : e' ∈ Finset.Icc 1 2 then
            blockSolve n2T n2RB n2hdc n2hK hdet e' he' τ' σ''
          else 0) {n2v21} τ')
      = (0 : n2T.State 2 → Qq) := by
    funext τ'
    rw [n2_bTerm_v21, bSplit_def, n2_splitOuts_empty' τ', Finset.sum_empty, add_zero]
    rfl
  show ((1 - Kmat n2T n2RB 2 (n2hK 2 he))⁻¹ *ᵥ
      (bTerm n2T n2RB 2 {n2v21} +
        bSplit n2T n2RB n2hdc 2 he _ {n2v21})) n2τ = 0
  rw [show (bTerm n2T n2RB 2 {n2v21} +
      bSplit n2T n2RB n2hdc 2 he
        (fun e' _ τ' σ'' =>
          if he' : e' ∈ Finset.Icc 1 2 then
            blockSolve n2T n2RB n2hdc n2hK hdet e' he' τ' σ''
          else 0) {n2v21}) = 0 from hb, Matrix.mulVec_zero]
  rfl

/-! ### F'. OKat membership and evaluation of polynomial quotients. -/

private lemma n2_okat_alg (r : Polynomial ℚ) (q₀ : ℚ) :
    algebraMap (Polynomial ℚ) Qq r ∈ OKat q₀ := by
  rw [mem_OKat_iff, RatFunc.denom_algebraMap]
  simp

private lemma n2_evalAt_alg (r : Polynomial ℚ) (q₀ : ℚ)
    (hok : algebraMap (Polynomial ℚ) Qq r ∈ OKat q₀) :
    (evalAt q₀ ⟨algebraMap (Polynomial ℚ) Qq r, hok⟩ : ℚ) = r.eval q₀ := by
  show RatFunc.eval (RingHom.id ℚ) q₀ (algebraMap (Polynomial ℚ) Qq r) = r.eval q₀
  rw [RatFunc.eval_algebraMap]
  simp [Polynomial.eval₂_id]

private lemma n2_okat_div {p₁ p₂ : Polynomial ℚ} {q₀ : ℚ} (h₂ : p₂.eval q₀ ≠ 0) :
    (algebraMap (Polynomial ℚ) Qq p₁ / algebraMap (Polynomial ℚ) Qq p₂) ∈ OKat q₀ := by
  rw [mem_OKat_iff]
  intro h0
  obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd p₁ p₂
  rw [hc, Polynomial.eval_mul, h0, zero_mul] at h₂
  exact h₂ rfl

private lemma n2_evalAt_div {p₁ p₂ : Polynomial ℚ} {q₀ : ℚ} (h₂ : p₂.eval q₀ ≠ 0)
    (hok : (algebraMap (Polynomial ℚ) Qq p₁ / algebraMap (Polynomial ℚ) Qq p₂) ∈ OKat q₀) :
    (evalAt q₀ ⟨algebraMap (Polynomial ℚ) Qq p₁ / algebraMap (Polynomial ℚ) Qq p₂, hok⟩ : ℚ)
      = p₁.eval q₀ / p₂.eval q₀ := by
  have hp₂ : p₂ ≠ 0 := fun h0 => h₂ (by rw [h0]; simp)
  have halg : algebraMap (Polynomial ℚ) Qq p₂ ≠ 0 := RatFunc.algebraMap_ne_zero hp₂
  have hmul : (⟨algebraMap (Polynomial ℚ) Qq p₁ / algebraMap (Polynomial ℚ) Qq p₂, hok⟩ :
        OKat q₀) * ⟨algebraMap (Polynomial ℚ) Qq p₂, n2_okat_alg p₂ q₀⟩
      = ⟨algebraMap (Polynomial ℚ) Qq p₁, n2_okat_alg p₁ q₀⟩ :=
    Subtype.ext (div_mul_cancel₀ _ halg)
  have hev := congrArg (fun z => (evalAt q₀ z : ℚ)) hmul
  simp only [map_mul] at hev
  rw [n2_evalAt_alg, n2_evalAt_alg] at hev
  rw [eq_div_iff h₂]
  exact hev

/-- rsh_interp at the gate: the evaluations of R_σ at every base prime are the
decided values (the two note-displayed solve entries and 0 at {(2,1)}). -/
private lemma n2_rsh_interp : ∀ σ ∈ n2SigmasSet, ∀ p ∈ n2PrimePools,
    ∀ hdet : DetHyp n2T n2RB n2hK,
    ∃ hok : Rsh n2T n2M n2RB n2hdc n2hK hdet n2F (fun _ => n2OnePG) σ ∈ OKat p,
      ((evalAt p ⟨Rsh n2T n2M n2RB n2hdc n2hK hdet n2F (fun _ => n2OnePG) σ, hok⟩ : ℚ) : ℝ)
        = n2RvalF σ p := by
  intro σ hσ p hp hdet
  obtain ⟨pp, hpp, rfl⟩ := hp
  have hpool : ((pp : ℚ)) ∈ n2M.Pools := n2_prime_sub ⟨pp, hpp, rfl⟩
  have h2 : (2 : ℚ) ≤ (pp : ℚ) := n2_pool_pos hpool
  have hden : ((pp : ℚ) ^ 2 + (pp : ℚ) + 1) ≠ 0 := (n2_den_pos h2).ne'
  have he2 : 2 ∈ Finset.Icc 1 2 := by decide
  have hevden : (X ^ 2 + X + 1 : Polynomial ℚ).eval (pp : ℚ) ≠ 0 := by
    simpa using hden
  rw [n2_Rsh_eq hdet σ he2]
  simp only [n2SigmasSet, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl
  · -- σ = {(1,1)²}: β = q²/(q²+q+1)
    have hbs : blockSolve n2T n2RB n2hdc n2hK hdet 2 he2 n2τ {n2v11, n2v11}
        = algebraMap (Polynomial ℚ) Qq (X ^ 2)
          / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) := (n2_solve_vals he2).2
    rw [hbs]
    refine ⟨n2_okat_div hevden, ?_⟩
    rw [n2_evalAt_div hevden]
    unfold n2RvalF
    rw [if_neg n2_sigma_ne_1, if_pos rfl]
    norm_num
  · -- σ = {(1,2)}: β = (q+1)/(q²+q+1)
    have hbs : blockSolve n2T n2RB n2hdc n2hK hdet 2 he2 n2τ {n2v12}
        = algebraMap (Polynomial ℚ) Qq (X + 1)
          / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) := (n2_solve_vals he2).1
    rw [hbs]
    refine ⟨n2_okat_div hevden, ?_⟩
    rw [n2_evalAt_div hevden]
    unfold n2RvalF
    rw [if_pos rfl]
    norm_num
  · -- σ = {(2,1)}: β = 0
    rw [n2_blockSolve_v21 hdet he2]
    refine ⟨zero_mem _, ?_⟩
    have h0 : (⟨(0 : Qq), zero_mem _⟩ : OKat (pp : ℚ)) = 0 := rfl
    rw [h0, map_zero]
    unfold n2RvalF
    rw [if_neg (fun h => n2_sigma_ne_3 h.symm), if_neg (fun h => n2_sigma_ne_2 h.symm)]
    norm_num

/-- The device W17ii height-sum instance.  Since ratification 2026-07-28 finding 4
this is no longer a field VALUE: `RS4Chain.wsh17_pin` is a PROJECTION-DEF equal to
`W17ii` at the chain's carriers, and this Prop is definitionally
`n2ChainCore.wsh17_pin` (the device carriers below are literals).  Discharged
sorry-free at unit `n2_rsh` (N2Rsh.lean).
This is the `W17ii` display's CONCLUSION instantiated at the device carriers
(`WshP ≡ n2OnePG`, `WshVal ≡ 1`, `shDom ≡ {0}`, `shWeightH ≡ 1` — the literals the
core's fields reduce to): at every shape and pool, the W-presentation evaluates to
the W-value AND the height weights over the height class sum to that value.  The
`Wsh17Package` premises are seam objects (S-8) with no E-phase carrier, so the
device instance is premise-free (stronger).  Discharged sorry-free at unit
`n2_rsh` (N2Rsh.lean); wave-4 re-keying replaces the field (§W4-SYNC S-8). -/
def n2Wsh17Device : Prop :=
  ∀ Ŝ ∈ n2F.Sh, ∀ q₀ ∈ n2M.Pools,
    (∃ hok : n2OnePG.val ∈ OKat q₀,
      ((evalAt q₀ ⟨n2OnePG.val, hok⟩ : ℚ) : ℝ) = 1) ∧
    HasSum (fun _h : ({0} : Set ℕ) => (1 : ℝ)) 1

/-- The chain CORE (P-phase, D-5 sorried-data idiom; deviation recorded at unit
`n2_x3`): carries EVERY field of the full instantiation.  Its `decidedTotal`
slot is superseded in `n2Chain` below by the blueprint's definitional pin
(§3b `n2_x3`: "decidedTotal := Σ Rval") — the n2_sigmas P-phase fill goes HERE;
`n2Chain` then inherits all fields with that one definitional override.
Assembled by obligation group (the n2M idiom): the DEVICE shallow-carrier group
(shDom/shEvtH/visH/shEvt/shWeightH + shevt_grouping) is the `n2_sh_events` fill —
the singleton height class {0}, the full-box event at the one height (so the
grouping is `singleton_biUnion`), weight = the WshVal total at the one height.
`WshVal := 1` is the `n2_wshp_device` value (pinned to 1 at pools by that unit's
display; the VALUE is placed here because `n2_sh_events`'s shWeightH pin needs it
definitionally — wsh_interp/wshval_bdd etc. stay with their owning units).  All
other groups awaiting their owning units' fills. -/
noncomputable def n2ChainCore : RS4Chain n2T n2M n2RB n2hdc n2hK n2F where
  L := n2Ledger
  B := n2B
  hns := n2_rexact.1
  PrimePools := n2PrimePools
  prime_sub := n2_prime_sub
  prime_base := n2_prime_base
  pools_e0 := n2_pools_e0
  legs_reg := n2_legs_reg
  Sigmas := n2SigmasSet
  sig_exact := n2_sig_exact
  -- legs_read (ratification 2026-07-28 finding 1): VACUOUS at the gate — every
  -- consumed pool p^δ lies in n2M.Pools (pools_closed) and every n2 state is
  -- active at every pool, so NO non-all-active consumed pool exists.
  legs_read := fun p hp δ _ hnot _ =>
    absurd ⟨n2M.pools_closed (p : ℚ) (n2_prime_sub hp) δ, fun _ _ _ => trivial⟩ hnot
  -- DEVICE 1-presentation fields (unit n2_wshp_device, R46/R52 — data below at n2OnePG):
  WshP := fun _ => n2OnePG
  wsh_ok := fun _ _ q₀ _ => n2OnePG_val_mem q₀
  -- (wsh17_pin is NO LONGER a field — ratification finding 4: it is the
  -- projection-def RS4Chain.wsh17_pin = W17ii at these carriers = n2Wsh17Device,
  -- discharged at unit n2_rsh.)
  WshVal := fun _ _ => 1
  wsh_interp := fun _ _ q₀ _ => by
    show ((evalAt q₀ ⟨n2OnePG.val, n2OnePG_val_mem q₀⟩ : ℚ) : ℝ) = 1
    rw [n2OnePG_evalAt]; norm_num
  wshval_bdd := fun _ _ _ _ => ⟨zero_le_one, le_refl 1⟩
  -- DEVICE shallow carriers (unit n2_sh_events, R52 + R55):
  shDom := fun _ => ({0} : Set ℕ)
  shEvtH := fun _ _ _ _ => Finset.univ
  visH := fun _ _ _ => ({0} : Finset ℕ)
  shEvt := fun _ _ _ => Finset.univ
  shWeightH := fun _ _ _ => 1
  shevt_grouping := fun _ _ _ => Finset.singleton_biUnion.symm
  shDom_ne := fun _ _ => ⟨(0 : ℕ), rfl⟩
  sh_realized := fun _ _ q₀ _ => ⟨0, fun N _ => by
    haveI := n2M.boxpos q₀ N
    exact Finset.univ_nonempty⟩
  shweight_card := fun _ _ h _ q₀ _ => ⟨0, fun N _ => by
    show (1 : ℝ) * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = (((Finset.univ : Finset (n2M.Box q₀ N))).card : ℝ)
    rw [one_mul, Finset.card_univ]⟩
  wshval_card := fun _ _ q₀ _ => ⟨0, fun N _ => by
    show (1 : ℝ) * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = (((Finset.univ : Finset (n2M.Box q₀ N))).card : ℝ)
    rw [one_mul, Finset.card_univ]⟩
  Rval := n2RvalF
  r_bdd := n2_r_bdd
  decidedTotal := fun q₀ => ∑ σ ∈ n2SigmasSet, n2RvalF σ q₀
  x3_total := fun p hp => n2_rval_sum (n2_prime_sub hp)
  rs1_equates := fun _ _ => rfl
  rsh_interp := n2_rsh_interp

/-- The gate's RS4Chain (FULL instantiation; wave-4 re-keying replaces exactly the
device fields named at §W4-SYNC S-8/S-10). -/
noncomputable def n2Chain : RS4Chain n2T n2M n2RB n2hdc n2hK n2F :=
  { n2ChainCore with
    decidedTotal := fun q₀ => ∑ σ ∈ n2ChainCore.Sigmas, n2ChainCore.Rval σ q₀
    x3_total := fun p hp =>
      (n2ChainCore.rs1_equates p hp).trans (n2ChainCore.x3_total p hp)
    rs1_equates := fun p hp => rfl }

theorem n2_sigmas :
    n2Chain.Sigmas = {{n2v11, n2v11}, {n2v12}, {n2v21}} :=
  rfl

end LeanUrat.MovesS
