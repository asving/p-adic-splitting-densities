/-
Unit U28.gate_order0_sep  (HC-2 campaign, E-phase — blueprint §5 Layer E)
moves_ref: the V2 gate's mirror at the tame prime q′ = 3 (realF2: split ≠ inert at
q′ = 3): the split and inert root histories yield DIFFERENT masses — σ-separation
through the bridge, as a stratum-count inequality at a fixed small N.
deps: U13 (concrete seeds), MovesC.thmC_b.  difficulty: medium.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ### §1 — p-adic digit extraction (p = 3)

The base-stage residual needs the digit of `x` at a level `k` with `3^k ∣ x`: the residue of
the exact quotient. Everything below is elementary DVR bookkeeping. -/

private lemma three_ne_zero' : (3:ℤ_[3]) ≠ 0 := by norm_num

private lemma three_pow_ne (k : ℕ) : ((3:ℤ_[3])^k) ≠ 0 := pow_ne_zero _ three_ne_zero'

private lemma pow_dvd_iff_le_val {x : ℤ_[3]} (hx : x ≠ 0) (n : ℕ) :
    (3:ℤ_[3])^n ∣ x ↔ n ≤ x.valuation := by
  rw [show (3:ℤ_[3]) = ((3:ℕ):ℤ_[3]) by norm_num]
  exact Ideal.mem_span_singleton.symm.trans (PadicInt.mem_span_pow_iff_le_valuation x hx n)

open Classical in
/-- The level-`k` digit of `x` (junk `0` unless `3^k ∣ x`): residue of the exact quotient. -/
private noncomputable def digAt (x : ℤ_[3]) (k : ℕ) : ZMod 3 :=
  if h : (3:ℤ_[3])^k ∣ x then PadicInt.toZMod h.choose else 0

private lemma digAt_spec {x y : ℤ_[3]} {k : ℕ} (h : x = (3:ℤ_[3])^k * y) :
    digAt x k = PadicInt.toZMod y := by
  have hd : (3:ℤ_[3])^k ∣ x := ⟨y, h⟩
  rw [digAt, dif_pos hd]
  congr 1
  exact mul_left_cancel₀ (three_pow_ne k) (by rw [← hd.choose_spec, h])

private lemma digAt_zero (k : ℕ) : digAt 0 k = 0 := by
  rw [digAt_spec (y := 0) (by ring), map_zero]

private lemma digAt_add {x y : ℤ_[3]} {k : ℕ} (hx : (3:ℤ_[3])^k ∣ x) (hy : (3:ℤ_[3])^k ∣ y) :
    digAt (x + y) k = digAt x k + digAt y k := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  rw [digAt_spec (y := a) rfl, digAt_spec (y := b) rfl,
    digAt_spec (y := a + b) (by ring), map_add]

private lemma digAt_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ_[3]) (k : ℕ)
    (h : ∀ i ∈ s, (3:ℤ_[3])^k ∣ f i) :
    digAt (∑ i ∈ s, f i) k = ∑ i ∈ s, digAt (f i) k := by
  classical
  induction s using Finset.induction with
  | empty => simp [digAt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      digAt_add (h a (Finset.mem_insert_self a s))
        (Finset.dvd_sum fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- A digit strictly below the divisibility level vanishes. -/
private lemma digAt_of_dvd_succ {x : ℤ_[3]} {k : ℕ} (h : (3:ℤ_[3])^(k+1) ∣ x) :
    digAt x k = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [pow_succ, mul_assoc, digAt_spec (y := 3 * y) rfl, map_mul]
  have : (PadicInt.toZMod (3:ℤ_[3]) : ZMod 3) = 0 := by
    rw [show (3:ℤ_[3]) = ((3:ℕ):ℤ_[3]) by norm_num, map_natCast]
    decide
  rw [this, zero_mul]

/-- The digit AT the exact valuation is the (nonzero) unit digit. -/
private lemma digAt_val_ne {x : ℤ_[3]} (hx : x ≠ 0) : digAt x x.valuation ≠ 0 := by
  have hspec := PadicInt.unitCoeff_spec hx
  have : digAt x x.valuation = PadicInt.toZMod (PadicInt.unitCoeff hx : ℤ_[3]) := by
    refine digAt_spec ?_
    conv_lhs => rw [hspec]
    push_cast
    ring
  rw [this]
  exact (IsUnit.map PadicInt.toZMod (PadicInt.unitCoeff hx).isUnit).ne_zero

/-- A nonzero digit certifies the exact valuation. -/
private lemma digAt_ne_zero {x : ℤ_[3]} {k : ℕ} (h : digAt x k ≠ 0) :
    x ≠ 0 ∧ x.valuation = k := by
  have hx : x ≠ 0 := by rintro rfl; exact h (digAt_zero k)
  have hd : (3:ℤ_[3])^k ∣ x := by
    by_contra hnd; rw [digAt, dif_neg hnd] at h; exact h rfl
  have hk : k ≤ x.valuation := (pow_dvd_iff_le_val hx k).mp hd
  refine ⟨hx, ?_⟩
  by_contra hne
  exact h (digAt_of_dvd_succ ((pow_dvd_iff_le_val hx (k+1)).mpr (by omega)))

/-- Digit of a product at the sum of two divisibility levels. -/
private lemma digAt_mul_level {x y : ℤ_[3]} {a b : ℕ}
    (hx : (3:ℤ_[3])^a ∣ x) (hy : (3:ℤ_[3])^b ∣ y) :
    digAt (x * y) (a + b) = digAt x a * digAt y b := by
  obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy
  rw [digAt_spec (y := u) rfl, digAt_spec (y := v) rfl,
    digAt_spec (y := u * v) (by ring), map_mul]

/-! ### §2 — the base weight `bwN f = min_j (v₃(f_j) + j)` and the initial form -/

/-- The (1,1)-weighted Gauss weight (ℕ-valued; junk 0 at `f = 0`). -/
private noncomputable def bwN (f : Polynomial ℤ_[3]) : ℕ :=
  if h : f.support.Nonempty then f.support.inf' h (fun j => (f.coeff j).valuation + j) else 0

private lemma bwN_le {f : Polynomial ℤ_[3]} {j : ℕ} (hj : j ∈ f.support) :
    bwN f ≤ (f.coeff j).valuation + j := by
  rw [bwN, dif_pos ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

private lemma bwN_exists {f : Polynomial ℤ_[3]} (hf : f ≠ 0) :
    ∃ j ∈ f.support, (f.coeff j).valuation + j = bwN f := by
  have h : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [bwN, dif_pos h]
  obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_inf' h (fun j => (f.coeff j).valuation + j)
  exact ⟨j, hj, hje.symm⟩

/-- Every coefficient is divisible by `3^(bwN f − j)`. -/
private lemma bwN_dvd (f : Polynomial ℤ_[3]) (j : ℕ) :
    (3:ℤ_[3])^(bwN f - j) ∣ f.coeff j := by
  by_cases hj : j ∈ f.support
  · have h1 := bwN_le hj
    have h2 : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    exact (pow_dvd_iff_le_val h2 _).mpr (by omega)
  · rw [Polynomial.mem_support_iff, not_not] at hj
    rw [hj]; exact dvd_zero _

/-- The initial form of `f` in `𝔽₃[z]`: the unit digits of the minimizing slots. -/
private noncomputable def ini (f : Polynomial ℤ_[3]) : Polynomial (ZMod 3) :=
  ∑ j ∈ f.support.filter (fun j => (f.coeff j).valuation + j = bwN f),
    Polynomial.C (digAt (f.coeff j) ((f.coeff j).valuation)) * Polynomial.X ^ j

private lemma ini_coeff (f : Polynomial ℤ_[3]) (i : ℕ) :
    (ini f).coeff i =
      if i ∈ f.support ∧ (f.coeff i).valuation + i = bwN f
      then digAt (f.coeff i) ((f.coeff i).valuation) else 0 := by
  classical
  rw [ini, Polynomial.finset_sum_coeff]
  have hterm : ∀ j,
      (Polynomial.C (digAt (f.coeff j) ((f.coeff j).valuation)) * Polynomial.X ^ j).coeff i
        = if j = i then digAt (f.coeff j) ((f.coeff j).valuation) else 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : j = i
    · simp [h]
    · rw [if_neg (fun he : i = j => h he.symm), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq']
  simp only [Finset.mem_filter]

/-- Coefficient formula in the digit normal form, valid for `i ≤ bwN f`. -/
private lemma ini_coeff_le {f : Polynomial ℤ_[3]} (i : ℕ) (hi : i ≤ bwN f) :
    (ini f).coeff i = digAt (f.coeff i) (bwN f - i) := by
  rw [ini_coeff]
  by_cases h : i ∈ f.support ∧ (f.coeff i).valuation + i = bwN f
  · rw [if_pos h]
    congr 1
    omega
  · rw [if_neg h]
    by_cases hs : i ∈ f.support
    · have hv := bwN_le hs
      have hne : (f.coeff i).valuation + i ≠ bwN f := fun he => h ⟨hs, he⟩
      have hne' : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hs
      refine (digAt_of_dvd_succ ((pow_dvd_iff_le_val hne' _).mpr (by omega))).symm
    · rw [Polynomial.mem_support_iff, not_not] at hs
      rw [hs, digAt_zero]

private lemma ini_coeff_gt {f : Polynomial ℤ_[3]} {i : ℕ} (hi : bwN f < i) :
    (ini f).coeff i = 0 := by
  rw [ini_coeff, if_neg]
  rintro ⟨-, he⟩
  omega

private lemma ini_natDegree_le (f : Polynomial ℤ_[3]) : (ini f).natDegree ≤ bwN f :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun _ h => ini_coeff_gt h

private lemma ini_ne_zero {f : Polynomial ℤ_[3]} (hf : f ≠ 0) : ini f ≠ 0 := by
  obtain ⟨j, hj, hje⟩ := bwN_exists hf
  have hc : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have : (ini f).coeff j ≠ 0 := by
    rw [ini_coeff, if_pos ⟨hj, hje⟩]
    exact digAt_val_ne hc
  exact fun h0 => this (by rw [h0, Polynomial.coeff_zero])

/-! ### §3 — multiplicativity of the weight and the initial form (the Gauss argument) -/

private lemma pow_dvd_coeff_pair (f g : Polynomial ℤ_[3]) (x : ℕ × ℕ) (m : ℕ)
    (hm : m ≤ (bwN f - x.1) + (bwN g - x.2)) :
    (3:ℤ_[3])^m ∣ f.coeff x.1 * g.coeff x.2 :=
  dvd_trans (pow_dvd_pow _ hm)
    (by rw [pow_add]; exact mul_dvd_mul (bwN_dvd f x.1) (bwN_dvd g x.2))

private lemma coeff_mul_dvd (f g : Polynomial ℤ_[3]) (i : ℕ) :
    (3:ℤ_[3])^(bwN f + bwN g - i) ∣ (f * g).coeff i := by
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum fun x hx => ?_
  have hjk := Finset.mem_antidiagonal.mp hx
  exact pow_dvd_coeff_pair f g x _ (by omega)

/-- The digit convolution: the level-`(bwf+bwg−i)` digit of `(f·g)ᵢ` is the `i`-th coefficient
of `ini f · ini g`. -/
private lemma digAt_coeff_mul (f g : Polynomial ℤ_[3]) (i : ℕ) (hi : i ≤ bwN f + bwN g) :
    digAt ((f * g).coeff i) (bwN f + bwN g - i) = (ini f * ini g).coeff i := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
    digAt_sum _ _ _ (fun x hx => by
      have hjk := Finset.mem_antidiagonal.mp hx
      exact pow_dvd_coeff_pair f g x _ (by omega))]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hjk := Finset.mem_antidiagonal.mp hx
  by_cases h1 : x.1 ≤ bwN f
  · by_cases h2 : x.2 ≤ bwN g
    · have he : bwN f + bwN g - i = (bwN f - x.1) + (bwN g - x.2) := by omega
      rw [he, digAt_mul_level (bwN_dvd f x.1) (bwN_dvd g x.2),
        ini_coeff_le x.1 h1, ini_coeff_le x.2 h2]
    · have hdvd : (3:ℤ_[3])^(bwN f + bwN g - i + 1) ∣ f.coeff x.1 * g.coeff x.2 :=
        pow_dvd_coeff_pair f g x _ (by omega)
      rw [digAt_of_dvd_succ hdvd, ini_coeff_gt (show bwN g < x.2 by omega), mul_zero]
  · have hdvd : (3:ℤ_[3])^(bwN f + bwN g - i + 1) ∣ f.coeff x.1 * g.coeff x.2 :=
      pow_dvd_coeff_pair f g x _ (by omega)
    rw [digAt_of_dvd_succ hdvd, ini_coeff_gt (show bwN f < x.1 by omega), zero_mul]

private lemma ini_mul_natDegree_le (f g : Polynomial ℤ_[3]) :
    (ini f * ini g).natDegree ≤ bwN f + bwN g :=
  le_trans Polynomial.natDegree_mul_le (add_le_add (ini_natDegree_le f) (ini_natDegree_le g))

private lemma bwN_mul {f g : Polynomial ℤ_[3]} (hf : f ≠ 0) (hg : g ≠ 0) :
    bwN (f * g) = bwN f + bwN g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hne : ini f * ini g ≠ 0 := mul_ne_zero (ini_ne_zero hf) (ini_ne_zero hg)
  obtain ⟨i₀, hi₀s⟩ := Polynomial.support_nonempty.mpr hne
  have hi₀ : (ini f * ini g).coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀s
  have hi₀le : i₀ ≤ bwN f + bwN g :=
    le_trans (Polynomial.le_natDegree_of_ne_zero hi₀) (ini_mul_natDegree_le f g)
  have hdig : digAt ((f*g).coeff i₀) (bwN f + bwN g - i₀) ≠ 0 := by
    rw [digAt_coeff_mul f g i₀ hi₀le]; exact hi₀
  obtain ⟨hc0, hval⟩ := digAt_ne_zero hdig
  refine le_antisymm ?_ ?_
  · have := bwN_le (Polynomial.mem_support_iff.mpr hc0)
    omega
  · obtain ⟨j, hj, hje⟩ := bwN_exists hfg
    have hcj : (f*g).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have := (pow_dvd_iff_le_val hcj _).mp (coeff_mul_dvd f g j)
    omega

private lemma ini_mul {f g : Polynomial ℤ_[3]} (hf : f ≠ 0) (hg : g ≠ 0) :
    ini (f * g) = ini f * ini g := by
  ext i
  by_cases hi : i ≤ bwN f + bwN g
  · rw [ini_coeff_le i (by rw [bwN_mul hf hg]; exact hi), bwN_mul hf hg,
      digAt_coeff_mul f g i hi]
  · rw [ini_coeff_gt (by rw [bwN_mul hf hg]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (ini_mul_natDegree_le f g) (by omega))]

/-! ### §4 — the additive laws -/

private lemma bwN_add_ge {f g : Polynomial ℤ_[3]} (hfg : f + g ≠ 0) (m : ℕ)
    (hmf : m ≤ bwN f) (hmg : m ≤ bwN g) : m ≤ bwN (f + g) := by
  obtain ⟨j, hj, hje⟩ := bwN_exists hfg
  have hcj : (f+g).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hdvd : (3:ℤ_[3])^(m - j) ∣ (f + g).coeff j := by
    rw [Polynomial.coeff_add]
    exact dvd_add (dvd_trans (pow_dvd_pow _ (by omega)) (bwN_dvd f j))
      (dvd_trans (pow_dvd_pow _ (by omega)) (bwN_dvd g j))
  have := (pow_dvd_iff_le_val hcj _).mp hdvd
  omega

private lemma ini_add {f g : Polynomial ℤ_[3]} (_hfg : f + g ≠ 0)
    (hEq : bwN f = bwN g) (hsum : bwN (f + g) = bwN f) :
    ini (f + g) = ini f + ini g := by
  ext i
  rw [Polynomial.coeff_add]
  by_cases hi : i ≤ bwN f
  · rw [ini_coeff_le i (by omega), ini_coeff_le i hi, ini_coeff_le i (by omega), hsum,
      Polynomial.coeff_add,
      digAt_add (bwN_dvd f i) (by rw [hEq]; exact bwN_dvd g i), hEq]
  · rw [ini_coeff_gt (show bwN (f+g) < i by omega), ini_coeff_gt (show bwN f < i by omega),
      ini_coeff_gt (show bwN g < i by omega), add_zero]

/-- The dominant-summand package: `w f < w g` forces `f + g ≠ 0`, `w (f+g) = w f`,
`ini (f+g) = ini f`. -/
private lemma add_lt_pack {f g : Polynomial ℤ_[3]} (hf : f ≠ 0)
    (hlt : bwN f < bwN g) :
    f + g ≠ 0 ∧ bwN (f + g) = bwN f ∧ ini (f + g) = ini f := by
  obtain ⟨j₀, hj₀, hje⟩ := bwN_exists hf
  have hcj : f.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀
  have hgd : ∀ i : ℕ, i ≤ bwN f → (3:ℤ_[3])^(bwN f - i + 1) ∣ g.coeff i := fun i hile =>
    dvd_trans (pow_dvd_pow _ (by omega)) (bwN_dvd g i)
  have hdig : digAt ((f+g).coeff j₀) (bwN f - j₀) ≠ 0 := by
    rw [Polynomial.coeff_add,
      digAt_add (bwN_dvd f j₀) (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) (hgd j₀ (by omega))),
      digAt_of_dvd_succ (hgd j₀ (by omega)), add_zero]
    have hlv : bwN f - j₀ = (f.coeff j₀).valuation := by omega
    rw [hlv]
    exact digAt_val_ne hcj
  obtain ⟨hc0, hval⟩ := digAt_ne_zero hdig
  have hfg : f + g ≠ 0 := fun h => hc0 (by rw [h, Polynomial.coeff_zero])
  have hup : bwN (f+g) ≤ bwN f := by
    have := bwN_le (Polynomial.mem_support_iff.mpr hc0)
    omega
  have hbw : bwN (f+g) = bwN f :=
    le_antisymm hup (bwN_add_ge hfg (bwN f) le_rfl (by omega))
  refine ⟨hfg, hbw, ?_⟩
  ext i
  by_cases hi : i ≤ bwN f
  · rw [ini_coeff_le i (by omega), ini_coeff_le i hi, hbw, Polynomial.coeff_add,
      digAt_add (bwN_dvd f i) (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) (hgd i hi)),
      digAt_of_dvd_succ (hgd i hi), add_zero]
  · rw [ini_coeff_gt (show bwN (f+g) < i by omega), ini_coeff_gt (show bwN f < i by omega)]

/-! ### §5 — the base stage `σ₀ : Stage 3 F9` (Φ = X, e = h = 1, K = FQ = the prime field) -/

private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The prime-field embedding `𝔽₃ → F9`. -/
private noncomputable def kap : ZMod 3 →+* F9 := ZMod.castHom dvd_rfl F9

/-- The base residue field: the prime subfield of `F9`, as a `Subfield`. -/
private noncomputable def Kb : Subfield F9 := kap.fieldRange

/-- The corestriction `𝔽₃ ≃ Kb` (as a ring hom; bijectivity below). -/
private noncomputable def rhoK : ZMod 3 →+* ↥Kb where
  toFun x := ⟨kap x, RingHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one kap)
  map_mul' x y := Subtype.ext (map_mul kap x y)
  map_zero' := Subtype.ext (map_zero kap)
  map_add' x y := Subtype.ext (map_add kap x y)

private lemma rhoK_inj : Function.Injective rhoK := fun a b h =>
  kap.injective (congrArg Subtype.val h)

private lemma rhoK_surj : Function.Surjective rhoK := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hy
  exact ⟨x, Subtype.ext hx⟩

private lemma rhoK_ne_zero {d : ZMod 3} (hd : d ≠ 0) : rhoK d ≠ 0 := fun h =>
  hd (rhoK_inj (by rw [h, map_zero]))

/-- The base residual `R(f) = toLaurent(ini f)` mapped into the prime subfield. -/
private noncomputable def bres (f : Polynomial ℤ_[3]) : LaurentPolynomial ↥Kb :=
  Polynomial.toLaurent ((ini f).map rhoK)

private lemma ini_zero : ini 0 = 0 := by
  rw [ini]; simp

private lemma bres_zero : bres 0 = 0 := by
  rw [bres, ini_zero]; simp

private lemma bres_ne_zero {f : Polynomial ℤ_[3]} (hf : f ≠ 0) : bres f ≠ 0 := by
  intro h
  have h1 : (ini f).map rhoK = 0 := Polynomial.toLaurent_injective (by rw [map_zero]; exact h)
  have h2 : ini f = 0 := by
    ext i
    have := congrArg (fun q => Polynomial.coeff q i) h1
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this ⊢
    exact rhoK_inj (by rw [this, map_zero])
  exact ini_ne_zero hf h2

private lemma bres_mul {f g : Polynomial ℤ_[3]} (hf : f ≠ 0) (hg : g ≠ 0) :
    bres (f * g) = bres f * bres g := by
  rw [bres, bres, bres, ini_mul hf hg, Polynomial.map_mul, map_mul]

/-- `bwN` of a nonzero constant is its valuation. -/
private lemma bwN_C {a : ℤ_[3]} (ha : a ≠ 0) : bwN (Polynomial.C a) = a.valuation := by
  have hne : Polynomial.C a ≠ (0 : Polynomial ℤ_[3]) := by
    rwa [ne_eq, Polynomial.C_eq_zero]
  obtain ⟨j, hj, hje⟩ := bwN_exists hne
  have hj0 : j = 0 := by
    by_contra h
    exact Polynomial.mem_support_iff.mp hj (by rw [Polynomial.coeff_C, if_neg h])
  subst hj0
  rw [Polynomial.coeff_C_zero] at hje
  omega

private lemma ini_C {a : ℤ_[3]} (ha : a ≠ 0) :
    ini (Polynomial.C a) = Polynomial.C (digAt a a.valuation) := by
  ext i
  by_cases hi : i = 0
  · subst hi
    rw [ini_coeff, if_pos ⟨Polynomial.mem_support_iff.mpr (by rwa [Polynomial.coeff_C_zero]), by
        simp [Polynomial.coeff_C_zero, bwN_C ha]⟩]
    simp only [Polynomial.coeff_C_zero]
  · have hns : ¬(i ∈ (Polynomial.C a).support ∧
        ((Polynomial.C a).coeff i).valuation + i = bwN (Polynomial.C a)) := by
      rintro ⟨hmem, -⟩
      refine hi ?_
      by_contra h
      exact Polynomial.mem_support_iff.mp hmem (by rw [Polynomial.coeff_C, if_neg h])
    rw [ini_coeff, if_neg hns, Polynomial.coeff_C, if_neg hi]

private lemma bwN_X : bwN (Polynomial.X : Polynomial ℤ_[3]) = 1 := by
  have hne : (Polynomial.X : Polynomial ℤ_[3]) ≠ 0 := Polynomial.X_ne_zero
  obtain ⟨j, hj, hje⟩ := bwN_exists hne
  have hj1 : j = 1 := by
    by_contra h
    exact Polynomial.mem_support_iff.mp hj (by
      rw [Polynomial.coeff_X, if_neg (fun he : 1 = j => h he.symm)])
  subst hj1
  rw [Polynomial.coeff_X_one, PadicInt.valuation_one] at hje
  omega

private lemma ini_X : ini (Polynomial.X : Polynomial ℤ_[3]) = Polynomial.X := by
  ext i
  by_cases hi : i = 1
  · subst hi
    rw [ini_coeff,
      if_pos ⟨Polynomial.mem_support_iff.mpr (by rw [Polynomial.coeff_X_one]; exact one_ne_zero),
        by rw [Polynomial.coeff_X_one, PadicInt.valuation_one, bwN_X]⟩]
    simp only [Polynomial.coeff_X_one, PadicInt.valuation_one]
    rw [digAt_spec (y := 1) (by ring), map_one]
  · have hns : ¬(i ∈ (Polynomial.X : Polynomial ℤ_[3]).support ∧
        (((Polynomial.X : Polynomial ℤ_[3])).coeff i).valuation + i
          = bwN (Polynomial.X : Polynomial ℤ_[3])) := by
      rintro ⟨hmem, -⟩
      refine hi ?_
      by_contra h
      exact Polynomial.mem_support_iff.mp hmem
        (by rw [Polynomial.coeff_X, if_neg (fun he : 1 = i => h he.symm)])
    rw [ini_coeff, if_neg hns, Polynomial.coeff_X, if_neg (fun he : 1 = i => hi he.symm)]

private lemma bres_X : bres (Polynomial.X : Polynomial ℤ_[3]) = LaurentPolynomial.T 1 := by
  rw [bres, ini_X, Polynomial.map_X, Polynomial.toLaurent_X]

private lemma val_three_pow (k : ℕ) : ((3:ℤ_[3])^k).valuation = k := by
  induction k with
  | zero => simpa using PadicInt.valuation_one
  | succ k ih =>
    rw [pow_succ, PadicInt.valuation_mul (three_pow_ne k) three_ne_zero', ih]
    have : ((3:ℕ):ℤ_[3]).valuation = 1 := PadicInt.valuation_p
    rw [show (3:ℤ_[3]) = ((3:ℕ):ℤ_[3]) by norm_num, this]

/-- Constants of every nonnegative weight with every prime-field digit are realized. -/
private lemma base_realizer (ν : ℤ) (hν : 0 ≤ ν) (c : (↥Kb)ˣ) :
    ∃ B : Polynomial ℤ_[3], B ≠ 0 ∧ inC Polynomial.X B ∧ (bwN B : ℤ) = ν ∧
      bres B = LaurentPolynomial.C (c : ↥Kb) * LaurentPolynomial.T 0 := by
  obtain ⟨d, hd⟩ := rhoK_surj (c : ↥Kb)
  have hdne : d ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hd, map_zero])
  set u : ℤ_[3] := ((d.val : ℕ) : ℤ_[3]) with hu
  have htz : PadicInt.toZMod u = d := by
    rw [hu, map_natCast, ZMod.natCast_val, ZMod.cast_id]
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at htz
    exact hdne htz.symm
  have hval0 : u.valuation = 0 := by
    by_contra hne
    have h1 : (3:ℤ_[3])^1 ∣ u := (pow_dvd_iff_le_val hune 1).mpr (by omega)
    obtain ⟨y, hy⟩ := h1
    rw [pow_one] at hy
    have : PadicInt.toZMod u = 0 := by
      rw [hy, map_mul, show PadicInt.toZMod (3:ℤ_[3]) = 0 by
        rw [show (3:ℤ_[3]) = ((3:ℕ):ℤ_[3]) by norm_num, map_natCast]; decide, zero_mul]
    exact hdne (htz.symm.trans this)
  set a : ℤ_[3] := u * (3:ℤ_[3])^(ν.toNat) with ha
  have hane : a ≠ 0 := mul_ne_zero hune (three_pow_ne _)
  have haval : a.valuation = ν.toNat := by
    rw [ha, PadicInt.valuation_mul hune (three_pow_ne _), hval0, val_three_pow, zero_add]
  refine ⟨Polynomial.C a, by rwa [ne_eq, Polynomial.C_eq_zero], ?_, ?_, ?_⟩
  · rw [inC, Polynomial.degree_C hane, Polynomial.degree_X]
    norm_num
  · rw [bwN_C hane, haval]
    omega
  · rw [bres, ini_C hane, Polynomial.map_C, Polynomial.toLaurent_C]
    have hdig : digAt a a.valuation = d := by
      rw [haval, ha, digAt_spec (y := u) (by ring), htz]
    rw [hdig, hd, LaurentPolynomial.T_zero, mul_one]

/-- Developments in the key `X` are literal coefficient lists. -/
private lemma dev_X_coeff {f : Polynomial ℤ_[3]} {B : ℕ → Polynomial ℤ_[3]} {Nd : ℕ}
    (hdev : IsDevelopment Polynomial.X f B Nd) :
    (∀ j, f.coeff j = (B j).coeff 0) ∧ (∀ j, Nd ≤ j → f.coeff j = 0) := by
  obtain ⟨hdeg, hbeyond, hsum⟩ := hdev
  have hBC : ∀ j, B j = Polynomial.C ((B j).coeff 0) := by
    intro j
    have : (B j).degree ≤ 0 := by
      have := hdeg j
      rw [Polynomial.degree_X] at this
      exact Order.le_of_lt_succ (by exact_mod_cast this)
    exact (Polynomial.eq_C_of_degree_le_zero this)
  have hcoeff : ∀ j, f.coeff j = if j < Nd then (B j).coeff 0 else 0 := by
    intro j
    rw [hsum, Polynomial.finset_sum_coeff]
    have hterm : ∀ k, (B k * Polynomial.X ^ k).coeff j
        = if k = j then (B k).coeff 0 else 0 := by
      intro k
      conv_lhs => rw [hBC k]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : k = j
      · simp [h]
      · rw [if_neg (fun he : j = k => h he.symm), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
  constructor
  · intro j
    rw [hcoeff j]
    by_cases hj : j < Nd
    · rw [if_pos hj]
    · rw [if_neg hj, hbeyond j (by omega), Polynomial.coeff_zero]
  · intro j hj
    rw [hcoeff j, if_neg (by omega)]

/-- K1 at the base key `X`. -/
private lemma base_K1 : K1At (fun f => (bwN f : ℤ)) Polynomial.X
    ((fun f => (bwN f : ℤ)) Polynomial.X) := by
  intro f B Nd hf hdev
  obtain ⟨hco, hbeyond⟩ := dev_X_coeff hdev
  have hBC : ∀ j, B j = Polynomial.C ((B j).coeff 0) := fun j =>
    Polynomial.eq_C_of_degree_le_zero (by
      have := hdev.1 j
      rw [Polynomial.degree_X] at this
      exact Order.le_of_lt_succ (by exact_mod_cast this))
  have hBw : ∀ j, f.coeff j ≠ 0 → bwN (B j) = (f.coeff j).valuation := by
    intro j hcj
    conv_lhs => rw [hBC j]
    rw [bwN_C (by rw [← hco j]; exact hcj), hco j]
  constructor
  · intro j hjN hBj
    have hcj : f.coeff j ≠ 0 := by
      rw [hco j]
      intro h0
      exact hBj ((hBC j).trans (by rw [h0, map_zero]))
    have hle := bwN_le (Polynomial.mem_support_iff.mpr hcj)
    show (bwN f : ℤ) ≤ (bwN (B j) : ℤ) + (j : ℤ) * ((bwN (Polynomial.X : Polynomial ℤ_[3]) : ℤ))
    rw [hBw j hcj, bwN_X]
    push_cast
    omega
  · obtain ⟨j₀, hj₀, hje⟩ := bwN_exists hf
    have hcj : f.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀
    have hjN : j₀ < Nd := by
      by_contra hge
      exact hcj (hbeyond j₀ (by omega))
    have hBne : B j₀ ≠ 0 := by
      intro h0
      rw [hco j₀, h0, Polynomial.coeff_zero] at hcj
      exact hcj rfl
    refine ⟨j₀, hjN, hBne, ?_⟩
    show (bwN f : ℤ) = (bwN (B j₀) : ℤ) + (j₀ : ℤ) * ((bwN (Polynomial.X : Polynomial ℤ_[3]) : ℤ))
    rw [hBw j₀ hcj, bwN_X]
    push_cast
    omega

/-- THE BASE STAGE `σ₀ : Stage 3 F9`: key `X`, index `(1,1)`, canonical Bézout `(1,0)`,
residue field the prime subfield, `w = bwN`, `R = bres`. -/
private noncomputable def sigma0 : Stage 3 F9 where
  e := 1
  h := 1
  s := 1
  t := 0
  he := le_rfl
  hh := le_rfl
  hcop := rfl
  hbez := by norm_num
  he1t := fun _ => rfl
  Φ := Polynomial.X
  hmonic := Polynomial.monic_X
  hdeg := by rw [Polynomial.natDegree_X]
  w := fun f => (bwN f : ℤ)
  wPrev := fun f => (bwN f : ℤ)
  K := Kb
  FQ := Kb
  hFQ_le := le_rfl
  R := bres
  hwmul := fun f g hf hg => by rw [bwN_mul hf hg]; push_cast; ring
  hwult := fun f g hf hg hfg => by
    have h1 := bwN_add_ge hfg (min (bwN f) (bwN g)) (min_le_left _ _) (min_le_right _ _)
    have : min ((bwN f : ℤ)) ((bwN g : ℤ)) = ((min (bwN f) (bwN g) : ℕ) : ℤ) := by
      push_cast; rfl
    rw [this]
    exact_mod_cast h1
  hvalgrp := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have h1 : (1:ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[3],
        f ≠ 0 ∧ g ≠ 0 ∧ (bwN f : ℤ) - (bwN g : ℤ) = n} := by
      refine ⟨Polynomial.C 3, 1, by
          rw [ne_eq, Polynomial.C_eq_zero]; exact three_ne_zero', one_ne_zero, ?_⟩
      rw [bwN_C three_ne_zero', show bwN (1 : Polynomial ℤ_[3]) = 0 by
          rw [show (1 : Polynomial ℤ_[3]) = Polynomial.C 1 from (map_one Polynomial.C).symm,
            bwN_C one_ne_zero, PadicInt.valuation_one],
        show (3:ℤ_[3]).valuation = 1 by
          rw [show (3:ℤ_[3]) = ((3:ℕ):ℤ_[3]) by norm_num]; exact PadicInt.valuation_p]
      norm_num
    have := AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure h1) x
    simpa using this
  hwΦ := by rw [bwN_X]
  hStretch := fun B _ _ => by push_cast; ring
  hR0 := bres_zero
  hRne := fun f hf => bres_ne_zero hf
  hRmul := fun f g hf hg => bres_mul hf hg
  hRadd := fun f g hf hg hfg hw hsum => by
    have hEq : bwN f = bwN g := by exact_mod_cast hw
    have hs : bwN (f + g) = bwN f := by exact_mod_cast hsum
    rw [bres, bres, bres, ini_add hfg hEq hs, Polynomial.map_add, map_add]
  hRlt := fun f g hf hg hfg hlt => by
    have hl : bwN f < bwN g := by exact_mod_cast hlt
    obtain ⟨-, -, hini⟩ := add_lt_pack hf hl
    rw [bres, bres, hini]
  hRΦ := bres_X
  hK1 := base_K1
  hS5 := fun B hB hBC => by
    obtain ⟨a, rfl⟩ : ∃ a, B = Polynomial.C a := by
      refine ⟨B.coeff 0, ?_⟩
      refine Polynomial.eq_C_of_degree_le_zero ?_
      have := hBC
      rw [inC, Polynomial.degree_X] at this
      exact Order.le_of_lt_succ (by exact_mod_cast this)
    have ha : a ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
    refine ⟨Units.mk0 (rhoK (digAt a a.valuation)) (rhoK_ne_zero (digAt_val_ne ha)), ?_⟩
    rw [bres, ini_C ha, Polynomial.map_C, Polynomial.toLaurent_C]
    simp
  reps := [Polynomial.C 3]
  hreps := by
    intro u hu
    rw [List.mem_singleton] at hu
    subst hu
    refine ⟨by rw [ne_eq, Polynomial.C_eq_zero]; exact three_ne_zero', ?_⟩
    rw [inC, Polynomial.degree_C three_ne_zero', Polynomial.degree_X]
    norm_num
  Tvec := [(Polynomial.C 3, 1)]
  hTvec := rfl
  weightSet := {n : ℤ | 0 ≤ n}
  hWS := fun B hB _ => by
    simp only [Set.mem_setOf_eq]
    positivity
  hS6a := fun ν hν c _ => by
    obtain ⟨B, hB1, hB2, hB3, hB4⟩ := base_realizer ν hν c
    refine ⟨B, hB1, hB2, hB3, ?_⟩
    rw [hB4, show (-0 : ℤ) * ν = 0 by ring]
  hS6b := fun ν a hν => by
    have hν' : ((bwN (Polynomial.X : Polynomial ℤ_[3]) : ℤ)) < ν := hν
    rw [bwN_X] at hν'
    obtain ⟨B, hB1, hB2, hB3, hB4⟩ := base_realizer ν (by omega) a
    refine ⟨B, hB1, hB2, hB3, ?_⟩
    rw [hB4, show (-0 : ℤ) * ν = 0 by ring]

/-! ### §6 — F9 facts, the two root nodes, the two histories -/

/-- `F9` has a square root of `−1` (a unit): the square of any generator of the order-8
cyclic group `F9ˣ`. -/
private lemma exists_sqrt_neg_one : ∃ z : F9ˣ, ((z : F9ˣ) : F9)^2 = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F9ˣ)
  have hcard : Nat.card F9ˣ = 8 := by
    have h9 : Nat.card F9 = 9 := by
      have := GaloisField.card 3 2 (by norm_num)
      exact this
    rw [Nat.card_units, h9]
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have h8 : g ^ 8 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one g
  have h4 : g ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  refine ⟨g ^ 2, ?_⟩
  have hsq : (((g ^ 4 : F9ˣ) : F9)) * (((g ^ 4 : F9ˣ) : F9)) = 1 := by
    rw [← Units.val_mul, ← pow_add]
    norm_num [h8]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd (Units.ext h) h4
  · rw [← h]
    push_cast
    ring

private noncomputable def sqrtm1 : F9ˣ := exists_sqrt_neg_one.choose

private lemma sqrtm1_sq : ((sqrtm1 : F9ˣ) : F9)^2 = -1 := exists_sqrt_neg_one.choose_spec

/-- The prime-field equiv `𝔽₃ ≃+* Kb`. -/
private noncomputable def rhoE : ZMod 3 ≃+* ↥Kb :=
  RingEquiv.ofBijective rhoK ⟨rhoK_inj, rhoK_surj⟩

/-- `z² + 1` is irreducible over `ZMod 3` (no roots; the two-coefficient criterion). -/
private lemma irr_zmod : Irreducible (Polynomial.X^2 + Polynomial.C 1 : Polynomial (ZMod 3)) := by
  by_contra h
  obtain ⟨c₁, c₂, h0, h1⟩ :=
    ((Polynomial.monic_X_pow_add_C _ two_ne_zero).not_irreducible_iff_exists_add_mul_eq_coeff
      Polynomial.natDegree_X_pow_add_C).mp h
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C] at h0 h1
  norm_num at h0 h1
  have : ∀ d₁ d₂ : ZMod 3, ¬((1:ZMod 3) = d₁ * d₂ ∧ (0:ZMod 3) = d₁ + d₂) := by decide
  exact this c₁ c₂ ⟨h0, h1⟩

/-- The inert descend polynomial `ψ = z² + 1` over the base residue field. -/
private noncomputable def psiIn : Polynomial ↥Kb := Polynomial.X^2 + Polynomial.C 1

private lemma psiIn_irr : Irreducible psiIn := by
  have hmap : (Polynomial.mapEquiv rhoE) (Polynomial.X^2 + Polynomial.C 1) = psiIn := by
    rw [Polynomial.mapEquiv_apply, psiIn, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_one]
  rw [← hmap]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv rhoE).toMulEquiv).mpr irr_zmod

private lemma psiIn_monic : psiIn.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero

private lemma psiIn_natDegree : psiIn.natDegree = 2 := by
  rw [psiIn]; exact Polynomial.natDegree_X_pow_add_C

private lemma psiIn_root : Polynomial.eval₂ Kb.subtype ((sqrtm1 : F9ˣ) : F9) psiIn = 0 := by
  rw [psiIn, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, map_one, sqrtm1_sq]
  ring

private lemma psiIn_ord : OrdPsiPoly psiIn psiIn 1 := by
  refine ⟨by simp, fun hdvd => ?_⟩
  have hne : psiIn ≠ 0 := psiIn_monic.ne_zero
  have hle : (psiIn ^ (1+1)).natDegree ≤ psiIn.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  rw [Polynomial.natDegree_pow, psiIn_natDegree] at hle
  omega

/-- The inert pattern digits `(1, 0, 1)` (the coefficients of `ψ = z² + 1`). -/
private noncomputable def patIn : ℕ → ↥Kb
  | 1 => 0
  | _ => 1

private lemma ranchIn_eq : psiIn
    = ∑ k ∈ Finset.range (2/1 + 1), Polynomial.C (patIn k) * Polynomial.X ^ k := by
  rw [show (2:ℕ)/1 = 2 by norm_num, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one,
    show patIn 0 = 1 from rfl, show patIn 1 = 0 from rfl, show patIn 2 = 1 from rfl, psiIn]
  simp only [map_zero, map_one, zero_mul, mul_zero, add_zero, pow_zero, one_mul]
  ring

/-- The split descend polynomial `ψ = z − 1`. -/
private noncomputable def psiSp : Polynomial ↥Kb := Polynomial.X - Polynomial.C 1

private lemma psiSp_monic : psiSp.Monic := Polynomial.monic_X_sub_C 1

private lemma psiSp_natDegree : psiSp.natDegree = 1 := by
  rw [psiSp]; exact Polynomial.natDegree_X_sub_C (x := (1 : ↥Kb))

private lemma psiSp_irr : Irreducible psiSp := by
  rw [psiSp]; exact Polynomial.irreducible_X_sub_C 1

private lemma psiSp_root : Polynomial.eval₂ Kb.subtype ((1 : F9ˣ) : F9) psiSp = 0 := by
  rw [psiSp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one,
    Units.val_one, sub_self]

private lemma psiSp_ord : OrdPsiPoly psiSp psiSp 1 := by
  refine ⟨by simp, fun hdvd => ?_⟩
  have hne : psiSp ≠ 0 := psiSp_monic.ne_zero
  have hle : (psiSp ^ (1+1)).natDegree ≤ psiSp.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  rw [Polynomial.natDegree_pow, psiSp_natDegree] at hle
  omega

/-- The split pattern digits `(−1, 1)`. -/
private noncomputable def patSp : ℕ → ↥Kb
  | 0 => -1
  | _ => 1

private lemma ranchSp_eq : psiSp
    = ∑ k ∈ Finset.range (1/1 + 1), Polynomial.C (patSp k) * Polynomial.X ^ k := by
  rw [show (1:ℕ)/1 = 1 by norm_num, Finset.sum_range_succ, Finset.sum_range_one,
    show patSp 0 = -1 from rfl, show patSp 1 = 1 from rfl, psiSp]
  simp only [map_neg, map_one, pow_zero, mul_one, one_mul]
  ring

/-- THE INERT ROOT NODE at level parameter `N`: side `(1, N)` over slots `[0, 2]`,
line `at b = (N+1) − N·b`, descend `(ψ, g, μ) = (z²+1, 2, 1)`. -/
private noncomputable def nodeIn (N : ℕ) (hN : 1 ≤ N) : Node 3 F9 where
  species := ReadSpecies.root
  σ := sigma0
  e := 1
  h := N
  s := 1
  t := 0
  g := 2
  μ := 1
  a := 0
  s0 := 0
  wSide := 2
  Dwidth := 1
  line := ⟨(N:ℚ)+1, (N:ℚ)⟩
  ustar := 1 - (N:ℚ)
  gam := (N:ℤ) + 1
  zbar := sqrtm1
  center := 1
  lift := 0
  ψ := psiIn
  pat := patIn
  Ranch := psiIn
  he := le_rfl
  hh := hN
  hcop := Nat.gcd_one_left N
  hbez := by push_cast; ring
  hbezCanon := ⟨le_rfl, by norm_num⟩
  hg := by norm_num
  hμ := le_rfl
  hEdvd := one_dvd 2
  hDwidth := Polynomial.natDegree_X.symm
  hψmonic := psiIn_monic
  hψdeg := psiIn_natDegree
  hψirr := psiIn_irr
  hRanch := ranchIn_eq
  hpat0 := by
    show (1 : ↥Kb) ≠ 0
    exact one_ne_zero
  hpatTop := by
    show patIn (2/1) ≠ 0
    rw [show (2:ℕ)/1 = 2 by norm_num, show patIn 2 = 1 from rfl]
    exact one_ne_zero
  hAnchor := by push_cast; ring
  hLineU := by
    show ((N:ℚ)+1) - (N:ℚ) * (((0 + 2) * 1 : ℕ) : ℚ) = 1 - (N:ℚ)
    push_cast
    ring
  hOrd := psiIn_ord
  hzbarRoot := psiIn_root
  hspecInc := fun h => nomatch h
  hspecRec := fun h => nomatch h
  hspecRecCenter := fun h => nomatch h

/-- THE SPLIT ROOT NODE at level parameter `N`: side `(1, 2N)` over slots `[0, 1]`,
line `at b = 1 − 2N·b`, descend `(ψ, g, μ) = (z − 1, 1, 1)`. -/
private noncomputable def nodeSp (N : ℕ) (hN : 1 ≤ N) : Node 3 F9 where
  species := ReadSpecies.root
  σ := sigma0
  e := 1
  h := 2 * N
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 1
  line := ⟨1, 2*(N:ℚ)⟩
  ustar := 1 - 2*(N:ℚ)
  gam := 1
  zbar := 1
  center := 1
  lift := 0
  ψ := psiSp
  pat := patSp
  Ranch := psiSp
  he := le_rfl
  hh := by omega
  hcop := Nat.gcd_one_left _
  hbez := by push_cast; ring
  hbezCanon := ⟨le_rfl, by norm_num⟩
  hg := le_rfl
  hμ := le_rfl
  hEdvd := one_dvd 1
  hDwidth := Polynomial.natDegree_X.symm
  hψmonic := psiSp_monic
  hψdeg := psiSp_natDegree
  hψirr := psiSp_irr
  hRanch := ranchSp_eq
  hpat0 := by
    show (-1 : ↥Kb) ≠ 0
    exact neg_ne_zero.mpr one_ne_zero
  hpatTop := by
    show patSp (1/1) ≠ 0
    rw [show (1:ℕ)/1 = 1 by norm_num, show patSp 1 = 1 from rfl]
    exact one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (1:ℚ) - 2*(N:ℚ) * (((0 + 1) * 1 : ℕ) : ℚ) = 1 - 2*(N:ℚ)
    push_cast
    ring
  hOrd := psiSp_ord
  hzbarRoot := psiSp_root
  hspecInc := fun h => nomatch h
  hspecRec := fun h => nomatch h
  hspecRecCenter := fun h => nomatch h

/-- The inert root history: the single read `nodeIn`. -/
private noncomputable def histIn (N : ℕ) (hN : 1 ≤ N) : History 3 F9 where
  nodes := [nodeIn N hN]
  nonempty := by simp
  root_iff := by
    intro j hj
    simp only [List.length_singleton] at hj
    interval_cases j
    exact iff_of_true rfl rfl

/-- The split root history: the single read `nodeSp`. -/
private noncomputable def histSp (N : ℕ) (hN : 1 ≤ N) : History 3 F9 where
  nodes := [nodeSp N hN]
  nonempty := by simp
  root_iff := by
    intro j hj
    simp only [List.length_singleton] at hj
    interval_cases j
    exact iff_of_true rfl rfl

/-! ### §7 — generic gate-JetSetup infrastructure: zero clauses, the zero system, the
deep-key block-locality (Θ = id is lawful because the landing-key constant sits at
valuation ≥ N — invisible in the box), boxChart injectivity. -/

/-- The literal-zero clause at coordinate `c` (support `{c}`, codim 1, `sat x ↔ x c = 0`). -/
private noncomputable def zeroClause {m : ℕ} (c : Fin m) : LevelClause 3 m where
  support := {c}
  codim := 1
  sat := fun x => x c = 0
  dep := fun x y h => by rw [h c (Finset.mem_singleton_self c)]
  count := by
    have h1 : Nat.card {y : Fin m → ZMod 3 // y c = 0 ∧ ∀ c' ∉ ({c} : Finset (Fin m)), y c' = 0}
        = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · refine ⟨fun a b => ?_⟩
        refine Subtype.ext (funext fun c' => ?_)
        by_cases hc' : c' = c
        · subst hc'; rw [a.prop.1, b.prop.1]
        · rw [a.prop.2 c' (by simp [hc']), b.prop.2 c' (by simp [hc'])]
      · exact ⟨⟨fun _ => 0, rfl, fun _ _ => rfl⟩⟩
    rw [h1, Finset.card_singleton]
    norm_num

/-- The all-zeros digit system pinned exactly on `D`. -/
private noncomputable def zeroSys {m : ℕ} (D : Finset (Fin m)) : Locus 3 m where
  pinned := fun c => decide (c ∈ D)
  solve := fun _ _ => 0

private lemma zeroSys_isSolution {m : ℕ} (D : Finset (Fin m)) (x : Fin m → ZMod 3) :
    (zeroSys D).IsSolution x ↔ ∀ c ∈ D, x c = 0 := by
  constructor
  · intro h c hc
    exact h c (by simp [zeroSys, hc])
  · intro h c hc
    have : c ∈ D := by simpa [zeroSys] using hc
    exact h c this

/-- The deep landing key `X^d + c`. -/
private noncomputable def gateKey (d : ℕ) (c : ℤ_[3]) : Polynomial ℤ_[3] :=
  Polynomial.X^d + Polynomial.C c

private lemma gateKey_natDegree (d : ℕ) (hd : 1 ≤ d) (c : ℤ_[3]) :
    (gateKey d c).natDegree = d := by
  rw [gateKey]; exact Polynomial.natDegree_X_pow_add_C

private lemma gateKey_degree (d : ℕ) (hd : 1 ≤ d) (c : ℤ_[3]) :
    (gateKey d c).degree = d := by
  rw [gateKey]
  exact Polynomial.degree_X_pow_add_C (by omega) c

/-- BLOCK-LOCALITY OF THE DEEP KEY: any `gateKey`-development determines every coefficient
of `f` modulo `3^M` from its own block slot alone (the key constant is `3^M`-divisible). -/
private lemma gateKey_block {d : ℕ} (hd : 1 ≤ d) {c : ℤ_[3]} {M : ℕ} (hc : (3:ℤ_[3])^M ∣ c)
    {f : Polynomial ℤ_[3]} {B : ℕ → Polynomial ℤ_[3]} {Nd : ℕ}
    (hdev : IsDevelopment (gateKey d c) f B Nd) (i : ℕ) :
    (3:ℤ_[3])^M ∣ f.coeff i - (B (i / d)).coeff (i % d) := by
  obtain ⟨hdeg, hbeyond, hsum⟩ := hdev
  have hdm := Nat.div_add_mod i d
  have hmlt : i % d < d := Nat.mod_lt i (by omega)
  have hqle : d * (i / d) ≤ i := by omega
  have hgcoeff : (∑ j ∈ Finset.range Nd, B j * Polynomial.X^(d*j)).coeff i
      = (B (i / d)).coeff (i % d) := by
    rw [Polynomial.finset_sum_coeff]
    have hterm : ∀ j, (B j * Polynomial.X^(d*j)).coeff i
        = if d*j ≤ i then (B j).coeff (i - d*j) else 0 := fun j =>
      Polynomial.coeff_mul_X_pow' (B j) (d*j) i
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    rw [Finset.sum_eq_single (i / d)]
    · rw [if_pos hqle]
      congr 1
      omega
    · intro j _ hj
      by_cases hin : d * j ≤ i
      · rw [if_pos hin]
        have hjle : j ≤ i / d :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hin)
        have hjlt : j < i / d := lt_of_le_of_ne hjle hj
        have hstep : d * (j + 1) ≤ d * (i / d) := Nat.mul_le_mul_left d hjlt
        rw [Nat.mul_succ] at hstep
        refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hdeg j) ?_)
        rw [gateKey_degree d hd c]
        exact_mod_cast (by omega : d ≤ i - d * j)
      · rw [if_neg hin]
    · intro hni
      rw [Finset.mem_range, not_lt] at hni
      rw [if_pos hqle, hbeyond _ (by omega), Polynomial.coeff_zero]
  have hdvd : Polynomial.C c ∣ f - ∑ j ∈ Finset.range Nd, B j * Polynomial.X^(d*j) := by
    conv_lhs => rw [show Polynomial.C c = gateKey d c - Polynomial.X^d by rw [gateKey]; ring]
    rw [hsum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    rw [← mul_sub]
    refine Dvd.dvd.mul_left ?_ (B j)
    rw [show Polynomial.X^(d*j) = (Polynomial.X^d)^j by rw [← pow_mul]]
    exact sub_dvd_pow_sub_pow _ _ j
  have hcd := (Polynomial.C_dvd_iff_dvd_coeff c (f - ∑ j ∈ Finset.range Nd,
    B j * Polynomial.X^(d*j))).mp hdvd i
  rw [Polynomial.coeff_sub, hgcoeff] at hcd
  exact dvd_trans hc hcd

/-- `baseDigit` congruence: digits below level `M` only see the class mod `3^M`. -/
private lemma baseDigit_congr {a a' : ℤ_[3]} {M ℓ : ℕ} (hℓ : ℓ < M)
    (h : (3:ℤ_[3])^M ∣ a - a') :
    baseDigit 3 ℓ a = baseDigit 3 ℓ a' := by
  have hmap : PadicInt.toZModPow (ℓ+1) a = PadicInt.toZModPow (ℓ+1) a' := by
    have hker : a - a' ∈ RingHom.ker (PadicInt.toZModPow (p := 3) (ℓ+1)) := by
      rw [PadicInt.ker_toZModPow]
      have h3 : (((3:ℕ)):ℤ_[3])^(ℓ+1) ∣ a - a' := by
        rw [show (((3:ℕ)):ℤ_[3]) = (3:ℤ_[3]) by norm_num]
        exact dvd_trans (pow_dvd_pow (3:ℤ_[3]) (show ℓ+1 ≤ M by omega)) h
      exact Ideal.mem_span_singleton.mpr h3
    rwa [RingHom.sub_mem_ker_iff] at hker
  rw [baseDigit, baseDigit, hmap]

/-- The box chart is injective. -/
private lemma boxChart_injective (n N : ℕ) : Function.Injective (boxChart n N) := by
  intro j j' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [boxChart] at h1 h2
  have hj := j.isLt
  have hj' := j'.isLt
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hj
    · exact h0
  have hb1 : (j : ℕ) % n < n := Nat.mod_lt (j : ℕ) hn
  have hb2 : (j' : ℕ) % n < n := Nat.mod_lt (j' : ℕ) hn
  have hm : (j : ℕ) % n = (j' : ℕ) % n := by omega
  have hd1 := Nat.div_add_mod (j : ℕ) n
  have hd2 := Nat.div_add_mod (j' : ℕ) n
  refine Fin.ext ?_
  have h3 : n * ((j : ℕ) / n) = n * ((j' : ℕ) / n) := by rw [h1]
  omega

/-- The gate fresh data: one literal-zero clause per coordinate of `D`. -/
private noncomputable def gateFresh (m : ℕ) (D : Finset (Fin m)) : FreshData 3 m :=
  ⟨D.toList.map zeroClause, by
    rw [List.pairwise_map]
    refine (Finset.nodup_toList D).imp ?_
    intro a b hab
    show Disjoint ({a} : Finset (Fin m)) ({b} : Finset (Fin m))
    exact Finset.disjoint_singleton.mpr hab⟩

private noncomputable def gateFreshFn (m : ℕ) (D : Finset (Fin m)) : ℕ → FreshData 3 m :=
  fun i => if i = 0 then gateFresh m D else ⟨[], List.Pairwise.nil⟩

private lemma gateFresh_sat_iff (m : ℕ) (D : Finset (Fin m)) (x : Fin m → ZMod 3) :
    (gateFresh m D).sat x ↔ ∀ c ∈ D, x c = 0 := by
  constructor
  · intro h c hc
    exact h (zeroClause c) (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩)
  · intro h cl hcl
    obtain ⟨c, hcD, rfl⟩ := List.mem_map.mp hcl
    exact h c (Finset.mem_toList.mp hcD)

/-- THE SHARED GATE `JetSetup` BUILDER: a length-1 root history over the deep landing key
`X^d + ck` (`3^N ∣ ck`, so the key constant is invisible in the box and `Θ = id` with the
literal frame-0 digit chart at EVERY frame is lawful), fresh data = one zero clause per
band coordinate of `D`, state chain `topLocus → zeroSys D`. -/
private noncomputable def gateSetup
    (N : ℕ) (hN : 1 ≤ N)
    (H : History 3 F9) (hlen : H.nodes.length = 1)
    (hcoh : HistoryCoherent H)
    (hrh : ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth → 1 ≤ (H.nodes[0]'hj).line.at b)
    (d : ℕ) (hd : 1 ≤ d) (ck : ℤ_[3]) (hck : (3:ℤ_[3])^N ∣ ck)
    (hland : ∀ hj : 0 < H.nodes.length, LandingKey (H.nodes[0]'hj) (gateKey d ck))
    (D : Finset (Fin (2*N)))
    (hband : ∀ (hj : 0 < H.nodes.length) (c : Fin (2*N)),
      inFreshBand H 2 (boxChart 2 N) 0 (H.nodes[0]'hj) c ↔ c ∈ D)
    (hvalsupp : ∀ (hj : 0 < H.nodes.length) (c : Fin (2*N)),
      IsValueCoord H (boxChart 2 N) 0 (H.nodes[0]'hj) c →
      IsValueSupport H (boxChart 2 N) 0 (H.nodes[0]'hj) ({c} : Finset (Fin (2*N))))
    (hzc : ∀ (hj : 0 < H.nodes.length) (j : Fin (2*N)),
      (boxChart 2 N j).2 < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth →
      ((j ∈ D) ↔ ((H.htH 1 (boxChart 2 N j) : ℚ) : WithBot ℚ)
        ≤ H.floorH 1 (boxChart 2 N j).2)) :
    JetSetup H 2 N (2*N) where
  hm := rfl
  hN := hN
  coordOf := boxChart 2 N
  coordOf_sorted := boxChart_sorted 2 N
  coordOf_lt := boxChart_lt 2 N
  coherent := hcoh
  realizable := fun i hi => absurd (hlen ▸ hi) (by omega)
  root_height := hrh
  Sigma := fun k => if k = 0 then topLocus 3 (2*N) else zeroSys D
  init := fun c => rfl
  fresh := gateFreshFn (2*N) D
  Theta := fun _ => id
  Theta_uni := fun _ i => ⟨fun _ => 0, fun x => (add_zero _).symm⟩
  keys := fun _ => gateKey d ck
  keys_mid := fun i hi => absurd (hlen ▸ hi) (by omega)
  landing := by
    intro i hi
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    exact hland _
  pres := fun _ x f => ∀ j : Fin (2*N),
    x j = baseDigit 3 (boxChart 2 N j).1 (f.coeff (boxChart 2 N j).2)
  pres_zero := fun x f => Iff.rfl
  pres_total := fun i _ f _ _ =>
    ⟨fun j => baseDigit 3 (boxChart 2 N j).1 (f.coeff (boxChart 2 N j).2), fun j => rfl⟩
  pres_theta := fun i _ x f h => h
  pres_block := by
    intro i hi f f' x x' hx hx' B B' Nd Nd' hB hB' c hc
    rw [hx c, hx' c]
    have hdeg : (gateKey d ck).natDegree = d := gateKey_natDegree d hd ck
    rw [hdeg] at hc
    have h1 := gateKey_block hd hck hB (boxChart 2 N c).2
    have h2 := gateKey_block hd hck hB' (boxChart 2 N c).2
    refine baseDigit_congr (boxChart_lt 2 N c).1 ?_
    have h3 := dvd_sub h1 h2
    rw [hc] at h3
    have h4 : f.coeff (boxChart 2 N c).2 - (B' ((boxChart 2 N c).2 / d)).coeff ((boxChart 2 N c).2 % d)
        - (f'.coeff (boxChart 2 N c).2 - (B' ((boxChart 2 N c).2 / d)).coeff ((boxChart 2 N c).2 % d))
        = f.coeff (boxChart 2 N c).2 - f'.coeff (boxChart 2 N c).2 := by ring
    rwa [h4] at h3
  stratum := fun i y => (gateFreshFn (2*N) D i).sat y
  recursion := by
    intro i hi x
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    show (zeroSys D).IsSolution x ↔ (topLocus 3 (2*N)).IsSolution x ∧ (gateFresh (2*N) D).sat x
    rw [zeroSys_isSolution, gateFresh_sat_iff]
    constructor
    · intro h
      exact ⟨fun c hc => by simp [topLocus] at hc, h⟩
    · rintro ⟨-, h⟩
      exact h
  inh_implied := fun i _ y _ => Iff.rfl
  zc := by
    intro i hi
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    refine ⟨?_, ?_⟩
    · intro j hj
      show (decide (j ∈ D) = true) ↔ _
      rw [decide_eq_true_eq]
      exact hzc hi j hj
    · intro j _ _ f
      rfl
  fresh_band := by
    intro i hi cl hcl c hc
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    have hcl' : ∃ a ∈ D, zeroClause a = cl := by simpa [gateFreshFn, gateFresh] using hcl
    obtain ⟨c₀, hc₀D, rfl⟩ := hcl'
    have hcc : c = c₀ := Finset.mem_singleton.mp hc
    subst hcc
    exact (hband hi c).mpr hc₀D
  fresh_cover := by
    intro i hi c hcband
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    refine ⟨zeroClause c, ?_, Finset.mem_singleton_self c⟩
    show zeroClause c ∈ (gateFreshFn (2*N) D 0).clauses
    simp only [gateFreshFn, if_pos rfl, gateFresh]
    exact List.mem_map.mpr ⟨c, Finset.mem_toList.mpr ((hband hi c).mp hcband), rfl⟩
  fresh_assembled := by
    intro i hi cl hcl
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    have hcl' : ∃ a ∈ D, zeroClause a = cl := by simpa [gateFreshFn, gateFresh] using hcl
    obtain ⟨c₀, hc₀D, rfl⟩ := hcl'
    by_cases hval : IsValueCoord H (boxChart 2 N) 0 (H.nodes[0]'hi) c₀
    · right
      refine ⟨hvalsupp hi c₀ hval, ?_, ?_⟩
      · show (1 : ℕ) = ({c₀} : Finset (Fin (2*N))).card
        rw [Finset.card_singleton]
      · show ∃ (T : TypObject 3 (2*N) ({c₀} : Finset (Fin (2*N))) (Fin 1 → ZMod 3))
            (v : Fin 1 → ZMod 3), ∀ x, ((zeroClause c₀).sat x ↔ T.φ x = v)
        refine ⟨⟨AddMonoidHom.mk' (fun x => fun _ => x c₀) (fun a b => rfl),
          fun x y h => funext fun _ => h c₀ (Finset.mem_singleton_self c₀),
          fun t => ⟨fun _ => t 0, funext fun i => congrArg t (Subsingleton.elim 0 i)⟩⟩,
          0, fun x => ?_⟩
        show x c₀ = 0 ↔ _
        constructor
        · intro h
          exact funext fun _ => h
        · intro h
          exact congrFun h 0
    · left
      exact ⟨c₀, rfl, rfl, fun x => Iff.rfl, hval⟩
  mstar_eq := by
    intro i hi
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    have hL : (gateFreshFn (2*N) D 0).mstar = D.card := by
      show (gateFresh (2*N) D).mstar = D.card
      rw [FreshData.mstar]
      have hrep : ((gateFresh (2*N) D).clauses.map LevelClause.codim)
          = List.replicate D.toList.length 1 := by
        rw [List.eq_replicate_iff]
        constructor
        · simp [gateFresh]
        · intro b hb
          rw [gateFresh, List.map_map] at hb
          obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
          rfl
      rw [hrep, List.sum_replicate, smul_eq_mul, mul_one, Finset.length_toList]
    have hR : Nat.card {c : Fin (2*N) //
        inFreshBand H 2 (boxChart 2 N) 0 (H.nodes[0]'hi) c} = D.card := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun c => hband hi c))]
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hL, hR]

/-- The SHZ locus of a gate setup is the zero cylinder on `D`. -/
private lemma gateSetup_SHZ (N : ℕ) (hN : 1 ≤ N) (H : History 3 F9) (hlen : H.nodes.length = 1)
    (hcoh) (hrh) (d : ℕ) (hd : 1 ≤ d) (ck : ℤ_[3]) (hck) (hland) (D : Finset (Fin (2*N)))
    (hband) (hvalsupp) (hzc) :
    (gateSetup N hN H hlen hcoh hrh d hd ck hck hland D hband hvalsupp hzc).SHZ
        (topLocus 3 (2*N))
      = {x : Fin (2*N) → ZMod 3 | ∀ c ∈ D, x c = 0} := by
  ext x
  simp only [JetSetup.SHZ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy0, hchain, hsat, -⟩
    intro c hc
    have h1 := hsat 0 (by omega)
    rw [show y 0 = x from hy0] at h1
    exact (gateFresh_sat_iff (2*N) D x).mp h1 c hc
  · intro h
    refine ⟨fun _ => x, rfl, fun i _ => rfl, fun i hi => ?_, fun c hc => by simp [topLocus] at hc⟩
    have hi0 : i = 0 := by have h' := hlen ▸ hi; omega
    subst hi0
    exact (gateFresh_sat_iff (2*N) D x).mpr h

/-! ### §8 — the two gate instantiations and the separation endgame -/

private lemma val_neg {x : ℤ_[3]} (hx : x ≠ 0) : (-x).valuation = x.valuation := by
  have hm1 : ((-1 : ℤ_[3])).valuation = 0 := by
    have h2 : ((-1 : ℤ_[3]) * (-1)).valuation = (-1:ℤ_[3]).valuation + (-1:ℤ_[3]).valuation :=
      PadicInt.valuation_mul (by norm_num) (by norm_num)
    rw [show ((-1:ℤ_[3]) * (-1)) = 1 by ring, PadicInt.valuation_one] at h2
    omega
  rw [show -x = (-1) * x by ring, PadicInt.valuation_mul (by norm_num) hx, hm1, zero_add]

private lemma bres_deep (M : ℕ) :
    bres (Polynomial.C ((3:ℤ_[3])^M)) = LaurentPolynomial.C (1 : ↥Kb) := by
  rw [bres, ini_C (three_pow_ne M), Polynomial.map_C, Polynomial.toLaurent_C, val_three_pow]
  congr 1
  rw [digAt_spec (y := 1) (by ring), map_one, map_one]

private lemma bres_deep_neg (M : ℕ) :
    bres (Polynomial.C (-(3:ℤ_[3])^M)) = LaurentPolynomial.C (-1 : ↥Kb) := by
  have hne : -(3:ℤ_[3])^M ≠ 0 := neg_ne_zero.mpr (three_pow_ne M)
  rw [bres, ini_C hne, Polynomial.map_C, Polynomial.toLaurent_C,
    val_neg (three_pow_ne M), val_three_pow]
  congr 1
  rw [digAt_spec (y := -1) (by ring), map_neg, map_one, map_neg, map_one]

private lemma psiIn_coeff0 : psiIn.coeff 0 = 1 := by
  rw [psiIn]
  simp [Polynomial.coeff_X_pow]

private lemma psiIn_coeff1 : psiIn.coeff 1 = 0 := by
  rw [psiIn]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one]

private lemma psiSp_coeff0 : psiSp.coeff 0 = -1 := by
  rw [psiSp]
  simp

/-- Generic singleton value-support law for `Dwidth = 1` root reads at frame 0. -/
private lemma gate_hvalsupp (N : ℕ) (H : History 3 F9)
    (hDw : ∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).Dwidth = 1) :
    ∀ (hj : 0 < H.nodes.length) (c : Fin (2*N)),
      IsValueCoord H (boxChart 2 N) 0 (H.nodes[0]'hj) c →
      IsValueSupport H (boxChart 2 N) 0 (H.nodes[0]'hj) ({c} : Finset (Fin (2*N))) := by
  intro hj c hval
  obtain ⟨hspan, hht⟩ := hval
  have hht0 : ∀ x : Coord, H.htH 0 x = (x.1 : ℚ) := by
    intro x
    rw [History.htH]
    simp
  have hfs1 : ∀ b : ℕ, (H.nodes[0]'hj).fineSlot b = b := by
    intro b
    rw [Node.fineSlot, hDw hj, Nat.div_one]
  refine ⟨(H.nodes[0]'hj).fineSlot (boxChart 2 N c).2, hspan, fun c' => ?_⟩
  constructor
  · intro hc'
    rw [Finset.mem_singleton] at hc'
    subst hc'
    exact ⟨rfl, hht⟩
  · rintro ⟨hfs, hht'⟩
    rw [Finset.mem_singleton]
    have hfs' : (boxChart 2 N c').2 = (boxChart 2 N c).2 := by
      rw [hfs1] at hfs
      rw [hfs, hfs1]
    have hhteq : H.htH 0 (boxChart 2 N c') = H.htH 0 (boxChart 2 N c) := by
      rw [hht', hht]
    rw [hht0, hht0] at hhteq
    have h1 : (boxChart 2 N c').1 = (boxChart 2 N c).1 := by exact_mod_cast hhteq
    exact boxChart_injective 2 N (Prod.ext h1 hfs')

private lemma htH0_eq (H : History 3 F9) (x : Coord) : H.htH 0 x = (x.1 : ℚ) := by
  rw [History.htH]
  simp

/-- The inert band: base 0 fully, base 1 up to level 1. -/
private def Din (N : ℕ) : Finset (Fin (2*N)) :=
  Finset.univ.filter (fun c => (boxChart 2 N c).2 = 0 ∨ (boxChart 2 N c).1 ≤ 1)

/-- The split band: base 0 up to level 1. -/
private def Dsp (N : ℕ) : Finset (Fin (2*N)) :=
  Finset.univ.filter (fun c => (boxChart 2 N c).2 = 0 ∧ (boxChart 2 N c).1 ≤ 1)

/-! #### Inert-side computations -/

private lemma histIn_coh (N : ℕ) (hN : 1 ≤ N) : HistoryCoherent (histIn N hN) := by
  refine ⟨fun _ => Polynomial.natDegree_X, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by have h' : i < 1 := hi; omega
    subst hi0
    show (N:ℚ) * (((1:ℕ):ℚ) * (((histIn N hN).strFrame 0 : ℕ):ℚ) * ((1:ℕ):ℚ)) = ((N:ℕ):ℚ)
    rw [show (histIn N hN).strFrame 0 = 1 from rfl]
    push_cast
    ring
  · intro i hi
    have hi0 : i = 0 := by have h' : i < 1 := hi; omega
    subst hi0
    show ((((N:ℤ) + 1) : ℤ) : ℚ)
      = ((1:ℕ):ℚ) * ((((histIn N hN).strFrame 0 : ℕ):ℚ) * (1 - (N:ℚ)))
        + (((0 + 2 : ℕ)):ℚ) * ((N:ℕ):ℚ)
    rw [show (histIn N hN).strFrame 0 = 1 from rfl]
    push_cast
    ring
  · intro i hi
    exact absurd (show i + 1 < 1 from hi) (by omega)

private lemma histIn_rh (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histIn N hN).nodes.length) (b : ℕ),
      b < ((histIn N hN).nodes[0]'hj).μ * ((histIn N hN).nodes[0]'hj).childWidth →
      1 ≤ ((histIn N hN).nodes[0]'hj).line.at b := by
  intro hj b hb
  have hb2 : b < 2 := hb
  show (1:ℚ) ≤ ((N:ℚ) + 1) - (N:ℚ) * (b:ℚ)
  have hN0 : (0:ℚ) ≤ (N:ℚ) := Nat.cast_nonneg N
  interval_cases b
  · norm_num
  · norm_num

private lemma histIn_R_clause (N : ℕ) :
    bres (Polynomial.C ((3:ℤ_[3])^(2*N)))
      = LaurentPolynomial.C (psiIn.coeff 0)
        * LaurentPolynomial.T (-(0:ℤ) * ((bwN (Polynomial.C ((3:ℤ_[3])^(2*N))) : ℕ) : ℤ)) := by
  rw [show (-(0:ℤ) * ((bwN (Polynomial.C ((3:ℤ_[3])^(2*N))) : ℕ) : ℤ)) = (0:ℤ) by ring,
    bres_deep, psiIn_coeff0, LaurentPolynomial.T_zero, mul_one]

private lemma histIn_land (N : ℕ) (hN : 1 ≤ N) :
    LandingKey (nodeIn N hN) (gateKey 2 ((3:ℤ_[3])^(2*N))) := by
  constructor
  · intro h
    exact nomatch h
  · intro _
    refine ⟨fun k => if k = 0 then Polynomial.C ((3:ℤ_[3])^(2*N)) else 0, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        exact absurd (show psiIn.coeff 0 = 0 from hk)
          (by rw [psiIn_coeff0]; exact one_ne_zero)
      · simp only [if_neg hk0]
    · intro k hk hkne
      have hk2 : k < 2 := hk
      have hk0 : k = 0 := by
        by_contra h
        have hk1 : k = 1 := by omega
        subst hk1
        exact hkne (show psiIn.coeff 1 = 0 from psiIn_coeff1)
      subst hk0
      simp only [reduceIte]
      refine ⟨by rw [ne_eq, Polynomial.C_eq_zero]; exact three_pow_ne _, ?_, ?_, ?_⟩
      · show inC Polynomial.X (Polynomial.C ((3:ℤ_[3])^(2*N)))
        rw [inC, Polynomial.degree_C (three_pow_ne _), Polynomial.degree_X]
        norm_num
      · show ((bwN (Polynomial.C ((3:ℤ_[3])^(2*N))) : ℕ) : ℤ) = ((N:ℕ):ℤ) * (((2:ℕ):ℤ) - ((0:ℕ):ℤ))
        rw [bwN_C (three_pow_ne _), val_three_pow]
        push_cast
        ring
      · exact histIn_R_clause N
    · show gateKey 2 ((3:ℤ_[3])^(2*N)) = Polynomial.X ^ (1*2)
        + ∑ k ∈ Finset.range 2,
          (if k = 0 then Polynomial.C ((3:ℤ_[3])^(2*N)) else 0) * Polynomial.X ^ (1*k)
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [reduceIte, one_ne_zero]
      rw [gateKey]
      ring

private lemma histIn_band (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histIn N hN).nodes.length) (c : Fin (2*N)),
      inFreshBand (histIn N hN) 2 (boxChart 2 N) 0 ((histIn N hN).nodes[0]'hj) c ↔
        c ∈ Din N := by
  intro hj c
  obtain ⟨hℓ, hb⟩ := boxChart_lt 2 N c
  rw [inFreshBand, Din, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have h1 : (boxChart 2 N c).2 < (histIn N hN).prevRim 2 0 := hb
  have h2 : (histIn N hN).floorH 0 (boxChart 2 N c).2
      < (((histIn N hN).htH 0 (boxChart 2 N c) : ℚ) : WithBot ℚ) := by
    show (⊥ : WithBot ℚ) < _
    exact WithBot.bot_lt_coe _
  have h3 : ((histIn N hN).nodes[0]'hj).slotVal
      (((histIn N hN).nodes[0]'hj).fineSlot (boxChart 2 N c).2)
      = ((N:ℚ) + 1) - (N:ℚ) * ((boxChart 2 N c).2 : ℚ) := by
    show (nodeIn N hN).slotVal ((nodeIn N hN).fineSlot (boxChart 2 N c).2) = _
    rw [Node.slotVal, Node.fineSlot, show ((nodeIn N hN).Dwidth) = 1 from rfl,
      Nat.div_one, Nat.mul_one, Line.at]
    rfl
  constructor
  · rintro ⟨-, -, hband⟩
    rw [htH0_eq, h3] at hband
    by_cases hb0 : (boxChart 2 N c).2 = 0
    · exact Or.inl hb0
    · have hb1 : (boxChart 2 N c).2 = 1 := by omega
      rw [hb1] at hband
      refine Or.inr ?_
      have : ((boxChart 2 N c).1 : ℚ) ≤ 1 := by push_cast at hband ⊢; linarith
      exact_mod_cast this
  · intro h
    refine ⟨h1, h2, ?_⟩
    rw [htH0_eq, h3]
    rcases h with hb0 | hℓ1
    · rw [hb0]
      push_cast
      have : ((boxChart 2 N c).1 : ℚ) < (N:ℚ) := by exact_mod_cast hℓ
      linarith
    · have h4 : ((boxChart 2 N c).1 : ℚ) ≤ 1 := by exact_mod_cast hℓ1
      have h5 : ((boxChart 2 N c).2 : ℚ) ≤ 1 := by
        have : (boxChart 2 N c).2 ≤ 1 := by omega
        exact_mod_cast this
      have hN0 : (1:ℚ) ≤ (N:ℚ) := by exact_mod_cast hN
      nlinarith

private lemma histIn_zc (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histIn N hN).nodes.length) (j : Fin (2*N)),
      (boxChart 2 N j).2 < ((histIn N hN).nodes[0]'hj).μ * ((histIn N hN).nodes[0]'hj).childWidth →
      ((j ∈ Din N) ↔ (((histIn N hN).htH 1 (boxChart 2 N j) : ℚ) : WithBot ℚ)
        ≤ (histIn N hN).floorH 1 (boxChart 2 N j).2) := by
  intro hj j _
  obtain ⟨hℓ, hb⟩ := boxChart_lt 2 N j
  have hht : (histIn N hN).htH 1 (boxChart 2 N j)
      = ((boxChart 2 N j).1 : ℚ) + (((boxChart 2 N j).2 % 2 : ℕ) : ℚ) * (N:ℚ) := by
    rw [History.htH, Finset.sum_range_one]
    congr 1
    show ((((histIn N hN).innerslotH 0 (boxChart 2 N j).2 : ℕ)) : ℚ)
        * (histIn N hN).kappaH 0 = _
    rw [show (histIn N hN).innerslotH 0 (boxChart 2 N j).2 = (boxChart 2 N j).2 % 2 by
        show ((boxChart 2 N j).2 % (nodeIn N hN).childWidth) / (nodeIn N hN).Dwidth = _
        rw [show (nodeIn N hN).childWidth = 2 from rfl, show (nodeIn N hN).Dwidth = 1 from rfl,
          Nat.div_one],
      show (histIn N hN).kappaH 0 = (N:ℚ) by
        show ((N:ℕ):ℚ) / (((1:ℕ):ℚ) * (((histIn N hN).strFrame 0 : ℕ):ℚ)) = (N:ℚ)
        rw [show (histIn N hN).strFrame 0 = 1 from rfl]
        norm_num]
  have hfloor : (histIn N hN).floorH 1 (boxChart 2 N j).2 = (((N:ℚ) + 1 : ℚ) : WithBot ℚ) := by
    rw [History.floorH]
    show (List.map (fun ν => ν.staircase (boxChart 2 N j).2)
        (List.take 1 [nodeIn N hN])).foldr max ⊥ = _
    rw [show List.take 1 [nodeIn N hN] = [nodeIn N hN] from rfl, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Node.staircase,
      if_pos (show (boxChart 2 N j).2 < (nodeIn N hN).μ * (nodeIn N hN).childWidth from hb),
      show ((boxChart 2 N j).2 / (nodeIn N hN).childWidth) * (nodeIn N hN).childWidth = 0 by
        show ((boxChart 2 N j).2 / 2) * 2 = 0
        omega]
    rw [max_eq_left bot_le]
    show (((((N:ℚ) + 1) - (N:ℚ) * ((0:ℕ):ℚ)) : ℚ) : WithBot ℚ) = _
    norm_num
  rw [hht, hfloor, Din, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, WithBot.coe_le_coe]
  by_cases hb0 : (boxChart 2 N j).2 = 0
  · constructor
    · intro _
      rw [hb0]
      simp only [Nat.zero_mod, Nat.cast_zero, zero_mul, add_zero]
      have : ((boxChart 2 N j).1 : ℚ) < (N:ℚ) := by exact_mod_cast hℓ
      linarith
    · intro _
      exact Or.inl hb0
  · have hb1 : (boxChart 2 N j).2 = 1 := by omega
    constructor
    · rintro (h | h)
      · exact absurd h hb0
      · rw [hb1]
        have h' : ((boxChart 2 N j).1 : ℚ) ≤ 1 := by exact_mod_cast h
        norm_num
        linarith
    · intro h
      rw [hb1] at h
      norm_num at h
      refine Or.inr ?_
      have h' : ((boxChart 2 N j).1 : ℚ) ≤ 1 := by linarith
      exact_mod_cast h'

/-! #### Split-side computations -/

private lemma histSp_coh (N : ℕ) (hN : 1 ≤ N) : HistoryCoherent (histSp N hN) := by
  refine ⟨fun _ => Polynomial.natDegree_X, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by have h' : i < 1 := hi; omega
    subst hi0
    show (2*(N:ℚ)) * (((1:ℕ):ℚ) * (((histSp N hN).strFrame 0 : ℕ):ℚ) * ((1:ℕ):ℚ))
      = ((2*N:ℕ):ℚ)
    rw [show (histSp N hN).strFrame 0 = 1 from rfl]
    push_cast
    ring
  · intro i hi
    have hi0 : i = 0 := by have h' : i < 1 := hi; omega
    subst hi0
    show (((1:ℤ)) : ℚ)
      = ((1:ℕ):ℚ) * ((((histSp N hN).strFrame 0 : ℕ):ℚ) * (1 - 2*(N:ℚ)))
        + (((0 + 1 : ℕ)):ℚ) * ((2*N:ℕ):ℚ)
    rw [show (histSp N hN).strFrame 0 = 1 from rfl]
    push_cast
    ring
  · intro i hi
    exact absurd (show i + 1 < 1 from hi) (by omega)

private lemma histSp_rh (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histSp N hN).nodes.length) (b : ℕ),
      b < ((histSp N hN).nodes[0]'hj).μ * ((histSp N hN).nodes[0]'hj).childWidth →
      1 ≤ ((histSp N hN).nodes[0]'hj).line.at b := by
  intro hj b hb
  have hb1 : b < 1 := hb
  interval_cases b
  show (1:ℚ) ≤ 1 - 2*(N:ℚ) * ((0:ℕ):ℚ)
  norm_num

private lemma histSp_R_clause (N : ℕ) :
    bres (Polynomial.C (-(3:ℤ_[3])^(2*N)))
      = LaurentPolynomial.C (psiSp.coeff 0)
        * LaurentPolynomial.T (-(0:ℤ) * ((bwN (Polynomial.C (-(3:ℤ_[3])^(2*N))) : ℕ) : ℤ)) := by
  rw [show (-(0:ℤ) * ((bwN (Polynomial.C (-(3:ℤ_[3])^(2*N))) : ℕ) : ℤ)) = (0:ℤ) by ring,
    bres_deep_neg, psiSp_coeff0, LaurentPolynomial.T_zero, mul_one]

private lemma histSp_land (N : ℕ) (hN : 1 ≤ N) :
    LandingKey (nodeSp N hN) (gateKey 1 (-(3:ℤ_[3])^(2*N))) := by
  constructor
  · intro h
    exact nomatch h
  · intro _
    refine ⟨fun k => if k = 0 then Polynomial.C (-(3:ℤ_[3])^(2*N)) else 0, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        exact absurd (show psiSp.coeff 0 = 0 from hk)
          (by rw [psiSp_coeff0]; exact neg_ne_zero.mpr one_ne_zero)
      · simp only [if_neg hk0]
    · intro k hk hkne
      have hk1 : k < 1 := hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [reduceIte]
      have hcne : -(3:ℤ_[3])^(2*N) ≠ 0 := neg_ne_zero.mpr (three_pow_ne _)
      refine ⟨by rw [ne_eq, Polynomial.C_eq_zero]; exact hcne, ?_, ?_, ?_⟩
      · show inC Polynomial.X (Polynomial.C (-(3:ℤ_[3])^(2*N)))
        rw [inC, Polynomial.degree_C hcne, Polynomial.degree_X]
        norm_num
      · show ((bwN (Polynomial.C (-(3:ℤ_[3])^(2*N))) : ℕ) : ℤ)
          = ((2*N:ℕ):ℤ) * (((1:ℕ):ℤ) - ((0:ℕ):ℤ))
        rw [bwN_C hcne, val_neg (three_pow_ne _), val_three_pow]
        push_cast
        ring
      · exact histSp_R_clause N
    · show gateKey 1 (-(3:ℤ_[3])^(2*N)) = Polynomial.X ^ (1*1)
        + ∑ k ∈ Finset.range 1,
          (if k = 0 then Polynomial.C (-(3:ℤ_[3])^(2*N)) else 0) * Polynomial.X ^ (1*k)
      rw [Finset.sum_range_one]
      simp only [reduceIte]
      rw [gateKey]
      ring

private lemma histSp_band (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histSp N hN).nodes.length) (c : Fin (2*N)),
      inFreshBand (histSp N hN) 2 (boxChart 2 N) 0 ((histSp N hN).nodes[0]'hj) c ↔
        c ∈ Dsp N := by
  intro hj c
  obtain ⟨hℓ, hb⟩ := boxChart_lt 2 N c
  rw [inFreshBand, Dsp, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have h1 : (boxChart 2 N c).2 < (histSp N hN).prevRim 2 0 := hb
  have h2 : (histSp N hN).floorH 0 (boxChart 2 N c).2
      < (((histSp N hN).htH 0 (boxChart 2 N c) : ℚ) : WithBot ℚ) := by
    show (⊥ : WithBot ℚ) < _
    exact WithBot.bot_lt_coe _
  have h3 : ((histSp N hN).nodes[0]'hj).slotVal
      (((histSp N hN).nodes[0]'hj).fineSlot (boxChart 2 N c).2)
      = (1:ℚ) - 2*(N:ℚ) * ((boxChart 2 N c).2 : ℚ) := by
    show (nodeSp N hN).slotVal ((nodeSp N hN).fineSlot (boxChart 2 N c).2) = _
    rw [Node.slotVal, Node.fineSlot, show ((nodeSp N hN).Dwidth) = 1 from rfl,
      Nat.div_one, Nat.mul_one, Line.at]
    rfl
  constructor
  · rintro ⟨-, -, hband⟩
    rw [htH0_eq, h3] at hband
    by_cases hb0 : (boxChart 2 N c).2 = 0
    · refine ⟨hb0, ?_⟩
      rw [hb0] at hband
      have h4 : ((boxChart 2 N c).1 : ℚ) ≤ 1 := by push_cast at hband ⊢; linarith
      exact_mod_cast h4
    · exfalso
      have hb1 : (boxChart 2 N c).2 = 1 := by omega
      rw [hb1] at hband
      have hN1 : (1:ℚ) ≤ (N:ℚ) := by exact_mod_cast hN
      have h0le : (0:ℚ) ≤ ((boxChart 2 N c).1 : ℚ) := Nat.cast_nonneg _
      push_cast at hband
      linarith
  · rintro ⟨hb0, hℓ1⟩
    refine ⟨h1, h2, ?_⟩
    rw [htH0_eq, h3, hb0]
    have h4 : ((boxChart 2 N c).1 : ℚ) ≤ 1 := by exact_mod_cast hℓ1
    push_cast
    linarith

private lemma histSp_zc (N : ℕ) (hN : 1 ≤ N) :
    ∀ (hj : 0 < (histSp N hN).nodes.length) (j : Fin (2*N)),
      (boxChart 2 N j).2 < ((histSp N hN).nodes[0]'hj).μ * ((histSp N hN).nodes[0]'hj).childWidth →
      ((j ∈ Dsp N) ↔ (((histSp N hN).htH 1 (boxChart 2 N j) : ℚ) : WithBot ℚ)
        ≤ (histSp N hN).floorH 1 (boxChart 2 N j).2) := by
  intro hj j hb
  obtain ⟨hℓ, -⟩ := boxChart_lt 2 N j
  have hb0 : (boxChart 2 N j).2 = 0 := by
    have : (boxChart 2 N j).2 < 1 := hb
    omega
  have hht : (histSp N hN).htH 1 (boxChart 2 N j) = ((boxChart 2 N j).1 : ℚ) := by
    rw [History.htH, Finset.sum_range_one]
    rw [show (histSp N hN).innerslotH 0 (boxChart 2 N j).2 = 0 by
        show ((boxChart 2 N j).2 % (nodeSp N hN).childWidth) / (nodeSp N hN).Dwidth = 0
        rw [show (nodeSp N hN).childWidth = 1 from rfl, Nat.mod_one, Nat.zero_div]]
    norm_num
  have hfloor : (histSp N hN).floorH 1 (boxChart 2 N j).2 = (((1:ℚ)) : WithBot ℚ) := by
    rw [History.floorH]
    show (List.map (fun ν => ν.staircase (boxChart 2 N j).2)
        (List.take 1 [nodeSp N hN])).foldr max ⊥ = _
    rw [show List.take 1 [nodeSp N hN] = [nodeSp N hN] from rfl, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Node.staircase,
      if_pos (show (boxChart 2 N j).2 < (nodeSp N hN).μ * (nodeSp N hN).childWidth from hb),
      show ((boxChart 2 N j).2 / (nodeSp N hN).childWidth) * (nodeSp N hN).childWidth = 0 by
        show ((boxChart 2 N j).2 / 1) * 1 = 0
        omega]
    rw [max_eq_left bot_le]
    show ((((1:ℚ) - 2*(N:ℚ) * ((0:ℕ):ℚ)) : ℚ) : WithBot ℚ) = _
    norm_num
  rw [hht, hfloor, Dsp, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, WithBot.coe_le_coe]
  constructor
  · rintro ⟨-, hℓ1⟩
    exact_mod_cast hℓ1
  · intro h
    exact ⟨hb0, by exact_mod_cast h⟩

/-! #### The cylinder count and the endgame -/

private lemma card_zero_cylinder (m : ℕ) (D : Finset (Fin m)) :
    Nat.card ↥{x : Fin m → ZMod 3 | ∀ c ∈ D, x c = 0} = 3^(m - D.card) := by
  have e : ↥{x : Fin m → ZMod 3 | ∀ c ∈ D, x c = 0} ≃ ({c : Fin m // c ∉ D} → ZMod 3) :=
  { toFun := fun x c => x.1 c.1
    invFun := fun g => ⟨fun c => if hc : c ∈ D then 0 else g ⟨c, hc⟩, fun c hc => dif_pos hc⟩
    left_inv := fun x => Subtype.ext (funext fun c => by
      show (if hc : c ∈ D then 0 else x.1 c) = x.1 c
      by_cases hc : c ∈ D
      · rw [dif_pos hc, x.2 c hc]
      · rw [dif_neg hc])
    right_inv := fun g => funext fun c => by
      show (if hc : c.1 ∈ D then 0 else g ⟨c.1, hc⟩) = g c
      rw [dif_neg c.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  exact Fintype.card_coe D

/-- ORDER-0 SEPARATION GATE (p = 3, n = 2): the inert root history (g = 2) and a split
root history (g = 1) produce DIFFERENT stratum masses at the same level N. -/
theorem gate_order0_sep (N : ℕ) (hN : 1 ≤ N) :
    ∃ (Hin Hsp : History 3 F9)
      (Jin : JetSetup Hin 2 N (2 * N)) (Jsp : JetSetup Hsp 2 N (2 * N)),
      Hin.nodes.length = 1 ∧ Hsp.nodes.length = 1 ∧
      (∀ h0 : 0 < Hin.nodes.length,
        (Hin.nodes[0]'h0).species = ReadSpecies.root ∧
        (Hin.nodes[0]'h0).g = 2 ∧ (Hin.nodes[0]'h0).μ = 1) ∧
      (∀ h0 : 0 < Hsp.nodes.length,
        (Hsp.nodes[0]'h0).species = ReadSpecies.root ∧
        (Hsp.nodes[0]'h0).g = 1 ∧ (Hsp.nodes[0]'h0).μ = 1) ∧
      Nat.card (Jin.SHZ (topLocus 3 (2 * N)))
        ≠ Nat.card (Jsp.SHZ (topLocus 3 (2 * N))) := by
  refine ⟨histIn N hN, histSp N hN,
    gateSetup N hN (histIn N hN) rfl (histIn_coh N hN) (histIn_rh N hN) 2 (by norm_num)
      ((3:ℤ_[3])^(2*N)) (pow_dvd_pow (3:ℤ_[3]) (by omega)) (fun _ => histIn_land N hN)
      (Din N) (histIn_band N hN) (gate_hvalsupp N (histIn N hN) (fun _ => rfl))
      (histIn_zc N hN),
    gateSetup N hN (histSp N hN) rfl (histSp_coh N hN) (histSp_rh N hN) 1 le_rfl
      (-(3:ℤ_[3])^(2*N)) ((dvd_neg).mpr (pow_dvd_pow (3:ℤ_[3]) (by omega)))
      (fun _ => histSp_land N hN)
      (Dsp N) (histSp_band N hN) (gate_hvalsupp N (histSp N hN) (fun _ => rfl))
      (histSp_zc N hN),
    rfl, rfl, fun h0 => ⟨rfl, rfl, rfl⟩, fun h0 => ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [gateSetup_SHZ, gateSetup_SHZ, card_zero_cylinder, card_zero_cylinder]
  have hsub : Dsp N ⊆ Din N := by
    intro c hc
    rw [Dsp, Finset.mem_filter] at hc
    rw [Din, Finset.mem_filter]
    exact ⟨hc.1, Or.inl hc.2.1⟩
  have hwmem : (⟨0, by omega⟩ : Fin (2*N)) ∈ Din N := by
    rw [Din, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Or.inr ?_⟩
    show (0:ℕ)/2 ≤ 1
    norm_num
  have hwnot : (⟨0, by omega⟩ : Fin (2*N)) ∉ Dsp N := by
    rw [Dsp, Finset.mem_filter]
    rintro ⟨-, hb, -⟩
    have h10 : (1:ℕ) = 0 := hb
    omega
  have hlt : (Dsp N).card < (Din N).card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨_, hwmem, hwnot⟩)
  have hle : (Din N).card ≤ 2*N := by
    calc (Din N).card ≤ (Finset.univ : Finset (Fin (2*N))).card := Finset.card_le_univ _
    _ = 2*N := by rw [Finset.card_univ, Fintype.card_fin]
  intro h
  have heq := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  omega

end LeanUrat.MovesJ
