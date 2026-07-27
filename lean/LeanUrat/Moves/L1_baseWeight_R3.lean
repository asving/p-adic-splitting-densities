/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L1_gaussVal
import LeanUrat.Moves.L0_FactA_exists

/-!
# Moves/L1_baseWeight_R3 — the base valuation is multiplicative (§B2-DEF D.2, base stage)

**Round-3 audit repair** of `L1.baseWeight`.  Introduces the base valuation

  `baseWeight φ e h f := min_i (e·v(aᵢ) + i·h)`

over the φ-adic development `f = Σ aᵢ·φⁱ` (`v = gaussVal`, the Gauss/content valuation from
`L1_gaussVal`), and proves its multiplicativity on nonzero polynomials.  The `i`-th φ-adic
coefficient of `f` is extracted canonically as `(f /ₘ φⁱ) %ₘ φ` (monic `φ`), so no development
choice is needed and the definition elaborates without `Fact A`/`Fact B`.

## Faithfulness (trust boundary)

The definition is the sInf min-formula of §A.1 B1.1 (MOVES ~1995-1999): the set of slot weights
`{e·v(aᵢ) + i·h : aᵢ ≠ 0}` is nonempty and bounded below by `0` for `f ≠ 0` (each `v ≥ 0`,
`i·h ≥ 0`), so its `sInf` is attained.  `gaussVal` is now IMPORTED from `L1_gaussVal` (the
manifest dependency; the original fan-out inlined an identical private copy only because the
dep's olean was not yet on disk) — the definition text of `baseWeight` is unchanged.

## The proof (this file, 2026-07-27; the former honest `sorry` is discharged)

Direct MacLane base-case argument via the φ-adic development calculus — no graded ring needed:

* **Master lemma** (`dev_slots`): the canonical slots `(f /ₘ φⁱ) %ₘ φ` read off ANY development
  (uniqueness via `div_modByMonic_unique`, peeling one φ at a time).
* **`≥`**: develop `f·g` as the Cauchy product `c k = Σ_{i+j=k} aᵢbⱼ` (through
  `Polynomial ℤ_[p][Y]` and `eval`), re-develop with carries `s k = c k %ₘ φ + c (k−1) /ₘ φ`;
  every slot's content is bounded below via Gauss multiplicativity (`L1_gaussVal_mul`) and
  content-monotonicity of monic division (the carry pays `+h ≥ +1`).
* **`≤`**: at the MAXIMAL minimizing slots `I, J` of `f, g` the `(I,J)` term of `c (I+J)` is
  strictly dominant (integrality: a non-minimal or shifted slot costs ≥ 1 more after dividing
  by `e`), and `hirred` (so `φ̄` is prime and nonzero polynomials of degree `< deg φ̄` are not
  multiples) keeps the residue of the dominant term alive through `%ₘ φ`; hence slot `I+J` of
  `f·g` has content exactly `v(a_I) + v(b_J)` and weight exactly `w f + w g`.

The added hypotheses are used exactly where the mathematics needs them: `hirred` for the residue
step, `hh` for the carry, `hmon`/`hd` for the division calculus; `he`, `hcop` are part of the
faithful D.2 signature (value-group normalization) and are not needed for multiplicativity.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- The base valuation `w(f) = min_i (e·v(aᵢ) + i·h)` over the φ-adic development `f = Σ aᵢ·φⁱ`
(D.2 base stage; `v = gaussVal`).  The `i`-th φ-adic coefficient is `(f /ₘ φⁱ) %ₘ φ`; the `sInf`
of the (nonempty, `0`-bounded-below) slot-weight set is the attained minimum. -/
noncomputable def baseWeight {p : ℕ} [Fact p.Prime] (φ : Polynomial ℤ_[p]) (e h : ℕ)
    (f : Polynomial ℤ_[p]) : ℤ :=
  sInf { m : ℤ | ∃ i : ℕ, ((f /ₘ φ ^ i) %ₘ φ) ≠ 0 ∧
            m = (e : ℤ) * gaussVal ((f /ₘ φ ^ i) %ₘ φ) + (i : ℤ) * (h : ℤ) }

section BaseWeightProof

variable {p : ℕ} [Fact p.Prime]

/-! ### 1. The ℕ-valued content and the divisibility dictionary

Inlined from `L1_gaussVal`, where these helpers are `private`; `gaussVal` itself and its
multiplicativity `L1_gaussVal_mul` are imported. -/

private noncomputable def natGV (f : Polynomial ℤ_[p]) : ℕ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation) else 0

private lemma gaussVal_eq_natGV (f : Polynomial ℤ_[p]) : gaussVal f = (natGV f : ℤ) := by
  unfold gaussVal natGV
  by_cases hs : f.support.Nonempty
  · rw [dif_pos hs, dif_pos hs, Nat.cast_finsetInf']
  · rw [dif_neg hs, dif_neg hs, Nat.cast_zero]

private lemma padic_pow_dvd_iff {x : ℤ_[p]} (hx : x ≠ 0) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ x ↔ n ≤ x.valuation :=
  Ideal.mem_span_singleton.symm.trans (PadicInt.mem_span_pow_iff_le_valuation x hx n)

private lemma cpow_dvd_iff {f : Polynomial ℤ_[p]} (hf : f ≠ 0) (n : ℕ) :
    (C (p : ℤ_[p])) ^ n ∣ f ↔ n ≤ natGV f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [← map_pow, Polynomial.C_dvd_iff_dvd_coeff]
  simp only [natGV, dif_pos hne]
  constructor
  · intro hall
    apply Finset.le_inf'
    intro i hi
    exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mp (hall i)
  · intro hle i
    by_cases hi : i ∈ f.support
    · exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mpr
        (le_trans hle (Finset.inf'_le _ hi))
    · rw [Polynomial.mem_support_iff, not_not] at hi
      rw [hi]; exact dvd_zero _

private lemma cpow_natGV_dvd (f : Polynomial ℤ_[p]) : (C (p : ℤ_[p])) ^ (natGV f) ∣ f := by
  by_cases hf : f = 0
  · rw [hf]; exact dvd_zero _
  · exact (cpow_dvd_iff hf _).mpr le_rfl

private lemma natGV_mul {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    natGV (f * g) = natGV f + natGV g := by
  have hmul := L1_gaussVal_mul f g hf hg
  rw [gaussVal_eq_natGV, gaussVal_eq_natGV, gaussVal_eq_natGV] at hmul
  exact_mod_cast hmul

private lemma natGV_add_min {x y : Polynomial ℤ_[p]}
    (hxy : x + y ≠ 0) : min (natGV x) (natGV y) ≤ natGV (x + y) := by
  refine (cpow_dvd_iff hxy _).mp (dvd_add ?_ ?_)
  · exact dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (cpow_natGV_dvd x)
  · exact dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (cpow_natGV_dvd y)

/-- A nonzero finite sum has a nonzero summand of content at most the sum's content
(the ultrametric minimum principle, in attained form). -/
private lemma sum_min_witness {ι : Type*} (t : Finset ι) (x : ι → Polynomial ℤ_[p])
    (hs : (∑ i ∈ t, x i) ≠ 0) :
    ∃ i ∈ t, x i ≠ 0 ∧ natGV (x i) ≤ natGV (∑ i ∈ t, x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hs ⊢
    by_cases hxa : x a = 0
    · rw [hxa, zero_add] at hs ⊢
      obtain ⟨i, his, hxi, hle⟩ := ih hs
      exact ⟨i, Finset.mem_insert_of_mem his, hxi, hle⟩
    · by_cases hss : (∑ i ∈ s, x i) = 0
      · rw [hss, add_zero] at hs ⊢
        exact ⟨a, Finset.mem_insert_self a s, hxa, le_rfl⟩
      · have hmin := natGV_add_min hs
        rcases le_total (natGV (x a)) (natGV (∑ i ∈ s, x i)) with hle | hle
        · refine ⟨a, Finset.mem_insert_self a s, hxa, ?_⟩
          rwa [min_eq_left hle] at hmin
        · obtain ⟨i, his, hxi, hle2⟩ := ih hss
          refine ⟨i, Finset.mem_insert_of_mem his, hxi, le_trans hle2 ?_⟩
          rwa [min_eq_right hle] at hmin

/-! ### 2. Content through monic division -/

private lemma C_mul_modByMonic (c : ℤ_[p]) (x q : Polynomial ℤ_[p]) :
    (C c * x) %ₘ q = C c * (x %ₘ q) := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, smul_modByMonic]

private lemma C_mul_divByMonic (c : ℤ_[p]) (x q : Polynomial ℤ_[p]) (hq : q.Monic) :
    (C c * x) /ₘ q = C c * (x /ₘ q) := by
  have hkey : C c * (x %ₘ q) + q * (C c * (x /ₘ q)) = C c * x := by
    linear_combination (C c) * (modByMonic_add_div x q)
  have hdeg : degree (C c * (x %ₘ q)) < degree q := by
    refine lt_of_le_of_lt ?_ (degree_modByMonic_lt x hq)
    calc degree (C c * (x %ₘ q)) ≤ degree (C c) + degree (x %ₘ q) := degree_mul_le _ _
      _ ≤ 0 + degree (x %ₘ q) := add_le_add degree_C_le le_rfl
      _ = degree (x %ₘ q) := zero_add _
  exact (div_modByMonic_unique (C c * (x /ₘ q)) (C c * (x %ₘ q)) hq ⟨hkey, hdeg⟩).1

private lemma cpow_dvd_modByMonic {n : ℕ} {x q : Polynomial ℤ_[p]}
    (hdvd : (C (p : ℤ_[p])) ^ n ∣ x) : (C (p : ℤ_[p])) ^ n ∣ x %ₘ q := by
  obtain ⟨y, rfl⟩ := hdvd
  rw [← map_pow, C_mul_modByMonic]
  exact dvd_mul_right _ _

private lemma cpow_dvd_divByMonic {n : ℕ} {x q : Polynomial ℤ_[p]} (hq : q.Monic)
    (hdvd : (C (p : ℤ_[p])) ^ n ∣ x) : (C (p : ℤ_[p])) ^ n ∣ x /ₘ q := by
  obtain ⟨y, rfl⟩ := hdvd
  rw [← map_pow, C_mul_divByMonic _ _ _ hq]
  exact dvd_mul_right _ _

/-! ### 3. The reduction dictionary mod `p` -/

private lemma toZMod_poly_eq_zero_iff (z : Polynomial ℤ_[p]) :
    z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) = 0 ↔ (C (p : ℤ_[p])) ∣ z := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  have hker : ∀ x : ℤ_[p], (PadicInt.toZMod : ℤ_[p] →+* ZMod p) x = 0 ↔ (p : ℤ_[p]) ∣ x := by
    intro x
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  constructor
  · intro h0 n
    have hcn : (z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).coeff n = 0 := by rw [h0]; simp
    rw [Polynomial.coeff_map] at hcn
    exact (hker _).mp hcn
  · intro hdvd
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (hker _).mpr (hdvd n)

private lemma natGV_eq_zero_iff {z : Polynomial ℤ_[p]} (hz : z ≠ 0) :
    natGV z = 0 ↔ ¬ (C (p : ℤ_[p])) ∣ z := by
  constructor
  · intro h0 hdvd
    have h1 : (1 : ℕ) ≤ natGV z := (cpow_dvd_iff hz 1).mp (by rwa [pow_one])
    omega
  · intro hnd
    by_contra hne
    refine hnd ?_
    rw [← pow_one (C (p : ℤ_[p]))]
    exact (cpow_dvd_iff hz 1).mpr (by omega)

/-- Extract the content: `z = C (p^natGV z) * z₀` with `z₀` nonzero mod `p`. -/
private lemma extract_content {z : Polynomial ℤ_[p]} (hz : z ≠ 0) :
    ∃ z₀ : Polynomial ℤ_[p], z = C ((p : ℤ_[p]) ^ (natGV z)) * z₀ ∧ z₀ ≠ 0 ∧
      z₀.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := cpow_natGV_dvd z
  rw [← map_pow] at hz₀
  refine ⟨z₀, hz₀, ?_, ?_⟩
  · intro h0; rw [h0, mul_zero] at hz₀; exact hz hz₀
  · intro hred
    rw [toZMod_poly_eq_zero_iff] at hred
    obtain ⟨w, hw⟩ := hred
    have hdvd : (C (p : ℤ_[p])) ^ (natGV z + 1) ∣ z := by
      refine ⟨w, ?_⟩
      conv_lhs => rw [hz₀, hw]
      rw [pow_succ, map_pow]
      ring
    have := (cpow_dvd_iff hz _).mp hdvd
    omega

private lemma natGV_C_pow (n : ℕ) : natGV (C ((p : ℤ_[p]) ^ n)) = n := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  have hpn : ((p : ℤ_[p]) ^ n) ≠ 0 := pow_ne_zero n hp0
  have hCne : (C ((p : ℤ_[p]) ^ n) : Polynomial ℤ_[p]) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact hpn
  have hge : n ≤ natGV (C ((p : ℤ_[p]) ^ n)) := by
    refine (cpow_dvd_iff hCne n).mp ⟨1, ?_⟩
    rw [mul_one, map_pow]
  have hlt : ¬ (n + 1 ≤ natGV (C ((p : ℤ_[p]) ^ n))) := by
    intro hle
    obtain ⟨w, hw⟩ := (cpow_dvd_iff hCne (n + 1)).mpr hle
    have hc0 := congrArg (fun z : Polynomial ℤ_[p] => z.coeff 0) hw
    simp only [coeff_C_zero, ← map_pow, Polynomial.coeff_C_mul] at hc0
    have hdvd : (p : ℤ_[p]) ^ (n + 1) ∣ (p : ℤ_[p]) ^ n := ⟨w.coeff 0, hc0⟩
    have hval := (padic_pow_dvd_iff hpn (n + 1)).mp hdvd
    have hvn : ((p : ℤ_[p]) ^ n).valuation = n * (p : ℤ_[p]).valuation :=
      PadicInt.valuation_pow _ _
    rw [hvn, PadicInt.valuation_p, mul_one] at hval
    omega
  omega

/-! ### 4. Canonical slots and the master (development-uniqueness) lemma -/

/-- The canonical `i`-th φ-adic slot of `f`. -/
private noncomputable def slotc (φ f : Polynomial ℤ_[p]) (i : ℕ) : Polynomial ℤ_[p] :=
  (f /ₘ φ ^ i) %ₘ φ

/-- Division by `φ^(j+1)` is division by `φ` then by `φ^j`. -/
private lemma div_pow_succ (φ : Polynomial ℤ_[p]) (hmon : φ.Monic) (_hd : 1 ≤ φ.natDegree)
    (f : Polynomial ℤ_[p]) (j : ℕ) : f /ₘ φ ^ (j + 1) = (f /ₘ φ) /ₘ φ ^ j := by
  have hφ0 : φ ≠ 0 := hmon.ne_zero
  have hdpow : ∀ n : ℕ, degree (φ ^ n) = ((n * φ.natDegree : ℕ) : WithBot ℕ) := by
    intro n
    rw [degree_eq_natDegree (pow_ne_zero n hφ0), hmon.natDegree_pow]
  have hkey : (f %ₘ φ + φ * ((f /ₘ φ) %ₘ φ ^ j)) + φ ^ (j + 1) * ((f /ₘ φ) /ₘ φ ^ j) = f := by
    have h1 := modByMonic_add_div f φ
    have h2 := modByMonic_add_div (f /ₘ φ) (φ ^ j)
    have hps : φ ^ (j + 1) = φ * φ ^ j := by rw [pow_succ]; ring
    rw [hps]
    linear_combination h1 + φ * h2
  have hdlt : degree (f %ₘ φ + φ * ((f /ₘ φ) %ₘ φ ^ j)) < degree (φ ^ (j + 1)) := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_lt_of_le (degree_modByMonic_lt f hmon) ?_
      rw [degree_eq_natDegree hφ0, hdpow]
      exact_mod_cast Nat.le_mul_of_pos_left _ (by omega)
    · by_cases hz : (f /ₘ φ) %ₘ φ ^ j = 0
      · rw [hz, mul_zero, degree_zero, hdpow]
        exact WithBot.bot_lt_coe _
      · rw [degree_mul]
        have hlt := degree_modByMonic_lt (f /ₘ φ) (hmon.pow (n := j))
        rw [hdpow j] at hlt
        rw [degree_eq_natDegree hz] at hlt ⊢
        rw [degree_eq_natDegree hφ0, hdpow, ← Nat.cast_add]
        have hlt' : ((f /ₘ φ) %ₘ φ ^ j).natDegree < j * φ.natDegree := by exact_mod_cast hlt
        have hexp : (j + 1) * φ.natDegree = j * φ.natDegree + φ.natDegree := by ring
        exact_mod_cast (by omega :
          φ.natDegree + ((f /ₘ φ) %ₘ φ ^ j).natDegree < (j + 1) * φ.natDegree)
  exact (div_modByMonic_unique ((f /ₘ φ) /ₘ φ ^ j) (f %ₘ φ + φ * ((f /ₘ φ) %ₘ φ ^ j))
    (hmon.pow (n := j + 1)) ⟨hkey, hdlt⟩).1

/-- **Master lemma**: the canonical slots read off any development. -/
private lemma dev_slots (φ : Polynomial ℤ_[p]) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree) :
    ∀ (N : ℕ) (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]),
      IsDevelopment φ f B N → ∀ j, slotc φ f j = B j := by
  intro N
  induction N with
  | zero =>
    intro f B hdev j
    obtain ⟨hdeg, hzero, hsum⟩ := hdev
    rw [Finset.range_zero, Finset.sum_empty] at hsum
    show (f /ₘ φ ^ j) %ₘ φ = B j
    rw [hsum, zero_divByMonic, zero_modByMonic, hzero j (Nat.zero_le j)]
  | succ N ih =>
    intro f B hdev
    obtain ⟨hdeg, hzero, hsum⟩ := hdev
    have hstep : ∑ i ∈ Finset.range N, B (i + 1) * φ ^ (i + 1)
        = φ * ∑ i ∈ Finset.range N, B (i + 1) * φ ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    have hqr : B 0 + φ * (∑ i ∈ Finset.range N, B (i + 1) * φ ^ i) = f := by
      rw [hsum, Finset.sum_range_succ', hstep, pow_zero, mul_one, add_comm]
    obtain ⟨hdivf, hmodf⟩ := div_modByMonic_unique (f := f) (g := φ)
      (∑ i ∈ Finset.range N, B (i + 1) * φ ^ i) (B 0) hmon ⟨hqr, hdeg 0⟩
    have hdev₁ : IsDevelopment φ (∑ i ∈ Finset.range N, B (i + 1) * φ ^ i)
        (fun i => B (i + 1)) N :=
      ⟨fun i => hdeg (i + 1), fun i hi => hzero (i + 1) (by omega), rfl⟩
    intro j
    cases j with
    | zero =>
      show (f /ₘ φ ^ 0) %ₘ φ = B 0
      rw [pow_zero, divByMonic_one]
      exact hmodf
    | succ j =>
      show (f /ₘ φ ^ (j + 1)) %ₘ φ = B (j + 1)
      rw [div_pow_succ φ hmon hd f j, hdivf]
      exact ih (∑ i ∈ Finset.range N, B (i + 1) * φ ^ i) (fun i => B (i + 1)) hdev₁ j

/-- The canonical slots form a development (Fact A + the master lemma). -/
private lemma canonical_dev (φ : Polynomial ℤ_[p]) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree)
    (f : Polynomial ℤ_[p]) : ∃ N, IsDevelopment φ f (slotc φ f) N := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists φ hmon hd f
  refine ⟨N, fun j => ?_, fun j hj => ?_, ?_⟩
  · show degree ((f /ₘ φ ^ j) %ₘ φ) < degree φ
    exact degree_modByMonic_lt _ hmon
  · rw [dev_slots φ hmon hd N f B hdev j]
    exact hdev.2.1 j hj
  · calc f = ∑ j ∈ Finset.range N, B j * φ ^ j := hdev.2.2
      _ = ∑ j ∈ Finset.range N, slotc φ f j * φ ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [dev_slots φ hmon hd N f B hdev j]

/-- A nonzero canonical slot bounds the index by the degree. -/
private lemma slot_index_le (φ : Polynomial ℤ_[p]) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree)
    {f : Polynomial ℤ_[p]} {i : ℕ} (hi : slotc φ f i ≠ 0) : i ≤ f.natDegree := by
  have hdiv : f /ₘ φ ^ i ≠ 0 := by
    intro h0
    exact hi (by show (f /ₘ φ ^ i) %ₘ φ = 0; rw [h0, zero_modByMonic])
  have hnlt : ¬ (degree f < degree (φ ^ i)) :=
    fun hlt => hdiv ((divByMonic_eq_zero_iff (hmon.pow (n := i))).mpr hlt)
  have h1 : (φ ^ i).natDegree ≤ f.natDegree := natDegree_le_natDegree (not_lt.mp hnlt)
  rw [hmon.natDegree_pow] at h1
  calc i ≤ i * φ.natDegree := Nat.le_mul_of_pos_right i (by omega)
    _ ≤ f.natDegree := h1

/-! ### 5. The slot-weight set of `baseWeight` -/

private def Sw (φ : Polynomial ℤ_[p]) (e₀ h₀ : ℕ) (f : Polynomial ℤ_[p]) : Set ℤ :=
  { m : ℤ | ∃ i : ℕ, slotc φ f i ≠ 0 ∧
      m = (e₀ : ℤ) * gaussVal (slotc φ f i) + (i : ℤ) * (h₀ : ℤ) }

private lemma baseWeight_eq_sInf (φ : Polynomial ℤ_[p]) (e₀ h₀ : ℕ) (f : Polynomial ℤ_[p]) :
    baseWeight φ e₀ h₀ f = sInf (Sw φ e₀ h₀ f) := rfl

private lemma Sw_bddBelow (φ : Polynomial ℤ_[p]) (e₀ h₀ : ℕ) (f : Polynomial ℤ_[p]) :
    BddBelow (Sw φ e₀ h₀ f) := by
  refine ⟨0, ?_⟩
  rintro m ⟨i, hi, rfl⟩
  have h1 : (0 : ℤ) ≤ gaussVal (slotc φ f i) := by
    rw [gaussVal_eq_natGV]; positivity
  have h2 : (0 : ℤ) ≤ (e₀ : ℤ) := by positivity
  have h3 : (0 : ℤ) ≤ (i : ℤ) * (h₀ : ℤ) := by positivity
  nlinarith

private lemma baseWeight_le (φ : Polynomial ℤ_[p]) (e₀ h₀ : ℕ) (f : Polynomial ℤ_[p])
    {i : ℕ} (hi : slotc φ f i ≠ 0) :
    baseWeight φ e₀ h₀ f ≤ (e₀ : ℤ) * (natGV (slotc φ f i) : ℤ) + (i : ℤ) * (h₀ : ℤ) := by
  rw [baseWeight_eq_sInf]
  exact csInf_le (Sw_bddBelow φ e₀ h₀ f) ⟨i, hi, by rw [gaussVal_eq_natGV]⟩

/-- The minimum is attained at a MAXIMAL minimizing slot: any strictly later nonzero slot
weighs at least one more. -/
private lemma baseWeight_attained_max (φ : Polynomial ℤ_[p]) (hmon : φ.Monic)
    (hd : 1 ≤ φ.natDegree) (e₀ h₀ : ℕ) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    ∃ i : ℕ, slotc φ f i ≠ 0 ∧
      baseWeight φ e₀ h₀ f = (e₀ : ℤ) * (natGV (slotc φ f i) : ℤ) + (i : ℤ) * (h₀ : ℤ) ∧
      ∀ i' : ℕ, i < i' → slotc φ f i' ≠ 0 →
        baseWeight φ e₀ h₀ f + 1 ≤ (e₀ : ℤ) * (natGV (slotc φ f i') : ℤ) + (i' : ℤ) * (h₀ : ℤ) := by
  classical
  have hne : (Sw φ e₀ h₀ f).Nonempty := by
    obtain ⟨N, hdev⟩ := canonical_dev φ hmon hd f
    have hex : ∃ j, slotc φ f j ≠ 0 := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hf
      rw [hdev.2.2]
      exact Finset.sum_eq_zero fun j _ => by rw [hall j, zero_mul]
    obtain ⟨j, hj⟩ := hex
    exact ⟨_, ⟨j, hj, rfl⟩⟩
  have hmem := Int.csInf_mem hne (Sw_bddBelow φ e₀ h₀ f)
  rw [← baseWeight_eq_sInf] at hmem
  obtain ⟨i₀, hi₀, heq₀⟩ := hmem
  rw [gaussVal_eq_natGV] at heq₀
  set P : ℕ → Prop := fun i => slotc φ f i ≠ 0 ∧
    baseWeight φ e₀ h₀ f = (e₀ : ℤ) * (natGV (slotc φ f i) : ℤ) + (i : ℤ) * (h₀ : ℤ) with hP
  have hi₀b : i₀ ≤ f.natDegree := slot_index_le φ hmon hd hi₀
  have hspec : P (Nat.findGreatest P f.natDegree) :=
    Nat.findGreatest_spec hi₀b (by rw [hP]; exact ⟨hi₀, heq₀⟩)
  refine ⟨Nat.findGreatest P f.natDegree, hspec.1, hspec.2, ?_⟩
  intro i' hgt hne'
  have hle' := baseWeight_le φ e₀ h₀ f hne'
  have hneq : baseWeight φ e₀ h₀ f
      ≠ (e₀ : ℤ) * (natGV (slotc φ f i') : ℤ) + (i' : ℤ) * (h₀ : ℤ) := by
    intro heq
    exact Nat.findGreatest_is_greatest hgt (slot_index_le φ hmon hd hne')
      (by rw [hP]; exact ⟨hne', heq⟩)
  exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne hle' hneq)

/-- Cancel a positive integer factor across a strict inequality. -/
private lemma cancel_mul_succ {e₀ : ℕ} (he : 1 ≤ e₀) {x y : ℕ}
    (hle : (e₀ : ℤ) * (x : ℤ) + 1 ≤ (e₀ : ℤ) * (y : ℤ)) : x + 1 ≤ y := by
  rcases Nat.lt_or_ge x y with hlt | hge
  · omega
  · exfalso
    have hyx : (y : ℤ) ≤ (x : ℤ) := by exact_mod_cast hge
    have : (e₀ : ℤ) * (y : ℤ) ≤ (e₀ : ℤ) * (x : ℤ) :=
      mul_le_mul_of_nonneg_left hyx (by positivity)
    linarith

/-! ### 6. The theorem -/

end BaseWeightProof

theorem L1_baseWeight_valuation {p : ℕ} [Fact p.Prime] (φ : Polynomial ℤ_[p]) (e h : ℕ) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.gcd e h = 1) (hirred : Irreducible (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : baseWeight φ e h (f * g) = baseWeight φ e h f + baseWeight φ e h g := by
  classical
  have hφ0 : φ ≠ 0 := hmon.ne_zero
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  -- (1) maximal minimizing slots of f and g
  obtain ⟨I, haI, hwf, hfmax⟩ := baseWeight_attained_max φ hmon hd e h hf
  obtain ⟨J, hbJ, hwg, hgmax⟩ := baseWeight_attained_max φ hmon hd e h hg
  set α := natGV (slotc φ f I) with hα
  set β := natGV (slotc φ g J) with hβ
  set V := α + β with hV
  set K := I + J with hK
  have hwfg : baseWeight φ e h f + baseWeight φ e h g
      = (e : ℤ) * (V : ℤ) + (K : ℤ) * (h : ℤ) := by
    rw [hwf, hwg, hV, hK]; push_cast; ring
  -- (2) canonical developments
  obtain ⟨Nf, hdevf⟩ := canonical_dev φ hmon hd f
  obtain ⟨Ng, hdevg⟩ := canonical_dev φ hmon hd g
  -- (3) the Cauchy product through Polynomial (Polynomial ℤ_[p])
  set F : Polynomial (Polynomial ℤ_[p]) :=
    ∑ i ∈ Finset.range Nf, Polynomial.monomial i (slotc φ f i) with hF
  set G : Polynomial (Polynomial ℤ_[p]) :=
    ∑ i ∈ Finset.range Ng, Polynomial.monomial i (slotc φ g i) with hG
  have hFcoeff : ∀ n, F.coeff n = slotc φ f n := by
    intro n
    rw [hF, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range Nf) n (fun i => slotc φ f i)]
    by_cases hn : n ∈ Finset.range Nf
    · rw [if_pos hn]
    · rw [if_neg hn]
      exact (hdevf.2.1 n (by simpa using hn)).symm
  have hGcoeff : ∀ n, G.coeff n = slotc φ g n := by
    intro n
    rw [hG, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range Ng) n (fun i => slotc φ g i)]
    by_cases hn : n ∈ Finset.range Ng
    · rw [if_pos hn]
    · rw [if_neg hn]
      exact (hdevg.2.1 n (by simpa using hn)).symm
  have hFeval : F.eval φ = f := by
    rw [hF, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial]
    exact hdevf.2.2.symm
  have hGeval : G.eval φ = g := by
    rw [hG, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial]
    exact hdevg.2.2.symm
  set c : ℕ → Polynomial ℤ_[p] := fun k => (F * G).coeff k with hc
  set M : ℕ := (F * G).natDegree with hM
  have hc_anti : ∀ k, c k = ∑ i ∈ Finset.range (k + 1), slotc φ f i * slotc φ g (k - i) := by
    intro k
    rw [hc]
    show (F * G).coeff k = _
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Finset.sum_congr rfl fun i _ => by rw [hFcoeff, hGcoeff]
  have hc0 : ∀ k, M < k → c k = 0 := by
    intro k hk
    rw [hc]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hk
  have hcfg : f * g = ∑ k ∈ Finset.range (M + 1), c k * φ ^ k := by
    have hprod : f * g = (F * G).eval φ := by rw [Polynomial.eval_mul, hFeval, hGeval]
    rw [hprod, Polynomial.eval_eq_sum_range]
  -- (4) the re-development with carries
  set cpred : ℕ → Polynomial ℤ_[p] :=
    fun k => match k with | 0 => 0 | j + 1 => c j with hcpred
  have hcpred0 : cpred 0 = 0 := rfl
  have hcpredS : ∀ j, cpred (j + 1) = c j := fun j => rfl
  set s : ℕ → Polynomial ℤ_[p] := fun k => c k %ₘ φ + cpred k /ₘ φ with hs
  have hsdef : ∀ k, s k = c k %ₘ φ + cpred k /ₘ φ := fun k => rfl
  -- slot degree bounds
  have hslot_natdeg : ∀ (w : Polynomial ℤ_[p]) i, (slotc φ w i).natDegree ≤ φ.natDegree - 1 := by
    intro w i
    have hlt : degree (slotc φ w i) < degree φ := degree_modByMonic_lt _ hmon
    by_cases hz : slotc φ w i = 0
    · rw [hz, natDegree_zero]; omega
    · have := natDegree_lt_natDegree hz hlt
      omega
  have hc_natdeg : ∀ k, (c k).natDegree ≤ 2 * φ.natDegree - 2 := by
    intro k
    rw [hc_anti k]
    apply natDegree_sum_le_of_forall_le
    intro i _
    calc (slotc φ f i * slotc φ g (k - i)).natDegree
        ≤ (slotc φ f i).natDegree + (slotc φ g (k - i)).natDegree := natDegree_mul_le
      _ ≤ (φ.natDegree - 1) + (φ.natDegree - 1) :=
          add_le_add (hslot_natdeg f i) (hslot_natdeg g (k - i))
      _ ≤ 2 * φ.natDegree - 2 := by omega
  have hbotφ : (⊥ : WithBot ℕ) < degree φ :=
    bot_lt_iff_ne_bot.mpr (fun hb => hφ0 (degree_eq_bot.mp hb))
  have hcdiv_deg : ∀ k, degree (c k /ₘ φ) < degree φ := by
    intro k
    by_cases hz : c k /ₘ φ = 0
    · rw [hz, degree_zero]; exact hbotφ
    · have hnd : (c k /ₘ φ).natDegree = (c k).natDegree - φ.natDegree :=
        natDegree_divByMonic (c k) hmon
      have h1 : (c k /ₘ φ).natDegree < φ.natDegree := by
        have := hc_natdeg k; omega
      rw [degree_eq_natDegree hz, degree_eq_natDegree hφ0]
      exact_mod_cast h1
  -- the development of f*g
  have hdev_s : IsDevelopment φ (f * g) s (M + 2) := by
    refine ⟨fun k => ?_, fun k hk => ?_, ?_⟩
    · -- degrees
      rw [hsdef k]
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_modByMonic_lt _ hmon) ?_)
      cases k with
      | zero => rw [hcpred0, zero_divByMonic, degree_zero]; exact hbotφ
      | succ k' => rw [hcpredS k']; exact hcdiv_deg k'
    · -- vanishing beyond M+2
      rw [hsdef k]
      cases k with
      | zero => exact absurd hk (by omega)
      | succ k' =>
        rw [hcpredS k', hc0 (k' + 1) (by omega), hc0 k' (by omega),
          zero_modByMonic, zero_divByMonic, add_zero]
    · -- the sum
      have hR : ∑ k ∈ Finset.range (M + 2), s k * φ ^ k
          = (∑ k ∈ Finset.range (M + 2), (c k %ₘ φ) * φ ^ k)
            + ∑ k ∈ Finset.range (M + 2), (cpred k /ₘ φ) * φ ^ k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [hsdef k, add_mul]
      have hR1 : ∑ k ∈ Finset.range (M + 2), (c k %ₘ φ) * φ ^ k
          = ∑ k ∈ Finset.range (M + 1), (c k %ₘ φ) * φ ^ k := by
        rw [Finset.sum_range_succ, hc0 (M + 1) (by omega), zero_modByMonic, zero_mul, add_zero]
      have hR2 : ∑ k ∈ Finset.range (M + 2), (cpred k /ₘ φ) * φ ^ k
          = ∑ k ∈ Finset.range (M + 1), (c k /ₘ φ) * φ ^ (k + 1) := by
        rw [Finset.sum_range_succ']
        have hu0 : (cpred 0 /ₘ φ) * φ ^ 0 = 0 := by
          rw [hcpred0, zero_divByMonic, zero_mul]
        rw [hu0, add_zero]
      rw [hR, hR1, hR2, ← Finset.sum_add_distrib, hcfg]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [← modByMonic_add_div (c k) φ]
      rw [pow_succ]
      ring
  have hslot : ∀ k, slotc φ (f * g) k = s k :=
    dev_slots φ hmon hd (M + 2) (f * g) s hdev_s
  -- (5) generic per-level lower bound
  have hCLB : ∀ k, c k ≠ 0 → baseWeight φ e h f + baseWeight φ e h g
      ≤ (e : ℤ) * (natGV (c k) : ℤ) + (k : ℤ) * (h : ℤ) := by
    intro k hck
    have hck' : (∑ i ∈ Finset.range (k + 1), slotc φ f i * slotc φ g (k - i)) ≠ 0 := by
      rw [← hc_anti k]; exact hck
    obtain ⟨i, hik, hterm_ne, hle⟩ := sum_min_witness (Finset.range (k + 1))
      (fun i => slotc φ f i * slotc φ g (k - i)) hck'
    have hi_ne : slotc φ f i ≠ 0 := left_ne_zero_of_mul hterm_ne
    have hj_ne : slotc φ g (k - i) ≠ 0 := right_ne_zero_of_mul hterm_ne
    have hik' : i ≤ k := by
      have := Finset.mem_range.mp hik; omega
    have h1 := baseWeight_le φ e h f hi_ne
    have h2 := baseWeight_le φ e h g hj_ne
    rw [natGV_mul hi_ne hj_ne] at hle
    rw [← hc_anti k] at hle
    have hle' : ((natGV (slotc φ f i) : ℤ) + (natGV (slotc φ g (k - i)) : ℤ))
        ≤ (natGV (c k) : ℤ) := by exact_mod_cast hle
    have hmono : (e : ℤ) * ((natGV (slotc φ f i) : ℤ) + (natGV (slotc φ g (k - i)) : ℤ))
        ≤ (e : ℤ) * (natGV (c k) : ℤ) :=
      mul_le_mul_of_nonneg_left hle' (by positivity)
    have hcast : ((i : ℤ)) + ((k - i : ℕ) : ℤ) = (k : ℤ) := by
      have hik'' : i + (k - i) = k := by omega
      exact_mod_cast hik''
    nlinarith [h1, h2, hmono, hcast]
  -- level bounds for the two carry parts
  have hMOD : ∀ k, c k %ₘ φ ≠ 0 → baseWeight φ e h f + baseWeight φ e h g
      ≤ (e : ℤ) * (natGV (c k %ₘ φ) : ℤ) + (k : ℤ) * (h : ℤ) := by
    intro k hne
    have hck : c k ≠ 0 := by
      intro h0; exact hne (by rw [h0, zero_modByMonic])
    have hdvd : (C (p : ℤ_[p])) ^ (natGV (c k)) ∣ c k %ₘ φ :=
      cpow_dvd_modByMonic (cpow_natGV_dvd (c k))
    have hle : natGV (c k) ≤ natGV (c k %ₘ φ) := (cpow_dvd_iff hne _).mp hdvd
    have hle' : ((natGV (c k) : ℤ)) ≤ (natGV (c k %ₘ φ) : ℤ) := by exact_mod_cast hle
    have hmono : (e : ℤ) * (natGV (c k) : ℤ) ≤ (e : ℤ) * (natGV (c k %ₘ φ) : ℤ) :=
      mul_le_mul_of_nonneg_left hle' (by positivity)
    have := hCLB k hck
    linarith
  have hDIV : ∀ k, cpred k /ₘ φ ≠ 0 → baseWeight φ e h f + baseWeight φ e h g
      ≤ (e : ℤ) * (natGV (cpred k /ₘ φ) : ℤ) + (k : ℤ) * (h : ℤ) := by
    intro k hne
    cases k with
    | zero =>
      exact absurd (by rw [hcpred0, zero_divByMonic]) hne
    | succ k' =>
      rw [hcpredS k'] at hne ⊢
      have hck : c k' ≠ 0 := by
        intro h0; exact hne (by rw [h0, zero_divByMonic])
      have hdvd : (C (p : ℤ_[p])) ^ (natGV (c k')) ∣ c k' /ₘ φ :=
        cpow_dvd_divByMonic hmon (cpow_natGV_dvd (c k'))
      have hle : natGV (c k') ≤ natGV (c k' /ₘ φ) := (cpow_dvd_iff hne _).mp hdvd
      have hle' : ((natGV (c k') : ℤ)) ≤ (natGV (c k' /ₘ φ) : ℤ) := by exact_mod_cast hle
      have hmono : (e : ℤ) * (natGV (c k') : ℤ) ≤ (e : ℤ) * (natGV (c k' /ₘ φ) : ℤ) :=
        mul_le_mul_of_nonneg_left hle' (by positivity)
      have hclb := hCLB k' hck
      have hcastk : ((k' + 1 : ℕ) : ℤ) = (k' : ℤ) + 1 := by push_cast; ring
      have hh' : (0 : ℤ) ≤ (h : ℤ) := by positivity
      rw [hcastk]
      nlinarith
  -- (6) the lower bound over all slots of f*g
  have hlb : ∀ m ∈ Sw φ e h (f * g), baseWeight φ e h f + baseWeight φ e h g ≤ m := by
    rintro m ⟨k, hk_ne, rfl⟩
    rw [hslot k] at hk_ne ⊢
    rw [gaussVal_eq_natGV]
    rw [hsdef k] at hk_ne ⊢
    by_cases hm0 : c k %ₘ φ = 0
    · rw [hm0, zero_add] at hk_ne ⊢
      exact hDIV k hk_ne
    · by_cases hd0 : cpred k /ₘ φ = 0
      · rw [hd0, add_zero] at hk_ne ⊢
        exact hMOD k hm0
      · have hmin := natGV_add_min hk_ne
        have hM' := hMOD k hm0
        have hD' := hDIV k hd0
        rcases min_cases (natGV (c k %ₘ φ)) (natGV (cpred k /ₘ φ)) with ⟨hminEq, _⟩ | ⟨hminEq, _⟩
        · rw [hminEq] at hmin
          have hle' : ((natGV (c k %ₘ φ) : ℤ))
              ≤ (natGV (c k %ₘ φ + cpred k /ₘ φ) : ℤ) := by exact_mod_cast hmin
          have hmono : (e : ℤ) * (natGV (c k %ₘ φ) : ℤ)
              ≤ (e : ℤ) * (natGV (c k %ₘ φ + cpred k /ₘ φ) : ℤ) :=
            mul_le_mul_of_nonneg_left hle' (by positivity)
          linarith
        · rw [hminEq] at hmin
          have hle' : ((natGV (cpred k /ₘ φ) : ℤ))
              ≤ (natGV (c k %ₘ φ + cpred k /ₘ φ) : ℤ) := by exact_mod_cast hmin
          have hmono : (e : ℤ) * (natGV (cpred k /ₘ φ) : ℤ)
              ≤ (e : ℤ) * (natGV (c k %ₘ φ + cpred k /ₘ φ) : ℤ) :=
            mul_le_mul_of_nonneg_left hle' (by positivity)
          linarith
  -- (7) strictness off the anchor pair (i ≠ I on the K-antidiagonal)
  have hstrict_term : ∀ i j : ℕ, i + j = K → i ≠ I → slotc φ f i ≠ 0 → slotc φ g j ≠ 0 →
      V + 1 ≤ natGV (slotc φ f i) + natGV (slotc φ g j) := by
    intro i j hij hne hai hbj
    have h1 := baseWeight_le φ e h f hai
    have h2 := baseWeight_le φ e h g hbj
    have hstrict : baseWeight φ e h f + baseWeight φ e h g + 1
        ≤ (e : ℤ) * (natGV (slotc φ f i) : ℤ) + (i : ℤ) * (h : ℤ)
          + ((e : ℤ) * (natGV (slotc φ g j) : ℤ) + (j : ℤ) * (h : ℤ)) := by
      rcases Nat.lt_or_ge i I with hlt | hge
      · have hjJ : J < j := by omega
        have := hgmax j hjJ hbj
        linarith
      · have hIi : I < i := lt_of_le_of_ne hge (Ne.symm hne)
        have := hfmax i hIi hai
        linarith
    rw [hwfg] at hstrict
    have hijZ : (i : ℤ) * (h : ℤ) + (j : ℤ) * (h : ℤ) = (K : ℤ) * (h : ℤ) := by
      have : ((i : ℤ) + (j : ℤ)) = (K : ℤ) := by exact_mod_cast hij
      nlinarith [this]
    have hmul : (e : ℤ) * (V : ℤ) + 1
        ≤ (e : ℤ) * ((natGV (slotc φ f i) + natGV (slotc φ g j) : ℕ) : ℤ) := by
      push_cast at hstrict ⊢
      linarith
    exact cancel_mul_succ he hmul
  -- (8) strict divisibility of the K-level tail and the (K−1)-level carry
  have hIK : I ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hcK_split : c K = slotc φ f I * slotc φ g J
      + ∑ i ∈ (Finset.range (K + 1)).erase I, slotc φ f i * slotc φ g (K - i) := by
    rw [hc_anti K]
    conv_lhs => rw [← Finset.insert_erase hIK,
      Finset.sum_insert (Finset.notMem_erase _ _)]
    rw [show K - I = J from by omega]
  have hy_dvd : (C (p : ℤ_[p])) ^ (V + 1)
      ∣ ∑ i ∈ (Finset.range (K + 1)).erase I, slotc φ f i * slotc φ g (K - i) := by
    apply Finset.dvd_sum
    intro i hi
    have hiI : i ≠ I := Finset.ne_of_mem_erase hi
    have hik : i ≤ K := by
      have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega
    by_cases hterm : slotc φ f i * slotc φ g (K - i) = 0
    · rw [hterm]; exact dvd_zero _
    · have hai : slotc φ f i ≠ 0 := left_ne_zero_of_mul hterm
      have hbj : slotc φ g (K - i) ≠ 0 := right_ne_zero_of_mul hterm
      rw [cpow_dvd_iff hterm, natGV_mul hai hbj]
      exact hstrict_term i (K - i) (by omega) hiI hai hbj
  have hextra_dvd : (C (p : ℤ_[p])) ^ (V + 1) ∣ cpred K /ₘ φ := by
    cases hK' : K with
    | zero => rw [hcpred0, zero_divByMonic]; exact dvd_zero _
    | succ K' =>
      rw [hcpredS K']
      apply cpow_dvd_divByMonic hmon
      rw [hc_anti K']
      apply Finset.dvd_sum
      intro i hi
      by_cases hterm : slotc φ f i * slotc φ g (K' - i) = 0
      · rw [hterm]; exact dvd_zero _
      · have hai : slotc φ f i ≠ 0 := left_ne_zero_of_mul hterm
        have hbj : slotc φ g (K' - i) ≠ 0 := right_ne_zero_of_mul hterm
        rw [cpow_dvd_iff hterm, natGV_mul hai hbj]
        have h1 := baseWeight_le φ e h f hai
        have h2 := baseWeight_le φ e h g hbj
        have hik : i ≤ K' := by
          have := Finset.mem_range.mp hi; omega
        -- e·(αᵢ+βⱼ) + K'·h ≥ e·V + (K'+1)·h  ⟹  αᵢ+βⱼ ≥ V+1  (h ≥ 1)
        have hsum : (e : ℤ) * (V : ℤ) + ((K' : ℤ) + 1) * (h : ℤ)
            ≤ (e : ℤ) * (natGV (slotc φ f i) : ℤ) + (i : ℤ) * (h : ℤ)
              + ((e : ℤ) * (natGV (slotc φ g (K' - i)) : ℤ)
                + ((K' - i : ℕ) : ℤ) * (h : ℤ)) := by
          have hKZ : ((K : ℕ) : ℤ) = (K' : ℤ) + 1 := by
            rw [hK']; push_cast; ring
          rw [← hKZ, ← hwfg]
          linarith
        have hijZ : (i : ℤ) + ((K' - i : ℕ) : ℤ) = (K' : ℤ) := by
          have hik'' : i + (K' - i) = K' := by omega
          exact_mod_cast hik''
        have hmul : (e : ℤ) * (V : ℤ) + 1
            ≤ (e : ℤ) * ((natGV (slotc φ f i) + natGV (slotc φ g (K' - i)) : ℕ) : ℤ) := by
          have hhZ : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
          have hih : (i : ℤ) * (h : ℤ) + ((K' - i : ℕ) : ℤ) * (h : ℤ)
              = (K' : ℤ) * (h : ℤ) := by nlinarith [hijZ]
          push_cast at hsum ⊢
          linarith
        exact cancel_mul_succ he hmul
  -- (9) the anchor term survives mod φ with exact content V
  obtain ⟨a₀, haa, ha₀ne, ha₀red⟩ := extract_content haI
  obtain ⟨b₀, hbb, hb₀ne, hb₀red⟩ := extract_content hbJ
  rw [← hα] at haa
  rw [← hβ] at hbb
  obtain ⟨y, hy⟩ := hy_dvd
  have hcKu : c K = C ((p : ℤ_[p]) ^ V) * (a₀ * b₀ + C (p : ℤ_[p]) * y) := by
    rw [hcK_split, hy, haa, hbb]
    have e1 : C ((p : ℤ_[p]) ^ α) * a₀ * (C ((p : ℤ_[p]) ^ β) * b₀)
        = C ((p : ℤ_[p]) ^ V) * (a₀ * b₀) := by
      rw [hV, pow_add, map_mul]; ring
    have e2 : (C (p : ℤ_[p])) ^ (V + 1) * y
        = C ((p : ℤ_[p]) ^ V) * (C (p : ℤ_[p]) * y) := by
      rw [← map_pow, pow_succ, map_mul]; ring
    rw [e1, e2, ← mul_add]
  set u := a₀ * b₀ + C (p : ℤ_[p]) * y with hu
  -- reduction of u is ρ(a₀)·ρ(b₀) ≠ 0 and not a multiple of φ̄
  have hρu_eq : u.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
      = a₀.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
        * b₀.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [hu, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have hpz : (PadicInt.toZMod (p : ℤ_[p]) : ZMod p) = 0 := by
      rw [map_natCast]
      exact ZMod.natCast_self p
    rw [hpz, Polynomial.C_0, zero_mul, add_zero]
  have hprime : Prime (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hirred
  have hφbar_mon : (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)).Monic := hmon.map _
  have hnodvd : ∀ z : Polynomial ℤ_[p], degree z < degree φ →
      z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) ≠ 0 →
      ¬ (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
        ∣ z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) := by
    intro z hdz hρz hdvd
    have h1 : degree (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))
        ≤ degree (z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) := degree_le_of_dvd hdvd hρz
    have h2 : degree (z.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) ≤ degree z :=
      degree_map_le
    have h3 : degree (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) = degree φ := by
      rw [degree_eq_natDegree hφbar_mon.ne_zero, degree_eq_natDegree hφ0,
        hmon.natDegree_map]
    rw [h3] at h1
    exact absurd (lt_of_le_of_lt (h1.trans h2) hdz) (lt_irrefl _)
  have hdeg_a₀ : degree a₀ < degree φ := by
    have h1 : degree (slotc φ f I) < degree φ := degree_modByMonic_lt _ hmon
    rw [haa, degree_mul, degree_C (pow_ne_zero α hp0), zero_add] at h1
    exact h1
  have hdeg_b₀ : degree b₀ < degree φ := by
    have h1 : degree (slotc φ g J) < degree φ := degree_modByMonic_lt _ hmon
    rw [hbb, degree_mul, degree_C (pow_ne_zero β hp0), zero_add] at h1
    exact h1
  have hnd_ab : ¬ (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
      ∣ (a₀.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
        * b₀.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))) := by
    intro hdvd
    rcases hprime.2.2 _ _ hdvd with hcase | hcase
    · exact hnodvd a₀ hdeg_a₀ ha₀red hcase
    · exact hnodvd b₀ hdeg_b₀ hb₀red hcase
  have hmodK_red : (u %ₘ φ).map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) ≠ 0 := by
    rw [map_modByMonic _ hmon, hρu_eq]
    intro h0
    rw [modByMonic_eq_zero_iff_dvd hφbar_mon] at h0
    exact hnd_ab h0
  have hmodK_ne : u %ₘ φ ≠ 0 := fun h0 => hmodK_red (by rw [h0, Polynomial.map_zero])
  have hmodK_gv : natGV (u %ₘ φ) = 0 := by
    rw [natGV_eq_zero_iff hmodK_ne]
    intro hdvd
    exact hmodK_red ((toZMod_poly_eq_zero_iff _).mpr hdvd)
  have hcKmod : c K %ₘ φ = C ((p : ℤ_[p]) ^ V) * (u %ₘ φ) := by
    rw [hcKu, C_mul_modByMonic]
  have hCpV_ne : (C ((p : ℤ_[p]) ^ V) : Polynomial ℤ_[p]) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact pow_ne_zero V hp0
  have hcKmod_ne : c K %ₘ φ ≠ 0 := by
    rw [hcKmod]; exact mul_ne_zero hCpV_ne hmodK_ne
  have hcKmod_gv : natGV (c K %ₘ φ) = V := by
    rw [hcKmod, natGV_mul hCpV_ne hmodK_ne, hmodK_gv, natGV_C_pow, add_zero]
  -- (10) the K-th slot of f*g has exact content V
  have hsK_ne_dvd : ¬ (C (p : ℤ_[p])) ^ (V + 1) ∣ s K := by
    intro hdvd
    have hxd : (C (p : ℤ_[p])) ^ (V + 1) ∣ c K %ₘ φ := by
      have hrew : c K %ₘ φ = s K - cpred K /ₘ φ := by rw [hsdef K]; ring
      rw [hrew]
      exact dvd_sub hdvd hextra_dvd
    have := (cpow_dvd_iff hcKmod_ne _).mp hxd
    rw [hcKmod_gv] at this
    omega
  have hsK_ne : s K ≠ 0 := fun h0 => hsK_ne_dvd (by rw [h0]; exact dvd_zero _)
  have hsK_dvd : (C (p : ℤ_[p])) ^ V ∣ s K := by
    rw [hsdef K]
    refine dvd_add ?_ (dvd_trans (pow_dvd_pow _ (by omega)) hextra_dvd)
    rw [hcKmod, ← map_pow]
    exact dvd_mul_right _ _
  have hsK_gv : natGV (s K) = V := by
    have h1 := (cpow_dvd_iff hsK_ne V).mp hsK_dvd
    have h2 : ¬ (V + 1 ≤ natGV (s K)) :=
      fun hle => hsK_ne_dvd ((cpow_dvd_iff hsK_ne _).mpr hle)
    omega
  -- (11) membership and conclusion
  have hmem : baseWeight φ e h f + baseWeight φ e h g ∈ Sw φ e h (f * g) := by
    refine ⟨K, ?_, ?_⟩
    · rw [hslot K]; exact hsK_ne
    · rw [hslot K, gaussVal_eq_natGV, hsK_gv, hwfg]
  rw [baseWeight_eq_sInf φ e h (f * g)]
  exact le_antisymm (csInf_le (Sw_bddBelow φ e h (f * g)) hmem) (le_csInf ⟨_, hmem⟩ hlb)

end LeanUrat.Moves
