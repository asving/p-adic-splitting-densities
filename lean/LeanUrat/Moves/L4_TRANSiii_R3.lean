import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L4_TRANSi_R3

/-!
# Moves/L4_TRANSiii — D.7(iii): `w'` is a valuation (multiplicativity)  [ROUND 3]

`moves_ref`: D.7(iii) w' is a valuation (gr_{w'} a domain); MOVES ~2196-2201.

`w'(fg) = w'(f) + w'(g)` for the next-stage slot-minimum weight `w'` at the lifted key `Φ̂`
under (I-aug).  The `≥` leg is dep `L4.TRANSi` (imported unit).  The `≤` leg is proved here by
the extremal-index argument: pick the LARGEST minimizing slots `j₀` (for `f`) and `k₀` (for `g`),
build the `Φ̂`-development of `f·g` by convolution + monic division, and observe that in slot
`j₀+k₀` the anchor remainder `R̃_{j₀k₀} = (B_{j₀}B''_{k₀}) %ₘ Φ̂` — whose weight is EXACTLY
`w(B_{j₀}) + w(B''_{k₀})` and which is nonzero, both by Lemma DIV (imported unit `L3.DIV`) — is
w-dominant: every other same-diagonal remainder is strictly deeper (extremal choice of `j₀,k₀`),
and every carried quotient from diagonal `j₀+k₀−1` is strictly deeper by (I-aug)
(`h' > e'·w(Φ̂)`).  Hence the slot has slot-weight exactly `w'f + w'g`, giving `≤` through the
`IsSlotMinWeight` lower-bound clause.  The `e' = 0` degenerate side is absorbed by the integer
arithmetic (the strict inequalities force `e' ≥ 1` whenever a competing term is nonzero).

Deps used: `L4.TRANSi` (`≥`, imported, its core is that unit's obligation), `L3.DIV` (exact
remainder weight + nonvanishing, imported, its core is that unit's obligation), `L3.liftMonic`
(degree of `Φ̂`, fully proved on disk), `L0.FactA_exists` (developments exist, fully proved on
disk).  `L3.K1`-transcendence is NOT needed on this route: development slots separate the
minimizing diagonals, and the extremal choice makes the minimizing pair unique in its slot.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

section TRANSiiiHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`: from `w(1·1) = w 1 + w 1`. -/
private lemma wiii_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w(−f) = w(f)` for `f ≠ 0`. -/
private lemma wiii_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.w (-f) = σ.w f := by
  have hne : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) hne hne
    rw [neg_mul_neg, one_mul] at h
    have h1 := wiii_one σ
    omega
  have h := σ.hwmul (-1) f hne hf
  rw [neg_one_mul] at h
  omega

/-- Ultrametric finite-sum lower bound (zeros allowed among the summands). -/
private lemma wiii_sum_ge (σ : Stage p F) {ι : Type*} (S : Finset ι)
    (a : ι → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro hm hsum
    simp at hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ σ.w (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ σ.w (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        exact le_trans (le_min h1 h2) (σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum)

/-- Two "zero or w-deeper than `b`" elements add to a "zero or w-deeper than `b`" element. -/
private lemma wiii_deep_or (σ : Stage p F) {x y : Polynomial ℤ_[p]} {b : ℤ}
    (hx : x = 0 ∨ b < σ.w x) (hy : y = 0 ∨ b < σ.w y) :
    x + y = 0 ∨ b < σ.w (x + y) := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]; exact hy
  · by_cases hy0 : y = 0
    · rw [hy0, add_zero]; exact hx
    · by_cases hxy : x + y = 0
      · exact Or.inl hxy
      · right
        have hbx : b < σ.w x := hx.resolve_left hx0
        have hby : b < σ.w y := hy.resolve_left hy0
        exact lt_of_lt_of_le (lt_min hbx hby) (σ.hwult x y hx0 hy0 hxy)

/-- Finite-sum version of `wiii_deep_or`. -/
private lemma wiii_sum_deep (σ : Stage p F) {ι : Type*} (S : Finset ι)
    (a : ι → Polynomial ℤ_[p]) (b : ℤ)
    (h : ∀ j ∈ S, a j = 0 ∨ b < σ.w (a j)) :
    (∑ j ∈ S, a j) = 0 ∨ b < σ.w (∑ j ∈ S, a j) := by
  classical
  revert h
  induction S using Finset.induction with
  | empty => intro h; simp
  | insert i T hiT ih =>
    intro h
    rw [Finset.sum_insert hiT]
    exact wiii_deep_or σ (h i (Finset.mem_insert_self i T))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Dominant-term lemma: adding a strictly w-deeper (or zero) term preserves nonvanishing and
the w-value. -/
private lemma wiii_dominant (σ : Stage p F) {x y : Polynomial ℤ_[p]}
    (hx : x ≠ 0) (hy : y = 0 ∨ σ.w x < σ.w y) :
    x + y ≠ 0 ∧ σ.w (x + y) = σ.w x := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]; exact ⟨hx, rfl⟩
  · have hyw : σ.w x < σ.w y := hy.resolve_left hy0
    have hxy : x + y ≠ 0 := by
      intro h
      have hyx : y = -x := eq_neg_of_add_eq_zero_right h
      rw [hyx, wiii_neg σ x hx] at hyw
      omega
    refine ⟨hxy, le_antisymm ?_ ?_⟩
    · by_contra hcon
      have hcon' : σ.w x < σ.w (x + y) := not_le.mp hcon
      have hns : x + y + -y ≠ 0 := by rw [add_neg_cancel_right]; exact hx
      have h2 := σ.hwult (x + y) (-y) hxy (neg_ne_zero.mpr hy0) hns
      rw [add_neg_cancel_right, wiii_neg σ y hy0] at h2
      exact absurd h2 (not_le.mpr (lt_min hcon' hyw))
    · calc σ.w x = min (σ.w x) (σ.w y) := (min_eq_left hyw.le).symm
        _ ≤ σ.w (x + y) := σ.hwult x y hx hy0 hxy

/-- `%ₘ` is additive (monic divisor), by uniqueness of monic division. -/
private lemma wiii_add_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic)
    (a b : Polynomial ℤ_[p]) :
    (a + b) %ₘ q = a %ₘ q + b %ₘ q := by
  have ha := Polynomial.modByMonic_add_div a q
  have hb := Polynomial.modByMonic_add_div b q
  refine (Polynomial.div_modByMonic_unique (a /ₘ q + b /ₘ q) (a %ₘ q + b %ₘ q) hq
    ⟨?_, ?_⟩).2
  · linear_combination ha + hb
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (Polynomial.degree_modByMonic_lt a hq) (Polynomial.degree_modByMonic_lt b hq))

/-- `%ₘ` distributes over finite sums (monic divisor). -/
private lemma wiii_sum_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic) {ι : Type*}
    (S : Finset ι) (a : ι → Polynomial ℤ_[p]) :
    (∑ j ∈ S, a j) %ₘ q = ∑ j ∈ S, (a j %ₘ q) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i T hiT ih =>
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT, wiii_add_modByMonic hq, ih]

end TRANSiiiHelpers

theorem L4_TRANSiii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : Φhat.Monic) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (hcop : Nat.gcd e' h' = 1) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' (f * gg) = w' f + w' gg := by
  classical
  -- ===== the `≥` leg is dep L4.TRANSi (imported unit) =====
  have hge : w' f + w' gg ≤ w' (f * gg) :=
    L4_TRANSi σ ψ g Φhat hlift hψ hψz zbar hzbar e' h' w' hw' hiaug f gg hf hg hfg
  refine le_antisymm ?_ hge
  -- ===== basic data =====
  have hψmon : ψ.Monic := hlift.1
  have hψdeg : ψ.natDegree = g := hlift.2.1
  have hg1 : 1 ≤ g := by
    by_contra hcon
    have hg0 : g = 0 := by omega
    have hψ0 : ψ.natDegree = 0 := by rw [hψdeg, hg0]
    have hψ1 : ψ = 1 := (Polynomial.Monic.natDegree_eq_zero hψmon).mp hψ0
    exact hψ.not_isUnit (hψ1 ▸ isUnit_one)
  have hΦd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree := (L3_liftMonic σ ψ g hg1 Φhat hlift).2
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hdpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hd1 : 1 ≤ Φhat.natDegree := by omega
  have hiaug' : (e' : ℤ) * σ.w Φhat < (h' : ℤ) := hiaug
  -- ===== developments of f and gg (dep L0.FactA, proved on disk) =====
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists Φhat hmon hd1 gg
  have hBfdeg : ∀ j, (Bf j).degree < Φhat.degree := hdevf.1
  have hBfz : ∀ j, Nf ≤ j → Bf j = 0 := hdevf.2.1
  have hfsum : f = ∑ j ∈ Finset.range Nf, Bf j * Φhat ^ j := hdevf.2.2
  have hBgdeg : ∀ k, (Bg k).degree < Φhat.degree := hdevg.1
  have hBgz : ∀ k, Ng ≤ k → Bg k = 0 := hdevg.2.1
  have hgsum : gg = ∑ k ∈ Finset.range Ng, Bg k * Φhat ^ k := hdevg.2.2
  have hNf1 : 1 ≤ Nf := by
    by_contra hcon
    have h0 : Nf = 0 := by omega
    rw [h0] at hfsum
    simp only [Finset.range_zero, Finset.sum_empty] at hfsum
    exact hf hfsum
  have hNg1 : 1 ≤ Ng := by
    by_contra hcon
    have h0 : Ng = 0 := by omega
    rw [h0] at hgsum
    simp only [Finset.range_zero, Finset.sum_empty] at hgsum
    exact hg hgsum
  -- ===== slot-min data for f and gg =====
  obtain ⟨hminf, jat, hjatNf, hjatnz, hjateq⟩ := hw' f Bf Nf hf hdevf
  obtain ⟨hming, kat, hkatNg, hkatnz, hkateq⟩ := hw' gg Bg Ng hg hdevg
  -- ===== the LARGEST attaining indices j₀, k₀ =====
  set sf : Finset ℕ := (Finset.range Nf).filter
    (fun j => Bf j ≠ 0 ∧ w' f = (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)) with hsf
  have hsfne : sf.Nonempty := ⟨jat, by
    simp only [hsf, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjatNf, hjatnz, hjateq⟩⟩
  set j₀ := sf.max' hsfne with hj₀def
  have hj₀mem : j₀ ∈ sf := sf.max'_mem hsfne
  have hj₀all : j₀ < Nf ∧ Bf j₀ ≠ 0 ∧ w' f = (e' : ℤ) * σ.w (Bf j₀) + (j₀ : ℤ) * (h' : ℤ) := by
    have h := hj₀mem
    simp only [hsf, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  obtain ⟨hj₀Nf, hj₀nz, hj₀eq⟩ := hj₀all
  have hstrictf : ∀ j, j < Nf → Bf j ≠ 0 → j₀ < j →
      w' f < (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    intro j hjN hjnz hgt
    rcases lt_or_eq_of_le (hminf j hjN hjnz) with h | h
    · exact h
    · exfalso
      have hmemj : j ∈ sf := by
        simp only [hsf, Finset.mem_filter, Finset.mem_range]
        exact ⟨hjN, hjnz, h⟩
      exact absurd (Finset.le_max' sf j hmemj) (not_le.mpr hgt)
  set sg : Finset ℕ := (Finset.range Ng).filter
    (fun k => Bg k ≠ 0 ∧ w' gg = (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ)) with hsg
  have hsgne : sg.Nonempty := ⟨kat, by
    simp only [hsg, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkatNg, hkatnz, hkateq⟩⟩
  set k₀ := sg.max' hsgne with hk₀def
  have hk₀mem : k₀ ∈ sg := sg.max'_mem hsgne
  have hk₀all : k₀ < Ng ∧ Bg k₀ ≠ 0 ∧ w' gg = (e' : ℤ) * σ.w (Bg k₀) + (k₀ : ℤ) * (h' : ℤ) := by
    have h := hk₀mem
    simp only [hsg, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  obtain ⟨hk₀Ng, hk₀nz, hk₀eq⟩ := hk₀all
  have hstrictg : ∀ k, k < Ng → Bg k ≠ 0 → k₀ < k →
      w' gg < (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) := by
    intro k hkN hknz hgt
    rcases lt_or_eq_of_le (hming k hkN hknz) with h | h
    · exact h
    · exfalso
      have hmemk : k ∈ sg := by
        simp only [hsg, Finset.mem_filter, Finset.mem_range]
        exact ⟨hkN, hknz, h⟩
      exact absurd (Finset.le_max' sg k hmemk) (not_le.mpr hgt)
  -- ===== generating polynomials and the convolution =====
  set FF : Polynomial (Polynomial ℤ_[p]) :=
    ∑ j ∈ Finset.range Nf, Polynomial.C (Bf j) * Polynomial.X ^ j with hFFdef
  set GG : Polynomial (Polynomial ℤ_[p]) :=
    ∑ k ∈ Finset.range Ng, Polynomial.C (Bg k) * Polynomial.X ^ k with hGGdef
  have hFFc : ∀ m, FF.coeff m = Bf m := by
    intro m
    rw [hFFdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Nf
    · rw [Finset.sum_eq_single m]
      · simp
      · intro j hj hjm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBfz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro j hj
      have hmj : m ≠ j := by
        have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmj]
  have hGGc : ∀ m, GG.coeff m = Bg m := by
    intro m
    rw [hGGdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Ng
    · rw [Finset.sum_eq_single m]
      · simp
      · intro k hk hkm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hkm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBgz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro k hk
      have hmk : m ≠ k := by
        have := Finset.mem_range.mp hk; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmk]
  have hFFeval : Polynomial.eval Φhat FF = f := by
    rw [hFFdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hfsum.symm
  have hGGeval : Polynomial.eval Φhat GG = gg := by
    rw [hGGdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hgsum.symm
  have hFFnd : FF.natDegree ≤ Nf - 1 := by
    rw [hFFdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hj
    omega
  have hGGnd : GG.natDegree ≤ Ng - 1 := by
    rw [hGGdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hk
    omega
  set H : Polynomial (Polynomial ℤ_[p]) := FF * GG with hHdef
  have hHnd : H.natDegree ≤ Nf + Ng - 2 := by
    rw [hHdef]
    refine le_trans Polynomial.natDegree_mul_le ?_
    omega
  have hHcoeff : ∀ m, H.coeff m = ∑ jk ∈ Finset.antidiagonal m, Bf jk.1 * Bg jk.2 := by
    intro m
    rw [hHdef, Polynomial.coeff_mul]
    exact Finset.sum_congr rfl (fun jk _ => by rw [hFFc, hGGc])
  have hHvan : ∀ m, Nf + Ng - 1 ≤ m → H.coeff m = 0 := by
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hprodsum : f * gg = ∑ m ∈ Finset.range (Nf + Ng), H.coeff m * Φhat ^ m := by
    rw [← hFFeval, ← hGGeval, ← Polynomial.eval_mul, ← hHdef]
    exact Polynomial.eval_eq_sum_range' (by omega) Φhat
  -- ===== the development of f·gg: remainders on the diagonal, carried quotients shifted =====
  set Cdev : ℕ → Polynomial ℤ_[p] := fun m =>
    H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) with hCdef
  have hCdev_eq : ∀ m, Cdev m
      = H.coeff m %ₘ Φhat + (if m = 0 then 0 else H.coeff (m - 1) /ₘ Φhat) := fun m => rfl
  have hBfnd : ∀ j, (Bf j).natDegree ≤ Φhat.natDegree - 1 := by
    intro j
    by_cases hz : Bf j = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hBfdeg j)
      omega
  have hBgnd : ∀ k, (Bg k).natDegree ≤ Φhat.natDegree - 1 := by
    intro k
    by_cases hz : Bg k = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hBgdeg k)
      omega
  have hHcnd : ∀ m, (H.coeff m).natDegree ≤ 2 * Φhat.natDegree - 2 := by
    intro m
    rw [hHcoeff m]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro jk hjk
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hBfnd jk.1
    have h2 := hBgnd jk.2
    omega
  have hQdeg : ∀ m, (H.coeff m /ₘ Φhat).degree < Φhat.degree := by
    intro m
    have hnd : (H.coeff m /ₘ Φhat).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_divByMonic _ hmon]
      have h2 := hHcnd m
      omega
    calc (H.coeff m /ₘ Φhat).degree
        ≤ ((H.coeff m /ₘ Φhat).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (Φhat.natDegree : WithBot ℕ) := by exact_mod_cast hnd
      _ = Φhat.degree := (Polynomial.degree_eq_natDegree hΦne).symm
  have hCdeg : ∀ m, (Cdev m).degree < Φhat.degree := by
    intro m
    rw [hCdev_eq m]
    by_cases hm : m = 0
    · rw [if_pos hm, add_zero]
      exact Polynomial.degree_modByMonic_lt _ hmon
    · rw [if_neg hm]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact Polynomial.degree_modByMonic_lt _ hmon
      · exact hQdeg (m - 1)
  have hCvan : ∀ m, Nf + Ng ≤ m → Cdev m = 0 := by
    intro m hm
    rw [hCdev_eq m]
    have hm0 : m ≠ 0 := by omega
    rw [if_neg hm0, hHvan m (by omega), hHvan (m - 1) (by omega),
      Polynomial.zero_modByMonic, Polynomial.zero_divByMonic, add_zero]
  have hCsum : f * gg = ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, Nf + Ng = N₁ + 1 := ⟨Nf + Ng - 1, by omega⟩
    have hz2 : H.coeff N₁ = 0 := hHvan N₁ (by omega)
    have hsplit : ∀ m, Cdev m * Φhat ^ m
        = (H.coeff m %ₘ Φhat) * Φhat ^ m
          + (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      intro m
      rw [hCdev_eq m]
      by_cases hm : m = 0
      · simp only [if_pos hm]
        rw [add_zero, add_zero]
      · simp only [if_neg hm]
        rw [add_mul]
    have hshift : (∑ m ∈ Finset.range (Nf + Ng),
          (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m))
        = ∑ m ∈ Finset.range (Nf + Ng), (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1) := by
      rw [hN₁]
      rw [Finset.sum_range_succ'
        (fun m => if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) N₁]
      rw [Finset.sum_range_succ (fun m => (H.coeff m /ₘ Φhat) * Φhat ^ (m + 1)) N₁]
      rw [if_pos rfl, add_zero, hz2, Polynomial.zero_divByMonic, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    rw [hprodsum]
    have e1 : ∑ m ∈ Finset.range (Nf + Ng), Cdev m * Φhat ^ m
        = (∑ m ∈ Finset.range (Nf + Ng), (H.coeff m %ₘ Φhat) * Φhat ^ m)
          + ∑ m ∈ Finset.range (Nf + Ng),
              (if m = 0 then 0 else (H.coeff (m - 1) /ₘ Φhat) * Φhat ^ m) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => hsplit m)
    rw [e1, hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    conv_lhs => rw [← Polynomial.modByMonic_add_div (H.coeff m) Φhat]
    ring
  have hdevC : IsDevelopment Φhat (f * gg) Cdev (Nf + Ng) := ⟨hCdeg, hCvan, hCsum⟩
  obtain ⟨hminC, -⟩ := hw' (f * gg) Cdev (Nf + Ng) hfg hdevC
  -- ===== Lemma DIV wrapper (dep L3.DIV, imported unit) =====
  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
      B.degree < Φhat.degree → B''.degree < Φhat.degree →
      (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'' := by
    intro B B'' hB hB'' hBd hB''d
    have hBd' : B.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB hBd
    have hB''d' : B''.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦd]; exact Polynomial.natDegree_lt_natDegree hB'' hB''d
    have hRd' : ((B * B'') %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
      by_cases hz : (B * B'') %ₘ Φhat = 0
      · rw [hz]; simpa using hdpos
      · rw [← hΦd]
        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hmon)
    have hdiv : B * B'' = ((B * B'') /ₘ Φhat) * Φhat + (B * B'') %ₘ Φhat := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div (B * B'') Φhat]
      ring
    have hd := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd' hB''d'
      ((B * B'') %ₘ Φhat) ((B * B'') /ₘ Φhat) hdiv hRd'
    exact ⟨hd.1, hd.2.1⟩
  -- ===== the anchor slot j₀ + k₀ =====
  set β : ℤ := σ.w (Bf j₀) + σ.w (Bg k₀) with hβdef
  obtain ⟨hx_ne, hx_w⟩ := hDIVw (Bf j₀) (Bg k₀) hj₀nz hk₀nz (hBfdeg j₀) (hBgdeg k₀)
  have hx_wβ : σ.w ((Bf j₀ * Bg k₀) %ₘ Φhat) = β := by rw [hx_w]
  have hμν : w' f + w' gg = (e' : ℤ) * β + ((j₀ : ℤ) + (k₀ : ℤ)) * (h' : ℤ) := by
    rw [hj₀eq, hk₀eq, hβdef]; ring
  -- deep bound for the OTHER remainders on the diagonal (extremal-index strictness)
  have hdeepR : ∀ jk ∈ (Finset.antidiagonal (j₀ + k₀)).erase (j₀, k₀),
      (Bf jk.1 * Bg jk.2) %ₘ Φhat = 0 ∨ β < σ.w ((Bf jk.1 * Bg jk.2) %ₘ Φhat) := by
    intro jk hjk
    rw [Finset.mem_erase, Finset.mem_antidiagonal] at hjk
    obtain ⟨hne, hdiag⟩ := hjk
    by_cases hz : (Bf jk.1 * Bg jk.2) %ₘ Φhat = 0
    · exact Or.inl hz
    right
    have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
      intro h0; rw [h0, Polynomial.zero_modByMonic] at hz; exact hz rfl
    have hBfne : Bf jk.1 ≠ 0 := left_ne_zero_of_mul hPne
    have hBgne : Bg jk.2 ≠ 0 := right_ne_zero_of_mul hPne
    have hjNf : jk.1 < Nf := by
      by_contra hcon; exact hBfne (hBfz jk.1 (not_lt.mp hcon))
    have hkNg : jk.2 < Ng := by
      by_contra hcon; exact hBgne (hBgz jk.2 (not_lt.mp hcon))
    have h1 : w' f ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBfne
    have h2 : w' gg ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBgne
    have hstrict : w' f + w' gg < (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ)
        + ((e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ)) := by
      rcases Nat.lt_or_ge j₀ jk.1 with hgt | hle
      · have hs := hstrictf jk.1 hjNf hBfne hgt
        linarith
      · have hkgt : k₀ < jk.2 := by
          rcases Nat.lt_or_ge jk.1 j₀ with hlt2 | hge2
          · omega
          · have hj_eq : jk.1 = j₀ := le_antisymm hle hge2
            have hk_eq : jk.2 = k₀ := by omega
            exact absurd (Prod.ext hj_eq hk_eq) hne
        have hs := hstrictg jk.2 hkNg hBgne hkgt
        linarith
    have hw_eq : σ.w ((Bf jk.1 * Bg jk.2) %ₘ Φhat) = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
      (hDIVw (Bf jk.1) (Bg jk.2) hBfne hBgne (hBfdeg jk.1) (hBgdeg jk.2)).2
    rw [hw_eq]
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ)
        = ((j₀ : ℤ) + (k₀ : ℤ)) * (h' : ℤ) := by
      have hc : (jk.1 : ℤ) + (jk.2 : ℤ) = (j₀ : ℤ) + (k₀ : ℤ) := by exact_mod_cast hdiag
      rw [← add_mul, hc]
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hlt : (e' : ℤ) * β < (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) := by
      linarith
    have hepos : (0 : ℤ) < (e' : ℤ) := by
      rcases Nat.eq_zero_or_pos e' with he0 | hp
      · exfalso; rw [he0] at hlt; simp at hlt
      · exact_mod_cast hp
    exact lt_of_mul_lt_mul_left hlt hepos.le
  -- deep bound for the carried quotient from diagonal j₀ + k₀ − 1 (uses (I-aug))
  have hdeepQ : ∀ m', m' + 1 = j₀ + k₀ →
      (H.coeff m' /ₘ Φhat = 0 ∨ β < σ.w (H.coeff m' /ₘ Φhat)) := by
    intro m' hm'
    by_cases hy : H.coeff m' /ₘ Φhat = 0
    · exact Or.inl hy
    right
    have hbound : ∀ jk ∈ Finset.antidiagonal m', Bf jk.1 * Bg jk.2 = 0 ∨
        β + σ.w Φhat + 1 ≤ σ.w (Bf jk.1 * Bg jk.2) := by
      intro jk hjk
      rw [Finset.mem_antidiagonal] at hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · exact Or.inl hPz
      right
      have hBfne : Bf jk.1 ≠ 0 := left_ne_zero_of_mul hPz
      have hBgne : Bg jk.2 ≠ 0 := right_ne_zero_of_mul hPz
      have hjNf : jk.1 < Nf := by
        by_contra hcon; exact hBfne (hBfz jk.1 (not_lt.mp hcon))
      have hkNg : jk.2 < Ng := by
        by_contra hcon; exact hBgne (hBgz jk.2 (not_lt.mp hcon))
      have h1 : w' f ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBfne
      have h2 : w' gg ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBgne
      have hwP : σ.w (Bf jk.1 * Bg jk.2) = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
        σ.hwmul _ _ hBfne hBgne
      have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) + (h' : ℤ)
          = ((j₀ : ℤ) + (k₀ : ℤ)) * (h' : ℤ) := by
        have hc : (jk.1 : ℤ) + (jk.2 : ℤ) + 1 = (j₀ : ℤ) + (k₀ : ℤ) := by
          exact_mod_cast (by omega : jk.1 + jk.2 + 1 = j₀ + k₀)
        rw [← hc]; ring
      have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
          = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
      have hkey : (e' : ℤ) * β + (h' : ℤ) ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) := by
        linarith
      rw [hwP]
      by_contra hcon
      have hle : σ.w (Bf jk.1) + σ.w (Bg jk.2) ≤ β + σ.w Φhat := by omega
      have hmul : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) ≤ (e' : ℤ) * (β + σ.w Φhat) :=
        mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg e')
      have hexp2 : (e' : ℤ) * (β + σ.w Φhat) = (e' : ℤ) * β + (e' : ℤ) * σ.w Φhat := by ring
      linarith
    have hconvm' : H.coeff m' ≠ 0 := by
      intro h0; rw [h0, Polynomial.zero_divByMonic] at hy; exact hy rfl
    have hwconv : β + σ.w Φhat + 1 ≤ σ.w (H.coeff m') := by
      rw [hHcoeff m']
      refine wiii_sum_ge σ _ _ _ (fun jk hjk hne0 => (hbound jk hjk).resolve_left hne0) ?_
      rw [← hHcoeff m']; exact hconvm'
    have hyΦ : Φhat * (H.coeff m' /ₘ Φhat) = H.coeff m' + -(H.coeff m' %ₘ Φhat) := by
      have hmd := Polynomial.modByMonic_add_div (H.coeff m') Φhat
      linear_combination hmd
    have hΦyne : Φhat * (H.coeff m' /ₘ Φhat) ≠ 0 := mul_ne_zero hΦne hy
    have hwΦy : β + σ.w Φhat + 1 ≤ σ.w (Φhat * (H.coeff m' /ₘ Φhat)) := by
      rw [hyΦ]
      by_cases hrz : H.coeff m' %ₘ Φhat = 0
      · rw [hrz, neg_zero, add_zero]; exact hwconv
      · have hrw : β + σ.w Φhat + 1 ≤ σ.w (H.coeff m' %ₘ Φhat) := by
          have hremsum : H.coeff m' %ₘ Φhat
              = ∑ jk ∈ Finset.antidiagonal m', (Bf jk.1 * Bg jk.2) %ₘ Φhat := by
            rw [hHcoeff m']
            exact wiii_sum_modByMonic hmon _ _
          rw [hremsum]
          refine wiii_sum_ge σ _ _ _ ?_ (by rw [← hremsum]; exact hrz)
          intro jk hjk hne0
          have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
            intro h0; rw [h0, Polynomial.zero_modByMonic] at hne0; exact hne0 rfl
          have hBfne : Bf jk.1 ≠ 0 := left_ne_zero_of_mul hPne
          have hBgne : Bg jk.2 ≠ 0 := right_ne_zero_of_mul hPne
          have hw_eq : σ.w ((Bf jk.1 * Bg jk.2) %ₘ Φhat)
              = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
            (hDIVw (Bf jk.1) (Bg jk.2) hBfne hBgne (hBfdeg jk.1) (hBgdeg jk.2)).2
          rw [hw_eq]
          have hb := (hbound jk hjk).resolve_left hPne
          rw [σ.hwmul _ _ hBfne hBgne] at hb
          exact hb
        have hnegne : -(H.coeff m' %ₘ Φhat) ≠ 0 := neg_ne_zero.mpr hrz
        have hsumne : H.coeff m' + -(H.coeff m' %ₘ Φhat) ≠ 0 := by
          rw [← hyΦ]; exact hΦyne
        have hult := σ.hwult _ _ hconvm' hnegne hsumne
        rw [wiii_neg σ _ hrz] at hult
        exact le_trans (le_min hwconv hrw) hult
    have hmulw := σ.hwmul Φhat (H.coeff m' /ₘ Φhat) hΦne hy
    rw [hmulw] at hwΦy
    linarith
  -- ===== assemble the anchor slot and conclude =====
  have hmem : (j₀, k₀) ∈ Finset.antidiagonal (j₀ + k₀) := Finset.mem_antidiagonal.mpr rfl
  have hCm₀ : Cdev (j₀ + k₀) = (Bf j₀ * Bg k₀) %ₘ Φhat
      + ((∑ jk ∈ (Finset.antidiagonal (j₀ + k₀)).erase (j₀, k₀), (Bf jk.1 * Bg jk.2) %ₘ Φhat)
        + (if j₀ + k₀ = 0 then 0 else H.coeff (j₀ + k₀ - 1) /ₘ Φhat)) := by
    rw [hCdev_eq (j₀ + k₀)]
    have hrem : H.coeff (j₀ + k₀) %ₘ Φhat
        = (∑ jk ∈ (Finset.antidiagonal (j₀ + k₀)).erase (j₀, k₀), (Bf jk.1 * Bg jk.2) %ₘ Φhat)
          + (Bf j₀ * Bg k₀) %ₘ Φhat := by
      rw [hHcoeff, wiii_sum_modByMonic hmon]
      exact (Finset.sum_erase_add _ _ hmem).symm
    rw [hrem]
    ring
  have hdeep_sum := wiii_sum_deep σ ((Finset.antidiagonal (j₀ + k₀)).erase (j₀, k₀))
    (fun jk => (Bf jk.1 * Bg jk.2) %ₘ Φhat) β hdeepR
  have hdeep_q : (if j₀ + k₀ = 0 then 0 else H.coeff (j₀ + k₀ - 1) /ₘ Φhat) = 0
      ∨ β < σ.w (if j₀ + k₀ = 0 then 0 else H.coeff (j₀ + k₀ - 1) /ₘ Φhat) := by
    by_cases hm0 : j₀ + k₀ = 0
    · rw [if_pos hm0]; exact Or.inl rfl
    · rw [if_neg hm0]
      exact hdeepQ (j₀ + k₀ - 1) (by omega)
  have hdeep := wiii_deep_or σ hdeep_sum hdeep_q
  have hdom := wiii_dominant σ hx_ne (by
    rcases hdeep with h0 | hw
    · exact Or.inl h0
    · right; rw [hx_wβ]; exact hw)
  obtain ⟨hCne, hCw⟩ := hdom
  rw [← hCm₀] at hCne hCw
  have hm₀N : j₀ + k₀ < Nf + Ng := by omega
  have hslot : w' (f * gg) ≤ (e' : ℤ) * σ.w (Cdev (j₀ + k₀)) + ((j₀ + k₀ : ℕ) : ℤ) * (h' : ℤ) :=
    hminC (j₀ + k₀) hm₀N hCne
  rw [hCw, hx_wβ] at hslot
  -- hslot : w'(f·gg) ≤ e'·β + (j₀+k₀)·h'
  have hcast : ((j₀ + k₀ : ℕ) : ℤ) = (j₀ : ℤ) + (k₀ : ℤ) := by push_cast; ring
  rw [hcast] at hslot
  linarith [hslot, hμν]

end LeanUrat.Moves
