/- JA-PE6 fresh leg: the GRTJA §3/§4 integer exponent system as GENERAL
   kernel-checked theorems over ℤ (route unused by PE1–PE5: no sampling,
   no interpolation, no engine — ∀-statements checked by the Lean kernel).

   Dictionary to the note (GRTJA_PROOF_2026-08-08.md at debf99d):
   - IsRes e ℓ V s  =  "s = ℓV mod e" (eq12 abscissa residue), characterized.
   - L1 res_spec / res_unique  =  eq12's s well-defined.
   - L2 master_lemma  =  PE5's coset master lemma / JA-GRID(a) integer-
     ordinate characterization: x is an integer-ordinate abscissa of the
     line hX + eY = V  ⟺  x ≡ ℓV (mod e).
   - L3 ordinate_integral  =  W2-L0 integrality (e ∣ V − s·h).
   - L4 res_least  =  JA-GRID(a): s is the least nonnegative such abscissa.
   - L5 eps_exponent  =  JA-EPS: ℓ′s − ℓu = −t, t = (ℓβ − s)/e.
   - L6 carry_clause  =  JA-GRID(c): s(V)+s(V′)−s(V+V′) = e·δ, δ ∈ {0,1},
     δ = 1 ⟺ s(V)+s(V′) ≥ e.
   - L7 cov_s / cov_t  =  the §3.2 "More generally" W2-L2 covariance display
     at the exponent layer: s(β+kW) = s(β), t(β+kW) = t(β)+kA (e ∣ W, A = ℓW/e).
   - L8 per_slot_exponent  =  THEOREM JA-RES's core: t(i) − τ = −i·A
     (Def-t(i) sign, u_i = β_i + i·W).
   - L9 orb_eps / orb_res  =  §4(iii)/(ORB-RES) orbit shifts: t ↦ t + κβ
     (ℓβ−s sign), t(i) ↦ t(i) − κu_i (Def-t(i) sign); s is ℓ-mod-e-blind
     (orbit_s_blind).
   - L10 exponent_split  =  the JA-VDIND/conjugation-form exponent split
     i·A = s₀·A + j·(e·A) on the grid i = s₀ + j·e.
   - L11 A_zero_iff  =  §1's "A_m = 0 ⟺ e_{m−1} = 1" under the normalized
     Bézout pin.
   - L12 field_step  =  the field layer of JA-RES consumes ONLY the integer
     identity (any group, any unit z).
   - L13 counter-instance (e,h,V) = (2,3,1) ⟹ u = −1 (the JA-GRID(a)
     proviso's non-vacuity witness, note §3.3). -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace JAPE6

/-- The eq12 abscissa residue, characterized: 0 ≤ s < e and s ≡ ℓV (mod e). -/
def IsRes (e ℓ V s : ℤ) : Prop := 0 ≤ s ∧ s < e ∧ e ∣ ℓ * V - s

/-- L1a: s := (ℓV) % e satisfies the characterization. -/
theorem res_spec (e ℓ V : ℤ) (he : 0 < e) : IsRes e ℓ V ((ℓ * V) % e) := by
  refine ⟨Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he,
    ⟨(ℓ * V) / e, ?_⟩⟩
  have h := Int.emod_add_ediv (ℓ * V) e
  linarith

/-- L1b: the characterization pins s uniquely (eq12's s is well-defined). -/
theorem res_unique (e ℓ V s s' : ℤ) (he : 0 < e)
    (hs : IsRes e ℓ V s) (hs' : IsRes e ℓ V s') : s = s' := by
  obtain ⟨h1, h2, k, hk⟩ := hs
  obtain ⟨h1', h2', k', hk'⟩ := hs'
  have hd : s' - s = e * (k - k') := by linear_combination hk - hk'
  have hz : k - k' = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have h9 : k - k' ≤ -1 := by omega
      nlinarith
    · have h9 : 1 ≤ k - k' := by omega
      nlinarith
  rw [hz, mul_zero] at hd
  omega

/-- L2 (the coset MASTER LEMMA = JA-GRID(a)'s integer-ordinate
    characterization): x is an abscissa with integer ordinate on
    hX + eY = V  ⟺  x ≡ ℓV (mod e), given the Bézout relation. -/
theorem master_lemma (e h ℓ ℓ' V x : ℤ) (hbez : ℓ * h + ℓ' * e = 1) :
    (∃ y, h * x + e * y = V) ↔ e ∣ x - ℓ * V := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨ℓ' * x - ℓ * y, by linear_combination ℓ * hy - x * hbez⟩
  · rintro ⟨k, hk⟩
    exact ⟨ℓ' * V - h * k, by linear_combination h * hk + V * hbez⟩

/-- L3 (= W2-L0 integrality): e divides V − s·h, so u := (V − s·h)/e ∈ ℤ. -/
theorem ordinate_integral (e h ℓ ℓ' V s : ℤ) (hbez : ℓ * h + ℓ' * e = 1)
    (hs : e ∣ ℓ * V - s) : e ∣ V - s * h := by
  obtain ⟨k, hk⟩ := hs
  exact ⟨h * k + ℓ' * V, by linear_combination h * hk - V * hbez⟩

/-- L4 (JA-GRID(a)): s is the LEAST nonnegative integer-ordinate abscissa. -/
theorem res_least (e ℓ V s x : ℤ) (he : 0 < e) (hs : IsRes e ℓ V s)
    (hx0 : 0 ≤ x) (hxd : e ∣ x - ℓ * V) : s ≤ x := by
  obtain ⟨hs0, hse, k, hk⟩ := hs
  obtain ⟨m, hm⟩ := hxd
  have hxs : x - s = e * (m + k) := by linear_combination hm + hk
  by_contra hcon
  push_neg at hcon
  have hneg : e * (m + k) < 0 := by linarith
  have hmk : m + k < 0 := by
    by_contra hnn
    push_neg at hnn
    nlinarith
  have hle : m + k ≤ -1 := by omega
  nlinarith

/-- L5 (JA-EPS): the ε-exponent ℓ′s − ℓu equals −t, t := (ℓβ − s)/e,
    at the point (s, u) on the line hs + eu = β. -/
theorem eps_exponent (e h ℓ ℓ' s u β t : ℤ) (he : e ≠ 0)
    (hbez : ℓ * h + ℓ' * e = 1) (hline : h * s + e * u = β)
    (ht : e * t = ℓ * β - s) :
    ℓ' * s - ℓ * u = -t := by
  have key : e * (ℓ' * s - ℓ * u) = e * (-t) := by
    linear_combination s * hbez - ℓ * hline + ht
  exact mul_left_cancel₀ he key

/-- L6 (JA-GRID(c), the carry clause): s(V) + s(V′) − s(V+V′) = e·δ with
    δ ∈ {0, 1}, and δ = 1 ⟺ s(V) + s(V′) ≥ e. -/
theorem carry_clause (e ℓ V V' s1 s2 s12 : ℤ) (he : 0 < e)
    (h1 : IsRes e ℓ V s1) (h2 : IsRes e ℓ V' s2)
    (h12 : IsRes e ℓ (V + V') s12) :
    (s1 + s2 - s12 = 0 ∨ s1 + s2 - s12 = e) ∧
      (s1 + s2 - s12 = e ↔ e ≤ s1 + s2) := by
  obtain ⟨a1, b1, k1, hk1⟩ := h1
  obtain ⟨a2, b2, k2, hk2⟩ := h2
  obtain ⟨a3, b3, k3, hk3⟩ := h12
  have hd : s1 + s2 - s12 = e * (k3 - k1 - k2) := by
    linear_combination -hk1 - hk2 + hk3
  set d := k3 - k1 - k2 with hdd
  have hd0 : 0 ≤ d := by
    by_contra hcon
    push_neg at hcon
    have h9 : d ≤ -1 := by omega
    nlinarith
  have hd1 : d ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h9 : 2 ≤ d := by omega
    nlinarith
  have hcases : d = 0 ∨ d = 1 := by omega
  rcases hcases with h0 | h1
  · rw [h0, mul_zero] at hd
    constructor
    · left; linarith
    · constructor
      · intro hE; omega
      · intro hge; omega
  · rw [h1, mul_one] at hd
    constructor
    · right; linarith
    · constructor
      · intro _; omega
      · intro _; omega

/-- L7a (W2-L2 covariance, s-layer): the residue is invariant under
    key-multiple weight shifts β ↦ β + kW, e ∣ W. -/
theorem cov_s (e ℓ β k W w s : ℤ) (hW : W = e * w) (hsd : e ∣ ℓ * β - s) :
    e ∣ ℓ * (β + k * W) - s := by
  obtain ⟨m, hm⟩ := hsd
  exact ⟨m + ℓ * k * w, by linear_combination hm + ℓ * k * hW⟩

/-- L7b (W2-L2 covariance, t-layer): t(β + kW) = t(β) + k·A, A := ℓW/e.
    Combined with L5 this is the §3.2 display ε(β)·z^{t-at-u} = z^{kA}. -/
theorem cov_t (e ℓ β k W w A s t t' : ℤ) (he : e ≠ 0)
    (hW : W = e * w) (hA : A = ℓ * w)
    (ht : e * t = ℓ * β - s) (ht' : e * t' = ℓ * (β + k * W) - s) :
    t' = t + k * A := by
  have key : e * t' = e * (t + k * A) := by
    linear_combination ht' - ht + ℓ * k * hW - e * k * hA
  exact mul_left_cancel₀ he key

/-- L8 (THEOREM JA-RES, the exponent core): with the Def-t(i) sign
    t = (s − ℓu)/e, τ = (s − ℓβ)/e and u = β + i·W on the line,
    t − τ = −i·A. The per-slot character law c_i = z^{−iA}·C_i is this
    identity read through L12. -/
theorem per_slot_exponent (e ℓ W w A s u β t τ i : ℤ) (he : e ≠ 0)
    (hW : W = e * w) (hA : A = ℓ * w) (hu : u = β + i * W)
    (ht : e * t = s - ℓ * u) (hτ : e * τ = s - ℓ * β) :
    t - τ = -(i * A) := by
  have key : e * (t - τ) = e * (-(i * A)) := by
    linear_combination ht - hτ - ℓ * i * hW + e * i * hA - ℓ * hu
  exact mul_left_cancel₀ he key

/-- L9a (§4(iii) ORB-EPS): under ℓ ↦ ℓ + κe the twist exponent shifts
    t ↦ t + κβ (the (ℓβ − s)/e sign). -/
theorem orb_eps (e ℓ κ β s t t' : ℤ) (he : e ≠ 0)
    (ht : e * t = ℓ * β - s) (ht' : e * t' = (ℓ + κ * e) * β - s) :
    t' = t + κ * β := by
  have key : e * t' = e * (t + κ * β) := by linear_combination ht' - ht
  exact mul_left_cancel₀ he key

/-- L9b (§4 ORB-RES): under ℓ ↦ ℓ + κe, Def-t(i) shifts t(i) ↦ t(i) − κ·u_i. -/
theorem orb_res (e ℓ κ u s t t' : ℤ) (he : e ≠ 0)
    (ht : e * t = s - ℓ * u) (ht' : e * t' = s - (ℓ + κ * e) * u) :
    t' = t - κ * u := by
  have key : e * t' = e * (t - κ * u) := by linear_combination ht' - ht
  exact mul_left_cancel₀ he key

/-- L9c (§4(iv)): s is ℓ-mod-e-blind — the κ-shift preserves the residue
    characterization, so eq12 and the carry clause are orbit-invariant. -/
theorem orbit_s_blind (e ℓ κ V s : ℤ) (hsd : e ∣ ℓ * V - s) :
    e ∣ (ℓ + κ * e) * V - s := by
  obtain ⟨m, hm⟩ := hsd
  exact ⟨m + κ * V, by linear_combination hm⟩

/-- L9d (ORB-RES grid form): on the side the ordinates step u_j = u₀ − j·h,
    so −κ·u_j = −κ·u₀ + j·(κh) — the displayed z^{−κu₀}·(z^{κh})^j. -/
theorem orb_res_grid (κ u0 h j : ℤ) : -(κ * (u0 - j * h)) = -(κ * u0) + j * (κ * h) := by
  ring

/-- L10 (JA-VDIND / conjugation form): on the grid i = s₀ + j·e the slot
    exponent splits i·A = s₀·A + j·(e·A) — the z^{−s₀A}·Q_A(ϑ y) shape,
    ϑ = z^{−eA}. -/
theorem exponent_split (s0 j e A : ℤ) :
    (s0 + j * e) * A = s0 * A + j * (e * A) := by ring

/-- L11 (§1 display): A = ℓ·g·γ = 0 ⟺ e = 1, under the normalized Bézout
    pin 0 ≤ ℓ < e and g, γ ≥ 1. -/
theorem A_zero_iff (e h ℓ ℓ' g γ : ℤ) (hbez : ℓ * h + ℓ' * e = 1)
    (hl0 : 0 ≤ ℓ) (hle : ℓ < e) (hg : 1 ≤ g) (hγ : 1 ≤ γ) :
    ℓ * g * γ = 0 ↔ e = 1 := by
  constructor
  · intro hA
    have hℓ : ℓ = 0 := by
      rcases mul_eq_zero.mp hA with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · omega
      · omega
    have he1 : ℓ' * e = 1 := by rw [hℓ] at hbez; linarith
    have hepos : 0 < e := by omega
    have hdvd : e ∣ 1 := ⟨ℓ', by linarith⟩
    have hle1 : e ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    omega
  · intro he1
    have hℓ : ℓ = 0 := by omega
    rw [hℓ]; ring

/-- L12 (the field layer of JA-RES consumes ONLY the integer identity):
    in ANY group, c = z^(t−τ)·C and t − τ = −i·A give the per-slot law. -/
theorem field_step {G : Type} [Group G] (z c C : G) {t τ i A : ℤ}
    (h : t - τ = -(i * A)) (hc : c = z ^ (t - τ) * C) :
    c = z ^ (-(i * A)) * C := by rw [hc, h]

/-- L13: the note's §3.3 counter-instance (e,h) = (2,3), V = 1:
    normalized Bézout (ℓ, ℓ′) = (1, −1); s = 1; u = (1 − 1·3)/2 = −1 < 0 —
    the JA-GRID(a) proviso is non-vacuous. -/
example : (1 * 3 + (-1) * 2 = 1) ∧ ((0:ℤ) ≤ 1 ∧ (1:ℤ) < 2) ∧
    ((1 * 1) % 2 = 1) ∧ (((1:ℤ) - 1 * 3) / 2 = -1) ∧ (((1:ℤ) - 1 * 3) / 2 < 0) := by
  norm_num

end JAPE6
