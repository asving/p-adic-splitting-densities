/- GRTW2 PE5 fresh leg — the note's integer-exponent system as KERNEL-CHECKED
   ∀-theorems (route unused by PE1–PE4: Lean kernel; no sampling, no pool).
   Covers: W2-L0 grid tie (congruence + least-abscissa), W2-L2 mismatch
   identity with its two integrality warrants + element form, the §1.1
   normalized-Bézout facts (ℓ = 0 ⟺ e = 1; A_m ≥ 0; A_m = 0 ⟺ e = 1),
   the §1.3/§2.1 slot-weight tie V_j = β_j, the §3.3(a) s = 0 warrant,
   the §3.4 m = 1 closed-form tie ξ = c₁^{e₁}, the LEMMA W2-ID1 exponent
   chain, and the PE3 counter-instance pins (every unit of ANY 4-element
   field satisfies the y³+c orbit equation; F₃ skeleton z⁴ = 1, z^(−13) = z;
   I4B integer skeleton γ₂ = A₂ = 13, A₁ = 4). -/
import Mathlib

namespace W2PE5

/-- W2-L0 (grid tie, congruence half): with ℓ a Bézout inverse of h mod e,
    x·h ≡ V (mod e)  ⟺  x ≡ ℓ·V (mod e). -/
theorem L0_grid_congr (e ℓ h V x : ℤ) (hbez : e ∣ (ℓ*h - 1)) :
    e ∣ (x*h - V) ↔ e ∣ (x - ℓ*V) := by
  constructor <;> intro hd
  · have hx : x - ℓ*V = ℓ*(x*h - V) - x*(ℓ*h - 1) := by ring
    rw [hx]; exact dvd_sub (hd.mul_left ℓ) (hbez.mul_left x)
  · have hx : x*h - V = h*(x - ℓ*V) + V*(ℓ*h - 1) := by ring
    rw [hx]; exact dvd_add (hd.mul_left h) (hbez.mul_left V)

/-- W2-L0 (least-abscissa half): s := (ℓV) mod e is nonnegative, < e, solves
    s·h ≡ V (mod e), and is ≤ every nonnegative solution. -/
theorem L0_least_abscissa (e ℓ h V : ℤ) (he : 0 < e) (hbez : e ∣ (ℓ*h - 1)) :
    0 ≤ (ℓ*V) % e ∧ (ℓ*V) % e < e ∧ e ∣ (((ℓ*V) % e)*h - V) ∧
    ∀ x, 0 ≤ x → e ∣ (x*h - V) → (ℓ*V) % e ≤ x := by
  refine ⟨Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he, ?_, ?_⟩
  · rw [L0_grid_congr e ℓ h V _ hbez]
    have h1 : e * (ℓ*V / e) + (ℓ*V) % e = ℓ*V := Int.ediv_add_emod _ _
    exact ⟨-(ℓ*V/e), by rw [mul_neg]; linarith⟩
  · intro x hx hsol
    have hcong : e ∣ (x - ℓ*V) := (L0_grid_congr e ℓ h V x hbez).mp hsol
    have hmod : x % e = (ℓ*V) % e := Int.ModEq.symm (Int.modEq_iff_dvd.mpr hcong)
    have hdiv : 0 ≤ x / e := Int.ediv_nonneg hx (le_of_lt he)
    have hsplit : e * (x / e) + x % e = x := Int.ediv_add_emod x e
    nlinarith [mul_nonneg (le_of_lt he) hdiv]

/-- W2-L2 integrality warrant 1: e ∣ V − s·h whenever s ≡ ℓV (mod e). -/
theorem L2_warrant1 (e ℓ ℓ' h V s : ℤ) (hbez : ℓ*h + ℓ'*e = 1)
    (hs : e ∣ (s - ℓ*V)) : e ∣ (V - s*h) := by
  have hx : V - s*h = (-h)*(s - ℓ*V) + (V*ℓ')*e := by linear_combination (-V)*hbez
  rw [hx]; exact dvd_add (hs.mul_left (-h)) (dvd_mul_left e (V*ℓ'))

/-- W2-L2 integrality warrant 2: e ∣ ℓu − s when u = V + kW, W ∈ eℤ. -/
theorem L2_warrant2 (e ℓ V u k W' s : ℤ) (hu : u = V + k*(e*W'))
    (hs : e ∣ (s - ℓ*V)) : e ∣ (ℓ*u - s) := by
  have hx : ℓ*u - s = -(s - ℓ*V) + e*(ℓ*k*W') := by rw [hu]; ring
  rw [hx]; exact dvd_add (dvd_neg.mpr hs) ⟨ℓ*k*W', rfl⟩

/-- W2-L2 (THE MISMATCH IDENTITY): T + (ℓ′s − ℓu′) = ℓ(u−V)/e = (ℓW/e)·k,
    stated with the exact-division witnesses. -/
theorem L2_mismatch (e ℓ ℓ' h V u k W' s x y : ℤ) (he : e ≠ 0)
    (hbez : ℓ*h + ℓ'*e = 1) (hu : u = V + k*(e*W'))
    (hx : V - s*h = e*x)      -- u′ = x, the exact division
    (hy : ℓ*u - s = e*y)      -- T  = y, the exact division
    : y + (ℓ'*s - ℓ*x) = ℓ*W'*k := by
  have key : e*(y + (ℓ'*s - ℓ*x)) = e*(ℓ*W'*k) := by linear_combination (-1)*hy + ℓ*hu + ℓ*hx + s*hbez
  exact mul_left_cancel₀ he key

/-- W2-L2 element form: ε(V)·z^T = z^{A·k} with A = ℓW/e = ℓ·g·γ
    (junction use: W = e·g·γ, so W' = g·γ and ℓW' = A). -/
theorem L2_element_form {G : Type*} [CommGroup G] (z : G)
    (e ℓ ℓ' h V u k gγ s x y : ℤ) (he : e ≠ 0)
    (hbez : ℓ*h + ℓ'*e = 1) (hu : u = V + k*(e*gγ))
    (hx : V - s*h = e*x) (hy : ℓ*u - s = e*y) :
    z^(ℓ'*s - ℓ*x) * z^y = z^((ℓ*gγ)*k) := by
  rw [← zpow_add]
  congr 1
  have := L2_mismatch e ℓ ℓ' h V u k gγ s x y he hbez hu hx hy
  linarith

/-- §1.1 normalized Bézout: with 0 ≤ ℓ < e and ℓh + ℓ′e = 1, ℓ = 0 ⟺ e = 1. -/
theorem bezout_ell_zero_iff (e ℓ ℓ' h : ℤ) (he : 1 ≤ e) (h0 : 0 ≤ ℓ)
    (hlt : ℓ < e) (hbez : ℓ*h + ℓ'*e = 1) : ℓ = 0 ↔ e = 1 := by
  constructor
  · intro hl
    have hd : e ∣ 1 := ⟨ℓ', by rw [hl] at hbez; linarith [mul_comm e ℓ']⟩
    have := Int.le_of_dvd one_pos hd
    omega
  · intro he1; omega

/-- §1.3: A_m = ℓ·g·γ ≥ 0 and A_m = 0 ⟺ e = 1 (given g, γ ≥ 1). -/
theorem A_nonneg_and_zero_iff (e ℓ ℓ' h g γ : ℤ) (he : 1 ≤ e) (h0 : 0 ≤ ℓ)
    (hlt : ℓ < e) (hbez : ℓ*h + ℓ'*e = 1) (hg : 1 ≤ g) (hγ : 1 ≤ γ) :
    0 ≤ ℓ*g*γ ∧ (ℓ*g*γ = 0 ↔ e = 1) := by
  constructor
  · positivity
  · rw [← bezout_ell_zero_iff e ℓ ℓ' h he h0 hlt hbez]
    constructor
    · intro hA
      rcases mul_eq_zero.mp hA with h1 | h2
      · rcases mul_eq_zero.mp h1 with h3 | h4
        · exact h3
        · omega
      · omega
    · intro hl; rw [hl]; ring

/-- §2.1 slot-weight tie (W2-L0 "Consequently"): V_j = u_j − j·e·W equals
    β_j = (g−j)·γ under the weight recursion γ = e·W + h. -/
theorem slot_weight_tie (g j h e W γ : ℤ) (hγ : γ = e*W + h) :
    (g*γ - j*h) - j*(e*W) = (g - j)*γ := by subst hγ; ring

/-- §3.3(a) warrant: the top junction has s = 0 because e ∣ V. -/
theorem top_slot_s_zero (e ℓ V : ℤ) (hV : e ∣ V) : (ℓ*V) % e = 0 :=
  Int.emod_eq_zero_of_dvd (hV.mul_left ℓ)

/-- §3.4 m = 1 tie: ξ = z^{−e·A} = (z^{−A})^e = c₁^{e} — the covariance is
    Thm-phir's constant to the ramification. -/
theorem m1_xi_is_c1_pow {G : Type*} [CommGroup G] (z : G) (e A : ℤ) :
    z^(-(e*A)) = (z^(-A))^e := by
  rw [← zpow_mul]; ring_nf

/-- LEMMA W2-ID1 exponent chain (the group algebra of the proof): if
    c = ξ^g and z^{Ae} = ξ⁻¹ and ξ^g = 1 and ξ^j = 1 (support triviality),
    then c·z^{Ae·j} = 1 — §3.4 rk. 3's m = 1 byte law. -/
theorem id1_chain {G : Type*} [CommGroup G] (ξ zAe : G) (g j : ℤ)
    (hz : zAe = ξ⁻¹) (hg : ξ^g = 1) (hj : ξ^j = 1) :
    ξ^g * zAe^j = 1 := by
  rw [hz, inv_zpow, hg, hj]; simp

/-- W2-ID1 w-forcing at j = 0: ψ(0) ≠ 0 and w·ψ(0) = ψ(0) force w = 1. -/
theorem id1_w_forcing {F : Type*} [Field F] (w a : F) (ha : a ≠ 0)
    (hw : w * a = a) : w = 1 := by
  field_simp at hw; exact hw

/-- PE3 counter-instance pin 1: in ANY field with exactly 4 elements, every
    nonzero x satisfies x³ = 1 (so EVERY unit satisfies the orbit equations
    of ψ₁ = y³ + ζ — the whole of F₄* is the ambiguity set). -/
theorem four_field_cube (F : Type*) [Field F] [Fintype F]
    (h4 : Fintype.card F = 4) (x : F) (hx : x ≠ 0) : x^3 = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one x hx
  rw [h4] at this; norm_num at this; exact this

/-- PE3 counter-instance pin 2: for any unit ξ with ξ³ = 1 the conjugated
    modulus is byte-identical: (ξy)³ + c = y³ + c for every y. -/
theorem orbit_eq_all_units {F : Type*} [Field F] (ξ c y : F) (h3 : ξ^3 = 1) :
    (ξ*y)^3 + c = y^3 + c := by
  have : (ξ*y)^3 = ξ^3 * y^3 := by ring
  rw [this, h3, one_mul]

/-- I4B §3.5 integer skeleton (reads (3,2,1),(2,1,1),(1,1,2),(2,1,1)):
    ℓ₀ = 2, ℓ₁ = 1 are the normalized Bézout representatives; γ₂ = 13,
    A₁ = 4, A₂ = 13 — the note's bracket figures. -/
theorem i4b_skeleton :
    (2*2) % 3 = 1 ∧ (1*1) % 2 = 1 ∧          -- ℓ₀ = 2 (e₀=3,h₀=2), ℓ₁ = 1 (e₁=2,h₁=1)
    (2:ℤ)*(3*1*2) + 1 = 13 ∧                 -- γ₂ = e₁·w₁Φ₁ + h₁, w₁Φ₁ = e₀g₀γ₁ = 6
    (2:ℤ)*1*2 = 4 ∧                          -- A₁ = ℓ₀·g₀·γ₁
    (1:ℤ)*1*13 = 13 := by                    -- A₂ = ℓ₁·g₁·γ₂
  norm_num

/-- I4B §3.5 character skeleton: in the residue field F₃ every unit z has
    z² = 1, hence χ₂ = z₁⁴ = 1 and ξ₃ = z₂^{−13} = z₂ (= −1 on I4B). -/
theorem i4b_character {G : Type*} [CommGroup G] (z1 z2 : G)
    (h1 : z1^(2:ℤ) = 1) (h2 : z2^(2:ℤ) = 1) :
    z1^(4:ℤ) = 1 ∧ z2^(-13:ℤ) = z2 := by
  constructor
  · have : z1^(4:ℤ) = (z1^(2:ℤ))^(2:ℤ) := by rw [← zpow_mul]; norm_num
    rw [this, h1, one_zpow]
  · have : z2^(-13:ℤ) = (z2^(2:ℤ))^(-7:ℤ) * z2 := by
      rw [← zpow_mul, ← zpow_add_one]; norm_num
    rw [this, h2, one_zpow, one_mul]

end W2PE5

#print axioms W2PE5.L0_least_abscissa
#print axioms W2PE5.L2_mismatch
#print axioms W2PE5.L2_element_form
#print axioms W2PE5.A_nonneg_and_zero_iff
#print axioms W2PE5.id1_chain
#print axioms W2PE5.four_field_cube
#print axioms W2PE5.i4b_character
