/-
Unit U30.gate_polOM  (HC-2 campaign, E-phase — blueprint §5 Layer E; FIRST-block
tripwire for U25's D.10 scale-arithmetic risk)
moves_ref: a concrete recentering node — the Case-L gate's recentering read data at
p = 2, transcribed (the P-phase pins the exact Case-L instance; the E-phase statement
pins p = 2 + species + the explicit-witness form). If even the witness instance fails
against `RecenterLiftSpec`, the scale-bookkeeping risk fires at day one, not at
escalation.  deps: D2, D3; Moves L1_base* (the base-stage construction).
difficulty: medium.  hypothesis_fields: none (axiom-free by construction).
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-!
## The witness stage (proof-layer helpers, all `private`)

The gate needs a CONCRETE proof-complete `Stage 2 (ZMod 2)` (every `Node` carries one).
We build the smallest honest one: the depth-one stage with key `Φ = X`, read index
`(e, h) = (1, 1)` (so `s = 1, t = 0`), residue field `K = ⊤ ⊆ 𝔽₂`, stage valuation

  `w f = min_j (v₂(coeff_j f) + j)`   (the weighted Gauss valuation, `w X = 1`),

and residual `R f = (image of f/2^{w f} in 𝔽₂[X]) ⊆ 𝔽₂[z^{±1}]`.  All laws are proved
through ONE mechanism: conjugation by the ring hom `G : f ↦ f.comp (C 2 * X)`, under
which `w f` becomes the exact `C 2`-divisibility exponent of `G f`, and the residual
becomes the genuine mod-2 reduction of the cofactor `Qp f := G f / C 2^{w f}` — so
multiplicativity of `w`/`R` is inherited from the DOMAIN `𝔽₂[X]`, with no graded ring.
Over `𝔽₂` every digit scalar is 1 and `t = 0` kills all position bookkeeping, which is
exactly why this instance stays small.
-/

/-! ### 1. `p = 2` scalar toolkit -/

private lemma two_nz : (2 : ℤ_[2]) ≠ 0 := by
  have h : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.prime_p
  exact_mod_cast h.ne_zero

private lemma val_two : (2 : ℤ_[2]).valuation = 1 := by
  have h := PadicInt.valuation_p (p := 2)
  simpa using h

private lemma val_two_pow (n : ℕ) : ((2 : ℤ_[2]) ^ n).valuation = n := by
  rw [PadicInt.valuation_pow, val_two, mul_one]

private lemma pow2_dvd_iff {x : ℤ_[2]} (hx : x ≠ 0) (n : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ x ↔ n ≤ x.valuation := by
  have h := Ideal.mem_span_singleton.symm.trans
    (PadicInt.mem_span_pow_iff_le_valuation x hx n)
  simpa using h

private lemma toZMod_eq_zero_iff (x : ℤ_[2]) :
    (PadicInt.toZMod x : ZMod 2) = 0 ↔ (2 : ℤ_[2]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  norm_num

/-! ### 2. The weight `w f = min_j (v₂(a_j) + j)` -/

private noncomputable def wN (f : Polynomial ℤ_[2]) : ℕ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation + i) else 0

private noncomputable def wZ (f : Polynomial ℤ_[2]) : ℤ := (wN f : ℤ)

private lemma wN_le {f : Polynomial ℤ_[2]} {i : ℕ} (hi : i ∈ f.support) :
    wN f ≤ (f.coeff i).valuation + i := by
  have hne : f.support.Nonempty := ⟨i, hi⟩
  unfold wN
  rw [dif_pos hne]
  exact Finset.inf'_le _ hi

private lemma wN_attained {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    ∃ i ∈ f.support, wN f = (f.coeff i).valuation + i := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  unfold wN
  rw [dif_pos hne]
  exact Finset.exists_mem_eq_inf' hne _

private lemma wN_C {b : ℤ_[2]} (hb : b ≠ 0) : wN (C b) = b.valuation := by
  have hCb : (C b : Polynomial ℤ_[2]) ≠ 0 := fun h => hb (Polynomial.C_eq_zero.mp h)
  obtain ⟨i, hi, hieq⟩ := wN_attained hCb
  have hi0 : i = 0 := by
    by_contra hne0
    exact (Polynomial.mem_support_iff.mp hi) (by rw [Polynomial.coeff_C, if_neg hne0])
  subst hi0
  rw [Polynomial.coeff_C_zero] at hieq
  omega

private lemma wN_X : wN (X : Polynomial ℤ_[2]) = 1 := by
  obtain ⟨i, hi, hieq⟩ := wN_attained (Polynomial.X_ne_zero (R := ℤ_[2]))
  have hi1 : i = 1 := by
    rw [Polynomial.support_X] at hi
    exact Finset.mem_singleton.mp hi
  subst hi1
  rw [Polynomial.coeff_X_one, PadicInt.valuation_one] at hieq
  omega

private lemma wZ_C {b : ℤ_[2]} (hb : b ≠ 0) : wZ (C b) = (b.valuation : ℤ) := by
  unfold wZ; rw [wN_C hb]

private lemma wZ_X : wZ (X : Polynomial ℤ_[2]) = 1 := by
  unfold wZ; rw [wN_X]; rfl

private lemma wZ_one : wZ (1 : Polynomial ℤ_[2]) = 0 := by
  rw [← Polynomial.C_1, wZ_C one_ne_zero, PadicInt.valuation_one]; rfl

/-! ### 3. The conjugation `G f = f.comp (C 2 * X)` and the divisibility bridge -/

private noncomputable def G (f : Polynomial ℤ_[2]) : Polynomial ℤ_[2] := f.comp (C 2 * X)

private lemma G_mul (f g : Polynomial ℤ_[2]) : G (f * g) = G f * G g :=
  Polynomial.mul_comp f g (C 2 * X)

private lemma G_add (f g : Polynomial ℤ_[2]) : G (f + g) = G f + G g :=
  Polynomial.add_comp

private lemma G_coeff (f : Polynomial ℤ_[2]) (n : ℕ) :
    (G f).coeff n = 2 ^ n * f.coeff n := by
  unfold G
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial i a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
        ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hni : n = i
      · subst hni; rw [if_pos rfl]; ring
      · rw [if_neg hni]; ring

/-- The bridge: `C 2^n ∣ G f` exactly captures `n ≤ w f`. -/
private lemma bridge {f : Polynomial ℤ_[2]} (hf : f ≠ 0) (n : ℕ) :
    C ((2 : ℤ_[2]) ^ n) ∣ G f ↔ n ≤ wN f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  unfold wN
  rw [dif_pos hne]
  constructor
  · intro hall
    apply Finset.le_inf'
    intro i hi
    have hci : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have h2i : (2 : ℤ_[2]) ^ i * f.coeff i ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ two_nz) hci
    have hd : (2 : ℤ_[2]) ^ n ∣ (2 : ℤ_[2]) ^ i * f.coeff i := by
      rw [← G_coeff]; exact hall i
    have hval := (pow2_dvd_iff h2i n).mp hd
    rw [PadicInt.valuation_mul (pow_ne_zero _ two_nz) hci, val_two_pow] at hval
    omega
  · intro hle i
    by_cases hi : i ∈ f.support
    · have hci : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
      have h2i : (2 : ℤ_[2]) ^ i * f.coeff i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ two_nz) hci
      rw [G_coeff]
      refine (pow2_dvd_iff h2i n).mpr ?_
      rw [PadicInt.valuation_mul (pow_ne_zero _ two_nz) hci, val_two_pow]
      have hinf := Finset.inf'_le (fun j => (f.coeff j).valuation + j) hi
      omega
    · have hz : f.coeff i = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hi
      rw [G_coeff, hz, mul_zero]
      exact dvd_zero _

private lemma Cpow_ne (m : ℕ) : (C ((2 : ℤ_[2]) ^ m) : Polynomial ℤ_[2]) ≠ 0 :=
  fun hC => pow_ne_zero m two_nz (Polynomial.C_eq_zero.mp hC)

/-! ### 4. The cofactor `Qp f` (exact division of `G f` by `C 2^{w f}`) -/

private lemma cpow_wN_dvd {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    C ((2 : ℤ_[2]) ^ wN f) ∣ G f := (bridge hf _).mpr le_rfl

open scoped Classical in
private noncomputable def Qp (f : Polynomial ℤ_[2]) : Polynomial ℤ_[2] :=
  if h : C ((2 : ℤ_[2]) ^ wN f) ∣ G f then h.choose else 0

private lemma Qp_spec {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    G f = C ((2 : ℤ_[2]) ^ wN f) * Qp f := by
  unfold Qp
  rw [dif_pos (cpow_wN_dvd hf)]
  exact (cpow_wN_dvd hf).choose_spec

/-- Exactness: the cofactor is not divisible by `C 2` (the minimum is attained). -/
private lemma Qp_not_dvd {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    ¬ C (2 : ℤ_[2]) ∣ Qp f := by
  rintro ⟨Q', hQ'⟩
  have hd : C ((2 : ℤ_[2]) ^ (wN f + 1)) ∣ G f := by
    refine ⟨Q', ?_⟩
    rw [Qp_spec hf, hQ', pow_succ, Polynomial.C_mul]
    ring
  have := (bridge hf _).mp hd
  omega

private lemma C2_dvd_iff (Q : Polynomial ℤ_[2]) :
    C (2 : ℤ_[2]) ∣ Q ↔ Q.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) = 0 := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro hall
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (toZMod_eq_zero_iff _).mpr (hall n)
  · intro h n
    rw [← toZMod_eq_zero_iff]
    have := congrArg (fun q => Polynomial.coeff q n) h
    simpa [Polynomial.coeff_map] using this

/-! ### 5. The weight laws (multiplicative, ultrametric) via the bridge -/

private lemma wN_mul {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) :
    wN (f * g) = wN f + wN g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have h1 : C ((2 : ℤ_[2]) ^ (wN f + wN g)) ∣ G (f * g) := by
    refine ⟨Qp f * Qp g, ?_⟩
    rw [G_mul, Qp_spec hf, Qp_spec hg, pow_add, Polynomial.C_mul]
    ring
  have h2 : ¬ (wN f + wN g + 1 ≤ wN (f * g)) := by
    intro hh
    have hd : C ((2 : ℤ_[2]) ^ (wN f + wN g + 1)) ∣ G (f * g) := (bridge hfg _).mpr hh
    rw [G_mul, Qp_spec hf, Qp_spec hg] at hd
    have hre : C ((2 : ℤ_[2]) ^ wN f) * Qp f * (C ((2 : ℤ_[2]) ^ wN g) * Qp g)
        = C ((2 : ℤ_[2]) ^ (wN f + wN g)) * (Qp f * Qp g) := by
      rw [pow_add, Polynomial.C_mul]; ring
    rw [hre, pow_succ, Polynomial.C_mul] at hd
    have hC2 : C (2 : ℤ_[2]) ∣ Qp f * Qp g :=
      (mul_dvd_mul_iff_left (Cpow_ne (wN f + wN g))).mp hd
    have hmap := (C2_dvd_iff _).mp hC2
    rw [Polynomial.map_mul] at hmap
    rcases mul_eq_zero.mp hmap with h | h
    · exact Qp_not_dvd hf ((C2_dvd_iff _).mpr h)
    · exact Qp_not_dvd hg ((C2_dvd_iff _).mpr h)
  have h3 := (bridge hfg _).mp h1
  omega

private lemma wN_min_le_add {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (wN f) (wN g) ≤ wN (f + g) := by
  refine (bridge hfg _).mp ?_
  have h1 : C ((2 : ℤ_[2]) ^ min (wN f) (wN g)) ∣ G f :=
    (bridge hf _).mpr (min_le_left _ _)
  have h2 : C ((2 : ℤ_[2]) ^ min (wN f) (wN g)) ∣ G g :=
    (bridge hg _).mpr (min_le_right _ _)
  rw [G_add]
  exact dvd_add h1 h2

private lemma wN_add_left {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (hlt : wN f < wN g) : wN (f + g) = wN f := by
  have h1 : min (wN f) (wN g) ≤ wN (f + g) := wN_min_le_add hf hg hfg
  have h2 : ¬ (wN f + 1 ≤ wN (f + g)) := by
    intro hh
    have hd : C ((2 : ℤ_[2]) ^ (wN f + 1)) ∣ G (f + g) := (bridge hfg _).mpr hh
    have hdg : C ((2 : ℤ_[2]) ^ (wN f + 1)) ∣ G g := (bridge hg _).mpr (by omega)
    have hdf : C ((2 : ℤ_[2]) ^ (wN f + 1)) ∣ G f := by
      have heq : G f = G (f + g) - G g := by rw [G_add]; ring
      rw [heq]
      exact dvd_sub hd hdg
    have := (bridge hf _).mp hdf
    omega
  omega

/-! ### 6. The residue apparatus: `𝔽₂[X] → 𝔽₂[z^{±1}]` over `K = ⊤ ⊆ 𝔽₂` -/

private abbrev KK : Subfield (ZMod 2) := ⊤

private noncomputable def ι : ZMod 2 →+* ↥KK :=
  ((Subfield.topEquiv : (⊤ : Subfield (ZMod 2)) ≃+* ZMod 2).symm :
    ZMod 2 ≃+* ↥(⊤ : Subfield (ZMod 2))).toRingHom

private noncomputable def Ψ : Polynomial (ZMod 2) →+* LaurentPolynomial ↥KK :=
  (Polynomial.toLaurent (R := ↥KK)).comp (Polynomial.mapRingHom ι)

private lemma Ψ_inj : Function.Injective Ψ := fun _ _ hab =>
  Polynomial.map_injective ι ι.injective (Polynomial.toLaurent_injective hab)

private noncomputable def red (f : Polynomial ℤ_[2]) : Polynomial (ZMod 2) :=
  (Qp f).map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)

private lemma red_ne {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : red f ≠ 0 :=
  fun h => Qp_not_dvd hf ((C2_dvd_iff _).mpr h)

open scoped Classical in
private noncomputable def Rmap (f : Polynomial ℤ_[2]) : LaurentPolynomial ↥KK :=
  if f = 0 then 0 else Ψ (red f)

private lemma Rmap_zero : Rmap 0 = 0 := by unfold Rmap; rw [if_pos rfl]

private lemma Rmap_of_ne {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : Rmap f = Ψ (red f) := by
  unfold Rmap; rw [if_neg hf]

private lemma Rmap_ne {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : Rmap f ≠ 0 := by
  rw [Rmap_of_ne hf]
  intro h
  exact red_ne hf (Ψ_inj (h.trans (map_zero Ψ).symm))

private lemma Qp_mul {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) :
    Qp (f * g) = Qp f * Qp g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  apply mul_left_cancel₀ (Cpow_ne (wN (f * g)))
  rw [← Qp_spec hfg, G_mul, Qp_spec hf, Qp_spec hg, wN_mul hf hg, pow_add, Polynomial.C_mul]
  ring

private lemma Rmap_mul {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) :
    Rmap (f * g) = Rmap f * Rmap g := by
  rw [Rmap_of_ne (mul_ne_zero hf hg), Rmap_of_ne hf, Rmap_of_ne hg]
  unfold red
  rw [Qp_mul hf hg, Polynomial.map_mul, map_mul]

private lemma Qp_add {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hgw : wN g = wN f) (hw : wN (f + g) = wN f) : Qp (f + g) = Qp f + Qp g := by
  apply mul_left_cancel₀ (Cpow_ne (wN (f + g)))
  rw [← Qp_spec hfg, G_add, Qp_spec hf, Qp_spec hg, hgw, hw, mul_add]

private lemma Rmap_add {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hgw : wN g = wN f) (hw : wN (f + g) = wN f) : Rmap (f + g) = Rmap f + Rmap g := by
  rw [Rmap_of_ne hfg, Rmap_of_ne hf, Rmap_of_ne hg]
  unfold red
  rw [Qp_add hf hg hfg hgw hw, Polynomial.map_add, map_add]

private lemma red_add_left {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (hlt : wN f < wN g) : red (f + g) = red f := by
  have hw : wN (f + g) = wN f := wN_add_left hf hg hfg hlt
  have hkey : Qp (f + g) = Qp f + C ((2 : ℤ_[2]) ^ (wN g - wN f)) * Qp g := by
    apply mul_left_cancel₀ (Cpow_ne (wN (f + g)))
    rw [← Qp_spec hfg, G_add, Qp_spec hf, Qp_spec hg, hw, mul_add, ← mul_assoc,
      ← Polynomial.C_mul, ← pow_add, show wN f + (wN g - wN f) = wN g from by omega]
  unfold red
  rw [hkey, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  have h0 : (PadicInt.toZMod ((2 : ℤ_[2]) ^ (wN g - wN f)) : ZMod 2) = 0 := by
    rw [map_pow]
    have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := (toZMod_eq_zero_iff _).mpr dvd_rfl
    rw [h2, zero_pow (by omega : wN g - wN f ≠ 0)]
  rw [h0, Polynomial.C_0, zero_mul, add_zero]

/-! ### 7. The concrete residuals `R X = z`, `R (C b) = 1` -/

private lemma Qp_X : Qp (X : Polynomial ℤ_[2]) = X := by
  apply mul_left_cancel₀ (Cpow_ne (wN (X : Polynomial ℤ_[2])))
  rw [← Qp_spec (Polynomial.X_ne_zero (R := ℤ_[2])), wN_X, pow_one]
  change (X : Polynomial ℤ_[2]).comp (C 2 * X) = C 2 * X
  exact Polynomial.X_comp

private lemma Rmap_X : Rmap (X : Polynomial ℤ_[2]) = LaurentPolynomial.T 1 := by
  rw [Rmap_of_ne (Polynomial.X_ne_zero (R := ℤ_[2]))]
  unfold red
  rw [Qp_X, Polynomial.map_X]
  unfold Ψ
  rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.toLaurent_X]

private lemma Qp_C {b : ℤ_[2]} (hb : b ≠ 0) :
    ∃ q : ℤ_[2], Qp (C b) = C q ∧ (PadicInt.toZMod q : ZMod 2) = 1 := by
  have hCb : (C b : Polynomial ℤ_[2]) ≠ 0 := fun h => hb (Polynomial.C_eq_zero.mp h)
  have hspec := Qp_spec hCb
  have hGC : G (C b) = C b := Polynomial.C_comp
  rw [hGC] at hspec
  have hdeg : (Qp (C b)).degree ≤ 0 := by
    have hd := congrArg Polynomial.degree hspec
    rw [Polynomial.degree_C hb, Polynomial.degree_mul,
      Polynomial.degree_C (pow_ne_zero _ two_nz), zero_add] at hd
    exact le_of_eq hd.symm
  refine ⟨(Qp (C b)).coeff 0, Polynomial.eq_C_of_degree_le_zero hdeg, ?_⟩
  have hnd := Qp_not_dvd hCb
  have hq0 : (PadicInt.toZMod ((Qp (C b)).coeff 0) : ZMod 2) ≠ 0 := by
    intro h0
    apply hnd
    have h2q : (2 : ℤ_[2]) ∣ (Qp (C b)).coeff 0 := (toZMod_eq_zero_iff _).mp h0
    have := map_dvd (C : ℤ_[2] →+* Polynomial ℤ_[2]) h2q
    rwa [← Polynomial.eq_C_of_degree_le_zero hdeg] at this
  have hall : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  exact hall _ hq0

private lemma Rmap_C {b : ℤ_[2]} (hb : b ≠ 0) : Rmap (C b) = 1 := by
  have hCb : (C b : Polynomial ℤ_[2]) ≠ 0 := fun h => hb (Polynomial.C_eq_zero.mp h)
  obtain ⟨q, hq, hq1⟩ := Qp_C hb
  rw [Rmap_of_ne hCb]
  unfold red
  rw [hq, Polynomial.map_C, hq1, Polynomial.C_1, map_one]

/-! ### 8. Small residue-field facts over `K = ⊤ ⊆ 𝔽₂` -/

private lemma subK_eq_one {x : ↥KK} (hx : x ≠ 0) : x = 1 := by
  have hall : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hv : (x : ZMod 2) ≠ 0 := fun h => hx (by apply Subtype.ext; simpa using h)
  apply Subtype.ext
  simpa using hall _ hv

private lemma deg_le_zero_of_lt_X {B : Polynomial ℤ_[2]}
    (h : B.degree < (X : Polynomial ℤ_[2]).degree) : B.degree ≤ 0 := by
  rw [Polynomial.degree_X] at h
  exact Nat.WithBot.lt_one_iff_le_zero.mp h

/-! ### 9. Lemma K1 at the key `X` -/

private lemma K1 : K1At wZ (X : Polynomial ℤ_[2]) (wZ (X : Polynomial ℤ_[2])) := by
  intro f B N hf hdev
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hBC : ∀ j, B j = C ((B j).coeff 0) := fun j =>
    Polynomial.eq_C_of_degree_le_zero (deg_le_zero_of_lt_X (hdeg j))
  have hcoeff : ∀ k, k < N → f.coeff k = (B k).coeff 0 := by
    intro k hk
    rw [hsum, Polynomial.finsetSum_coeff]
    have hterm : ∀ j ∈ Finset.range N,
        (B j * X ^ j).coeff k = if k = j then (B j).coeff 0 else 0 := by
      intro j _
      conv_lhs => rw [hBC j]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hkj : k = j
      · rw [if_pos hkj, if_pos hkj, mul_one]
      · rw [if_neg hkj, if_neg hkj, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Finset.range N) k,
      if_pos (Finset.mem_range.mpr hk)]
  have hcoeff0 : ∀ k, N ≤ k → f.coeff k = 0 := by
    intro k hk
    rw [hsum, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j hj
    conv_lhs => rw [hBC j]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hkj
    have := Finset.mem_range.mp hj
    omega
  constructor
  · intro j hjN hBj
    have hbj : (B j).coeff 0 ≠ 0 := fun h => hBj (by rw [hBC j, h, Polynomial.C_0])
    have hsupp : j ∈ f.support :=
      Polynomial.mem_support_iff.mpr (by rw [hcoeff j hjN]; exact hbj)
    have hle := wN_le hsupp
    rw [hcoeff j hjN] at hle
    change wZ f ≤ wZ (B j) + (j : ℤ) * wZ (X : Polynomial ℤ_[2])
    rw [wZ_X, hBC j, wZ_C hbj]
    unfold wZ
    omega
  · obtain ⟨i, hi, hieq⟩ := wN_attained hf
    have hiN : i < N := by
      by_contra hge
      exact (Polynomial.mem_support_iff.mp hi) (hcoeff0 i (by omega))
    have hbi : (B i).coeff 0 ≠ 0 := by
      rw [← hcoeff i hiN]; exact Polynomial.mem_support_iff.mp hi
    refine ⟨i, hiN, fun h => hbi (by rw [h, Polynomial.coeff_zero]), ?_⟩
    change wZ f = wZ (B i) + (i : ℤ) * wZ (X : Polynomial ℤ_[2])
    rw [wZ_X, hBC i, wZ_C hbi]
    rw [hcoeff i hiN] at hieq
    unfold wZ
    omega

/-! ### 10. The witness stage `σ₀ : Stage 2 (ZMod 2)` -/

private noncomputable def σ₀ : Stage 2 (ZMod 2) where
  e := 1
  h := 1
  s := 1
  t := 0
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  he1t := fun _ => rfl
  Φ := X
  hmonic := Polynomial.monic_X
  hdeg := Polynomial.natDegree_X.ge
  w := wZ
  wPrev := wZ
  K := KK
  FQ := KK
  hFQ_le := le_refl _
  R := Rmap
  hwmul := by
    intro f g hf hg
    unfold wZ
    exact_mod_cast wN_mul hf hg
  hwult := by
    intro f g hf hg hfg
    unfold wZ
    exact_mod_cast wN_min_le_add hf hg hfg
  hvalgrp := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[2], f ≠ 0 ∧ g ≠ 0 ∧ wZ f - wZ g = n} :=
      ⟨X, 1, Polynomial.X_ne_zero, one_ne_zero, by rw [wZ_X, wZ_one, sub_zero]⟩
    have hmem := AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure h1) n
    simpa using hmem
  hwΦ := by rw [wZ_X]; rfl
  hStretch := by
    intro B hB hBC
    rw [Nat.cast_one, one_mul]
  hR0 := Rmap_zero
  hRne := fun f hf => Rmap_ne hf
  hRmul := fun f g hf hg => Rmap_mul hf hg
  hRadd := by
    intro f g hf hg hfg hwfg hsum
    unfold wZ at hwfg hsum
    refine Rmap_add hf hg hfg ?_ ?_
    · exact_mod_cast hwfg.symm
    · exact_mod_cast hsum
  hRlt := by
    intro f g hf hg hfg hlt
    unfold wZ at hlt
    have hltN : wN f < wN g := by exact_mod_cast hlt
    rw [Rmap_of_ne hfg, Rmap_of_ne hf]
    exact congrArg Ψ (red_add_left hf hg hfg hltN)
  hRΦ := Rmap_X
  hK1 := K1
  hS5 := by
    intro B hB hBc
    refine ⟨1, ?_⟩
    have hb : B = C (B.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (deg_le_zero_of_lt_X hBc)
    have hb0 : B.coeff 0 ≠ 0 := fun h => hB (by rw [hb, h, Polynomial.C_0])
    rw [hb, Rmap_C hb0]
    simp [LaurentPolynomial.T_zero]
  reps := []
  hreps := by intro ũ h; exact absurd h (List.not_mem_nil)
  Tvec := []
  hTvec := rfl
  weightSet := {ν : ℤ | ∃ B : Polynomial ℤ_[2], B ≠ 0 ∧ inC (X : Polynomial ℤ_[2]) B ∧ wZ B = ν}
  hWS := fun B hB hBc => ⟨B, hB, hBc, rfl⟩
  hS6a := by
    rintro ν ⟨B, hB, hBc, hBw⟩
    refine ⟨1, fun c _ => ⟨B, hB, hBc, hBw, ?_⟩⟩
    have hb : B = C (B.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (deg_le_zero_of_lt_X hBc)
    have hb0 : B.coeff 0 ≠ 0 := fun h => hB (by rw [hb, h, Polynomial.C_0])
    have hc1 : ((c * 1 : (↥KK)ˣ) : ↥KK) = 1 := subK_eq_one (c * 1).ne_zero
    rw [hb, Rmap_C hb0, hc1]
    simp [LaurentPolynomial.T_zero]
  hS6b := by
    intro ν a hν
    rw [wZ_X] at hν
    refine ⟨C ((2 : ℤ_[2]) ^ ν.toNat), ?_, ?_, ?_, ?_⟩
    · exact fun h => pow_ne_zero _ two_nz (Polynomial.C_eq_zero.mp h)
    · change (C ((2 : ℤ_[2]) ^ ν.toNat)).degree < (X : Polynomial ℤ_[2]).degree
      rw [Polynomial.degree_X]
      exact Polynomial.degree_C_lt
    · rw [wZ_C (pow_ne_zero _ two_nz), val_two_pow]
      omega
    · have ha1 : (a : ↥KK) = 1 := subK_eq_one a.ne_zero
      rw [Rmap_C (pow_ne_zero _ two_nz), ha1]
      simp [LaurentPolynomial.T_zero]

/-! ### 11. The witness node `ν₀` (species = recentering) -/

private noncomputable def ν₀ : Node 2 (ZMod 2) where
  species := ReadSpecies.recentering
  σ := σ₀
  e := 1
  h := 1
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 1
  line := ⟨0, 0⟩
  ustar := 0
  gam := 0
  zbar := 1
  center := 1
  lift := C 2
  ψ := X - C 1
  pat := fun _ => 1
  Ranch := X - C 1
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := ⟨le_refl 0, by norm_num⟩
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := ⟨1, rfl⟩
  hDwidth := Polynomial.natDegree_X.symm
  hψmonic := Polynomial.monic_X_sub_C 1
  hψdeg := Polynomial.natDegree_X_sub_C 1
  hψirr := Polynomial.irreducible_X_sub_C 1
  hRanch := by
    have h2 : (1 : ↥σ₀.K) + 1 = 0 := by
      apply Subtype.ext
      simpa using (by decide : (1 : ZMod 2) + 1 = 0)
    have hP : (1 : Polynomial ↥σ₀.K) + 1 = 0 := by
      have hC := congrArg (Polynomial.C (R := ↥σ₀.K)) h2
      simpa [map_add, map_one, map_zero] using hC
    rw [show (1 / 1 + 1 : ℕ) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Polynomial.C_1, pow_zero, pow_one, mul_one, one_mul]
    linear_combination -hP
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by simp [Line.at]
  hOrd := by
    constructor
    · rw [pow_one]
    · intro hdvd
      have hne : (X - C (1 : ↥KK)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
      have hd := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hd
      omega
  hzbarRoot := by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X]
  hspecInc := fun hcontra => nomatch hcontra
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, by simp⟩

/-! ### 12. The explicit witness lift `t_L = C 2` -/

private lemma spec_C2 : RecenterLiftSpec ν₀ (C (2 : ℤ_[2])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (C (2 : ℤ_[2])).degree < (X : Polynomial ℤ_[2]).degree
    rw [Polynomial.degree_X]
    exact Polynomial.degree_C_lt
  · exact fun hC => two_nz (Polynomial.C_eq_zero.mp hC)
  · show wZ (C (2 : ℤ_[2])) = wZ X
    rw [wZ_C two_nz, val_two, wZ_X]
    rfl
  · exact (by rw [Rmap_C two_nz, LaurentPolynomial.T_zero, map_one, mul_one] :
      Rmap (C (2 : ℤ_[2])) = LaurentPolynomial.C (1 : ↥KK) * LaurentPolynomial.T 0)

/-- GATE: a concrete recentering node at p = 2 on which the recentering-lift spec is
realized by EXPLICIT WITNESS — polOM's totality instantiated once, axiom-free. -/
theorem gate_polOM :
    ∃ ν : Node 2 (ZMod 2), ν.species = ReadSpecies.recentering ∧
      (∃ tL : Polynomial ℤ_[2], RecenterLiftSpec ν tL) ∧
      RecenterLiftSpec ν ((polOM 2 (ZMod 2)).liftOf ν) := by
  have hex : ∃ tL : Polynomial ℤ_[2], RecenterLiftSpec ν₀ tL := ⟨C 2, spec_C2⟩
  refine ⟨ν₀, rfl, hex, ?_⟩
  have hlift : (polOM 2 (ZMod 2)).liftOf ν₀ = hex.choose := by
    unfold polOM
    exact dif_pos hex
  rw [hlift]
  exact hex.choose_spec

end LeanUrat.MovesJ
