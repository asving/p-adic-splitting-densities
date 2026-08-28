/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C51
import Uniformity.ChapC.C118a
import Uniformity.ChapC.C130s6
import Uniformity.ChapC.C131aa
import Uniformity.ChapC.C133mh0
import Uniformity.ChapC.C150rb4

/-!
# Uniformity.ChapC.C150rb5 — A-C.23: the repaired `refine_invariants`, as a THEOREM

**Unit A23E (2026-08-28), amendment A-C.23.**  RB3R (`runs/wave-c/verdict_RB3R.md` §2,
codex-confirmed 5/5; support theorems `C150rb4.lean`) proved that the signed C.56(i)
conclusion's `IsTestKey` conjunct is a STATEMENT-LEVEL OVERCLAIM of the source clause
`EFF.GENTOW1.28`: the corrected key `Φ₂⁺ = composedKey T - k2DigitLift T s lam` genuinely
carries the lift's own digits at `F.key`-abscissae `towerSolve u₂ e₂ lam + e₂·t` — off the
exact-zero lattice whenever `e₂ ∤ lam` — so conjuncts 4/5a of `IsTestKey` are not implied
by the hypotheses (and are false under the faithful `k2Coord` reading).  The source claims
only the PERTURBATION-STABLE package: monic of degree `D₂`, level-1 development one-sided
of slope `κ₂ = u₂/e₂` with residual `ψ₂` and side reads byte-unchanged.  That package is
exactly what the dv-graded Hensel engine's M4 perturbation law (`C133mh0.dv_pure_add_of_lt`,
MH.6) preserves — and this file PROVES it, discharging the re-signed C.56(i) with no axiom.

## The theorem

`refine_invariants` (root namespace, the A-C.23 re-signed statement): under the signed
premises (byte-identical to the pre-amendment axiom, leanspec `ChapC.lean:2163`; the
`f`-side hypotheses are deliberately unused — the signed conclusion never mentioned `f`),
the corrected key `Φ₂⁺` is monic of degree `T.D₂`, has top `F.key`-digit `1`, is
`IsDvPure` at `(T.u₂, T.e₂)`, and its side data is byte-unchanged: pinned height
`T.f₂ * T.u₂` at the side minimum and level residual polynomial `towerLabel T` — i.e.
`composedKey T`'s own pinned data (C.47 + C131aa `dvResPoly_testKey`).

## The one new ingredient: the lift's grade floor

`dvSupp_k2DigitLift_ge`: every term of `k2DigitLift T s lam` sits at cleared level grade
exactly `lam`, so `dvSupp F (k2DigitLift T s lam) T.u₂ T.e₂ ≥ lam > T.E₂` — the M4 input.
The exactness of the `n2Exp` exponent solve (`e₁e₂a₀ + ie₂h + bu₂ = M`, no ℕ-truncation)
is the `EFF.GENTOW1.27` `a₀ ≥ 0` audit inequality, closed here from the node floor
`T.hfloor` (`u₂ > e₂·e₁f₁·h`): `towerSolve_mod_eq` (the solve's congruence succeeds on a
coprime pair), `n2Exp_grade_eq_of_le` (the exact grade equation at live heights), and the
per-monomial `dvSupp` floor through `stageHeight`'s coefficient valuations.  The floor is
choice-robust: only `π^{a₀} ∣ coefficient` is consumed, never the `k2Coord` values.

## DEPENDS

C133mh0 (MH.6 `dv_pure_add_of_lt`) · C47 (`composedKey_isTestKey/_monic/_natDegree`) ·
C131aa (`isTestKey_isDvPure`, `dvResPoly_testKey`) · C150rb4 (`towerSolve_lt`,
`n2Exp_snd_*`, `natDegree_k2DigitLift_lt`, `keyDeg₂_eq_D₂`, `corrected_top_digit`) ·
C130s6 (`dvSupp_neg`, `min_dvSupp_le_dvSupp_add`) · C35 (`dvSideMin_eq_zero_of_isDvPure`) ·
C118a (`stageHeight_zero`, `smul_top_pos`, `dev_zero_any`) · C02/C06/C07/C29 (defs) ·
B04/B32a/B35a (`dev` calculus) · C51/C38a (the signed premise vocabulary).

## Status

Sorry-free, axiom-free (Lean core only) — see the AxCheck footer.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

namespace C150rb5

/-! ### Part 0 — `towerSolve` exactness on a coprime pair -/

/-- **The C.83 solve is exact on a coprime pair**: `towerSolve u e k · u ≡ k (mod e)`.
Existence of a solution in `[0, e)` is coprimality (an inverse of `u` mod `e`); the
`List.find?` search therefore succeeds and returns a witness of its own predicate. -/
theorem towerSolve_mod_eq {e : ℕ} (he : 0 < e) {u : ℕ} (hcop : Nat.Coprime u e) (k : ℕ) :
    towerSolve u e k * u % e = k % e := by
  obtain ⟨b₀, hb₀lt, hb₀⟩ : ∃ b₀, b₀ < e ∧ b₀ * u % e = k % e := by
    haveI : NeZero e := ⟨he.ne'⟩
    refine ⟨k * ((u : ZMod e))⁻¹.val % e, Nat.mod_lt _ he, ?_⟩
    rw [Nat.mod_mul_mod]
    have hone : ((u : ZMod e))⁻¹ * (u : ZMod e) = 1 := by
      rw [mul_comm]; exact ZMod.coe_mul_inv_eq_one u hcop
    have hz : ((k * ((u : ZMod e))⁻¹.val * u : ℕ) : ZMod e) = ((k : ℕ) : ZMod e) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rw [mul_assoc, hone, mul_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  unfold towerSolve
  cases hfind : (List.range e).find? (fun b => (b * u) % e == k % e) with
  | none =>
    exact absurd (by simpa using hb₀)
      (by simpa using List.find?_eq_none.mp hfind b₀ (List.mem_range.mpr hb₀lt))
  | some b =>
    have hp := List.find?_some hfind
    simpa using hp

/-! ### Part 1 — valuation floors for monomials -/

/-- `gaussVal` of a constant is the coefficient's valuation (local copy of C35b's
`gaussVal_C`, generic universe). -/
private theorem gaussVal_C' (a : O) :
    gaussVal (Polynomial.C a) = IsDiscreteValuationRing.addVal O a := by
  simp [gaussVal]

/-- `addVal (π ^ a) = a` (the C35b `addVal_two_pow` induction, at a general uniformizer). -/
private theorem addVal_pi_pow (hπ : Irreducible π) (a : ℕ) :
    IsDiscreteValuationRing.addVal O (π ^ a) = (a : ℕ∞) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AddValuation.map_mul, ih, addVal_uniformizer hπ]
    push_cast
    ring

/-- The valuation floor of a `π`-power multiple. -/
private theorem le_addVal_of_pow_dvd (hπ : Irreducible π) {c : O} {a : ℕ}
    (h : π ^ a ∣ c) : (a : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  obtain ⟨d, rfl⟩ := h
  rw [AddValuation.map_mul, addVal_pi_pow hπ]
  exact le_self_add

/-- **The stage-height floor of a monomial digit**: `dv(C c · X^p) ≥ e₁·a + h·p` when
`π^a ∣ c` — coefficientwise off `EFF.HE6.10`'s display. -/
private theorem le_stageHeight_C_mul_X_pow (F : KeyFrame O π) (hπ : Irreducible π)
    {c : O} {a : ℕ} (hdvd : π ^ a ∣ c) (p : ℕ) :
    ((F.e₁ * a + F.h * p : ℕ) : ℕ∞)
      ≤ F.stageHeight (Polynomial.C c * Polynomial.X ^ p) := by
  rw [KeyFrame.stageHeight_eq_inf]
  refine Finset.le_inf fun n _ => ?_
  by_cases hnp : n = p
  · subst hnp
    have hc : (Polynomial.C c * Polynomial.X ^ n).coeff n = c := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    rw [hc, gaussVal_C']
    calc ((F.e₁ * a + F.h * n : ℕ) : ℕ∞)
        = (F.e₁ : ℕ∞) * (a : ℕ∞) + (F.h : ℕ∞) * (n : ℕ∞) := by push_cast; ring
      _ ≤ (F.e₁ : ℕ∞) * IsDiscreteValuationRing.addVal O c + (F.h : ℕ∞) * (n : ℕ∞) := by
          gcongr
          exact le_addVal_of_pow_dvd hπ hdvd
      _ = F.e₁ • IsDiscreteValuationRing.addVal O c + (F.h : ℕ∞) * (n : ℕ∞) := by
          rw [nsmul_eq_mul]
  · have hc : (Polynomial.C c * Polynomial.X ^ p).coeff n = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hnp, mul_zero]
    rw [hc, gaussVal_C', AddValuation.map_zero, C118a.smul_top_pos F.he₁, top_add]
    exact le_top

/-! ### Part 2 — `dvSupp` floors: zero, single monomial term, finite sums -/

private theorem dvSupp_zero' (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    dvSupp F (0 : Polynomial O) u ℓ = ⊤ := by
  rw [dvSupp]
  simp [dvHgt, C118a.dev_zero_any, C118a.stageHeight_zero, C118a.smul_top_pos hℓ]

/-- The ultrametric floor of a finite sum, from C130s6's binary inequality. -/
private theorem le_dvSupp_finset_sum (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) {c : ℕ∞}
    {ι : Type*} (sfin : Finset ι) (g : ι → Polynomial O)
    (hg : ∀ i ∈ sfin, c ≤ dvSupp F (g i) u ℓ) :
    c ≤ dvSupp F (∑ i ∈ sfin, g i) u ℓ := by
  classical
  induction sfin using Finset.induction_on with
  | empty => rw [Finset.sum_empty, dvSupp_zero' F hℓ]; exact le_top
  | @insert a sfin' ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min (hg a (Finset.mem_insert_self a sfin'))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))) ?_
    exact C130s6.min_dvSupp_le_dvSupp_add F hℓ _ _

/-- **The `dvSupp` floor of a single lift term** `C c · X^p · Φ′^q`: its only nonzero
`F.key`-digit sits at abscissa `q` with stage height `≥ e₁a + hp`, so the cleared support
is `≥ ℓ(e₁a + hp) + uq`. -/
private theorem le_dvSupp_C_mul_X_pow_mul_key (F : KeyFrame O π) (hπ : Irreducible π)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {c : O} {a p q lam : ℕ} (hdvd : π ^ a ∣ c)
    (hp : p < F.e₁ * F.f₁)
    (heq : ℓ * (F.e₁ * a + F.h * p) + u * q = lam) :
    (lam : ℕ∞) ≤ dvSupp F (Polynomial.C c * Polynomial.X ^ p * F.key ^ q) u ℓ := by
  have hkeypos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  rw [dvSupp]
  refine Finset.le_inf fun j _ => ?_
  rcases Nat.lt_trichotomy j q with hlt | heqj | hgt
  · rw [dvHgt, dev_mul_pow_of_lt F.hmonic _ _ _ hlt, C118a.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  · subst heqj
    have hdev : dev F.key (Polynomial.C c * Polynomial.X ^ p * F.key ^ j) j
        = Polynomial.C c * Polynomial.X ^ p := by
      have h0 := dev_mul_pow F.hmonic j (Polynomial.C c * Polynomial.X ^ p) 0
      rw [Nat.add_zero] at h0
      rw [h0]
      by_cases hc0 : c = 0
      · subst hc0
        rw [Polynomial.C_0, zero_mul]
        exact Polynomial.zero_modByMonic F.key
      · show (Polynomial.C c * Polynomial.X ^ p) %ₘ F.key = _
        refine (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr ?_
        rw [Polynomial.degree_C_mul_X_pow p hc0,
          Polynomial.degree_eq_natDegree F.hmonic.ne_zero]
        exact_mod_cast (by rw [F.hdeg]; exact hp : p < F.key.natDegree)
    rw [dvHgt, hdev]
    calc (lam : ℕ∞) = ((ℓ * (F.e₁ * a + F.h * p) + u * j : ℕ) : ℕ∞) := by rw [heq]
      _ = (ℓ : ℕ∞) * ((F.e₁ * a + F.h * p : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞) := by
          push_cast; ring
      _ ≤ (ℓ : ℕ∞) * F.stageHeight (Polynomial.C c * Polynomial.X ^ p)
            + (u : ℕ∞) * (j : ℕ∞) := by
          gcongr
          exact le_stageHeight_C_mul_X_pow F hπ hdvd p
      _ = ℓ • F.stageHeight (Polynomial.C c * Polynomial.X ^ p)
            + (u : ℕ∞) * (j : ℕ∞) := by rw [nsmul_eq_mul]
  · obtain ⟨d, rfl⟩ : ∃ d, j = q + (d + 1) := ⟨j - q - 1, by omega⟩
    have hdeg0 : (Polynomial.C c * Polynomial.X ^ p).natDegree
        < (d + 1) * F.key.natDegree := by
      calc (Polynomial.C c * Polynomial.X ^ p).natDegree
          ≤ p := le_trans Polynomial.natDegree_mul_le (by simp)
        _ < F.e₁ * F.f₁ := hp
        _ = 1 * F.key.natDegree := by rw [F.hdeg, one_mul]
        _ ≤ (d + 1) * F.key.natDegree := Nat.mul_le_mul (by omega) le_rfl
    have hdev0 : dev F.key (Polynomial.C c * Polynomial.X ^ p * F.key ^ q) (q + (d + 1))
        = 0 := by
      rw [dev_mul_pow F.hmonic]
      exact dev_eq_zero_of_lt F.hmonic hkeypos _ _ hdeg0
    rw [dvHgt, hdev0, C118a.stageHeight_zero, C118a.smul_top_pos hℓ, top_add]
    exact le_top

/-! ### Part 3 — the exact `n2Exp` grade equation at live heights -/

private theorem n2Exp_fst_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) :
    (n2Exp T m).1
      = ((m - towerSolve T.u₂ T.e₂ m * T.u₂) / T.e₂
          - F.slotIdx ((m - towerSolve T.u₂ T.e₂ m * T.u₂) / T.e₂) * F.h) / F.e₁ := rfl

/-- **The exact grade equation** `e₂(e₁a₀ + h·i) + u₂·b = M` of the `n̂₂` solve, for any
height `M` above the truncation threshold: both ℕ-divisions in `n2Exp` are exact
(`towerSolve`'s congruence + `slotIdx`'s congruence), and both ℕ-subtractions are genuine
(the `EFF.GENTOW1.27` audit inequality, from the node floor). -/
private theorem n2Exp_grade_eq_of_le {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hh : 1 ≤ F.h) {M : ℕ}
    (hM : T.e₂ * T.u₂ + T.e₂ * (F.e₁ * F.h) + 2 ≤ M + T.u₂) :
    T.e₂ * (F.e₁ * (n2Exp T M).1 + F.h * (n2Exp T M).2.1) + T.u₂ * (n2Exp T M).2.2
      = M := by
  rw [n2Exp_fst_eq, C150rb4.n2Exp_snd_fst_eq, C150rb4.n2Exp_snd_snd_eq]
  set b := towerSolve T.u₂ T.e₂ M with hbdef
  set m' := (M - b * T.u₂) / T.e₂ with hm'def
  set i := F.slotIdx m' with hidef
  have hblt : b < T.e₂ := by
    rw [hbdef]; exact C150rb4.towerSolve_lt T.he₂ T.u₂ M
  have hbmod : b * T.u₂ % T.e₂ = M % T.e₂ := by
    rw [hbdef]; exact towerSolve_mod_eq T.he₂ T.hcop M
  have hbu : b * T.u₂ + T.u₂ ≤ T.e₂ * T.u₂ := by
    calc b * T.u₂ + T.u₂ = (b + 1) * T.u₂ := by ring
      _ ≤ T.e₂ * T.u₂ := Nat.mul_le_mul hblt le_rfl
  have hbuM : b * T.u₂ ≤ M := by omega
  have hdvd : T.e₂ ∣ M - b * T.u₂ := (Nat.modEq_iff_dvd' hbuM).mp hbmod
  have he2m' : T.e₂ * m' = M - b * T.u₂ := Nat.mul_div_cancel' hdvd
  have hm'lb : T.e₂ * (F.e₁ * F.h) + 2 ≤ T.e₂ * m' := by
    rw [he2m']; omega
  have hm'lb2 : F.e₁ * F.h + 1 ≤ m' := by
    by_contra hcon
    have hcon' : m' < F.e₁ * F.h + 1 := not_le.mp hcon
    have hcon2 : T.e₂ * m' ≤ T.e₂ * (F.e₁ * F.h) :=
      Nat.mul_le_mul le_rfl (by omega)
    omega
  have hilt : i < F.e₁ := by
    rw [hidef]; exact (F.slotIdx_spec m').1
  have hicong : i * F.h ≡ m' [MOD F.e₁] := by
    rw [hidef]; exact (F.slotIdx_spec m').2
  have hih : i * F.h ≤ m' := by
    have h1 : i * F.h + F.h ≤ F.e₁ * F.h := by
      calc i * F.h + F.h = (i + 1) * F.h := by ring
        _ ≤ F.e₁ * F.h := Nat.mul_le_mul hilt le_rfl
    omega
  have hdvd1 : F.e₁ ∣ m' - i * F.h := (Nat.modEq_iff_dvd' hih).mp hicong
  have he1a : F.e₁ * ((m' - i * F.h) / F.e₁) = m' - i * F.h := Nat.mul_div_cancel' hdvd1
  have hS : F.e₁ * ((m' - i * F.h) / F.e₁) + F.h * i = m' := by
    rw [he1a, Nat.mul_comm F.h i]
    omega
  calc T.e₂ * (F.e₁ * ((m' - i * F.h) / F.e₁) + F.h * i) + T.u₂ * b
      = T.e₂ * m' + T.u₂ * b := by rw [hS]
    _ = (M - b * T.u₂) + T.u₂ * b := by rw [he2m']
    _ = M := by rw [Nat.mul_comm T.u₂ b]; omega

/-! ### Part 4 — the lift's grade floor (the M4 input) -/

/-- Every lift term's `X`-exponent stays under `D′ = e₁f₁` (C150rb4's private `xexp_lt`,
re-derived). -/
private theorem xexp_lt' {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (M : ℕ) {r : ℕ} (hr : r < F.f₁) :
    (n2Exp T M).2.1 + F.e₁ * r < F.e₁ * F.f₁ :=
  calc (n2Exp T M).2.1 + F.e₁ * r
      < F.e₁ + F.e₁ * r := Nat.add_lt_add_right (C150rb4.n2Exp_snd_fst_lt T M) _
    _ = F.e₁ * (r + 1) := by ring
    _ ≤ F.e₁ * F.f₁ := Nat.mul_le_mul le_rfl hr

/-- ★ **The grade floor of the `K₂`-digit lift**: every term of `k2DigitLift T s lam`
sits at cleared level grade exactly `lam`, so `W(lift) ≥ lam`.  Choice-robust: only the
`π`-power divisibility of the coefficients is consumed, never their values. -/
theorem dvSupp_k2DigitLift_ge {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    (s : AdjoinRoot (towerLabel T)) {lam : ℕ} (hslope : T.E₂ < lam) :
    (lam : ℕ∞) ≤ dvSupp F (k2DigitLift T s lam) T.u₂ T.e₂ := by
  classical
  unfold k2DigitLift
  refine le_dvSupp_finset_sum F T.he₂ _ _ fun r hr => ?_
  refine le_dvSupp_finset_sum F T.he₂ _ _ fun t ht => ?_
  have hr' : r < F.f₁ := Finset.mem_range.mp hr
  have ht' : t < T.f₂ := Finset.mem_range.mp ht
  -- the audit atoms
  have key1 : F.e₁ * T.e₂ * F.h * r + T.e₂ * (F.e₁ * F.h) ≤ F.e₁ * T.e₂ * F.h * F.f₁ := by
    calc F.e₁ * T.e₂ * F.h * r + T.e₂ * (F.e₁ * F.h)
        = F.e₁ * T.e₂ * F.h * (r + 1) := by ring
      _ ≤ F.e₁ * T.e₂ * F.h * F.f₁ := Nat.mul_le_mul_left _ hr'
  have key2 : F.e₁ * T.e₂ * F.h * F.f₁ + 1 ≤ T.u₂ := by
    have h1 : T.e₂ * (F.e₁ * F.f₁) * F.h < T.u₂ := T.hfloor
    calc F.e₁ * T.e₂ * F.h * F.f₁ + 1 = T.e₂ * (F.e₁ * F.f₁) * F.h + 1 := by ring
      _ ≤ T.u₂ := h1
  have key3 : T.e₂ * T.u₂ * t + T.e₂ * T.u₂ ≤ T.e₂ * T.u₂ * T.f₂ := by
    calc T.e₂ * T.u₂ * t + T.e₂ * T.u₂ = T.e₂ * T.u₂ * (t + 1) := by ring
      _ ≤ T.e₂ * T.u₂ * T.f₂ := Nat.mul_le_mul_left _ ht'
  have hX4lam : T.e₂ * T.u₂ * T.f₂ < lam := by
    have hE2 : T.E₂ = T.e₂ * T.f₂ * T.u₂ := rfl
    calc T.e₂ * T.u₂ * T.f₂ = T.e₂ * T.f₂ * T.u₂ := by ring
      _ < lam := hE2 ▸ hslope
  have key4 : T.u₂ ≤ T.e₂ * T.u₂ := Nat.le_mul_of_pos_left T.u₂ T.he₂
  have key5 : T.e₂ * T.u₂ ≤ T.e₂ * T.u₂ * T.f₂ := Nat.le_mul_of_pos_right _ T.hf₂
  have hΔlam : F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t ≤ lam := by omega
  have hgen := n2Exp_grade_eq_of_le T hh
    (M := lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t)) (by omega)
  refine le_dvSupp_C_mul_X_pow_mul_key F hπ T.he₂ (dvd_mul_left _ _)
    (xexp_lt' T _ hr') ?_
  calc T.e₂ * (F.e₁ * (n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1
          + F.h * ((n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1 + F.e₁ * r))
        + T.u₂ * ((n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2 + T.e₂ * t)
      = (T.e₂ * (F.e₁ * (n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1
          + F.h * (n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1)
          + T.u₂ * (n2Exp T (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2)
        + (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t) := by ring
    _ = (lam - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))
        + (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t) := by rw [hgen]
    _ = lam := Nat.sub_add_cancel hΔlam

end C150rb5

/-! ### THE NODE — the A-C.23 re-signed C.56(i), proved -/

set_option linter.unusedVariables false in
/-- **NODE C.56(i), `refine_invariants` (re-signed: A-C.23, 2026-08-28)** — the
source-faithful GENTOW-2(i): the corrected key `Φ₂⁺ = Φ₂ - lift(s; lam)` keeps the
perturbation-stable key package.  Monic of degree `D₂` and top `F.key`-digit `1`
(C150rb4); one-sided of slope `κ₂ = u₂/e₂` with pinned height `f₂u₂` and level residual
`towerLabel T` byte-unchanged (M4, `C133mh0.dv_pure_add_of_lt`, fed by the lift's grade
floor `W(lift) ≥ lam > E₂`).  The premises are byte-identical to the pre-amendment axiom
(leanspec `ChapC.lean:2163`, archived at commit `523c8a7b`); the `f`-side hypotheses are
deliberately unused — the signed conclusion never mentioned `f`. -/
theorem refine_invariants {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂) :
    (composedKey T - k2DigitLift T s lam).Monic ∧
    (composedKey T - k2DigitLift T s lam).natDegree = T.D₂ ∧
    dev F.key (composedKey T - k2DigitLift T s lam) (T.e₂ * T.f₂) = 1 ∧
    IsDvPure F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ ∧
    ∃ hne' : (dvSideSet F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂).Nonempty,
    ∃ hp' : dvHgt F (composedKey T - k2DigitLift T s lam)
        (dvSideMin F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ hne')
        = ((T.f₂ * T.u₂ : ℕ) : ℕ∞),
      dvResPoly F H₀ hpin (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ hne'
        (T.f₂ * T.u₂) hp' = towerLabel T := by
  classical
  -- the composed key's own pinned data (C.47 + C131aa)
  have hTK : IsTestKey (T.levelDatum hπ) (composedKey T) := composedKey_isTestKey T hπ hh
  have hpure : IsDvPure F (composedKey T) T.u₂ T.e₂ :=
    isTestKey_isDvPure (T.levelDatum hπ) hTK
  have hxne : (dvSideSet F (composedKey T) T.u₂ T.e₂).Nonempty := ⟨0, hpure.1⟩
  have hmin0 : dvSideMin F (composedKey T) T.u₂ T.e₂ hxne = 0 :=
    dvSideMin_eq_zero_of_isDvPure hpure hxne
  have hslot0 := (hTK.2.2.2.2 0 (T.levelDatum hπ).hrdeg).2 (T.levelDatum hπ).hr0
  have hrdeg : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  have hh0 : dvHgt F (composedKey T) 0 = ((T.f₂ * T.u₂ : ℕ) : ℕ∞) := by
    have h1 := hslot0.1
    rw [mul_zero, Nat.sub_zero, hrdeg] at h1
    exact h1
  have hMx : dvHgt F (composedKey T) (dvSideMin F (composedKey T) T.u₂ T.e₂ hxne)
      = ((T.f₂ * T.u₂ : ℕ) : ℕ∞) := by rw [hmin0]; exact hh0
  have hxsupp : dvSupp F (composedKey T) T.u₂ T.e₂ = ((T.E₂ : ℕ) : ℕ∞) := by
    have hmem := hpure.1
    simp only [dvSideSet, Finset.mem_filter, Finset.mem_range] at hmem
    have hsupp0 : dvSupp F (composedKey T) T.u₂ T.e₂
        = T.e₂ • dvHgt F (composedKey T) 0 + (T.u₂ * 0 : ℕ∞) := hmem.2.1
    rw [hsupp0, hh0, show T.E₂ = T.e₂ * (T.f₂ * T.u₂) from by
      rw [show T.E₂ = T.e₂ * T.f₂ * T.u₂ from rfl]; ring]
    push_cast [nsmul_eq_mul]
    ring
  -- the lift side: degree drop + grade floor
  have hliftdeg : (k2DigitLift T s lam).natDegree < (composedKey T).natDegree := by
    rw [composedKey_natDegree T hπ, C150rb4.keyDeg₂_eq_D₂ T hπ]
    exact C150rb4.natDegree_k2DigitLift_lt T s lam
  have hydeg : (-(k2DigitLift T s lam)).degree < (composedKey T).degree := by
    rw [Polynomial.degree_neg]
    exact Polynomial.degree_lt_degree hliftdeg
  have hy : ((T.E₂ + 1 : ℕ) : ℕ∞) ≤ dvSupp F (-(k2DigitLift T s lam)) T.u₂ T.e₂ := by
    rw [C130s6.dvSupp_neg]
    exact le_trans (by exact_mod_cast Nat.succ_le_of_lt hslope)
      (C150rb5.dvSupp_k2DigitLift_ge T hπ hh s hslope)
  -- M4
  obtain ⟨hmon, hdeg', hpure', hne', hpinM', hres'⟩ :=
    C133mh0.dv_pure_add_of_lt F hπ H₀ hpin T.he₂ T.hcop (composedKey_monic T) hpure
      (hxne := hxne) hMx hxsupp hydeg hy
  have hlabel : dvResPoly F H₀ hpin (composedKey T) T.u₂ T.e₂ hxne (T.f₂ * T.u₂) hMx
      = towerLabel T :=
    dvResPoly_testKey hπ (T.levelDatum hπ) hTK hxne (T.f₂ * T.u₂) hMx
  rw [sub_eq_add_neg]
  exact ⟨hmon,
    hdeg'.trans (by rw [composedKey_natDegree T hπ, C150rb4.keyDeg₂_eq_D₂ T hπ]),
    by rw [← sub_eq_add_neg]; exact C150rb4.corrected_top_digit T s lam,
    hpure', hne', hpinM', hres'.trans hlabel⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C150rb5.towerSolve_mod_eq
#print axioms Uniformity.Density.Tower.C150rb5.dvSupp_k2DigitLift_ge
#print axioms Uniformity.Density.Tower.refine_invariants

end AxCheck
