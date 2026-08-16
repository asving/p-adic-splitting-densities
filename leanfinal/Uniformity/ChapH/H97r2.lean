/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H97r1
import Uniformity.ChapG.G58
import Uniformity.Density.NormLeaves
import Uniformity.StrongHensel

/-!
# Uniformity.ChapH.H97r2 — the recentred certificates: cases E, L, R

**Chapter H, node-support file `H97r2`** (unit OM-1, `docs/openmath-campaign/
OM-1_n3-rate_2026-08-16.md`, step S2). The three decidedness certificates of the recentred
four-case split (`N3_CHECK` §13.1): for a cubic `monicPoly b` with all coefficients in `𝔪`,

| case | condition | verdict |
|---|---|---|
| **E** | `π² ∤ B₀` | `c3ram` (Eisenstein) |
| **L** | `π² ∣ B₀`, `π² ∤ B₁` | `c3linRam` (strong Hensel at a shifted centre) |
| **R** | `π² ∣ B₀`, `π² ∣ B₁`, `π³ ∤ B₀` | `c3ram` (no root + coprime norm-valuations) |

Every hypothesis is a `π ∣ ·` predicate readable mod `π³`, which is what makes these
LEVEL-3 class certificates in the step lemma (H97r3).

**PROVENANCE (quarry discipline).** Backport from the `leancheck` sidecar, verified building
green at leancheck commit `b00b0505` (2026-08-16): `UniformityCheck/N3Shift.lean`
(`typeOf_ram3_of_val_one`), `UniformityCheck/N3CertLinRam.lean` (`exists_root_of_val_one`,
`typeOf_linRam_of_val_one`), `UniformityCheck/N3CertRam.lean` (`exists_root_of_natDegree_one`,
`irreducible_of_no_root_cubic`, `no_root_of_val_two`, `typeOf_ram3_of_val_two`).
**Dedup-audit — verbatim moves except:**

1. namespace `UniformityCheck` → `Uniformity.Density`.
2. **CASE E**: leancheck's `typeOf_ram3_of_eisenstein` takes four membership arguments; the
   landed G.58 version takes `(hlow : ∀ i, b i ∈ 𝔪, h0 : b 0 ∉ 𝔪²)` — the wrapper below
   re-packages the divisibility hypotheses accordingly.
3. **CASE R is RE-BASED**: leancheck proves `2 ∈ normValues` through its own 444-line cubic
   norm layer (`cub3`/`cubElt`/`norm_root_cub`); here the landed general-degree CN-19
   `norm_adjoinRoot_root` (`NormLeaves.lean`) supplies `N(θ) = (−1)³·b₀` directly, and the
   `θ ≠ 0` / module instances are set up exactly as in the landed `typeOf_eisenstein`
   (same file). The statement is byte-identical up to `cub3 b ↦ monicPoly b` (the two are
   equal — leancheck's `monicPoly_eq_cub3`); the certified content is unchanged.
4. leancheck's `exists_cubic_root_strong` wrapper (`P5Consume.lean`) is inlined: CASE L calls
   the landed `Uniformity.Hensel.strongHensel` directly.
5. `isUnit_leadingCoeff_of_dvd_monic` / `isUnit_of_natDegree_zero` are NOT ported (landed in
   `TypeOf.lean`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. CASE E — `v(B₀) = 1` is Eisenstein (port: `N3Shift`) -/

section CertE

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CASE E of the recentred split**, in `π`-divisibility form: `v(B₀) = 1` (with
`B₁, B₂ ∈ 𝔪`) forces `{(3,1)}`. A restatement of G.58's `typeOf_ram3_of_eisenstein`. -/
theorem typeOf_ram3_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h0 : π ∣ b 0) (h0' : ¬ π ^ 2 ∣ b 0) (h1 : π ∣ b 1) (h2 : π ∣ b 2) :
    typeOf (monicPoly b) = c3ram := by
  have hmem : ∀ x : O, π ∣ x → x ∈ maximalIdeal O := fun x hx =>
    (mem_maximalIdeal_iff_dvd hπ x).2 hx
  have hlow : ∀ i : Fin 3, b i ∈ maximalIdeal O := by
    intro i
    fin_cases i
    · exact hmem _ h0
    · exact hmem _ h1
    · exact hmem _ h2
  have h0m : b 0 ∉ (maximalIdeal O) ^ 2 := fun hc =>
    h0' ((mem_maximalIdeal_pow_iff_dvd hπ 2 (b 0)).1 hc)
  exact typeOf_ram3_of_eisenstein hlow h0m

end CertE

/-! ## 2. CASE L — `v(B₁) = 1`, `v(B₀) ≥ 2` is linear × ramified (port: `N3CertLinRam`)

THE strong-Hensel consumer. Strong Hensel does NOT fire at `x₀ = 0` (there
`v(F(0)) = v(B₀)` can be exactly `2 = 2·v(F′(0))`, failing `k > 2w` by one); it fires at the
SHIFTED centre `x₀ = πt` with `t := −C·u⁻¹`, where `B₁ = πu` and `B₀ = π²C`. -/

section CertL

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The shifted strong-Hensel centre fires.** With `B₁ = π u` (`u` a unit), `B₀ = π² C`,
`B₂ = π B₂′`, the point `x₀ = π·(−C·u⁻¹)` has `π³ ∣ F(x₀)` and `F′(x₀) = π · unit`; strong Hensel
therefore returns a root `r` of `F` with `π² ∣ r − x₀`, in particular `π ∣ r`. -/
theorem exists_root_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ∣ b 1) (h1' : ¬ π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) :
    ∃ r : O, (monicPoly b).eval r = 0 ∧ π ∣ r ∧ π ^ 2 ∣ (b 1 + b 2 * r + r ^ 2) - b 1 := by
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨u, hu_eq⟩ := h1
  obtain ⟨c, hc⟩ := h0
  obtain ⟨B2, hB2⟩ := h2
  -- `u` is a unit: otherwise `π ∣ u`, hence `π² ∣ b 1`, contradicting `h1'`
  have hu : IsUnit u := by
    by_contra hun
    refine h1' ?_
    have hπu : π ∣ u := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hun)
    obtain ⟨d, rfl⟩ := hπu
    exact ⟨d, by rw [hu_eq]; ring⟩
  -- the shifted centre `x₀ = π t`, where `t = -c·u⁻¹` solves `u t + c = 0` exactly
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨t, hut⟩ : ∃ t : O, u * t + c = 0 := ⟨-(c * w), by linear_combination (-c) * hw⟩
  -- `F(x₀) = π³(t³ + B₂′t²)`, so `k = 3`
  have hval : π ^ 3 ∣ (monicPoly b).eval (π * t) := by
    refine ⟨t ^ 3 + B2 * t ^ 2, ?_⟩
    rw [cubic_eval, hB2, hu_eq, hc]
    linear_combination (π ^ 2) * hut
  -- `F′(x₀) = π·(u + π(3t² + 2B₂′t))`, a unit times `π`, so `w = 1` exactly
  have hmem : π * (3 * t ^ 2 + 2 * B2 * t) ∈ maximalIdeal O :=
    (mem_maximalIdeal_iff_dvd hπ _).2 ⟨_, rfl⟩
  have hbu : IsUnit (u + π * (3 * t ^ 2 + 2 * B2 * t)) :=
    Uniformity.Hensel.isUnit_add_of_mem_maximalIdeal hu hmem
  have hd : ∃ v : Oˣ, (monicPoly b).derivative.eval (π * t) = π ^ 1 * v := by
    refine ⟨hbu.unit, ?_⟩
    rw [hbu.unit_spec, cubic_deriv_eval, hB2, hu_eq]
    ring
  obtain ⟨r, hr0, hrd, -⟩ := Uniformity.Hensel.strongHensel hπ hd hval (by norm_num)
  have hrd2 : π ^ 2 ∣ r - π * t := by simpa using hrd
  have hπr : π ∣ r := by
    have hsum := dvd_add ((dvd_pow_self π (by norm_num : (2 : ℕ) ≠ 0)).trans hrd2)
      (dvd_mul_right π t)
    simpa using hsum
  refine ⟨r, hr0, hπr, ?_⟩
  obtain ⟨s, hs⟩ := hπr
  refine ⟨B2 * s + s ^ 2, ?_⟩
  rw [hB2, hs]
  ring

/-- **CERT L (CASE L of the recentred split).** `v(B₁) = 1` with `v(B₀) ≥ 2`, `v(B₂) ≥ 1`
forces the type `{(1,1),(2,1)}`: a root of positive valuation, peeled off, leaves an Eisenstein
quadratic. -/
theorem typeOf_linRam_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ∣ b 1) (h1' : ¬ π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) :
    typeOf (monicPoly b) = c3linRam := by
  obtain ⟨r, hr, hπr, hsq⟩ := exists_root_of_val_one hπ h2 h1 h1' h0
  have hsq' : π ^ 2 ∣ b 2 * r + r ^ 2 := by
    have hid : (b 1 + b 2 * r + r ^ 2) - b 1 = b 2 * r + r ^ 2 := by ring
    rwa [hid] at hsq
  -- the cofactor `peel b r = ![b 1 + b 2 r + r², b 2 + r]` is Eisenstein
  have hg0 : peel b r 0 ∈ maximalIdeal O := by
    rw [peel_zero]
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have hid : b 1 + b 2 * r + r ^ 2 = b 1 + (b 2 * r + r ^ 2) := by ring
    rw [hid]
    exact dvd_add h1 ((dvd_pow_self π (by norm_num : (2 : ℕ) ≠ 0)).trans hsq')
  have hg0' : peel b r 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    rw [peel_zero] at hmem
    refine h1' ?_
    have hdvd : π ^ 2 ∣ b 1 + b 2 * r + r ^ 2 := by
      rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hid : b 1 = (b 1 + b 2 * r + r ^ 2) - (b 2 * r + r ^ 2) := by ring
    rw [hid]
    exact dvd_sub hdvd hsq'
  have hg1 : peel b r 1 ∈ maximalIdeal O := by
    rw [peel_one]
    exact (mem_maximalIdeal_iff_dvd hπ _).2 (dvd_add h2 hπr)
  apply FactorizationType.ext
  rw [cubic_peel b r hr, typeOf_linear_mul (monicPoly_monic (peel b r)) r,
    typeOf_ram_of_eisenstein hg0 hg0' hg1]
  rfl

end CertL

/-! ## 3. CASE R — `v(B₀) = 2`, `v(B₁) ≥ 2` is totally ramified (port: `N3CertRam`,
re-based on CN-19)

The Newton polygon reading is "one side of slope `−2/3`", but the proof never mentions
polygons: no root in `O` (valuation bookkeeping) ⟹ irreducible (a monic cubic factors through
a monic linear factor); `f = 1` because `2` and `3` are both norm-valuations and
`gcd(2,3) = 1`. ⚠ The `π² ∣ B₁` hypothesis is NOT decoration: at `v(B₁) = 1` the type is
`{(1,1),(2,1)}` instead (CASE L above) — the correction `N3_CHECK` §13.1 records against
§9.4's table. -/

section CertR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A degree-`1` polynomial with unit leading coefficient has a root: monicize and read off
`r = −u⁻¹ · p₀`. -/
private theorem exists_root_of_natDegree_one {p : Polynomial O} (hd : p.natDegree = 1)
    (hu : IsUnit p.leadingCoeff) : ∃ r : O, p.eval r = 0 := by
  obtain ⟨u, hu'⟩ := hu
  have hp : p = C (p.coeff 1) * X + C (p.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one (by omega)
  have hlc : p.coeff 1 = (u : O) := by rw [hu', leadingCoeff, hd]
  have heval : ∀ r : O, p.eval r = p.coeff 1 * r + p.coeff 0 := by
    intro r
    conv_lhs => rw [hp]
    simp
  refine ⟨-((↑u⁻¹ : O) * p.coeff 0), ?_⟩
  rw [heval, hlc, mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]

/-- **A monic cubic with no root in `O` is irreducible.** Any nontrivial factorization of a
monic polynomial has both factors with unit leading coefficient and positive degree, so at
degree `3` one factor has degree `1`; monicizing it exhibits a root. -/
theorem irreducible_of_no_root_cubic {b : Fin 3 → O}
    (h : ∀ r : O, (monicPoly b).eval r ≠ 0) : Irreducible (monicPoly b) := by
  have hm : (monicPoly b).Monic := monicPoly_monic b
  have hd : (monicPoly b).natDegree = 3 := monicPoly_natDegree b
  constructor
  · intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  · intro g k hgk
    have hg0 : g ≠ 0 := by
      rintro rfl; exact hm.ne_zero (hgk.trans (zero_mul k))
    have hk0 : k ≠ 0 := by
      rintro rfl; exact hm.ne_zero (hgk.trans (mul_zero g))
    have hgu : IsUnit g.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic hm ⟨k, hgk⟩
    have hku : IsUnit k.leadingCoeff :=
      isUnit_leadingCoeff_of_dvd_monic hm ⟨g, by rw [hgk, mul_comm]⟩
    have hdeg : g.natDegree + k.natDegree = 3 := by
      rw [← natDegree_mul hg0 hk0, ← hgk]; exact hd
    rcases Nat.eq_zero_or_pos g.natDegree with hgz | hgpos
    · exact Or.inl (isUnit_of_natDegree_zero hgz hgu)
    rcases Nat.eq_zero_or_pos k.natDegree with hkz | hkpos
    · exact Or.inr (isUnit_of_natDegree_zero hkz hku)
    exfalso
    have key : ∀ p q : Polynomial O, monicPoly b = p * q → p.natDegree = 1 →
        IsUnit p.leadingCoeff → False := by
      intro p q hpq hp1 hpu
      obtain ⟨r, hr⟩ := exists_root_of_natDegree_one hp1 hpu
      exact h r (by rw [hpq, eval_mul, hr, zero_mul])
    have hone : g.natDegree = 1 ∨ k.natDegree = 1 := by omega
    rcases hone with h1 | h1
    · exact key g k hgk h1 hgu
    · exact key k g (by rw [hgk, mul_comm]) h1 hku

/-- **Step 1 of CERT R: no root in `O`.** -/
theorem no_root_of_val_two {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) (h0' : ¬ π ^ 3 ∣ b 0) (r : O) :
    (monicPoly b).eval r ≠ 0 := by
  intro hr
  rw [cubic_eval] at hr
  have h1' : π ∣ b 1 := (dvd_pow_self π two_ne_zero).trans h1
  have h0'' : π ∣ b 0 := (dvd_pow_self π two_ne_zero).trans h0
  -- `π ∣ r³` because `r³ = -(b₂r² + b₁r + b₀)` and `π` divides each summand
  have hcube : π ∣ r ^ 3 := by
    have hEq : r ^ 3 = -(b 2 * r ^ 2 + b 1 * r + b 0) := by linear_combination hr
    rw [hEq]
    exact dvd_neg.mpr
      (dvd_add (dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1' _)) h0'')
  have hπr : π ∣ r := hπ.prime.dvd_of_dvd_pow hcube
  obtain ⟨c, hc⟩ := h2
  obtain ⟨d, hd⟩ := h1
  obtain ⟨s, hs⟩ := hπr
  subst hs
  rw [hc, hd] at hr
  exact h0' ⟨-(s ^ 3 + c * s ^ 2 + d * s), by linear_combination hr⟩

/-- **CERT R (CASE R of the recentred split).** `v(B₀) = 2` together with `v(B₁) ≥ 2`,
`v(B₂) ≥ 1` forces the totally ramified type `{(3,1)}` — over a general discrete valuation
ring, no residue characteristic hypothesis, no completeness. -/
theorem typeOf_ram3_of_val_two {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) (h0' : ¬ π ^ 3 ∣ b 0) :
    typeOf (monicPoly b) = c3ram := by
  have hm : (monicPoly b).Monic := monicPoly_monic b
  have hd3 : (monicPoly b).natDegree = 3 := monicPoly_natDegree b
  have hirr : Irreducible (monicPoly b) :=
    irreducible_of_no_root_cubic (no_root_of_val_two hπ h2 h1 h0 h0')
  -- `b 0` has valuation exactly `2`
  obtain ⟨c, hc⟩ := h0
  have hcu : IsUnit c := by
    by_contra hcn
    refine h0' ?_
    have hπc : π ∣ c := by
      rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcn)
    obtain ⟨e, rfl⟩ := hπc
    exact ⟨e, by rw [hc]; ring⟩
  have hcv : IsDiscreteValuationRing.addVal O c = 0 := by
    rw [← hcu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (b 0) = ((2 : ℕ) : ℕ∞) := by
    rw [hc, AddValuation.map_mul, hπ.addVal_pow, hcv, add_zero]
  -- module instances for the norm (as in the landed `typeOf_eisenstein`)
  have hdpos : 0 < (monicPoly b).natDegree := by omega
  haveI : Nontrivial (AdjoinRoot (monicPoly b)) :=
    AdjoinRoot.nontrivial _ (ne_of_gt (natDegree_pos_iff_degree_pos.1 hdpos))
  haveI : Module.Free O (AdjoinRoot (monicPoly b)) := hm.free_adjoinRoot
  haveI : Module.Finite O (AdjoinRoot (monicPoly b)) := hm.finite_adjoinRoot
  -- `N(θ) = (−1)³·b₀ = −b₀` (CN-19), of valuation exactly `2`
  have hcoeff : (monicPoly b).coeff 0 = b 0 := monicPoly_coeff_lt b (by norm_num)
  have hnorm : Algebra.norm O (AdjoinRoot.root (monicPoly b)) = -(b 0) := by
    rw [norm_adjoinRoot_root hm hdpos, hd3, hcoeff]
    ring
  have ha0 : b 0 ≠ 0 := fun hz => h0' (by rw [hz]; exact dvd_zero _)
  have hne : (AdjoinRoot.root (monicPoly b)) ≠ 0 := by
    intro hz
    rw [hz, Algebra.norm_zero] at hnorm
    exact ha0 (neg_eq_zero.1 hnorm.symm)
  have hmem2 : (2 : ℕ) ∈ normValues (monicPoly b) := by
    refine ⟨two_pos, AdjoinRoot.root (monicPoly b), hne, ?_⟩
    rw [hnorm, AddValuation.map_neg, hval]
  have hmem3 : (3 : ℕ) ∈ normValues (monicPoly b) := by
    have hmem := natDegree_mem_normValues hm hdpos hπ
    rwa [hd3] at hmem
  have hinf : inertiaDegOf (monicPoly b) = 1 :=
    inertiaDegOf_eq_one_of_coprime hmem2 hmem3 (by norm_num)
  -- assemble: `monicPoly b` is its own monic factorization, and `e = 3 / 1 = 3`
  have hF : IsMonicFactorization (monicPoly b) {monicPoly b} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨hm, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [c3ram, efPair, ramIndexOf, hinf, hd3]

end CertR

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_ram3_of_val_one
#print axioms Uniformity.Density.exists_root_of_val_one
#print axioms Uniformity.Density.typeOf_linRam_of_val_one
#print axioms Uniformity.Density.irreducible_of_no_root_cubic
#print axioms Uniformity.Density.no_root_of_val_two
#print axioms Uniformity.Density.typeOf_ram3_of_val_two

end AxCheck
