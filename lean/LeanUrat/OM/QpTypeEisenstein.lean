/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType

/-!
# QpTypeEisenstein — the axiom-free `(e, f) = (deg, 1)` theorem for Eisenstein bundles
(Wild Wave 2 FLAG-1 closure, guardian audit 2026-07-21)

The Wave-2 guardian audit of `om_leaf_faithful` (see `notes/SEMANTIC_AUDIT_LOG.md`, tail) accepted
the axiom with FLAG 1: the fine-(e,f) swap mutation (`{(1,2)}` for `{(2,1)}` at the wild gate) was
not machine-refutable — the recorded probe catches only factor-COUNT mutations, so the (e,f)
PAYLOAD at the gate was cite-trusted. This module closes the flag with a machine guard:

* `ef_of_eisenstein` / `eOf_of_eisenstein` / `fOf_of_eisenstein` / `efOf_of_eisenstein` —
  **axiom-free**: for monic `g : ℤ_[p][X]` Eisenstein at `p·ℤ_[p]` of positive degree and ANY
  bundle `D : LocalFactorData p g`, the genuine mathlib invariants are forced:
  `eOf p D = g.natDegree` and `fOf p D = 1` (full equality, not just the `≥` the probe needs).
  Route: the root `x` of `g` generating `L` is integral, hence descends to `y : O`
  (`IsIntegralClosure.isIntegral_iff`); expanding `aeval y g = 0` and splitting off the
  Eisenstein constant term gives the key identity `y^n = π_p · unit` in the local ring `O`
  (the `unit` is `algebraMap(c₀) + w` with `c₀ := a₀/p` a unit of `ℤ_[p]` — Eisenstein's
  `a₀ ∉ (p)²` — and `w ∈ m_O`); writing `y = u·ϖ^k` in the DVR `O` pins
  `map (p·ℤ_[p]) = m_O^(k·n)`, so `ramificationIdx = k·n ≥ n` by `Ideal.ramificationIdx_spec`;
  the fundamental identity `e·f = [L:ℚ_p] = n` (`ramificationIdx_mul_inertiaDeg_of_isLocalRing`,
  discharged through `IsIntegralClosure.isFractionRing_of_finite_extension` +
  `IsIntegralClosure.finite`) then collapses `k = 1`, `e = n`, `f = 1`.
* `gate_ef_forced` — the wild-gate corollary: membership of a genuine monic quadratic in the
  Wave-1 gate fiber (`Tselfloop 2 gateSide gateShape`) forces `efOf 2 D = (2, 1)` for EVERY
  bundle `D` on it (via the PROVED `QpType.wildGateFiber_valuation` +
  `QpType.isEisensteinAt_of_wildGate`). This is the positive-coherence leg tying the axiom's
  `{(2,1)}` payload to the machine-checked Eisenstein data.
* `efOf_mem_qpType` / `qpType_singleton_forces` — probe plumbing: a singleton-type
  `QpFactorization` consists of exactly `f` itself, and its bundle's `efOf` is the type's
  single pair.
* **Mutation probe (fine-(e,f) swap)**: the mutated axiom concluding the SINGLETON type
  `{(1,2)}` — which PASSES the old factor-count probe — now derives `False` against
  `gateFiber_nonempty` + `gate_ef_forced`. Machine-checked in a scratch file (NOT committed);
  verbatim text and output recorded in the `Mutation probe evidence` comment block below.

Leaf module: no existing file is modified (census append to `AxChk_baseline.lean` is the wave's
Part D). **No axiom, no sorry** — every declaration here must be core-only (AxCheck at bottom).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.QpTypeEisenstein

open Polynomial IsLocalRing
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## Block 1 — local-ring helper -/

/-- In a local ring, a unit plus a maximal-ideal element is a unit. -/
theorem isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra hu
  have hmem : a + b ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hu
  have hamem : a ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hmem hb
    simpa using this
  exact mem_nonunits_iff.mp ((mem_maximalIdeal a).mp hamem) ha

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Block 2 — the master theorem: Eisenstein bundles have `(e, f) = (deg, 1)` -/

/-- **The Eisenstein `(e, f)` theorem (master form, axiom-free).** For monic
`g : ℤ_[p][X]` Eisenstein at `p·ℤ_[p]` with `0 < deg g`, EVERY local-factor bundle
`D : LocalFactorData p g` has `eOf p D = deg g` and `fOf p D = 1`. -/
theorem ef_of_eisenstein {g : ℤ_[p][X]} (hg : g.Monic)
    (hEis : g.IsEisensteinAt (maximalIdeal ℤ_[p])) (hdeg : 0 < g.natDegree)
    (D : QpType.LocalFactorData p g) :
    QpType.eOf p D = g.natDegree ∧ QpType.fOf p D = 1 := by
  letI := D.fieldL
  letI := D.algQL
  letI := D.algZL
  letI := D.towerZQL
  letI := D.crO
  letI := D.domO
  letI := D.dvrO
  letI := D.algZO
  letI := D.algOL
  letI := D.towerZOL
  letI := D.intClosure
  letI := D.liesOver
  -- the instance stack for the fundamental identity
  haveI hFD : FiniteDimensional ℚ_[p] D.L :=
    FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq]; omega)
  haveI : IsFractionRing D.O D.L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] D.L D.O
  haveI : Module.Finite ℤ_[p] D.O := IsIntegralClosure.finite ℤ_[p] ℚ_[p] D.L D.O
  -- the root of g in L descends to O
  obtain ⟨x, hxroot, -⟩ := D.hasRoot
  rw [Polynomial.aeval_map_algebraMap] at hxroot
  have hxint : IsIntegral ℤ_[p] x := ⟨g, hg, by rwa [Polynomial.aeval_def] at hxroot⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := D.O) (R := ℤ_[p]) (B := D.L)).mp hxint
  have hyroot : Polynomial.aeval y g = 0 := by
    apply IsIntegralClosure.algebraMap_injective D.O ℤ_[p] D.L
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hy]
    exact hxroot
  -- injectivity of ℤ_[p] → O (via ℤ_[p] → ℚ_[p] → L and O → L)
  have hinjL : Function.Injective (algebraMap ℤ_[p] D.L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] D.L]
    exact (algebraMap ℚ_[p] D.L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hinj : Function.Injective (algebraMap ℤ_[p] D.O) := by
    intro a b hab
    apply hinjL
    rw [IsScalarTower.algebraMap_eq ℤ_[p] D.O D.L, RingHom.comp_apply, RingHom.comp_apply, hab]
  have hfp0 : algebraMap ℤ_[p] D.O (p : ℤ_[p]) ≠ 0 := by
    intro h
    exact (PadicInt.prime_p (p := p)).ne_zero (hinj (by rw [h, map_zero]))
  -- the lying-over containment and y ∈ m_O
  have hmaple : Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p]) ≤ maximalIdeal D.O := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (P := maximalIdeal D.O) (p := maximalIdeal ℤ_[p]))
  have hymem : y ∈ maximalIdeal D.O := by
    have hpow := hEis.isWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      hyroot hg g.natDegree (le_of_eq (hg.natDegree_map _))
    exact (Ideal.IsMaximal.isPrime inferInstance).mem_of_pow_mem g.natDegree (hmaple hpow)
  -- Eisenstein coefficient data: g.coeff i = p * c i for i < deg, with c 0 a UNIT
  have hcoeff : ∀ i, i < g.natDegree → ∃ cc : ℤ_[p], g.coeff i = (p : ℤ_[p]) * cc := by
    intro i hi
    have hmemi := hEis.mem hi
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmemi
  choose! c hc using hcoeff
  have hc0unit : IsUnit (c 0) := by
    by_contra hcu
    have hc0m : c 0 ∈ maximalIdeal ℤ_[p] := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcu)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hc0m
    obtain ⟨d, hd⟩ := hc0m
    apply hEis.notMem
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨d, by rw [hc 0 hdeg, hd]; ring⟩
  -- expand aeval y g = 0 into the coefficient sum and peel both ends
  have hexp : ∑ i ∈ Finset.range (g.natDegree + 1),
      algebraMap ℤ_[p] D.O (g.coeff i) * y ^ i = 0 := by
    calc ∑ i ∈ Finset.range (g.natDegree + 1), algebraMap ℤ_[p] D.O (g.coeff i) * y ^ i
        = ∑ i ∈ Finset.range (g.natDegree + 1), g.coeff i • y ^ i :=
          Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
      _ = Polynomial.aeval y g := (Polynomial.aeval_eq_sum_range y).symm
      _ = 0 := hyroot
  rw [Finset.sum_range_succ, hg.coeff_natDegree, map_one, one_mul] at hexp
  obtain ⟨m, hm⟩ : ∃ m, g.natDegree = m + 1 := ⟨g.natDegree - 1, by omega⟩
  rw [hm, Finset.sum_range_succ', pow_zero, mul_one] at hexp
  -- hexp : (∑ i ∈ range m, a_{i+1}·y^{i+1}) + a₀ + y^(m+1) = 0
  set w : D.O := ∑ i ∈ Finset.range m, algebraMap ℤ_[p] D.O (c (i + 1)) * y ^ (i + 1) with hwdef
  have hsum : ∑ i ∈ Finset.range m, algebraMap ℤ_[p] D.O (g.coeff (i + 1)) * y ^ (i + 1)
      = algebraMap ℤ_[p] D.O (p : ℤ_[p]) * w := by
    rw [hwdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    rw [hc (i + 1) (by omega), map_mul, mul_assoc]
  have h2 : algebraMap ℤ_[p] D.O (g.coeff 0)
      = algebraMap ℤ_[p] D.O (p : ℤ_[p]) * algebraMap ℤ_[p] D.O (c 0) := by
    rw [← map_mul, ← hc 0 hdeg]
  -- THE KEY IDENTITY: y^(deg) = p · unit in O
  have hkey : y ^ (m + 1)
      = algebraMap ℤ_[p] D.O (p : ℤ_[p]) * -(algebraMap ℤ_[p] D.O (c 0) + w) := by
    linear_combination hexp - hsum - h2
  have hwmem : w ∈ maximalIdeal D.O := by
    rw [hwdef]
    refine Ideal.sum_mem _ fun i hi => ?_
    exact Ideal.mul_mem_left _ _ (by rw [pow_succ]; exact Ideal.mul_mem_left _ _ hymem)
  have hu0unit : IsUnit (algebraMap ℤ_[p] D.O (c 0) + w) :=
    isUnit_add_of_mem_maximalIdeal (hc0unit.map (algebraMap ℤ_[p] D.O)) hwmem
  -- y ≠ 0
  have hy0 : y ≠ 0 := by
    intro h0
    have hz : algebraMap ℤ_[p] D.O (p : ℤ_[p]) * -(algebraMap ℤ_[p] D.O (c 0) + w) = 0 := by
      rw [← hkey, h0, zero_pow (by omega : m + 1 ≠ 0)]
    rcases mul_eq_zero.mp hz with h | h
    · exact hfp0 h
    · exact hu0unit.ne_zero (neg_eq_zero.mp h)
  -- DVR structure: y = u · ϖ^k with k ≥ 1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.O
  obtain ⟨k, u, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, mul_one] at hyk
    exact mem_nonunits_iff.mp ((mem_maximalIdeal y).mp hymem) (hyk ▸ u.isUnit)
  -- p and ϖ^(k(m+1)) are associated in O
  have hassoc1 : Associated (algebraMap ℤ_[p] D.O (p : ℤ_[p])) (y ^ (m + 1)) := by
    obtain ⟨vu, hvu⟩ := hu0unit.neg
    exact ⟨vu, by rw [hvu]; exact hkey.symm⟩
  have hassoc2 : Associated (y ^ (m + 1)) (ϖ ^ (k * (m + 1))) := by
    refine Associated.symm ⟨u ^ (m + 1), ?_⟩
    rw [hyk, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]
    ring
  have hassoc : Associated (algebraMap ℤ_[p] D.O (p : ℤ_[p])) (ϖ ^ (k * (m + 1))) :=
    hassoc1.trans hassoc2
  -- hence map(p·ℤ_p) = m_O^(k(m+1)), and ramificationIdx = k(m+1) by spec
  have hspan : Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      = maximalIdeal D.O ^ (k * (m + 1)) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hgt : ¬ Ideal.map (algebraMap ℤ_[p] D.O) (maximalIdeal ℤ_[p])
      ≤ maximalIdeal D.O ^ (k * (m + 1) + 1) := by
    rw [hspan, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    intro hdvd
    have hle := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hdvd
    rw [hϖ.addVal_pow, hϖ.addVal_pow] at hle
    have : k * (m + 1) + 1 ≤ k * (m + 1) := by exact_mod_cast hle
    omega
  have he_val : QpType.eOf p D = k * (m + 1) := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = k * (m + 1)
    exact Ideal.ramificationIdx_spec (le_of_eq hspan) hgt
  -- the fundamental identity e·f = [L:ℚ_p] = deg g
  have hbot : maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro hb
    have hpmem : (p : ℤ_[p]) ∈ (⊥ : Ideal ℤ_[p]) := by
      rw [← hb, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    exact (PadicInt.prime_p (p := p)).ne_zero (Ideal.mem_bot.mp hpmem)
  have hef : QpType.eOf p D * QpType.fOf p D = m + 1 := by
    show Ideal.ramificationIdx (maximalIdeal ℤ_[p]) (maximalIdeal D.O) *
      Ideal.inertiaDeg (maximalIdeal ℤ_[p]) (maximalIdeal D.O) = m + 1
    rw [Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (S := D.O) (K := ℚ_[p]) (L := D.L)
      hbot, D.finrank_eq, hm]
  -- conclude: k·(m+1)·f = m+1 forces k = 1 and f = 1
  have hkf : k * QpType.fOf p D = 1 := by
    have h3 : (m + 1) * (k * QpType.fOf p D) = (m + 1) * 1 := by
      rw [mul_one]
      calc (m + 1) * (k * QpType.fOf p D)
          = k * (m + 1) * QpType.fOf p D := by ring
        _ = QpType.eOf p D * QpType.fOf p D := by rw [he_val]
        _ = m + 1 := hef
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  have hk_eq : k = 1 := Nat.dvd_one.mp ⟨QpType.fOf p D, hkf.symm⟩
  have hf_eq : QpType.fOf p D = 1 := Nat.dvd_one.mp ⟨k, by rw [mul_comm]; exact hkf.symm⟩
  exact ⟨by rw [he_val, hk_eq, one_mul, ← hm], hf_eq⟩

/-- **`e = deg` for Eisenstein bundles** (FLAG-1 target 1, equality form). -/
theorem eOf_of_eisenstein {g : ℤ_[p][X]} (hg : g.Monic)
    (hEis : g.IsEisensteinAt (maximalIdeal ℤ_[p])) (hdeg : 0 < g.natDegree)
    (D : QpType.LocalFactorData p g) : QpType.eOf p D = g.natDegree :=
  (ef_of_eisenstein p hg hEis hdeg D).1

/-- **`f = 1` for Eisenstein bundles.** -/
theorem fOf_of_eisenstein {g : ℤ_[p][X]} (hg : g.Monic)
    (hEis : g.IsEisensteinAt (maximalIdeal ℤ_[p])) (hdeg : 0 < g.natDegree)
    (D : QpType.LocalFactorData p g) : QpType.fOf p D = 1 :=
  (ef_of_eisenstein p hg hEis hdeg D).2

/-- **`(e, f) = (deg, 1)` for Eisenstein bundles** (pair form). -/
theorem efOf_of_eisenstein {g : ℤ_[p][X]} (hg : g.Monic)
    (hEis : g.IsEisensteinAt (maximalIdeal ℤ_[p])) (hdeg : 0 < g.natDegree)
    (D : QpType.LocalFactorData p g) : QpType.efOf p D = (g.natDegree, 1) := by
  unfold QpType.efOf
  rw [eOf_of_eisenstein p hg hEis hdeg D, fOf_of_eisenstein p hg hEis hdeg D]

/-! ## Block 3 — the wild-gate corollary (positive coherence, FLAG-1 target 3) -/

/-- **The gate forces `(e, f) = (2, 1)`.** For a genuine monic quadratic in the level-`N`
classifier fiber of the Wave-1 wild gate shape, EVERY local-factor bundle carries
`efOf = (2, 1)` — machine-checked, no axiom. (In particular `eOf ≠ 1`: the fine-(e,f)
swap `{(1,2)}` is machine-refutable at the gate; see the mutation-probe evidence below.) -/
theorem gate_ef_forced {N : ℕ} (hN0 : 0 < N) (hN2 : 2 ≤ N) {f : ℤ_[2][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify 2 2 N (PadicLift.toBox 2 2 N hN0 f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape)
    (D : QpType.LocalFactorData 2 f) :
    QpType.efOf 2 D = (2, 1) := by
  obtain ⟨h0, h1⟩ := QpType.wildGateFiber_valuation 2 hN0 hN2 hf hdeg hfib
  have hEis := QpType.isEisensteinAt_of_wildGate 2 hf hdeg h0 h1
  have h := efOf_of_eisenstein 2 hf hEis (by omega) D
  rwa [hdeg] at h

/-- The gate's `eOf` is `2` (projection of `gate_ef_forced`; the mutation-refuting strength
`eOf ≥ 2`, hence `eOf ≠ 1`, follows). -/
theorem gate_eOf_forced {N : ℕ} (hN0 : 0 < N) (hN2 : 2 ≤ N) {f : ℤ_[2][X]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify 2 2 N (PadicLift.toBox 2 2 N hN0 f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape)
    (D : QpType.LocalFactorData 2 f) :
    QpType.eOf 2 D = 2 :=
  congrArg Prod.fst (gate_ef_forced hN0 hN2 hf hdeg hfib D)

/-! ## Block 4 — probe plumbing: reading a singleton `qpType` -/

/-- The `efOf` of any factor's bundle is a member of the factorization's type multiset. -/
theorem efOf_mem_qpType {f : ℤ_[p][X]} (F : QpType.QpFactorization p f) {g : ℤ_[p][X]}
    (hmem : g ∈ F.factors) :
    QpType.efOf p (F.data g hmem) ∈ (QpType.qpType p F).data := by
  show QpType.efOf p (F.data g hmem)
    ∈ ↑(F.factors.pmap (fun g hg => QpType.efOf p (F.data g hg)) (fun _ h => h))
  exact Multiset.mem_coe.mpr (List.mem_pmap.mpr ⟨g, hmem, rfl⟩)

/-- **Singleton types force the factor and its `(e, f)`.** If `qpType p F = {σef}` then the
factor list is exactly `[f]` and the carried bundle has `efOf = σef`. (This is what upgrades
the old count-only mutation probe to an (e,f)-payload probe.) -/
theorem qpType_singleton_forces {f : ℤ_[p][X]} (F : QpType.QpFactorization p f)
    (σef : ℕ × ℕ) (hσ : QpType.qpType p F = ⟨{σef}⟩) :
    ∃ hmem : f ∈ F.factors, QpType.efOf p (F.data f hmem) = σef := by
  have hlen : F.factors.length = 1 := by
    have hcard := congrArg (fun t => Multiset.card t.data) hσ
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, hfac⟩ := List.length_eq_one_iff.mp hlen
  have hg₁ : g₁ = f := by
    have hprod := F.prod_eq
    rw [hfac, List.prod_singleton] at hprod
    exact hprod
  subst hg₁
  have hmem : g₁ ∈ F.factors := by rw [hfac]; exact List.mem_singleton_self _
  refine ⟨hmem, ?_⟩
  have hin := efOf_mem_qpType p F hmem
  rw [hσ] at hin
  exact Multiset.mem_singleton.mp hin

/-! ## Block 4b — non-vacuity witness for the Eisenstein theorem (the U1 lesson)

`ef_of_eisenstein` is a conditional over `(hg, hEis, hdeg, D)`; the mandatory gate: exhibit a
concrete instance where ALL hypotheses hold simultaneously, so the theorem is not vacuously true
through an uninhabitable hypothesis set. Witness: `g = X + p` (monic, Eisenstein at `p·ℤ_[p]`,
degree 1) with the trivial bundle `L = ℚ_[p]`, `O = ℤ_[p]`, root `-p`. -/

/-- `X + p` is Eisenstein at `p·ℤ_[p]`. -/
theorem isEisensteinAt_X_add_p :
    (X + C (p : ℤ_[p])).IsEisensteinAt (maximalIdeal ℤ_[p]) := by
  constructor
  · rw [(monic_X_add_C _).leadingCoeff]
    intro hmem
    exact (Ideal.IsMaximal.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ hmem isUnit_one)
  · intro n hn
    rw [natDegree_X_add_C] at hn
    interval_cases n
    rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  · rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
    intro hmem
    have h2 := (PadicInt.mem_span_pow_iff_le_valuation _ (PadicInt.prime_p).ne_zero 2).mp hmem
    rw [PadicInt.valuation_p] at h2
    omega

/-- The degree-1 Eisenstein witness bundle: `g = X + p`, `L = ℚ_[p]`, `O = ℤ_[p]`. -/
noncomputable def eisWitnessData : QpType.LocalFactorData p (X + C (p : ℤ_[p])) where
  L := ℚ_[p]
  fieldL := inferInstance
  algQL := inferInstance
  algZL := inferInstance
  towerZQL := inferInstance
  finrank_eq := by rw [natDegree_X_add_C, Module.finrank_self]
  hasRoot := ⟨-(p : ℚ_[p]), by simp, Subsingleton.elim _ _⟩
  O := ℤ_[p]
  crO := inferInstance
  domO := inferInstance
  dvrO := inferInstance
  algZO := inferInstance
  algOL := inferInstance
  towerZOL := inferInstance
  intClosure := inferInstance
  liesOver := ⟨by simp [Ideal.under]⟩

/-- **Non-vacuity gate:** the Eisenstein theorem FIRES on the witness, with the correct value
`(e, f) = (deg, 1) = (1, 1)`. -/
theorem eisWitness_ef :
    QpType.eOf p (eisWitnessData p) = 1 ∧ QpType.fOf p (eisWitnessData p) = 1 := by
  have h := ef_of_eisenstein p (monic_X_add_C _) (isEisensteinAt_X_add_p p)
    (by rw [natDegree_X_add_C]; omega) (eisWitnessData p)
  rwa [natDegree_X_add_C] at h

/-! ## Block 5 — the upgraded mutation probe: the fine-(e,f) swap is refuted (evidence block)

**Mutation probe evidence (machine-checked 2026-07-21, scratch NOT committed).** The Wave-2
guardian audit FLAG 1 observed that the recorded probe (`OM/OmLeafFaithful.lean` Block 4) catches
only factor-COUNT mutations: a mutated axiom concluding the fine-(e,f)-swapped SINGLETON type
`{(1,2)}` (instead of the true `{(2,1)}`) still produces exactly one irreducible factor and
therefore PASSES the old probe. The following scratch module — the REAL axiom's hypotheses
verbatim, conclusion mutated to `{(1,2)}` — was compiled against this module and
`OM/OmLeafFaithful.lean`, and `lake env lean` accepted it with zero errors: `False` DERIVES from
the mutated axiom + `OmLeafFaithful.gateFiber_nonempty` + this module's AXIOM-FREE
`gate_ef_forced` / `qpType_singleton_forces`. The (e,f) PAYLOAD of the axiom's conclusion is
therefore machine-guarded at the gate, not cite-trusted: FLAG 1 is closed.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.QpTypeEisenstein

namespace LeanUrat.OM.QpTypeEisensteinScratch

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of `om_leaf_faithful` verbatim, conclusion
replaced by the fine-(e,f)-SWAPPED SINGLETON type `{(1,2)}` — a mutation the OLD (factor-count)
probe cannot catch, since the factorization still has exactly one factor. -/
axiom om_leaf_faithful_MUTATED_efswap (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (2 : ℕ))}⟩ : FactorizationType)

/-- The ef-swap mutation is REFUTED: at the inhabited gate fiber
(`OmLeafFaithful.gateFiber_nonempty`) it forces a singleton factorization whose unique factor is
`f0` itself with bundle payload `efOf = (1,2)` (`QpTypeEisenstein.qpType_singleton_forces`), but
the AXIOM-FREE Eisenstein theorem forces `efOf = (2,1)` for EVERY bundle on the gate fiber
(`QpTypeEisenstein.gate_ef_forced`). -/
theorem mutation_efswap_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := OmLeafFaithful.gateFiber_nonempty
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED_efswap 2 2 3 (by norm_num)
    (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) _ OmLeafFaithful.gate_mem_omMenuW
    f0 hf hdeg hfib
  obtain ⟨hmem, hef⟩ := QpTypeEisenstein.qpType_singleton_forces 2 F ((1 : ℕ), (2 : ℕ)) hF
  have hef2 : QpType.efOf 2 (F.data f0 hmem) = (2, 1) :=
    QpTypeEisenstein.gate_ef_forced (by norm_num) (by norm_num) hf hdeg hfib (F.data f0 hmem)
  rw [hef] at hef2
  exact absurd hef2 (by decide)

end LeanUrat.OM.QpTypeEisensteinScratch

#print axioms LeanUrat.OM.QpTypeEisensteinScratch.mutation_efswap_refuted
```

`lake env lean` output on the scratch (2026-07-21): NO errors; the single info line

```
'LeanUrat.OM.QpTypeEisensteinScratch.mutation_efswap_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.QpTypeEisensteinScratch.om_leaf_faithful_MUTATED_efswap]
```

i.e. `False` follows from the MUTATED axiom + Lean core + PROVED theorems alone — the real
`om_leaf_faithful` does NOT appear in the refutation's cone. Together with the recorded
split-type probe (`OM/OmLeafFaithful.lean` Block 4, factor count) and the positive coherence
(`OmLeafFaithful.gate_axiom_coherent` + `gate_ef_forced` above: the REAL conclusion `{(2,1)}` is
exactly what the machine forces), the axiom's gate payload is pinned in BOTH coordinates. -/

/-! ## Block 6 — axiom census (this module declares NO axiom; everything must be core-only) -/

section AxCheck

#print axioms LeanUrat.OM.QpTypeEisenstein.isUnit_add_of_mem_maximalIdeal
#print axioms LeanUrat.OM.QpTypeEisenstein.ef_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.eOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.fOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.efOf_of_eisenstein
#print axioms LeanUrat.OM.QpTypeEisenstein.gate_ef_forced
#print axioms LeanUrat.OM.QpTypeEisenstein.gate_eOf_forced
#print axioms LeanUrat.OM.QpTypeEisenstein.isEisensteinAt_X_add_p
#print axioms LeanUrat.OM.QpTypeEisenstein.eisWitnessData
#print axioms LeanUrat.OM.QpTypeEisenstein.eisWitness_ef
#print axioms LeanUrat.OM.QpTypeEisenstein.efOf_mem_qpType
#print axioms LeanUrat.OM.QpTypeEisenstein.qpType_singleton_forces

end AxCheck

end LeanUrat.OM.QpTypeEisenstein
