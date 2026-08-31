/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG56
import Uniformity.ChapH.H116b4a

/-!
# Uniformity.ChapI.IFCG61 — [IGV 2026-08-31] the per-depth cluster censuses: the
Igusa axis of the ramified convolution remainder — THE MIN-REDUCTION and the
`min = 1` box law at every degree

Stage IGV of the cone census (design record `runs/wave-c/verdict_IGV.md`; VCL's axis 1,
consuming RCD = `IFCG56` and the ring-level `monicPoly` kit of `H116b4a`).  RCD left the
depth-stratum ROOT COUNTS — the values `#depthPairSet O π n₁ n₂ L v` of the level-`L`
digit boxes at exact resultant depth `v` — as the census's named value input, with only
the `(1,1)` instance landed.  This file lands the structural reduction and the complete
`min = 1` axis:

* **§0 THE CLASS-LEVEL KIT.**  `mixDepth_eq_iff` (the exact-depth reader with NO lifts
  and NO irreducibility: `mixDepth = v ↔ mk π^v ∣ classRes ∧ ¬ mk π^{v+1} ∣ classRes`
  below the cap), `mk_pow_dvd_iff_le_resOrd` (class divisibility = windowed valuation),
  and the tail-polynomial instruments `polyOf` (`Σ bᵢ Xⁱ`, the NON-monic coefficient
  box) with its coefficient/degree readers.
* **§1 ★★ THE MIN-REDUCTION** (`classRes_eq_redRes` + `card_depthPairSet_reduce`): for
  `0 < n₁ ≤ n₂`, dividing the second monic frame by the first —
  `Res(f, g) = Res(f, g mod f)` at the pinned sizes, entirely over the truncation ring
  (mathlib's `resultant_add_mul_right` + `resultant_add_right_deg`, monic top
  coefficient `1`) — exhibits the depth-`v` stratum as a FULL cylinder over the REDUCED
  diagonal carrier `redDepthPairSet n₁` (monic × free box at size `n₁`):
  `#depthPairSet(n₁,n₂,N,v) = #redDepthPairSet(n₁,N,v) · q^{(n₂−n₁)N}`.
  Mechanism: the division Euclid map `(c₁,c₂) ↦ ((c₁, rem), quot)` is an explicit
  bijection with the (reduced pair) × (free quotient box) — `divSplit`, with the
  roundtrips run by `monicPoly_coeff_self_ring` and `div_modByMonic_unique`.  With
  ★ `card_depthPairSet_swap` (`resultant_comm`; the sign is a unit), EVERY box value
  at ANY `(n₁,n₂)` reduces to the diagonal reduced census at `min(n₁,n₂)` — **the
  depth law depends only on the minimum degree**.
* **§2 ★★ THE `min = 1` LAW AT EVERY DEGREE** (`card_depthPairSet_one_right`/`_left`):
  `redRes` at size `1` is the SECOND coordinate itself (`redRes_one`), so
  `#redDepthPairSet(1,N,v) = (q−1)q^{2N−v−1}` and
  `#depthPairSet(1,n₂,N,v) = (q−1)·q^{(1+n₂)N−v−1}` — i.e.
  `P[v(Res) = v] = (1−1/q)q^{−v}` for ALL degrees with `min = 1`, at every level,
  uniform in `q`.  RCD's `card_depthPairSet_one_one` is re-derived as an instance
  (the Lean-internal cross-check).
* **§3 THE URLIM PACKAGING.**  ★ `zcURLim_depthDensity_one_right`/`_left` — the
  normalized depth-density family at `min = 1` is `ZcURLim` OUTRIGHT with value
  `(q−1)/q^{v+1}` (numerator `X−1`, denominator `X^{v+1}`); and
  ★ `zcURLim_depthDensity_of_reduced` — at EVERY `0 < n₁ ≤ n₂` the depth-density
  `ZcURLim` follows from the reduced diagonal density `ZcURLim` at `n₁` (the exact
  cylinder identity; no error term).

## THE MASTER LAW (mathematics of record; general `m`, NOT transcribed to Lean here)

Unit IGV's derivation (verdict `runs/wave-c/verdict_IGV.md`): for random monic pairs
over any DVR with residue cardinality `q`, with `m = min(n₁,n₂)`, `s = 1/q`, the
exact-depth densities have generating function

    Σ_v P[v(Res) = v]·t^v  =  Z_m(t)  =  ∏_{j=1}^{m} (1 − s^j t^{j−1})/(1 − s^j t^j),

box form `#depthPairSet(n₁,n₂,L,v) = [t^v]Z_m · q^{(n₁+n₂)L}` (exact, `v < L`); mean
`E[v(Res)] = Σ_{j=1}^m 1/(q^j − 1)`.  Derivation chain: the min-reduction (§1 here, in
Lean) → norm formulation `∏ g(αᵢ) = N_{O[x]/f}(g mod f)` → Hensel localization along
the residual factorization (independent uniform local pieces) → the `r`-adic
Weierstrass/coprime-Hensel peel giving the local recursion
`B_e(1−(st)^{δe}) = Σ_{c<e}(s^δ)^c(1−s^δ)(t^δ)^c B_c`, solved by
`B_e = (s;st)_e/(st;st)_e` → Euler product over irreducibles collapsed by the `F_q[x]`
zeta and the `q`-binomial theorem.  Verified EXACTLY (integer-exact box counts, 17
configurations, `m = 1,2,3,4`, `p = 2,3,5`, depths through `v = 4`, boxes up to
16.7M pairs) — `runs/wave-c/igv_battery.py` + `igv_battery_heavy.log`.  The `m ≥ 2`
values enter Lean only through the named remainder below.

## THE HONEST FENCE

NOT proved here: (i) the diagonal reduced census values at `m ≥ 2` (the Lean
transcription of the localization/Weierstrass recursion — the exact named remainder of
VCL's axis 1 on the value side; the `min`-reduction above confines it to the diagonal);
(ii) the VIS-restriction: `zcURLim_visDepth_of_clusters`'s premise sums the cluster
census over the VISIBLE cells only — which visible cells the clusters land on (B.42's
block-grouping genre) is VCL's axis 3 territory and is untouched; (iii) VCL's axis 2
(the summed rationality across depths).  Nothing weakened; zero new axioms; every
consumed statement byte-untouched.

## Axiom fence (machine-exact at landing)

EVERY declaration in this file expects PURE Lean core
`{propext, Classical.choice, Quot.sound}` — the min-reduction, the swap, the `min = 1`
laws, and the URLim packagings consume only IFCG56 §1's Lean-core carrier, IFCG41's
Lean-core depth instruments, H116b4a's ring-level coefficient kit, and mathlib
resultant algebra.  B.42, the C.33 cites, and `AX_cellRecursion` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG61

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG24 (ZcURLim card_setOf_resOrd_eq)
open Uniformity.Density.IFCG41 (classRes mixDepth mixDepth_le mixDepth_dvd le_mixDepth
  mk_pow_dvd_mk_iff)
open Uniformity.Density.IFCG56 (depthPairSet card_depthPairSet_levels
  card_depthPairSet_one_one)

/-! ## §0 — the class-level kit -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The class-level exact-depth reader** — no lifts, no irreducibility: below the
window cap, `mixDepth = v` is exactly the pair of class divisibility conditions. -/
theorem mixDepth_eq_iff {π : O} {n₁ n₂ N v : ℕ} (hvN : v < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    mixDepth π c₁ c₂ = v
      ↔ ((Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v)) ∣ classRes c₁ c₂
          ∧ ¬ (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ (v + 1))) ∣ classRes c₁ c₂) := by
  have hstep : ∀ w u : ℕ, w ≤ u →
      (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ w))
        ∣ (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ u)) := by
    intro w u hwu
    refine ⟨Ideal.Quotient.mk _ (π ^ (u - w)), ?_⟩
    rw [← map_mul, ← pow_add]
    congr 2
    omega
  constructor
  · rintro rfl
    refine ⟨mixDepth_dvd π c₁ c₂, fun hcon => ?_⟩
    have := le_mixDepth π (by omega : mixDepth π c₁ c₂ + 1 ≤ N) hcon
    omega
  · rintro ⟨h1, h2⟩
    have hle : v ≤ mixDepth π c₁ c₂ := le_mixDepth π hvN.le h1
    have hgt : ¬ v + 1 ≤ mixDepth π c₁ c₂ := fun hcon =>
      h2 ((hstep (v + 1) _ hcon).trans (mixDepth_dvd π c₁ c₂))
    omega

/-- Class divisibility by `mk (π^k)` is the windowed-valuation threshold. -/
theorem mk_pow_dvd_iff_le_resOrd {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k ≤ N)
    (x : Res O N) :
    (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ k)) ∣ x ↔ k ≤ resOrd x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mk_pow_dvd_mk_iff hπ hk, resOrd_ge_iff hπ hk]

end Kit

section PolyOf

variable {R : Type*} [CommRing R]

/-- **The tail polynomial** of a coefficient vector: `Σᵢ bᵢ Xⁱ`, the general (non-monic)
degree-`< n` box member. -/
def polyOf {n : ℕ} (b : Fin n → R) : Polynomial R :=
  ∑ i : Fin n, C (b i) * X ^ (i : ℕ)

theorem polyOf_coeff_lt {n : ℕ} (b : Fin n → R) {i : ℕ} (hi : i < n) :
    (polyOf b).coeff i = b ⟨i, hi⟩ := by
  classical
  unfold polyOf
  rw [finsetSum_coeff, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro b' _ hbi
    have hne : i ≠ (b' : ℕ) := fun heq => hbi (Fin.ext heq.symm)
    rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
  · simp

/-- The tail polynomial has degree `< n` (over ANY commutative ring — no
nontriviality needed: there is no leading term to protect). -/
theorem polyOf_degree_lt {n : ℕ} (b : Fin n → R) :
    (polyOf b).degree < (n : WithBot ℕ) := by
  unfold polyOf
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le (i : ℕ) (b i)) ?_
  exact_mod_cast i.isLt

/-- Reconstruction: a polynomial of `natDegree < n` IS the tail polynomial of its
coefficient vector. -/
theorem polyOf_eq_self {n : ℕ} {p : Polynomial R} (hp : p.natDegree < n) :
    polyOf (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  ext k
  by_cases hk : k < n
  · rw [polyOf_coeff_lt _ hk]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (le_of_not_gt hk)),
      coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le (polyOf_degree_lt _) (by exact_mod_cast le_of_not_gt hk))]

end PolyOf

/-! ## §1 — ★★ THE MIN-REDUCTION -/

section MinReduction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The reduced diagonal resultant**: the pinned-size-`(n,n)` resultant of the monic
frame against the FREE (non-monic) tail box — the carrier the min-reduction lands on. -/
def redRes {n N : ℕ} (c b : Coeff O n N) : Res O N :=
  Polynomial.resultant (monicPoly c) (polyOf b) n n

/-- **The reduced depth-`v` stratum**: monic × free pairs at exact reduced-resultant
depth `v` (class divisibility form). -/
def redDepthPairSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n L v : ℕ) :
    Set (Coeff O n L × Coeff O n L) :=
  {d | (Ideal.Quotient.mk ((maximalIdeal O) ^ L) (π ^ v)) ∣ redRes d.1 d.2
    ∧ ¬ (Ideal.Quotient.mk ((maximalIdeal O) ^ L) (π ^ (v + 1))) ∣ redRes d.1 d.2}

/-- The remainder coefficient vector of the division `monicPoly c₂ = monicPoly c₁ · Q + r`. -/
def remCoeff {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) : Coeff O n₁ N :=
  fun i => ((monicPoly c₂) %ₘ (monicPoly c₁)).coeff (i : ℕ)

/-- The quotient coefficient vector of the same division. -/
def quotCoeff {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    Coeff O (n₂ - n₁) N :=
  fun i => ((monicPoly c₂) /ₘ (monicPoly c₁)).coeff (i : ℕ)

/-- The rebuilt coefficient vector `monicPoly c₁ · monicPoly e + polyOf b`. -/
def buildCoeff {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (b : Coeff O n₁ N)
    (e : Coeff O (n₂ - n₁) N) : Coeff O n₂ N :=
  fun i => (monicPoly c₁ * monicPoly e + polyOf b).coeff (i : ℕ)

variable {n₁ n₂ N : ℕ}

private theorem rem_natDegree_lt (h1 : 0 < n₁) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    ((monicPoly c₂) %ₘ (monicPoly c₁)).natDegree < n₁ := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hfd : (monicPoly c₁).natDegree = n₁ := monicPoly_natDegree_ring c₁
  have hne1 : (monicPoly c₁) ≠ 1 := fun hcon => by
    rw [hcon] at hfd
    simp at hfd
    omega
  have := natDegree_modByMonic_lt (monicPoly c₂) (monicPoly_monic_ring c₁) hne1
  omega

/-- The remainder IS the tail polynomial of `remCoeff`. -/
theorem polyOf_remCoeff (h1 : 0 < n₁) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    polyOf (remCoeff c₁ c₂) = (monicPoly c₂) %ₘ (monicPoly c₁) :=
  polyOf_eq_self (rem_natDegree_lt h1 hN c₁ c₂)

private theorem quot_natDegree (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    ((monicPoly c₂) /ₘ (monicPoly c₁)).natDegree = n₂ - n₁ := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  rw [natDegree_divByMonic _ (monicPoly_monic_ring c₁), monicPoly_natDegree_ring,
    monicPoly_natDegree_ring]

private theorem quot_monic (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    ((monicPoly c₂) /ₘ (monicPoly c₁)).Monic := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hf : (monicPoly c₁).Monic := monicPoly_monic_ring c₁
  have hfd : (monicPoly c₁).natDegree = n₁ := monicPoly_natDegree_ring c₁
  have hgd : (monicPoly c₂).natDegree = n₂ := monicPoly_natDegree_ring c₂
  -- read the top coefficient of `g = rem + f·quot` at `n₂`
  have hsplit := modByMonic_add_div (monicPoly c₂) (monicPoly c₁)
  have htop : (monicPoly c₂).coeff n₂ = 1 := by
    have h' := (monicPoly_monic_ring c₂).coeff_natDegree
    rwa [hgd] at h'
  have hrem : ((monicPoly c₂) %ₘ (monicPoly c₁)).coeff n₂ = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (rem_natDegree_lt h1 hN c₁ c₂) hn)
  have hmul : ((monicPoly c₁) * ((monicPoly c₂) /ₘ (monicPoly c₁))).coeff n₂
      = ((monicPoly c₂) /ₘ (monicPoly c₁)).leadingCoeff := by
    have h' := coeff_mul_degree_add_degree (monicPoly c₁)
      ((monicPoly c₂) /ₘ (monicPoly c₁))
    rw [hfd, quot_natDegree hN c₁ c₂, hf.leadingCoeff, one_mul] at h'
    have hsum : n₁ + (n₂ - n₁) = n₂ := by omega
    rwa [hsum] at h'
  have hcoeff : ((monicPoly c₂) %ₘ (monicPoly c₁)).coeff n₂
      + ((monicPoly c₁) * ((monicPoly c₂) /ₘ (monicPoly c₁))).coeff n₂
      = (monicPoly c₂).coeff n₂ := by
    rw [← coeff_add, hsplit]
  rw [hrem, zero_add, hmul, htop] at hcoeff
  exact hcoeff

/-- The quotient IS the monic frame of `quotCoeff`. -/
theorem monicPoly_quotCoeff (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    monicPoly (quotCoeff c₁ c₂) = (monicPoly c₂) /ₘ (monicPoly c₁) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  exact monicPoly_coeff_self_ring (quot_monic h1 hn hN c₁ c₂) (quot_natDegree hN c₁ c₂)

/-- ★★ **THE MIN-REDUCTION IDENTITY**: the class resultant at sizes `(n₁, n₂)` IS the
reduced diagonal resultant of the division remainder at size `(n₁, n₁)` — mathlib's
`Res(f, g + f·p) = Res(f, g)` plus the monic size-drop, entirely over the truncation
ring. -/
theorem classRes_eq_redRes (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    classRes c₁ c₂ = redRes c₁ (remCoeff c₁ c₂) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hf : (monicPoly c₁).Monic := monicPoly_monic_ring c₁
  have hfd : (monicPoly c₁).natDegree = n₁ := monicPoly_natDegree_ring c₁
  show Polynomial.resultant (monicPoly c₁) (monicPoly c₂) n₁ n₂ = _
  rw [redRes, polyOf_remCoeff h1 hN c₁ c₂]
  conv_lhs => rw [← modByMonic_add_div (monicPoly c₂) (monicPoly c₁)]
  rw [Polynomial.resultant_add_mul_right (monicPoly c₁)
    ((monicPoly c₂) %ₘ (monicPoly c₁)) ((monicPoly c₂) /ₘ (monicPoly c₁)) n₁ n₂
    (by rw [quot_natDegree hN c₁ c₂]; omega)
    (le_of_eq hfd)]
  have hrd : ((monicPoly c₂) %ₘ (monicPoly c₁)).natDegree ≤ n₁ :=
    (rem_natDegree_lt h1 hN c₁ c₂).le
  have h := Polynomial.resultant_add_right_deg (f := monicPoly c₁)
    (g := (monicPoly c₂) %ₘ (monicPoly c₁)) (m := n₁) (n := n₁) (n₂ - n₁) hrd
  have hexp : n₁ + (n₂ - n₁) = n₂ := by omega
  rw [hexp] at h
  have hc1 : (monicPoly c₁).coeff n₁ = 1 := by
    have h' := hf.coeff_natDegree
    rwa [hfd] at h'
  rw [h, hc1, one_pow, one_mul]

/-- Membership transport: the depth-`v` condition on the pair reads exactly on the
reduced pair `(c₁, remCoeff c₁ c₂)`. -/
theorem mem_depthPairSet_iff_red {π : O} {v : ℕ} (h1 : 0 < n₁) (hn : n₁ ≤ n₂)
    (hvN : v < N) (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    (c₁, c₂) ∈ depthPairSet O π n₁ n₂ N v
      ↔ (c₁, remCoeff c₁ c₂) ∈ redDepthPairSet O π n₁ N v := by
  have hN : 0 < N := by omega
  simp only [depthPairSet, redDepthPairSet, Set.mem_setOf_eq]
  rw [mixDepth_eq_iff hvN, classRes_eq_redRes h1 hn hN]

private theorem build_roundtrip (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    buildCoeff c₁ (remCoeff c₁ c₂) (quotCoeff c₁ c₂) = c₂ := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  funext i
  show (monicPoly c₁ * monicPoly (quotCoeff c₁ c₂) + polyOf (remCoeff c₁ c₂)).coeff _
      = c₂ i
  rw [monicPoly_quotCoeff h1 hn hN c₁ c₂, polyOf_remCoeff h1 hN c₁ c₂, add_comm,
    modByMonic_add_div (monicPoly c₂) (monicPoly c₁),
    monicPoly_coeff_lt_ring c₂ i.isLt]

private theorem monicPoly_buildCoeff (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ b : Coeff O n₁ N) (e : Coeff O (n₂ - n₁) N) :
    monicPoly (buildCoeff c₁ b e) = monicPoly c₁ * monicPoly e + polyOf b := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hf : (monicPoly c₁).Monic := monicPoly_monic_ring c₁
  have he : (monicPoly e).Monic := monicPoly_monic_ring e
  have hmulmonic : (monicPoly c₁ * monicPoly e).Monic := hf.mul he
  have hmuldeg : (monicPoly c₁ * monicPoly e).natDegree = n₂ := by
    rw [hf.natDegree_mul he, monicPoly_natDegree_ring, monicPoly_natDegree_ring]
    omega
  have hlt : (polyOf b).degree < (monicPoly c₁ * monicPoly e).degree := by
    rw [degree_eq_natDegree hmulmonic.ne_zero, hmuldeg]
    exact lt_of_lt_of_le (polyOf_degree_lt b) (by exact_mod_cast hn)
  have hFm : (monicPoly c₁ * monicPoly e + polyOf b).Monic := hmulmonic.add_of_left hlt
  have hFd : (monicPoly c₁ * monicPoly e + polyOf b).natDegree = n₂ := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hlt)]
    exact hmuldeg
  exact monicPoly_coeff_self_ring hFm hFd

private theorem rem_quot_build (hn : n₁ ≤ n₂) (hN : 0 < N)
    (c₁ b : Coeff O n₁ N) (e : Coeff O (n₂ - n₁) N) :
    remCoeff c₁ (buildCoeff c₁ b e) = b ∧ quotCoeff c₁ (buildCoeff c₁ b e) = e := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hf : (monicPoly c₁).Monic := monicPoly_monic_ring c₁
  have hkey : monicPoly (buildCoeff c₁ b e) /ₘ (monicPoly c₁) = monicPoly e
      ∧ monicPoly (buildCoeff c₁ b e) %ₘ (monicPoly c₁) = polyOf b := by
    refine div_modByMonic_unique (monicPoly e) (polyOf b) hf ⟨?_, ?_⟩
    · rw [monicPoly_buildCoeff hn hN c₁ b e]
      ring
    · rw [degree_eq_natDegree hf.ne_zero, monicPoly_natDegree_ring]
      exact polyOf_degree_lt b
  constructor
  · funext i
    show (monicPoly (buildCoeff c₁ b e) %ₘ (monicPoly c₁)).coeff _ = b i
    rw [hkey.2, polyOf_coeff_lt _ i.isLt]
  · funext i
    show (monicPoly (buildCoeff c₁ b e) /ₘ (monicPoly c₁)).coeff _ = e i
    rw [hkey.1, monicPoly_coeff_lt_ring e i.isLt]

/-- **The division split**: the Euclid map is an explicit bijection between the pair box
at `(n₁, n₂)` and (reduced diagonal pairs at `n₁`) × (the free quotient box). -/
private def divSplit (h1 : 0 < n₁) (hn : n₁ ≤ n₂) (hN : 0 < N) :
    (Coeff O n₁ N × Coeff O n₂ N) ≃ ((Coeff O n₁ N × Coeff O n₁ N) × Coeff O (n₂ - n₁) N) where
  toFun d := ((d.1, remCoeff d.1 d.2), quotCoeff d.1 d.2)
  invFun p := (p.1.1, buildCoeff p.1.1 p.1.2 p.2)
  left_inv d := by
    obtain ⟨c₁, c₂⟩ := d
    exact Prod.ext rfl (build_roundtrip h1 hn hN c₁ c₂)
  right_inv p := by
    obtain ⟨⟨c₁, b⟩, e⟩ := p
    have h := rem_quot_build hn hN c₁ b e
    exact Prod.ext (Prod.ext rfl h.1) h.2

private theorem natCard_prod_set {α β : Type*} (s : Set α) (t : Set β) :
    Nat.card (s ×ˢ t : Set (α × β)) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.Set.prod s t)

/-- ★★ **THE MIN-REDUCTION COUNT**: the depth-`v` stratum at sizes `(n₁, n₂)` is a FULL
cylinder over the reduced diagonal stratum at size `n₁` — every box value reduces to
the diagonal reduced census at the minimum degree.  No irreducibility hypothesis. -/
theorem card_depthPairSet_reduce {π : O} {v : ℕ} (h1 : 0 < n₁) (hn : n₁ ≤ n₂)
    (hvN : v < N) :
    Nat.card (depthPairSet O π n₁ n₂ N v)
      = Nat.card (redDepthPairSet O π n₁ N v) * residueCard O ^ ((n₂ - n₁) * N) := by
  have hN : 0 < N := by omega
  have himg : (divSplit (O := O) h1 hn hN) '' (depthPairSet O π n₁ n₂ N v)
      = (redDepthPairSet O π n₁ N v) ×ˢ (Set.univ : Set (Coeff O (n₂ - n₁) N)) := by
    ext p
    constructor
    · rintro ⟨⟨c₁, c₂⟩, hmem, rfl⟩
      exact ⟨(mem_depthPairSet_iff_red h1 hn hvN c₁ c₂).mp hmem, Set.mem_univ _⟩
    · rintro ⟨hmem, -⟩
      obtain ⟨⟨c₁, b⟩, e⟩ := p
      refine ⟨(c₁, buildCoeff c₁ b e), ?_, ?_⟩
      · rw [mem_depthPairSet_iff_red h1 hn hvN, (rem_quot_build hn hN c₁ b e).1]
        exact hmem
      · show ((c₁, remCoeff c₁ (buildCoeff c₁ b e)), quotCoeff c₁ (buildCoeff c₁ b e)) = _
        rw [(rem_quot_build hn hN c₁ b e).1, (rem_quot_build hn hN c₁ b e).2]
  calc Nat.card (depthPairSet O π n₁ n₂ N v)
      = Nat.card ((divSplit (O := O) h1 hn hN) '' (depthPairSet O π n₁ n₂ N v)) :=
        (Nat.card_image_of_injective (divSplit (O := O) h1 hn hN).injective _).symm
    _ = Nat.card (redDepthPairSet O π n₁ N v)
          * Nat.card (Set.univ : Set (Coeff O (n₂ - n₁) N)) := by
        rw [himg, natCard_prod_set]
    _ = Nat.card (redDepthPairSet O π n₁ N v) * residueCard O ^ ((n₂ - n₁) * N) := by
        rw [Nat.card_coe_set_eq (Set.univ : Set (Coeff O (n₂ - n₁) N)), Set.ncard_univ,
          card_coeff]

/-- The mixing depth is symmetric in the two frames (`resultant_comm`; the sign
`(−1)^{n₁n₂}` is a unit and does not move divisibility). -/
theorem mixDepth_swap {π : O} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    mixDepth π c₂ c₁ = mixDepth π c₁ c₂ := by
  have hsq : ((-1 : Res O N)) ^ (n₂ * n₁) * ((-1 : Res O N)) ^ (n₂ * n₁) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n₂ * n₁, rfl⟩
  have key : ∀ w : ℕ,
      ((Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ w)) ∣ classRes c₂ c₁
        ↔ (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ w)) ∣ classRes c₁ c₂) := by
    intro w
    have hcomm : classRes c₂ c₁
        = (-1 : Res O N) ^ (n₂ * n₁) * classRes c₁ c₂ := by
      show Polynomial.resultant (monicPoly c₂) (monicPoly c₁) n₂ n₁ = _
      exact Polynomial.resultant_comm (monicPoly c₂) (monicPoly c₁) n₂ n₁
    rw [hcomm]
    constructor
    · intro h
      have h2 := h.mul_left ((-1 : Res O N) ^ (n₂ * n₁))
      rwa [← mul_assoc, hsq, one_mul] at h2
    · intro h
      exact h.mul_left _
  apply le_antisymm
  · exact le_mixDepth π (mixDepth_le π c₂ c₁) ((key _).mp (mixDepth_dvd π c₂ c₁))
  · exact le_mixDepth π (mixDepth_le π c₁ c₂) ((key _).mpr (mixDepth_dvd π c₁ c₂))

/-- ★ **The swap**: the box values are symmetric in `(n₁, n₂)` — with the reduction,
every box value rests on the diagonal reduced census at `min(n₁, n₂)`. -/
theorem card_depthPairSet_swap {π : O} (n₁ n₂ N v : ℕ) :
    Nat.card (depthPairSet O π n₁ n₂ N v) = Nat.card (depthPairSet O π n₂ n₁ N v) := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodComm (Coeff O n₁ N) (Coeff O n₂ N)) ?_)
  rintro ⟨c₁, c₂⟩
  show mixDepth π c₁ c₂ = v ↔ mixDepth π c₂ c₁ = v
  rw [mixDepth_swap]

end MinReduction

/-! ## §2 — ★★ the `min = 1` law at every degree -/

section MinOne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- At size `1` the reduced resultant IS the second coordinate: `Res(X + a₀, b₀)` at
pinned sizes `(1,1)` is `b₀` (pure computation, valid over any ring). -/
theorem redRes_one {N : ℕ} (c b : Coeff O 1 N) : redRes c b = b 0 := by
  have hpoly : polyOf b = C (b 0) := by
    unfold polyOf
    rw [Fin.sum_univ_one]
    simp
  have h := Polynomial.resultant_add_right_deg (f := monicPoly c) (g := C (b 0))
    (m := 1) (n := 0) 1 (le_of_eq (natDegree_C _))
  rw [zero_add] at h
  have hc : (monicPoly c).coeff 1 = 1 := by
    unfold monicPoly
    rw [coeff_add, coeff_X_pow, if_pos rfl, Fin.sum_univ_one]
    simp
  show Polynomial.resultant (monicPoly c) (polyOf b) 1 1 = b 0
  rw [hpoly, h, Polynomial.resultant_C_zero_right, hc, one_pow, one_mul, pow_one]

/-- ★ **The reduced diagonal census at size `1`**: `(q−1)·q^{2N−v−1}` — the `(1,1)` law
on the reduced carrier. -/
theorem card_redDepthPairSet_one {π : O} (hπ : Irreducible π) {N v : ℕ} (hvN : v < N) :
    Nat.card (redDepthPairSet O π 1 N v)
      = (residueCard O - 1) * residueCard O ^ (2 * N - v - 1) := by
  classical
  set φ : (Coeff O 1 N × Coeff O 1 N) →+ Res O N :=
    { toFun := fun d => d.2 0
      map_zero' := rfl
      map_add' := fun _ _ => rfl } with hφ
  have hsurj : Function.Surjective φ := fun z => ⟨((fun _ => 0), (fun _ => z)), rfl⟩
  have hset : redDepthPairSet O π 1 N v = φ ⁻¹' {x : Res O N | resOrd x = v} := by
    ext ⟨c, b⟩
    simp only [redDepthPairSet, Set.mem_setOf_eq, Set.mem_preimage]
    rw [redRes_one c b]
    show _ ↔ resOrd (b 0) = v
    rw [mk_pow_dvd_iff_le_resOrd hπ hvN.le, mk_pow_dvd_iff_le_resOrd hπ hvN]
    omega
  have hker : Nat.card φ.ker = residueCard O ^ N := by
    have h2 := card_preimage_of_surjective φ hsurj Set.univ
    rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ,
      Nat.card_coe_set_eq (Set.univ : Set (Res O N)), Set.ncard_univ,
      Nat.card_prod, card_coeff, card_res] at h2
    have hqpos : 0 < residueCard O ^ N := pow_pos (residueCard_pos O) _
    refine Nat.eq_of_mul_eq_mul_right hqpos ?_
    rw [← h2, one_mul]
  have hexp : N + (N - v - 1) = 2 * N - v - 1 := by omega
  rw [hset, card_preimage_of_surjective φ hsurj, hker, card_setOf_resOrd_eq hvN,
    ← mul_assoc, mul_comm (residueCard O ^ N), mul_assoc, ← pow_add, hexp]

/-- ★★ **THE `min = 1` LAW AT EVERY DEGREE** (right form):
`#depthPairSet(1, n₂, N, v) = (q−1)·q^{(1+n₂)N − v − 1}`, i.e.
`P[v(Res) = v] = (1 − 1/q)·q^{−v}` for ALL `n₂ ≥ 1`, at every level, uniform in `q`. -/
theorem card_depthPairSet_one_right {π : O} (hπ : Irreducible π) {n₂ N v : ℕ}
    (hn : 1 ≤ n₂) (hvN : v < N) :
    Nat.card (depthPairSet O π 1 n₂ N v)
      = (residueCard O - 1) * residueCard O ^ ((1 + n₂) * N - v - 1) := by
  rw [card_depthPairSet_reduce one_pos hn hvN, card_redDepthPairSet_one hπ hvN,
    mul_assoc, ← pow_add]
  have h1 : (1 + n₂) * N = N + n₂ * N := by ring
  have h2 : (n₂ - 1) * N = n₂ * N - N := by
    rw [Nat.sub_mul, one_mul]
  have h3 : N ≤ n₂ * N := Nat.le_mul_of_pos_left N (by omega)
  have hexp : 2 * N - v - 1 + (n₂ - 1) * N = (1 + n₂) * N - v - 1 := by omega
  rw [hexp]

/-- ★★ The `min = 1` law, left form (via the swap). -/
theorem card_depthPairSet_one_left {π : O} (hπ : Irreducible π) {n₁ N v : ℕ}
    (hn : 1 ≤ n₁) (hvN : v < N) :
    Nat.card (depthPairSet O π n₁ 1 N v)
      = (residueCard O - 1) * residueCard O ^ ((n₁ + 1) * N - v - 1) := by
  rw [card_depthPairSet_swap, card_depthPairSet_one_right hπ hn hvN, Nat.add_comm 1 n₁]

/-- Lean-internal cross-check: RCD's landed `(1,1)` value is the `n₂ = 1, N = v + 1`
instance of the new law. -/
example {π : O} (hπ : Irreducible π) (v : ℕ) :
    Nat.card (depthPairSet O π 1 1 (v + 1) v)
      = (residueCard O - 1) * residueCard O ^ (v + 1) := by
  have hexp : (1 + 1) * (v + 1) - v - 1 = v + 1 := by omega
  rw [card_depthPairSet_one_right hπ le_rfl (Nat.lt_succ_self v), hexp]

end MinOne

/-! ## §3 — the URLim packaging -/

section URLim

/-- ★ **The reduced-to-general `ZcURLim` transport**: at every `0 < n₁ ≤ n₂`, the
depth-density `ZcURLim` follows from the reduced diagonal density `ZcURLim` at `n₁` —
the min-reduction is an exact cylinder identity, so the two normalized families agree
from level `v + 1` on. -/
theorem zcURLim_depthDensity_of_reduced {n₁ n₂ v : ℕ} (h1 : 0 < n₁) (hn : n₁ ≤ n₂)
    (hred : ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (redDepthPairSet O π n₁ M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (2 * n₁ * M))) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π n₁ n₂ M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * M)) := by
  obtain ⟨p, d, hd0, h⟩ := hred
  refine ⟨p, d, hd0, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hde, htend⟩ := h O
  refine ⟨hde, fun π hπ => ?_⟩
  refine Filter.Tendsto.congr' ?_ (htend π hπ)
  refine Filter.eventually_atTop.mpr ⟨v + 1, fun M hM => ?_⟩
  simp only []
  have hqR : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast residueCard_pos O
  rw [card_depthPairSet_reduce h1 hn (by omega : v < M)]
  have hexp : (n₁ + n₂) * M = 2 * n₁ * M + (n₂ - n₁) * M := by
    have h : n₁ + n₂ = 2 * n₁ + (n₂ - n₁) := by omega
    rw [h, Nat.add_mul]
  rw [hexp, pow_add]
  push_cast
  rw [div_eq_div_iff (ne_of_gt (pow_pos hqR _))
    (ne_of_gt (mul_pos (pow_pos hqR _) (pow_pos hqR _)))]
  ring

/-- ★★ **The `min = 1` depth-density `ZcURLim`, OUTRIGHT** (right form): numerator
`X − 1`, denominator `X^{v+1}` — the value `(q−1)/q^{v+1}` at every `n₂ ≥ 1`. -/
theorem zcURLim_depthDensity_one_right (n₂ v : ℕ) (hn : 1 ≤ n₂) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π 1 n₂ M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((1 + n₂) * M)) := by
  refine ⟨Polynomial.X - 1, Polynomial.X ^ (v + 1),
    pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : residueCard O ≠ 0)
  have hqR : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < residueCard O)
  refine ⟨by rw [Polynomial.eval_pow, Polynomial.eval_X]; exact pow_ne_zero _ hq0, ?_⟩
  intro π hπ
  have hval : ((((Polynomial.X - 1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ))
      / ((Polynomial.X ^ (v + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ (v + 1) := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    push_cast
    ring
  rw [hval]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨v + 1, fun M hM => ?_⟩
  simp only []
  have hMle : v + 1 ≤ (1 + n₂) * M :=
    le_trans hM (Nat.le_mul_of_pos_left M (by omega))
  have hden : ((residueCard O : ℕ) : ℝ) ^ ((1 + n₂) * M)
      = ((residueCard O : ℕ) : ℝ) ^ ((1 + n₂) * M - v - 1)
        * ((residueCard O : ℕ) : ℝ) ^ (v + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [card_depthPairSet_one_right hπ hn (by omega : v < M), hden]
  push_cast [Nat.cast_sub (by omega : 1 ≤ residueCard O)]
  rw [div_eq_div_iff (ne_of_gt (pow_pos hqR _))
    (ne_of_gt (mul_pos (pow_pos hqR _) (pow_pos hqR _)))]
  ring

/-- ★ The `min = 1` depth-density `ZcURLim`, left form. -/
theorem zcURLim_depthDensity_one_left (n₁ v : ℕ) (hn : 1 ≤ n₁) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π n₁ 1 M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + 1) * M)) := by
  have h := zcURLim_depthDensity_one_right n₁ v hn
  refine h.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [card_depthPairSet_swap, Nat.add_comm 1 n₁]

end URLim

end Uniformity.Density.IFCG61

end

/-! ## AXCHECK FOOTER — EVERY row expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG61.mixDepth_eq_iff
#print axioms Uniformity.Density.IFCG61.mk_pow_dvd_iff_le_resOrd
#print axioms Uniformity.Density.IFCG61.polyOf_eq_self
#print axioms Uniformity.Density.IFCG61.polyOf_remCoeff
#print axioms Uniformity.Density.IFCG61.monicPoly_quotCoeff
#print axioms Uniformity.Density.IFCG61.classRes_eq_redRes
#print axioms Uniformity.Density.IFCG61.mem_depthPairSet_iff_red
#print axioms Uniformity.Density.IFCG61.card_depthPairSet_reduce
#print axioms Uniformity.Density.IFCG61.mixDepth_swap
#print axioms Uniformity.Density.IFCG61.card_depthPairSet_swap
#print axioms Uniformity.Density.IFCG61.redRes_one
#print axioms Uniformity.Density.IFCG61.card_redDepthPairSet_one
#print axioms Uniformity.Density.IFCG61.card_depthPairSet_one_right
#print axioms Uniformity.Density.IFCG61.card_depthPairSet_one_left
#print axioms Uniformity.Density.IFCG61.zcURLim_depthDensity_of_reduced
#print axioms Uniformity.Density.IFCG61.zcURLim_depthDensity_one_right
#print axioms Uniformity.Density.IFCG61.zcURLim_depthDensity_one_left
