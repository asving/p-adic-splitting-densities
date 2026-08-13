/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Struct
import UniformityCheck.DeepSet

/-!
# UniformityCheck.N3Drain — how far the `n = 3` undecided mass drains

`N3Struct.cubic_structure` splits every monic cubic three ways; `N3Struct.decidedAt_of_peel`
kills the simple-root branch whenever the quadratic cofactor is not deeply tangent. What is
left is:

    undecidedSet O 3 N  ⊆  peelSet π N  ∪  tripleSet N            (`undecidedSet_subset`)

* `peelSet π N` — classes with a lift having a root `r` whose quadratic cofactor `peel a r`
  carries a centre of tangency depth `N`. **`#(peelSet π (2M)) ≤ q^{5M}`** out of `q^{6M}`
  (`card_peelSet_le`): the class is a function of `(r, g₀, g₁)` and `leanfinal`'s `class_pinned`
  pins `g₀` from `(γ mod π^M, g₁ mod π^{2M})`.
* `tripleSet N` — classes residually equal to `(X − γ̄)³`. **`#(tripleSet N)·q² ≤ q^{3N}`**
  (`card_tripleSet_le`): the level-1 truncation is one of `q` classes.

Consequences:

* `undecidedSeq_three_le` : `undecidedSeq O 3 (2M) ≤ (1/q)^M + 1/q²`;
* `upperDensity_three_le` : `upperDensity O 3 σ ≤ genuineDensity O 3 σ + 1/q²` — **the `n = 3`
  bracket between the certified density and the possible density closes to within `1/q²`**
  (`1/4` at `q = 2`, `1/9` at `q = 3`);
* `drainage_three_of_triple` : **full drainage at `n = 3` is EXACTLY drainage on the triple-root
  stratum.** Branch (b) is finished; the remaining obligation is a statement about residually
  perfect cubes only.

What the triple-root branch needs is diagnosed in `notes/N3_CHECK_2026-08-13.md` §9.4: a STRONG
Hensel lemma (`v(F(x₀)) > 2v(F′(x₀))` with `v(F′(x₀)) > 0`), which mathlib has only for `ℤ_[p]`
and which the coprime-factorization form of Hensel does NOT supply.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial Filter Topology

section Drain

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-! ## 1. The two strata -/

/-- **The branch-(b) stratum.** A level-`N` class with a lift `a` having a root `r` whose
quadratic cofactor `peel a r` carries a centre of tangency depth `N`. By `decidedAt_of_peel`
every undecided class with a simple residual root lies here. -/
def peelSet (π : O) (N : ℕ) : Set (Coeff O 3 N) :=
  {c | ∃ (a : Fin 3 → O) (r γ : O), proj O 3 N a = c ∧ (monicPoly a).eval r = 0 ∧
    Tang π (peel a r) N γ}

/-- **The triple-root stratum.** A level-`N` class whose residue cubic is `(X − γ̄)³`. -/
def tripleSet (N : ℕ) : Set (Coeff O 3 N) :=
  {c | ∃ (a : Fin 3 → O) (γ : O), proj O 3 N a = c ∧ resVec a = cubeCoeff (residue O γ)}

/-- The `q` level-1 classes that are residually perfect cubes. -/
def tripleRes (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] : Set (Coeff O 3 1) :=
  Set.range (fun γ : ResidueField O => liftRes1 (cubeCoeff γ))

/-- The level-1 class of `a` is the residue coefficient vector of `a`, read through
`res1Equiv`. -/
theorem proj_one_eq_liftRes1 (a : Fin 3 → O) : proj O 3 1 a = liftRes1 (resVec a) := by
  funext i
  refine (res1Equiv O).injective ?_
  show res1Equiv O (Ideal.Quotient.mk _ (a i)) = res1Equiv O ((res1Equiv O).symm (resVec a i))
  rw [res1Equiv_mk, RingEquiv.apply_symm_apply]
  rfl

/-! ## 2. Counting the triple-root stratum -/

theorem card_tripleRes_le : Nat.card (tripleRes O) ≤ residueCard O := by
  have hsurj : Function.Surjective
      (fun γ : ResidueField O => (⟨liftRes1 (cubeCoeff γ), ⟨γ, rfl⟩⟩ : tripleRes O)) := by
    rintro ⟨c, γ, rfl⟩
    exact ⟨γ, rfl⟩
  exact Nat.card_le_card_of_surjective _ hsurj

/-- **`#(tripleSet N) · q² ≤ q^{3N}`.** The residual perfect cubes occupy at most `q` of the
`q³` level-1 classes. -/
theorem card_tripleSet_le {N : ℕ} (hN : 1 ≤ N) :
    Nat.card (tripleSet (O := O) N) * residueCard O ^ 2 ≤ residueCard O ^ (3 * N) := by
  classical
  have hsub : tripleSet (O := O) N ⊆ (coeffFactor (O := O) 3 hN) ⁻¹' (tripleRes O) := by
    rintro c ⟨a, γ, rfl, hγ⟩
    exact ⟨residue O γ, by rw [coeffFactor_proj, proj_one_eq_liftRes1, hγ]⟩
  have hle1 : Nat.card (tripleSet (O := O) N)
      ≤ Nat.card ((coeffFactor (O := O) 3 hN) ⁻¹' (tripleRes O)) :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective _)
  have hcp := card_preimage_coeffFactor (O := O) 3 hN (tripleRes O)
  rw [card_coeff, card_coeff] at hcp
  have hq : 0 < residueCard O := residueCard_pos O
  refine Nat.le_of_mul_le_mul_right ?_ hq
  calc Nat.card (tripleSet (O := O) N) * residueCard O ^ 2 * residueCard O
      = Nat.card (tripleSet (O := O) N) * residueCard O ^ (3 * 1) := by ring
    _ ≤ Nat.card ((coeffFactor (O := O) 3 hN) ⁻¹' (tripleRes O)) * residueCard O ^ (3 * 1) :=
        Nat.mul_le_mul_right _ hle1
    _ = Nat.card (tripleRes O) * residueCard O ^ (3 * N) := hcp
    _ ≤ residueCard O * residueCard O ^ (3 * N) := Nat.mul_le_mul_right _ card_tripleRes_le
    _ = residueCard O ^ (3 * N) * residueCard O := by ring

/-! ## 3. Counting the branch-(b) stratum -/

/-- **`#(peelSet π (2M)) ≤ q^{5M}`.** The class is the function
`a = ![−r g₀, g₀ − g₁ r, g₁ − r]` of `(r, g₀, g₁)`, and `class_pinned'` recovers `g₀` from the
tangency centre mod `π^M` together with `g₁` mod `π^{2M}`. So `(r, γ, a₂)` mod
`(π^{2M}, π^M, π^{2M})` determines the class. -/
theorem card_peelSet_le {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (peelSet π (2 * M)) ≤ residueCard O ^ (5 * M) := by
  classical
  have key : ∀ c : peelSet π (2 * M), ∃ p : (Fin 3 → O) × O × O,
      proj O 3 (2 * M) p.1 = (c : Coeff O 3 (2 * M)) ∧ (monicPoly p.1).eval p.2.1 = 0 ∧
        Tang π (peel p.1 p.2.1) (2 * M) p.2.2 := by
    rintro ⟨c, a, r, γ, ha, hr, hT⟩
    exact ⟨(a, r, γ), ha, hr, hT⟩
  choose f hf1 hf2 hf3 using key
  have hinj : Function.Injective (fun c : peelSet π (2 * M) =>
      ((Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * M)) (f c).2.1,
        Ideal.Quotient.mk ((maximalIdeal O) ^ M) (f c).2.2,
        (c : Coeff O 3 (2 * M)) 2) : Res O (2 * M) × Res O M × Res O (2 * M))) := by
    intro c c' hcc
    have e1 : Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * M)) (f c).2.1
        = Ideal.Quotient.mk _ (f c').2.1 := congrArg Prod.fst hcc
    have e2 : Ideal.Quotient.mk ((maximalIdeal O) ^ M) (f c).2.2
        = Ideal.Quotient.mk _ (f c').2.2 := congrArg (fun x => x.2.1) hcc
    have e3 : (c : Coeff O 3 (2 * M)) 2 = (c' : Coeff O 3 (2 * M)) 2 :=
      congrArg (fun x => x.2.2) hcc
    have hr : π ^ (2 * M) ∣ ((f c').2.1 - (f c).2.1) :=
      (mem_maximalIdeal_pow_iff_dvd hπ _ _).1 (Ideal.Quotient.eq.1 e1.symm)
    have hγ : π ^ M ∣ ((f c').2.2 - (f c).2.2) :=
      (mem_maximalIdeal_pow_iff_dvd hπ _ _).1 (Ideal.Quotient.eq.1 e2.symm)
    have ea : (c : Coeff O 3 (2 * M)) 2 = Ideal.Quotient.mk _ ((f c).1 2) := by rw [← hf1 c]; rfl
    have ea' : (c' : Coeff O 3 (2 * M)) 2 = Ideal.Quotient.mk _ ((f c').1 2) := by
      rw [← hf1 c']; rfl
    have ha2 : π ^ (2 * M) ∣ ((f c').1 2 - (f c).1 2) :=
      (mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).1
        (Ideal.Quotient.eq.1 (by rw [← ea, ← ea']; exact e3.symm))
    -- the cofactors' linear coefficients agree, hence (class_pinned') so do their constants
    have hg1 : π ^ (2 * M) ∣ (peel (f c').1 (f c').2.1 1 - peel (f c).1 (f c).2.1 1) := by
      simp only [peel_one]
      have hid : ((f c').1 2 + (f c').2.1) - ((f c).1 2 + (f c).2.1)
          = ((f c').1 2 - (f c).1 2) + ((f c').2.1 - (f c).2.1) := by ring
      rw [hid]
      exact dvd_add ha2 hr
    have hg0 : π ^ (2 * M) ∣ (peel (f c').1 (f c').2.1 0 - peel (f c).1 (f c).2.1 0) :=
      class_pinned' (hf3 c) (hf3 c') hγ hg1
    -- rebuild the remaining coefficients from `(r, g₀, g₁)`
    have ha1 : π ^ (2 * M) ∣ ((f c').1 1 - (f c).1 1) := by
      have hid : (f c').1 1 - (f c).1 1
          = (peel (f c').1 (f c').2.1 0 - peel (f c).1 (f c).2.1 0)
            - (peel (f c').1 (f c').2.1 1 - peel (f c).1 (f c).2.1 1) * (f c').2.1
            - peel (f c).1 (f c).2.1 1 * ((f c').2.1 - (f c).2.1) := by
        simp only [peel_zero, peel_one]; ring
      rw [hid]
      exact dvd_sub (dvd_sub hg0 (hg1.mul_right _)) (hr.mul_left _)
    have ha0 : π ^ (2 * M) ∣ ((f c').1 0 - (f c).1 0) := by
      have hid : (f c').1 0 - (f c).1 0
          = -(((f c').2.1 - (f c).2.1) * peel (f c').1 (f c').2.1 0)
            - (f c).2.1 * (peel (f c').1 (f c').2.1 0 - peel (f c).1 (f c).2.1 0) := by
        rw [peel_const _ _ (hf2 c), peel_const _ _ (hf2 c')]; ring
      rw [hid]
      exact dvd_sub (dvd_neg.2 (hr.mul_right _)) (hg0.mul_left _)
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i
    · show (c : Coeff O 3 (2 * M)) 0 = (c' : Coeff O 3 (2 * M)) 0
      rw [← hf1 c, ← hf1 c']
      exact Ideal.Quotient.eq.2
        ((mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).2 (dvd_sub_comm.1 ha0))
    · show (c : Coeff O 3 (2 * M)) 1 = (c' : Coeff O 3 (2 * M)) 1
      rw [← hf1 c, ← hf1 c']
      exact Ideal.Quotient.eq.2
        ((mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).2 (dvd_sub_comm.1 ha1))
    · exact e3
  have hle := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_prod, card_res] at hle
  calc Nat.card (peelSet π (2 * M))
      ≤ residueCard O ^ (2 * M) * (residueCard O ^ M * residueCard O ^ (2 * M)) := hle
    _ = residueCard O ^ (5 * M) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring

/-! ## 4. The structure inclusion -/

/-- **THE DRAINAGE DICHOTOMY AT `n = 3`.** Every undecided level-`N` class (`N ≥ 1`) is either
branch-(b) tangent or residually a perfect cube. -/
theorem undecidedSet_subset {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N) :
    undecidedSet O 3 N ⊆ peelSet π N ∪ tripleSet N := by
  intro c hc
  obtain ⟨a, ha⟩ := proj_surjective O 3 N c
  rcases cubic_structure a with ⟨r, hr, hu⟩ | hno | ⟨γ, hγ⟩
  · by_cases hT : ∃ γ : O, Tang π (peel a r) N γ
    · obtain ⟨γ, hγ⟩ := hT
      exact Or.inl ⟨a, r, γ, ha, hr, hγ⟩
    · refine absurd ?_ (hc (typeOf (monicPoly a)))
      rw [← ha]
      exact decidedAt_of_peel hπ hN hr hu hT
  · refine absurd ?_ (hc c3inert)
    intro b hb
    refine inert3_decided hno b ?_
    have h1 : proj O 3 1 b = proj O 3 1 a := by
      have h := congrArg (coeffFactor (O := O) 3 hN) (hb.trans ha.symm)
      rwa [coeffFactor_proj, coeffFactor_proj] at h
    rw [h1, proj_one_eq_liftRes1]
  · exact Or.inr ⟨a, γ, ha, hγ⟩

/-! ## 5. The quantitative consequences -/

/-- The undecided proportion inside the triple-root stratum: the whole remaining obligation. -/
noncomputable def tripleUndecidedSeq (N : ℕ) : ℝ :=
  (Nat.card (undecidedSet O 3 N ∩ tripleSet (O := O) N : Set (Coeff O 3 N)) : ℝ)
    / (residueCard O : ℝ) ^ (3 * N)

theorem undecidedCount_three_le {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N) :
    undecidedCount O 3 N
      ≤ Nat.card (peelSet π N)
        + Nat.card (undecidedSet O 3 N ∩ tripleSet (O := O) N : Set (Coeff O 3 N)) := by
  classical
  have hsub : undecidedSet O 3 N
      ⊆ peelSet π N ∪ (undecidedSet O 3 N ∩ tripleSet (O := O) N) := by
    intro c hc
    rcases undecidedSet_subset hπ hN hc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hc, h⟩
  rw [undecidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc (undecidedSet O 3 N).ncard
      ≤ (peelSet π N ∪ (undecidedSet O 3 N ∩ tripleSet (O := O) N)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ _ := Set.ncard_union_le _ _

/-- **The undecided proportion at `n = 3` and level `2M`**: branch (b) costs `q^{-M}`, the
triple-root stratum is all that is left. -/
theorem undecidedSeq_three_le {π : O} (hπ : Irreducible π) {M : ℕ} (hM : 1 ≤ M) :
    undecidedSeq O 3 (2 * M)
      ≤ (1 / (residueCard O : ℝ)) ^ M + tripleUndecidedSeq (O := O) (2 * M) := by
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  set T : ℕ := Nat.card (undecidedSet O 3 (2 * M) ∩ tripleSet (O := O) (2 * M) :
    Set (Coeff O 3 (2 * M))) with hTdef
  have hcount := undecidedCount_three_le (O := O) hπ (N := 2 * M) (by omega)
  have hpeel := card_peelSet_le (O := O) hπ M
  have hcast : (undecidedCount O 3 (2 * M) : ℝ) ≤ (residueCard O : ℝ) ^ (5 * M) + (T : ℝ) := by
    have h1 : (undecidedCount O 3 (2 * M) : ℝ) ≤ (Nat.card (peelSet π (2 * M)) : ℝ) + (T : ℝ) := by
      exact_mod_cast hcount
    have h2 : (Nat.card (peelSet π (2 * M)) : ℝ) ≤ (residueCard O : ℝ) ^ (5 * M) := by
      exact_mod_cast hpeel
    linarith
  have hpow : (3 : ℕ) * (2 * M) = 6 * M := by ring
  calc undecidedSeq O 3 (2 * M)
      = (undecidedCount O 3 (2 * M) : ℝ) / (residueCard O : ℝ) ^ (6 * M) := by
        rw [undecidedSeq, hpow]
    _ ≤ ((residueCard O : ℝ) ^ (5 * M) + (T : ℝ)) / (residueCard O : ℝ) ^ (6 * M) := by
        gcongr
    _ = (1 / (residueCard O : ℝ)) ^ M + (T : ℝ) / (residueCard O : ℝ) ^ (6 * M) := by
        have hne : (residueCard O : ℝ) ≠ 0 := ne_of_gt hq
        have h6 : (residueCard O : ℝ) ^ (6 * M)
            = (residueCard O : ℝ) ^ (5 * M) * (residueCard O : ℝ) ^ M := by
          rw [← pow_add]; congr 1; ring
        rw [add_div]
        congr 1
        rw [div_pow, one_pow, h6]
        field_simp
    _ = (1 / (residueCard O : ℝ)) ^ M + tripleUndecidedSeq (O := O) (2 * M) := by
        rw [tripleUndecidedSeq, hpow]

/-- The triple-root stratum is at most `1/q²` of everything, so the undecided proportion at
`n = 3` is eventually at most `q^{-M} + q^{-2}` — this is the unconditional half. -/
theorem tripleUndecidedSeq_le {N : ℕ} (hN : 1 ≤ N) :
    tripleUndecidedSeq (O := O) N ≤ 1 / (residueCard O : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  have hle : Nat.card (undecidedSet O 3 N ∩ tripleSet (O := O) N : Set (Coeff O 3 N))
      ≤ Nat.card (tripleSet (O := O) N) :=
    Nat.card_le_card_of_injective (Set.inclusion Set.inter_subset_right)
      (Set.inclusion_injective _)
  have h := card_tripleSet_le (O := O) hN
  have hcast : (Nat.card (undecidedSet O 3 N ∩ tripleSet (O := O) N : Set (Coeff O 3 N)) : ℝ)
      * (residueCard O : ℝ) ^ 2 ≤ (residueCard O : ℝ) ^ (3 * N) := by
    have h1 : (Nat.card (undecidedSet O 3 N ∩ tripleSet (O := O) N : Set (Coeff O 3 N)) : ℝ)
        ≤ (Nat.card (tripleSet (O := O) N) : ℝ) := by exact_mod_cast hle
    have h2 : (Nat.card (tripleSet (O := O) N) : ℝ) * (residueCard O : ℝ) ^ 2
        ≤ (residueCard O : ℝ) ^ (3 * N) := by exact_mod_cast h
    nlinarith [pow_pos hq 2]
  rw [tripleUndecidedSeq, div_le_div_iff₀ (pow_pos hq _) (pow_pos hq _), one_mul]
  exact hcast

/-- **THE `n = 3` BRACKET CLOSES TO WITHIN `1/q²`.** For every splitting type, the possible
(upper) density exceeds the certified (genuine) density by at most `1/q²` — `1/4` at `q = 2`,
`1/9` at `q = 3`. Unconditional, general `O`. -/
theorem upperDensity_three_le (σ : FactorizationType) :
    upperDensity O 3 σ ≤ genuineDensity O 3 σ + 1 / (residueCard O : ℝ) ^ 2 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hlim : Tendsto (fun M : ℕ => gapSeq O 3 σ (2 * M)) atTop
      (𝓝 (upperDensity O 3 σ - genuineDensity O 3 σ)) :=
    ((possibleSeq_tendsto (O := O) 3 σ).sub (decidedSeq_tendsto (O := O) 3 σ)).comp
      tendsto_two_mul_atTop
  have hrhs : Tendsto (fun M : ℕ =>
      (1 / (residueCard O : ℝ)) ^ M + 1 / (residueCard O : ℝ) ^ 2) atTop
      (𝓝 (0 + 1 / (residueCard O : ℝ) ^ 2)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one qR_pos]
    exact_mod_cast one_lt_residueCard O
  have hbd : (fun M : ℕ => gapSeq O 3 σ (2 * M)) ≤ᶠ[atTop]
      (fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M + 1 / (residueCard O : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    refine le_trans (gapSeq_le_undecidedSeq 3 (2 * M) σ) ?_
    refine le_trans (undecidedSeq_three_le hπ hM) ?_
    gcongr
    exact tripleUndecidedSeq_le (by omega)
  have hkey := le_of_tendsto_of_tendsto hlim hrhs hbd
  linarith

/-- **DRAINAGE AT `n = 3` REDUCES TO THE TRIPLE-ROOT STRATUM.** If the undecided classes that
are residually perfect cubes drain, then the whole `n = 3` ambiguity gap drains, for every
splitting type. Branch (b) is fully discharged. -/
theorem drainage_three_of_triple
    (h : Tendsto (fun M : ℕ => tripleUndecidedSeq (O := O) (2 * M)) atTop (𝓝 0))
    (σ : FactorizationType) : UndecidedVanishes O 3 σ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hanti : Antitone (gapSeq O 3 σ) := by
    intro N M hNM
    simp only [gapSeq]
    have h1 := possibleSeq_antitone (O := O) 3 σ hNM
    have h2 := decidedSeq_mono (O := O) 3 σ hNM
    linarith
  have hbdd : BddBelow (Set.range (gapSeq O 3 σ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨N, rfl⟩
    exact gapSeq_nonneg 3 σ N
  have hlim : Tendsto (gapSeq O 3 σ) atTop (𝓝 (⨅ N, gapSeq O 3 σ N)) :=
    tendsto_atTop_ciInf hanti hbdd
  have hsub : Tendsto (fun M : ℕ => gapSeq O 3 σ (2 * M)) atTop (𝓝 (⨅ N, gapSeq O 3 σ N)) :=
    hlim.comp tendsto_two_mul_atTop
  have hgeom : Tendsto (fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one qR_pos]
    exact_mod_cast one_lt_residueCard O
  have hzero : Tendsto (fun M : ℕ => gapSeq O 3 σ (2 * M)) atTop (𝓝 0) := by
    refine squeeze_zero'
      (g := fun M : ℕ => (1 / (residueCard O : ℝ)) ^ M + tripleUndecidedSeq (O := O) (2 * M))
      (Eventually.of_forall (fun M => gapSeq_nonneg 3 σ (2 * M))) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with M hM
      exact le_trans (gapSeq_le_undecidedSeq 3 (2 * M) σ) (undecidedSeq_three_le hπ hM)
    · simpa using hgeom.add h
  have hL : (⨅ N, gapSeq O 3 σ N) = 0 := tendsto_nhds_unique hsub hzero
  rw [UndecidedVanishes, ← hL]
  exact hlim

end Drain

#print axioms UniformityCheck.card_peelSet_le
#print axioms UniformityCheck.card_tripleSet_le
#print axioms UniformityCheck.undecidedSet_subset
#print axioms UniformityCheck.undecidedSeq_three_le
#print axioms UniformityCheck.upperDensity_three_le
#print axioms UniformityCheck.drainage_three_of_triple

end UniformityCheck
