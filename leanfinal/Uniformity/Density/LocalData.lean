/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.Density.LocalData — the local base, the level-`N` coefficient boxes

**Part 1 of the `Uniformity` repo** (see `README.md`). This file fixes the *arena* in which
the genuine density is defined:

* the **local base** `O`: a complete discrete valuation ring with finite residue field
  (`CommRing O`, `IsDomain O`, `IsDiscreteValuationRing O`,
  `IsAdicComplete (maximalIdeal O) O`, `Finite (ResidueField O)`).  `ℤ_[p]` is an instance
  (`instances` section at the end); so is every finite unramified/ramified extension of `ℤ_[p]`
  or `𝔽_q⟦t⟧`, once its instances are supplied — nothing below uses `p` or characteristic.
* `residueCard O = q`: the residue-field cardinality.  **This is the `q` of the uniformity
  theorem** — the input of the rational function the main theorem produces.
* the **level-`N` coefficient box** `Coeff O n N = Fin n → O ⧸ 𝔪 ^ N`: the truncations of the
  coefficient vectors of monic degree-`n` polynomials, and `monicPoly` turning a coefficient
  vector into the polynomial `X ^ n + ∑ aᵢ Xⁱ`.

Nothing here mentions an Okutsu–Montes engine, a Newton polygon, or any classifier: this is the
raw counting arena. The point of the whole Part-1 construction is that the density is defined
from *these* objects only.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity

/-! ## 0. The splitting-type grain (quarry copy) -/

/-- A **factorization type** `σ` of degree `n`: a multiset of pairs `(eᵢ, fᵢ)` (ramification /
residue data of the irreducible `p`-adic factors) with `∑ eᵢ fᵢ = n` (`notes/HUMAN_PROOF.md §0`). -/
-- verbatim from LeanUrat/Interface.lean:152 (quarry copy, verified 2026-08-13)
structure FactorizationType where
  /-- The multiset of `(e, f)` pairs. -/
  data : Multiset (ℕ × ℕ)

/-- The degree `n = ∑ eᵢ fᵢ` of a factorization type. -/
-- verbatim from LeanUrat/Interface.lean:157 (quarry copy, verified 2026-08-13)
def FactorizationType.degree (σ : FactorizationType) : ℕ :=
  (σ.data.map (fun p => p.1 * p.2)).sum

@[ext]
theorem FactorizationType.ext {σ τ : FactorizationType} (h : σ.data = τ.data) : σ = τ := by
  cases σ; cases τ; simpa using h

noncomputable instance : DecidableEq FactorizationType := Classical.decEq _

namespace Density

open IsLocalRing Polynomial

/-! ## 1. The local base and its residue cardinality -/

section Base

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **`q` — the residue cardinality of the local base.** For `O = ℤ_[p]` this is `p`; for the
unramified extension of degree `f` it is `p ^ f`; for `𝔽_q⟦t⟧` it is `q`. This is the single
numerical input of the rational function the uniformity theorem produces. -/
noncomputable def residueCard : ℕ := Nat.card (ResidueField O)

/-- The level-`N` truncation ring `O ⧸ 𝔪 ^ N`. -/
abbrev Res (N : ℕ) : Type _ := O ⧸ (maximalIdeal O) ^ N

instance instFiniteRes (N : ℕ) : Finite (Res O N) := by
  have : Finite (O ⧸ maximalIdeal O) := ‹Finite (ResidueField O)›
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal O)) N

instance instNontrivialResidueField : Nontrivial (ResidueField O) := inferInstance

/-- `2 ≤ q`: the residue field is a nontrivial finite field. -/
theorem two_le_residueCard : 2 ≤ residueCard O := by
  have h1 : Nat.card (ResidueField O) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, ‹_›⟩
  have h2 : Nat.card (ResidueField O) ≠ 1 := by
    intro h
    have : Subsingleton (ResidueField O) := Nat.card_eq_one_iff_unique.1 h |>.1
    exact (not_subsingleton_iff_nontrivial.2 inferInstance) this
  show 2 ≤ Nat.card (ResidueField O)
  omega

theorem residueCard_pos : 0 < residueCard O := lt_of_lt_of_le two_pos (two_le_residueCard O)

theorem one_lt_residueCard : 1 < residueCard O := two_le_residueCard O

end Base

/-! ## 2. The complete local base: the standing bundle -/

section Complete

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The bundle is nonempty in the intended sense: `O` is Henselian at its maximal ideal
(adic completeness ⇒ Henselian). Recorded so that later Hensel-lifting arguments have a
one-line entry point. -/
theorem henselian_of_complete : HenselianRing O (maximalIdeal O) := inferInstance

/-- **Completeness ⇒ Henselian local ring.** The `HenselianRing` instance mathlib derives from
`IsAdicComplete` asks for the derivative to be a unit *in the residue field*; over a local ring
that is implied by (indeed equivalent to) being a unit in `O`. This is the form the gate proofs
use: a simple root mod `𝔪` lifts to a root in `O`. -/
instance henselianLocalRing_of_adicComplete : HenselianLocalRing O where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (maximalIdeal O)))

end Complete

/-! ## 3. The level-`N` coefficient box -/

section Box

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The level-`N` coefficient box** at degree `n`: coefficient vectors `(a₀,…,a_{n-1})` of monic
degree-`n` polynomials, read modulo `𝔪 ^ N`. Its cardinality is `q ^ (n * N)`
(`card_coeff`). -/
abbrev Coeff (n N : ℕ) : Type _ := Fin n → Res O N

instance instFiniteCoeff (n N : ℕ) : Finite (Coeff O n N) := Pi.finite

/-- Truncation of an integral coefficient vector to level `N`. -/
def proj (n N : ℕ) (a : Fin n → O) : Coeff O n N := fun i => Ideal.Quotient.mk _ (a i)

theorem proj_surjective (n N : ℕ) : Function.Surjective (proj O n N) := by
  intro c
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (c i)
  exact ⟨a, funext ha⟩

end Box

section Poly

variable {O : Type*} [CommRing O] [IsDomain O]

/-- **`monicPoly a = X ^ n + ∑ i, aᵢ Xⁱ`** — the monic degree-`n` polynomial with coefficient
vector `a`. Every monic degree-`n` polynomial over `O` is of this shape. -/
noncomputable def monicPoly {n : ℕ} (a : Fin n → O) : Polynomial O :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ)

theorem degree_tail_lt {n : ℕ} (a : Fin n → O) :
    (∑ i : Fin n, C (a i) * X ^ (i : ℕ)).degree < (X ^ n : Polynomial O).degree := by
  classical
  have hXn : (X ^ n : Polynomial O).degree = (n : WithBot ℕ) := by
    simpa using (degree_X_pow (R := O) n)
  rw [hXn]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le (i : ℕ) (a i)) ?_
  exact_mod_cast (i.isLt : (i : ℕ) < n)

theorem monicPoly_monic {n : ℕ} (a : Fin n → O) : (monicPoly a).Monic :=
  (monic_X_pow n).add_of_left (degree_tail_lt a)

theorem monicPoly_degree {n : ℕ} (a : Fin n → O) : (monicPoly a).degree = (n : WithBot ℕ) := by
  unfold monicPoly
  rw [degree_add_eq_left_of_degree_lt (degree_tail_lt a)]
  simpa using (degree_X_pow (R := O) n)

theorem monicPoly_natDegree {n : ℕ} (a : Fin n → O) : (monicPoly a).natDegree = n := by
  rw [natDegree, monicPoly_degree]; rfl

end Poly

/-! ## 4. The truncation tower and the fibre-counting lemma

The level-`(N+1)` box surjects onto the level-`N` box; because the surjection is an additive
group homomorphism, **all its fibres have the same size**, so pulling a set back multiplies
its *proportion* by nothing at all. This is the only counting input the monotonicity of the
decided proportion needs (and it does not require knowing the fibre size). -/

section Tower

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A]

/-- **Fibre counting.** For a surjective homomorphism of finite abelian groups, the preimage of
a set `t` has cardinality `#(ker) * #t`. -/
theorem card_preimage_of_surjective (f : A →+ B) (hf : Function.Surjective f) (t : Set B) :
    Nat.card (f ⁻¹' t) = Nat.card f.ker * Nat.card t := by
  classical
  have hfin : Finite B := Finite.of_surjective f hf
  let e : (A ⧸ f.ker) ≃+ B := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  have hcomp : f ⁻¹' t = (QuotientAddGroup.mk (s := f.ker)) ⁻¹' (e ⁻¹' t) := by
    ext a; simp [e, QuotientAddGroup.quotientKerEquivOfSurjective]
  have he : Nat.card (e ⁻¹' t) = Nat.card t :=
    Nat.card_congr (e.toEquiv.subtypeEquiv (fun _ => Iff.rfl))
  rw [hcomp,
    Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet (f.ker) (e ⁻¹' t)),
    Nat.card_prod, he]

end Tower

/-! ## 5. The size of the level-`N` truncation: `#(O ⧸ 𝔪^N) = q ^ N` -/

section Card

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The truncation ring map `O ⧸ 𝔪 ^ M → O ⧸ 𝔪 ^ N` for `N ≤ M`. -/
def resFactor {N M : ℕ} (h : N ≤ M) : Res O M →+* Res O N :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right h)

theorem resFactor_mk {N M : ℕ} (h : N ≤ M) (x : O) :
    resFactor (O := O) h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem resFactor_surjective {N M : ℕ} (h : N ≤ M) :
    Function.Surjective (resFactor (O := O) h) :=
  Ideal.Quotient.factor_surjective _

/-- **`#(O ⧸ 𝔪 ^ N) = q ^ N`.** Proved by induction: the kernel of
`O ⧸ 𝔪 ^ (N+1) → O ⧸ 𝔪 ^ N` is the image of `𝔪 ^ N`, and multiplication by `π ^ N` identifies
it with the residue field. -/
theorem card_res (N : ℕ) : Nat.card (Res O N) = residueCard O ^ N := by
  classical
  induction N with
  | zero =>
    have hsub : Subsingleton (Res O 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    simp [Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨0⟩⟩]
  | succ N ih =>
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
    set φ : Res O (N + 1) →+* Res O N := resFactor (Nat.le_succ N) with hφ
    have hsurj : Function.Surjective φ := resFactor_surjective _
    -- the additive hom `μ : x ↦ [x * π ^ N]`
    set μ : O →+ Res O (N + 1) :=
      (Ideal.Quotient.mk ((maximalIdeal O) ^ (N + 1))).toAddMonoidHom.comp
        (AddMonoidHom.mulRight (π ^ N)) with hμ
    have hμ_apply : ∀ x : O, μ x = Ideal.Quotient.mk _ (x * π ^ N) := fun _ => rfl
    have hπ0 : π ≠ 0 := hπ.ne_zero
    -- kernel of μ is the maximal ideal
    have hker : μ.ker = (maximalIdeal O).toAddSubgroup := by
      ext x
      simp only [AddMonoidHom.mem_ker, hμ_apply, Ideal.Quotient.eq_zero_iff_mem,
        Submodule.mem_toAddSubgroup]
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        pow_succ]
      constructor
      · intro ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have : x * π ^ N = (π * c) * π ^ N := by rw [hc]; ring
        exact mul_right_cancel₀ (pow_ne_zero N hπ0) this
      · rintro ⟨c, rfl⟩
        exact ⟨c, by ring⟩
    -- range of μ is the kernel of φ
    have hφmk : ∀ z : O, φ (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z := fun _ => rfl
    have hrange : (μ.range : Set (Res O (N + 1))) = (φ.toAddMonoidHom.ker : Set (Res O (N + 1))) := by
      ext y
      simp only [SetLike.mem_coe, AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
      constructor
      · rintro ⟨x, rfl⟩
        show φ (μ x) = 0
        rw [hμ_apply, hφmk, Ideal.Quotient.eq_zero_iff_mem, hm,
          Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨x, by ring⟩
      · intro hy
        replace hy : φ y = 0 := hy
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ (N + 1)) y
        rw [hφmk, Ideal.Quotient.eq_zero_iff_mem, hm, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] at hy
        obtain ⟨c, rfl⟩ := hy
        exact ⟨c, by rw [hμ_apply]; ring_nf⟩
    -- so #ker φ = #(O ⧸ 𝔪) = q
    have hcardker : Nat.card (φ.toAddMonoidHom.ker) = residueCard O := by
      have h1 : Nat.card (μ.range) = Nat.card (φ.toAddMonoidHom.ker) :=
        Nat.card_congr (Equiv.setCongr hrange)
      have h2 : Nat.card (O ⧸ μ.ker) = Nat.card (μ.range) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange μ).toEquiv
      rw [← h1, ← h2, hker]
      rfl
    -- and #(level N+1) = #ker φ * #(level N)
    have hprod : Nat.card (Res O (N + 1)) = Nat.card (φ.toAddMonoidHom.ker) * Nat.card (Res O N) := by
      have := card_preimage_of_surjective (A := Res O (N + 1)) (B := Res O N)
        φ.toAddMonoidHom hsurj Set.univ
      simpa using this
    rw [hprod, hcardker, ih, pow_succ, mul_comm]

/-- `#(Coeff O n N) = q ^ (n * N)` — the box count. -/
theorem card_coeff (n N : ℕ) : Nat.card (Coeff O n N) = residueCard O ^ (n * N) := by
  rw [Nat.card_pi]
  simp [card_res, Finset.prod_const, ← pow_mul, Nat.mul_comm]

/-- The coefficient-box truncation `Coeff O n M → Coeff O n N` for `N ≤ M`, as an additive
homomorphism (this is what makes all its fibres the same size). -/
def coeffFactor (n : ℕ) {N M : ℕ} (h : N ≤ M) : Coeff O n M →+ Coeff O n N :=
  Pi.addMonoidHom fun i => (resFactor (O := O) h).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i)

theorem coeffFactor_apply (n : ℕ) {N M : ℕ} (h : N ≤ M) (c : Coeff O n M) (i : Fin n) :
    coeffFactor (O := O) n h c i = resFactor h (c i) := rfl

theorem coeffFactor_surjective (n : ℕ) {N M : ℕ} (h : N ≤ M) :
    Function.Surjective (coeffFactor (O := O) n h) := by
  intro c
  choose a ha using fun i => resFactor_surjective (O := O) h (c i)
  exact ⟨a, funext ha⟩

theorem coeffFactor_proj (n : ℕ) {N M : ℕ} (h : N ≤ M) (a : Fin n → O) :
    coeffFactor (O := O) n h (proj O n M a) = proj O n N a := rfl

/-- **The proportion is preserved by refinement.** For any set `S` of level-`N` classes, the
number of level-`M` classes refining a member of `S`, divided by the level-`M` box count, equals
`#S` divided by the level-`N` box count. (Stated multiplicatively over `ℕ`.) -/
theorem card_preimage_coeffFactor (n : ℕ) {N M : ℕ} (h : N ≤ M) (S : Set (Coeff O n N)) :
    Nat.card ((coeffFactor (O := O) n h) ⁻¹' S) * Nat.card (Coeff O n N)
      = Nat.card S * Nat.card (Coeff O n M) := by
  have hs := coeffFactor_surjective (O := O) n h
  have h1 := card_preimage_of_surjective (coeffFactor (O := O) n h) hs S
  have h2 := card_preimage_of_surjective (coeffFactor (O := O) n h) hs Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h2
  rw [h1, h2]
  ring

end Card

/-! ## 5b. Valuation bookkeeping in one coordinate

Promoted 2026-08-20 from `ChapC/C110.lean`'s `private` cluster (the RE-PLAN item C.53's and
C.110's headers both flag): the divisibility reads of `addVal` and the one-coordinate count
`#{r : O ⧸ 𝔪 ^ N | r lifts to valuation ≥ m} = q ^ (N − m)` with the `ℕ`-subtraction CLIP.
The former `private` copies in C110/C53/C53c now consume these. -/

section ValCount

open IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem le_addVal_iff_pow_dvd (hπ : Irreducible π) (m : ℕ) (x : O) :
    ((m : ℕ) : ℕ∞) ≤ addVal O x ↔ π ^ m ∣ x := by
  rw [← hπ.addVal_pow m]
  exact addVal_le_iff_dvd

theorem mem_pow_maximalIdeal_iff (hπ : Irreducible π) (m : ℕ) (x : O) :
    x ∈ (IsLocalRing.maximalIdeal O) ^ m ↔ π ^ m ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- The level-`N` classes with a lift of valuation `≥ m`, when `N ≤ m`: only the zero class
(the CLIP branch — the bound lies at or beyond the window). -/
theorem card_res_ge_of_le (hπ : Irreducible π) {N m : ℕ} (h : N ≤ m) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  have hzero : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r = 0 := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_maximalIdeal_iff hπ]
      exact dvd_trans (pow_dvd_pow _ h) ((le_addVal_iff_pow_dvd hπ m x).1 hx)
    · rintro rfl
      exact ⟨0, by simp, by simp⟩
  have hone : Nat.card {r : Res O N // r = 0} = 1 := by simp
  rw [Nat.sub_eq_zero_of_le h, pow_zero, ← hone]
  exact Nat.card_congr (Equiv.subtypeEquivRight hzero)

/-- The level-`N` classes with a lift of valuation `≥ m`, when `m ≤ N`: `q ^ (N − m)` of them —
the range of the additive map `x ↦ [x·π ^ m]`, whose kernel is `𝔪 ^ (N−m)`. -/
theorem card_res_ge_of_ge [Finite (ResidueField O)] (hπ : Irreducible π) {N m : ℕ}
    (h : m ≤ N) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  classical
  set μ : O →+ Res O N :=
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)).toAddMonoidHom.comp
      (AddMonoidHom.mulRight (π ^ m)) with hμ
  have hμ_apply : ∀ x : O, μ x = Ideal.Quotient.mk _ (x * π ^ m) := fun _ => rfl
  have hrange : ∀ r : Res O N,
      (∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x) ↔ r ∈ Set.range μ := by
    intro r
    constructor
    · rintro ⟨x, rfl, hx⟩
      obtain ⟨y, rfl⟩ := (le_addVal_iff_pow_dvd hπ m x).1 hx
      exact ⟨y, by rw [hμ_apply]; ring_nf⟩
    · rintro ⟨y, rfl⟩
      refine ⟨y * π ^ m, rfl, ?_⟩
      exact (le_addVal_iff_pow_dvd hπ m _).2 ⟨y, by ring⟩
  have hker : μ.ker = ((IsLocalRing.maximalIdeal O) ^ (N - m)).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, hμ_apply, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_toAddSubgroup]
    rw [mem_pow_maximalIdeal_iff hπ, mem_pow_maximalIdeal_iff hπ]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hid : π ^ (N - m) * c * π ^ m = π ^ N * c := by
        rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]
      have hsplit : x * π ^ m = (π ^ (N - m) * c) * π ^ m := by rw [hid]; exact hc
      exact mul_right_cancel₀ (pow_ne_zero m hπ.ne_zero) hsplit
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel h]⟩
  have hcard : Nat.card (Set.range μ) = Nat.card (O ⧸ μ.ker) :=
    (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange μ).toEquiv).symm
  have hq : Nat.card (O ⧸ μ.ker) = residueCard O ^ (N - m) := by
    rw [hker]
    exact card_res (O := O) (N - m)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hrange), hcard, hq]

/-- **One coordinate, both branches.**  `#{r : O ⧸ 𝔪 ^ N | r lifts to valuation ≥ m}
= q ^ (N − m)`, the subtraction being the `ℕ`-CLIP. -/
theorem card_res_ge [Finite (ResidueField O)] (hπ : Irreducible π) (N m : ℕ) :
    Nat.card {r : Res O N // ∃ x : O, Ideal.Quotient.mk _ x = r ∧ ((m : ℕ) : ℕ∞) ≤ addVal O x}
      = residueCard O ^ (N - m) := by
  rcases le_total m N with h | h
  · exact card_res_ge_of_ge hπ h
  · exact card_res_ge_of_le hπ h

end ValCount

/-! ## 6. `ℤ_[p]` is an instance of the bundle -/

section Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

instance : Finite (ResidueField ℤ_[p]) :=
  Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv

example : IsDiscreteValuationRing ℤ_[p] := inferInstance
example : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] := inferInstance

/-- **`q = p` for `O = ℤ_[p]`.** -/
theorem residueCard_padicInt : residueCard ℤ_[p] = p := by
  rw [residueCard, Nat.card_congr (PadicInt.residueField (p := p)).toEquiv]
  simp

end Padic

end Density

end Uniformity
