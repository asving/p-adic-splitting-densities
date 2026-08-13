/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.GenuineDensity — the density, as a proved limit

Fix a complete DVR `O` with finite residue field of cardinality `q`, a degree `n`, and a
splitting type `σ`. A level-`N` coefficient class `c ∈ (O ⧸ 𝔪^N)^n` is

* **`σ`-DECIDED** iff *every* monic degree-`n` polynomial whose coefficients reduce to `c` has
  `typeOf = σ` (`DecidedAt`), and
* **`σ`-POSSIBLE** iff *some* such polynomial has `typeOf = σ` (`PossibleAt`).

Then

    decidedSeq  σ N = #{σ-decided classes at level N} / q ^ (n * N)   (monotone ↑, ≤ 1)
    possibleSeq σ N = #{σ-possible classes at level N} / q ^ (n * N)  (antitone ↓, ≥ 0)

and

    genuineDensity O n σ  :=  ⨆ N, decidedSeq  σ N     (`decidedSeq_tendsto`: it IS the limit)
    upperDensity   O n σ  :=  ⨅ N, possibleSeq σ N     (`possibleSeq_tendsto`)

**The density is an `ℝ`-valued theorem-backed limit, never a value carried as data.** The
sandwich `decidedSeq ≤ genuineDensity ≤ upperDensity ≤ possibleSeq` is proved, and the
**drainage tie** `gapSeq → 0 → upperDensity = genuineDensity` (`upperDensity_eq_of_drainage`)
makes the drainage hypothesis do real work: without it the two densities are only known to
bracket the true one.

Degenerate conventions, chosen deliberately:
* `N = 0`: the level-0 box is a single class (`O ⧸ 𝔪^0` is trivial), so `decidedSeq σ 0` is
  `1` if *every* monic degree-`n` polynomial has type `σ` and `0` otherwise. Harmless: the
  sequence is monotone from there.
* `n = 0`: the only monic polynomial is `1`, whose type is `⟨0⟩` (the empty multiset); the box
  is a single class, so `genuineDensity O 0 ⟨0⟩ = 1` and `0` for every other `σ`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-! ## 1. Decided and possible classes -/

/-- **`c` is `σ`-DECIDED at level `N`**: *every* monic degree-`n` polynomial whose coefficient
vector reduces to `c` mod `𝔪 ^ N` has splitting type `σ`. (Not vacuous: `proj` is surjective,
so every class has lifts — `decided_imp_possible`.) -/
def DecidedAt (n : ℕ) (σ : FactorizationType) (N : ℕ) (c : Coeff O n N) : Prop :=
  ∀ a : Fin n → O, proj O n N a = c → typeOf (monicPoly a) = σ

/-- **`c` is `σ`-POSSIBLE at level `N`**: *some* monic degree-`n` lift of `c` has type `σ`. -/
def PossibleAt (n : ℕ) (σ : FactorizationType) (N : ℕ) (c : Coeff O n N) : Prop :=
  ∃ a : Fin n → O, proj O n N a = c ∧ typeOf (monicPoly a) = σ

/-- The set of `σ`-decided level-`N` classes. -/
def decidedSet (n : ℕ) (σ : FactorizationType) (N : ℕ) : Set (Coeff O n N) :=
  {c | DecidedAt O n σ N c}

/-- The set of `σ`-possible level-`N` classes. -/
def possibleSet (n : ℕ) (σ : FactorizationType) (N : ℕ) : Set (Coeff O n N) :=
  {c | PossibleAt O n σ N c}

variable {O}

theorem decided_imp_possible {n : ℕ} {σ : FactorizationType} {N : ℕ} {c : Coeff O n N}
    (h : DecidedAt O n σ N c) : PossibleAt O n σ N c := by
  obtain ⟨a, ha⟩ := proj_surjective O n N c
  exact ⟨a, ha, h a ha⟩

theorem decidedSet_subset_possibleSet (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedSet O n σ N ⊆ possibleSet O n σ N := fun _ hc => decided_imp_possible hc

/-- Distinct types have disjoint decided sets (a class has a lift, and that lift has one type). -/
theorem decidedSet_disjoint {n : ℕ} {σ τ : FactorizationType} (hστ : σ ≠ τ) (N : ℕ) :
    Disjoint (decidedSet O n σ N) (decidedSet O n τ N) := by
  rw [Set.disjoint_left]
  intro c hcσ hcτ
  obtain ⟨a, ha⟩ := proj_surjective O n N c
  exact hστ ((hcσ a ha).symm.trans (hcτ a ha))

variable (O)

/-! ## 2. The counts and the two normalized sequences -/

/-- `#{σ-decided level-N classes}` (an honest `ℕ`). -/
noncomputable def decidedCount (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℕ :=
  Nat.card (decidedSet O n σ N)

/-- `#{σ-possible level-N classes}` (an honest `ℕ`). -/
noncomputable def possibleCount (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℕ :=
  Nat.card (possibleSet O n σ N)

/-- `decidedSeq σ N = #{σ-decided level-N classes} / q ^ (n * N)`, the level-`N` *certified*
proportion. Monotone nondecreasing in `N`. -/
noncomputable def decidedSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  (decidedCount O n σ N : ℝ) / (residueCard O : ℝ) ^ (n * N)

/-- `possibleSeq σ N = #{σ-possible level-N classes} / q ^ (n * N)`, the level-`N` *upper*
proportion. Antitone in `N`. -/
noncomputable def possibleSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  (possibleCount O n σ N : ℝ) / (residueCard O : ℝ) ^ (n * N)

section Basic

variable {O}

theorem qR_pos : (0 : ℝ) < (residueCard O : ℝ) := by
  exact_mod_cast residueCard_pos O

theorem qpow_pos (k : ℕ) : (0 : ℝ) < (residueCard O : ℝ) ^ k := pow_pos qR_pos k

theorem qpow_ne (k : ℕ) : ((residueCard O : ℝ)) ^ k ≠ 0 := (qpow_pos k).ne'

theorem decidedCount_le (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedCount O n σ N ≤ residueCard O ^ (n * N) := by
  rw [← card_coeff (O := O) n N]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

theorem possibleCount_le (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    possibleCount O n σ N ≤ residueCard O ^ (n * N) := by
  rw [← card_coeff (O := O) n N]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

theorem decidedSeq_nonneg (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    0 ≤ decidedSeq O n σ N :=
  div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le

theorem possibleSeq_nonneg (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    0 ≤ possibleSeq O n σ N :=
  div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le

theorem decidedSeq_le_one (n : ℕ) (σ : FactorizationType) (N : ℕ) : decidedSeq O n σ N ≤ 1 := by
  rw [decidedSeq, div_le_one (qpow_pos _)]
  exact_mod_cast decidedCount_le (O := O) n σ N

theorem possibleSeq_le_one (n : ℕ) (σ : FactorizationType) (N : ℕ) : possibleSeq O n σ N ≤ 1 := by
  rw [possibleSeq, div_le_one (qpow_pos _)]
  exact_mod_cast possibleCount_le (O := O) n σ N

theorem decidedCount_le_possibleCount (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedCount O n σ N ≤ possibleCount O n σ N :=
  Nat.card_le_card_of_injective (Set.inclusion (decidedSet_subset_possibleSet n σ N))
    (Set.inclusion_injective _)

theorem decidedSeq_le_possibleSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedSeq O n σ N ≤ possibleSeq O n σ N := by
  have h1 : (decidedCount O n σ N : ℝ) ≤ (possibleCount O n σ N : ℝ) := by
    exact_mod_cast decidedCount_le_possibleCount n σ N
  unfold decidedSeq possibleSeq
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos (O := O) _
  rw [div_le_div_iff₀ hq hq]
  nlinarith [h1, hq]

end Basic

/-! ## 3. Refinement: monotone / antitone -/

section Refine

variable {O}

/-- Refining a `σ`-decided class keeps it `σ`-decided. -/
theorem preimage_decidedSet_subset {n : ℕ} {σ : FactorizationType} {N M : ℕ} (h : N ≤ M) :
    (coeffFactor (O := O) n h) ⁻¹' (decidedSet O n σ N) ⊆ decidedSet O n σ M := by
  intro c hc a ha
  refine hc a ?_
  rw [← coeffFactor_proj (O := O) n h a, ha]

/-- The image of a `σ`-possible class is `σ`-possible. -/
theorem possibleSet_subset_preimage {n : ℕ} {σ : FactorizationType} {N M : ℕ} (h : N ≤ M) :
    possibleSet O n σ M ⊆ (coeffFactor (O := O) n h) ⁻¹' (possibleSet O n σ N) := by
  rintro c ⟨a, rfl, hta⟩
  exact ⟨a, (coeffFactor_proj (O := O) n h a), hta⟩

private theorem seq_le_of_count {n : ℕ} {N M : ℕ} (A : ℕ) (B : ℕ)
    (hAB : A * residueCard O ^ (n * M) ≤ B * residueCard O ^ (n * N)) :
    (A : ℝ) / (residueCard O : ℝ) ^ (n * N) ≤ (B : ℝ) / (residueCard O : ℝ) ^ (n * M) := by
  rw [div_le_div_iff₀ (qpow_pos (O := O) (n * N)) (qpow_pos (O := O) (n * M))]
  have h2 : ((A * residueCard O ^ (n * M) : ℕ) : ℝ) ≤ ((B * residueCard O ^ (n * N) : ℕ) : ℝ) :=
    Nat.cast_le.2 hAB
  push_cast at h2
  linarith

theorem decidedSeq_mono (n : ℕ) (σ : FactorizationType) : Monotone (decidedSeq O n σ) := by
  intro N M h
  simp only [decidedSeq]
  refine seq_le_of_count (O := O) (n := n) _ _ ?_
  have hcount := card_preimage_coeffFactor (O := O) n h (decidedSet O n σ N)
  have hsub : Nat.card ((coeffFactor (O := O) n h) ⁻¹' (decidedSet O n σ N))
      ≤ decidedCount O n σ M :=
    Nat.card_le_card_of_injective (Set.inclusion (preimage_decidedSet_subset (O := O) h))
      (Set.inclusion_injective _)
  rw [card_coeff, card_coeff] at hcount
  calc decidedCount O n σ N * residueCard O ^ (n * M)
      = Nat.card ((coeffFactor (O := O) n h) ⁻¹' (decidedSet O n σ N)) * residueCard O ^ (n * N) :=
        hcount.symm
    _ ≤ decidedCount O n σ M * residueCard O ^ (n * N) := Nat.mul_le_mul_right _ hsub

theorem possibleSeq_antitone (n : ℕ) (σ : FactorizationType) : Antitone (possibleSeq O n σ) := by
  intro N M h
  simp only [possibleSeq]
  refine seq_le_of_count (O := O) (n := n) _ _ ?_
  have hcount := card_preimage_coeffFactor (O := O) n h (possibleSet O n σ N)
  have hsub : possibleCount O n σ M
      ≤ Nat.card ((coeffFactor (O := O) n h) ⁻¹' (possibleSet O n σ N)) :=
    Nat.card_le_card_of_injective (Set.inclusion (possibleSet_subset_preimage (O := O) h))
      (Set.inclusion_injective _)
  rw [card_coeff, card_coeff] at hcount
  calc possibleCount O n σ M * residueCard O ^ (n * N)
      ≤ Nat.card ((coeffFactor (O := O) n h) ⁻¹' (possibleSet O n σ N)) * residueCard O ^ (n * N) :=
        Nat.mul_le_mul_right _ hsub
    _ = possibleCount O n σ N * residueCard O ^ (n * M) := hcount

end Refine

/-! ## 4. THE DENSITY -/

/-- **THE GENUINE DENSITY** of monic degree-`n` polynomials over `O` of splitting type `σ`:
the limit of the level-`N` *decided* proportions. It is a real number defined as a supremum,
and `decidedSeq_tendsto` proves it is the honest `N → ∞` limit. -/
noncomputable def genuineDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨆ N, decidedSeq O n σ N

/-- **The upper (possible) density**: the limit of the level-`N` *possible* proportions. -/
noncomputable def upperDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨅ N, possibleSeq O n σ N

section Limits

variable {O}

theorem decidedSeq_bddAbove (n : ℕ) (σ : FactorizationType) :
    BddAbove (Set.range (decidedSeq O n σ)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨N, rfl⟩
  exact decidedSeq_le_one n σ N

theorem possibleSeq_bddBelow (n : ℕ) (σ : FactorizationType) :
    BddBelow (Set.range (possibleSeq O n σ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  exact possibleSeq_nonneg n σ N

/-- **`genuineDensity` IS the limit of the decided proportions.** -/
theorem decidedSeq_tendsto (n : ℕ) (σ : FactorizationType) :
    Tendsto (decidedSeq O n σ) atTop (𝓝 (genuineDensity O n σ)) :=
  tendsto_atTop_ciSup (decidedSeq_mono n σ) (decidedSeq_bddAbove n σ)

/-- **`upperDensity` IS the limit of the possible proportions.** -/
theorem possibleSeq_tendsto (n : ℕ) (σ : FactorizationType) :
    Tendsto (possibleSeq O n σ) atTop (𝓝 (upperDensity O n σ)) :=
  tendsto_atTop_ciInf (possibleSeq_antitone n σ) (possibleSeq_bddBelow n σ)

theorem decidedSeq_le_genuineDensity (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedSeq O n σ N ≤ genuineDensity O n σ :=
  le_ciSup (decidedSeq_bddAbove n σ) N

theorem upperDensity_le_possibleSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    upperDensity O n σ ≤ possibleSeq O n σ N :=
  ciInf_le (possibleSeq_bddBelow n σ) N

theorem genuineDensity_nonneg (n : ℕ) (σ : FactorizationType) : 0 ≤ genuineDensity O n σ :=
  le_trans (decidedSeq_nonneg n σ 0) (decidedSeq_le_genuineDensity n σ 0)

theorem genuineDensity_le_one (n : ℕ) (σ : FactorizationType) : genuineDensity O n σ ≤ 1 :=
  ciSup_le (fun N => decidedSeq_le_one n σ N)

theorem upperDensity_nonneg (n : ℕ) (σ : FactorizationType) : 0 ≤ upperDensity O n σ :=
  le_ciInf (fun N => possibleSeq_nonneg n σ N)

theorem upperDensity_le_one (n : ℕ) (σ : FactorizationType) : upperDensity O n σ ≤ 1 :=
  le_trans (upperDensity_le_possibleSeq n σ 0) (possibleSeq_le_one n σ 0)

/-- **The sandwich.** The genuine (decided) density never exceeds the upper (possible) one. -/
theorem genuineDensity_le_upperDensity (n : ℕ) (σ : FactorizationType) :
    genuineDensity O n σ ≤ upperDensity O n σ := by
  refine ciSup_le (fun N => le_ciInf (fun M => ?_))
  calc decidedSeq O n σ N ≤ decidedSeq O n σ (max N M) := decidedSeq_mono n σ (le_max_left N M)
    _ ≤ possibleSeq O n σ (max N M) := decidedSeq_le_possibleSeq n σ _
    _ ≤ possibleSeq O n σ M := possibleSeq_antitone n σ (le_max_right N M)

end Limits

/-! ## 5. Drainage: the tie that makes the hypothesis do work -/

/-- The level-`N` *ambiguity gap* for `σ`: the proportion of classes that have a lift of type
`σ` but are not decided (some lift has another type). -/
noncomputable def gapSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) : ℝ :=
  possibleSeq O n σ N - decidedSeq O n σ N

/-- **Drainage at `σ`**: the ambiguity gap drains to `0`. (At `n = 2` the informal corpus
proves the exact rate `q ^ (-N)`; nothing here assumes a rate.) -/
def UndecidedVanishes (n : ℕ) (σ : FactorizationType) : Prop :=
  Tendsto (gapSeq O n σ) atTop (𝓝 0)

variable {O}

theorem gapSeq_nonneg (n : ℕ) (σ : FactorizationType) (N : ℕ) : 0 ≤ gapSeq O n σ N :=
  sub_nonneg.2 (decidedSeq_le_possibleSeq n σ N)

/-- **THE DRAINAGE TIE.** If the ambiguity gap drains, the upper density collapses onto the
genuine one, so the certified (decided) limit really is *the* density of type-`σ` polynomials
— not merely a lower bound for it. This is the theorem that makes a drainage hypothesis load
bearing rather than decorative. -/
theorem upperDensity_eq_of_drainage {n : ℕ} {σ : FactorizationType}
    (h : UndecidedVanishes O n σ) : upperDensity O n σ = genuineDensity O n σ := by
  have hlim : Tendsto (fun N => decidedSeq O n σ N + gapSeq O n σ N) atTop
      (𝓝 (genuineDensity O n σ + 0)) := (decidedSeq_tendsto n σ).add h
  have heq : (fun N => decidedSeq O n σ N + gapSeq O n σ N) = possibleSeq O n σ := by
    funext N; simp [gapSeq]
  rw [heq, add_zero] at hlim
  exact tendsto_nhds_unique (possibleSeq_tendsto n σ) hlim

/-- Converse direction: if the two densities agree, the gap drains. So `UndecidedVanishes` is
exactly the statement that the bracket closes. -/
theorem drainage_of_upperDensity_eq {n : ℕ} {σ : FactorizationType}
    (h : upperDensity O n σ = genuineDensity O n σ) : UndecidedVanishes O n σ := by
  have := (possibleSeq_tendsto (O := O) n σ).sub (decidedSeq_tendsto (O := O) n σ)
  rw [h, sub_self] at this
  exact this

/-! ## 6. Total mass: densities of distinct types sum to at most `1`

This is what turns *lower* bounds on the other types into an *upper* bound on `σ` — the
mechanism the `n = 2` gates use. -/

section Total

theorem sum_decidedCount_le (n : ℕ) (S : Finset FactorizationType) (N : ℕ) :
    ∑ σ ∈ S, decidedCount O n σ N ≤ residueCard O ^ (n * N) := by
  classical
  have hinj : Function.Injective
      (fun x : (Σ σ : {σ // σ ∈ S}, decidedSet O n σ.1 N) => (x.2 : Coeff O n N)) := by
    rintro ⟨σ, c⟩ ⟨τ, c'⟩ hcc
    simp only at hcc
    have hστ : (σ : FactorizationType) = (τ : FactorizationType) := by
      by_contra hne
      exact (Set.disjoint_left.1 (decidedSet_disjoint (O := O) (n := n) hne N)) c.2
        (by rw [hcc]; exact c'.2)
    obtain rfl : σ = τ := Subtype.ext hστ
    simpa using Subtype.ext hcc
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [card_coeff] at hle
  rw [Nat.card_sigma] at hle
  rw [← Finset.sum_attach S (fun σ => decidedCount O n σ N)]
  exact hle

theorem sum_decidedSeq_le_one (n : ℕ) (S : Finset FactorizationType) (N : ℕ) :
    ∑ σ ∈ S, decidedSeq O n σ N ≤ 1 := by
  have h := sum_decidedCount_le (O := O) n S N
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos _
  rw [show (∑ σ ∈ S, decidedSeq O n σ N)
      = (∑ σ ∈ S, (decidedCount O n σ N : ℝ)) / (residueCard O : ℝ) ^ (n * N) by
    rw [Finset.sum_div]; rfl, div_le_one hq]
  calc (∑ σ ∈ S, (decidedCount O n σ N : ℝ)) = ((∑ σ ∈ S, decidedCount O n σ N : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((residueCard O ^ (n * N) : ℕ) : ℝ) := Nat.cast_le.2 h
    _ = (residueCard O : ℝ) ^ (n * N) := by push_cast; rfl

/-- **Total mass ≤ 1.** The genuine densities of finitely many distinct types sum to at
most `1`. -/
theorem sum_genuineDensity_le_one (n : ℕ) (S : Finset FactorizationType) :
    ∑ σ ∈ S, genuineDensity O n σ ≤ 1 := by
  have hlim : Tendsto (fun N => ∑ σ ∈ S, decidedSeq O n σ N) atTop
      (𝓝 (∑ σ ∈ S, genuineDensity O n σ)) :=
    tendsto_finsetSum S (fun σ _ => decidedSeq_tendsto n σ)
  exact le_of_tendsto hlim (Eventually.of_forall (fun N => sum_decidedSeq_le_one n S N))

/-- **The complement upper bound.** Any level-`N` decided mass certified for *other* types
bounds `σ`'s density from above. With a matching lower bound `decidedSeq σ N ≤ genuineDensity σ`
this brackets the density from both sides at a finite level. -/
theorem genuineDensity_le_of_others (n : ℕ) (σ : FactorizationType) (S : Finset FactorizationType)
    (hσ : σ ∉ S) (N : ℕ) :
    genuineDensity O n σ ≤ 1 - ∑ τ ∈ S, decidedSeq O n τ N := by
  have h1 : ∑ τ ∈ insert σ S, genuineDensity O n τ ≤ 1 :=
    sum_genuineDensity_le_one n (insert σ S)
  rw [Finset.sum_insert hσ] at h1
  have h2 : ∑ τ ∈ S, decidedSeq O n τ N ≤ ∑ τ ∈ S, genuineDensity O n τ :=
    Finset.sum_le_sum (fun τ _ => decidedSeq_le_genuineDensity n τ N)
  linarith

end Total

end Uniformity.Density
