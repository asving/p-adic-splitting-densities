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

    genuineDensity O n σ  :=  ⨅ N, possibleSeq σ N     (`possibleSeq_tendsto`: it IS the limit)
    decidedDensity O n σ  :=  ⨆ N, decidedSeq  σ N     (`decidedSeq_tendsto`)

**`genuineDensity` is THE density** (Asvin, 2026-08-13, Q5): the limit of the proportion of
level-`N` coefficient classes *consistent with* type `σ`. `decidedDensity` is the certified
**inner** approximation — the proportion of classes on which `σ` is already forced.

**Both are `ℝ`-valued theorem-backed limits, never values carried as data.** The sandwich
`decidedSeq ≤ decidedDensity ≤ genuineDensity ≤ possibleSeq` is proved, and the **drainage
tie** `gapSeq → 0 → genuineDensity = decidedDensity` (`genuineDensity_eq_of_drainage`, with
converse `drainage_of_genuineDensity_eq`) makes the drainage hypothesis do real work: without
it the two are only known to bracket each other. Drainage is *proved* unconditionally at
`n = 1` (`Gates.lean`) and at `n = 2` (`Drainage.lean`), so at those degrees every statement
about `decidedDensity` transfers verbatim to `genuineDensity`.

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

/-- **THE CERTIFIED (DECIDED) DENSITY**: the limit of the level-`N` *decided* proportions —
the proportion of level-`N` classes on which the type `σ` is already forced. It is a real
number defined as a supremum, and `decidedSeq_tendsto` proves it is the honest `N → ∞` limit.
It is an *inner* approximation: `decidedDensity ≤ genuineDensity` always
(`decidedDensity_le_genuineDensity`), with equality exactly when the gap drains
(`genuineDensity_eq_of_drainage` / `drainage_of_genuineDensity_eq`).

This is the object that used to be called `genuineDensity` before the 2026-08-13 rewire; the
name `genuineDensity` now belongs to the object below. -/
noncomputable def decidedDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
  ⨆ N, decidedSeq O n σ N

/-- **THE GENUINE DENSITY** of monic degree-`n` polynomials over `O` of splitting type `σ`:
**the limit of the proportion of level-`N` coefficient classes that are consistent with type
`σ`** (i.e. that have at least one monic degree-`n` lift of type `σ`). It is a real number
defined as an infimum, and `possibleSeq_tendsto` proves it is the honest `N → ∞` limit of
`possibleSeq`, which is antitone in `N`.

*Why this is THE density* (Asvin, 2026-08-13, Q5). Reading the coefficient space `O ^ n` at
level `N` cuts it into `q ^ (n·N)` equal boxes; the type-`σ` locus is covered by exactly the
boxes it meets, i.e. the `σ`-possible ones, so `possibleSeq σ N` is the level-`N` proportion
of the space that could still be type `σ`. Refining the level can only remove boxes, never
add them, so the proportions decrease and their limit exists: that limit is the density of
the type-`σ` locus read from *outside*. The inner reading is `decidedDensity`, and the two
agree exactly under drainage — which is proved unconditionally at `n = 1` and `n = 2`
(`genuineDensity_eq_decidedDensity_one`, `genuineDensity_eq_decidedDensity_two`).

*What this is NOT.* It is not asserted here to be the Haar measure of the type-`σ` locus:
that bridge needs measurability of the locus and is not formalized (see the unit note §3B.4).
`genuineDensity` is, formally, the limit of the consistent-class proportions, full stop. -/
noncomputable def genuineDensity (n : ℕ) (σ : FactorizationType) : ℝ :=
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

/-- **`decidedDensity` IS the limit of the decided proportions.** -/
theorem decidedSeq_tendsto (n : ℕ) (σ : FactorizationType) :
    Tendsto (decidedSeq O n σ) atTop (𝓝 (decidedDensity O n σ)) :=
  tendsto_atTop_ciSup (decidedSeq_mono n σ) (decidedSeq_bddAbove n σ)

/-- **`genuineDensity` IS the limit of the possible proportions.** -/
theorem possibleSeq_tendsto (n : ℕ) (σ : FactorizationType) :
    Tendsto (possibleSeq O n σ) atTop (𝓝 (genuineDensity O n σ)) :=
  tendsto_atTop_ciInf (possibleSeq_antitone n σ) (possibleSeq_bddBelow n σ)

theorem decidedSeq_le_decidedDensity (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    decidedSeq O n σ N ≤ decidedDensity O n σ :=
  le_ciSup (decidedSeq_bddAbove n σ) N

theorem genuineDensity_le_possibleSeq (n : ℕ) (σ : FactorizationType) (N : ℕ) :
    genuineDensity O n σ ≤ possibleSeq O n σ N :=
  ciInf_le (possibleSeq_bddBelow n σ) N

theorem decidedDensity_nonneg (n : ℕ) (σ : FactorizationType) : 0 ≤ decidedDensity O n σ :=
  le_trans (decidedSeq_nonneg n σ 0) (decidedSeq_le_decidedDensity n σ 0)

theorem decidedDensity_le_one (n : ℕ) (σ : FactorizationType) : decidedDensity O n σ ≤ 1 :=
  ciSup_le (fun N => decidedSeq_le_one n σ N)

theorem genuineDensity_nonneg (n : ℕ) (σ : FactorizationType) : 0 ≤ genuineDensity O n σ :=
  le_ciInf (fun N => possibleSeq_nonneg n σ N)

theorem genuineDensity_le_one (n : ℕ) (σ : FactorizationType) : genuineDensity O n σ ≤ 1 :=
  le_trans (genuineDensity_le_possibleSeq n σ 0) (possibleSeq_le_one n σ 0)

/-- **The sandwich.** The certified (decided, inner) density never exceeds the genuine
(possible, outer) one. -/
theorem decidedDensity_le_genuineDensity (n : ℕ) (σ : FactorizationType) :
    decidedDensity O n σ ≤ genuineDensity O n σ := by
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

/-- **THE DRAINAGE TIE.** If the ambiguity gap drains, the genuine (outer) density collapses
onto the certified (decided, inner) one, so the certified limit really *is* the density of
type-`σ` polynomials — not merely a lower bound for it. This is the theorem that makes a
drainage hypothesis load bearing rather than decorative, and it is the licence for every
`decidedDensity → genuineDensity` re-keying downstream. -/
theorem genuineDensity_eq_of_drainage {n : ℕ} {σ : FactorizationType}
    (h : UndecidedVanishes O n σ) : genuineDensity O n σ = decidedDensity O n σ := by
  have hlim : Tendsto (fun N => decidedSeq O n σ N + gapSeq O n σ N) atTop
      (𝓝 (decidedDensity O n σ + 0)) := (decidedSeq_tendsto n σ).add h
  have heq : (fun N => decidedSeq O n σ N + gapSeq O n σ N) = possibleSeq O n σ := by
    funext N; simp [gapSeq]
  rw [heq, add_zero] at hlim
  exact tendsto_nhds_unique (possibleSeq_tendsto n σ) hlim

/-- Converse direction: if the two densities agree, the gap drains. So `UndecidedVanishes` is
exactly the statement that the bracket closes. -/
theorem drainage_of_genuineDensity_eq {n : ℕ} {σ : FactorizationType}
    (h : genuineDensity O n σ = decidedDensity O n σ) : UndecidedVanishes O n σ := by
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

/-- **Total mass ≤ 1.** The *certified* (decided) densities of finitely many distinct types sum
to at most `1`. (The analogous statement for `genuineDensity` is FALSE in general: possible
sets overlap, so the outer proportions can sum to more than `1` at every finite level. What is
true unconditionally for `genuineDensity` is the *reverse* inequality over a covering menu —
`one_le_sum_genuineDensity` in §7.) -/
theorem sum_decidedDensity_le_one (n : ℕ) (S : Finset FactorizationType) :
    ∑ σ ∈ S, decidedDensity O n σ ≤ 1 := by
  have hlim : Tendsto (fun N => ∑ σ ∈ S, decidedSeq O n σ N) atTop
      (𝓝 (∑ σ ∈ S, decidedDensity O n σ)) :=
    tendsto_finsetSum S (fun σ _ => decidedSeq_tendsto n σ)
  exact le_of_tendsto hlim (Eventually.of_forall (fun N => sum_decidedSeq_le_one n S N))

/-- **The complement upper bound.** Any level-`N` decided mass certified for *other* types
bounds `σ`'s density from above. With a matching lower bound `decidedSeq σ N ≤ decidedDensity σ`
this brackets the density from both sides at a finite level. -/
theorem decidedDensity_le_of_others (n : ℕ) (σ : FactorizationType) (S : Finset FactorizationType)
    (hσ : σ ∉ S) (N : ℕ) :
    decidedDensity O n σ ≤ 1 - ∑ τ ∈ S, decidedSeq O n τ N := by
  have h1 : ∑ τ ∈ insert σ S, decidedDensity O n τ ≤ 1 :=
    sum_decidedDensity_le_one n (insert σ S)
  rw [Finset.sum_insert hσ] at h1
  have h2 : ∑ τ ∈ S, decidedSeq O n τ N ≤ ∑ τ ∈ S, decidedDensity O n τ :=
    Finset.sum_le_sum (fun τ _ => decidedSeq_le_decidedDensity n τ N)
  linarith

end Total

/-! ## 7. `Σ_σ R_σ = 1`: what holds unconditionally, and what needs drainage

Asvin, 2026-08-13 (Q5): *"let us prove that `Σ_σ R_σ = 1` using this definition"*. Over the
NEW `genuineDensity` the two halves have very different status, and this section states both
honestly.

* **`≥ 1` is UNCONDITIONAL** (`one_le_sum_genuineDensity`), given only that the finite menu
  `S` covers: every monic degree-`n` polynomial over `O` has its type in `S`. Reason: every
  class has a lift, that lift has *some* type, and the class is then possible for that type —
  so the `σ`-possible sets over `σ ∈ S` cover the whole box at every level, whence
  `Σ_σ possibleSeq σ N ≥ 1` for every `N`, and the inequality survives the limit.
* **`≤ 1` needs drainage** (`sum_genuineDensity_eq_one_of_drainage`). It is *false* for the
  raw level-`N` proportions — a class ambiguous between two types is counted twice — and only
  the vanishing of the ambiguity gap removes the double counting in the limit.

Consequently `Σ_σ genuineDensity O n σ = 1` is proved here **modulo drainage at every type of
the menu**, for every `n`; the unconditional general-`n` statement is exactly the general-`n`
drainage leg and is named (unproved) as `TotalMassOne` in `Statement.lean`. At `n = 1` and
`n = 2` drainage IS proved, so there the identity is unconditional. -/

section Cover

variable (O)

/-- **A covering menu at degree `n`**: a finite set `S` of splitting types containing the type
of *every* monic degree-`n` polynomial over `O`. This is the finiteness input that makes
`Σ_σ` meaningful — `FactorizationType` itself is infinite, and only finitely many types occur
in degree `n`. (At `n = 2`, `{split, inert, ram}` is such a menu — `typeOf_two_cases`.) -/
def CoveringMenu (n : ℕ) (S : Finset FactorizationType) : Prop :=
  ∀ a : Fin n → O, typeOf (monicPoly a) ∈ S

variable {O}

/-- Over a covering menu the `σ`-POSSIBLE sets cover every level-`N` box: a class has a lift,
the lift has a type, and that type is in the menu. -/
theorem card_le_sum_possibleCount {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) (N : ℕ) :
    residueCard O ^ (n * N) ≤ ∑ σ ∈ S, possibleCount O n σ N := by
  classical
  have hex : ∀ c : Coeff O n N, ∃ σ : {σ // σ ∈ S}, PossibleAt O n σ.1 N c := by
    intro c
    obtain ⟨a, ha⟩ := proj_surjective O n N c
    exact ⟨⟨typeOf (monicPoly a), h a⟩, a, ha, rfl⟩
  choose f hf using hex
  have hinj : Function.Injective (fun c : Coeff O n N =>
      (⟨f c, ⟨c, hf c⟩⟩ : Σ σ : {σ // σ ∈ S}, possibleSet O n σ.1 N)) := by
    intro c d hcd
    have := congrArg (fun x : (Σ σ : {σ // σ ∈ S}, possibleSet O n σ.1 N) =>
      (x.2 : Coeff O n N)) hcd
    simpa using this
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [card_coeff, Nat.card_sigma] at hle
  rw [← Finset.sum_attach S (fun σ => possibleCount O n σ N)]
  exact hle

/-- The level-`N` form: over a covering menu the possible proportions sum to at least `1`. -/
theorem one_le_sum_possibleSeq {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) (N : ℕ) : 1 ≤ ∑ σ ∈ S, possibleSeq O n σ N := by
  have hcount := card_le_sum_possibleCount h N
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos _
  rw [show (∑ σ ∈ S, possibleSeq O n σ N)
      = (∑ σ ∈ S, (possibleCount O n σ N : ℝ)) / (residueCard O : ℝ) ^ (n * N) by
    rw [Finset.sum_div]; rfl, le_div_iff₀ hq, one_mul]
  calc (residueCard O : ℝ) ^ (n * N) = ((residueCard O ^ (n * N) : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((∑ σ ∈ S, possibleCount O n σ N : ℕ) : ℝ) := Nat.cast_le.2 hcount
    _ = ∑ σ ∈ S, (possibleCount O n σ N : ℝ) := by push_cast; rfl

/-- **`Σ_σ R_σ ≥ 1`, UNCONDITIONALLY** (given a covering menu). This is the half of
`Σ_σ R_σ = 1` that the *outer* density gets for free — and it is the half that the certified
inner density `decidedDensity` can never have, because a decided class is decided for exactly
one type while the mass may sit forever in undecided classes. -/
theorem one_le_sum_genuineDensity {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) : 1 ≤ ∑ σ ∈ S, genuineDensity O n σ := by
  have hlim : Tendsto (fun N => ∑ σ ∈ S, possibleSeq O n σ N) atTop
      (𝓝 (∑ σ ∈ S, genuineDensity O n σ)) :=
    tendsto_finsetSum S (fun σ _ => possibleSeq_tendsto n σ)
  exact ge_of_tendsto hlim (Eventually.of_forall (fun N => one_le_sum_possibleSeq h N))

/-- **`Σ_σ R_σ = 1`, GENERAL `n`, MODULO DRAINAGE.** For any covering menu whose every type
drains, the genuine densities sum to exactly `1`. The `≥` half is unconditional
(`one_le_sum_genuineDensity`); the `≤` half is where drainage is spent — it converts each
`genuineDensity` into the corresponding `decidedDensity`, whose distinct types are disjoint
and hence sum to at most `1` (`sum_decidedDensity_le_one`). -/
theorem sum_genuineDensity_eq_one_of_drainage {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) (hd : ∀ σ ∈ S, UndecidedVanishes O n σ) :
    ∑ σ ∈ S, genuineDensity O n σ = 1 := by
  refine le_antisymm ?_ (one_le_sum_genuineDensity h)
  have hrw : ∑ σ ∈ S, genuineDensity O n σ = ∑ σ ∈ S, decidedDensity O n σ :=
    Finset.sum_congr rfl (fun σ hσ => genuineDensity_eq_of_drainage (hd σ hσ))
  rw [hrw]
  exact sum_decidedDensity_le_one n S

/-- The same, packaged as the drainage-free consequence people actually quote: under drainage
the genuine and certified total masses agree and both equal `1`. -/
theorem sum_decidedDensity_eq_one_of_drainage {n : ℕ} {S : Finset FactorizationType}
    (h : CoveringMenu O n S) (hd : ∀ σ ∈ S, UndecidedVanishes O n σ) :
    ∑ σ ∈ S, decidedDensity O n σ = 1 := by
  rw [← sum_genuineDensity_eq_one_of_drainage h hd]
  exact (Finset.sum_congr rfl (fun σ hσ => genuineDensity_eq_of_drainage (hd σ hσ))).symm

end Cover

end Uniformity.Density
