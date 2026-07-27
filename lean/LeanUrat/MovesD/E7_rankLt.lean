/-
Unit E7.selRank_lt  (MovesD campaign, E-phase)  [AUX]
[REV 4: re-verified against the TRANSPORTED `EligibleImage` (§3.4) — Fable#2 G1's
counterexample (six reducible ord-1 quadratics vs m̄ = 2) hits only the withdrawn gloss.]
informal: the defined rank is a legal selection index: selRank < m̄_r.
deps: E3, E6.
sketch: (i) MEMBERSHIP: ψImage ν satisfies the transported predicate — monic/deg/ord push
through the coefficient embedding, and ν.ψ itself is the irreducible lift over
↥σ.K ≃ poolSubfield (E3's identification); (ii) CARD: the transported eligible set pulls
back injectively to E6's K-side set, so its card ≤ m̄; rank = a proper-initial-segment
count in a set of card ≤ m̄ containing ψImage.  difficulty: medium-hard.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.E3_frameField
import LeanUrat.MovesD.E6_eligibleCard

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC Polynomial

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Finiteness of any subtype of monic degree-`g` polynomials over a finite field:
the coefficient tuple `(coeff 0, …, coeff g)` determines the polynomial. -/
private lemma finite_of_monic_natDegree {K : Type*} [Field K] [Finite K] (g : ℕ)
    (S : Polynomial K → Prop) (hS : ∀ q, S q → q.Monic ∧ q.natDegree = g) :
    Finite {q : Polynomial K // S q} := by
  apply Finite.of_injective (β := (Fin (g + 1) → K)) (fun q => fun i : Fin (g + 1) => q.1.coeff i)
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  obtain ⟨-, hqd⟩ := hS q hq
  obtain ⟨-, hq'd⟩ := hS q' hq'
  apply Subtype.ext
  change q = q'
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ g
  · simpa using congrFun h ⟨k, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hqd]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hq'd]; omega)]

/-- The defined rank is a legal selection index: selRank < m̄_r. -/
theorem selRank_lt {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    selRank R.w ν < R.mbar := by
  classical
  -- Step 1. The frame field IS the pool subfield (E3's identification, as an equality of
  -- `Subfield F`: two subfields with the same carrier coincide).
  have hcarrier : (ν.σ.K : Set F) = pool p R.w F := by
    rw [← frameField_eq_pool hM]; exact Subtype.range_coe.symm
  have hex : ∃ S : Subfield F, (S : Set F) = pool p R.w F := ⟨ν.σ.K, hcarrier⟩
  have hKeq : poolSubfield p R.w F = ν.σ.K := by
    have hcoe : (poolSubfield p R.w F : Set F) = pool p R.w F := by
      unfold poolSubfield
      rw [dif_pos hex]
      exact hex.choose_spec
    apply SetLike.coe_injective
    rw [hcoe, hcarrier]
  -- The injective coefficient embedding `↥ν.σ.K ↪ F`.
  have hinj : Function.Injective ν.σ.K.subtype := Subfield.subtype_injective ν.σ.K
  -- Step 2. MEMBERSHIP: ψImage ν is an eligible F-side factor.
  have hmem : EligibleImage p R.w ν.g ν.μ (RanchImage ν) (ψImage ν) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- monic
      change (ν.ψ.map ν.σ.K.subtype).Monic
      exact ν.hψmonic.map _
    · -- degree g
      change (ν.ψ.map ν.σ.K.subtype).natDegree = ν.g
      rw [natDegree_map_eq_of_injective hinj]
      exact ν.hψdeg
    · -- ord_ψ = μ
      change OrdPsiPoly (ν.ψ.map ν.σ.K.subtype) (ν.Ranch.map ν.σ.K.subtype) ν.μ
      refine ⟨?_, ?_⟩
      · rw [← Polynomial.map_pow]
        exact (map_dvd_map ν.σ.K.subtype hinj (ν.hψmonic.pow _)).mpr ν.hOrd.1
      · intro hcon
        rw [← Polynomial.map_pow] at hcon
        exact ν.hOrd.2 ((map_dvd_map ν.σ.K.subtype hinj (ν.hψmonic.pow _)).mp hcon)
    · -- irreducible lift over the pool subfield
      rw [hKeq]
      exact ⟨ν.ψ, ν.hψirr, rfl⟩
  -- Irreflexivity of the lex order (so ψImage is not counted by its own rank).
  have hirrefl : ¬ lexLt (fieldEnum F) (ψImage ν) (ψImage ν) := by
    rintro ⟨k, hk, -⟩
    exact absurd hk (lt_irrefl _)
  -- Step 3. Pull each eligible F-side factor back to a K-side eligible factor.
  have key : ∀ (q : Polynomial F), EligibleImage p R.w ν.g ν.μ (RanchImage ν) q →
      ∃ q₀ : Polynomial ↥ν.σ.K,
        (q₀.Monic ∧ Irreducible q₀ ∧ q₀.natDegree = ν.g ∧ OrdPsiPoly q₀ ν.Ranch ν.μ)
        ∧ q₀.map ν.σ.K.subtype = q := by
    intro q hq
    obtain ⟨q₀, hirr, hmap⟩ : ∃ q₀ : Polynomial ↥ν.σ.K, Irreducible q₀ ∧ q₀.map ν.σ.K.subtype = q := by
      have h4 := hq.2.2.2
      rw [hKeq] at h4
      exact h4
    have hmonq0 : q₀.Monic := by
      apply (Function.Injective.monic_map_iff hinj).mpr
      rw [hmap]; exact hq.1
    have hdeg : q₀.natDegree = ν.g := by
      rw [← natDegree_map_eq_of_injective hinj q₀, hmap]
      exact hq.2.1
    have hord : OrdPsiPoly q₀ ν.Ranch ν.μ := by
      refine ⟨?_, ?_⟩
      · apply (map_dvd_map ν.σ.K.subtype hinj (hmonq0.pow ν.μ)).mp
        rw [Polynomial.map_pow, hmap]
        exact hq.2.2.1.1
      · intro hcon
        apply hq.2.2.1.2
        have hd : (q₀ ^ (ν.μ + 1)).map ν.σ.K.subtype ∣ ν.Ranch.map ν.σ.K.subtype :=
          (map_dvd_map ν.σ.K.subtype hinj (hmonq0.pow (ν.μ + 1))).mpr hcon
        rw [Polynomial.map_pow, hmap] at hd
        exact hd
    exact ⟨q₀, ⟨hmonq0, hirr, hdeg, hord⟩, hmap⟩
  -- Finiteness of both eligible sets (subtypes of monic degree-g polynomials).
  haveI hfinK :
      Finite {q : Polynomial ↥ν.σ.K //
        q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} :=
    finite_of_monic_natDegree ν.g _ (fun q h => ⟨h.1, h.2.2.1⟩)
  haveI hfinF :
      Finite {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q} :=
    finite_of_monic_natDegree ν.g _ (fun q h => ⟨h.1, h.2.1⟩)
  -- The F-side eligible set injects into the K-side one, so its cardinality is ≤.
  have hcardle : Nat.card {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q}
      ≤ Nat.card {q : Polynomial ↥ν.σ.K //
          q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} := by
    apply Nat.card_le_card_of_injective
      (f := fun q : {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q} =>
        (⟨(key q.1 q.2).choose, (key q.1 q.2).choose_spec.1⟩ :
          {q : Polynomial ↥ν.σ.K //
            q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ}))
    intro a b h
    have e1 : (key a.1 a.2).choose = (key b.1 b.2).choose := congrArg Subtype.val h
    apply Subtype.ext
    calc a.1 = (key a.1 a.2).choose.map ν.σ.K.subtype := ((key a.1 a.2).choose_spec.2).symm
      _ = (key b.1 b.2).choose.map ν.σ.K.subtype := by rw [e1]
      _ = b.1 := (key b.1 b.2).choose_spec.2
  -- The rank is a strict-initial-segment count of a finite set containing ψImage.
  have hstrict : selRank R.w ν
      < Nat.card {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q} := by
    unfold selRank
    exact Finite.card_subtype_lt (x := ⟨ψImage ν, hmem⟩) hirrefl
  -- m̄_r equals E6's bound under the shape match.
  have hmbar : (ν.wSide / ν.e) / (ν.g * ν.μ) = R.mbar := by
    simp only [ShapeRead.mbar, ShapeRead.len]
    rw [hM.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.2.2.1]
  -- Chain: selRank < card(F-side) ≤ card(K-side) ≤ ⌊ℓ/(gμ)⌋ = m̄.
  refine lt_of_lt_of_le hstrict (le_trans hcardle ?_)
  rw [← hmbar]
  exact eligible_card_le ν

end LeanUrat.MovesD
