/-
Unit E8.rank_inj  (MovesD campaign, E-phase)  [AUX]
informal: on ONE eligible set, rank determines the factor (lex through the shared
`fieldEnum` is a strict total order — the note's "ordered lexicographically by
coefficient vectors in D.3(e)'s fixed residue bases").
deps (blueprint): E3, E6.  [as-built, 2026-07-30 verify-2 fold-in: imported only Defs;
E3's subfield identity was re-proved privately below (`poolSubfield_eq`) and E6's
`eligible_card_le` is not used — rank_inj needs no cardinality bound.]
[SYN2-S1 SWEEP-5, 2026-07-31: the verify-2 duplication is CLOSED — E3/E7 now imported;
`poolSubfield_eq` is a short corollary of E3's `frameField_eq_pool` (the cite, no
re-proof); `finite_eligible` DELETED, re-pointed at E7's de-privatized survivor
`finite_of_monic_natDegree`.]
sketch: equal Ranch-images + E3's common subfield give literally equal F-side eligible
sets; two members of a finite set with equal strict-initial-segment counts under a strict
total order are equal.  difficulty: medium-hard.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.E3_frameField
import LeanUrat.MovesD.E7_rankLt

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### `lexLt` is a strict linear order on `Polynomial F` -/

private lemma lexLt_irrefl (en : F ≃ Fin (Nat.card F)) (q : Polynomial F) :
    ¬ lexLt en q q := by
  rintro ⟨k, hk, -⟩
  exact absurd hk (lt_irrefl _)

private lemma lexLt_trans (en : F ≃ Fin (Nat.card F)) {a b c : Polynomial F}
    (hab : lexLt en a b) (hbc : lexLt en b c) : lexLt en a c := by
  obtain ⟨k1, h1, e1⟩ := hab
  obtain ⟨k2, h2, e2⟩ := hbc
  rcases lt_trichotomy k1 k2 with hlt | heq | hgt
  · refine ⟨k2, ?_, ?_⟩
    · rw [e1 k2 hlt]; exact h2
    · intro j hj; rw [e1 j (lt_trans hlt hj), e2 j hj]
  · subst heq
    refine ⟨k1, lt_trans h1 h2, ?_⟩
    intro j hj; rw [e1 j hj, e2 j hj]
  · refine ⟨k1, ?_, ?_⟩
    · rw [← e2 k1 hgt]; exact h1
    · intro j hj; rw [e1 j hj, e2 j (lt_trans hgt hj)]

private lemma lexLt_trichot (en : F ≃ Fin (Nat.card F)) {a b : Polynomial F}
    (h : a ≠ b) : lexLt en a b ∨ lexLt en b a := by
  have hd0 : a - b ≠ 0 := sub_ne_zero.mpr h
  have hcoeff : (a - b).coeff (a - b).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hd0
  have hne : a.coeff (a - b).natDegree ≠ b.coeff (a - b).natDegree := by
    intro he; apply hcoeff; rw [Polynomial.coeff_sub, he, sub_self]
  have habove : ∀ j, (a - b).natDegree < j → a.coeff j = b.coeff j := by
    intro j hj
    have hz : (a - b).coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hj
    rw [Polynomial.coeff_sub, sub_eq_zero] at hz
    exact hz
  have hen : en (a.coeff (a - b).natDegree) ≠ en (b.coeff (a - b).natDegree) :=
    fun he => hne (en.injective he)
  rcases lt_or_gt_of_ne hen with hlt | hgt
  · exact Or.inl ⟨(a - b).natDegree, hlt, habove⟩
  · exact Or.inr ⟨(a - b).natDegree, hgt, fun j hj => (habove j hj).symm⟩

/-! ### rank is injective on a finite set with a strict total order -/

private lemma rank_count_inj {α : Type*} [Finite α] (r : α → α → Prop)
    (hirr : ∀ x, ¬ r x x) (htr : ∀ x y z, r x y → r y z → r x z)
    (htri : ∀ x y, x ≠ y → r x y ∨ r y x)
    {a b : α} (h : Nat.card {x : α // r x a} = Nat.card {x : α // r x b}) : a = b := by
  by_contra hne
  have hA : Nat.card {x : α // r x a} = ({x | r x a}).ncard := rfl
  have hB : Nat.card {x : α // r x b} = ({x | r x b}).ncard := rfl
  rcases htri a b hne with hab | hba
  · have hss : {x | r x a} ⊂ {x | r x b} := by
      refine ⟨fun x hx => htr x a b hx hab, ?_⟩
      intro hsup
      exact hirr a (hsup hab)
    have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
    rw [← hA, ← hB] at hlt; omega
  · have hss : {x | r x b} ⊂ {x | r x a} := by
      refine ⟨fun x hx => htr x b a hx hba, ?_⟩
      intro hsup
      exact hirr b (hsup hba)
    have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
    rw [← hA, ← hB] at hlt; omega

/-! ### the eligible set is finite -/

/- [SYN2-S1 SWEEP-5, 2026-07-31] finite_eligible DELETED — supplied by E7's
de-privatized `finite_of_monic_natDegree` (EligibleImage extracts Monic ∧ natDegree = g). -/

/-! ### the pool subfield IS the matched frame field — E3's identity, CITED
[SYN2-S1 SWEEP-5, 2026-07-31: was "proved inline" (the verify-2 record); now the
Subfield-valued corollary of `E3.frameField_eq_pool`, single proof source.] -/

private lemma poolSubfield_eq {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    poolSubfield p R.w F = ν.σ.K := by
  classical
  have hcarrier : (ν.σ.K : Set F) = pool p R.w F := by
    rw [← frameField_eq_pool hM]
    exact Set.ext fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  have hex : ∃ S : Subfield F, (S : Set F) = pool p R.w F := ⟨ν.σ.K, hcarrier⟩
  have hpeq : poolSubfield p R.w F = hex.choose := by
    unfold poolSubfield; rw [dif_pos hex]
  rw [hpeq]
  apply SetLike.coe_injective
  rw [hex.choose_spec]
  exact hcarrier.symm

/-! ### ψ-image membership: ψImage ν is eligible for ν -/

private lemma psi_mem {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    EligibleImage p R.w ν.g ν.μ (RanchImage ν) (ψImage ν) := by
  simp only [ψImage, RanchImage, EligibleImage, OrdPsiPoly]
  refine ⟨ν.hψmonic.map _, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Polynomial.natDegree_map_eq_of_injective ν.σ.K.subtype.injective]; exact ν.hψdeg
  · obtain ⟨hdvd, -⟩ := ν.hOrd
    rw [← Polynomial.map_pow]
    exact (Polynomial.map_dvd_map ν.σ.K.subtype ν.σ.K.subtype.injective (ν.hψmonic.pow ν.μ)).mpr hdvd
  · obtain ⟨-, hnd⟩ := ν.hOrd
    rw [← Polynomial.map_pow]
    intro hc
    exact hnd ((Polynomial.map_dvd_map ν.σ.K.subtype ν.σ.K.subtype.injective
      (ν.hψmonic.pow (ν.μ + 1))).mp hc)
  · rw [poolSubfield_eq hM]
    exact ⟨ν.ψ, ν.hψirr, rfl⟩

/-- On one eligible set, equal rank forces equal ψ-image. -/
theorem rank_inj {R : ShapeRead} {ν ν' : Node p F} (hM : R.Matches ν) (hM' : R.Matches ν')
    (hg : ν.g = ν'.g) (hμ : ν.μ = ν'.μ) (hR : RanchImage ν = RanchImage ν')
    (hs : selRank R.w ν = selRank R.w ν') :
    ψImage ν = ψImage ν' := by
  -- membership of both ψ-images in the common (ν-parametrised) eligible set
  have hmem : EligibleImage p R.w ν.g ν.μ (RanchImage ν) (ψImage ν) := psi_mem hM
  have hmem' : EligibleImage p R.w ν.g ν.μ (RanchImage ν) (ψImage ν') := by
    rw [hg, hμ, hR]; exact psi_mem hM'
  -- express both counts over the very same (ν-parametrised) eligible set
  have e1 : selRank R.w ν
      = Nat.card {q : {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q}
          // lexLt (fieldEnum F) q.1 (ψImage ν)} := rfl
  have e2 : selRank R.w ν'
      = Nat.card {q : {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q}
          // lexLt (fieldEnum F) q.1 (ψImage ν')} := by
    show Nat.card {q : {q : Polynomial F // EligibleImage p R.w ν'.g ν'.μ (RanchImage ν') q}
            // lexLt (fieldEnum F) q.1 (ψImage ν')}
       = Nat.card {q : {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q}
            // lexLt (fieldEnum F) q.1 (ψImage ν')}
    rw [hg, hμ, hR]
  rw [e1, e2] at hs
  -- the common eligible subtype, with both ψ-images as members
  haveI : Finite {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q} :=
    finite_of_monic_natDegree ν.g _ (fun q h => ⟨h.1, h.2.1⟩)
  have key : (⟨ψImage ν, hmem⟩ :
        {q : Polynomial F // EligibleImage p R.w ν.g ν.μ (RanchImage ν) q})
      = ⟨ψImage ν', hmem'⟩ := by
    exact rank_count_inj
      (fun x y => lexLt (fieldEnum F) x.1 y.1)
      (fun x => lexLt_irrefl _ _)
      (fun x y z => lexLt_trans _)
      (fun x y hxy => lexLt_trichot _ (fun heq => hxy (Subtype.ext heq)))
      hs
  exact congrArg Subtype.val key

end LeanUrat.MovesD
