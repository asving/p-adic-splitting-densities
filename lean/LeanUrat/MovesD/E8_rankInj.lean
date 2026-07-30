/-
Unit E8.rank_inj  (MovesD campaign, E-phase)  [AUX]
informal: on ONE eligible set, rank determines the factor (lex through the shared
`fieldEnum` is a strict total order — the note's "ordered lexicographically by
coefficient vectors in D.3(e)'s fixed residue bases").
deps (blueprint): E3, E6.  [as-built, 2026-07-30 verify-2 fold-in: imports only Defs;
E3's subfield identity is re-proved privately below (`poolSubfield_eq`) and E6's
`eligible_card_le` is not used — rank_inj needs no cardinality bound.]
sketch: equal Ranch-images + E3's common subfield give literally equal F-side eligible
sets; two members of a finite set with equal strict-initial-segment counts under a strict
total order are equal.  difficulty: medium-hard.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

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

private lemma finite_eligible (w g μ : ℕ) (Rq : Polynomial F) :
    Finite {q : Polynomial F // EligibleImage p w g μ Rq q} := by
  apply Finite.of_injective
    (f := fun q : {q : Polynomial F // EligibleImage p w g μ Rq q} =>
      (fun i : Fin (g + 1) => q.1.coeff i))
  intro q q' hqq'
  apply Subtype.ext
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ g
  · simpa using congrFun hqq' ⟨i, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [q.2.2.1]; omega),
       Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [q'.2.2.1]; omega)]

/-! ### the pool subfield IS the matched frame field (E3, proved inline) -/

private lemma poolSubfield_eq {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    poolSubfield p R.w F = ν.σ.K := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcard, -⟩ := hM
  -- `hcard : Nat.card ↥ν.σ.K = p ^ R.w`
  have hcarrier : (ν.σ.K : Set F) = pool p R.w F := by
    -- the easy inclusion: a finite field of order `p^w` lies in the pool
    have hsub : (ν.σ.K : Set F) ⊆ pool p R.w F := by
      intro x hx
      simp only [pool, Set.mem_setOf_eq]
      haveI : Fintype ↥ν.σ.K := Fintype.ofFinite _
      have hcard' : Fintype.card ↥ν.σ.K = p ^ R.w := by
        rw [← Nat.card_eq_fintype_card]; exact hcard
      have hpow : (⟨x, hx⟩ : ↥ν.σ.K) ^ (p ^ R.w) = ⟨x, hx⟩ := by
        rw [← hcard']; exact FiniteField.pow_card _
      simpa using congrArg (fun z : ↥ν.σ.K => (z : F)) hpow
    -- the pool is finite of size `≤ p^w` (roots of `X^{p^w} - X`)
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hq2 : 2 ≤ p ^ R.w := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ R.w := Nat.pow_le_pow_right (by omega) R.hw
    have hφ0 : (Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F) ≠ 0 := by
      intro h0
      have hc1 : (Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F).coeff (p ^ R.w) = 1 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
            Polynomial.coeff_X_of_ne_one (by omega), sub_zero]
      rw [h0, Polynomial.coeff_zero] at hc1
      exact one_ne_zero hc1.symm
    have hset : pool p R.w F =
        (↑(Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F).roots.toFinset : Set F) := by
      ext x
      simp only [pool, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset,
                 Polynomial.mem_roots', hφ0, ne_eq, not_false_eq_true, true_and,
                 Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
                 Polynomial.eval_X, sub_eq_zero]
    have hpoolfin : (pool p R.w F).Finite := by
      rw [hset]; exact Finset.finite_toSet _
    have hpoolcard : (pool p R.w F).ncard ≤ p ^ R.w := by
      rw [hset, Set.ncard_coe_finset]
      calc (Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F).roots.toFinset.card
          ≤ Multiset.card (Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F).roots :=
            Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ (p ^ R.w) - Polynomial.X : Polynomial F).natDegree :=
            Polynomial.card_roots' _
        _ ≤ p ^ R.w := by
            refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
            rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
            exact max_le le_rfl (by omega)
    have hKcard : (ν.σ.K : Set F).ncard = p ^ R.w := hcard
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hKcard]; exact hpoolcard) hpoolfin
  -- convert the carrier equality into a subfield equality
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
    finite_eligible R.w ν.g ν.μ (RanchImage ν)
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
