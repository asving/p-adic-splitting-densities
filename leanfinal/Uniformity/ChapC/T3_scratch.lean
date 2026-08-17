import Uniformity.ChapC.C107

set_option linter.style.longLine false
set_option linter.overlappingInstances false

namespace S7

open Uniformity Uniformity.Density.Tower Polynomial

theorem factors_mul_unit {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    {c a : α} (hc : IsUnit c) :
    UniqueFactorizationMonoid.factors (c * a) = UniqueFactorizationMonoid.factors a := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hca : c * a ≠ 0 := fun h => ha (hc.mul_right_eq_zero.1 h)
  have hassoc : Associated (c * a) a := (associated_unit_mul_left a c hc)
  have hpred : (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod (c * a))
      = (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod a) := by
    funext f
    exact propext ⟨fun h => ⟨h.1, h.2.trans hassoc⟩, fun h => ⟨h.1, h.2.trans hassoc.symm⟩⟩
  rw [UniqueFactorizationMonoid.factors, UniqueFactorizationMonoid.factors,
    dif_neg hca, dif_neg ha]
  congr 1

variable {K : Type*} [CommRing K] [IsDomain K] [Finite K]

theorem isUnit_ne_zero {c : K} (hc : c ≠ 0) : IsUnit c := by
  obtain ⟨d, hd⟩ := (Finite.isField_of_domain K).mul_inv_cancel hc
  exact ⟨⟨c, d, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

variable [UniqueFactorizationMonoid K]

theorem residualTypeOf_C_mul {c : K} (hc : c ≠ 0) (p : Polynomial K) :
    residualTypeOf (Polynomial.C c * p) = residualTypeOf p := by
  unfold residualTypeOf
  rw [factors_mul_unit (Polynomial.isUnit_C.2 (isUnit_ne_zero hc))]

theorem residualTypeOf_degree {p : Polynomial K} (hp : p ≠ 0) :
    (residualTypeOf p).degree = p.natDegree := by
  classical
  have h1 : (UniqueFactorizationMonoid.factors p).prod.natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.factors_prod hp))
  have hzero : (0 : Polynomial K) ∉ UniqueFactorizationMonoid.factors p := by
    intro h
    exact (UniqueFactorizationMonoid.irreducible_of_factor _ h).ne_zero rfl
  have h2 : ((UniqueFactorizationMonoid.factors p).map Polynomial.natDegree).sum
      = (UniqueFactorizationMonoid.factors p).prod.natDegree :=
    (Polynomial.natDegree_multiset_prod _ hzero).symm
  have h3 := Finset.sum_multiset_map_count (UniqueFactorizationMonoid.factors p)
      (fun q : Polynomial K => q.natDegree)
  show (((UniqueFactorizationMonoid.factors p).toFinset.val.map
      (fun q : Polynomial K => (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))).map
      (fun x : ℕ × ℕ => x.1 * x.2)).sum = p.natDegree
  rw [Multiset.map_map]
  have hcongr : ∀ q ∈ (UniqueFactorizationMonoid.factors p).toFinset,
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ (fun q : Polynomial K =>
        (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))) q
        = (UniqueFactorizationMonoid.factors p).count q • q.natDegree := by
    intro q _
    show q.natDegree * (UniqueFactorizationMonoid.factors p).count q
      = (UniqueFactorizationMonoid.factors p).count q • q.natDegree
    rw [smul_eq_mul, Nat.mul_comm]
  have key : ∑ q ∈ (UniqueFactorizationMonoid.factors p).toFinset,
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ (fun q : Polynomial K =>
        (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))) q = p.natDegree := by
    rw [Finset.sum_congr rfl hcongr, ← h3, h2, h1]
  exact key

end S7
