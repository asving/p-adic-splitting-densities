import LeanUrat.OM.CellCard

/-!
# The general residual-shape count tie — `shapeCount = choicePoly.eval`

This module proves the **multiplicativity-over-degrees crux** (`card_shapeSet_prod`) for the
per-side residual-shape count `CellCard.shapeCount`, the **RHS choice-polynomial evaluation bridge**
(`choicePoly_eval_prod`, tying `OMCountV2.choicePoly` to a product of falling factorials over the
punctured pools), and the **reduction of the full tie to the single-degree count**
(`shapeCount_tie_general_of_singleDegree`).

## What is proved (all `sorry`-free, core-only axioms)

* `card_shapeSet_prod` (**crux #1, blueprint step 1**): for any factorization-shape multiset `L`,
  `shapeCount` factors as the product over the distinct factor-degrees `d` of the degree-`d` block
  count `Nat.card (shapeSet (L.filter (·.1 = d)))`.  Mechanism: a monic prime-to-`X` polynomial
  factors uniquely as the product of its degree-`d` blocks `blockAt M d`, the blocks are pairwise
  coprime (distinct-degree factors share no irreducible), and `polyShape` is additive on coprime
  products (`CellMenu.polyShape_mul`); this yields a bijection to the product of block-shape sets
  (`Nat.card_eq_of_bijective` + `Nat.card_pi`), exactly mirroring `Order0.card_sepStratum`.
* `choicePoly_eval_prod` (**RHS bridge, uses blueprint step 3**): `(choicePoly true L).eval p`
  equals `∏_d  descFactorial (avail (ZMod p) d) k_d / symFactor L d`, `k_d = (L.map fst).count d`,
  via `Order0.availPoly_eval` (the banked necklace cross-tie `necklaceQ_eq_card` at `d ≥ 2`, the
  `q-1` punctured linear pool at `d = 1`) and the descending-factorial identity for `ffPoly`.
* `shapeCount_tie_general_of_singleDegree` (**assembly**): the target tie
  `(shapeCount p l : ℚ) = (choicePoly true l).eval p` follows from the crux and the bridge GIVEN the
  single-degree count `hSingle` (blueprint step 2).

## The single-degree count (blueprint step 2, now PROVED) and the unconditional tie

* `single_degree_count` (**blueprint step 2**): for `d ≥ 1` and a pure degree-`d` slice `L`
  (all first coordinates `= d`, all multiplicities `≥ 1`), the number of monic prime-to-`X`
  polynomials of shape `L` equals `descFactorial (avail_d, |L|) / symFactorMultiset L`.  Mechanism:
  build `M = ∏ (eᵢ)^(wᵢ)` from an injection `e : Fin |L| ↪ pool_d` and an exponent word `w`
  enumerating `L`'s multiplicities; `buildPoly` lands in the shape set (UFM: `normalizedFactors` is
  additive on the prime powers), is surjective onto it, and its fibers are the word-stabilizer of
  `w`, counted by `DomMulAct.stabilizer_card' = ∏_μ c_μ!`.  Combined with `Fintype.card_embedding_eq`
  (`#(Fin k ↪ pool) = descFactorial(|pool|,k)`) this gives `descFactorial = |shapeSet|·symFactor`.
* `shapeCount_tie_general` (**UNCONDITIONAL**): the general tie
  `(shapeCount p l : ℚ) = (choicePoly true l).eval p` for any `l` with positive degrees AND positive
  multiplicities — `hSingle` DISCHARGED by `single_degree_count`.
* `cell_card_mCell_uncond` (**blueprint step 4, keystone**): the per-cell census
  `cell_card_mCell` with its `hties` hypothesis discharged (positivity of the shapes' entries comes
  from `mem_shapesOfDegree_iff`).
-/

open Polynomial
namespace LeanUrat.OM.ShapeCountTie
open LeanUrat.OM LeanUrat.OM.CellCard LeanUrat.OM.OMCountV2 LeanUrat.OM.Order0 LeanUrat.OM.CellMenu
open UniqueFactorizationMonoid
open scoped Classical

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Foundational facts -/

theorem not_X_dvd_iff {M : (ZMod p)[X]} (hmon : M.Monic) :
    ¬ X ∣ M ↔ X ∉ normalizedFactors M := by
  classical
  refine ⟨fun hX hmem => hX (dvd_of_mem_normalizedFactors hmem), fun hX hdvd => hX ?_⟩
  exact (Polynomial.mem_normalizedFactors_iff hmon.ne_zero).mpr ⟨prime_X.irreducible, monic_X, hdvd⟩

theorem multiset_eq_sum_filter {α β : Type*} [DecidableEq β] (s : Multiset α) (key : α → β) :
    s = ∑ b ∈ (s.map key).toFinset, s.filter (fun a => key a = b) := by
  classical
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have hkey : key a ∈ (s.map key).toFinset :=
      Multiset.mem_toFinset.mpr (Multiset.mem_map_of_mem key ha)
    rw [Multiset.count_sum', Finset.sum_eq_single (key a)]
    · rw [Multiset.count_filter, if_pos rfl]
    · intro b _ hb; rw [Multiset.count_filter, if_neg (fun h => hb h.symm)]
    · intro hnot; exact absurd hkey hnot
  · rw [Multiset.count_eq_zero.mpr ha, Multiset.count_sum']
    refine (Finset.sum_eq_zero ?_).symm
    intro b _; rw [Multiset.count_filter]
    split
    · exact Multiset.count_eq_zero.mpr ha
    · rfl

/-! ## Per-degree blocks (crux #1: multiplicativity over degrees) -/

noncomputable def blockAt (M : (ZMod p)[X]) (d : ℕ) : (ZMod p)[X] :=
  ((normalizedFactors M).filter (fun ψ => ψ.natDegree = d)).prod

lemma nf_blockAt (M : (ZMod p)[X]) (d : ℕ) :
    normalizedFactors (blockAt p M d) = (normalizedFactors M).filter (fun ψ => ψ.natDegree = d) := by
  classical
  unfold blockAt
  set s := (normalizedFactors M).filter (fun ψ => ψ.natDegree = d) with hs
  have hirr : ∀ ψ ∈ s, Irreducible ψ :=
    fun ψ hψ => irreducible_of_normalized_factor ψ (Multiset.mem_filter.mp hψ).1
  have hmon : ∀ ψ ∈ s, ψ.Monic :=
    fun ψ hψ => Order0.monic_of_mem_normalizedFactors (Multiset.mem_filter.mp hψ).1
  rw [normalizedFactors_prod_eq s hirr,
    Multiset.map_congr rfl (fun ψ hψ => (hmon ψ hψ).normalize_eq_self), Multiset.map_id']

lemma blockAt_monic (M : (ZMod p)[X]) (d : ℕ) : (blockAt p M d).Monic := by
  unfold blockAt
  have h := monic_multiset_prod_of_monic
    ((normalizedFactors M).filter (fun ψ => ψ.natDegree = d)) id
    (fun ψ hψ => Order0.monic_of_mem_normalizedFactors (Multiset.mem_filter.mp hψ).1)
  rwa [Multiset.map_id] at h

lemma blockAt_notX {M : (ZMod p)[X]} (hX : ¬ X ∣ M) (d : ℕ) : ¬ X ∣ (blockAt p M d) := by
  unfold blockAt
  intro hdvd
  obtain ⟨ψ, hψs, hXψ⟩ := Prime.exists_mem_multiset_dvd prime_X hdvd
  rw [Multiset.mem_filter] at hψs
  have hψmon : ψ.Monic := Order0.monic_of_mem_normalizedFactors hψs.1
  have hirr : Irreducible ψ := irreducible_of_normalized_factor ψ hψs.1
  exact Order0.ne_X_of_not_X_dvd hX hψs.1
    (eq_of_monic_of_associated monic_X hψmon (irreducible_X.associated_of_dvd hirr hXψ)).symm

lemma prod_blockAt {M : (ZMod p)[X]} (hmon : M.Monic) :
    ∏ d ∈ ((normalizedFactors M).map Polynomial.natDegree).toFinset, blockAt p M d = M := by
  classical
  unfold blockAt
  rw [← Multiset.prod_sum, ← multiset_eq_sum_filter (normalizedFactors M) Polynomial.natDegree,
    Order0.prod_normalizedFactors_of_monic hmon]

lemma polyShape_blockAt (M : (ZMod p)[X]) (d : ℕ) :
    polyShape p (blockAt p M d) = (polyShape p M).filter (fun q => q.1 = d) := by
  letI := Classical.decEq ((ZMod p)[X])
  unfold polyShape
  rw [nf_blockAt, Multiset.filter_map]
  simp only [Function.comp_apply]
  have hsupp : (Multiset.filter (fun ψ => ψ.natDegree = d) (normalizedFactors M)).toFinset.val
      = Multiset.filter (fun ψ => ψ.natDegree = d) (normalizedFactors M).toFinset.val := by
    rw [Multiset.toFinset_filter, Finset.filter_val]
  refine Multiset.map_congr hsupp ?_
  intro ψ hψ
  rw [Multiset.mem_filter] at hψ
  congr 1
  rw [Multiset.count_filter, if_pos hψ.2]


lemma exists_mem_polyShape_fst {M : (ZMod p)[X]} {ψ : (ZMod p)[X]}
    (hψ : ψ ∈ normalizedFactors M) :
    ∃ q ∈ polyShape p M, q.1 = ψ.natDegree := by
  letI := Classical.decEq ((ZMod p)[X])
  refine ⟨(ψ.natDegree, (normalizedFactors M).count ψ), ?_, rfl⟩
  unfold polyShape
  exact Multiset.mem_map_of_mem _ (by rw [Finset.mem_val, Multiset.mem_toFinset]; exact hψ)

lemma degFinset_eq_polyShape_fst (M : (ZMod p)[X]) :
    ((normalizedFactors M).map Polynomial.natDegree).toFinset
      = ((polyShape p M).map Prod.fst).toFinset := by
  letI := Classical.decEq ((ZMod p)[X])
  unfold polyShape
  rw [Multiset.map_map]
  have hcomp : ((fun q : ℕ×ℕ => q.1) ∘
      (fun ψ : (ZMod p)[X] => (ψ.natDegree, (normalizedFactors M).count ψ)))
      = Polynomial.natDegree := funext (fun ψ => rfl)
  rw [hcomp]
  ext a
  simp only [Multiset.mem_toFinset, Multiset.mem_map]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩; exact ⟨ψ, Multiset.mem_toFinset.mpr hψ, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    rw [Finset.mem_val, Multiset.mem_toFinset] at hψ
    exact ⟨ψ, hψ, rfl⟩

lemma coprime_of_factorDeg {A B : (ZMod p)[X]} {d e : ℕ} (hde : d ≠ e)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hAdeg : ∀ ψ ∈ normalizedFactors A, ψ.natDegree = d)
    (hBdeg : ∀ ψ ∈ normalizedFactors B, ψ.natDegree = e) :
    IsCoprime A B := by
  rw [← isRelPrime_iff_isCoprime, isRelPrime_iff_no_prime_factors hA]
  intro q hqA hqB hqprime
  have hirr : Irreducible q := hqprime.irreducible
  obtain ⟨ψA, hψA, hassocA⟩ := exists_mem_normalizedFactors_of_dvd hA hirr hqA
  obtain ⟨ψB, hψB, hassocB⟩ := exists_mem_normalizedFactors_of_dvd hB hirr hqB
  have hAB : Associated ψA ψB := hassocA.symm.trans hassocB
  have hdeg : ψA.natDegree = ψB.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hAB)
  rw [hAdeg ψA hψA, hBdeg ψB hψB] at hdeg
  exact hde hdeg


/-! ## The block-shape set and the crux count decomposition -/

/-- Monic, prime-to-`X` polynomials whose factorization shape is `sh` — the general shape set
whose cardinality is `shapeCount`. -/
def shapeSet (sh : Multiset (ℕ × ℕ)) : Set (ZMod p)[X] :=
  {M : (ZMod p)[X] | M.Monic ∧ ¬ X ∣ M ∧ polyShape p M = sh}

lemma shapeCount_eq_card (l : List (ℕ × ℕ)) :
    shapeCount p l = Nat.card (shapeSet p (l : Multiset (ℕ × ℕ))) := rfl

/-- The polyShape of a finset product of pairwise-coprime (distinct-degree) monic factors is the
sum of the block shapes. Here `B d` is monic prime-to-X with all factors of degree `d`. -/
lemma polyShape_finset_prod {s : Finset ℕ} (B : ℕ → (ZMod p)[X])
    (hne : ∀ d ∈ s, B d ≠ 0)
    (hdeg : ∀ d ∈ s, ∀ ψ ∈ normalizedFactors (B d), ψ.natDegree = d) :
    polyShape p (∏ d ∈ s, B d) = ∑ d ∈ s, polyShape p (B d) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      -- polyShape of 1 = 0
      unfold polyShape
      rw [normalizedFactors_one]; simp
  | cons a t ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons]
      have hBa0 : B a ≠ 0 := hne a (Finset.mem_cons_self a t)
      have hprod0 : (∏ d ∈ t, B d) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        exact fun d hd => hne d (Finset.mem_cons_of_mem hd)
      -- coprimality of B a with the rest: every factor of ∏_t has degree ≠ a
      have hcop : IsCoprime (B a) (∏ d ∈ t, B d) := by
        rw [← isRelPrime_iff_isCoprime, isRelPrime_iff_no_prime_factors hBa0]
        intro q hqA hqB hqp
        obtain ⟨ψA, hψA, hassocA⟩ := exists_mem_normalizedFactors_of_dvd hBa0 hqp.irreducible hqA
        -- q divides ∏_t ⟹ divides some B d, d ∈ t
        obtain ⟨d, hd, hqBd⟩ := (hqp.dvd_finsetProd_iff B).mp hqB
        have hBd0 : B d ≠ 0 := hne d (Finset.mem_cons_of_mem hd)
        obtain ⟨ψB, hψB, hassocB⟩ := exists_mem_normalizedFactors_of_dvd hBd0 hqp.irreducible hqBd
        have hAB : Associated ψA ψB := hassocA.symm.trans hassocB
        have hdegeq : ψA.natDegree = ψB.natDegree :=
          Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hAB)
        rw [hdeg a (Finset.mem_cons_self a t) ψA hψA,
            hdeg d (Finset.mem_cons_of_mem hd) ψB hψB] at hdegeq
        exact ha (hdegeq ▸ hd)
      rw [polyShape_mul p hBa0 hprod0 hcop, ih (fun d hd => hne d (Finset.mem_cons_of_mem hd))
        (fun d hd => hdeg d (Finset.mem_cons_of_mem hd))]



lemma filter_finset_sum {α β : Type*} [DecidableEq β] (P : α → Prop) [DecidablePred P]
    (s : Finset β) (f : β → Multiset α) :
    (∑ e ∈ s, f e).filter P = ∑ e ∈ s, (f e).filter P := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, Multiset.filter_add, ih]

lemma nf_finset_prod {s : Finset ℕ} (B : ℕ → (ZMod p)[X]) (hne : ∀ d ∈ s, B d ≠ 0) :
    normalizedFactors (∏ d ∈ s, B d) = ∑ d ∈ s, normalizedFactors (B d) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [normalizedFactors_one]
  | cons a t ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons]
      have hBa0 : B a ≠ 0 := hne a (Finset.mem_cons_self a t)
      have hprod0 : (∏ d ∈ t, B d) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]; exact fun d hd => hne d (Finset.mem_cons_of_mem hd)
      rw [normalizedFactors_mul hBa0 hprod0, ih (fun d hd => hne d (Finset.mem_cons_of_mem hd))]

lemma blockAt_finset_prod {s : Finset ℕ} (B : ℕ → (ZMod p)[X]) (hne : ∀ d ∈ s, B d ≠ 0)
    (hmon : ∀ d ∈ s, (B d).Monic)
    (hdeg : ∀ d ∈ s, ∀ ψ ∈ normalizedFactors (B d), ψ.natDegree = d)
    {d : ℕ} (hd : d ∈ s) :
    blockAt p (∏ e ∈ s, B e) d = B d := by
  classical
  unfold blockAt
  rw [nf_finset_prod p B hne, filter_finset_sum]
  have hfilt : ∀ e ∈ s, (normalizedFactors (B e)).filter (fun ψ => ψ.natDegree = d)
      = if e = d then normalizedFactors (B d) else 0 := by
    intro e he
    split
    · next hed => subst hed
                  exact Multiset.filter_eq_self.mpr (fun ψ hψ => hdeg e he ψ hψ)
    · next hed => refine Multiset.filter_eq_nil.mpr (fun ψ hψ hcontra => ?_)
                  rw [hdeg e he ψ hψ] at hcontra
                  exact hed hcontra
  rw [Finset.sum_congr rfl hfilt, Finset.sum_ite_eq' s d, if_pos hd,
    Order0.prod_normalizedFactors_of_monic (hmon d hd)]

/-! ## Crux #1: `shapeCount` is multiplicative over degrees -/

/-- **Crux (multiplicativity over degrees).** For any shape multiset `L`, the count of monic
prime-to-`X` polynomials of shape `L` is the product over the distinct factor-degrees of the
count of the degree-`d` block shape `L.filter (·.1 = d)`. -/
theorem card_shapeSet_prod (L : Multiset (ℕ × ℕ)) :
    Nat.card (shapeSet p L)
      = ∏ d ∈ (L.map Prod.fst).toFinset, Nat.card (shapeSet p (L.filter (fun q => q.1 = d))) := by
  classical
  set Ds := (L.map Prod.fst).toFinset with hDs
  -- Bijection shapeSet L ≃ Π (d : Ds), shapeSet (L.filter (·.1=d))
  have key : Nat.card (shapeSet p L)
      = Nat.card ((d : Ds) → shapeSet p (L.filter (fun q => q.1 = (d : ℕ)))) := by
    refine Nat.card_eq_of_bijective
      (fun M d => ⟨blockAt p (M : (ZMod p)[X]) (d : ℕ), ?_, ?_, ?_⟩) ⟨?_, ?_⟩
    · exact blockAt_monic p _ _
    · exact blockAt_notX p M.2.2.1 _
    · rw [polyShape_blockAt, M.2.2.2]
    · -- injective
      intro M N hMN
      refine Subtype.ext ?_
      have hMdegs : ((normalizedFactors (M : (ZMod p)[X])).map Polynomial.natDegree).toFinset = Ds := by
        rw [degFinset_eq_polyShape_fst, M.2.2.2]
      have hNdegs : ((normalizedFactors (N : (ZMod p)[X])).map Polynomial.natDegree).toFinset = Ds := by
        rw [degFinset_eq_polyShape_fst, N.2.2.2]
      rw [← prod_blockAt p M.2.1, ← prod_blockAt p N.2.1, hMdegs, hNdegs]
      refine Finset.prod_congr rfl (fun d hd => ?_)
      have := congrArg Subtype.val (congrFun hMN ⟨d, hd⟩)
      exact this
    · -- surjective
      intro y
      -- assemble M = ∏_{d ∈ Ds} (y d)
      set B : ℕ → (ZMod p)[X] := fun d =>
        if hd : d ∈ Ds then ((y ⟨d, hd⟩ : (ZMod p)[X])) else 1 with hB_def
      have hB_eq : ∀ (d : ℕ) (hd : d ∈ Ds), B d = (y ⟨d, hd⟩ : (ZMod p)[X]) := by
        intro d hd; simp only [hB_def]; rw [dif_pos hd]
      have hBmon : ∀ d ∈ Ds, (B d).Monic := by
        intro d hd; rw [hB_eq d hd]; exact (y ⟨d, hd⟩).2.1
      have hBne : ∀ d ∈ Ds, B d ≠ 0 := fun d hd => (hBmon d hd).ne_zero
      have hBshape : ∀ d ∈ Ds, polyShape p (B d) = L.filter (fun q => q.1 = d) := by
        intro d hd; rw [hB_eq d hd]; exact (y ⟨d, hd⟩).2.2.2
      -- degree of factors of B d is d
      have hBdeg : ∀ d ∈ Ds, ∀ ψ ∈ normalizedFactors (B d), ψ.natDegree = d := by
        intro d hd ψ hψ
        -- (deg ψ, count ψ) ∈ polyShape (B d) = L.filter (·.1=d), so first coord = d
        obtain ⟨q, hqmem, hq1⟩ := exists_mem_polyShape_fst p hψ
        rw [hBshape d hd, Multiset.mem_filter] at hqmem
        rw [← hq1]; exact hqmem.2
      set M : (ZMod p)[X] := ∏ d ∈ Ds, B d with hM_def
      have hMmon : M.Monic := by
        rw [hM_def]
        exact monic_prod_of_monic _ _ (fun d hd => hBmon d hd)
      have hMne : M ≠ 0 := hMmon.ne_zero
      have hMshape : polyShape p M = L := by
        rw [hM_def, polyShape_finset_prod p B hBne hBdeg]
        rw [Finset.sum_congr rfl hBshape]
        -- ∑_{d ∈ Ds} L.filter(·.1=d) = L  (group by first coordinate)
        rw [← multiset_eq_sum_filter L Prod.fst]
      have hMX : ¬ X ∣ M := by
        rw [not_X_dvd_iff p hMmon]
        intro hXmem
        -- X would be a factor of degree 1, but then (1, count) ∈ polyShape = L, and X ∈ B 1
        -- Simpler: X ∣ M ⟹ X ∣ some B d ⟹ contradiction with prime-to-X of block? blocks are y d
        -- Use: X ∈ nf M and nf M via product. Actually derive X ∣ M then X ∣ some B d.
        have hXdvd : X ∣ M := dvd_of_mem_normalizedFactors hXmem
        rw [hM_def] at hXdvd
        obtain ⟨d, hd, hXBd⟩ := (prime_X.dvd_finsetProd_iff B).mp hXdvd
        have : ¬ X ∣ B d := by rw [hB_eq d hd]; exact (y ⟨d, hd⟩).2.2.1
        exact this hXBd
      refine ⟨⟨M, hMmon, hMX, hMshape⟩, ?_⟩
      funext d
      refine Subtype.ext ?_
      show blockAt p M (d : ℕ) = (y d : (ZMod p)[X])
      rw [← hB_eq (d : ℕ) d.2, hM_def]
      exact blockAt_finset_prod p B hBne hBmon hBdeg d.2
  rw [key, Nat.card_pi, ← Finset.prod_coe_sort Ds
    (fun d => Nat.card (shapeSet p (L.filter (fun q => q.1 = d))))]


/-! ## Single-degree count (blueprint step 2): the residual-shape count per degree -/

/-- The pool as a subtype (finite field, degree d). -/
abbrev Pool (d : ℕ) := ↥(Order0.poolFinset (ZMod p) d)

/-- Build a monic polynomial from a word of exponents and an assignment of pool elements. -/
noncomputable def buildPoly {d n : ℕ} (w : Fin n → ℕ) (e : Fin n → Pool p d) : (ZMod p)[X] :=
  ∏ i : Fin n, ((e i : (ZMod p)[X])) ^ (w i)

/-- Mapping over `Fin n` through an equiv to a subtype equals mapping over the finset. -/
lemma map_equiv_subtype {α β : Type*} [DecidableEq α] (S : Finset α) {n : ℕ} (b : Fin n ≃ ↥S)
    (f : α → β) :
    Finset.univ.val.map (fun i => f (b i : α)) = S.val.map f := by
  have h1 : Finset.univ.val.map (fun i => ((b i : ↥S))) = (Finset.univ : Finset ↥S).val := by
    have := congrArg Finset.val (Finset.map_univ_equiv b)
    rwa [Finset.map_val, Equiv.coe_toEmbedding] at this
  calc Finset.univ.val.map (fun i => f (b i : α))
      = (Finset.univ.val.map (fun i => (b i : ↥S))).map (fun s : ↥S => f (s : α)) := by
        rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset ↥S).val.map (fun s : ↥S => f (s : α)) := by rw [h1]
    _ = S.val.attach.map (fun s => f s.val) := by congr 1
    _ = S.val.map f := Multiset.attach_map_val' S.val f

/-- `map` over `univ.val` is invariant under permuting the index. -/
lemma map_univ_perm {n : ℕ} {α : Type*} (w : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map (fun i => w (σ i)) = Finset.univ.val.map w := by
  rw [show (fun i => w (σ i)) = w ∘ σ from rfl, ← Multiset.map_map]
  congr 1
  have h := Finset.map_univ_equiv σ
  have := congrArg Finset.val h
  rwa [Finset.map_val, Equiv.coe_toEmbedding] at this

/-- Two words with equal image-multiset differ by a permutation. -/
lemma exists_word_perm {n : ℕ} {α : Type*} [LinearOrder α] (w w' : Fin n → α)
    (h : Finset.univ.val.map w = Finset.univ.val.map w') :
    ∃ τ : Equiv.Perm (Fin n), (fun i => w' (τ i)) = w := by
  have hsort : w' ∘ Tuple.sort w' = w ∘ Tuple.sort w := by
    apply List.ofFn_injective
    have hperm : (List.ofFn (w' ∘ Tuple.sort w')).Perm (List.ofFn (w ∘ Tuple.sort w)) := by
      apply Multiset.coe_eq_coe.mp
      rw [← Fin.univ_val_map, ← Fin.univ_val_map]
      show Finset.univ.val.map (fun i => w' ((Tuple.sort w') i))
        = Finset.univ.val.map (fun i => w ((Tuple.sort w) i))
      rw [map_univ_perm w' (Tuple.sort w'), map_univ_perm w (Tuple.sort w), h]
    have hs1 : (List.ofFn (w' ∘ Tuple.sort w')).SortedLE := by
      rw [List.sortedLE_ofFn_iff]; exact Tuple.monotone_sort w'
    have hs2 : (List.ofFn (w ∘ Tuple.sort w)).SortedLE := by
      rw [List.sortedLE_ofFn_iff]; exact Tuple.monotone_sort w
    exact hperm.eq_of_sortedLE hs1 hs2
  refine ⟨(Tuple.sort w).symm.trans (Tuple.sort w'), ?_⟩
  funext i
  rw [Equiv.trans_apply]
  have := congrFun hsort ((Tuple.sort w).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  exact this

section BuildFacts
variable {d n : ℕ} (w : Fin n → ℕ) (e : Fin n → Pool p d)

lemma pool_irred (i : Fin n) : Irreducible ((e i : (ZMod p)[X])) :=
  (Order0.mem_poolFinset.mp (e i).2).1.1

lemma pool_monic (i : Fin n) : ((e i : (ZMod p)[X])).Monic :=
  (Order0.mem_poolFinset.mp (e i).2).1.2.1

lemma pool_deg (i : Fin n) : ((e i : (ZMod p)[X])).natDegree = d :=
  (Order0.mem_poolFinset.mp (e i).2).1.2.2

lemma pool_neX (i : Fin n) : ((e i : (ZMod p)[X])) ≠ X :=
  (Order0.mem_poolFinset.mp (e i).2).2

lemma pool_normalize (i : Fin n) : normalize ((e i : (ZMod p)[X])) = (e i : (ZMod p)[X]) :=
  (pool_monic p e i).normalize_eq_self

lemma pool_ne_zero (i : Fin n) : ((e i : (ZMod p)[X])) ^ (w i) ≠ 0 :=
  pow_ne_zero _ (pool_monic p e i).ne_zero

-- normalizedFactors of the build: sum over i of (w i) • {e i}
lemma nf_buildPoly :
    normalizedFactors (buildPoly p w e)
      = ∑ i : Fin n, (w i) • ({(e i : (ZMod p)[X])} : Multiset _) := by
  unfold buildPoly
  rw [Finset.prod_eq_multiset_prod, normalizedFactors_multiset_prod, Multiset.map_map]
  · rw [Finset.sum_eq_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    rw [Function.comp_apply, normalizedFactors_of_irreducible_pow (pool_irred p e i),
      pool_normalize p e i, ← Multiset.nsmul_singleton]
  · -- 0 ∉ the mapped multiset
    intro h0
    rw [Multiset.mem_map] at h0
    obtain ⟨i, _, hi⟩ := h0
    exact pool_ne_zero p w e i hi

lemma buildPoly_monic : (buildPoly p w e).Monic := by
  unfold buildPoly
  exact monic_prod_of_monic _ _ (fun i _ => (pool_monic p e i).pow _)

lemma buildPoly_notX : ¬ X ∣ (buildPoly p w e) := by
  intro hdvd
  unfold buildPoly at hdvd
  obtain ⟨i, _, hi⟩ := (prime_X.dvd_finsetProd_iff _).mp hdvd
  have hirr := pool_irred p e i
  have hdvd' : X ∣ (e i : (ZMod p)[X]) := prime_X.dvd_of_dvd_pow hi
  exact pool_neX p e i
    (eq_of_monic_of_associated monic_X (pool_monic p e i)
      (irreducible_X.associated_of_dvd hirr hdvd')).symm

lemma mem_nf_buildPoly (hpos : ∀ i, 1 ≤ w i) {ψ : (ZMod p)[X]} :
    ψ ∈ normalizedFactors (buildPoly p w e) ↔ ∃ i, (e i : (ZMod p)[X]) = ψ := by
  rw [nf_buildPoly]
  rw [Multiset.mem_sum]
  constructor
  · rintro ⟨i, _, hi⟩
    rw [Multiset.mem_nsmul_of_ne_zero ((by have := hpos i; omega : w i ≠ 0)), Multiset.mem_singleton] at hi
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ i, by
      rw [Multiset.mem_nsmul_of_ne_zero ((by have := hpos i; omega : w i ≠ 0))]; exact Multiset.mem_singleton_self _⟩

lemma polyShape_buildPoly (hinj : Function.Injective e) (hpos : ∀ i, 1 ≤ w i) :
    polyShape p (buildPoly p w e) = Finset.univ.val.map (fun i => (d, w i)) := by
  classical
  -- work under the same DecidableEq instance as `polyShape`
  letI : DecidableEq ((ZMod p)[X]) := Classical.decEq _
  have hcount : ∀ i, (normalizedFactors (buildPoly p w e)).count ((e i : (ZMod p)[X])) = w i := by
    intro i
    rw [nf_buildPoly, Multiset.count_sum', Finset.sum_eq_single i]
    · rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
    · intro j _ hj
      rw [Multiset.count_nsmul, Multiset.count_singleton,
        if_neg (fun h => hj (hinj (Subtype.ext h.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hval : (normalizedFactors (buildPoly p w e)).dedup
      = Finset.univ.val.map (fun i => (e i : (ZMod p)[X])) := by
    have hnodup : (Finset.univ.val.map (fun i => (e i : (ZMod p)[X]))).Nodup :=
      Multiset.Nodup.map (fun a b h => hinj (Subtype.ext h)) Finset.univ.nodup
    refine (Multiset.Nodup.ext (normalizedFactors _).nodup_dedup hnodup).mpr ?_
    intro ψ
    rw [Multiset.mem_dedup, mem_nf_buildPoly p w e hpos, Multiset.mem_map]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, Finset.mem_univ i, rfl⟩
    · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  show (normalizedFactors (buildPoly p w e)).toFinset.val.map
      (fun ψ => (ψ.natDegree, (normalizedFactors (buildPoly p w e)).count ψ))
      = Finset.univ.val.map (fun i => (d, w i))
  rw [Multiset.toFinset_val, hval, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  rw [Function.comp_apply, pool_deg p e i, hcount i]

/-- If `σ` fixes the word, `buildPoly` is invariant under reindexing by `σ`. -/
lemma buildPoly_perm_word_eq (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, w (σ i) = w i) :
    buildPoly p w (fun i => e (σ i)) = buildPoly p w e := by
  unfold buildPoly
  rw [← Equiv.prod_comp σ (fun j => (e j : (ZMod p)[X]) ^ (w j))]
  apply Finset.prod_congr rfl
  intro i _
  rw [hσ i]

/-- The range of the (coerced) assignment equals the support of the normalized factors. -/
lemma range_eq_of_buildPoly_eq (hpos : ∀ i, 1 ≤ w i) {e' : Fin n → Pool p d}
    (heq : buildPoly p w e = buildPoly p w e') :
    Set.range (fun i => (e i : (ZMod p)[X])) = Set.range (fun i => (e' i : (ZMod p)[X])) := by
  ext ψ
  simp only [Set.mem_range]
  have h1 : (∃ i, (e i : (ZMod p)[X]) = ψ) ↔ ψ ∈ normalizedFactors (buildPoly p w e) :=
    (mem_nf_buildPoly p w e hpos).symm
  have h2 : (∃ i, (e' i : (ZMod p)[X]) = ψ) ↔ ψ ∈ normalizedFactors (buildPoly p w e') :=
    (mem_nf_buildPoly p w e' hpos).symm
  rw [h1, h2, heq]

/-- The key rigidity: two injective assignments giving the same `buildPoly` differ by a
permutation that fixes the exponent word. -/
lemma exists_perm_of_buildPoly_eq (hinj : Function.Injective e) (hpos : ∀ i, 1 ≤ w i)
    {e' : Fin n → Pool p d} (hinj' : Function.Injective e')
    (heq : buildPoly p w e = buildPoly p w e') :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, w (σ i) = w i) ∧ (fun i => e (σ i)) = e' := by
  classical
  letI : DecidableEq ((ZMod p)[X]) := Classical.decEq _
  -- ranges of the coerced assignments coincide
  have hrangeC := range_eq_of_buildPoly_eq p w e hpos heq
  -- lift to ranges in `Pool` (Subtype.val is injective)
  have hrange : Set.range e' = Set.range e := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have : (e' i : (ZMod p)[X]) ∈ Set.range (fun i => (e i : (ZMod p)[X])) := by
        rw [hrangeC]; exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, Subtype.ext hj⟩
    · rintro ⟨i, rfl⟩
      have : (e i : (ZMod p)[X]) ∈ Set.range (fun i => (e' i : (ZMod p)[X])) := by
        rw [← hrangeC]; exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, Subtype.ext hj⟩
  -- build the permutation with e (σ i) = e' i
  let φ := Equiv.ofInjective e' hinj'
  let φ₀ := Equiv.ofInjective e hinj
  refine ⟨φ.trans ((Equiv.setCongr hrange).trans φ₀.symm), ?_, ?_⟩
  · -- word is fixed: count matching
    intro i
    have hcount : ∀ j, (normalizedFactors (buildPoly p w e)).count ((e j : (ZMod p)[X])) = w j := by
      intro j
      rw [nf_buildPoly, Multiset.count_sum', Finset.sum_eq_single j]
      · rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
      · intro j' _ hj'
        rw [Multiset.count_nsmul, Multiset.count_singleton,
          if_neg (fun h => hj' (hinj (Subtype.ext h.symm))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hcount' : ∀ j, (normalizedFactors (buildPoly p w e')).count ((e' j : (ZMod p)[X])) = w j := by
      intro j
      rw [nf_buildPoly, Multiset.count_sum', Finset.sum_eq_single j]
      · rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
      · intro j' _ hj'
        rw [Multiset.count_nsmul, Multiset.count_singleton,
          if_neg (fun h => hj' (hinj' (Subtype.ext h.symm))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    set σ := φ.trans ((Equiv.setCongr hrange).trans φ₀.symm)
    have hσe : (e (σ i) : (ZMod p)[X]) = (e' i : (ZMod p)[X]) := by
      show (e (φ₀.symm ((Equiv.setCongr hrange) (φ i))) : (ZMod p)[X]) = _
      have h1 : (φ₀ (φ₀.symm ((Equiv.setCongr hrange) (φ i))) : Pool p d) = e' i := by
        rw [Equiv.apply_symm_apply]
        show (((Equiv.setCongr hrange) (φ i)) : Pool p d) = e' i
        rfl
      rw [Equiv.ofInjective_apply] at h1
      exact congrArg (fun (z : Pool p d) => (z : (ZMod p)[X])) h1
    have := hcount (σ i)
    rw [hσe, heq, hcount' i] at this
    exact this.symm
  · -- e ∘ σ = e'
    funext i
    set σ := φ.trans ((Equiv.setCongr hrange).trans φ₀.symm)
    show e (φ₀.symm ((Equiv.setCongr hrange) (φ i))) = e' i
    have h1 : (φ₀ (φ₀.symm ((Equiv.setCongr hrange) (φ i))) : Pool p d) = e' i := by
      rw [Equiv.apply_symm_apply]
      show (((Equiv.setCongr hrange) (φ i)) : Pool p d) = e' i
      rfl
    rw [Equiv.ofInjective_apply] at h1
    exact h1

/-- **Surjectivity**: any monic prime-to-`X` `M` whose shape is `univ.val.map (d, w·)` (with all
exponents positive) is `buildPoly p w e₀` for some injective assignment `e₀`. -/
lemma exists_buildPoly (_hpos : ∀ i, 1 ≤ w i) {M : (ZMod p)[X]}
    (hmon : M.Monic) (hX : ¬ X ∣ M)
    (hshape : polyShape p M = Finset.univ.val.map (fun i => (d, w i))) :
    ∃ e₀ : Fin n → Pool p d, Function.Injective e₀ ∧ buildPoly p w e₀ = M := by
  classical
  letI : DecidableEq ((ZMod p)[X]) := Classical.decEq _
  -- the distinct factors of M, as a finset of the pool
  have hfac_pool : ∀ ψ ∈ (normalizedFactors M).toFinset, ψ ∈ Order0.poolFinset (ZMod p) d := by
    intro ψ hψ
    rw [Multiset.mem_toFinset] at hψ
    rw [Order0.mem_poolFinset]
    refine ⟨⟨irreducible_of_normalized_factor ψ hψ, Order0.monic_of_mem_normalizedFactors hψ, ?_⟩,
      Order0.ne_X_of_not_X_dvd hX hψ⟩
    -- degree d: (natDegree ψ, count) ∈ polyShape M = univ.val.map (d, w·), so natDegree = d
    have : (ψ.natDegree, (normalizedFactors M).count ψ) ∈ polyShape p M := by
      show (ψ.natDegree, (normalizedFactors M).count ψ)
        ∈ (normalizedFactors M).toFinset.val.map
          (fun φ => (φ.natDegree, (normalizedFactors M).count φ))
      exact Multiset.mem_map_of_mem _ (Multiset.mem_toFinset.mpr hψ)
    rw [hshape, Fin.univ_val_map, Multiset.mem_coe, List.mem_ofFn] at this
    obtain ⟨i, hi⟩ := this
    exact ((Prod.ext_iff.mp hi).1).symm
  -- card of the factor set = n
  have hcard : (normalizedFactors M).toFinset.card = n := by
    have h1 := congrArg Multiset.card hshape
    unfold polyShape at h1
    rw [Multiset.card_map, Multiset.card_map] at h1
    -- h1 : (nf.toFinset.val).card = univ.val.card
    have h2 : (normalizedFactors M).toFinset.card = (Finset.univ : Finset (Fin n)).val.card := by
      rw [Finset.card]; exact h1
    rw [h2]
    show (Finset.univ : Finset (Fin n)).card = n
    rw [Finset.card_univ, Fintype.card_fin]
  -- a bijection Fin n ≃ factor set
  let S := (normalizedFactors M).toFinset
  let b : Fin n ≃ ↥S := (Finset.equivFinOfCardEq hcard).symm
  -- raw assignment and its word
  let e_raw : Fin n → Pool p d := fun i => ⟨(b i : (ZMod p)[X]), hfac_pool _ (b i).2⟩
  let w' : Fin n → ℕ := fun i => (normalizedFactors M).count ((b i : (ZMod p)[X]))
  have he_raw_inj : Function.Injective e_raw := by
    intro i j hij
    have hval : (e_raw i : (ZMod p)[X]) = (e_raw j : (ZMod p)[X]) :=
      congrArg (fun z : Pool p d => (z : (ZMod p)[X])) hij
    exact b.injective (Subtype.ext hval)
  -- degree of every factor is d
  have hdeg_fac : ∀ ψ ∈ S, ψ.natDegree = d := by
    intro ψ hψ
    exact (Order0.mem_poolFinset.mp (hfac_pool ψ hψ)).1.2.2
  -- shapes: univ.val.map (d, w'·) = polyShape M via the bijection b
  have hshape' : Finset.univ.val.map (fun i => (d, w' i)) = polyShape p M := by
    unfold polyShape
    have hbridge := map_equiv_subtype S b
      (fun φ => (φ.natDegree, (normalizedFactors M).count φ))
    rw [← hbridge]
    apply Multiset.map_congr rfl
    intro i _
    show (d, (normalizedFactors M).count ((b i : (ZMod p)[X])))
      = ((b i : (ZMod p)[X]).natDegree, (normalizedFactors M).count ((b i : (ZMod p)[X])))
    rw [hdeg_fac _ (b i).2]
  -- match words by a permutation: univ.map w = univ.map w'
  have hww : Finset.univ.val.map w = Finset.univ.val.map w' := by
    have hdw : Finset.univ.val.map (fun i => (d, w i))
        = Finset.univ.val.map (fun i => (d, w' i)) := by
      rw [← hshape, ← hshape']
    -- strip the constant first coordinate: map snd
    have := congrArg (Multiset.map Prod.snd) hdw
    rwa [Multiset.map_map, Multiset.map_map] at this
  obtain ⟨τ, hτ⟩ := exists_word_perm w w' hww
  refine ⟨fun i => e_raw (τ i), he_raw_inj.comp τ.injective, ?_⟩
  -- buildPoly p w (e_raw ∘ τ) = M
  unfold buildPoly
  -- reindex the product to ∏_{ψ ∈ S} ψ ^ count ψ = nf.prod = M
  have hval : ∀ i, ((e_raw (τ i) : (ZMod p)[X])) ^ (w i)
      = ((b (τ i) : (ZMod p)[X])) ^ (w' (τ i)) := by
    intro i
    have : w i = w' (τ i) := (congrFun hτ i).symm
    rw [this]
  rw [Finset.prod_congr rfl (fun i _ => hval i)]
  -- ∏ i, (b (τ i))^(w' (τ i)) = ∏ i, (b i)^(w' i)  (reindex by τ)
  rw [Equiv.prod_comp τ (fun j => ((b j : (ZMod p)[X])) ^ (w' j))]
  -- now = ∏_{ψ ∈ S} ψ^(count) = nf.prod = M
  -- LHS: ∏ i, (b i)^(w' i) = ∏_{ψ ∈ S} ψ^count, via the bridge
  have hLHS : (∏ i, ((b i : (ZMod p)[X])) ^ (w' i))
      = (S.val.map (fun ψ => ψ ^ ((normalizedFactors M).count ψ))).prod := by
    rw [Finset.prod_eq_multiset_prod]
    congr 1
    exact map_equiv_subtype S b (fun ψ => ψ ^ ((normalizedFactors M).count ψ))
  rw [hLHS]
  -- RHS: (S.val.map (ψ ↦ ψ^count)).prod = nf.prod = M
  have hRHS : (S.val.map (fun ψ => ψ ^ ((normalizedFactors M).count ψ))).prod
      = (normalizedFactors M).prod := by
    conv_rhs => rw [Finset.prod_multiset_count]
    rw [Finset.prod_eq_multiset_prod]
  rw [hRHS, Order0.prod_normalizedFactors_of_monic hmon]

/-- The shape-set at the word `w`, as a subtype (all-degree-`d`, positive exponents). -/
def shapeSetW (d : ℕ) {n : ℕ} (w : Fin n → ℕ) : Set (ZMod p)[X] :=
  {M : (ZMod p)[X] | M.Monic ∧ ¬ X ∣ M ∧ polyShape p M = Finset.univ.val.map (fun i => (d, w i))}

/-- The fiber of `buildPoly` over `M`, as embeddings. -/
def Fib (d : ℕ) {n : ℕ} (w : Fin n → ℕ) (M : (ZMod p)[X]) : Type _ :=
  {e : Fin n ↪ Pool p d // buildPoly p w (fun i => e i) = M}

/-- **Fiber = word-stabilizer.**  For `M` in the shape-set, the fiber of `buildPoly` over `M`
is in bijection with the permutations fixing the word `w`. -/
lemma card_Fib (hpos : ∀ i, 1 ≤ w i) {M : (ZMod p)[X]} (hM : M ∈ shapeSetW p d w) :
    Nat.card (Fib p d w M) = Nat.card {σ : Equiv.Perm (Fin n) // (fun i => w (σ i)) = w} := by
  classical
  obtain ⟨hmon, hX, hshape⟩ := hM
  -- base point
  obtain ⟨e₀, he₀inj, he₀⟩ := exists_buildPoly p w hpos hmon hX hshape
  -- the chosen permutation attached to a fiber element
  have hfibM : ∀ e : Fib p d w M, buildPoly p w e₀ = buildPoly p w e.1 := by
    intro e; rw [he₀]; exact e.2.symm
  -- the WStab type
  let WStab := {σ : Equiv.Perm (Fin n) // (fun i => w (σ i)) = w}
  -- forward map
  let fwd : Fib p d w M → WStab := fun e =>
    ⟨Classical.choose (exists_perm_of_buildPoly_eq p w e₀ he₀inj hpos e.1.injective (hfibM e)),
      funext (Classical.choose_spec (exists_perm_of_buildPoly_eq p w e₀ he₀inj hpos e.1.injective
        (hfibM e))).1⟩
  have hfwd_spec : ∀ e : Fib p d w M, (fun i => e₀ ((fwd e).1 i)) = (fun i => (e.1 i : Pool p d)) :=
    fun e => (Classical.choose_spec (exists_perm_of_buildPoly_eq p w e₀ he₀inj hpos e.1.injective
      (hfibM e))).2
  -- inverse map
  have hinv_build : ∀ σ : WStab, buildPoly p w (fun i => e₀ (σ.1 i)) = M := by
    intro σ
    rw [buildPoly_perm_word_eq p w e₀ σ.1 (fun i => congrFun σ.2 i), he₀]
  let inv : WStab → Fib p d w M := fun σ =>
    ⟨⟨fun i => e₀ (σ.1 i), he₀inj.comp σ.1.injective⟩, hinv_build σ⟩
  refine Nat.card_congr ⟨fwd, inv, ?_, ?_⟩
  · -- left_inv: inv (fwd e) = e
    intro e
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    show e₀ ((fwd e).1 i) = e.1 i
    exact congrFun (hfwd_spec e) i
  · -- right_inv: fwd (inv σ) = σ
    intro σ
    apply Subtype.ext
    -- both give the reindexed embedding; e₀ injective ⟹ perms agree
    apply Equiv.ext
    intro i
    apply he₀inj
    have := congrFun (hfwd_spec (inv σ)) i
    -- (inv σ).1 i = e₀ (σ.1 i), so this : e₀ ((fwd (inv σ)).1 i) = e₀ (σ.1 i)
    exact this

/-- The word symmetry factor `∏_v (#{i // w i = v})!`. -/
noncomputable def symFW {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∏ v ∈ Finset.image w Finset.univ, (Nat.card {i : Fin n // w i = v}).factorial

/-- Word-stabilizer cardinality is `symFW`. -/
lemma card_wstab :
    Nat.card {σ : Equiv.Perm (Fin n) // (fun i => w (σ i)) = w} = symFW w := by
  classical
  have h := DomMulAct.stabilizer_card' (α := Fin n) (ι := ℕ) w
  -- h : Fintype.card {g // w ∘ g = w} = ∏ i ∈ image w univ, (card {a // w a = i})!
  rw [Nat.card_congr (Equiv.refl {σ : Equiv.Perm (Fin n) // (fun i => w (σ i)) = w}),
    Nat.card_eq_fintype_card]
  rw [show (@Fintype.card {σ : Equiv.Perm (Fin n) // (fun i => w (σ i)) = w} _)
      = Fintype.card {g : Equiv.Perm (Fin n) // w ∘ (g : Fin n → Fin n) = w} from
    Fintype.card_congr (Equiv.refl _)]
  rw [h]
  unfold symFW
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [Nat.card_eq_fintype_card]

/-- `symFW` in terms of the multiplicity multiset. -/
lemma symFW_eq (μs : Multiset ℕ) (hμ : Finset.univ.val.map w = μs) :
    symFW w = ∏ v ∈ μs.toFinset, (μs.count v).factorial := by
  classical
  unfold symFW
  have himg : Finset.image w Finset.univ = μs.toFinset := by
    ext v
    rw [Finset.mem_image, Multiset.mem_toFinset, ← hμ, Multiset.mem_map]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, Finset.mem_univ i, rfl⟩
    · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  rw [himg]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hμ, Multiset.count_map,
    Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun i _ => eq_comm)

/-- Cardinality of the pool subtype is `avail`. -/
lemma card_Pool : Nat.card (Pool p d) = Order0.avail (ZMod p) d := by
  rw [Pool, Nat.card_eq_fintype_card, Fintype.card_coe, Order0.card_poolFinset]

instance instFinite_Fib (M : (ZMod p)[X]) : Finite (Fib p d w M) := by
  unfold Fib; infer_instance

/-- The shape-set is finite: it is contained in the image of the (finite) embedding type. -/
lemma finite_shapeSetW (hpos : ∀ i, 1 ≤ w i) : (shapeSetW p d w).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun e : Fin n ↪ Pool p d => buildPoly p w (fun i => e i)))
  intro M hM
  obtain ⟨hmon, hX, hshape⟩ := hM
  obtain ⟨e₀, he₀inj, he₀⟩ := exists_buildPoly p w hpos hmon hX hshape
  exact ⟨⟨e₀, he₀inj⟩, he₀⟩

@[reducible] noncomputable def fintype_shapeSetW (hpos : ∀ i, 1 ≤ w i) :
    Fintype (shapeSetW p d w) := (finite_shapeSetW p w hpos).fintype

/-- **The word-level master count.**  The falling factorial of the pool size splits as the
shape-set cardinality times the word symmetry factor. -/
lemma descFactorial_eq (hpos : ∀ i, 1 ≤ w i) :
    (Order0.avail (ZMod p) d).descFactorial n
      = Nat.card (shapeSetW p d w) * symFW w := by
  classical
  haveI : Fintype (shapeSetW p d w) := fintype_shapeSetW p w hpos
  -- LHS = card of embeddings
  have hemb : Nat.card (Fin n ↪ Pool p d) = (Order0.avail (ZMod p) d).descFactorial n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, card_Pool]
  -- bijection (Fin n ↪ Pool) ≃ Σ M : shapeSetW, Fib M
  have hbij : Nat.card (Fin n ↪ Pool p d)
      = Nat.card (Σ M : ↥(shapeSetW p d w), Fib p d w (M : (ZMod p)[X])) := by
    refine Nat.card_congr ?_
    refine {
      toFun := fun e => ⟨⟨buildPoly p w (fun i => e i), ?_⟩, ⟨e, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := fun e => rfl
      right_inv := ?_ }
    · -- buildPoly ∈ shapeSetW
      refine ⟨buildPoly_monic p w (fun i => e i), buildPoly_notX p w (fun i => e i), ?_⟩
      exact polyShape_buildPoly p w (fun i => e i) e.injective hpos
    · -- right_inv
      rintro ⟨⟨M, hM⟩, ⟨e, he⟩⟩
      -- he : buildPoly p w e = M
      obtain rfl : buildPoly p w (fun i => e i) = M := he
      rfl
  -- Σ card = ∑ card(Fib) = ∑ symFW = card(shapeSetW) * symFW
  rw [← hemb, hbij, Nat.card_sigma]
  have hsum : ∀ M : ↥(shapeSetW p d w), Nat.card (Fib p d w (M : (ZMod p)[X])) = symFW w := by
    intro M
    rw [card_Fib p w hpos M.2]
    exact card_wstab w
  rw [Finset.sum_congr rfl (fun M _ => hsum M), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul]

end BuildFacts

/-- The per-degree symmetry factor of a pure-degree slice `L`, as a multiset product. -/
noncomputable def symFactorMultiset (L : Multiset (ℕ × ℕ)) : ℕ :=
  ∏ v ∈ (L.map Prod.snd).toFinset, ((L.map Prod.snd).count v).factorial

lemma symFactorMultiset_ne_zero (L : Multiset (ℕ × ℕ)) : symFactorMultiset L ≠ 0 := by
  unfold symFactorMultiset
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => Nat.factorial_ne_zero _)

/-- **The single-degree count** (blueprint step 2).  For a pure degree-`d` slice `L`
(all first coordinates `= d`, all multiplicities `≥ 1`), the count of monic prime-to-`X`
polynomials of shape `L` is `descFactorial (avail_d, |L|) / symFactorMultiset L`. -/
theorem single_degree_count (d : ℕ) (_hd : 1 ≤ d) (L : Multiset (ℕ × ℕ))
    (hLd : ∀ q ∈ L, q.1 = d) (hmpos : ∀ q ∈ L, 1 ≤ q.2) :
    ((Nat.card (shapeSet p L) : ℕ) : ℚ)
      = ((Order0.avail (ZMod p) d).descFactorial (Multiset.card L) : ℚ)
          / (symFactorMultiset L : ℚ) := by
  classical
  -- enumerate L
  obtain ⟨g, hg⟩ : ∃ g : Fin L.card → ℕ × ℕ, Finset.univ.val.map g = L := by
    refine ⟨fun i => L.toList.get (Fin.cast (by rw [Multiset.length_toList]) i), ?_⟩
    rw [Fin.univ_val_map]
    have hofFn : List.ofFn
        (fun i : Fin L.card => L.toList.get (Fin.cast (by rw [Multiset.length_toList]) i))
        = L.toList := by
      apply List.ext_getElem
      · simp [Multiset.length_toList]
      · intro k h1 h2; simp [List.getElem_ofFn]
    rw [hofFn, Multiset.coe_toList]
  -- each g i ∈ L
  have hgmem : ∀ i, g i ∈ L := by
    intro i; rw [← hg]; exact Multiset.mem_map_of_mem g (Finset.mem_univ i)
  set w : Fin L.card → ℕ := fun i => (g i).2 with hw
  have hpos : ∀ i, 1 ≤ w i := fun i => hmpos _ (hgmem i)
  have hgd : ∀ i, (g i).1 = d := fun i => hLd _ (hgmem i)
  -- L = univ.map (d, w·)
  have hLeq : Finset.univ.val.map (fun i => (d, w i)) = L := by
    calc Finset.univ.val.map (fun i => (d, w i))
        = Finset.univ.val.map g := by
          apply Multiset.map_congr rfl
          intro i _
          show (d, (g i).2) = g i
          rw [← hgd i]
      _ = L := hg
  -- shapeSet p L = shapeSetW p d w
  have hset : shapeSet p L = shapeSetW p d w := by
    unfold shapeSet shapeSetW
    rw [hLeq]
  -- word multiset = L.map snd
  have hwmap : Finset.univ.val.map w = L.map Prod.snd := by
    rw [hw]
    show Finset.univ.val.map (fun i => (g i).2) = L.map Prod.snd
    calc Finset.univ.val.map (fun i => (g i).2)
        = (Finset.univ.val.map g).map Prod.snd := by rw [Multiset.map_map]; rfl
      _ = L.map Prod.snd := by rw [hg]
  -- symFW = symFactorMultiset
  have hsym : symFW w = symFactorMultiset L := by
    rw [symFW_eq w (L.map Prod.snd) hwmap, symFactorMultiset]
  -- the master count
  have hmaster := descFactorial_eq (d := d) p w hpos
  have hcardset : Nat.card (shapeSet p L) = Nat.card (shapeSetW p d w) :=
    Nat.card_congr (Equiv.setCongr hset)
  rw [hcardset]
  -- hmaster : descFactorial(avail, L.card) = card(shapeSetW) * symFW w
  rw [hsym] at hmaster
  -- move to ℚ
  have hsymℚ : (symFactorMultiset L : ℚ) ≠ 0 := by
    exact_mod_cast symFactorMultiset_ne_zero L
  rw [eq_div_iff hsymℚ]
  have : ((Order0.avail (ZMod p) d).descFactorial (Multiset.card L) : ℚ)
      = ((Nat.card (shapeSetW p d w) : ℕ) : ℚ) * (symFactorMultiset L : ℚ) := by
    rw [← Nat.cast_mul]
    exact_mod_cast hmaster
  rw [this]


/-! ## RHS bridge: the choice polynomial per-degree factor -/

lemma descFactorial_add (N a b : ℕ) :
    N.descFactorial (a + b) = N.descFactorial a * (N - a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
      have h1 : a + (b + 1) = (a + b) + 1 := by ring
      rw [h1, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]; ring

lemma cast_descFactorial_eq_prod (n k : ℕ) :
    (n.descFactorial k : ℚ) = ∏ i ∈ Finset.range k, ((n : ℚ) - (i : ℚ)) := by
  rw [← descPochhammer_eval_eq_descFactorial ℚ n k, descPochhammer_eval_eq_prod_range]

/-- `ff(availPoly d, k)` evaluated at `p` is the descending factorial of the pool size. -/
lemma ffPoly_availPoly_eval (d k : ℕ) (hd : 1 ≤ d) :
    (ffPoly (poolPoly true d) k).eval (p : ℚ)
      = ((Order0.avail (ZMod p) d).descFactorial k : ℚ) := by
  rw [show poolPoly true d = Order0.availPoly d from rfl]
  have hpcard : (p : ℚ) = (Nat.card (ZMod p) : ℚ) := by rw [Nat.card_zmod]
  unfold ffPoly
  rw [Polynomial.eval_prod, hpcard,
    Finset.prod_congr rfl (fun i (_ : i ∈ Finset.range k) => by
      rw [Polynomial.eval_sub, Polynomial.eval_C, Order0.availPoly_eval (ZMod p) d hd]),
    cast_descFactorial_eq_prod]

/-- The RHS choice polynomial, evaluated at `p`, is the product over factor-degrees of the
per-degree factor `descFactorial(avail_d, k_d) / symFactor_d`. -/
lemma choicePoly_eval_prod (L : List (ℕ × ℕ)) (hLpos : ∀ q ∈ L, 1 ≤ q.1) :
    (choicePoly true L).eval (p : ℚ)
      = ∏ d ∈ (L.map Prod.fst).toFinset,
          ((Order0.avail (ZMod p) d).descFactorial ((L.map Prod.fst).count d) : ℚ)
            / (symFactor L d : ℚ) := by
  unfold choicePoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl (fun d hd => ?_)
  have hd1 : 1 ≤ d := by
    rw [List.mem_toFinset, List.mem_map] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    exact hLpos q hq
  rw [Polynomial.eval_mul, Polynomial.eval_C, ffPoly_availPoly_eval p d _ hd1,
    one_div, ← div_eq_inv_mul]


/-! ## Assembly: reduction of the general tie to the single-degree count

The general tie follows from the crux (multiplicativity over degrees) and the RHS bridge, GIVEN the
single-degree count `#2`.  We package the remaining obligation (`#2`) as an explicit hypothesis
`hSingle`, so this module stays `sorry`-free while pinning the exact missing lemma: for each factor
degree `d ≥ 1` appearing in `l`, the count of monic prime-to-`X` polynomials whose factors are all
of degree `d` with multiplicity profile `l.filter (·.1 = d)` equals
`descFactorial (avail_d, k_d) / symFactor_d`. -/

/-- **The general residual-shape count tie, reduced to the single-degree count.**  Given the
per-degree count `hSingle`, the actual count of monic polynomials over `ZMod p` prime to `X` with
factorization type `l` equals the engine's choice-count polynomial evaluated at `p`. -/
theorem shapeCount_tie_general_of_singleDegree (l : List (ℕ × ℕ)) (hlpos : ∀ q ∈ l, 1 ≤ q.1)
    (hSingle : ∀ d ∈ (l.map Prod.fst).toFinset,
      ((Nat.card (shapeSet p ((l : Multiset (ℕ × ℕ)).filter (fun q => q.1 = d))) : ℕ) : ℚ)
        = ((Order0.avail (ZMod p) d).descFactorial ((l.map Prod.fst).count d) : ℚ)
            / (symFactor l d : ℚ)) :
    ((CellCard.shapeCount p l : ℕ) : ℚ) = (OMCountV2.choicePoly true l).eval (p : ℚ) := by
  rw [choicePoly_eval_prod p l hlpos]
  rw [shapeCount_eq_card, card_shapeSet_prod p (l : Multiset (ℕ × ℕ))]
  -- LHS degree finset is over the multiset's fst-image; align with the list's fst-image
  have hfst : (((l : Multiset (ℕ × ℕ))).map Prod.fst).toFinset = (l.map Prod.fst).toFinset := by
    rw [Multiset.map_coe]; rfl
  rw [hfst, Nat.cast_prod]
  exact Finset.prod_congr rfl (fun d hd => hSingle d hd)

/-! ## The unconditional general tie -/

/-- `|filter (·.1=d)|` equals the degree-`d` multiplicity `(l.map fst).count d`. -/
lemma card_filter_eq_count (l : List (ℕ × ℕ)) (d : ℕ) :
    ((l : Multiset (ℕ × ℕ)).filter (fun q => q.1 = d)).card = (l.map Prod.fst).count d := by
  classical
  rw [← Multiset.coe_count, ← Multiset.map_coe, Multiset.count_map]
  exact congrArg Multiset.card (Multiset.filter_congr (fun q _ => eq_comm))

/-- The multiset symmetry factor of the degree-`d` slice equals the harness's `symFactor`. -/
lemma symFactorMultiset_filter_eq (l : List (ℕ × ℕ)) (d : ℕ) :
    symFactorMultiset ((l : Multiset (ℕ × ℕ)).filter (fun q => q.1 = d))
      = OMCountV2.symFactor l d := by
  classical
  have hbridge : ((l : Multiset (ℕ × ℕ)).filter (fun q => q.1 = d)).map Prod.snd
      = ((OMCountV2.faceMus l d : List ℕ) : Multiset ℕ) := by
    unfold OMCountV2.faceMus
    rw [← Multiset.map_coe]
    congr 1
  unfold symFactorMultiset OMCountV2.symFactor
  rw [hbridge]
  simp only [Multiset.coe_count, List.toFinset_coe]

/-- **The general residual-shape count tie (UNCONDITIONAL).**  For any factorization-shape list
`l` with positive degrees and positive multiplicities, the actual count of monic prime-to-`X`
polynomials of shape `l` equals the engine's choice-count polynomial evaluated at `p`. -/
theorem shapeCount_tie_general (l : List (ℕ × ℕ)) (hlpos : ∀ q ∈ l, 1 ≤ q.1)
    (hmpos : ∀ q ∈ l, 1 ≤ q.2) :
    ((CellCard.shapeCount p l : ℕ) : ℚ) = (OMCountV2.choicePoly true l).eval (p : ℚ) := by
  classical
  refine shapeCount_tie_general_of_singleDegree p l hlpos (fun d hd => ?_)
  -- discharge hSingle via single_degree_count
  rw [List.mem_toFinset, List.mem_map] at hd
  obtain ⟨q₀, hq₀, rfl⟩ := hd
  set L := (l : Multiset (ℕ × ℕ)).filter (fun q => q.1 = q₀.1) with hL
  have hLd : ∀ q ∈ L, q.1 = q₀.1 := by
    intro q hq; rw [hL, Multiset.mem_filter] at hq; exact hq.2
  have hLmpos : ∀ q ∈ L, 1 ≤ q.2 := by
    intro q hq
    rw [hL, Multiset.mem_filter, Multiset.mem_coe] at hq
    exact hmpos q hq.1
  have hd1 : 1 ≤ q₀.1 := hlpos q₀ hq₀
  have hcount := single_degree_count p q₀.1 hd1 L hLd hLmpos
  rw [hcount]
  -- align L.card and symFactorMultiset with the hSingle statement
  rw [card_filter_eq_count l q₀.1, symFactorMultiset_filter_eq l q₀.1]

/-! ## The unconditional per-cell census (keystone payoff) -/

/-- For a valid shape assignment, every shape `l ∈ sh` has positive degrees and multiplicities. -/
lemma pos_of_shapesFor {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    (hsh : ShapesFor P sh) {l : List (ℕ × ℕ)} (hl : l ∈ sh) :
    (∀ q ∈ l, 1 ≤ q.1) ∧ (∀ q ∈ l, 1 ≤ q.2) := by
  -- l corresponds (via Forall₂) to some side pr with l ∈ shapesOfDegree (sideDeg pr)
  unfold ShapesFor at hsh
  -- extract the matching side degree by induction on the Forall₂ relation
  have hmem : ∃ pr, l ∈ shapesOfDegree (sideDeg pr) := by
    generalize hLB : sidePairs P = LB at hsh
    clear hLB
    induction hsh with
    | nil => simp at hl
    | @cons a b la lb hab _ ih =>
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact ⟨b, hab⟩
        · exact ih hl'
  obtain ⟨pr, hpr⟩ := hmem
  obtain ⟨-, hpos, -⟩ := mem_shapesOfDegree_iff.mp hpr
  exact ⟨fun q hq => (hpos q hq).1, fun q hq => (hpos q hq).2⟩

/-- **The unconditional per-cell census** (blueprint step 4, keystone payoff).  For any menu path
`P` and valid shape assignment `sh`, the count of boxes in the cell equals the engine's `mCell`
value times the free-digit volume — the `hties` hypothesis of `cell_card_mCell` DISCHARGED. -/
theorem cell_card_mCell_uncond {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : MenuPath s N P) {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    (Nat.card {f : QuotientBox.monicBox p N s // InCell p f (mkCell s P sh)} : ℚ)
      = mCell (mkCell s P sh) p * (p : ℚ) ^ freeExp s N P := by
  refine CellCard.cell_card_mCell p hN hP hsh (fun l hl => ?_)
  obtain ⟨hlpos, hmpos⟩ := pos_of_shapesFor hsh hl
  exact shapeCount_tie_general p l hlpos hmpos

end LeanUrat.OM.ShapeCountTie
