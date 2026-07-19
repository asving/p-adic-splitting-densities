/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L3
import LeanUrat.L3Gauss
import LeanUrat.OM.Necklace
import LeanUrat.OM.Order0

/-!
# LeanUrat.OM.Order0Count — the level-1 count identities (HNODE0 blueprint §3, package β)

The combinatorial engine behind the root-node coefficient of `montes_order0` at level 1:

* **β2a (cross-tie)** — `necklaceQ_eq_card`: the abstract necklace count `Necklace.necklaceQ d Q`
  at `Q = #F` equals the number of monic irreducible degree-`d` polynomials over the finite field
  `F` (divide `L3Gauss.gauss_necklace_count` by `d`).
* **β2b (pool sizes)** — `card_monicIrreducibleDegree_one`: `#Irr₁ = Q` (the linears `X + C c`);
  `card_poolSet` / `card_poolFinset`: the punctured pool `Irr_d \ {X}` has size
  `avail F d = if d = 1 then Q - 1 else #Irr_d` (`X` itself IS monic irreducible of degree 1, and
  it is the one linear factor excluded on the generic stratum `a₀ ≠ 0`).
* **β3 (choose = ff/k!)** — `cast_choose_eq_prod_range_div`: in `ℚ`,
  `C(m, k) = (∏_{i<k} (m - i)) / k!`, valid for ALL `m, k` (for `k > m` both sides vanish: the
  product hits the factor `m - m = 0`). Via `Nat.cast_choose_eq_descPochhammer_div` +
  `descPochhammer_eval_eq_prod_range`.
* **β1+β4 (the count)** — `card_sepStratum`: over a finite field `F`, for a partition
  `P : n.Partition`, the number of monic squarefree degree-`n` polynomials `f` with `¬ X ∣ f` and
  factor-degree multiset `P.parts` is `∏_{d ∈ P.parts.toFinset} C(avail F d, k_d)` with
  `k_d = P.parts.count d`. Proof: the factor-slice map `f ↦ (d ↦ degree-d factors of f)` is a
  bijection onto `Π_d (k_d-subsets of the punctured pool)`, by unique factorization
  (`UniqueFactorizationMonoid.normalizedFactors`; over a field the normalized factors of a monic
  polynomial are monic and multiply back to it).

Everything is sorry-free and axiom-clean (`propext, Classical.choice, Quot.sound`).

The `NormalizationMonoid F` underlying `normalizedFactors` needs `[DecidableEq F]`
(`CommGroupWithZero.instNormalizedGCDMonoid`), so the β1/β4 declarations carry it, following the
`L3Squarefree` house pattern; the `Nat.card` values are independent of the instance.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.Order0

open Polynomial UniqueFactorizationMonoid

/-! ## β2a — the cross-tie: `necklaceQ d (#F) = #Irr_d`

`Necklace.necklaceQ d q = (∑_{e ∣ d} μ(e)·q^{d/e} : ℤ→ℚ) / d`, and
`L3Gauss.gauss_necklace_count` gives `d · #Irr_d = ∑_{e ∣ d} μ(e)·(#F)^{d/e}` in `ℚ`. -/

/-- **β2a (cross-tie).** For `d ≥ 1` the necklace count at alphabet size `Q = #F` is exactly the
number of monic irreducible degree-`d` polynomials over the finite field `F`. -/
theorem necklaceQ_eq_card (F : Type*) [Field F] [Finite F] (d : ℕ) (hd : 1 ≤ d) :
    Necklace.necklaceQ d (Nat.card F) = (Nat.card (L3.monicIrreducibleDegree F d) : ℚ) := by
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hd)
  rw [Necklace.necklaceQ, Necklace.necklaceSum]
  push_cast
  rw [← L3Gauss.gauss_necklace_count F d hd, mul_div_cancel_left₀ _ hd0]

/-! ## β2b — pool sizes -/

/-- The monic polynomials of a fixed degree over a finite field form a finite set
(their `Nat.card` is the positive number `Q^m` by `L3.card_monicDegree`). -/
lemma finite_monicDegree (F : Type*) [Field F] [Finite F] (m : ℕ) :
    (L3.monicDegree F m).Finite := by
  rw [← Set.finite_coe_iff]
  exact Nat.finite_of_card_ne_zero (by
    rw [L3.card_monicDegree]
    exact pow_ne_zero m Nat.card_pos.ne')

/-- The monic irreducibles of a fixed degree over a finite field form a finite set. -/
lemma finite_monicIrreducibleDegree (F : Type*) [Field F] [Finite F] (d : ℕ) :
    (L3.monicIrreducibleDegree F d).Finite :=
  (finite_monicDegree F d).subset fun _ hp => ⟨hp.2.1, hp.2.2⟩

/-- Over a field, EVERY monic polynomial of degree `1` is irreducible, so the degree-`1` pool is
the full monic slice. -/
lemma monicIrreducibleDegree_one_eq (F : Type*) [Field F] :
    L3.monicIrreducibleDegree F 1 = L3.monicDegree F 1 := by
  ext p
  simp only [L3.monicIrreducibleDegree, L3.monicDegree, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hm, hd⟩
    exact ⟨hm, hd⟩
  · rintro ⟨hm, hd⟩
    exact ⟨irreducible_of_degree_eq_one ((degree_eq_iff_natDegree_eq hm.ne_zero).mpr hd), hm, hd⟩

/-- **β2b, full linear pool.** `#Irr₁ = Q`: the monic irreducible linears are the `X + C c`. -/
theorem card_monicIrreducibleDegree_one (F : Type*) [Field F] [Finite F] :
    Nat.card (L3.monicIrreducibleDegree F 1) = Nat.card F := by
  rw [monicIrreducibleDegree_one_eq, L3.card_monicDegree, pow_one]

/-- `X` itself is monic irreducible of degree `1` (the excluded linear factor). -/
lemma X_mem_monicIrreducibleDegree_one (F : Type*) [Field F] :
    (X : F[X]) ∈ L3.monicIrreducibleDegree F 1 :=
  ⟨irreducible_X, monic_X, natDegree_X⟩

/-- **The punctured degree-`d` pool**: monic irreducibles of degree `d`, with `X` excluded (a
no-op for `d ≠ 1`). These are the admissible degree-`d` factors on the stratum `¬ X ∣ f`. -/
def poolSet (F : Type*) [Field F] (d : ℕ) : Set F[X] :=
  L3.monicIrreducibleDegree F d \ {X}

lemma finite_poolSet (F : Type*) [Field F] [Finite F] (d : ℕ) : (poolSet F d).Finite :=
  (finite_monicIrreducibleDegree F d).subset Set.sdiff_subset

/-- **The pool size** `avail F d`: `Q - 1` at `d = 1` (linears minus `X`), `#Irr_d` for `d ≠ 1`.
This is the ℕ-valued shadow of `Order0.availPoly` evaluated at `Q = #F`. -/
noncomputable def avail (F : Type*) [Field F] (d : ℕ) : ℕ :=
  if d = 1 then Nat.card F - 1 else Nat.card (L3.monicIrreducibleDegree F d)

@[simp] lemma avail_one (F : Type*) [Field F] : avail F 1 = Nat.card F - 1 := by
  simp [avail]

lemma avail_of_ne_one (F : Type*) [Field F] {d : ℕ} (hd : d ≠ 1) :
    avail F d = Nat.card (L3.monicIrreducibleDegree F d) := by
  simp [avail, hd]

/-- **β2b (punctured pool size).** `#(Irr_d \ {X}) = avail F d`; in particular at `d = 1` the
punctured pool has `Q - 1` elements. -/
theorem card_poolSet (F : Type*) [Field F] [Finite F] (d : ℕ) :
    Nat.card (poolSet F d) = avail F d := by
  rcases eq_or_ne d 1 with rfl | hd
  · rw [avail_one]
    show Nat.card ↥(L3.monicIrreducibleDegree F 1 \ {X}) = Nat.card F - 1
    rw [Nat.card_coe_set_eq,
      Set.ncard_sdiff_singleton_of_mem (X_mem_monicIrreducibleDegree_one F),
      ← Nat.card_coe_set_eq, card_monicIrreducibleDegree_one]
  · rw [avail_of_ne_one F hd]
    have hX : (X : F[X]) ∉ L3.monicIrreducibleDegree F d := by
      intro hmem
      obtain ⟨-, -, hdeg⟩ := hmem
      exact hd (by rw [← hdeg, natDegree_X])
    show Nat.card ↥(L3.monicIrreducibleDegree F d \ {X}) = _
    rw [Set.sdiff_singleton_eq_self hX]

/-- **β2b, `d = 1` corollary in the prompt's normal form**: the punctured linear pool has
`Q - 1` elements. -/
theorem card_poolSet_one (F : Type*) [Field F] [Finite F] :
    Nat.card (poolSet F 1) = Nat.card F - 1 := by
  rw [card_poolSet, avail_one]

/-! ## β3 — the choose = falling-factorial/k! cast identity -/

/-- **β3.** In `ℚ`, `C(m, k) = (∏_{i < k} (m - i)) / k!` for ALL naturals `m, k`. For `k ≤ m` the
casts align factor by factor; for `k > m` the binomial vanishes and so does the product (the
factor at `i = m` is `0`). Both cases are packaged by mathlib's `descPochhammer` route. -/
theorem cast_choose_eq_prod_range_div (m k : ℕ) :
    (m.choose k : ℚ) = (∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ))) / (k.factorial : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]

/-! ## β1 + β4 — the level-1 separable-stratum count

The stratum of monic squarefree `f` with `¬ X ∣ f` and factor-degree multiset `P.parts` is in
bijection with `Π_{d ∈ P.parts.toFinset} (k_d-subsets of poolSet F d)`, `k_d = P.parts.count d`,
via `f ↦ (d ↦ degree-d slice of normalizedFactors f)`. -/

section Stratum

/-- The pool as a `Finset` (via `Set.Finite.toFinset`). -/
noncomputable def poolFinset (F : Type*) [Field F] [Finite F] (d : ℕ) : Finset F[X] :=
  (finite_poolSet F d).toFinset

lemma mem_poolFinset {F : Type*} [Field F] [Finite F] {d : ℕ} {ψ : F[X]} :
    ψ ∈ poolFinset F d ↔ (Irreducible ψ ∧ ψ.Monic ∧ ψ.natDegree = d) ∧ ψ ≠ X := by
  simp only [poolFinset, Set.Finite.mem_toFinset, poolSet, Set.mem_sdiff, Set.mem_singleton_iff,
    L3.monicIrreducibleDegree, Set.mem_setOf_eq, ne_eq]

lemma card_poolFinset (F : Type*) [Field F] [Finite F] (d : ℕ) :
    (poolFinset F d).card = avail F d := by
  show (finite_poolSet F d).toFinset.card = avail F d
  rw [← Set.ncard_eq_toFinset_card (poolSet F d) (finite_poolSet F d), ← Nat.card_coe_set_eq,
    card_poolSet]

/-- **The level-1 separable stratum** (blueprint §3 `Sep₁(λ)` intersected with the pattern-λ
condition): monic, degree `n`, squarefree, `X ∤ f` (⟺ unit constant coefficient), with
factor-degree multiset `P.parts`. (The `natDegree` conjunct is implied by the pattern condition
but kept to match the blueprint's stratum description.) -/
def sepStratum (F : Type*) [Field F] [DecidableEq F] (n : ℕ) (P : n.Partition) : Set F[X] :=
  {f | f.Monic ∧ f.natDegree = n ∧ Squarefree f ∧ ¬ X ∣ f ∧
    (normalizedFactors f).map natDegree = P.parts}

/-- The degree-`d` slice of the (distinct) monic irreducible factors of `f`. -/
noncomputable def factorsAt {F : Type*} [Field F] [DecidableEq F] (f : F[X]) (d : ℕ) :
    Finset F[X] :=
  (normalizedFactors f).toFinset.filter fun ψ => ψ.natDegree = d

lemma mem_factorsAt {F : Type*} [Field F] [DecidableEq F] {f ψ : F[X]} {d : ℕ} :
    ψ ∈ factorsAt f d ↔ ψ ∈ normalizedFactors f ∧ ψ.natDegree = d := by
  simp [factorsAt]

/-- Over a field, every normalized factor is monic (`normalize` fixes it and `normalize` of a
nonzero polynomial is monic). -/
lemma monic_of_mem_normalizedFactors {F : Type*} [Field F] [DecidableEq F] {f ψ : F[X]}
    (hψ : ψ ∈ normalizedFactors f) : ψ.Monic := by
  have h := monic_normalize (p := ψ) (ne_zero_of_mem_normalizedFactors hψ)
  rwa [normalize_normalized_factor ψ hψ] at h

/-- On the stratum `¬ X ∣ f`, no normalized factor equals `X`. -/
lemma ne_X_of_not_X_dvd {F : Type*} [Field F] [DecidableEq F] {f ψ : F[X]}
    (hX : ¬ X ∣ f) (hψ : ψ ∈ normalizedFactors f) : ψ ≠ X := by
  rintro rfl
  exact hX (dvd_of_mem_normalizedFactors hψ)

/-- A monic polynomial over a field IS the product of its normalized factors (not merely up to
associates): `prod_normalizedFactors_eq` gives `normalize f`, and `normalize f = f` for monic. -/
lemma prod_normalizedFactors_of_monic {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hf : f.Monic) : (normalizedFactors f).prod = f := by
  rw [prod_normalizedFactors_eq hf.ne_zero, hf.normalize_eq_self]

/-- **Forward well-definedness (β1, one direction of the bijection).** For `f` in the stratum,
the degree-`d` factor slice is a `k_d`-subset of the punctured pool. -/
lemma factorsAt_mem_powersetCard {F : Type*} [Field F] [Finite F] [DecidableEq F]
    {n : ℕ} {P : n.Partition} {f : F[X]} (hf : f ∈ sepStratum F n P) {d : ℕ} :
    factorsAt f d ∈ (poolFinset F d).powersetCard (P.parts.count d) := by
  obtain ⟨hmon, -, hsq, hX, hparts⟩ := hf
  have hnodup : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hmon.ne_zero).mp hsq
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro ψ hψ
    rw [mem_factorsAt] at hψ
    rw [mem_poolFinset]
    exact ⟨⟨irreducible_of_normalized_factor ψ hψ.1, monic_of_mem_normalizedFactors hψ.1,
      hψ.2⟩, ne_X_of_not_X_dvd hX hψ.1⟩
  · -- the slice size is the multiplicity of `d` in the degree pattern
    have h2 : P.parts.count d
        = ((normalizedFactors f).filter (fun ψ => d = ψ.natDegree)).card := by
      rw [← hparts, Multiset.count_map]
    rw [h2]
    show ((normalizedFactors f).toFinset.filter (fun ψ => ψ.natDegree = d)).card = _
    rw [Finset.card_def, Finset.filter_val, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnodup]
    exact congrArg Multiset.card (Multiset.filter_congr (fun ψ _ => eq_comm))

/-- **Injectivity (β1).** A stratum element is determined by its degree slices: the slices
reassemble the (nodup) normalized-factor multiset, whose product is `f`. -/
lemma eq_of_factorsAt_eq {F : Type*} [Field F] [DecidableEq F]
    {n : ℕ} {P : n.Partition} {f g : F[X]}
    (hf : f ∈ sepStratum F n P) (hg : g ∈ sepStratum F n P)
    (h : ∀ d ∈ P.parts.toFinset, factorsAt f d = factorsAt g d) : f = g := by
  obtain ⟨hfm, -, hfsq, -, hfparts⟩ := hf
  obtain ⟨hgm, -, hgsq, -, hgparts⟩ := hg
  have hfn : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hfm.ne_zero).mp hfsq
  have hgn : (normalizedFactors g).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hgm.ne_zero).mp hgsq
  have step : ∀ (u v : F[X]), (normalizedFactors u).map natDegree = P.parts →
      (∀ d ∈ P.parts.toFinset, factorsAt u d = factorsAt v d) →
      ∀ ψ ∈ normalizedFactors u, ψ ∈ normalizedFactors v := by
    intro u v hparts hEq ψ hψ
    have hdmem : ψ.natDegree ∈ P.parts.toFinset := by
      rw [Multiset.mem_toFinset, ← hparts]
      exact Multiset.mem_map_of_mem _ hψ
    have hmem : ψ ∈ factorsAt v ψ.natDegree := by
      rw [← hEq _ hdmem, mem_factorsAt]
      exact ⟨hψ, rfl⟩
    exact (mem_factorsAt.mp hmem).1
  have hset : normalizedFactors f = normalizedFactors g := by
    have htf : (normalizedFactors f).toFinset = (normalizedFactors g).toFinset := by
      ext ψ
      simp only [Multiset.mem_toFinset]
      exact ⟨fun hψ => step f g hfparts h ψ hψ,
        fun hψ => step g f hgparts (fun d hd => (h d hd).symm) ψ hψ⟩
    have hval := congrArg Finset.val htf
    rwa [Multiset.toFinset_val, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hfn,
      Multiset.dedup_eq_self.mpr hgn] at hval
  rw [← prod_normalizedFactors_of_monic hfm, ← prod_normalizedFactors_of_monic hgm, hset]

/-- Degree-homogeneous finset families have `Nodup` total multiset (slices of distinct degrees
are disjoint, and each slice is a finset). -/
lemma nodup_sum_val {F : Type*} [Field F] (s : Finset ℕ) (G : ℕ → Finset F[X])
    (hdeg : ∀ d ∈ s, ∀ ψ ∈ G d, ψ.natDegree = d) :
    (∑ d ∈ s, (G d).val).Nodup := by
  revert hdeg
  induction s using Finset.cons_induction with
  | empty => intro _; simp
  | cons a t ha ih =>
    intro hdeg
    rw [Finset.sum_cons, Multiset.nodup_add]
    refine ⟨(G a).nodup, ih fun d hd ψ hψ => hdeg d (Finset.mem_cons_of_mem hd) ψ hψ, ?_⟩
    rw [Multiset.disjoint_left]
    intro ψ hψa hψt
    obtain ⟨d, hd, hmem⟩ := Multiset.mem_sum.mp hψt
    have h1 : ψ.natDegree = a := hdeg a (Finset.mem_cons_self a t) ψ hψa
    have h2 : ψ.natDegree = d := hdeg d (Finset.mem_cons_of_mem hd) ψ hmem
    have hda : d = a := by rw [← h2, h1]
    exact ha (hda ▸ hd)

/-- **Surjectivity (β1, the other direction).** Any choice of `k_d`-subsets of the pools
multiplies to a stratum element whose degree slices are the chosen subsets. -/
lemma prod_mem_sepStratum {F : Type*} [Field F] [Finite F] [DecidableEq F]
    {n : ℕ} {P : n.Partition} (G : ℕ → Finset F[X])
    (hsub : ∀ d ∈ P.parts.toFinset, ∀ ψ ∈ G d, ψ ∈ poolFinset F d)
    (hcard : ∀ d ∈ P.parts.toFinset, (G d).card = P.parts.count d) :
    (∑ e ∈ P.parts.toFinset, (G e).val).prod ∈ sepStratum F n P ∧
      ∀ d ∈ P.parts.toFinset,
        factorsAt ((∑ e ∈ P.parts.toFinset, (G e).val).prod) d = G d := by
  set s : Multiset F[X] := ∑ e ∈ P.parts.toFinset, (G e).val with hs_def
  have hdeg : ∀ d ∈ P.parts.toFinset, ∀ ψ ∈ G d, ψ.natDegree = d :=
    fun d hd ψ hψ => (mem_poolFinset.mp (hsub d hd ψ hψ)).1.2.2
  have hirr : ∀ ψ ∈ s, Irreducible ψ := by
    intro ψ hψ
    obtain ⟨d, hd, hmem⟩ := Multiset.mem_sum.mp hψ
    exact (mem_poolFinset.mp (hsub d hd ψ hmem)).1.1
  have hmon : ∀ ψ ∈ s, ψ.Monic := by
    intro ψ hψ
    obtain ⟨d, hd, hmem⟩ := Multiset.mem_sum.mp hψ
    exact (mem_poolFinset.mp (hsub d hd ψ hmem)).1.2.1
  have hneX : ∀ ψ ∈ s, ψ ≠ X := by
    intro ψ hψ
    obtain ⟨d, hd, hmem⟩ := Multiset.mem_sum.mp hψ
    exact (mem_poolFinset.mp (hsub d hd ψ hmem)).2
  have hnodup : s.Nodup := nodup_sum_val P.parts.toFinset G hdeg
  have hsmon : s.prod.Monic := by
    have h := monic_multiset_prod_of_monic s id fun ψ hψ => hmon ψ hψ
    rwa [Multiset.map_id] at h
  -- unique factorization: the factors of the product are exactly the chosen multiset
  have hnf : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s hirr,
      Multiset.map_congr rfl fun ψ hψ => (hmon ψ hψ).normalize_eq_self, Multiset.map_id']
  -- the degree multiset of `s` is the partition
  have hmapdeg : s.map natDegree = P.parts := by
    have hmap_sum : ∀ t : Finset ℕ,
        (∑ e ∈ t, (G e).val).map natDegree = ∑ e ∈ t, ((G e).val.map natDegree) := by
      intro t
      induction t using Finset.cons_induction with
      | empty => simp
      | cons a u ha ih => rw [Finset.sum_cons, Finset.sum_cons, Multiset.map_add, ih]
    have h1 : s.map natDegree = ∑ e ∈ P.parts.toFinset, ((G e).val.map natDegree) := by
      rw [hs_def]
      exact hmap_sum P.parts.toFinset
    have h2 : ∀ d ∈ P.parts.toFinset,
        (G d).val.map natDegree = P.parts.count d • ({d} : Multiset ℕ) := by
      intro d hd
      rw [Multiset.map_congr rfl fun ψ hψ => hdeg d hd ψ hψ, Multiset.map_const',
        Multiset.nsmul_singleton, ← Finset.card_def, hcard d hd]
    rw [h1, Finset.sum_congr rfl h2, Multiset.toFinset_sum_count_nsmul_eq]
  have hprod_mem : s.prod ∈ sepStratum F n P := by
    refine ⟨hsmon, ?_, ?_, ?_, ?_⟩
    · -- natDegree = n
      rw [natDegree_multiset_prod_of_monic s hmon, hmapdeg, P.parts_sum]
    · -- squarefree
      refine (squarefree_iff_nodup_normalizedFactors hsmon.ne_zero).mpr ?_
      rw [hnf]
      exact hnodup
    · -- ¬ X ∣ ∏
      intro hdvd
      obtain ⟨ψ, hψs, hXψ⟩ := Prime.exists_mem_multiset_dvd prime_X hdvd
      exact hneX ψ hψs (eq_of_monic_of_associated monic_X (hmon ψ hψs)
        (irreducible_X.associated_of_dvd (hirr ψ hψs) hXψ)).symm
    · -- degree pattern
      rw [hnf]
      exact hmapdeg
  have hfac : ∀ d ∈ P.parts.toFinset, factorsAt s.prod d = G d := by
    intro d hd
    ext ψ
    rw [mem_factorsAt, hnf]
    constructor
    · rintro ⟨hψs, hψdeg⟩
      obtain ⟨d', hd', hmem⟩ := Multiset.mem_sum.mp hψs
      have hdd : d' = d := by rw [← hψdeg, hdeg d' hd' ψ hmem]
      exact hdd ▸ hmem
    · intro hψ
      exact ⟨Multiset.mem_sum.mpr ⟨d, hd, hψ⟩, hdeg d hd ψ hψ⟩
  exact ⟨hprod_mem, hfac⟩

/-- **β1+β4: the level-1 separable-stratum count.** Over a finite field `F`, for a partition
`P : n.Partition`, the number of monic squarefree degree-`n` polynomials `f` with `¬ X ∣ f` and
factor-degree multiset `P.parts` equals
`∏_{d ∈ P.parts.toFinset} C(avail F d, P.parts.count d)` — `k_d` distinct monic irreducible
factors of each degree `d`, drawn from the punctured pool (`X` excluded at `d = 1`). -/
theorem card_sepStratum (F : Type*) [Field F] [Finite F] [DecidableEq F]
    (n : ℕ) (P : n.Partition) :
    Nat.card (sepStratum F n P)
      = ∏ d ∈ P.parts.toFinset, (avail F d).choose (P.parts.count d) := by
  have key : Nat.card (sepStratum F n P)
      = Nat.card ((d : P.parts.toFinset) →
          ↥((poolFinset F (d : ℕ)).powersetCard (P.parts.count (d : ℕ)))) := by
    refine Nat.card_eq_of_bijective
      (fun f d => ⟨factorsAt (f : F[X]) (d : ℕ), factorsAt_mem_powersetCard f.2⟩)
      ⟨?_, ?_⟩
    · -- injective
      intro f g hfg
      refine Subtype.ext (eq_of_factorsAt_eq f.2 g.2 fun d hd => ?_)
      exact congrArg Subtype.val (congrFun hfg ⟨d, hd⟩)
    · -- surjective
      intro y
      set G : ℕ → Finset F[X] := fun d =>
        if hd : d ∈ P.parts.toFinset then ((y ⟨d, hd⟩ : Finset F[X])) else ∅ with hG_def
      have hG_eq : ∀ (d : ℕ) (hd : d ∈ P.parts.toFinset),
          G d = (y ⟨d, hd⟩ : Finset F[X]) := by
        intro d hd
        simp only [hG_def]
        rw [dif_pos hd]
      have hsub : ∀ d ∈ P.parts.toFinset, ∀ ψ ∈ G d, ψ ∈ poolFinset F d := by
        intro d hd ψ hψ
        rw [hG_eq d hd] at hψ
        exact (Finset.mem_powersetCard.mp (y ⟨d, hd⟩).2).1 hψ
      have hcard : ∀ d ∈ P.parts.toFinset, (G d).card = P.parts.count d := by
        intro d hd
        rw [hG_eq d hd]
        exact (Finset.mem_powersetCard.mp (y ⟨d, hd⟩).2).2
      obtain ⟨hmem, hfac⟩ := prod_mem_sepStratum G hsub hcard
      refine ⟨⟨_, hmem⟩, ?_⟩
      funext d
      refine Subtype.ext ?_
      show factorsAt _ (d : ℕ) = _
      rw [hfac (d : ℕ) d.2, hG_eq (d : ℕ) d.2]
  rw [key, Nat.card_pi,
    ← Finset.prod_coe_sort P.parts.toFinset (fun d => (avail F d).choose (P.parts.count d))]
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [Nat.card_eq_finsetCard, Finset.card_powersetCard, card_poolFinset]

end Stratum

end LeanUrat.OM.Order0
