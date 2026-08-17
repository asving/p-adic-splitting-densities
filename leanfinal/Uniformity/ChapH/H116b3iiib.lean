/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H63w
import Uniformity.ChapH.H116b2
import Uniformity.ChapH.H116b3i
import Uniformity.ChapH.H116b3ii
import Uniformity.ChapH.H116b3iii
import Uniformity.ChapB.B39a

/-!
# Uniformity.ChapH.H116b3iiib — the ¬IsCSState transport, part 2 (SKELETON v2)

**Chapter H, NODE H.116b3-iii (2/2)** — the assembly `not_isCSState_plantedPoly_swap` at the
byte-frozen A-H.8 statement, per the block record §3's steps (3a)–(3f) as corrected by A-H.8.
FENCE A-H.8/F1 binds. ⚠ Consumes `B39a` (rider signed, owner ratification-by-compile
2026-08-17).

CHAIN: `planted_map_residue_eq` (PROVED — the u = 0 branch's engine) →
`planted_side_transport_at_zero` (u = 0: the full witness transport off the equal residue
maps) → `planted_delta_above_line` (u > 0: steps (3a)+(3b)+(3c), THE BEAST) → the assembly
(via b3-ii's congruences and part 1's bridge, `monicPoly_coeff_self` as the plumbing).
Every declaration PROVED (sorry-free).
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The u = 0 engine (record step (3e), first half).** The two planted products have EQUAL
reductions mod `π`: every alpha factor reduces to `X ^ μ_p` independently of its presentation
(`alphaParent_map_residue`), and the cofactor is shared. -/
theorem planted_map_residue_eq {π : O} (hπ : Irreducible π) {N r : ℕ}
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) :
    (plantedPoly π L bb' Qc).map (residue O) = (plantedPoly π L bb Qc).map (residue O) := by
  unfold plantedPoly
  rw [Polynomial.map_mul, Polynomial.map_mul]
  congr 1
  rw [Polynomial.map_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [alphaParent_map_residue hπ _ (hLchild p.1 p.2).2.1,
    alphaParent_map_residue hπ _ (hLchild p.1 p.2).2.1]

/-- Height-0 digit polynomial of a constant: the residue. -/
private theorem digPoly_zero_C {π : O} (c : O) :
    digPoly π 0 (Polynomial.C c) = Polynomial.C (residue O c) := by
  unfold digPoly
  rw [Polynomial.natDegree_C]
  rw [Finset.sum_range_one, Polynomial.coeff_C_zero, pow_zero, mul_one, digAt_zero]

/-- The monic support value at slope `(0, 1)` vanishes (attained at the top coefficient). -/
private theorem suppVal_zero_one_of_monic {g : Polynomial O} (hg : g.Monic) :
    suppVal X g 0 1 = 0 := by
  refine le_antisymm ?_ zero_le
  have hmem : g.natDegree ∈ Finset.range (g.natDegree + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_self _)
  have hle := Finset.inf_le (f := fun j => (1 : ℕ) • npHgt X g j + ((0 * j : ℕ) : ℕ∞)) hmem
  have hval : (1 : ℕ) • npHgt X g g.natDegree + ((0 * g.natDegree : ℕ) : ℕ∞) = 0 := by
    rw [npHgt_X, hg.coeff_natDegree,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 isUnit_one]
    simp
  rw [suppVal]
  exact hval ▸ hle

/-- At `(0, 1)` on a monic polynomial, on-side means height zero, i.e. unit coefficient,
i.e. nonzero residue. -/
private theorem onSide_zero_one_iff {g : Polynomial O}
    (hg : g.Monic) (j : ℕ) :
    OnSide X g 0 1 j ↔ (g.map (residue O)).coeff j ≠ 0 := by
  have hOn : OnSide X g 0 1 j ↔ npHgt X g j = 0 := by
    unfold OnSide
    rw [suppVal_zero_one_of_monic hg]
    constructor
    · intro h
      have := h
      rwa [one_nsmul, Nat.zero_mul, Nat.cast_zero, add_zero] at this
    · intro h
      rw [one_nsmul, h, Nat.zero_mul, Nat.cast_zero, add_zero]
  rw [hOn, npHgt_X, Polynomial.coeff_map]
  constructor
  · intro h
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
      (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  · intro h
    exact IsDiscreteValuationRing.addVal_eq_zero_iff.2
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h)

/-- **The u = 0 branch (record step (3e), second half).** At `(u, ℓ) = (0, 1)` the whole side
datum — support value, side set, pinned height (necessarily `0`), and residual polynomial —
is read off `f mod π`, so equal reductions transport the CS witness verbatim. B.77 is NOT
usable here (A-H.8 §2.2: `Visible π X f 1` fails on the planted `f`). -/
private theorem planted_side_transport_at_zero {π : O} (hπ : Irreducible π)
    {f f' : Polynomial O} (hf : f.Monic) (hf' : f'.Monic)
    (hdeg : f'.natDegree = f.natDegree)
    (hmap : f'.map (residue O) = f.map (residue O)) :
    sideSet X f' 0 1 = sideSet X f 0 1 ∧
      ∀ (hne : (sideSet X f 0 1).Nonempty) (hne' : (sideSet X f' 0 1).Nonempty),
        resPoly π X f' 0 1 hne' 0 = resPoly π X f 0 1 hne 0 := by
  classical
  have hres : ∀ j, residue O (f'.coeff j) = residue O (f.coeff j) := by
    intro j
    have := congrArg (fun p => Polynomial.coeff p j) hmap
    simpa [Polynomial.coeff_map] using this
  have hset : sideSet X f' 0 1 = sideSet X f 0 1 := by
    unfold sideSet
    rw [hdeg]
    refine Finset.filter_congr fun j _ => ?_
    rw [onSide_zero_one_iff hf', onSide_zero_one_iff hf, hmap]
  refine ⟨hset, fun hne hne' => ?_⟩
  have hmin : sideMin X f' 0 1 hne' = sideMin X f 0 1 hne := by
    unfold sideMin
    have key : ∀ (h₁ : (sideSet X f' 0 1).Nonempty) (h₂ : (sideSet X f 0 1).Nonempty),
        (sideSet X f' 0 1).min' h₁ = (sideSet X f 0 1).min' h₂ := by
      rw [hset]; intro h₁ h₂; rfl
    exact key hne' hne
  have hmax : sideMax X f' 0 1 hne' = sideMax X f 0 1 hne := by
    unfold sideMax
    have key : ∀ (h₁ : (sideSet X f' 0 1).Nonempty) (h₂ : (sideSet X f 0 1).Nonempty),
        (sideSet X f' 0 1).max' h₁ = (sideSet X f 0 1).max' h₂ := by
      rw [hset]; intro h₁ h₂; rfl
    exact key hne' hne
  have hdegs : sideDeg X f' 0 1 hne' = sideDeg X f 0 1 hne := by
    unfold sideDeg
    rw [hmin, hmax]
  unfold resPoly
  rw [hdegs]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  unfold resCoeff
  rw [hmin]
  unfold resMk
  rw [dev_X, dev_X, Nat.zero_sub, digPoly_zero_C, digPoly_zero_C, hres]

/-! ### The pointwise line toolkit (record step (3c)'s engine)

`lineF ℓ u g j := ℓ • npHgt X g j + u·j` is the cleared support functional read pointwise.
Everything below manipulates it through three moves: it is monotone in the height, it
distributes over convolution (`addVal_mul` + `coeff_mul`), and lower bounds pass through
finite sums (`addVal_add`). -/

private theorem enat_smul_mono'' {ℓ : ℕ} {x y : ℕ∞} (h : x ≤ y) : ℓ • x ≤ ℓ • y := by
  rw [nsmul_eq_mul, nsmul_eq_mul]
  exact mul_le_mul_right h _

private theorem enat_smul_cancel' {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∀ {x y : ℕ∞}, ℓ • x = ℓ • y → x = y := by
  have hℓ0 : (ℓ : ℕ∞) ≠ 0 := by exact_mod_cast hℓ.ne'
  intro x y h
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe y =>
      rw [ENat.mul_top hℓ0] at h
      exact absurd h.symm (WithTop.mul_ne_top (ENat.coe_ne_top _) (ENat.coe_ne_top _))
  | coe x =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [ENat.mul_top hℓ0] at h
      exact absurd h (WithTop.mul_ne_top (ENat.coe_ne_top _) (ENat.coe_ne_top _))
    | coe y =>
      rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have hnat : ℓ * x = ℓ * y := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left hℓ hnat

/-- A uniform lower bound on the line functional passes through finite sums of ring
elements. -/
private theorem line_le_addVal_sum {ι : Type*} {s : Finset ι} {f : ι → O} {c K : ℕ∞}
    {ℓ : ℕ} (hℓ : 0 < ℓ)
    (h : ∀ i ∈ s, c ≤ ℓ • IsDiscreteValuationRing.addVal O (f i) + K) :
    c ≤ ℓ • IsDiscreteValuationRing.addVal O (∑ i ∈ s, f i) + K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
        ENat.mul_top (by exact_mod_cast hℓ.ne')]
      exact le_top.trans (le_self_add)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hmin := IsDiscreteValuationRing.addVal_add
        (a := f i) (b := ∑ j ∈ s, f j)
      rcases min_le_iff.1 (le_refl (min (IsDiscreteValuationRing.addVal O (f i))
          (IsDiscreteValuationRing.addVal O (∑ j ∈ s, f j)))) with _ | _
      all_goals {
        rcases le_total (IsDiscreteValuationRing.addVal O (f i))
            (IsDiscreteValuationRing.addVal O (∑ j ∈ s, f j)) with hcase | hcase
        · have hv : IsDiscreteValuationRing.addVal O (f i)
              ≤ IsDiscreteValuationRing.addVal O (f i + ∑ j ∈ s, f j) := by
            have := hmin; rwa [min_eq_left hcase] at this
          exact le_trans (h i (Finset.mem_insert_self i s))
            (add_le_add (enat_smul_mono'' hv) le_rfl)
        · have hv : IsDiscreteValuationRing.addVal O (∑ j ∈ s, f j)
              ≤ IsDiscreteValuationRing.addVal O (f i + ∑ j ∈ s, f j) := by
            have := hmin; rwa [min_eq_right hcase] at this
          exact le_trans (ih fun p hp => h p (Finset.mem_insert_of_mem hp))
            (add_le_add (enat_smul_mono'' hv) le_rfl)
      }

/-- **Pointwise convolution**: line lower bounds ADD along a product of polynomials. -/
private theorem line_conv {u ℓ : ℕ} (hℓ : 0 < ℓ) {g h : Polynomial O} {a b : ℕ∞}
    (hg : ∀ s, a ≤ ℓ • npHgt X g s + ((u * s : ℕ) : ℕ∞))
    (hh : ∀ s, b ≤ ℓ • npHgt X h s + ((u * s : ℕ) : ℕ∞)) :
    ∀ j, a + b ≤ ℓ • npHgt X (g * h) j + ((u * j : ℕ) : ℕ∞) := by
  intro j
  rw [npHgt_X, Polynomial.coeff_mul]
  refine line_le_addVal_sum hℓ fun p hp => ?_
  have hpj : p.1 + p.2 = j := Finset.mem_antidiagonal.1 hp
  rw [IsDiscreteValuationRing.addVal_mul, smul_add]
  have hsplit : ((u * j : ℕ) : ℕ∞) = ((u * p.1 : ℕ) : ℕ∞) + ((u * p.2 : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add, ← Nat.mul_add, hpj]
  rw [hsplit]
  have hg' := hg p.1
  have hh' := hh p.2
  rw [npHgt_X] at hg' hh'
  calc a + b ≤ (ℓ • IsDiscreteValuationRing.addVal O (g.coeff p.1) + ((u * p.1 : ℕ) : ℕ∞))
        + (ℓ • IsDiscreteValuationRing.addVal O (h.coeff p.2) + ((u * p.2 : ℕ) : ℕ∞)) :=
        add_le_add hg' hh'
    _ = _ := by ring

/-- Pointwise convolution over a `Finset` product. -/
private theorem line_conv_prod {ι : Type*} {u ℓ : ℕ} (hℓ : 0 < ℓ) {s : Finset ι}
    {A : ι → Polynomial O} {c : ι → ℕ∞}
    (h : ∀ p ∈ s, ∀ j, c p ≤ ℓ • npHgt X (A p) j + ((u * j : ℕ) : ℕ∞)) :
    ∀ j, (∑ p ∈ s, c p) ≤ ℓ • npHgt X (∏ p ∈ s, A p) j + ((u * j : ℕ) : ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro j
      rw [Finset.sum_empty]
      exact zero_le
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact line_conv hℓ (h i (Finset.mem_insert_self i s))
        (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- The pointwise reading of the support value: every abscissa sits on or above the support
line (inside the coefficient range by the `inf`, outside it vacuously at `⊤`). -/
private theorem suppVal_le_line {u ℓ : ℕ} (hℓ : 0 < ℓ) (g : Polynomial O) :
    ∀ j, suppVal X g u ℓ ≤ ℓ • npHgt X g j + ((u * j : ℕ) : ℕ∞) := by
  intro j
  by_cases hj : j ≤ g.natDegree
  · exact Finset.inf_le (Finset.mem_range.2 (by omega))
  · have hz : g.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [npHgt_X, hz, IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
      ENat.mul_top (by exact_mod_cast hℓ.ne')]
    exact le_top.trans le_self_add

/-- **The difference-factor line bound (record step (3a), graded form).** The swap difference
of one planted factor clears its own factor's support value by a full `ℓ`. -/
private theorem line_diff_factor {π : O} (hπ : Irreducible π) {μ k : ℕ} (hk : 1 ≤ k)
    {b b' : Fin μ → O} (hbb : ∀ i, b' i - b i ∈ maximalIdeal O) (ŵ : O)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) :
    ∀ s, ((ℓ + μ * min (ℓ * k) u : ℕ) : ℕ∞)
      ≤ ℓ • npHgt X (alphaParent π b' k ŵ - alphaParent π b k ŵ) s
          + ((u * s : ℕ) : ℕ∞) := by
  intro s
  by_cases hs : s ≤ μ
  · have hdvd := pow_grade_succ_dvd_coeff_alphaParent_sub hπ hbb k ŵ s
    have hval : ((k * (μ - s) + 1 : ℕ) : ℕ∞)
        ≤ npHgt X (alphaParent π b' k ŵ - alphaParent π b k ŵ) s := by
      rw [npHgt_X]
      exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hdvd
    refine le_trans ?_ (add_le_add (enat_smul_mono'' hval) le_rfl)
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add]
    refine Nat.cast_le.2 ?_
    have h3 : ℓ * (k * (μ - s) + 1) = ℓ * (k * (μ - s)) + ℓ := by ring
    rcases le_total (ℓ * k) u with hmin | hmin
    · rw [min_eq_left hmin]
      have h1 : ℓ * k * s ≤ u * s := Nat.mul_le_mul_right s hmin
      have h2 : μ * (ℓ * k) = ℓ * (k * (μ - s)) + ℓ * k * s := by
        obtain ⟨t, ht⟩ : ∃ t, μ = t + s := ⟨μ - s, (Nat.sub_add_cancel hs).symm⟩
        subst ht
        rw [Nat.add_sub_cancel]
        ring
      omega
    · rw [min_eq_right hmin]
      have h1 : u * (μ - s) ≤ ℓ * (k * (μ - s)) := by
        have h := Nat.mul_le_mul_right (μ - s) hmin
        calc u * (μ - s) ≤ ℓ * k * (μ - s) := h
          _ = ℓ * (k * (μ - s)) := by ring
      have h2 : μ * u = u * (μ - s) + u * s := by
        obtain ⟨t, ht⟩ : ∃ t, μ = t + s := ⟨μ - s, (Nat.sub_add_cancel hs).symm⟩
        subst ht
        rw [Nat.add_sub_cancel]
        ring
      omega
  · have hz : (alphaParent π b' k ŵ - alphaParent π b k ŵ).coeff s = 0 := by
      have hd' : (alphaParent π b' k ŵ).coeff s = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [alphaParent_natDegree]; omega)
      have hd : (alphaParent π b k ŵ).coeff s = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [alphaParent_natDegree]; omega)
      rw [Polynomial.coeff_sub, hd', hd, sub_zero]
    rw [npHgt_X, hz, IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
      ENat.mul_top (by exact_mod_cast hℓ.ne')]
    exact le_top.trans le_self_add

/-! ### The Minkowski identity (record step (3b), via B39a's general graded product law) -/

private theorem isKey_X' : IsKey (X : Polynomial O) := by
  refine ⟨Polynomial.monic_X, by rw [Polynomial.natDegree_X]; norm_num, ?_⟩
  rw [Polynomial.map_X]
  exact Polynomial.irreducible_X

/-- Pinned side minima and pinned heights ADD along a finite product (B39a iterated). -/
private theorem minkowski_prod {ι : Type*} {u ℓ : ℕ} {π : O} (hπ : Irreducible π)
    (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {s : Finset ι} {A : ι → Polynomial O} {Hh m : ι → ℕ}
    (hpin : ∀ p ∈ s, ∀ hne : (sideSet X (A p) u ℓ).Nonempty,
      npHgt X (A p) (sideMin X (A p) u ℓ hne) = ((Hh p : ℕ) : ℕ∞))
    (hmin : ∀ p ∈ s, ∀ hne : (sideSet X (A p) u ℓ).Nonempty,
      sideMin X (A p) u ℓ hne = m p) :
    ∀ hne : (sideSet X (∏ p ∈ s, A p) u ℓ).Nonempty,
      npHgt X (∏ p ∈ s, A p) (sideMin X (∏ p ∈ s, A p) u ℓ hne)
          = ((∑ p ∈ s, Hh p : ℕ) : ℕ∞) ∧
        sideMin X (∏ p ∈ s, A p) u ℓ hne = ∑ p ∈ s, m p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro hne
      rw [Finset.sum_empty, Finset.sum_empty]
      have hone : ∀ j ∈ sideSet X (1 : Polynomial O) u ℓ, j = 0 := by
        intro j hj
        have hjr := (Finset.mem_filter.1 hj).1
        rw [Polynomial.natDegree_one] at hjr
        have := Finset.mem_range.1 hjr
        omega
      have haux : ∀ (h₁ : (sideSet X (1 : Polynomial O) u ℓ).Nonempty),
          npHgt X (1 : Polynomial O) (sideMin X (1 : Polynomial O) u ℓ h₁)
              = ((0 : ℕ) : ℕ∞) ∧
            sideMin X (1 : Polynomial O) u ℓ h₁ = 0 := by
        intro h₁
        have hmin0 : sideMin X (1 : Polynomial O) u ℓ h₁ = 0 :=
          hone _ (Finset.min'_mem _ h₁)
        refine ⟨?_, hmin0⟩
        rw [hmin0, npHgt_X, Polynomial.coeff_one_zero,
          IsDiscreteValuationRing.addVal_one, Nat.cast_zero]
      have hgen : ∀ (h₁ : (sideSet X (∏ p ∈ (∅ : Finset ι), A p) u ℓ).Nonempty),
          npHgt X (∏ p ∈ (∅ : Finset ι), A p)
              (sideMin X (∏ p ∈ (∅ : Finset ι), A p) u ℓ h₁) = ((0 : ℕ) : ℕ∞) ∧
            sideMin X (∏ p ∈ (∅ : Finset ι), A p) u ℓ h₁ = 0 := by
        rw [Finset.prod_empty]
        exact haux
      exact hgen hne
  | insert i s hi ih =>
      intro hne
      have hneA : (sideSet X (A i) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
      have hneT : (sideSet X (∏ p ∈ s, A p) u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
      obtain ⟨ihpin, ihmin⟩ := ih
        (fun p hp => hpin p (Finset.mem_insert_of_mem hp))
        (fun p hp => hmin p (Finset.mem_insert_of_mem hp)) hneT
      have hpinA := hpin i (Finset.mem_insert_self i s) hneA
      have hminA := hmin i (Finset.mem_insert_self i s) hneA
      -- support values are pinned, hence finite
      have hWA : suppVal X (A i) u ℓ
          = ((ℓ * Hh i + u * m i : ℕ) : ℕ∞) := by
        have := suppVal_eq_of_onSide hpinA
          (onSide_of_mem_sideSet (Finset.min'_mem _ hneA))
        rwa [hminA] at this
      have hWT : suppVal X (∏ p ∈ s, A p) u ℓ
          = ((ℓ * (∑ p ∈ s, Hh p) + u * (∑ p ∈ s, m p) : ℕ) : ℕ∞) := by
        have := suppVal_eq_of_onSide ihpin
          (onSide_of_mem_sideSet (Finset.min'_mem _ hneT))
        rwa [ihmin] at this
      have htf : suppVal X (A i) u ℓ ≠ ⊤ := by rw [hWA]; exact ENat.coe_ne_top _
      have htz : suppVal X (∏ p ∈ s, A p) u ℓ ≠ ⊤ := by rw [hWT]; exact ENat.coe_ne_top _
      have hprod : (∏ p ∈ insert i s, A p) = A i * ∏ p ∈ s, A p :=
        Finset.prod_insert hi
      have hne' : (sideSet X (A i * ∏ p ∈ s, A p) u ℓ).Nonempty := by
        rw [← hprod]; exact hne
      have hminmul := sideMin_mul_gen hπ isKey_X' hu hℓ hcop htf htz hneA hneT
        hpinA ihpin hne'
      have hpinmul := npHgt_mul_gen hπ isKey_X' hu hℓ hcop htf htz hneA hneT
        hpinA ihpin
      constructor
      · have goal1 : npHgt X (A i * ∏ p ∈ s, A p)
            (sideMin X (A i * ∏ p ∈ s, A p) u ℓ hne')
              = ((Hh i + ∑ p ∈ s, Hh p : ℕ) : ℕ∞) := by
          rw [hminmul]
          exact hpinmul
        rw [Finset.sum_insert hi]
        have hcongr : ∀ (h₁ : (sideSet X (∏ p ∈ insert i s, A p) u ℓ).Nonempty),
            npHgt X (∏ p ∈ insert i s, A p)
              (sideMin X (∏ p ∈ insert i s, A p) u ℓ h₁)
                = ((Hh i + ∑ p ∈ s, Hh p : ℕ) : ℕ∞) := by
          rw [hprod]
          intro h₁
          exact goal1
        exact hcongr hne
      · rw [Finset.sum_insert hi]
        have hcongr : ∀ (h₁ : (sideSet X (∏ p ∈ insert i s, A p) u ℓ).Nonempty),
            sideMin X (∏ p ∈ insert i s, A p) u ℓ h₁ = m i + ∑ p ∈ s, m p := by
          rw [hprod]
          intro h₁
          rw [hminmul, hminA, ihmin]
        exact hcongr hne

/-- **L2 = record steps (3a)+(3b)+(3c): the swap difference sits strictly above the planted
supporting line** at every `(u, ℓ)` with `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ` — exactly
b3-ii's `habove` hypothesis. Route: per-factor pins (b3-i) → the Minkowski identity
(`minkowski_prod`, B39a iterated, then once against the cofactor) → the H63w signed-sum
telescope with `line_diff_factor` + `line_conv_prod` → the pointwise convolution against the
cofactor. -/
private theorem planted_delta_above_line {π : O} (hπ : Irreducible π) {N r : ℕ}
    (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) :
    ∀ j, suppVal X (plantedPoly π L bb Qc) u ℓ
      < ℓ • npHgt X (plantedPoly π L bb' Qc - plantedPoly π L bb Qc) j
          + ((u * j : ℕ) : ℕ∞) := by
  classical
  -- the two planted products and the shared cofactor
  set P : Polynomial O := ∏ p ∈ L.attach,
    alphaParent π (classSect O p.1.1 N ((bb p)).1) p.1.2.1 (resSect O p.1.2.2) with hP
  set P' : Polynomial O := ∏ p ∈ L.attach,
    alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2) with hP'
  set Q : Polynomial O := monicPoly (classSect O r N Qc.1) with hQ
  have hfPQ : plantedPoly π L bb Qc = P * Q := by rw [hP, hQ]; rfl
  have hfPQ' : plantedPoly π L bb' Qc = P' * Q := by rw [hP', hQ]; rfl
  -- the per-factor combinatorial profile
  set Hfun : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
    fun p => if ℓ * p.1.2.1 ≤ u then p.1.1 * p.1.2.1 else 0 with hHfun
  set mfun : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
    fun p => if ℓ * p.1.2.1 ≤ u then 0 else p.1.1 with hmfun
  set wfun : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
    fun p => ℓ * Hfun p + u * mfun p with hwfun
  -- per-factor data, unprimed and primed
  have hbmem : ∀ (cc : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
      (p : {x : ℕ × ℕ × ResidueField O // x ∈ L}) (i : Fin p.1.1),
      classSect O p.1.1 N ((cc p)).1 i ∈ maximalIdeal O :=
    fun cc p i => mem_maximalIdeal_classSect hN (cc p) i
  have hpinfam : ∀ (cc : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N),
      ∀ p ∈ L.attach, ∀ hne : (sideSet X
        (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1 (resSect O p.1.2.2)) u ℓ).Nonempty,
        npHgt X (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1 (resSect O p.1.2.2))
            (sideMin X (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1
              (resSect O p.1.2.2)) u ℓ hne) = ((Hfun p : ℕ) : ℕ∞) := by
    intro cc p _ hne
    rw [hHfun]
    exact npHgt_sideMin_alphaParent hπ (hbmem cc p) (hLchild p.1 p.2).2.2
      (residue_resSect O p.1.2.2) hne
  have hminfam : ∀ (cc : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N),
      ∀ p ∈ L.attach, ∀ hne : (sideSet X
        (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1 (resSect O p.1.2.2)) u ℓ).Nonempty,
        sideMin X (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1
          (resSect O p.1.2.2)) u ℓ hne = mfun p := by
    intro cc p _ hne
    rw [hmfun]
    exact sideMin_alphaParent hπ (hbmem cc p) (hLchild p.1 p.2).2.2
      (residue_resSect O p.1.2.2) hne
  have hWfam : ∀ (cc : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
      (p : {x : ℕ × ℕ × ResidueField O // x ∈ L}),
      suppVal X (alphaParent π (classSect O p.1.1 N ((cc p)).1) p.1.2.1 (resSect O p.1.2.2)) u ℓ
        = ((p.1.1 * min (ℓ * p.1.2.1) u : ℕ) : ℕ∞) :=
    fun cc p => suppVal_alphaParent hπ (hbmem cc p) (hLchild p.1 p.2).2.2
      (residue_resSect O p.1.2.2) u ℓ
  -- the per-factor support value in profile form: w p = μ_p · min(ℓk_p, u)
  have hwvalue : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      wfun p = p.1.1 * min (ℓ * p.1.2.1) u := by
    intro p
    simp only [hwfun, hHfun, hmfun]
    by_cases hcase : ℓ * p.1.2.1 ≤ u
    · rw [if_pos hcase, if_pos hcase, min_eq_left hcase]
      ring
    · rw [if_neg hcase, if_neg hcase, min_eq_right (le_of_not_ge hcase)]
      ring
  -- the Minkowski profile of P (and P')
  have hneP : (sideSet X P u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  obtain ⟨hPpin, hPmin⟩ := minkowski_prod hπ hu hℓ hcop
    (hpinfam bb) (hminfam bb) hneP
  have hWP : suppVal X P u ℓ
      = ((ℓ * (∑ p ∈ L.attach, Hfun p) + u * (∑ p ∈ L.attach, mfun p) : ℕ) : ℕ∞) := by
    have := suppVal_eq_of_onSide hPpin (onSide_of_mem_sideSet (Finset.min'_mem _ hneP))
    rwa [hPmin] at this
  -- the cofactor profile
  have hQmonic : Q.Monic := by rw [hQ]; exact monicPoly_monic _
  have hQtop : suppVal X Q u ℓ ≠ ⊤ := by
    have h1 := suppVal_le_line (u := u) hℓ Q Q.natDegree
    have h2 : npHgt X Q Q.natDegree = 0 := by
      rw [npHgt_X, hQmonic.coeff_natDegree, IsDiscreteValuationRing.addVal_one]
    rw [h2, smul_zero, zero_add] at h1
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
  have hneQ : (sideSet X Q u ℓ).Nonempty := sideSet_nonempty_gen _ _ _ _
  obtain ⟨HQ, hHQ⟩ := ENat.ne_top_iff_exists.1
    (npHgt_ne_top_of_onSide hℓ hQtop (onSide_of_mem_sideSet (Finset.min'_mem _ hneQ)))
  have hHQ' : npHgt X Q (sideMin X Q u ℓ hneQ) = ((HQ : ℕ) : ℕ∞) := hHQ.symm
  set mQ : ℕ := sideMin X Q u ℓ hneQ with hmQ
  have hWQ : suppVal X Q u ℓ = ((ℓ * HQ + u * mQ : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHQ' (onSide_of_mem_sideSet (Finset.min'_mem _ hneQ))
  -- the Minkowski value of the whole planted polynomial
  have htfP : suppVal X P u ℓ ≠ ⊤ := by rw [hWP]; exact ENat.coe_ne_top _
  have hWf : suppVal X (P * Q) u ℓ
      = ((ℓ * ((∑ p ∈ L.attach, Hfun p) + HQ)
          + u * ((∑ p ∈ L.attach, mfun p) + mQ) : ℕ) : ℕ∞) := by
    have := suppVal_mul_gen hπ isKey_X' hu hℓ hcop htfP hQtop hneP hneQ hPpin hHQ'
    rwa [hPmin, ← hmQ] at this
  -- (IV): the swap difference clears the planted support line by a full ℓ
  have hdiffbound : ∀ i, ((ℓ + ∑ p ∈ L.attach, wfun p : ℕ) : ℕ∞)
      ≤ ℓ • npHgt X (P' - P) i + ((u * i : ℕ) : ℕ∞) := by
    have hid := prod_sub_prod_eq_signed_sum L.attach
      (fun p => alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2)
        - alphaParent π (classSect O p.1.1 N ((bb p)).1) p.1.2.1 (resSect O p.1.2.2))
      (fun p => alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2))
    simp only [sub_sub_cancel] at hid
    rw [← hP', ← hP] at hid
    intro i
    rw [hid, npHgt_X, Polynomial.finsetSum_coeff]
    refine line_le_addVal_sum hℓ fun t ht => ?_
    have htne : t.Nonempty :=
      Finset.nonempty_of_ne_empty (Finset.ne_of_mem_erase ht)
    have htsub : t ⊆ L.attach := Finset.mem_powerset.1 (Finset.mem_of_mem_erase ht)
    -- the three factor bounds
    have hsign : ∀ s', (0 : ℕ∞)
        ≤ ℓ • npHgt X ((-1 : Polynomial O) ^ (t.card + 1)) s' + ((u * s' : ℕ) : ℕ∞) :=
      fun _ => zero_le
    have hdiffs : ∀ p ∈ t, ∀ s', (((ℓ + wfun p : ℕ)) : ℕ∞)
        ≤ ℓ • npHgt X
            (alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2)
              - alphaParent π (classSect O p.1.1 N ((bb p)).1) p.1.2.1 (resSect O p.1.2.2)) s'
          + ((u * s' : ℕ) : ℕ∞) := by
      intro p _ s'
      have := line_diff_factor hπ (hLchild p.1 p.2).2.1
        (fun i => Submodule.sub_mem _ (hbmem bb' p i) (hbmem bb p i))
        (resSect O p.1.2.2) hu hℓ s'
      rwa [← hwvalue p] at this
    have hprimed : ∀ p ∈ L.attach \ t, ∀ s', (((wfun p : ℕ)) : ℕ∞)
        ≤ ℓ • npHgt X
            (alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2)) s'
          + ((u * s' : ℕ) : ℕ∞) := by
      intro p _ s'
      have hline := suppVal_le_line (u := u) hℓ
        (alphaParent π (classSect O p.1.1 N ((bb' p)).1) p.1.2.1 (resSect O p.1.2.2)) s'
      have hW := hWfam bb' p
      rw [hW, ← hwvalue p] at hline
      exact hline
    -- convolve
    have hbt := line_conv_prod hℓ hdiffs
    have hbp := line_conv_prod hℓ hprimed
    have hconv := line_conv hℓ (line_conv hℓ hsign hbt) hbp i
    rw [← npHgt_X]
    refine le_trans ?_ hconv
    -- the constant arithmetic, at ℕ level
    rw [zero_add, ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_add]
    refine Nat.cast_le.2 ?_
    have hsplit : (∑ p ∈ t, wfun p) + ∑ p ∈ L.attach \ t, wfun p
        = ∑ p ∈ L.attach, wfun p := by
      rw [add_comm]
      exact Finset.sum_sdiff htsub
    have hcard : 1 ≤ t.card := Finset.card_pos.2 htne
    have hexpand : ∑ p ∈ t, (ℓ + wfun p) = t.card * ℓ + ∑ p ∈ t, wfun p := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have hcardle : ℓ ≤ t.card * ℓ := Nat.le_mul_of_pos_left ℓ (by omega)
    omega
  -- (V) + the strict inequality
  intro j
  rw [hfPQ, hfPQ']
  have hdelta : P' * Q - P * Q = (P' - P) * Q := by ring
  rw [hdelta, hWf]
  have hV := line_conv hℓ hdiffbound (suppVal_le_line (u := u) hℓ Q) j
  rw [hWQ, ← Nat.cast_add] at hV
  refine lt_of_lt_of_le ?_ hV
  refine Nat.cast_lt.2 ?_
  have hsumw : ∑ p ∈ L.attach, wfun p
      = ℓ * (∑ p ∈ L.attach, Hfun p) + u * (∑ p ∈ L.attach, mfun p) := by
    simp only [hwfun]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hd1 : ℓ * ((∑ p ∈ L.attach, Hfun p) + HQ)
      = ℓ * (∑ p ∈ L.attach, Hfun p) + ℓ * HQ := by ring
  have hd2 : u * ((∑ p ∈ L.attach, mfun p) + mQ)
      = u * (∑ p ∈ L.attach, mfun p) + u * mQ := by ring
  omega

set_option linter.unusedVariables false in
/-- **H.116b3 = H.116b3-iii (2/2) [NEW NODE: A-H.7; RE-SPLIT: A-H.8].** THE `¬ IsCSState`
TRANSPORT — swapping the child presentations of a planted product while keeping the cofactor
cannot create a composite-stage event. Statement BYTE-UNCHANGED from the leanspec stub.
Assembly: extract the CS witness at the planted lift of `c'` (`monicPoly_coeff_self` + `hc'`),
transport its side data across the swap — `u > 0` through `planted_delta_above_line` +
b3-ii's three congruences, `u = 0` (whence `ℓ = 1` by coprimality) through
`planted_side_transport_at_zero` — and land the witness at the planted lift of `c`, closing
with part 1's `isCSState_of_exists_lift` against `hcs`. -/
theorem not_isCSState_plantedPoly_swap {π : O}
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hπ : Irreducible π) {m N r : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (hdeg : (∑ p ∈ L, p.1) + r = m)
    (bb bb' : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) (c c' : ClusterState O m N)
    (hc : proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) = c.1)
    (hc' : proj O m N (fun i : Fin m => (plantedPoly π L bb' Qc).coeff (i : ℕ)) = c'.1)
    (h0 : ¬ IsDrainState c) (h0' : ¬ IsDrainState c') (hcs : ¬ IsCSState π c) :
    ¬ IsCSState π c' := by
  classical
  intro hcs'
  apply hcs
  have hm0 : 0 < m := by omega
  -- the two planted polynomials, their monicity, and the common degree m
  have hfm : (plantedPoly π L bb Qc).Monic := plantedPoly_monic π L bb Qc
  have hfm' : (plantedPoly π L bb' Qc).Monic := plantedPoly_monic π L bb' Qc
  have hfdeg : (plantedPoly π L bb Qc).natDegree = m := by
    rw [plantedPoly_natDegree]; exact hdeg
  have hfdeg' : (plantedPoly π L bb' Qc).natDegree = m := by
    rw [plantedPoly_natDegree]; exact hdeg
  have hdeg2 : (plantedPoly π L bb' Qc).natDegree = (plantedPoly π L bb Qc).natDegree := by
    rw [hfdeg, hfdeg']
  have hfa : monicPoly (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ))
      = plantedPoly π L bb Qc := monicPoly_coeff_self hfm hfdeg
  have hfa' : monicPoly (fun i : Fin m => (plantedPoly π L bb' Qc).coeff (i : ℕ))
      = plantedPoly π L bb' Qc := monicPoly_coeff_self hfm' hfdeg'
  -- extract the CS witness at the planted lift of c', and read it on f' itself
  obtain ⟨u, ℓ, hne'A, H₀, hℓ, hcop, hpin'A, ψ, hψirr, hψblk, hψdvdA⟩ := hcs'.2 _ hc'
  have hne'₀ : (sideSet X (plantedPoly π L bb' Qc) u ℓ).Nonempty := by
    rw [← hfa']; exact hne'A
  have hpin'₀ : npHgt X (plantedPoly π L bb' Qc)
      (sideMin X (plantedPoly π L bb' Qc) u ℓ hne'₀) = (H₀ : ℕ∞) := by
    have key : ∀ (h₁ : (sideSet X (plantedPoly π L bb' Qc) u ℓ).Nonempty),
        npHgt X (plantedPoly π L bb' Qc)
          (sideMin X (plantedPoly π L bb' Qc) u ℓ h₁) = (H₀ : ℕ∞) := by
      rw [← hfa']
      intro h₁
      exact hpin'A
    exact key hne'₀
  have hψdvd₀ : ψ ^ 2 ∣ resPoly π X (plantedPoly π L bb' Qc) u ℓ hne'₀ H₀ := by
    have key : ∀ (h₁ : (sideSet X (plantedPoly π L bb' Qc) u ℓ).Nonempty),
        ψ ^ 2 ∣ resPoly π X (plantedPoly π L bb' Qc) u ℓ h₁ H₀ := by
      rw [← hfa']
      intro h₁
      exact hψdvdA
    exact key hne'₀
  -- close through part 1's bridge at the planted lift of c
  refine isCSState_of_exists_lift hπ hm0 h0
    ⟨fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ), hc, ?_⟩
  rw [hfa]
  rcases Nat.eq_zero_or_pos u with hu0 | hu
  · -- the u = 0 branch: coprimality forces ℓ = 1, everything reads off f mod π
    subst hu0
    have hℓ1 : ℓ = 1 := Nat.coprime_zero_left ℓ |>.1 hcop
    subst hℓ1
    obtain ⟨hset0, hres0⟩ := planted_side_transport_at_zero (π := π) hπ hfm hfm' hdeg2
      (planted_map_residue_eq hπ L hLchild bb bb' Qc)
    -- the pinned height of the witness is 0
    have hH₀0 : H₀ = 0 := by
      have hOn' : OnSide X (plantedPoly π L bb' Qc) 0 1
          (sideMin X (plantedPoly π L bb' Qc) 0 1 hne'₀) :=
        onSide_of_mem_sideSet (Finset.min'_mem _ hne'₀)
      have heq : (1 : ℕ) • npHgt X (plantedPoly π L bb' Qc)
            (sideMin X (plantedPoly π L bb' Qc) 0 1 hne'₀)
          + ((0 * sideMin X (plantedPoly π L bb' Qc) 0 1 hne'₀ : ℕ) : ℕ∞)
            = suppVal X (plantedPoly π L bb' Qc) 0 1 := hOn'
      rw [suppVal_zero_one_of_monic hfm', one_nsmul, Nat.zero_mul, Nat.cast_zero,
        add_zero, hpin'₀] at heq
      exact_mod_cast heq
    subst hH₀0
    have hne : (sideSet X (plantedPoly π L bb Qc) 0 1).Nonempty := by
      rw [← hset0]; exact hne'₀
    refine ⟨0, 1, hne, 0, one_pos, Nat.coprime_zero_left 1 |>.2 rfl, ?_, ψ, hψirr, hψblk, ?_⟩
    · -- the pin on f at height 0
      have hOn : OnSide X (plantedPoly π L bb Qc) 0 1
          (sideMin X (plantedPoly π L bb Qc) 0 1 hne) :=
        onSide_of_mem_sideSet (Finset.min'_mem _ hne)
      have heq : (1 : ℕ) • npHgt X (plantedPoly π L bb Qc)
            (sideMin X (plantedPoly π L bb Qc) 0 1 hne)
          + ((0 * sideMin X (plantedPoly π L bb Qc) 0 1 hne : ℕ) : ℕ∞)
            = suppVal X (plantedPoly π L bb Qc) 0 1 := hOn
      rw [suppVal_zero_one_of_monic hfm, one_nsmul, Nat.zero_mul, Nat.cast_zero,
        add_zero] at heq
      rw [heq, Nat.cast_zero]
    · rw [← hres0 hne hne'₀]
      exact hψdvd₀
  · -- the u > 0 branch: the above-line transport (the beast + b3-ii)
    have habove : ∀ jj, suppVal X (plantedPoly π L bb Qc) u ℓ
        < ℓ • npHgt X (plantedPoly π L bb' Qc - plantedPoly π L bb Qc) jj
            + ((u * jj : ℕ) : ℕ∞) :=
      planted_delta_above_line hπ hN L hLchild bb bb' Qc hu hℓ hcop
    have habove' : ∀ jj, suppVal X (plantedPoly π L bb Qc) u ℓ
        ≤ ℓ • npHgt X (plantedPoly π L bb' Qc - plantedPoly π L bb Qc) jj
            + ((u * jj : ℕ) : ℕ∞) := fun jj => le_of_lt (habove jj)
    have hdX : 0 < (X : Polynomial O).natDegree := by simp [Polynomial.natDegree_X]
    have hset : sideSet X (plantedPoly π L bb' Qc) u ℓ
        = sideSet X (plantedPoly π L bb Qc) u ℓ :=
      sideSet_congr_of_above_line hπ Polynomial.monic_X hdX hℓ hdeg2 habove
    have hsupp : suppVal X (plantedPoly π L bb' Qc) u ℓ
        = suppVal X (plantedPoly π L bb Qc) u ℓ :=
      suppVal_congr_of_above_line hπ Polynomial.monic_X hdX hℓ hdeg2 habove
    have hne : (sideSet X (plantedPoly π L bb Qc) u ℓ).Nonempty := by
      rw [← hset]; exact hne'₀
    have hmin : sideMin X (plantedPoly π L bb' Qc) u ℓ hne'₀
        = sideMin X (plantedPoly π L bb Qc) u ℓ hne := by
      unfold sideMin
      have key : ∀ (h₁ : (sideSet X (plantedPoly π L bb' Qc) u ℓ).Nonempty)
          (h₂ : (sideSet X (plantedPoly π L bb Qc) u ℓ).Nonempty),
          (sideSet X (plantedPoly π L bb' Qc) u ℓ).min' h₁
            = (sideSet X (plantedPoly π L bb Qc) u ℓ).min' h₂ := by
        rw [hset]; intro h₁ h₂; rfl
      exact key hne'₀ hne
    -- the pin transports by cancellation along the equal support values
    have hpinf : npHgt X (plantedPoly π L bb Qc)
        (sideMin X (plantedPoly π L bb Qc) u ℓ hne) = (H₀ : ℕ∞) := by
      have hOn : OnSide X (plantedPoly π L bb Qc) u ℓ
          (sideMin X (plantedPoly π L bb Qc) u ℓ hne) :=
        onSide_of_mem_sideSet (Finset.min'_mem _ hne)
      have hOn' : OnSide X (plantedPoly π L bb' Qc) u ℓ
          (sideMin X (plantedPoly π L bb' Qc) u ℓ hne'₀) :=
        onSide_of_mem_sideSet (Finset.min'_mem _ hne'₀)
      have h₁ : ℓ • npHgt X (plantedPoly π L bb Qc)
            (sideMin X (plantedPoly π L bb Qc) u ℓ hne)
          + ((u * sideMin X (plantedPoly π L bb Qc) u ℓ hne : ℕ) : ℕ∞)
            = suppVal X (plantedPoly π L bb Qc) u ℓ := hOn
      have h₂ : ℓ • npHgt X (plantedPoly π L bb' Qc)
            (sideMin X (plantedPoly π L bb' Qc) u ℓ hne'₀)
          + ((u * sideMin X (plantedPoly π L bb' Qc) u ℓ hne'₀ : ℕ) : ℕ∞)
            = suppVal X (plantedPoly π L bb' Qc) u ℓ := hOn'
      rw [hmin, hsupp] at h₂
      have heq := h₁.trans h₂.symm
      have hfin : ((u * sideMin X (plantedPoly π L bb Qc) u ℓ hne : ℕ) : ℕ∞) ≠ ⊤ :=
        ENat.coe_ne_top _
      have hcancel := WithTop.add_right_cancel hfin heq
      have hkey := enat_smul_cancel' hℓ hcancel
      rw [hmin] at hpin'₀
      rw [hkey]
      exact hpin'₀
    -- the pinned height sits inside the support (finiteness for the resPoly transport)
    have htop : suppVal X (plantedPoly π L bb Qc) u ℓ ≠ ⊤ := by
      have := suppVal_eq_of_onSide hpinf
        (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
      rw [this]
      exact ENat.coe_ne_top _
    refine ⟨u, ℓ, hne, H₀, hℓ, hcop, hpinf, ψ, hψirr, hψblk, ?_⟩
    have hres := resPoly_congr_of_above_line hπ Polynomial.monic_X hdX hℓ hcop hdeg2
      habove hne htop hpinf
    rw [← hres]
    exact hψdvd₀

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Induction.not_isCSState_plantedPoly_swap
#print axioms Uniformity.Density.Induction.planted_map_residue_eq
end AxCheck
