/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG49

/-!
# Uniformity.ChapI.IFCG50 — [KDN 2026-08-30] `DiscNullAt n` DISCHARGED at every `n`;
`KrasnerAt n` reduced to its irreducible core

**Unit KDN.**  DTD's IFCG49 reduced the capstone's `a2` field to the two decoupled
residual Props `KrasnerAt n` (pointwise Krasner/OM completeness — field theory, no
counting) and `DiscNullAt n` (the discriminant-null cylinder proportion drains —
counting, no field theory).  THIS file:

* **PROVES `DiscNullAt n` for EVERY `n`, unconditionally** (`discNullAt`).  The engine
  is elementary and reuses DTD's König machinery twice:
  - *one variable* (§2): for a nonzero `g ∈ O[Y]`, if the level-`D` null cylinder
    `{y : g(y) ≡ 0 mod π^D}` never empties, the König point is an EXACT root `r ∈ O`;
    factoring `g = (Y − r)·h` and splitting ultrametrically
    (`s_{2t}(g) ≤ q^{−t} + s_t(h)`) drains by induction on the degree — no Newton
    polygons, no splitting fields, no extensions;
  - *many variables* (§3): induction on the number of coefficient coordinates via
    `MvPolynomial.finSuccEquiv`; if the null proportion of `F` does not drain, the
    classes with HEAVY fibers (fiber proportion ≥ half the limit) and a guarded
    nonvanishing leading coefficient form a truncation-closed, everywhere-nonempty
    family; its König point specialises `F` to a NONZERO one-variable polynomial whose
    null proportion cannot drain — contradicting §2.  Per-`O` Tendsto throughout: the
    compactness substitutes for the (false-in-general) uniform rate.
  - *the bridge* (§4): the generic discriminant resultant
    `genericDisc n ∈ MvPolynomial (Fin n) O` evaluates to `classDisc` at every level
    (resultant commutes with every ring map at pinned formal degrees), and is NONZERO
    because a product of `n` distinct monic linear factors (powers of a uniformizer —
    every DVR is infinite) is separable.
* **REDUCES `KrasnerAt n` to its irreducible core** (§5): the named residual
  `KrasnerIrredAt m` is the SAME Prop restricted to `monicPoly a` IRREDUCIBLE.  A
  general separable monic factors over the UFD `O[X]` into monic irreducibles
  (`TypeOf.monicFactorization_exists`); separability descends to the factors and gives
  the pairwise resultant nonvanishing over `Frac O`; the landed IFCG42 transfer
  `decidedAt_mulClass_of_not_dvd_resultant` recombines the factor decisions at the
  exact resultant depth.  `KrasnerIrredAt` is proved at `m = 0, 1` (nonvacuity).
* **FIRES the capstone feeds** (§6):

      ★★★ `discNullAt : ∀ n, DiscNullAt n`                          -- UNCONDITIONAL
      ★★★ `deepTailDrainAt_of_krasner : KrasnerAt n → DeepTailDrainAt n`
      ★★★ `drainageAt_all_of_krasner :
             (∀ m, 4 ≤ m → KrasnerAt m) → ∀ n, DrainageAt n`
      ★★★ `drainageAt_all_of_krasnerIrred :
             (∀ m, KrasnerIrredAt m) → ∀ n, DrainageAt n`

  The capstone's ENTIRE `a2` field now rests on the single classical residual
  `KrasnerIrredAt m` (`m ≥ 4`): *an irreducible separable monic over a complete DVR is
  eventually decided* — quantitative Krasner in its weakest pointwise ∃-form.

## Honesty

`KrasnerAt`, `DiscNullAt`, `DeepTailDrainAt`, `DrainageAt`, `DecidedAt` are consumed
byte-unchanged from IFCG49/IFCG46/the corpus; nothing is weakened.  `KrasnerIrredAt`
strengthens the hypothesis of `KrasnerAt` by `Irreducible (monicPoly a)` and is
otherwise byte-parallel (∀-`O`, `O : Type`, the corpus's universe convention).  The
drains are per-`O` Tendsto, exactly as consumed; no uniform rate in `q` is claimed.
Axioms: Lean core only.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.IFCG50

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG49

/-! ## §0 Toolkit: DVR valuation splitting, the box-proportion calculus, limit helpers -/

section Toolkit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

theorem mem_maximalIdeal_pow_iff_dvd {π : O} (hπ : Irreducible π) (k : ℕ) (x : O) :
    x ∈ (maximalIdeal O) ^ k ↔ π ^ k ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem pow_dvd_unit_mul_pow_iff {π : O} (hπ : Irreducible π) (u : Oˣ) (k s : ℕ) :
    π ^ k ∣ (u : O) * π ^ s ↔ k ≤ s := by
  constructor
  · intro hdvd
    by_contra hks
    have hks' : s < k := by omega
    obtain ⟨c, hc⟩ := hdvd
    have hs : s + (k - s) = k := by omega
    have h1 : π ^ s * (u : O) = π ^ s * (π ^ (k - s) * c) := by
      calc π ^ s * (u : O) = (u : O) * π ^ s := mul_comm _ _
        _ = π ^ k * c := hc
        _ = π ^ s * (π ^ (k - s) * c) := by rw [← mul_assoc, ← pow_add, hs]
    have h2 : (u : O) = π ^ (k - s) * c := mul_left_cancel₀ (pow_ne_zero s hπ.ne_zero) h1
    have h3 : π ∣ (u : O) := (dvd_pow_self π (by omega : k - s ≠ 0)).trans ⟨c, h2⟩
    exact hπ.not_isUnit (isUnit_of_dvd_unit h3 u.isUnit)
  · intro hks
    exact Dvd.dvd.mul_left (pow_dvd_pow π hks) _

/-- **The ultrametric split**: if `a * b` vanishes to order `D` but `a` does not vanish
to order `t`, then `b` vanishes to order `D − t`. -/
theorem mem_pow_sub_of_mul_mem {D t : ℕ} {a b : O}
    (hab : a * b ∈ (maximalIdeal O) ^ D) (ha : a ∉ (maximalIdeal O) ^ t) :
    b ∈ (maximalIdeal O) ^ (D - t) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [mem_maximalIdeal_pow_iff_dvd hπ] at hab ha ⊢
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero _)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact dvd_zero _
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  obtain ⟨r, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hprod : ((u : O) * π ^ s) * ((v : O) * π ^ r) = ((u * v : Oˣ) : O) * π ^ (s + r) := by
    rw [Units.val_mul, pow_add]; ring
  rw [hprod, pow_dvd_unit_mul_pow_iff hπ] at hab
  rw [pow_dvd_unit_mul_pow_iff hπ] at ha ⊢
  omega

theorem exists_notMem_maximalIdeal_pow [IsAdicComplete (maximalIdeal O) O] {r : O}
    (hr : r ≠ 0) : ∃ k, r ∉ (maximalIdeal O) ^ k := by
  by_contra hall
  refine hr (IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal O) O) r fun n => ?_)
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.zero]
  by_contra hn
  exact hall ⟨n, hn⟩

variable (O) in
/-- The proportion of a level-`D` class set inside the degree-`n` coefficient box. -/
noncomputable def boxProp (n D : ℕ) (S : Set (Coeff O n D)) : ℝ :=
  (Nat.card S : ℝ) / (residueCard O : ℝ) ^ (n * D)

theorem boxProp_nonneg (n D : ℕ) (S : Set (Coeff O n D)) : 0 ≤ boxProp O n D S :=
  div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le

theorem boxProp_mono {n D : ℕ} {S T : Set (Coeff O n D)} (h : S ⊆ T) :
    boxProp O n D S ≤ boxProp O n D T :=
  div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.card_le_card_of_injective (Set.inclusion h) (Set.inclusion_injective _))
    (qpow_pos _).le

theorem boxProp_le_one (n D : ℕ) (S : Set (Coeff O n D)) : boxProp O n D S ≤ 1 := by
  rw [boxProp, div_le_one (qpow_pos _)]
  exact_mod_cast (card_coeff (O := O) n D) ▸
    Nat.card_le_card_of_injective (Subtype.val (p := (· ∈ S))) Subtype.val_injective

theorem boxProp_union_le {n D : ℕ} (S T : Set (Coeff O n D)) :
    boxProp O n D (S ∪ T) ≤ boxProp O n D S + boxProp O n D T := by
  rw [boxProp, boxProp, boxProp, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (qpow_pos _).le
  have h1 : (S ∪ T).ncard ≤ S.ncard + T.ncard := Set.ncard_union_le S T
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact_mod_cast h1

/-- The preimage law: a level-`M` cylinder condition has the same proportion at every
level `D ≥ M` (IFCG46 §0's exact fiber count, normalized). -/
theorem boxProp_preimage_eq {n M D : ℕ} (h : M ≤ D) (S : Set (Coeff O n M)) :
    boxProp O n D ((coeffFactor (O := O) n h) ⁻¹' S) = boxProp O n M S := by
  rw [boxProp, boxProp, IFCG46.card_preimage_coeffFactor_eq n h S]
  have hexp : n * (D - M) + n * M = n * D := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  rw [div_eq_div_iff (qpow_pos _).ne' (qpow_pos _).ne']
  push_cast
  rw [← hexp, pow_add]
  ring

/-- The antitone workhorse: if the level-`D` set lies inside the cylinder over a
level-`M` set, its proportion is dominated by the level-`M` proportion. -/
theorem boxProp_le_of_subset_preimage {n M D : ℕ} (h : M ≤ D) {S : Set (Coeff O n D)}
    {T : Set (Coeff O n M)} (hsub : S ⊆ (coeffFactor (O := O) n h) ⁻¹' T) :
    boxProp O n D S ≤ boxProp O n M T :=
  (boxProp_mono hsub).trans (boxProp_preimage_eq h T).le

theorem proj_cons {k D : ℕ} (b : O) (a : Fin k → O) :
    proj O (k + 1) D (Fin.cons b a)
      = Fin.cons (Ideal.Quotient.mk ((maximalIdeal O) ^ D) b) (proj O k D a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

end Toolkit

section RealSeq

/-- Antitone nonnegative with a null subsequence bound ⟹ tendsto `0`. -/
theorem tendsto_zero_of_antitone_of_subseq {f : ℕ → ℝ} (hanti : Antitone f)
    (h0 : ∀ D, 0 ≤ f D) {u : ℕ → ℕ} {g : ℕ → ℝ} (hle : ∀ t, f (u t) ≤ g t)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro x ⟨D, rfl⟩; exact h0 D⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hL0 : (⨅ D, f D) = 0 := by
    have h1 : ∀ t, (⨅ D, f D) ≤ g t := fun t => (ciInf_le hbdd (u t)).trans (hle t)
    have h2 : (⨅ D, f D) ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hg h1
    have h3 : 0 ≤ (⨅ D, f D) := le_ciInf h0
    linarith
  rwa [hL0] at hlim

/-- Antitone nonnegative not tending to `0` ⟹ a uniform positive floor. -/
theorem exists_pos_forall_le_of_not_tendsto {f : ℕ → ℝ} (hanti : Antitone f)
    (h0 : ∀ D, 0 ≤ f D) (hnot : ¬ Tendsto f atTop (𝓝 0)) :
    ∃ ε > 0, ∀ D, ε ≤ f D := by
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro x ⟨D, rfl⟩; exact h0 D⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ D, f D, ?_, fun D => ciInf_le hbdd D⟩
  rcases lt_or_eq_of_le (le_ciInf h0) with h | h
  · exact h
  · exact absurd (h ▸ hlim) hnot

/-- `q^{−t} → 0` for `1 < q`. -/
theorem tendsto_inv_qpow_zero {q : ℝ} (hq : 1 < q) :
    Tendsto (fun t : ℕ => 1 / q ^ t) atTop (𝓝 0) := by
  have h1 : (0 : ℝ) ≤ 1 / q := by positivity
  have h2 : 1 / q < 1 := by
    rw [div_lt_one (lt_trans one_pos hq)]; exact hq
  have := tendsto_pow_atTop_nhds_zero_of_lt_one h1 h2
  refine this.congr fun t => ?_
  rw [div_pow, one_pow]

end RealSeq

/-! ## §1 The one-variable drain

For a nonzero `g ∈ O[Y]`: if the level-`D` null cylinders `{y : g(y) ≡ 0 mod π^D}`
never empty, DTD's König engine produces a single integral point that is null at EVERY
level — an EXACT root `r ∈ O` (adic Hausdorffness).  Factoring `g = (Y − r)·h` and
splitting each null class ultrametrically (either `y ≡ r mod π^t`, or `h(y) ≡ 0
mod π^{D−t}`) gives `s_{2t}(g) ≤ q^{−t} + s_t(h)`, and the proportion drains by
induction on the degree.  No Newton polygons, no field extensions. -/

section OneVar

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

variable (O) in
/-- The level-`D` null cylinder of `g ∈ O[Y]`, on the 1-dimensional box. -/
def oneNullSet (g : Polynomial O) (D : ℕ) : Set (Coeff O 1 D) :=
  {y | Polynomial.eval (y 0) (g.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D))) = 0}

variable (O) in
/-- The level-`D` null proportion of `g`. -/
noncomputable def oneNullProp (g : Polynomial O) (D : ℕ) : ℝ :=
  boxProp O 1 D (oneNullSet O g D)

theorem mem_oneNullSet_proj {g : Polynomial O} {D : ℕ} (b : Fin 1 → O) :
    proj O 1 D b ∈ oneNullSet O g D ↔ g.eval (b 0) ∈ (maximalIdeal O) ^ D := by
  have h1 : Polynomial.eval ((proj O 1 D b) 0) (g.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D)))
      = Ideal.Quotient.mk ((maximalIdeal O) ^ D) (g.eval (b 0)) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply _ _
  rw [oneNullSet, Set.mem_setOf_eq, h1, Ideal.Quotient.eq_zero_iff_mem]

theorem truncClosed_oneNullSet (g : Polynomial O) : TruncClosed (oneNullSet O g) := by
  intro N M h y hy
  obtain ⟨b, rfl⟩ := proj_surjective O 1 M y
  have h1 : coeffFactor (O := O) 1 h (proj O 1 M b) = proj O 1 N b := rfl
  rw [h1, mem_oneNullSet_proj]
  rw [mem_oneNullSet_proj] at hy
  exact Ideal.pow_le_pow_right h hy

theorem antitone_oneNullProp (g : Polynomial O) : Antitone (oneNullProp O g) := by
  intro N M h
  exact boxProp_le_of_subset_preimage h (fun y hy => truncClosed_oneNullSet g h y hy)

theorem oneNullProp_nonneg (g : Polynomial O) (D : ℕ) : 0 ≤ oneNullProp O g D :=
  boxProp_nonneg _ _ _

/-- If some level empties, the proportion is eventually `0`. -/
theorem tendsto_oneNullProp_zero_of_empty {g : Polynomial O} {D₀ : ℕ}
    (hemp : oneNullSet O g D₀ = ∅) : Tendsto (oneNullProp O g) atTop (𝓝 0) := by
  have hzero : ∀ D, D₀ ≤ D → oneNullProp O g D = 0 := by
    intro D hD
    have hDemp : oneNullSet O g D = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have h2 := truncClosed_oneNullSet g hD y hy
      rw [hemp] at h2
      exact h2
    rw [oneNullProp, boxProp, hDemp]
    simp
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop D₀] with D hD
  exact (hzero D hD).symm

/-- ★ **THE KÖNIG ROOT** — if the null cylinders of `g` never empty, `g` has an exact
root in `O` (the engine point is null at every level; Hausdorffness finishes). -/
theorem exists_root_of_forall_oneNull_nonempty [IsAdicComplete (maximalIdeal O) O]
    {g : Polynomial O} (hall : ∀ D, (oneNullSet O g D).Nonempty) :
    ∃ r : O, g.eval r = 0 := by
  obtain ⟨b, hb⟩ := exists_point_of_truncClosed (truncClosed_oneNullSet g) hall
  refine ⟨b 0, ?_⟩
  by_contra hne
  obtain ⟨k, hk⟩ := exists_notMem_maximalIdeal_pow hne
  exact hk ((mem_oneNullSet_proj b).mp (hb k))

/-- The ultrametric split: a level-`D` null class of `g = (Y − r)·h` either agrees with
`r` to level `t`, or is a level-`(D − t)` null class of `h`. -/
theorem oneNullSet_subset_split {g h : Polynomial O} {r : O}
    (hgh : g = (X - C r) * h) {t D : ℕ} (ht : t ≤ D) :
    oneNullSet O g D ⊆
      ((coeffFactor (O := O) 1 ht) ⁻¹' {proj O 1 t (fun _ => r)}) ∪
      ((coeffFactor (O := O) 1 (Nat.sub_le D t)) ⁻¹' (oneNullSet O h (D - t))) := by
  intro y hy
  obtain ⟨b, rfl⟩ := proj_surjective O 1 D y
  rw [mem_oneNullSet_proj] at hy
  by_cases hball : b 0 - r ∈ (maximalIdeal O) ^ t
  · left
    have h1 : coeffFactor (O := O) 1 ht (proj O 1 D b) = proj O 1 t b := rfl
    rw [Set.mem_preimage, h1, Set.mem_singleton_iff]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hball
  · right
    have h1 : coeffFactor (O := O) 1 (Nat.sub_le D t) (proj O 1 D b) = proj O 1 (D - t) b := rfl
    rw [Set.mem_preimage, h1, mem_oneNullSet_proj]
    have heval : g.eval (b 0) = (b 0 - r) * h.eval (b 0) := by
      rw [hgh, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [heval] at hy
    exact mem_pow_sub_of_mul_mem hy hball

/-- The split, counted: `s_D(g) ≤ q^{−t} + s_{D−t}(h)`. -/
theorem oneNullProp_le_split {g h : Polynomial O} {r : O} (hgh : g = (X - C r) * h)
    {t D : ℕ} (ht : t ≤ D) :
    oneNullProp O g D ≤ 1 / (residueCard O : ℝ) ^ t + oneNullProp O h (D - t) := by
  calc oneNullProp O g D
      ≤ boxProp O 1 D (((coeffFactor (O := O) 1 ht) ⁻¹' {proj O 1 t (fun _ => r)}) ∪
          ((coeffFactor (O := O) 1 (Nat.sub_le D t)) ⁻¹' (oneNullSet O h (D - t)))) :=
        boxProp_mono (oneNullSet_subset_split hgh ht)
    _ ≤ boxProp O 1 D ((coeffFactor (O := O) 1 ht) ⁻¹' {proj O 1 t (fun _ => r)})
        + boxProp O 1 D ((coeffFactor (O := O) 1 (Nat.sub_le D t)) ⁻¹'
            (oneNullSet O h (D - t))) := boxProp_union_le _ _
    _ = boxProp O 1 t {proj O 1 t (fun _ => r)} + oneNullProp O h (D - t) := by
        rw [boxProp_preimage_eq, boxProp_preimage_eq]; rfl
    _ = 1 / (residueCard O : ℝ) ^ t + oneNullProp O h (D - t) := by
        congr 1
        rw [boxProp, Nat.card_unique, Nat.cast_one, one_mul]

/-- ★★ **THE ONE-VARIABLE DRAIN**, degree-bounded form. -/
theorem tendsto_oneNullProp_zero_aux [IsAdicComplete (maximalIdeal O) O] :
    ∀ (d : ℕ) (g : Polynomial O), g ≠ 0 → g.natDegree ≤ d →
      Tendsto (oneNullProp O g) atTop (𝓝 0) := by
  intro d
  induction d with
  | zero =>
    intro g hg hd
    by_cases hall : ∀ D, (oneNullSet O g D).Nonempty
    · exfalso
      obtain ⟨r, hroot⟩ := exists_root_of_forall_oneNull_nonempty hall
      have hg0 : g = C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hd)
      rw [hg0, Polynomial.eval_C] at hroot
      exact hg (by rw [hg0, hroot, map_zero])
    · obtain ⟨D₀, hD₀⟩ := not_forall.mp hall
      exact tendsto_oneNullProp_zero_of_empty (Set.not_nonempty_iff_eq_empty.mp hD₀)
  | succ d IH =>
    intro g hg hd
    by_cases hall : ∀ D, (oneNullSet O g D).Nonempty
    · obtain ⟨r, hroot⟩ := exists_root_of_forall_oneNull_nonempty hall
      obtain ⟨h, hgh⟩ := (Polynomial.dvd_iff_isRoot.mpr hroot : (X - C r) ∣ g)
      have hh0 : h ≠ 0 := fun h0 => hg (by rw [hgh, h0, mul_zero])
      have hdeg : g.natDegree = 1 + h.natDegree := by
        rw [hgh, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hh0,
          Polynomial.natDegree_X_sub_C]
      have hIH := IH h hh0 (by omega)
      have hsplit : ∀ t : ℕ, oneNullProp O g (t + t)
          ≤ 1 / (residueCard O : ℝ) ^ t + oneNullProp O h t := by
        intro t
        have h2 := oneNullProp_le_split (O := O) hgh (Nat.le_add_right t t)
        rwa [Nat.add_sub_cancel] at h2
      refine tendsto_zero_of_antitone_of_subseq (antitone_oneNullProp g)
        (oneNullProp_nonneg g) (u := fun t => t + t) hsplit ?_
      have h1 : Tendsto (fun t : ℕ => 1 / (residueCard O : ℝ) ^ t) atTop (𝓝 0) :=
        tendsto_inv_qpow_zero (by exact_mod_cast one_lt_residueCard O)
      simpa using h1.add hIH
    · obtain ⟨D₀, hD₀⟩ := not_forall.mp hall
      exact tendsto_oneNullProp_zero_of_empty (Set.not_nonempty_iff_eq_empty.mp hD₀)

/-- ★★ **THE ONE-VARIABLE DRAIN** — the null proportion of any NONZERO one-variable
polynomial over `O` tends to `0`. -/
theorem tendsto_oneNullProp_zero [IsAdicComplete (maximalIdeal O) O] {g : Polynomial O}
    (hg : g ≠ 0) : Tendsto (oneNullProp O g) atTop (𝓝 0) :=
  tendsto_oneNullProp_zero_aux g.natDegree g hg le_rfl

end OneVar

/-! ## §2 The multivariable drain

Induction on the number of coefficient coordinates.  The level-`D` null set of
`F ∈ O[x₁,…,x_{k+1}]` fibers over the tail coordinates; if the null proportion does not
drain, the classes with HEAVY fibers (fiber proportion ≥ half the infimum) and a
guarded nonvanishing leading coefficient (level `D₀`, chosen by the induction
hypothesis) form a truncation-closed, everywhere-nonempty family.  Its König point
specialises `F` to a NONZERO one-variable polynomial with non-draining null proportion
— contradicting §1.  The compactness substitutes for the (unavailable) uniform rate in
the fiberwise limits. -/

section MultiVar

/-- `finSuccEquiv` commutes with coefficient ring maps. -/
theorem finSuccEquiv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (F : MvPolynomial (Fin (k + 1)) R) :
    MvPolynomial.finSuccEquiv S k (MvPolynomial.map φ F)
      = Polynomial.map (MvPolynomial.map φ) (MvPolynomial.finSuccEquiv R k F) := by
  have h : ((MvPolynomial.finSuccEquiv S k).toAlgHom.toRingHom).comp (MvPolynomial.map φ)
      = (Polynomial.mapRingHom (MvPolynomial.map φ)).comp
          ((MvPolynomial.finSuccEquiv R k).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_mapRingHom, MvPolynomial.map_C, Polynomial.map_C]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [MvPolynomial.map_X, MvPolynomial.finSuccEquiv_X_zero,
          Polynomial.coe_mapRingHom, Polynomial.map_X]
      · simp [MvPolynomial.map_X, MvPolynomial.finSuccEquiv_X_succ,
          Polynomial.coe_mapRingHom, Polynomial.map_C]
  exact RingHom.congr_fun h F

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Family-level: truncation-closed families have antitone proportions. -/
theorem antitone_boxProp_of_truncClosed {n : ℕ} {S : ∀ N, Set (Coeff O n N)}
    (hcl : TruncClosed S) : Antitone (fun D => boxProp O n D (S D)) := by
  intro N M h
  exact boxProp_le_of_subset_preimage h (fun c hc => hcl h c hc)

/-- Family-level: a truncation-closed family that empties at some level has proportion
eventually `0`. -/
theorem tendsto_boxProp_zero_of_empty {n : ℕ} {S : ∀ N, Set (Coeff O n N)}
    (hcl : TruncClosed S) {D₀ : ℕ} (hemp : S D₀ = ∅) :
    Tendsto (fun D => boxProp O n D (S D)) atTop (𝓝 0) := by
  have hzero : ∀ D, D₀ ≤ D → boxProp O n D (S D) = 0 := by
    intro D hD
    have hDemp : S D = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro c hc
      have h2 := hcl hD c hc
      rw [hemp] at h2
      exact h2
    rw [boxProp, hDemp]
    simp
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop D₀] with D hD
  exact (hzero D hD).symm

variable (O) in
/-- The level-`D` null cylinder of `F ∈ O[x₁,…,x_k]` on the `k`-dimensional box. -/
def mvNullSet {k : ℕ} (F : MvPolynomial (Fin k) O) (D : ℕ) : Set (Coeff O k D) :=
  {c | MvPolynomial.eval c
    (MvPolynomial.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D)) F) = 0}

variable (O) in
/-- The level-`D` null proportion of `F`. -/
noncomputable def mvNullProp {k : ℕ} (F : MvPolynomial (Fin k) O) (D : ℕ) : ℝ :=
  boxProp O k D (mvNullSet O F D)

/-- Evaluation at a projected point factors through the quotient (ring-hom form). -/
theorem eval_proj_comp_map_mk {k : ℕ} (a : Fin k → O) (D : ℕ) :
    (MvPolynomial.eval (proj O k D a)).comp
        (MvPolynomial.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D)))
      = (Ideal.Quotient.mk ((maximalIdeal O) ^ D)).comp
          (MvPolynomial.eval a : MvPolynomial (Fin k) O →+* O) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp [proj]

theorem mem_mvNullSet_proj {k : ℕ} {F : MvPolynomial (Fin k) O} {D : ℕ} (a : Fin k → O) :
    proj O k D a ∈ mvNullSet O F D ↔ MvPolynomial.eval a F ∈ (maximalIdeal O) ^ D := by
  have h1 : MvPolynomial.eval (proj O k D a)
      (MvPolynomial.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D)) F)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ D) (MvPolynomial.eval a F) :=
    RingHom.congr_fun (eval_proj_comp_map_mk a D) F
  rw [mvNullSet, Set.mem_setOf_eq, h1, Ideal.Quotient.eq_zero_iff_mem]

theorem truncClosed_mvNullSet {k : ℕ} (F : MvPolynomial (Fin k) O) :
    TruncClosed (mvNullSet O F) := by
  intro N M h c hc
  obtain ⟨a, rfl⟩ := proj_surjective O k M c
  have h1 : coeffFactor (O := O) k h (proj O k M a) = proj O k N a := rfl
  rw [h1, mem_mvNullSet_proj]
  rw [mem_mvNullSet_proj] at hc
  exact Ideal.pow_le_pow_right h hc

theorem antitone_mvNullProp {k : ℕ} (F : MvPolynomial (Fin k) O) :
    Antitone (mvNullProp O F) :=
  antitone_boxProp_of_truncClosed (truncClosed_mvNullSet F)

variable (O) in
/-- The `y`-fiber of the null set of `F ∈ O[x₀,…,x_k]` over the tail class `c`. -/
def fiberSet {k : ℕ} (F : MvPolynomial (Fin (k + 1)) O) (D : ℕ) (c : Coeff O k D) :
    Set (Coeff O 1 D) :=
  {y | Fin.cons (y 0) c ∈ mvNullSet O F D}

variable (O) in
/-- The fiber proportion. -/
noncomputable def fiberProp {k : ℕ} (F : MvPolynomial (Fin (k + 1)) O) (D : ℕ)
    (c : Coeff O k D) : ℝ :=
  boxProp O 1 D (fiberSet O F D c)

/-- ★ The fiber over a KÖNIG POINT is the null cylinder of the one-variable
specialisation. -/
theorem fiberSet_proj_eq_oneNullSet {k : ℕ} (F : MvPolynomial (Fin (k + 1)) O) (D : ℕ)
    (a : Fin k → O) :
    fiberSet O F D (proj O k D a)
      = oneNullSet O
          (Polynomial.map (MvPolynomial.eval a) (MvPolynomial.finSuccEquiv O k F)) D := by
  ext y
  rw [fiberSet, Set.mem_setOf_eq, mvNullSet, Set.mem_setOf_eq, oneNullSet, Set.mem_setOf_eq]
  rw [MvPolynomial.eval_eq_eval_mv_eval', finSuccEquiv_map, Polynomial.map_map,
    eval_proj_comp_map_mk, ← Polynomial.map_map]

/-- Fiber proportions grow under truncation (the fiber is a cylinder refinement). -/
theorem fiberProp_le_trunc {k : ℕ} {F : MvPolynomial (Fin (k + 1)) O} {N M : ℕ}
    (h : N ≤ M) (c : Coeff O k M) :
    fiberProp O F M c ≤ fiberProp O F N (coeffFactor (O := O) k h c) := by
  obtain ⟨a, rfl⟩ := proj_surjective O k M c
  have hcf : coeffFactor (O := O) k h (proj O k M a) = proj O k N a := rfl
  rw [hcf, fiberProp, fiberProp]
  refine boxProp_le_of_subset_preimage h ?_
  intro y hy
  obtain ⟨b, rfl⟩ := proj_surjective O 1 M y
  rw [fiberSet, Set.mem_setOf_eq] at hy
  have h1 : Fin.cons ((proj O 1 M b) 0) (proj O k M a)
      = proj O (k + 1) M (Fin.cons (b 0) a) := (proj_cons (b 0) a).symm
  rw [h1] at hy
  have h2 := truncClosed_mvNullSet F h _ hy
  have h3 : coeffFactor (O := O) (k + 1) h (proj O (k + 1) M (Fin.cons (b 0) a))
      = proj O (k + 1) N (Fin.cons (b 0) a) := rfl
  rw [h3] at h2
  show coeffFactor (O := O) 1 h (proj O 1 M b) ∈ fiberSet O F N (proj O k N a)
  have h4 : coeffFactor (O := O) 1 h (proj O 1 M b) = proj O 1 N b := rfl
  rw [h4, fiberSet, Set.mem_setOf_eq]
  have h5 : Fin.cons ((proj O 1 N b) 0) (proj O k N a)
      = proj O (k + 1) N (Fin.cons (b 0) a) := (proj_cons (b 0) a).symm
  rw [h5]
  exact h2

/-- The abstract slice equivalence: on any box set `S`, the slice over a fixed tail
class `c` is equivalent to any set `T` carved out by the `Fin.cons`-membership. -/
def sliceEquivOfMem {k D : ℕ} (S : Set (Coeff O (k + 1) D)) (T : Set (Coeff O 1 D))
    (c : Coeff O k D) (hmem : ∀ y : Coeff O 1 D, y ∈ T ↔ Fin.cons (y 0) c ∈ S) :
    {x : ↥S // Fin.tail x.1 = c} ≃ ↥T where
  toFun x := ⟨fun _ => x.1.1 0, by
    obtain ⟨⟨z, hzS⟩, hzc⟩ := x
    rw [hmem]
    show Fin.cons (z 0) c ∈ S
    rw [← hzc, Fin.cons_self_tail]
    exact hzS⟩
  invFun y := ⟨⟨Fin.cons (y.1 0) c, (hmem y.1).mp y.2⟩, Fin.tail_cons _ _⟩
  left_inv x := by
    obtain ⟨⟨z, hzS⟩, hzc⟩ := x
    apply Subtype.ext
    apply Subtype.ext
    show Fin.cons (z 0) c = z
    rw [← hzc, Fin.cons_self_tail]
  right_inv y := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show (Fin.cons (y.1 0) c : Fin (k + 1) → Res O D) 0 = y.1 0
    rw [Fin.cons_zero]

/-- The level-`D` null count fibers over the tail classes. -/
theorem card_mvNullSet_eq_sum {k : ℕ} (F : MvPolynomial (Fin (k + 1)) O) (D : ℕ)
    [Fintype (Coeff O k D)] :
    Nat.card (mvNullSet O F D) = ∑ c : Coeff O k D, Nat.card (fiberSet O F D c) := by
  have h1 : Nat.card (mvNullSet O F D)
      = Nat.card ((c : Coeff O k D) × {x : ↥(mvNullSet O F D) // Fin.tail x.1 = c}) :=
    Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : ↥(mvNullSet O F D) => Fin.tail x.1)).symm
  rw [h1, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun c _ => Nat.card_congr
    (sliceEquivOfMem (mvNullSet O F D) (fiberSet O F D c) c (fun _ => Iff.rfl)))

/-- ★★ **THE HEAVY-FIBER SURVIVOR** (the counting core): if the null proportion of `F`
never drops below `ε` while the level-`D₀` null proportion of `G` is below `ε/2`, then
at every level `D ≥ D₀` some tail class has fiber proportion ≥ `ε/2` AND escapes the
level-`D₀` null cylinder of `G`. -/
theorem exists_heavy_survivor {k : ℕ} {F : MvPolynomial (Fin (k + 1)) O}
    {G : MvPolynomial (Fin k) O} {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ D, ε ≤ mvNullProp O F D) {D₀ : ℕ} (hD₀ : mvNullProp O G D₀ < ε / 2)
    {D : ℕ} (hD : D₀ ≤ D) :
    ∃ c : Coeff O k D, ε / 2 ≤ fiberProp O F D c
      ∧ coeffFactor (O := O) k hD c ∉ mvNullSet O G D₀ := by
  classical
  letI : Fintype (Coeff O k D) := Fintype.ofFinite _
  have hq1 : (1 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast one_lt_residueCard O
  set q : ℝ := (residueCard O : ℝ) with hq
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
  have hsum : (Nat.card (mvNullSet O F D) : ℝ)
      = ∑ c : Coeff O k D, (Nat.card (fiberSet O F D c) : ℝ) := by
    rw [card_mvNullSet_eq_sum F D]
    push_cast
    rfl
  have hfiber_le : ∀ c : Coeff O k D, (Nat.card (fiberSet O F D c) : ℝ) ≤ q ^ D := by
    intro c
    have h1 := boxProp_le_one (O := O) 1 D (fiberSet O F D c)
    rw [boxProp, div_le_one (qpow_pos _)] at h1
    calc (Nat.card (fiberSet O F D c) : ℝ) ≤ (residueCard O : ℝ) ^ (1 * D) := h1
      _ = q ^ D := by rw [one_mul]
  set H : Finset (Coeff O k D) := Finset.univ.filter (fun c => ε / 2 ≤ fiberProp O F D c)
    with hH
  have hcardH : ε / 2 * q ^ (k * D) ≤ (H.card : ℝ) := by
    have hlow : ε * q ^ ((k + 1) * D) ≤ (Nat.card (mvNullSet O F D) : ℝ) := by
      have h1 := hε D
      rw [mvNullProp, boxProp, le_div_iff₀ (qpow_pos _)] at h1
      exact h1
    have hsplit : (Nat.card (mvNullSet O F D) : ℝ)
        ≤ (H.card : ℝ) * q ^ D + q ^ (k * D) * (ε / 2 * q ^ D) := by
      rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun c => ε / 2 ≤ fiberProp O F D c) (fun c => (Nat.card (fiberSet O F D c) : ℝ))]
      refine add_le_add ?_ ?_
      · calc ∑ c ∈ H, (Nat.card (fiberSet O F D c) : ℝ)
            ≤ ∑ _c ∈ H, q ^ D := Finset.sum_le_sum (fun c _ => hfiber_le c)
          _ = (H.card : ℝ) * q ^ D := by rw [Finset.sum_const, nsmul_eq_mul]
      · have hlight : ∀ c ∈ Finset.univ.filter (fun c => ¬ (ε / 2 ≤ fiberProp O F D c)),
            (Nat.card (fiberSet O F D c) : ℝ) ≤ ε / 2 * q ^ D := by
          intro c hc
          rw [Finset.mem_filter] at hc
          have h1 : fiberProp O F D c < ε / 2 := not_le.mp hc.2
          rw [fiberProp, boxProp, div_lt_iff₀ (qpow_pos _)] at h1
          calc (Nat.card (fiberSet O F D c) : ℝ)
              ≤ ε / 2 * (residueCard O : ℝ) ^ (1 * D) := h1.le
            _ = ε / 2 * q ^ D := by rw [one_mul]
        calc ∑ c ∈ Finset.univ.filter (fun c => ¬ (ε / 2 ≤ fiberProp O F D c)),
              (Nat.card (fiberSet O F D c) : ℝ)
            ≤ ∑ _c ∈ Finset.univ.filter (fun c => ¬ (ε / 2 ≤ fiberProp O F D c)),
              (ε / 2 * q ^ D) := Finset.sum_le_sum hlight
          _ = ((Finset.univ.filter (fun c => ¬ (ε / 2 ≤ fiberProp O F D c))).card : ℝ)
              * (ε / 2 * q ^ D) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ q ^ (k * D) * (ε / 2 * q ^ D) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have h2 : (Finset.univ.filter
                  (fun c => ¬ (ε / 2 ≤ fiberProp O F D c))).card
                  ≤ Fintype.card (Coeff O k D) :=
                (Finset.card_filter_le _ _).trans Finset.card_univ.le
              have h3 : Fintype.card (Coeff O k D) = residueCard O ^ (k * D) := by
                rw [← Nat.card_eq_fintype_card, card_coeff]
              calc ((Finset.univ.filter
                    (fun c => ¬ (ε / 2 ≤ fiberProp O F D c))).card : ℝ)
                  ≤ (Fintype.card (Coeff O k D) : ℝ) := by exact_mod_cast h2
                _ = q ^ (k * D) := by rw [h3, hq]; push_cast; rfl
    have hexp : q ^ ((k + 1) * D) = q ^ (k * D) * q ^ D := by
      rw [← pow_add]
      congr 1
      ring
    have h4 : ε * (q ^ (k * D) * q ^ D)
        ≤ (H.card : ℝ) * q ^ D + q ^ (k * D) * (ε / 2 * q ^ D) := by
      rw [← hexp]
      exact hlow.trans hsplit
    have hqD : (0 : ℝ) < q ^ D := pow_pos hq0 D
    have h5 : ε / 2 * q ^ (k * D) * q ^ D ≤ (H.card : ℝ) * q ^ D := by nlinarith [h4]
    exact le_of_mul_le_mul_right h5 hqD
  set B : Set (Coeff O k D) := (coeffFactor (O := O) k hD) ⁻¹' (mvNullSet O G D₀) with hB
  have hBcard : (Nat.card B : ℝ) < ε / 2 * q ^ (k * D) := by
    have h1 : Nat.card B = Nat.card (mvNullSet O G D₀) * residueCard O ^ (k * (D - D₀)) :=
      IFCG46.card_preimage_coeffFactor_eq k hD (mvNullSet O G D₀)
    have h2 : (Nat.card (mvNullSet O G D₀) : ℝ) < ε / 2 * q ^ (k * D₀) := by
      have h3 := hD₀
      rw [mvNullProp, boxProp, div_lt_iff₀ (qpow_pos _)] at h3
      exact h3
    have hexp2 : k * D₀ + k * (D - D₀) = k * D := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hD]
    calc (Nat.card B : ℝ)
        = (Nat.card (mvNullSet O G D₀) : ℝ) * q ^ (k * (D - D₀)) := by
          rw [h1, hq]; push_cast; rfl
      _ < ε / 2 * q ^ (k * D₀) * q ^ (k * (D - D₀)) :=
          mul_lt_mul_of_pos_right h2 (pow_pos hq0 _)
      _ = ε / 2 * q ^ (k * D) := by rw [mul_assoc, ← pow_add, hexp2]
  by_contra hno
  have hall : ∀ c ∈ H, c ∈ B := by
    intro c hc
    by_contra hcB
    exact hno ⟨c, (Finset.mem_filter.mp hc).2, fun hmem => hcB hmem⟩
  letI : Fintype ↥B := Fintype.ofFinite _
  have hsub : H ⊆ B.toFinset := fun c hc => Set.mem_toFinset.mpr (hall c hc)
  have hle : (H.card : ℝ) ≤ (Nat.card B : ℝ) := by
    have h1 := Finset.card_le_card hsub
    rw [Set.toFinset_card] at h1
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast h1
  linarith

/-- ★★★ **THE MULTIVARIABLE DRAIN** — the null proportion of any NONZERO polynomial in
`k` coefficient variables over `O` tends to `0`.  Induction on `k`; the heavy-fiber
survivor family feeds the König engine, whose point specialises `F` to a nonzero
one-variable polynomial contradicting §1's drain. -/
theorem tendsto_mvNullProp_zero [IsAdicComplete (maximalIdeal O) O] :
    ∀ {k : ℕ} (F : MvPolynomial (Fin k) O), F ≠ 0 →
      Tendsto (mvNullProp O F) atTop (𝓝 0) := by
  intro k
  induction k with
  | zero =>
    intro F hF
    obtain ⟨r, rfl⟩ := MvPolynomial.C_surjective (Fin 0) F
    have hr : r ≠ 0 := fun h0 => hF (by rw [h0, map_zero])
    obtain ⟨D₀, hD₀⟩ := exists_notMem_maximalIdeal_pow hr
    have hemp : mvNullSet O (MvPolynomial.C r : MvPolynomial (Fin 0) O) D₀ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨a, rfl⟩ := proj_surjective O 0 D₀ c
      have h1 := (mem_mvNullSet_proj a).mp hc
      rw [MvPolynomial.eval_C] at h1
      exact hD₀ h1
    exact tendsto_boxProp_zero_of_empty (truncClosed_mvNullSet _) hemp
  | succ k IH =>
    intro F hF
    by_contra hnot
    obtain ⟨ε, hε0, hε⟩ := exists_pos_forall_le_of_not_tendsto (antitone_mvNullProp F)
      (fun D => boxProp_nonneg _ _ _) hnot
    have hP0 : MvPolynomial.finSuccEquiv O k F ≠ 0 := fun h0 =>
      hF ((MvPolynomial.finSuccEquiv O k).injective (by rw [h0, map_zero]))
    set P := MvPolynomial.finSuccEquiv O k F with hPdef
    set G := P.coeff P.natDegree with hGdef
    have hG0 : G ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    obtain ⟨D₀, hD₀⟩ :=
      ((IH G hG0).eventually_lt_const (by linarith : (0 : ℝ) < ε / 2)).exists
    set S : ∀ D, Set (Coeff O k D) := fun D =>
      {c | ε / 2 ≤ fiberProp O F D c
        ∧ ∀ h : D₀ ≤ D, coeffFactor (O := O) k h c ∉ mvNullSet O G D₀} with hSdef
    have hcl : TruncClosed S := by
      intro N M h c hc
      refine ⟨le_trans hc.1 (fiberProp_le_trunc h c), fun hD₀N => ?_⟩
      rw [coeffFactor_coeffFactor]
      exact hc.2 (hD₀N.trans h)
    have hne : ∀ D, (S D).Nonempty := by
      have hne' : ∀ D, D₀ ≤ D → (S D).Nonempty := by
        intro D hD
        obtain ⟨c, hc1, hc2⟩ := exists_heavy_survivor hε0 hε hD₀ hD
        exact ⟨c, hc1, fun _ => hc2⟩
      intro D
      rcases Nat.lt_or_ge D D₀ with hD | hD
      · obtain ⟨c, hc⟩ := hne' D₀ le_rfl
        exact ⟨coeffFactor (O := O) k hD.le c, hcl hD.le c hc⟩
      · exact hne' D hD
    obtain ⟨a, ha⟩ := exists_point_of_truncClosed hcl hne
    set g := Polynomial.map (MvPolynomial.eval a : MvPolynomial (Fin k) O →+* O) P
      with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      have h1 : MvPolynomial.eval a G = 0 := by
        have h2 : g.coeff P.natDegree = MvPolynomial.eval a G := Polynomial.coeff_map _ _
        rw [h0, Polynomial.coeff_zero] at h2
        exact h2.symm
      have h3 := (ha D₀).2 le_rfl
      have h4 : coeffFactor (O := O) k le_rfl (proj O k D₀ a) = proj O k D₀ a := rfl
      rw [h4] at h3
      exact h3 ((mem_mvNullSet_proj a).mpr (by rw [h1]; exact zero_mem _))
    have hheavy : ∀ D, ε / 2 ≤ oneNullProp O g D := by
      intro D
      have h1 := (ha D).1
      rw [fiberProp, fiberSet_proj_eq_oneNullSet] at h1
      exact h1
    obtain ⟨D, hD⟩ := ((tendsto_oneNullProp_zero hg0).eventually_lt_const
      (by linarith : (0 : ℝ) < ε / 2)).exists
    linarith [hheavy D]

end MultiVar

/-! ## §3 The generic discriminant and the DISCHARGE of `DiscNullAt`

The generic monic `𝔉 = X^n + Σᵢ C(xᵢ)·Xⁱ` over `MvPolynomial (Fin n) O` carries the
generic discriminant resultant `genericDisc = Res(𝔉, 𝔉′)` at the pinned formal degrees
`(n, n−1)`.  The resultant commutes with EVERY coefficient ring map at pinned degrees
(`resultant_map_map` is unconditional), so `genericDisc` evaluates to `classDisc` on
every level-`D` class — the discriminant-null cylinder IS the null cylinder of one
fixed `n`-variable polynomial.  That polynomial is NONZERO: at the coefficient vector
of `∏ᵢ (X − π^{i+1})` (distinct roots — powers of a uniformizer never repeat) the
discriminant resultant is nonzero over `Frac O` by separability.  §2's drain fires. -/

section Disc

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

variable (O) in
/-- The generic monic polynomial of degree `n`. -/
noncomputable def genericMonic (n : ℕ) : Polynomial (MvPolynomial (Fin n) O) :=
  X ^ n + ∑ i : Fin n, C (MvPolynomial.X i) * X ^ (i : ℕ)

variable (O) in
/-- The generic discriminant resultant `Res(𝔉, 𝔉′)` at formal degrees `(n, n−1)`. -/
noncomputable def genericDisc (n : ℕ) : MvPolynomial (Fin n) O :=
  Polynomial.resultant (genericMonic O n) (derivative (genericMonic O n)) n (n - 1)

theorem map_genericMonic {n : ℕ} {S : Type*} [CommRing S]
    (ψ : MvPolynomial (Fin n) O →+* S) :
    Polynomial.map ψ (genericMonic O n)
      = X ^ n + ∑ i : Fin n, C (ψ (MvPolynomial.X i)) * X ^ (i : ℕ) := by
  simp only [genericMonic, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

theorem apply_genericDisc {n : ℕ} {S : Type*} [CommRing S]
    (ψ : MvPolynomial (Fin n) O →+* S) :
    ψ (genericDisc O n)
      = Polynomial.resultant (Polynomial.map ψ (genericMonic O n))
          (derivative (Polynomial.map ψ (genericMonic O n))) n (n - 1) := by
  rw [genericDisc, ← Polynomial.resultant_map_map, Polynomial.derivative_map]

/-- The generic discriminant evaluates to the integral discriminant resultant. -/
theorem eval_genericDisc {n : ℕ} (a : Fin n → O) :
    MvPolynomial.eval a (genericDisc O n)
      = Polynomial.resultant (monicPoly a) (derivative (monicPoly a)) n (n - 1) := by
  have h1 : Polynomial.map (MvPolynomial.eval a : MvPolynomial (Fin n) O →+* O)
      (genericMonic O n) = monicPoly a := by
    rw [map_genericMonic]
    simp only [MvPolynomial.eval_X]
    rfl
  rw [apply_genericDisc, h1]

/-- The generic discriminant evaluates to `classDisc` on every level-`D` class. -/
theorem eval_map_genericDisc {n D : ℕ} (c : Coeff O n D) :
    MvPolynomial.eval c (MvPolynomial.map (Ideal.Quotient.mk ((maximalIdeal O) ^ D))
      (genericDisc O n)) = classDisc c := by
  have hψ : MvPolynomial.eval c (MvPolynomial.map
        (Ideal.Quotient.mk ((maximalIdeal O) ^ D)) (genericDisc O n))
      = ((MvPolynomial.eval c).comp (MvPolynomial.map
          (Ideal.Quotient.mk ((maximalIdeal O) ^ D)))) (genericDisc O n) := rfl
  have h1 : Polynomial.map ((MvPolynomial.eval c).comp (MvPolynomial.map
        (Ideal.Quotient.mk ((maximalIdeal O) ^ D)))) (genericMonic O n)
      = classPoly c := by
    rw [map_genericMonic]
    simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval_X]
    rfl
  rw [hψ, apply_genericDisc, h1]
  rfl

/-- The null cylinders of the generic discriminant ARE the discriminant-null sets. -/
theorem mvNullSet_genericDisc (n D : ℕ) :
    mvNullSet O (genericDisc O n) D = discNullSet O n D := by
  ext c
  rw [mvNullSet, Set.mem_setOf_eq, discNullSet, Set.mem_setOf_eq, eval_map_genericDisc]

theorem mvNullProp_genericDisc (n : ℕ) :
    mvNullProp O (genericDisc O n) = discNullSeq O n := by
  funext D
  rw [mvNullProp, boxProp, mvNullSet_genericDisc, discNullSeq]

/-- ★ **THE WITNESS** — the generic discriminant is a NONZERO polynomial: a product of
`n` distinct monic linear factors (powers of a uniformizer) is separable, and its
discriminant resultant is nonzero already over `Frac O`. -/
theorem genericDisc_ne_zero (n : ℕ) : genericDisc (O := O) n ≠ 0 := by
  intro h0
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set K := FractionRing O
  set φ : O →+* K := algebraMap O K with hφdef
  set f₀ : Polynomial O := ∏ i : Fin n, (X - C (π ^ ((i : ℕ) + 1))) with hf₀
  have hf₀monic : f₀.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hf₀deg : f₀.natDegree = n := by
    rw [hf₀, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C]
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
  set a : Fin n → O := fun i => f₀.coeff (i : ℕ) with ha
  have hfa : monicPoly a = f₀ := IFCG17.monicPoly_coeff_eq_self hf₀monic hf₀deg
  -- the mapped witness splits into distinct linear factors over `K`
  have hmap : f₀.map φ = ∏ i : Fin n, (X - C (φ (π ^ ((i : ℕ) + 1)))) := by
    rw [hf₀, ← Polynomial.coe_mapRingHom, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C])
  have hinj : Function.Injective (fun i : Fin n => φ (π ^ ((i : ℕ) + 1))) := by
    intro i j hij
    have hOinj : Function.Injective φ := IsFractionRing.injective O K
    have hpow : π ^ ((i : ℕ) + 1) = π ^ ((j : ℕ) + 1) := hOinj hij
    have h1 : (i : ℕ) + 1 ≤ (j : ℕ) + 1 := by
      refine (pow_dvd_unit_mul_pow_iff hπ 1 _ _).mp ?_
      rw [Units.val_one, one_mul, ← hpow]
    have h2 : (j : ℕ) + 1 ≤ (i : ℕ) + 1 := by
      refine (pow_dvd_unit_mul_pow_iff hπ 1 _ _).mp ?_
      rw [Units.val_one, one_mul, hpow]
    exact Fin.ext (by omega)
  have hsep : (f₀.map φ).Separable := by
    rw [hmap]
    exact (Polynomial.separable_prod_X_sub_C_iff).mpr hinj
  -- the resultant over `K` at the pinned degrees is nonzero
  have hd : (f₀.map φ).natDegree = n := by rw [hf₀monic.natDegree_map, hf₀deg]
  have hd' : (f₀.map φ).derivative.natDegree ≤ n - 1 :=
    (Polynomial.natDegree_derivative_le _).trans (by rw [hd])
  have hne : Polynomial.resultant (f₀.map φ) (f₀.map φ).derivative n (n - 1) ≠ 0 := by
    have hpad := Polynomial.resultant_add_right_deg (f := f₀.map φ)
      (g := (f₀.map φ).derivative) (m := n) (n := (f₀.map φ).derivative.natDegree)
      (k := (n - 1) - (f₀.map φ).derivative.natDegree) le_rfl
    rw [Nat.add_sub_cancel' hd'] at hpad
    have hcoeff : (f₀.map φ).coeff n = 1 := by
      have h1 := (hf₀monic.map φ).coeff_natDegree
      rwa [hd] at h1
    have hbase : Polynomial.resultant (f₀.map φ) (f₀.map φ).derivative n
        (f₀.map φ).derivative.natDegree ≠ 0 := by
      have h2 := Polynomial.resultant_ne_zero (f₀.map φ) (f₀.map φ).derivative hsep
      rwa [hd] at h2
    rw [hpad, hcoeff, one_pow, one_mul]
    exact hbase
  -- transport back to `O` and hit the vanishing evaluation
  have hres : Polynomial.resultant f₀ (derivative f₀) n (n - 1) ≠ 0 := by
    intro hz
    refine hne ?_
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map, hz, map_zero]
  refine hres ?_
  have h3 := eval_genericDisc (O := O) a
  rw [h0, map_zero, hfa] at h3
  exact h3.symm

/-- ★★★ **`DiscNullAt n` HOLDS AT EVERY `n`** — the counting residual of IFCG49 is
DISCHARGED, unconditionally: over every complete DVR with finite residue field, the
proportion of level-`D` classes whose discriminant resultant vanishes mod `π^D` tends
to `0`. -/
theorem discNullAt (n : ℕ) : DiscNullAt n := by
  intro O _ _ _ _ _
  have h1 := tendsto_mvNullProp_zero (O := O) (genericDisc O n) (genericDisc_ne_zero n)
  rwa [mvNullProp_genericDisc] at h1

end Disc

/-! ## §4 `KrasnerAt` reduced to its IRREDUCIBLE core

A separable monic factors over the UFD `O[X]` into monic irreducibles
(`monicFactorization_exists`); separability over `Frac O` descends to every factor and
makes distinct factors coprime, hence all the pinned-degree resultants nonvanish; the
landed IFCG42 transfer `decidedAt_mulClass_of_not_dvd_resultant` recombines the factor
decisions at the exact resultant depth `v` (extracted by adic Hausdorffness), with the
levels lifted by IFCG49's `decidedAt_of_coeffFactor`.  What remains of `KrasnerAt` is
EXACTLY the classical Krasner statement for one irreducible separable monic. -/

section KrasnerRed

open Uniformity.Density.IFCG42 (decidedAt_mulClass_of_not_dvd_resultant)

/-- ★ **THE IRREDUCIBLE KRASNER CORE** — `KrasnerAt`'s statement restricted to
IRREDUCIBLE `monicPoly a`: an irreducible separable monic over a complete DVR is
decided at some finite level.  This is the exact classical content of Krasner's lemma /
Okutsu–Montes completeness (per-point, ∃-level, no rate); it is the ONLY residual of
the capstone's `a2` field after this file. -/
def KrasnerIrredAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ a : Fin n → O, Irreducible (monicPoly a) →
      Polynomial.resultant (monicPoly a) (Polynomial.derivative (monicPoly a)) n (n - 1) ≠ 0 →
      ∃ (N : ℕ) (σ : FactorizationType), DecidedAt O n σ N (proj O n N a)

/-- A separable product has coprime factors (constructively, from the Bezout data). -/
theorem isCoprime_of_separable_mul {K : Type*} [CommRing K] {f g : Polynomial K}
    (h : (f * g).Separable) : IsCoprime f g := by
  obtain ⟨u, v, huv⟩ := h
  rw [Polynomial.derivative_mul] at huv
  exact ⟨v * derivative g, u * f + v * derivative f, by linear_combination huv⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Monic irreducibles have positive degree. -/
theorem natDegree_ne_zero_of_monic_irreducible {g : Polynomial O} (hg : g.Monic)
    (hirr : Irreducible g) : g.natDegree ≠ 0 := by
  intro h0
  rw [Polynomial.Monic.natDegree_eq_zero hg] at h0
  exact hirr.not_isUnit (h0 ▸ isUnit_one)

/-- Separability over a field forces the pinned-degree discriminant resultant nonzero. -/
theorem resultant_deriv_pinned_ne_zero {K : Type*} [Field K] {f : Polynomial K}
    (hf : f.Monic) (hsep : f.Separable) {n : ℕ} (hd : f.natDegree = n) :
    Polynomial.resultant f (derivative f) n (n - 1) ≠ 0 := by
  have hd' : (derivative f).natDegree ≤ n - 1 :=
    (Polynomial.natDegree_derivative_le _).trans (by rw [hd])
  have hpad := Polynomial.resultant_add_right_deg (f := f) (g := derivative f) (m := n)
    (n := (derivative f).natDegree) (k := (n - 1) - (derivative f).natDegree) le_rfl
  rw [Nat.add_sub_cancel' hd'] at hpad
  have hcoeff : f.coeff n = 1 := by
    have h1 := hf.coeff_natDegree
    rwa [hd] at h1
  have hbase : Polynomial.resultant f (derivative f) n (derivative f).natDegree ≠ 0 := by
    have h2 := Polynomial.resultant_ne_zero f (derivative f) hsep
    rwa [hd] at h2
  rw [hpad, hcoeff, one_pow, one_mul]
  exact hbase

/-- The pinned-degree discriminant resultant over `O` nonvanishes for a monic whose
image over `Frac O` is separable. -/
theorem resultant_deriv_ne_zero_of_separable_map {g : Polynomial O} (hg : g.Monic)
    {n : ℕ} (hdeg : g.natDegree = n)
    (hsep : (g.map (algebraMap O (FractionRing O))).Separable) :
    Polynomial.resultant g (derivative g) n (n - 1) ≠ 0 := by
  intro hz
  refine resultant_deriv_pinned_ne_zero (hg.map _) hsep
    (by rw [hg.natDegree_map, hdeg]) ?_
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map, hz, map_zero]

/-- Coprimality over `Frac O` forces the pinned-degree pair resultant nonzero. -/
theorem resultant_pair_ne_zero_of_coprime_map {g h : Polynomial O} (hg : g.Monic)
    (hh : h.Monic)
    (hcop : IsCoprime (g.map (algebraMap O (FractionRing O)))
      (h.map (algebraMap O (FractionRing O)))) :
    Polynomial.resultant g h g.natDegree h.natDegree ≠ 0 := by
  intro hz
  have h1 := Polynomial.resultant_ne_zero _ _ hcop
  rw [hg.natDegree_map, hh.natDegree_map] at h1
  exact h1 (by rw [Polynomial.resultant_map_map, hz, map_zero])

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★★ **THE RECOMBINATION INDUCTION** — a multiset of monic irreducibles with
separable product and decided members has a decided product, through the IFCG42
transfer at the exact resultant depths. -/
theorem decidedAt_multiset_prod :
    ∀ (s : Multiset (Polynomial O)) (m : ℕ),
      (∀ g ∈ s, g.Monic ∧ Irreducible g) →
      ((s.prod.map (algebraMap O (FractionRing O))).Separable) →
      (∀ g ∈ s, ∃ (N : ℕ) (σ : FactorizationType),
        DecidedAt O g.natDegree σ N (proj O g.natDegree N (fun i => g.coeff (i : ℕ)))) →
      s.prod.natDegree = m →
      ∃ (N : ℕ) (σ : FactorizationType),
        DecidedAt O m σ N (proj O m N (fun i : Fin m => s.prod.coeff (i : ℕ))) := by
  intro s
  refine Multiset.induction_on s ?_ ?_
  · -- the empty product: `1` is decided at its constant type
    intro m _ _ _ hm
    rw [Multiset.prod_zero] at hm ⊢
    have hm0 : m = 0 := by rw [← hm, Polynomial.natDegree_one]
    subst hm0
    have hb1 : ∀ b : Fin 0 → O, monicPoly b = 1 := by
      intro b
      rw [monicPoly]
      simp
    exact ⟨1, typeOf (1 : Polynomial O), fun b _ => by rw [hb1 b]⟩
  · intro g s' IH m hall hsep hdec hm
    have hg := hall g (Multiset.mem_cons_self g s')
    have hs' : ∀ g' ∈ s', g'.Monic ∧ Irreducible g' :=
      fun g' hg' => hall g' (Multiset.mem_cons_of_mem hg')
    have hprod : (g ::ₘ s').prod = g * s'.prod := Multiset.prod_cons g s'
    have hs'monic : s'.prod.Monic := by
      have h1 := monic_multiset_prod_of_monic s' id (fun g' hg' => (hs' g' hg').1)
      rwa [Multiset.map_id] at h1
    -- separability splits into the factor pair
    have hsepmul : ((g.map (algebraMap O (FractionRing O)))
        * (s'.prod.map (algebraMap O (FractionRing O)))).Separable := by
      rw [← Polynomial.map_mul, ← hprod]
      exact hsep
    have hseps' : (s'.prod.map (algebraMap O (FractionRing O))).Separable :=
      hsepmul.of_mul_right
    have hcop : IsCoprime (g.map (algebraMap O (FractionRing O)))
        (s'.prod.map (algebraMap O (FractionRing O))) := isCoprime_of_separable_mul hsepmul
    -- the two decisions
    obtain ⟨N₁, σ₁, hd₁⟩ := hdec g (Multiset.mem_cons_self g s')
    obtain ⟨N₂, σ₂, hd₂⟩ := IH s'.prod.natDegree hs' hseps'
      (fun g' hg' => hdec g' (Multiset.mem_cons_of_mem hg')) rfl
    -- the exact resultant depth
    have hgnd : g.natDegree ≠ 0 := natDegree_ne_zero_of_monic_irreducible hg.1 hg.2
    have hres0 : Polynomial.resultant g s'.prod g.natDegree s'.prod.natDegree ≠ 0 :=
      resultant_pair_ne_zero_of_coprime_map hg.1 hs'monic hcop
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨w, hw⟩ := exists_notMem_maximalIdeal_pow hres0
    have hw1 : 1 ≤ w := by
      by_contra h
      have hw0 : w = 0 := by omega
      rw [hw0, pow_zero, Ideal.one_eq_top] at hw
      exact hw Submodule.mem_top
    have hres : ¬ π ^ ((w - 1) + 1) ∣
        Polynomial.resultant g s'.prod g.natDegree s'.prod.natDegree := by
      intro hdvd
      refine hw ?_
      rw [mem_maximalIdeal_pow_iff_dvd hπ]
      have hww : (w - 1) + 1 = w := by omega
      rwa [hww] at hdvd
    -- level bookkeeping
    set v := w - 1 with hv
    set N := v + max (v + 1) (max N₁ N₂) with hN
    have hNv : 2 * v + 1 ≤ N := by
      have h1 := le_max_left (v + 1) (max N₁ N₂)
      omega
    have hN₁ : N₁ ≤ N - v := by
      have h1 := le_max_left N₁ N₂
      have h2 := le_max_right (v + 1) (max N₁ N₂)
      omega
    have hN₂ : N₂ ≤ N - v := by
      have h1 := le_max_right N₁ N₂
      have h2 := le_max_right (v + 1) (max N₁ N₂)
      omega
    -- coefficient vectors and their monic polynomials
    have hma₁ : monicPoly (fun i : Fin g.natDegree => g.coeff (i : ℕ)) = g :=
      IFCG17.monicPoly_coeff_eq_self hg.1 rfl
    have hma₂ : monicPoly (fun i : Fin s'.prod.natDegree => s'.prod.coeff (i : ℕ))
        = s'.prod := IFCG17.monicPoly_coeff_eq_self hs'monic rfl
    -- decisions at the shifted level
    have hd₁' : DecidedAt O g.natDegree σ₁ (N - v)
        (proj O g.natDegree (N - v) (fun i => g.coeff (i : ℕ))) :=
      decidedAt_of_coeffFactor hN₁ hd₁
    have hd₂' : DecidedAt O s'.prod.natDegree σ₂ (N - v)
        (proj O s'.prod.natDegree (N - v) (fun i => s'.prod.coeff (i : ℕ))) :=
      decidedAt_of_coeffFactor hN₂ hd₂
    -- the resultant instrument on the coefficient vectors
    have hresm : ¬ π ^ (v + 1) ∣ Polynomial.resultant
        (monicPoly (fun i : Fin g.natDegree => g.coeff (i : ℕ)))
        (monicPoly (fun i : Fin s'.prod.natDegree => s'.prod.coeff (i : ℕ)))
        g.natDegree s'.prod.natDegree := by
      rw [hma₁, hma₂]
      exact hres
    -- FIRE the transfer
    have htrans := decidedAt_mulClass_of_not_dvd_resultant hπ hNv (Or.inl hgnd)
      hresm hd₁' hd₂'
    rw [← mulClass_proj] at htrans
    rw [hma₁, hma₂] at htrans
    -- degree accounting closes the goal
    have hm' : g.natDegree + s'.prod.natDegree = m := by
      rw [← hm, hprod, hg.1.natDegree_mul hs'monic]
    subst hm'
    rw [hprod]
    exact ⟨N, ⟨σ₁.data + σ₂.data⟩, htrans⟩

end KrasnerRed

section KrasnerFire

/-- ★★★ **THE REDUCTION** — `KrasnerAt n` (IFCG49's field-theory residual, at every
`n`) follows from the irreducible Krasner core at all degrees. -/
theorem krasnerAt_of_krasnerIrred {n : ℕ} (hcore : ∀ m, KrasnerIrredAt m) :
    KrasnerAt n := by
  intro O _ _ _ _ _ a hres
  have hfm : (monicPoly a).Monic := monicPoly_monic a
  obtain ⟨s, hs⟩ := monicFactorization_exists hfm
  -- separability of the full polynomial over `Frac O`, from the resultant hypothesis
  have hsep : ((monicPoly a).map (algebraMap O (FractionRing O))).Separable := by
    have h1 : Polynomial.resultant ((monicPoly a).map (algebraMap O (FractionRing O)))
        (derivative ((monicPoly a).map (algebraMap O (FractionRing O)))) n (n - 1) ≠ 0 := by
      rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
      intro h2
      exact hres (IsFractionRing.injective O (FractionRing O) (by rw [h2, map_zero]))
    have hd : ((monicPoly a).map (algebraMap O (FractionRing O))).natDegree = n := by
      rw [hfm.natDegree_map, monicPoly_natDegree]
    have hd' : (derivative ((monicPoly a).map (algebraMap O (FractionRing O)))).natDegree
        ≤ n - 1 := (Polynomial.natDegree_derivative_le _).trans (by rw [hd])
    have hpad := Polynomial.resultant_add_right_deg
      (f := (monicPoly a).map (algebraMap O (FractionRing O)))
      (g := derivative ((monicPoly a).map (algebraMap O (FractionRing O)))) (m := n)
      (n := (derivative ((monicPoly a).map (algebraMap O (FractionRing O)))).natDegree)
      (k := (n - 1) - (derivative ((monicPoly a).map
        (algebraMap O (FractionRing O)))).natDegree) le_rfl
    rw [Nat.add_sub_cancel' hd'] at hpad
    have hdef : Polynomial.resultant ((monicPoly a).map (algebraMap O (FractionRing O)))
        (derivative ((monicPoly a).map (algebraMap O (FractionRing O)))) n
        (derivative ((monicPoly a).map (algebraMap O (FractionRing O)))).natDegree ≠ 0 := by
      intro h3
      rw [hpad, h3, mul_zero] at h1
      exact h1 rfl
    by_contra hnsep
    have h4 := Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (hfm.map (algebraMap O (FractionRing O))).ne_zero, hnsep⟩
    rw [hd] at h4
    exact hdef h4
  -- each factor is decided, by the CORE
  have hdec : ∀ g ∈ s, ∃ (N : ℕ) (σ : FactorizationType),
      DecidedAt O g.natDegree σ N (proj O g.natDegree N (fun i => g.coeff (i : ℕ))) := by
    intro g hgs
    obtain ⟨hgm, hgirr⟩ := hs.1 g hgs
    have hmb : monicPoly (fun i : Fin g.natDegree => g.coeff (i : ℕ)) = g :=
      IFCG17.monicPoly_coeff_eq_self hgm rfl
    have hgdvd : (g.map (algebraMap O (FractionRing O)))
        ∣ ((monicPoly a).map (algebraMap O (FractionRing O))) :=
      Polynomial.map_dvd _ (hs.2 ▸ Multiset.dvd_prod hgs)
    have hsepg : (g.map (algebraMap O (FractionRing O))).Separable := hsep.of_dvd hgdvd
    have hresg : Polynomial.resultant g (derivative g) g.natDegree (g.natDegree - 1) ≠ 0 :=
      resultant_deriv_ne_zero_of_separable_map hgm rfl hsepg
    exact hcore g.natDegree O (fun i => g.coeff (i : ℕ))
      (by rw [hmb]; exact hgirr) (by rw [hmb]; exact hresg)
  -- recombine
  obtain ⟨N, σ, hdN⟩ := decidedAt_multiset_prod s n hs.1 (by rw [hs.2]; exact hsep) hdec
    (by rw [hs.2, monicPoly_natDegree])
  refine ⟨N, σ, ?_⟩
  have hveq : (fun i : Fin n => s.prod.coeff (i : ℕ)) = a := by
    funext i
    rw [hs.2, monicPoly_coeff_lt a i.isLt]
  rwa [hveq] at hdN

/-- Nonvacuity: the core holds vacuously at degree `0` (the unit is not irreducible). -/
theorem krasnerIrredAt_zero : KrasnerIrredAt 0 := by
  intro O _ _ _ _ _ a hirr _
  exfalso
  have h1 : monicPoly a = 1 := by
    rw [monicPoly]
    simp
  rw [h1] at hirr
  exact hirr.not_isUnit isUnit_one

/-- Nonvacuity: the core holds at degree `1` — linear polynomials are decided at level
`1` with type `⟨{(1,1)}⟩`. -/
theorem krasnerIrredAt_one : KrasnerIrredAt 1 := by
  intro O _ _ _ _ _ a _ _
  exact ⟨1, ⟨{(1, 1)}⟩, fun b _ =>
    typeOf_of_natDegree_one (monicPoly_monic b) (monicPoly_natDegree b)⟩

end KrasnerFire

/-! ## §5 THE FIRES — the capstone's `a2` field through IFCG49 -/

/-- ★★★ **HALF THE FENCE FALLS** — with `DiscNullAt` discharged, `KrasnerAt n` ALONE
now yields UDR's deep-tail drain at every `n`. -/
theorem deepTailDrainAt_of_krasner {n : ℕ} (hK : KrasnerAt n) :
    IFCG46.DeepTailDrainAt n :=
  deepTailDrainAt_of_krasner_discNull hK (discNullAt n)

/-- ★★★ **THE CAPSTONE FEED, DISC SIDE DISCHARGED** — the ENTIRE `a2` field
(`∀ n, DrainageAt n`) now rests on `KrasnerAt m` (`m ≥ 4`) alone. -/
theorem drainageAt_all_of_krasner (hK : ∀ m, 4 ≤ m → KrasnerAt m) :
    ∀ n, DrainageAt n :=
  drainageAt_all_of_krasner_discNull hK (fun m _ => discNullAt m)

/-- ★★★ **THE CAPSTONE FEED FROM THE IRREDUCIBLE CORE ALONE** — the `a2` field rests
on the single classical residual `KrasnerIrredAt m`: an IRREDUCIBLE separable monic
over a complete DVR is eventually decided.  Everything else is machine-checked. -/
theorem drainageAt_all_of_krasnerIrred (hcore : ∀ m, KrasnerIrredAt m) :
    ∀ n, DrainageAt n :=
  drainageAt_all_of_krasner (fun _ _ => krasnerAt_of_krasnerIrred hcore)

/-- ★ **THE DEEP KRASNER CORE** — `KrasnerIrredAt` with the residue-irreducible case
removed: only irreducible separable monics whose residue reduction is NOT irreducible
(the residue-power/OM-tower inputs) remain.  This is the exact deep-wild residual. -/
def KrasnerDeepAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ a : Fin n → O, Irreducible (monicPoly a) →
      ¬ Irreducible ((monicPoly a).map (IsLocalRing.residue O)) →
      Polynomial.resultant (monicPoly a) (Polynomial.derivative (monicPoly a)) n (n - 1) ≠ 0 →
      ∃ (N : ℕ) (σ : FactorizationType), DecidedAt O n σ N (proj O n N a)

/-- ★★ The residue-irreducible inputs are ALREADY decided (CN-21 through IFCG46), so
the irreducible core reduces to its deep-wild part. -/
theorem krasnerIrredAt_of_deep {n : ℕ} (hdeep : KrasnerDeepAt n) : KrasnerIrredAt n := by
  intro O _ _ _ _ _ a hirr hres
  by_cases hred : Irreducible ((monicPoly a).map (IsLocalRing.residue O))
  · have hn : n ≠ 0 := by
      intro h0
      subst h0
      have h1 : monicPoly a = 1 := by
        rw [monicPoly]
        simp
      rw [h1] at hirr
      exact hirr.not_isUnit isUnit_one
    exact ⟨1, ⟨{(1, n)}⟩, IFCG46.decidedAt_of_irreducible_residue hn one_ne_zero hred⟩
  · exact hdeep O a hirr hred hres

/-- ★★★ **THE SHARPEST FIRE** — the capstone's `a2` field from the DEEP-WILD Krasner
core alone: every shallow input (residue-irreducible, reducible, linear, constant) is
machine-checked away. -/
theorem drainageAt_all_of_krasnerDeep (hdeep : ∀ m, KrasnerDeepAt m) :
    ∀ n, DrainageAt n :=
  drainageAt_all_of_krasnerIrred (fun m => krasnerIrredAt_of_deep (hdeep m))

end Uniformity.Density.IFCG50

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG50.mem_pow_sub_of_mul_mem
#print axioms Uniformity.Density.IFCG50.exists_root_of_forall_oneNull_nonempty
#print axioms Uniformity.Density.IFCG50.tendsto_oneNullProp_zero
#print axioms Uniformity.Density.IFCG50.fiberSet_proj_eq_oneNullSet
#print axioms Uniformity.Density.IFCG50.card_mvNullSet_eq_sum
#print axioms Uniformity.Density.IFCG50.exists_heavy_survivor
#print axioms Uniformity.Density.IFCG50.tendsto_mvNullProp_zero
#print axioms Uniformity.Density.IFCG50.genericDisc_ne_zero
#print axioms Uniformity.Density.IFCG50.discNullAt
#print axioms Uniformity.Density.IFCG50.decidedAt_multiset_prod
#print axioms Uniformity.Density.IFCG50.krasnerAt_of_krasnerIrred
#print axioms Uniformity.Density.IFCG50.krasnerIrredAt_zero
#print axioms Uniformity.Density.IFCG50.krasnerIrredAt_one
#print axioms Uniformity.Density.IFCG50.deepTailDrainAt_of_krasner
#print axioms Uniformity.Density.IFCG50.drainageAt_all_of_krasner
#print axioms Uniformity.Density.IFCG50.drainageAt_all_of_krasnerIrred
#print axioms Uniformity.Density.IFCG50.krasnerIrredAt_of_deep
#print axioms Uniformity.Density.IFCG50.drainageAt_all_of_krasnerDeep
