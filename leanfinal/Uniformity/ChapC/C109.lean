/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C109a
import Uniformity.ChapC.C109i
import Uniformity.ChapC.C109ii
import Uniformity.ChapC.C109iii
import Uniformity.ChapC.C109iv
import Uniformity.ChapC.C109v
import Uniformity.ChapB.B36

/-!
# Uniformity.ChapC.C109 — the exact node cell count (the A-C.5 ASSEMBLY)

**Chapter C, NODE C.109** (`ht_node_cell_card`, statement byte-frozen from
`leanspec/Leanspec/ChapC.lean`, the A-C.2 re-sign) — the exact count of the level-`N` node
cell: `Q^{B_v(N)}` times the product of the side censuses.  This module ASSEMBLES the five
signed layers C.109-i … C.109-v (amendment A-C.5) into the frozen statement.

## Assembly route (A-C.5, with one recorded deviation)

Through C.109a's development bridge `E`, a cell class is a vector of `m` block classes; the
cell conditions decompose as: per-block height floors (`le_gaussVal_iff` at level `N`,
readable since `hvis`), vertex exactness = the height-`Pceil` digit is NONZERO (B.36), and
the per-side residual types = conditions on the PRICED digits, which assemble into a sweep
function `sweepRead` satisfying exactly C.109-v's `SweepCond` (the on-side height law makes
`resPoly`'s coefficients the priced digits).  The count then fibers over the sweep
assignment: every fibre is a product of blocks of `r`-independent size (`C.109-iii`'s
uniformity), and C.109-v counts the base.

**Recorded deviation from the route sketch**: C.109-ii's global box count enters through
its per-digit refinement C.109-iii (summing the uniform fibre over the `Q` digit values
recovers the box count blockwise), because the assembly needs the count in the free-lift
block carrier, not the dev-of-monic carrier.  C.109-ii is imported and its statement is the
blockwise special case; nothing is weakened.

## Status

SKELETON (in construction): the lemma chain is stated and elaborates; bodies land
hardest-first with per-lemma commits.  Zero `sorry` required before this node is declared
LANDED; final footprint must be Lean core only.
-/

set_option linter.style.longLine false
set_option linter.overlappingInstances false

namespace Uniformity.Density.Tower.C109asm

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. Class-level digit reads (level-`N` congruence) -/

/-- the digit at height `h` only reads the class mod `π ^ (h + 1)`. -/
theorem digAt_congr (hπ : Irreducible π) {h : ℕ} {x x' : O}
    (hdvd : π ^ (h + 1) ∣ (x' - x)) : digAt π h x = digAt π h x' := by
  obtain ⟨w, hw⟩ := hdvd
  have hx' : x' = x + π ^ (h + 1) * w := by linear_combination hw
  by_cases hx : π ^ h ∣ x
  · obtain ⟨y, rfl⟩ := hx
    have hx'2 : x' = π ^ h * (y + π * w) := by rw [hx']; ring
    rw [digAt_eq hπ (rfl : π ^ h * y = π ^ h * y), digAt_eq hπ hx'2, map_add]
    have : IsLocalRing.residue O (π * w) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
      exact Dvd.intro w rfl
    rw [this, add_zero]
  · have hx2 : ¬ π ^ h ∣ x' := by
      intro hc
      refine hx ?_
      have : π ^ h ∣ π ^ (h + 1) * w := Dvd.dvd.mul_right (pow_dvd_pow π (Nat.le_succ h)) w
      have := hc.sub this
      rwa [hx', add_sub_cancel_right] at this
    rw [digAt, digAt, dif_neg hx, dif_neg hx2]

/-- The height-`h` digit map factors through level-`N` classes (`h < N`): congruent
coefficient vectors give equal `resMk` reads. -/
theorem resMk_proj_congr (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {N h : ℕ} (hh : h < N) {A A' : Polynomial O}
    (hA : A.natDegree < Φ.natDegree) (hA' : A'.natDegree < Φ.natDegree)
    (hproj : proj O Φ.natDegree N (fun i => A.coeff i)
      = proj O Φ.natDegree N (fun i => A'.coeff i)) :
    resMk π Φ h A = resMk π Φ h A' := by
  have hcoeff : ∀ i : ℕ, π ^ N ∣ (A'.coeff i - A.coeff i) := by
    intro i
    by_cases hi : i < Φ.natDegree
    · have hmk := congrFun hproj ⟨i, hi⟩
      have hmem : A.coeff i - A'.coeff i ∈ (IsLocalRing.maximalIdeal O) ^ N :=
        Ideal.Quotient.eq.mp hmk
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
      exact dvd_sub_comm.mp hmem
    · rw [A.coeff_eq_zero_of_natDegree_lt (by omega),
        A'.coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
      exact dvd_zero _
  have hdig : digPoly π h A = digPoly π h A' := by
    ext i
    rw [digPoly_coeff hπ, digPoly_coeff hπ]
    exact digAt_congr hπ (dvd_trans (pow_dvd_pow π (by omega)) (hcoeff i))
  rw [resMk, resMk, hdig]

/-- Vertex exactness at the digit: on the `h`-floor, the height-`h` digit is nonzero iff
the Gauss valuation is exactly `h` (B.36 both ways). -/
theorem resMk_ne_zero_iff_gaussVal (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h : ℕ} {A : Polynomial O} (hA : A.degree < Φ.degree)
    (hfl : (h : ℕ∞) ≤ gaussVal A) :
    resMk π Φ h A ≠ 0 ↔ gaussVal A = (h : ℕ∞) := by
  constructor
  · intro hne
    rcases eq_or_lt_of_le hfl with heq | hlt
    · exact heq.symm
    · exfalso
      refine hne ?_
      rw [resMk_eq_zero_iff hπ hΦ hA, digPoly_eq_zero_iff hπ hfl]
      exact_mod_cast Order.add_one_le_of_lt hlt
  · intro heq
    have hA0 : A ≠ 0 := by
      intro h0
      rw [← gaussVal_eq_top_iff] at h0
      rw [h0] at heq
      exact (ENat.top_ne_coe h).elim heq
    exact resMk_ne_zero hπ hΦ hA hA0 heq

/-- the chosen integral lift of a level-`N` residue class. -/
noncomputable def liftRes {N : ℕ} (x : Res O N) : O :=
  (Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x).choose

theorem liftRes_spec {N : ℕ} (x : Res O N) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (liftRes x) = x :=
  (Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x).choose_spec

/-- the chosen polynomial lift of a block class (degree `< d` by construction). -/
noncomputable def blockPoly {d N : ℕ} (c : Coeff O d N) : Polynomial O :=
  ∑ i : Fin d, C (liftRes (c i)) * X ^ (i : ℕ)

theorem blockPoly_coeff {d N : ℕ} (c : Coeff O d N) (t : ℕ) :
    (blockPoly c).coeff t = if h : t < d then liftRes (c ⟨t, h⟩) else 0 := by
  classical
  rw [blockPoly, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : t < d
  · rw [dif_pos h, Finset.sum_eq_single (⟨t, h⟩ : Fin d)]
    · simp
    · intro b _ hb
      exact if_neg fun hc => hb (Fin.ext hc.symm)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => if_neg fun hc => h ?_
    exact hc ▸ b.isLt

theorem blockPoly_natDegree_lt {d N : ℕ} (hd : 0 < d) (c : Coeff O d N) :
    (blockPoly c).natDegree < d := by
  rcases eq_or_ne (blockPoly c) 0 with h0 | h0
  · simpa [h0] using hd
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro t ht
    rw [blockPoly_coeff]
    exact dif_neg (by exact_mod_cast not_lt.2 ht)

theorem blockPoly_proj {d N : ℕ} (c : Coeff O d N) :
    proj O d N (fun i => (blockPoly c).coeff i) = c := by
  funext i
  show Ideal.Quotient.mk _ ((blockPoly c).coeff (i : ℕ)) = c i
  rw [blockPoly_coeff, dif_pos i.isLt, Fin.eta]
  exact liftRes_spec (c i)

/-- **the class-level digit read** at height `h`: the `resMk` of the chosen lift. -/
noncomputable def blockDigit (π : O) (Φ : Polynomial O) (h N : ℕ)
    (c : Coeff O Φ.natDegree N) : resField Φ :=
  resMk π Φ h (blockPoly c)

/-- `blockDigit` agrees with the `resMk` read of ANY lift of the class. -/
theorem blockDigit_eq (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {N h : ℕ} (hh : h < N) {A : Polynomial O} (hA : A.natDegree < Φ.natDegree) :
    blockDigit π Φ h N (proj O Φ.natDegree N (fun i => A.coeff i)) = resMk π Φ h A := by
  rw [blockDigit]
  refine resMk_proj_congr hπ hΦ hh
    (blockPoly_natDegree_lt (lt_of_le_of_lt (Nat.zero_le _) hA) _) hA ?_
  rw [blockPoly_proj]

/-! ### 2. The development assembly (blocks → the monic member) -/

/-- Assembling blocks of degree `< deg Φ` below a monic top reproduces the blocks as the
`Φ`-adic development, with top coefficient `1` (B.06 `dev_unique`). -/
theorem dev_assemble {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (A : Fin m → Polynomial O) (hdeg : ∀ j, (A j).degree < Φ.degree) :
    (∀ j : Fin m, dev Φ (∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m) (j : ℕ) = A j)
      ∧ dev Φ (∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m) m = 1 := by
  classical
  set f := ∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m with hf
  set a : ℕ → Polynomial O :=
    fun j => if h : j < m then A ⟨j, h⟩ else if j = m then 1 else 0 with ha
  have hΦ0 : Φ ≠ 0 := hΦm.ne_zero
  have hdegΦ : (0 : WithBot ℕ) < Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ0]
    exact_mod_cast hΦd
  have hdeg' : ∀ j, (a j).degree < Φ.degree := by
    intro j
    simp only [ha]
    by_cases h1 : j < m
    · rw [dif_pos h1]; exact hdeg _
    · rw [dif_neg h1]
      by_cases h2 : j = m
      · rw [if_pos h2, Polynomial.degree_one]; exact hdegΦ
      · rw [if_neg h2, Polynomial.degree_zero, Polynomial.degree_eq_natDegree hΦ0]
        exact WithBot.bot_lt_coe _
  have hsum : ∑ j ∈ Finset.range (m + 1), a j * Φ ^ j = f := by
    rw [Finset.sum_range_succ, hf]
    congr 1
    · rw [Finset.sum_range fun j => a j * Φ ^ j]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ha, dif_pos i.isLt, Fin.eta]
    · simp only [ha, dif_neg (lt_irrefl m), if_true, one_mul]
  have huniq := dev_unique hΦm hΦd hdeg' hsum
  constructor
  · intro j
    have := (huniq (j : ℕ) (by omega)).symm
    simp only [ha, dif_pos j.isLt, Fin.eta] at this
    exact this
  · have := (huniq m (by omega)).symm
    simp only [ha, dif_neg (lt_irrefl m), if_pos rfl] at this
    exact this

/-- the assembled polynomial is monic of degree `m·d`, hence IS a `monicPoly`. -/
theorem assemble_eq_monicPoly {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (A : Fin m → Polynomial O) (hdeg : ∀ j, (A j).degree < Φ.degree) :
    ∃ a : Fin (m * Φ.natDegree) → O,
      monicPoly a = ∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m := by
  classical
  set f := ∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m with hf
  have hΦ0 : Φ ≠ 0 := hΦm.ne_zero
  have hΦmdeg : (Φ ^ m).degree = ((m * Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree hΦ0]
    rw [nsmul_eq_mul]
    exact_mod_cast rfl
  have htaildeg : (∑ i : Fin m, A i * Φ ^ (i : ℕ)).degree < (Φ ^ m).degree := by
    rw [hΦmdeg]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (m * Φ.natDegree))]
    intro i _
    have hAi : (A i).natDegree < Φ.natDegree := by
      rcases eq_or_ne (A i) 0 with h0 | h0
      · rw [h0, Polynomial.natDegree_zero]; exact hΦd
      · rw [Polynomial.natDegree_lt_iff_degree_lt h0,
          ← Polynomial.degree_eq_natDegree hΦ0]
        exact hdeg i
    have hnat : ((A i * Φ ^ (i : ℕ)).natDegree) < m * Φ.natDegree := by
      have h1 : (A i * Φ ^ (i : ℕ)).natDegree ≤ (A i).natDegree + (i : ℕ) * Φ.natDegree := by
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        rw [Polynomial.natDegree_pow]
      have h2 : ((i : ℕ) + 1) * Φ.natDegree ≤ m * Φ.natDegree :=
        Nat.mul_le_mul_right _ i.isLt
      nlinarith [hAi]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnat)
  have hmon : f.Monic := by
    rw [hf, add_comm]
    exact (hΦm.pow m).add_of_left htaildeg
  have hdegf : f.natDegree = m * Φ.natDegree := by
    have : f.degree = (Φ ^ m).degree := by
      rw [hf]
      rw [add_comm]
      exact Polynomial.degree_add_eq_left_of_degree_lt htaildeg
    have h2 : (Φ ^ m).natDegree = m * Φ.natDegree := by
      rw [Polynomial.natDegree_pow]
    rw [Polynomial.natDegree, this, ← Polynomial.natDegree]
    exact h2
  refine ⟨fun i => f.coeff (i : ℕ), ?_⟩
  ext t
  rw [monicPoly, Polynomial.coeff_add, coeff_X_pow]
  have htail : (∑ i : Fin (m * Φ.natDegree), C (f.coeff (i : ℕ)) * X ^ (i : ℕ)).coeff t
      = if t < m * Φ.natDegree then f.coeff t else 0 := by
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases h : t < m * Φ.natDegree
    · rw [if_pos h, Finset.sum_eq_single (⟨t, h⟩ : Fin (m * Φ.natDegree))]
      · simp
      · intro b _ hb
        exact if_neg fun hc => hb (Fin.ext hc.symm)
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun b _ => if_neg fun hc => h ?_
      exact hc ▸ b.isLt
  rw [htail]
  rcases lt_trichotomy t (m * Φ.natDegree) with h | h | h
  · rw [if_neg (by omega), if_pos h, zero_add]
  · rw [if_pos h, if_neg (by omega), add_zero, h, ← hdegf]
    exact hmon.coeff_natDegree.symm
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
    exact (f.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ### 3. The sweep read and the block sets -/

open Classical in
/-- **the sweep read** of a block-class vector: the height-`Pceil j` digit at on-hull
positions below `m`, the monic `1` at `m`, `0` elsewhere. -/
noncomputable def sweepRead (π : O) (Φ : Polynomial O) (v : HTNode) (N : ℕ)
    (g : Fin v.m → Coeff O Φ.natDegree N) : ℕ → resField Φ :=
  fun j =>
    if hj : j < v.m then
      (if v.OnHull j then blockDigit π Φ (v.Pceil j) N (g ⟨j, hj⟩) else 0)
    else if j = v.m then 1 else 0

/-- **the floored block set** at height `h`: classes with a lift of degree `< d` above the
`h`-floor.  (The free-lift carrier of C.109-iii, without the digit prescription.) -/
def BlockSet (π : O) (Φ : Polynomial O) (h N : ℕ) : Set (Coeff O Φ.natDegree N) :=
  {c | ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
    proj O Φ.natDegree N (fun i => A.coeff i) = c ∧ (h : ℕ∞) ≤ gaussVal A}

/-- the priced refinement: C.109-iii's subtype is the `blockDigit` fibre of `BlockSet`. -/
theorem blockSet_digit_eq_iii (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    {c : Coeff O Φ.natDegree N | c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = {c | ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
          proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
          (h : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = x} := by
  sorry

/-- the priced block count, from C.109-iii. -/
theorem card_blockSet_digit (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    Nat.card {c : Coeff O Φ.natDegree N //
        c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = Nat.card (resField Φ) ^ (N - h - 1) := by
  sorry

/-- the floored block count: summing the uniform priced fibre over the `Q` digit values
(C.109-ii's content, recovered blockwise in the free-lift carrier). -/
theorem card_blockSet (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) :
    Nat.card (BlockSet π Φ h N) = Nat.card (resField Φ) ^ (N - h) := by
  sorry

/-! ### 4. The hull side dictionary from the height profile -/

/-- The on-side height law: along a genuine side, the ceiled heights are affine of slope
`−u/ℓ` (stated addition-form, ℕ-subtraction-free). -/
theorem pceil_on_side (v : HTNode) (hwf : v.WF) {u ℓ : ℕ} (hS : v.IsSide u ℓ)
    {k : ℕ} (hk : k ≤ v.nodeSideDeg u ℓ) :
    v.Pceil ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k) + u * k
      = v.Pceil ((v.nodeSideSet u ℓ).min.getD 0) := by
  sorry

/-- **the synthetic side dictionary**: for a monic degree-`m·d` polynomial whose height
profile has the node floors and vertex exactness, each genuine node side is read off `f`
with matching left endpoint, residual degree, and pinned left height.  (The floors+vertex
core of C.109-iv, needed in BOTH directions of the crux — C.109-iv itself takes full cell
membership, which the backward direction does not yet have.) -/
theorem side_dictionary_of_profile (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    (v : HTNode) (hwf : v.WF)
    {f : Polynomial O} (hmon : f.Monic) (hdeg : f.natDegree = v.m * Φ.natDegree)
    (hfl : ∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j)
    (hvx : ∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞))
    {u ℓ : ℕ} (hS : v.IsSide u ℓ) :
    ∃ hne : (sideSet Φ f u ℓ).Nonempty,
      sideMin Φ f u ℓ hne = (v.nodeSideSet u ℓ).min.getD 0 ∧
      sideDeg Φ f u ℓ hne = v.nodeSideDeg u ℓ ∧
      npHgt Φ f (sideMin Φ f u ℓ hne)
        = ((v.Pceil (sideMin Φ f u ℓ hne) : ℕ) : ℕ∞) := by
  sorry

/-! ### 5. The crux: cell membership ↔ sweep condition + block floors -/

/-- **The crux equivalence.**  Through a componentwise development bridge `E` (C.109a), a
level-`N` class is in the cell iff its sweep read satisfies C.109-v's `SweepCond` and every
block class lies in its floored block set. -/
theorem mem_iff_blocks (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]
    (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    (E : Coeff O (v.m * Φ.natDegree) N ≃ (Fin v.m → Coeff O Φ.natDegree N))
    (hE : ∀ (a : Fin (v.m * Φ.natDegree) → O) (j : Fin v.m) (i : Fin Φ.natDegree),
      E (proj O (v.m * Φ.natDegree) N a) j i
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
            ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ)))
    (c : Coeff O (v.m * Φ.natDegree) N) :
    (∃ a : Fin (v.m * Φ.natDegree) → O,
        proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v)
      ↔ (C109v.SweepCond v (sweepRead π Φ v N (E c))
          ∧ ∀ j : Fin v.m, E c j ∈ BlockSet π Φ (v.Pceil (j : ℕ)) N) := by
  sorry

/-! ### 6. Cardinality glue -/

/-- counting by fibres of a map into a finite base. -/
theorem card_eq_sum_fibers {α β : Type*} [Finite α] [Fintype β] (F : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // F a = b} := by
  sorry

/-- the sweep base is finite (assignments are supported on `≤ m + 1` positions). -/
theorem finite_sweepCond {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (v : HTNode) :
    Finite {r : ℕ → K // C109v.SweepCond v r} := by
  sorry

open Classical in
/-- the exponent arithmetic: the free digits left after pricing are exactly `B_v(N)`
(`hwf`'s `L`-law + `hvis` for the honest ℕ-subtraction). -/
theorem exponent_arith (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    ∑ j ∈ Finset.range v.m,
        (if v.OnHull j then N - v.Pceil j - 1 else N - v.Pceil j) = v.B N := by
  sorry

end Uniformity.Density.Tower.C109asm

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.109 — the exact node cell count** (`(HT-cell)`, `EFF.W12.83/84` step 1).
Statement byte-frozen from the A-C.2 re-signed leanspec block; proof = the A-C.5 assembly
of the five landed layers (module docstring). -/
theorem ht_node_cell_card (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]  -- all derivable from hΦ; binders for elaboration
    (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
        ∃ a : Fin (v.m * Φ.natDegree) → O,
          proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v}
      = Nat.card (resField Φ) ^ v.B N
        * ∏ p ∈ v.sides, sideCensus (resField Φ) (v.sideType p.1 p.2) := by
  sorry

end Uniformity.Density.Tower
