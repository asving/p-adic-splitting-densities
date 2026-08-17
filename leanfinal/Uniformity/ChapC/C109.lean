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

/-- counting by fibres of a map into a finite base. -/
theorem card_eq_sum_fibers {α β : Type*} [Finite α] [Fintype β] (F : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a : α // F a = b} := by
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma]

/-- the priced refinement: C.109-iii's subtype is the `blockDigit` fibre of `BlockSet`. -/
theorem blockSet_digit_eq_iii (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    {c : Coeff O Φ.natDegree N | c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = {c | ∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
          proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
          (h : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = x} := by
  ext c
  simp only [Set.mem_setOf_eq, BlockSet]
  constructor
  · rintro ⟨⟨A, hd, hp, hf⟩, hbd⟩
    refine ⟨A, hd, hp, hf, ?_⟩
    rw [← blockDigit_eq hπ hΦ hh hd, hp]
    exact hbd
  · rintro ⟨A, hd, hp, hf, hres⟩
    refine ⟨⟨A, hd, hp, hf⟩, ?_⟩
    rw [← hp, blockDigit_eq hπ hΦ hh hd]
    exact hres

/-- the priced block count, from C.109-iii. -/
theorem card_blockSet_digit (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) (x : resField Φ) :
    Nat.card {c : Coeff O Φ.natDegree N //
        c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x}
      = Nat.card (resField Φ) ^ (N - h - 1) := by
  have hiff : ∀ c : Coeff O Φ.natDegree N,
      (c ∈ BlockSet π Φ h N ∧ blockDigit π Φ h N c = x)
        ↔ (∃ A : Polynomial O, A.natDegree < Φ.natDegree ∧
            proj O Φ.natDegree N (fun i => A.coeff i) = c ∧
            (h : ℕ∞) ≤ gaussVal A ∧ resMk π Φ h A = x) :=
    fun c => Set.ext_iff.mp (blockSet_digit_eq_iii hπ hΦ hh x) c
  exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans
    (ht_priced_digit_fibre hπ hΦ h N hh x)

set_option maxHeartbeats 1000000 in
/-- the floored block count: summing the uniform priced fibre over the `Q` digit values
(C.109-ii's content, recovered blockwise in the free-lift carrier). -/
theorem card_blockSet (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    {h N : ℕ} (hh : h < N) :
    Nat.card (BlockSet π Φ h N) = Nat.card (resField Φ) ^ (N - h) := by
  classical
  haveI : Fintype (resField Φ) := Fintype.ofFinite _
  haveI : Finite (BlockSet π Φ h N) := Subtype.finite
  have h1 := card_eq_sum_fibers (β := resField Φ)
    (fun c : BlockSet π Φ h N => blockDigit π Φ h N c.1)
  rw [h1]
  have h2 : ∀ x : resField Φ,
      Nat.card {c : BlockSet π Φ h N // blockDigit π Φ h N c.1 = x}
        = Nat.card (resField Φ) ^ (N - h - 1) := by
    intro x
    exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun c => c ∈ BlockSet π Φ h N) (fun c => blockDigit π Φ h N c = x))).trans
      (card_blockSet_digit hπ hΦ hh x)
  rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, ← pow_succ']
  congr 1
  omega

/-! ### 4. The hull side dictionary from the height profile -/

/-- The on-side height law: along a genuine side, the ceiled heights are affine of slope
`−u/ℓ` (stated addition-form, ℕ-subtraction-free). -/
theorem pceil_on_side (v : HTNode) (hwf : v.WF) {u ℓ : ℕ} (hS : v.IsSide u ℓ)
    {k : ℕ} (hk : k ≤ v.nodeSideDeg u ℓ) :
    v.Pceil ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k) + u * k
      = v.Pceil ((v.nodeSideSet u ℓ).min.getD 0) := by
  show v.Pceil (C109v.nsMin v u ℓ + ℓ * k) + u * k = v.Pceil (C109v.nsMin v u ℓ)
  have hmem := C109v.mem_lattice hS.1 hwf hS hk
  have heq := C109v.nv_eq_of_mem hS hmem
  set a := v.Pceil (C109v.nsMin v u ℓ + ℓ * k) with hadef
  set b := v.Pceil (C109v.nsMin v u ℓ) with hbdef
  have hsplit : u * (C109v.nsMin v u ℓ + ℓ * k)
      = u * C109v.nsMin v u ℓ + ℓ * (u * k) := by ring
  have hkey : ℓ * (a + u * k) = ℓ * b := by
    have h1 : ℓ * (a + u * k) = ℓ * a + ℓ * (u * k) := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_left hS.1 hkey

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
  classical
  have hd : 0 < Φ.natDegree := hΦ.pos
  set j₀ := C109v.nsMin v u ℓ with hj₀
  set j₁ := C109v.nsMax v u ℓ with hj₁
  have hj₀m : j₀ ≤ v.m := C109v.le_m_of_mem (C109v.nsMin_mem hS)
  have hj₁m : j₁ ≤ v.m := C109v.le_m_of_mem (C109v.nsMax_mem hS)
  have hmmd : v.m ≤ v.m * Φ.natDegree := Nat.le_mul_of_pos_right _ hd
  set V := ℓ * v.Pceil j₀ + u * j₀ with hV
  have hVle : ∀ i, i ≤ v.m → V ≤ ℓ * v.Pceil i + u * i := fun i hi =>
    C109v.nv_le_of_mem (C109v.nsMin_mem hS) hi
  have hsmultop : ℓ • (⊤ : ℕ∞) = ⊤ := by
    rw [nsmul_eq_mul]
    exact WithTop.mul_top (Nat.cast_ne_zero.mpr hS.1.ne')
  have htop : ∀ j, v.m < j → npHgt Φ f j = ⊤ := by
    intro j hj
    have hz : dev Φ f j = 0 := dev_eq_zero_of_lt hΦ.monic hd f j
      (by rw [hdeg]; exact (Nat.mul_lt_mul_right hd).2 hj)
    rw [npHgt, hz]
    exact gaussVal_eq_top_iff.2 rfl
  have hWcast : ∀ (j H : ℕ), npHgt Φ f j = (H : ℕ∞) →
      ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    intro j H hH
    rw [hH, nsmul_eq_mul]
    push_cast
    ring
  have hsupp : suppVal Φ f u ℓ = (V : ℕ∞) := by
    apply le_antisymm
    · refine le_trans (Finset.inf_le (Finset.mem_range.2
        (lt_of_le_of_lt (le_trans hj₀m (hdeg ▸ hmmd)) (Nat.lt_succ_self _)))) ?_
      rw [hWcast j₀ (v.Pceil j₀) (hvx j₀ hj₀m (C109v.isVertex_nsMin hS))]
    · refine Finset.le_inf ?_
      intro j _
      rcases le_or_gt j v.m with hjm | hjm
      · rcases eq_or_ne (npHgt Φ f j) ⊤ with hT | hT
        · rw [hT, hsmultop, top_add]
          exact le_top
        · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
          have hPH : v.Pceil j ≤ H := by
            have := hfl j hjm
            rw [← hH] at this
            exact_mod_cast this
          rw [hWcast j H hH.symm]
          have : V ≤ ℓ * H + u * j :=
            le_trans (hVle j hjm)
              (Nat.add_le_add_right (Nat.mul_le_mul_left ℓ hPH) _)
          exact_mod_cast this
      · rw [htop j hjm, hsmultop, top_add]
        exact le_top
  -- the two endpoints are on the side of `f`
  have hvertexW : ∀ j, j ∈ v.nodeSideSet u ℓ → v.IsVertex j → OnSide Φ f u ℓ j := by
    intro j hjmem hjv
    have hjm := C109v.le_m_of_mem hjmem
    rw [OnSide, hsupp, hWcast j (v.Pceil j) (hvx j hjm hjv)]
    exact_mod_cast (C109v.nv_eq_of_mem hS hjmem)
  have hj0on : OnSide Φ f u ℓ j₀ :=
    hvertexW j₀ (C109v.nsMin_mem hS) (C109v.isVertex_nsMin hS)
  have hj1on : OnSide Φ f u ℓ j₁ :=
    hvertexW j₁ (C109v.nsMax_mem hS) (C109v.isVertex_nsMax hS)
  have hj0mem : j₀ ∈ sideSet Φ f u ℓ :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.2 (by omega), hj0on⟩
  have hj1mem : j₁ ∈ sideSet Φ f u ℓ :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.2 (by omega), hj1on⟩
  -- containment in the node side set
  have hsub : ∀ j, j ∈ sideSet Φ f u ℓ → j ∈ v.nodeSideSet u ℓ := by
    intro j hjmem
    have hon : OnSide Φ f u ℓ j := onSide_of_mem_sideSet hjmem
    rw [OnSide, hsupp] at hon
    have hjm : j ≤ v.m := by
      by_contra hc
      rw [htop j (by omega), hsmultop, top_add] at hon
      exact (WithTop.top_ne_coe (α := ℕ)) hon
    have hT : npHgt Φ f j ≠ ⊤ := by
      intro hT
      rw [hT, hsmultop, top_add] at hon
      exact (WithTop.top_ne_coe (α := ℕ)) hon
    obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
    have hPH : v.Pceil j ≤ H := by
      have := hfl j hjm
      rw [← hH] at this
      exact_mod_cast this
    rw [hWcast j H hH.symm] at hon
    have hnat : ℓ * H + u * j = V := by exact_mod_cast hon
    have hjeq : ℓ * v.Pceil j + u * j = V := by
      have h1 : ℓ * v.Pceil j + u * j ≤ ℓ * H + u * j :=
        Nat.add_le_add_right (Nat.mul_le_mul_left ℓ hPH) _
      have h2 := hVle j hjm
      omega
    exact C109v.mem_nodeSideSet.mpr ⟨hjm, fun i hi => by
      rw [hjeq]
      exact hVle i hi⟩
  have hne : (sideSet Φ f u ℓ).Nonempty := ⟨j₀, hj0mem⟩
  have hminEq : sideMin Φ f u ℓ hne = j₀ :=
    le_antisymm (Finset.min'_le _ _ hj0mem)
      (Finset.le_min' _ _ _ fun j hj => C109v.nsMin_le_of_mem hS (hsub j hj))
  have hmaxEq : sideMax Φ f u ℓ hne = j₁ :=
    le_antisymm (Finset.max'_le _ _ _ fun j hj => C109v.le_nsMax_of_mem hS (hsub j hj))
      (Finset.le_max' _ _ hj1mem)
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact hminEq
  · rw [sideDeg, hminEq, hmaxEq, C109v.nodeSideDeg_eq]
  · rw [hminEq]
    exact hvx j₀ hj₀m (C109v.isVertex_nsMin hS)

/-- the top development coefficient of a monic degree-`m·d` polynomial is `1`
(B.05's expansion + a leading-coefficient comparison with the assembled twin). -/
theorem dev_top_of_monic {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} {f : Polynomial O} (hmon : f.Monic) (hdeg : f.natDegree = m * Φ.natDegree) :
    dev Φ f m = 1 := by
  classical
  set A : Fin m → Polynomial O := fun j => dev Φ f (j : ℕ) with hA
  have hdegA : ∀ j : Fin m, (A j).degree < Φ.degree := fun j => degree_dev_lt hΦm hΦd f _
  obtain ⟨a, ha⟩ := assemble_eq_monicPoly hΦm hΦd A hdegA
  set g := ∑ i : Fin m, A i * Φ ^ (i : ℕ) + Φ ^ m with hg
  have hgmon : g.Monic := ha ▸ monicPoly_monic a
  have hgdeg : g.natDegree = m * Φ.natDegree := by rw [← ha, monicPoly_natDegree]
  have hexp : ∑ j ∈ Finset.range (m + 1), dev Φ f j * Φ ^ j = f :=
    sum_dev_eq hΦm hΦd f
      (by rw [hdeg]; exact (Nat.mul_lt_mul_right hΦd).2 (Nat.lt_succ_self m))
  have h1 : f = (∑ i : Fin m, A i * Φ ^ (i : ℕ)) + dev Φ f m * Φ ^ m := by
    conv_lhs => rw [← hexp]
    rw [Finset.sum_range_succ, Finset.sum_range fun j => dev Φ f j * Φ ^ j]
  have hfg : f - g = (dev Φ f m - 1) * Φ ^ m := by
    conv_lhs => rw [h1, hg]
    ring
  by_contra hne
  have hsub : dev Φ f m - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hdegfg : (f - g).degree < ((m * Φ.natDegree : ℕ) : WithBot ℕ) := by
    have h1 : f.degree = g.degree := by
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
        Polynomial.degree_eq_natDegree hgmon.ne_zero, hdeg, hgdeg]
    have h2 := Polynomial.degree_sub_lt h1 hmon.ne_zero (by rw [hmon, hgmon])
    rwa [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg] at h2
  have hΦm0 : Φ ≠ 0 := hΦm.ne_zero
  have hdegge : ((m * Φ.natDegree : ℕ) : WithBot ℕ) ≤ (f - g).degree := by
    rw [hfg, Polynomial.degree_mul]
    have h3 : (Φ ^ m).degree = ((m * Φ.natDegree : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree hΦm0, nsmul_eq_mul]
      exact_mod_cast rfl
    rw [h3]
    calc ((m * Φ.natDegree : ℕ) : WithBot ℕ)
        = 0 + ((m * Φ.natDegree : ℕ) : WithBot ℕ) := (zero_add _).symm
      _ ≤ (dev Φ f m - 1).degree + ((m * Φ.natDegree : ℕ) : WithBot ℕ) :=
          add_le_add (Polynomial.zero_le_degree_iff.mpr hsub) le_rfl
  exact absurd hdegfg (not_lt.2 hdegge)

/-- the height-`0` digit read of the constant `1` is `1`. -/
theorem resMk_one {Φ : Polynomial O} (hπ : Irreducible π) :
    resMk π Φ 0 (1 : Polynomial O) = 1 := by
  have hdig : digPoly π 0 (1 : Polynomial O) = 1 := by
    ext i
    rw [digPoly_coeff hπ, Polynomial.coeff_one, Polynomial.coeff_one]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [if_pos rfl, if_pos rfl, digAt_zero, map_one]
    · rw [if_neg hi, if_neg hi, digAt_zero, map_zero]
  rw [resMk, hdig, map_one]

/-- **the residual polynomial as the priced-digit sweep**: under the profile, `resPoly`'s
`k`-th coefficient is the height-`Pceil` digit of the development block at the side's `k`-th
lattice abscissa. -/
theorem resPoly_eq_sweep (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    (v : HTNode) (hwf : v.WF)
    {f : Polynomial O} (hmon : f.Monic) (hdeg : f.natDegree = v.m * Φ.natDegree)
    (hfl : ∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j)
    (hvx : ∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞))
    {u ℓ : ℕ} (hS : v.IsSide u ℓ)
    (hne : (sideSet Φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hpin : npHgt Φ f (sideMin Φ f u ℓ hne) = (H₀ : ℕ∞)) :
    resPoly π Φ f u ℓ hne H₀
      = ∑ k ∈ Finset.range (v.nodeSideDeg u ℓ + 1),
          Polynomial.C (resMk π Φ (v.Pceil ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k))
              (dev Φ f ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k)))
            * Polynomial.X ^ k := by
  obtain ⟨hne', hmin, hdeg', hpin'⟩ :=
    side_dictionary_of_profile hπ hΦ v hwf hmon hdeg hfl hvx hS
  have hH₀ : H₀ = v.Pceil ((v.nodeSideSet u ℓ).min.getD 0) := by
    have h1 : npHgt Φ f (sideMin Φ f u ℓ hne) = ((v.Pceil (sideMin Φ f u ℓ hne) : ℕ) : ℕ∞) := by
      have : sideMin Φ f u ℓ hne = sideMin Φ f u ℓ hne' := rfl
      rw [this, hpin']
    rw [hpin] at h1
    have h2 : H₀ = v.Pceil (sideMin Φ f u ℓ hne) := by exact_mod_cast h1
    rw [h2]
    exact congrArg v.Pceil hmin
  rw [resPoly]
  have hsd : sideDeg Φ f u ℓ hne = v.nodeSideDeg u ℓ := hdeg'
  rw [hsd]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ v.nodeSideDeg u ℓ := by rw [Finset.mem_range] at hk; omega
  have hlaw := pceil_on_side v hwf hS hkd
  have hmin2 : sideMin Φ f u ℓ hne = (v.nodeSideSet u ℓ).min.getD 0 := hmin
  have hheight : H₀ - u * k = v.Pceil ((v.nodeSideSet u ℓ).min.getD 0 + ℓ * k) := by
    rw [hH₀]; omega
  rw [resCoeff, hmin2, hheight]

theorem dev_natDegree_lt {Φ : Polynomial O} (hΦ : IsKey Φ) (f : Polynomial O) (j : ℕ) :
    (dev Φ f j).natDegree < Φ.natDegree := by
  rcases eq_or_ne (dev Φ f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hΦ.pos
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0,
      ← Polynomial.degree_eq_natDegree hΦ.monic.ne_zero]
    exact degree_dev_lt hΦ.monic hΦ.pos f j

theorem gaussVal_one : gaussVal (1 : Polynomial O) = 0 := by
  rw [gaussVal]
  simp [Polynomial.natDegree_one, Polynomial.coeff_one, addVal_one]

/-- **the sweep read is the priced-digit sum**: at any side, the polynomial `resOf` of the
sweep read of the block classes of `f` is the sum of the `resMk` digit reads of `f`'s
development blocks along the side's lattice. -/
theorem resOf_sweepRead_eq (hπ : Irreducible π) {Φ : Polynomial O} (hΦ : IsKey Φ)
    (v : HTNode) (hwf : v.WF) {N : ℕ} (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    {f : Polynomial O} (hmon : f.Monic) (hdegf : f.natDegree = v.m * Φ.natDegree)
    (g : Fin v.m → Coeff O Φ.natDegree N)
    (hg : ∀ j : Fin v.m, g j = proj O Φ.natDegree N (fun i => (dev Φ f (j : ℕ)).coeff i))
    {U L : ℕ} (hS : v.IsSide U L) :
    C109v.resOf v (sweepRead π Φ v N g) U L
      = ∑ k ∈ Finset.range (v.nodeSideDeg U L + 1),
          Polynomial.C (resMk π Φ (v.Pceil ((v.nodeSideSet U L).min.getD 0 + L * k))
              (dev Φ f ((v.nodeSideSet U L).min.getD 0 + L * k)))
            * Polynomial.X ^ k := by
  classical
  rw [C109v.resOf]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ v.nodeSideDeg U L := by rw [Finset.mem_range] at hk; omega
  have hpmem := C109v.mem_lattice hS.1 hwf hS hkd
  have hpm : C109v.nsMin v U L + L * k ≤ v.m := C109v.le_m_of_mem hpmem
  have hpoh : v.OnHull (C109v.nsMin v U L + L * k) := C109v.onHull_of_mem hS.1 hpmem
  have hcoef : sweepRead π Φ v N g (C109v.nsMin v U L + L * k)
      = resMk π Φ (v.Pceil (C109v.nsMin v U L + L * k))
          (dev Φ f (C109v.nsMin v U L + L * k)) := by
    rcases eq_or_lt_of_le hpm with heq | hlt
    · rw [heq]
      show (if hj : v.m < v.m then _ else if v.m = v.m then 1 else 0) = _
      rw [dif_neg (lt_irrefl v.m), if_pos rfl, hwf.1,
        dev_top_of_monic hΦ.monic hΦ.pos hmon hdegf, resMk_one hπ]
    · show (if hj : C109v.nsMin v U L + L * k < v.m then _ else _) = _
      rw [dif_pos hlt, if_pos hpoh, hg ⟨_, hlt⟩]
      exact blockDigit_eq hπ hΦ (hvis _ (by omega)) (dev_natDegree_lt hΦ f _)
  rw [hcoef]
  rfl

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
  classical
  set r := sweepRead π Φ v N (E c) with hr
  have hrm : r v.m = 1 := by
    show (if hj : v.m < v.m then _ else if v.m = v.m then 1 else 0) = 1
    rw [dif_neg (lt_irrefl v.m), if_pos rfl]
  have hrhigh : ∀ j, v.m < j → r j = 0 := by
    intro j hj
    show (if hj' : j < v.m then _ else if j = v.m then 1 else 0) = 0
    rw [dif_neg (by omega), if_neg (by omega)]
  have hroff : ∀ j, j < v.m → ¬ v.OnHull j → r j = 0 := by
    intro j hj hoh
    show (if hj' : j < v.m then (if v.OnHull j then _ else 0) else _) = 0
    rw [dif_pos hj, if_neg hoh]
  constructor
  · rintro ⟨a, hpa, hcell⟩
    obtain ⟨hmon, hdegf, hfl, hvx, hsides⟩ := hcell
    set f := monicPoly a with hf
    have hEcj : ∀ j : Fin v.m,
        E c j = proj O Φ.natDegree N (fun i => (dev Φ f (j : ℕ)).coeff i) := by
      intro j
      funext i
      rw [← hpa]
      exact hE a j i
    have hread : ∀ (j : ℕ) (hj : j < v.m), v.OnHull j →
        r j = resMk π Φ (v.Pceil j) (dev Φ f j) := by
      intro j hj hoh
      show (if hj' : j < v.m then (if v.OnHull j then
        blockDigit π Φ (v.Pceil j) N (E c ⟨j, hj'⟩) else 0) else _) = _
      rw [dif_pos hj, if_pos hoh, hEcj ⟨j, hj⟩]
      exact blockDigit_eq hπ hΦ (hvis j (by omega)) (dev_natDegree_lt hΦ f j)
    refine ⟨⟨?_, hroff, hrm, ?_, ?_⟩, ?_⟩
    · -- support clause
      intro j hjne
      by_contra hc
      exact hjne (hrhigh j (by omega))
    · -- vertex clause
      intro j hjm hv
      rcases eq_or_lt_of_le hjm with heq | hlt
      · rw [heq, hrm]
        exact one_ne_zero
      · rw [hread j hlt (C109v.onHull_of_isVertex hv)]
        exact (resMk_ne_zero_iff_gaussVal hπ hΦ (degree_dev_lt hΦ.monic hΦ.pos f j)
          (hfl j hjm)).mpr (hvx j hjm hv)
    · -- side-type clause
      intro U L hmem
      have hS : v.IsSide U L := C109v.isSide_of_mem hwf hmem
      obtain ⟨hne, hmin, hdeg', hpin'⟩ :=
        side_dictionary_of_profile hπ hΦ v hwf hmon hdegf hfl hvx hS
      have htype := hsides U L hS.1 hS.2.1 hmem hne
        (v.Pceil (sideMin Φ f U L hne)) hpin'
      rw [resPoly_eq_sweep hπ hΦ v hwf hmon hdegf hfl hvx hS hne hpin'] at htype
      rw [← resOf_sweepRead_eq hπ hΦ v hwf hvis hmon hdegf (E c) hEcj hS] at htype
      exact htype
    · -- block floors
      intro j
      exact ⟨dev Φ f (j : ℕ), dev_natDegree_lt hΦ f _, (hEcj j).symm,
        hfl (j : ℕ) (le_of_lt j.isLt)⟩
  · rintro ⟨hsweep, hblocks⟩
    choose A hAdeg hAproj hAfl using hblocks
    have hdegA : ∀ j : Fin v.m, (A j).degree < Φ.degree := by
      intro j
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      rw [Polynomial.degree_eq_natDegree hΦ.monic.ne_zero]
      exact_mod_cast hAdeg j
    obtain ⟨a, ha⟩ := assemble_eq_monicPoly hΦ.monic hΦ.pos A hdegA
    obtain ⟨hdevlow, hdevtop⟩ := dev_assemble hΦ.monic hΦ.pos A hdegA
    set f := monicPoly a with hf
    have hgf : f = ∑ i : Fin v.m, A i * Φ ^ (i : ℕ) + Φ ^ v.m := ha
    have hdevf : ∀ j : Fin v.m, dev Φ f (j : ℕ) = A j := by
      intro j; rw [hgf]; exact hdevlow j
    have hdevfm : dev Φ f v.m = 1 := by rw [hgf]; exact hdevtop
    have hmon : f.Monic := monicPoly_monic a
    have hdegf : f.natDegree = v.m * Φ.natDegree := monicPoly_natDegree a
    have hEcj : ∀ j : Fin v.m,
        E c j = proj O Φ.natDegree N (fun i => (dev Φ f (j : ℕ)).coeff i) := by
      intro j
      rw [hdevf j]
      exact (hAproj j).symm
    -- the height profile of the assembled member
    have hfl : ∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j := by
      intro j hjm
      rcases eq_or_lt_of_le hjm with heq | hlt
      · rw [heq, npHgt, hdevfm, gaussVal_one, hwf.1]
        exact le_of_eq Nat.cast_zero
      · rw [npHgt, hdevf ⟨j, hlt⟩]
        exact hAfl ⟨j, hlt⟩
    have hvx : ∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞) := by
      intro j hjm hv
      rcases eq_or_lt_of_le hjm with heq | hlt
      · rw [heq, npHgt, hdevfm, gaussVal_one, hwf.1]
        exact Nat.cast_zero.symm
      · have hrne : r j ≠ 0 := hsweep.2.2.2.1 j hjm hv
        have hoh : v.OnHull j := C109v.onHull_of_isVertex hv
        have hrd : r j = resMk π Φ (v.Pceil j) (A ⟨j, hlt⟩) := by
          show (if hj' : j < v.m then (if v.OnHull j then
            blockDigit π Φ (v.Pceil j) N (E c ⟨j, hj'⟩) else 0) else _) = _
          rw [dif_pos hlt, if_pos hoh, hEcj ⟨j, hlt⟩, hdevf ⟨j, hlt⟩]
          exact blockDigit_eq hπ hΦ (hvis j (by omega)) (by
            rw [← hdevf ⟨j, hlt⟩]; exact dev_natDegree_lt hΦ f j)
        rw [hrd] at hrne
        have := (resMk_ne_zero_iff_gaussVal hπ hΦ (hdegA ⟨j, hlt⟩)
          (hAfl ⟨j, hlt⟩)).mp hrne
        rw [npHgt, hdevf ⟨j, hlt⟩]
        exact this
    refine ⟨a, ?_, hmon, hdegf, hfl, hvx, ?_⟩
    · -- proj a = c through E's injectivity
      refine E.injective ?_
      funext j i
      rw [hE a j i, hEcj j]
      rfl
    · -- the side-type clause of the cell
      intro U L hL hcop hmem hne H₀ hpin
      have hS : v.IsSide U L := C109v.isSide_of_mem hwf hmem
      rw [resPoly_eq_sweep hπ hΦ v hwf hmon hdegf hfl hvx hS hne hpin]
      rw [← resOf_sweepRead_eq hπ hΦ v hwf hvis hmon hdegf (E c) hEcj hS]
      exact hsweep.2.2.2.2 U L hmem

/-! ### 6. Cardinality glue -/

/-- the sweep base is finite (assignments are supported on `≤ m + 1` positions). -/
theorem finite_sweepCond {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (v : HTNode) :
    Finite {r : ℕ → K // C109v.SweepCond v r} := by
  have hinj : Function.Injective (fun (r : {r : ℕ → K // C109v.SweepCond v r}) =>
      (fun i : Fin (v.m + 1) => r.1 (i : ℕ))) := by
    intro r r' h
    refine Subtype.ext (funext fun j => ?_)
    rcases le_or_gt j v.m with hj | hj
    · exact congrFun h ⟨j, by omega⟩
    · have h1 : r.1 j = 0 := by
        by_contra hc
        exact absurd (r.2.1 j hc) (by omega)
      have h2 : r'.1 j = 0 := by
        by_contra hc
        exact absurd (r'.2.1 j hc) (by omega)
      rw [h1, h2]
  exact Finite.of_injective _ hinj

open Classical in
/-- the exponent arithmetic: the free digits left after pricing are exactly `B_v(N)`
(`hwf`'s `L`-law + `hvis` for the honest ℕ-subtraction). -/
theorem exponent_arith (v : HTNode) (hwf : v.WF) (N : ℕ)
    (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    ∑ j ∈ Finset.range v.m,
        (if v.OnHull j then N - v.Pceil j - 1 else N - v.Pceil j) = v.B N := by
  have hterm : ∀ j ∈ Finset.range v.m,
      (if v.OnHull j then N - v.Pceil j - 1 else N - v.Pceil j)
        = (N - v.Pceil j) - (if v.OnHull j then 1 else 0) := by
    intro j _
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hterm]
  have hsum1 : (∑ j ∈ Finset.range v.m,
        ((N - v.Pceil j) - (if v.OnHull j then 1 else 0)))
      + (∑ j ∈ Finset.range v.m, (if v.OnHull j then 1 else 0))
      = ∑ j ∈ Finset.range v.m, (N - v.Pceil j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hvis j (by rw [Finset.mem_range] at hj; omega)
    split_ifs <;> omega
  have hLcount : (∑ j ∈ Finset.range v.m, (if v.OnHull j then 1 else 0)) = v.L := by
    rw [hwf.2.2.1, Finset.card_filter]
  have hsum2 : (∑ j ∈ Finset.range v.m, (N - v.Pceil j))
      + ∑ j ∈ Finset.range v.m, v.Pceil j = v.m * N := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun j hj => (by
      have := hvis j (by rw [Finset.mem_range] at hj; omega)
      omega : (N - v.Pceil j) + v.Pceil j = N)]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hB : v.B N = v.m * N - (∑ j ∈ Finset.range v.m, v.Pceil j) - v.L := rfl
  omega

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
