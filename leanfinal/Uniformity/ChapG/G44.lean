/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G20
import Uniformity.ChapG.G41

/-!
# Uniformity.ChapG.G44 — the level-`N` decided proportions in closed form

**Chapter G, NODE G.44** (`blueprint/CHAP-G_base_cases_menus.md` §5). *The two decided sequences,
written as explicit finite geometric partial sums.* For every complete DVR with finite residue
field and every level `N`:

  `decidedSeq O 2 ramType   N = ∑_{j < N/2}     (q−1)/q^(2j+2)`
  `decidedSeq O 2 inertType N = ∑_{k < (N+1)/2} (q−1)/(2·q^(2k+1))`

Together with G.43 (`decidedCount_split_eq_inert`, hence the same formula for `splitType`) and G.37
(`undecidedSeq_two_eq = q^(−N)`) these are the whole `n = 2` census at every finite level; G.45's
`tendsto_geom_partial` turns them into the limits `1/(q+1)`, `q/(2(q+1))`, `q/(2(q+1))`.

**⚠ STATEMENT CORRECTION (adjudicated 2026-08-15, before landing).** The blueprint and the
`leanspec` stub sign the RAM index set as `Finset.range ((N+1)/2)`. **That is FALSE at odd `N`**, and
the smallest witness is `N = 1`: G.31's `decidedSet_ram_eq` makes `decidedSet O 2 ramType 1` the
union over `Finset.range 1` of `depthSet π 1 1`, which is EMPTY by G.30a (`1 ≤ 2·0+1`), so
`decidedSeq O 2 ramType 1 = 0`; the signed right-hand side is `(q−1)/q² > 0` because `q ≥ 2`. The
genuine ram index set is `{j | 2j+2 ≤ N} = Finset.range (N/2)` — a ram class needs a full ODD depth
`2j+1` *plus* the room `2j+2 ≤ N` that G.25 requires to certify it. A machine-checked refutation of
the signed form (`decidedSeq ℤ_[2] 2 ramType 1 = 0` versus `1/4`) accompanies this node in the
landing report; it is not committed. The INERT index set `Finset.range ((N+1)/2)` is CORRECT as
signed (`k < (N+1)/2 ↔ 2k+1 ≤ N`, which is exactly what G.41's counting identity needs).

DEPENDS: G.41 (`decidedSet_inert_eq`, `card_inertStratum`, `card_biUnion_range_of_disjoint`,
`depthSet_disjoint`) · landed `decidedSet_ram_eq` (G.31), `card_depthSet` (G.20),
`depthSet_odd_eq_empty` (G.30a), `decidedSeq`, `qpow_ne`,
`IsDiscreteValuationRing.exists_irreducible`.

**PROOF (ram).** `decidedSet_ram_eq` presents the ram-decided set as a union over `Finset.range N`
of odd depth strata; the strata are pairwise disjoint (`depthSet_disjoint`), so
`card_biUnion_range_of_disjoint` gives `∑_{j<N} #(depthSet π N (2j+1))`. The terms with `j ≥ N/2`
vanish (`depthSet_odd_eq_empty`, since `N/2 ≤ j → N ≤ 2j+1`), so `Finset.sum_subset` trims the
index set to `Finset.range (N/2)`. For `j < N/2` write `N = (2j+1)+1+r` and read G.20:
`#(depthSet π N (2j+1)) + q^(2j+2r+2) = q^(2j+2r+3)`. Cast to `ℝ`, cross-multiply against
`q^(2N) = q^(4j+2r+4)`, and one `linear_combination q^(2j+2) · (that identity)` closes each summand.
Everything stays additive — no `ℕ` subtraction anywhere.

**PROOF (inert).** Same skeleton with `decidedSet_inert_eq` (whose index set needs no trimming) and
G.41's `2·#(inertStratum) + q^(2k+2r+1) = q^(2k+2r+2)` at `N = 2k+1+r`; the extra factor `2` is what
puts the `2` in the denominator `2·q^(2k+1)`.

**Arithmetic anchors** (independently verified): at `N = 1`, `#inertStratum π 1 0 = (q²−q)/2 =
#splitStratum`, ram `= 0`, undecided `= q`, total `q² − q + q = q²` ✓. At `N = 2`, inert `= split =
(q⁴−q³)/2`, ram `= q³−q²`, undecided `= q²`, total `q⁴` ✓.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.44, ram half.** The level-`N` ram-decided proportion as an explicit geometric partial sum.
The index set is `Finset.range (N / 2)`, i.e. `{j | 2j+2 ≤ N}` — see the CORRECTION note in this
file's module docstring for why the signed `Finset.range ((N+1)/2)` is false at odd `N`. -/
theorem decidedSeq_two_ram_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 ramType N
      = ∑ j ∈ Finset.range (N / 2),
          ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ (2 * j + 2) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hcount : decidedCount O 2 ramType N
      = ∑ j ∈ Finset.range (N / 2), Nat.card (Menu.depthSet π N (2 * j + 1)) := by
    have h1 : decidedCount O 2 ramType N
        = ∑ j ∈ Finset.range N, Nat.card (Menu.depthSet π N (2 * j + 1)) := by
      rw [decidedCount, Menu.decidedSet_ram_eq hπ N]
      exact Menu.card_biUnion_range_of_disjoint _ _ fun i j hij =>
        Menu.depthSet_disjoint hπ (show 2 * i + 1 ≠ 2 * j + 1 by omega)
    rw [h1]
    refine (Finset.sum_subset (s₁ := Finset.range (N / 2)) (s₂ := Finset.range N)
      (Finset.range_subset_range.2 (Nat.div_le_self N 2)) ?_).symm
    intro x _ hx
    have hx' : N / 2 ≤ x := by simpa using hx
    rw [Menu.depthSet_odd_eq_empty hπ (show N ≤ 2 * x + 1 by omega)]
    simp
  rw [decidedSeq, hcount, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : 2 * j + 2 ≤ N := by
    have := Finset.mem_range.1 hj
    omega
  obtain ⟨r, rfl⟩ : ∃ r, N = 2 * j + 1 + 1 + r := ⟨N - (2 * j + 2), by omega⟩
  have hR : (Nat.card (Menu.depthSet π (2 * j + 1 + 1 + r) (2 * j + 1)) : ℝ)
      + (residueCard O : ℝ) ^ (2 * j + 1 + 2 * r + 1)
      = (residueCard O : ℝ) ^ (2 * j + 1 + 2 * r + 2) := by
    exact_mod_cast Menu.card_depthSet hπ (2 * j + 1) r
  rw [div_eq_div_iff (qpow_ne _) (qpow_ne _)]
  linear_combination (residueCard O : ℝ) ^ (2 * j + 2) * hR

/-- **G.44, inert half.** The level-`N` inert-decided proportion as an explicit geometric partial
sum. Here the signed index set `Finset.range ((N+1)/2)` is exactly right: `k < (N+1)/2 ↔ 2k+1 ≤ N`,
the hypothesis of G.41's count. By G.43 the same formula holds for `splitType`. -/
theorem decidedSeq_two_inert_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (2 * (residueCard O : ℝ) ^ (2 * k + 1)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hcount : decidedCount O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2), Nat.card (Menu.inertStratum π N k) := by
    rw [decidedCount, Menu.decidedSet_inert_eq hπ N]
    exact Menu.card_biUnion_range_of_disjoint _ _ fun i j hij =>
      (Menu.depthSet_disjoint hπ (show 2 * i ≠ 2 * j by omega)).mono
        (fun _ hc => hc.1) (fun _ hc => hc.1)
  rw [decidedSeq, hcount, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : 2 * k + 1 ≤ N := by
    have := Finset.mem_range.1 hk
    omega
  obtain ⟨r, rfl⟩ : ∃ r, N = 2 * k + 1 + r := ⟨N - (2 * k + 1), by omega⟩
  have hR : 2 * (Nat.card (Menu.inertStratum π (2 * k + 1 + r) k) : ℝ)
      + (residueCard O : ℝ) ^ (2 * k + 2 * r + 1)
      = (residueCard O : ℝ) ^ (2 * k + 2 * r + 2) := by
    exact_mod_cast Menu.card_inertStratum hπ k r
  rw [div_eq_div_iff (qpow_ne _) (mul_ne_zero two_ne_zero (qpow_ne _))]
  linear_combination (residueCard O : ℝ) ^ (2 * k + 1) * hR

section AxCheck

#print axioms Uniformity.Density.decidedSeq_two_ram_eq
#print axioms Uniformity.Density.decidedSeq_two_inert_eq

end AxCheck

end Uniformity.Density
