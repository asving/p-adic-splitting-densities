/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G41
import Uniformity.ChapG.G42

/-!
# Uniformity.ChapG.G43 — `decidedCount_split_eq_inert`, W-11's every-window identity

**Chapter G, NODE G.43** (`blueprint/CHAP-G_base_cases_menus.md` §5). *The split/inert symmetry is
not asymptotic.* At EVERY level `N` the two counts are literally equal:

  `decidedCount O 2 splitType N = decidedCount O 2 inertType N`,

for every complete DVR with finite residue field, both residue characteristics. The limit statement
`genuineDensity split = genuineDensity inert` is a corollary of this, not the other way round.

The mechanism is entirely residue-field-level. Both decided sets are the disjoint union of the even
depth strata (G.41 `decidedSet_inert_eq`, G.42 `decidedSet_split_eq`, over the SAME index set
`Finset.range ((N+1)/2)`), and stratum by stratum the two halves have the same size because G.38 and
G.39 are the same equation over the residue field `K`:

  `2·#{p : K × K | AniForm p} + #K = #K·#K = 2·#{p : K × K | SepPair p} + #K`,

i.e. `#{anisotropic pairs} = #{separable-split pairs} = q(q−1)/2`. Cancelling the shared `q^(2k+2r+1)`
and the factor `2` in G.41's and G.42's counting identities gives the per-stratum equality; summing
over `k` gives the theorem.

DEPENDS: G.41 (`decidedSet_inert_eq`, `card_inertStratum`, `card_biUnion_range_of_disjoint`,
`depthSet_disjoint`), G.42 (`decidedSet_split_eq`, `card_splitStratum`) · landed `decidedCount`,
`IsDiscreteValuationRing.exists_irreducible`, `inertStratum`/`splitStratum` (G.31).

**PROOF.**
1. Pick an irreducible `π`.
2. Both strata sit in `depthSet π N (2k)`, and distinct depths are disjoint (`depthSet_disjoint`),
   so the strata are pairwise disjoint in `k` and `card_biUnion_range_of_disjoint` turns each
   decided count into `∑ k ∈ Finset.range ((N+1)/2), Nat.card (stratum π N k)`.
3. Per `k` in range: `k < (N+1)/2` gives `2k+1 ≤ N`, so `N = 2k+1+r` for `r := N − (2k+1)`;
   G.41 and G.42 then read
   `2·#inert + q^(2k+2r+1) = q^(2k+2r+2) = 2·#split + q^(2k+2r+1)`,
   and `Nat.add_right_cancel` + `Nat.eq_of_mul_eq_mul_left two_pos` give `#split = #inert`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **W-11's every-window identity, exactly:** at every level the split-decided and inert-decided
classes are equinumerous — not merely equal in the limit. The mechanism is the residue-field
coincidence `#{anisotropic pairs} = #{separable-split pairs} = q(q−1)/2`. -/
theorem decidedCount_split_eq_inert [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedCount O 2 splitType N = decidedCount O 2 inertType N := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hsplit : decidedCount O 2 splitType N
      = ∑ k ∈ Finset.range ((N + 1) / 2), Nat.card (Menu.splitStratum π N k) := by
    rw [decidedCount, Menu.decidedSet_split_eq hπ N]
    exact Menu.card_biUnion_range_of_disjoint _ _ fun i j hij =>
      (Menu.depthSet_disjoint hπ (show 2 * i ≠ 2 * j by omega)).mono
        (fun _ hc => hc.1) (fun _ hc => hc.1)
  have hinert : decidedCount O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2), Nat.card (Menu.inertStratum π N k) := by
    rw [decidedCount, Menu.decidedSet_inert_eq hπ N]
    exact Menu.card_biUnion_range_of_disjoint _ _ fun i j hij =>
      (Menu.depthSet_disjoint hπ (show 2 * i ≠ 2 * j by omega)).mono
        (fun _ hc => hc.1) (fun _ hc => hc.1)
  rw [hsplit, hinert]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : 2 * k + 1 ≤ N := by
    have := Finset.mem_range.1 hk
    omega
  obtain ⟨r, rfl⟩ : ∃ r, N = 2 * k + 1 + r := ⟨N - (2 * k + 1), by omega⟩
  refine Nat.eq_of_mul_eq_mul_left two_pos (Nat.add_right_cancel (m := residueCard O ^ (2 * k + 2 * r + 1)) ?_)
  rw [Menu.card_splitStratum hπ k r, Menu.card_inertStratum hπ k r]

section AxCheck

#print axioms Uniformity.Density.decidedCount_split_eq_inert

end AxCheck

end Uniformity.Density
