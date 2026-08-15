/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G12
import Uniformity.ChapG.G19
import Uniformity.ChapG.G25
import Uniformity.ChapG.G30
import Uniformity.ChapG.G30a
import Uniformity.ChapG.G33

/-!
# Uniformity.ChapG.G31 — `inertStratum` / `splitStratum` / `decidedSet_ram_eq`

**Chapter G, NODE G.31** (`blueprint/CHAP-G_base_cases_menus.md` §5). *The level-`N` partition,
ram half.* The `ramType`-decided classes are exactly the union of the ODD depth strata:
`decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2j+1)`. The two even-stratum
halves `inertStratum`/`splitStratum` are defined here; their companion identities
`decidedSet_inert_eq`, `decidedSet_split_eq` are folded into G.41/G.42, per the node's SIZE note.

**Dependency gap CURED at blueprint AMENDMENT 2026-08-15 §A-7.** Wave-3 booked this node BLOCKED:
the index set `Finset.range N` runs `j = 0 … N−1`, i.e. odd depths up to `2N−1`, while only
`2j+1 < N` is a genuine stratum, so the ⊇ inclusion needs the overshoot to contribute nothing.
The supplier is the new micro-node **G.30a** `depthSet_odd_eq_empty` (`N ≤ 2j+1 →
depthSet π N (2j+1) = ∅`), used in the last branch below. The general shape the fleet asked for
(`depthSet π N t = ∅` for every `t ≥ N`) is FALSE at even `t` in residue characteristic 2 — see
§A-7 and `G30a.lean`'s docstring — but the union here is odd-indexed, so the true odd form
suffices and the node's STATEMENT needed no repair.

DEPENDS: G.12, G.19, G.25, G.30, G.30a, G.33 · landed `decidedSet` (`GenuineDensity.lean:74`),
`proj_surjective`, `exists_max_step` (`Drainage.lean:556`), `Tang_zero`, `splitType_ne_ramType`,
`inertType_ne_ramType`. (The blueprint's DEPENDS listed G.29, `decidedSet_disjoint`,
`typeOf_two_cases`, `undecidedSet`; the landed route uses none of them — see §A-7's corrected
DEPENDS. In particular step 2 needs only G.33's split lift, not the G.33/G.34 pair: one lift of
the wrong type already contradicts ram-decidedness.)

**PROOF.**
1. (⊆) let `c` be ram-decided and `a` any lift. No centre of `a` reaches depth `N`: G.33 would
   turn such a centre into a `splitType` lift of the same class, contradicting decidedness via
   `splitType_ne_ramType`.
2. `exists_max_step` on `Q t := ∃ γ, Tang π a t γ` gives a maximal depth `t < N`; `c ∈ depthSet
   π N t` (the maximality transfers across lifts by G.12, using `t + 1 ≤ N`).
3. G.30 at that `t`: the even branch makes `c` inert- or split-decided, contradicting
   ram-decidedness directly (no need for `decidedSet_disjoint`); so `t = 2j+1`, and `j < N`.
4. (⊇) `2j+2 ≤ N`: G.25. Otherwise `N ≤ 2j+1` and the stratum is empty by G.30a.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- The inert half of an even stratum. -/
def inertStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 inertType N c}

/-- The split half of an even stratum. -/
def splitStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 splitType N c}

/-- **The level-`N` partition, ram half.** A class is `ramType`-decided at level `N` exactly
when its depth is odd and below the window. The index set `Finset.range N` overshoots the
genuine strata (`2j+1 < N`); the overshoot is empty by G.30a. -/
theorem decidedSet_ram_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2 * j + 1) := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    have hnt : ¬ ∃ γ, Tang π a N γ := by
      rintro ⟨γ, hγ⟩
      obtain ⟨b, hb, hbty⟩ := exists_split_lift hπ hγ
      exact splitType_ne_ramType (hbty.symm.trans (hc b (hb.trans ha)))
    obtain ⟨t, htlt, hPt, hmax⟩ :=
      exists_max_step (Q := fun t => ∃ γ, Tang π a t γ) ⟨0, Tang_zero π a 0⟩ N hnt
    have hmem : c ∈ depthSet π N t := by
      refine ⟨?_, ?_⟩
      · obtain ⟨γ, hγ⟩ := hPt
        exact ⟨a, ha, γ, hγ⟩
      · rintro ⟨b, hb, γ', hγ'⟩
        exact hmax ⟨γ', tang_of_proj_eq hπ (by omega) (hb.trans ha.symm) hγ'⟩
    rcases depth_type hπ htlt hmem with ⟨j, hj, _⟩ | ⟨k, hk, hd⟩
    · exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (by omega), hj ▸ hmem⟩
    · exfalso
      rcases hd with hd | hd
      · exact inertType_ne_ramType ((hd a ha).symm.trans (hc a ha))
      · exact splitType_ne_ramType ((hd a ha).symm.trans (hc a ha))
  · intro hc
    obtain ⟨j, hj, hmem⟩ := Set.mem_iUnion₂.1 hc
    by_cases hlt : 2 * j + 2 ≤ N
    · exact decidedAt_ram_of_depth_odd hπ hmem hlt
    · rw [depthSet_odd_eq_empty hπ (by omega)] at hmem
      exact absurd hmem (Set.notMem_empty c)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.decidedSet_ram_eq

end AxCheck
