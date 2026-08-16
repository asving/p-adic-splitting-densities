/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H106 — the cluster-state carrier and its census

**Chapter H, NODE H.106** (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1 completion
layer, dated extension 2026-08-16; provenance OM-2 §4 sketch `N2.0`, source `EFF.GENIND.07`).
First node of **N-2**, the cluster event grammar over `O`.

`ClusterState O m N` is the `(m, d = 1, N)` cluster system: the level-`N` classes of the
recentred `Φ`-adic development (`Φ = X`, `f = X ^ m + ∑_{j < m} a_j X ^ j`, every `ā_j = 0`) —
i.e. `Coeff O m N`-vectors every coordinate of which lies in the image ideal
`𝔪 / 𝔪 ^ N ⊆ O ⧸ 𝔪 ^ N`.  The lemma half is the state census:

* `card_clusterState` — `#(ClusterState O m N) = q ^ (m * (N − 1))` at `1 ≤ N`,
  with `q = residueCard O`.

Two auxiliary facts are exported because the rest of §17 reads the image ideal constantly:

* `mem_map_maximalIdeal_iff_resFactor_eq_zero` — the image ideal `𝔪 / 𝔪 ^ N` is exactly the
  kernel of the level-1 truncation `Res O N →+* Res O 1` (this is what makes the coordinate
  count an additive-fibre count rather than an ideal computation);
* `card_map_maximalIdeal` — the one-coordinate count `#(𝔪 / 𝔪 ^ N) = q ^ (N − 1)`.

**Scope fence (§17.0).** This carrier is the `d = 1` system, the sketch's own scope; any
`d ≥ 2` analogue of its leaf reads is `B-BOX-1`-gated and is NOT declared here.

DEPENDS: landed `Coeff`, `Res`, `resFactor`, `resFactor_mk`, `resFactor_surjective`,
`card_res`, `card_preimage_of_surjective`, `residueCard`, `residueCard_pos`
(`Uniformity/Density/LocalData.lean`) · mathlib `Equiv.subtypePiEquivPi`, `Nat.card_pi`,
`Ideal.mem_map_iff_of_surjective`.

## TEETH (GC-8)

The node's TEETH are the PART-1 cell inventories of
`verification/openmath/OM2_genindb_battery.py` — the state-space size of each `(q, m, N)` cell
is the enumeration total of that cell (`cluster_states` = `elements(N, val_ge = 1) ^ m`, i.e.
`(q ^ (N − 1)) ^ m`).  The theorem `card_clusterState` IS that inventory, proved.  The
`#guard` block below reproduces the cheap arithmetic leg: the theorem's closed form
`q ^ (m * (N − 1))` agrees with the battery's product-of-coordinates enumeration at every cell
of the battery's `part1` plan, and hits its two largest cells (32,768 and 19,683 states) on the
nose.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The carrier -/

/-- **H.106 (def half). The cluster-state carrier.** The `(m, d = 1, N)` system: level-`N`
coefficient classes with every coordinate residually zero, i.e. in the image ideal
`𝔪 / 𝔪 ^ N` — the recentred `Φ`-adic development at `Φ = X`, whose polynomial is
`f = X ^ m + ∑_{j < m} a_j X ^ j` with every `ā_j = 0`. -/
def ClusterState (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) : Type _ :=
  {c : Coeff O m N //
    ∀ i, c i ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}

/-! ## 2. The image ideal is the kernel of the level-1 truncation -/

/-- **The image ideal, identified.** For `1 ≤ N`, an element of `O ⧸ 𝔪 ^ N` lies in the image
of `𝔪` exactly when it dies in `O ⧸ 𝔪 ^ 1`.  (The forward direction is where the work is: a
witness `b ∈ 𝔪` with `mk b = mk a` only gives `b − a ∈ 𝔪 ^ N`, and `𝔪 ^ N ≤ 𝔪` closes it.) -/
theorem mem_map_maximalIdeal_iff_resFactor_eq_zero {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {N : ℕ} (hN : 1 ≤ N) (x : Res O N) :
    x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))
      ↔ resFactor (O := O) hN x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) x
  rw [resFactor_mk, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  constructor
  · intro hmem
    obtain ⟨b, hb, hba⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
    have hd : b - a ∈ (maximalIdeal O) ^ N := Ideal.Quotient.eq.1 hba
    have hd' : b - a ∈ maximalIdeal O := Ideal.pow_le_self (by omega) hd
    have : a = b - (b - a) := by ring
    rw [this]
    exact Ideal.sub_mem _ hb hd'
  · intro ha
    exact Ideal.mem_map_of_mem _ ha

/-! ## 3. The one-coordinate count -/

/-- **`#(𝔪 / 𝔪 ^ N) = q ^ (N − 1)`.** The image ideal is the kernel of a surjective additive
map `Res O N → Res O 1` between finite groups, so `q ^ N = #(kernel) * q`. -/
theorem card_map_maximalIdeal {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {N : ℕ} (hN : 1 ≤ N) :
    Nat.card {x : Res O N //
        x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}
      = residueCard O ^ (N - 1) := by
  classical
  have hsurj : Function.Surjective (resFactor (O := O) hN) := resFactor_surjective (O := O) hN
  -- the subtype is the kernel of the level-1 truncation
  have hcongr : Nat.card {x : Res O N //
      x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}
      = Nat.card (resFactor (O := O) hN).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      rw [mem_map_maximalIdeal_iff_resFactor_eq_zero hN x]
      exact Iff.symm AddMonoidHom.mem_ker))
  -- fibre counting: `#(Res O N) = #(ker) * #(Res O 1)`
  have hprod : Nat.card (Res O N)
      = Nat.card (resFactor (O := O) hN).toAddMonoidHom.ker * Nat.card (Res O 1) := by
    have := card_preimage_of_surjective (A := Res O N) (B := Res O 1)
      (resFactor (O := O) hN).toAddMonoidHom hsurj Set.univ
    simpa using this
  rw [card_res, card_res] at hprod
  -- `q ^ N = q ^ (N − 1) * q ^ 1`, so the kernel has `q ^ (N − 1)` elements
  have hsplit : residueCard O ^ N = residueCard O ^ (N - 1) * residueCard O ^ 1 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hprod
  rw [hcongr]
  exact (Nat.eq_of_mul_eq_mul_right (by simpa using residueCard_pos O) hprod).symm

/-! ## 4. The census -/

/-- **H.106 (lemma half). The state census.** `#(ClusterState O m N) = q ^ (m * (N − 1))` —
`EFF.GENIND.07`'s state count, and the enumeration total of every PART-1 battery cell. -/
theorem card_clusterState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m N : ℕ) (hN : 1 ≤ N) :
    Nat.card (ClusterState O m N) = residueCard O ^ (m * (N - 1)) := by
  classical
  have e : ClusterState O m N ≃
      ((i : Fin m) → {x : Res O N //
        x ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}) :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [card_map_maximalIdeal hN, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]
  rw [Nat.mul_comm]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.mem_map_maximalIdeal_iff_resFactor_eq_zero
#print axioms Uniformity.Density.Induction.card_map_maximalIdeal
#print axioms Uniformity.Density.Induction.card_clusterState

end AxCheck

/-! ## TEETH — the PART-1 cell inventory, reproduced

`clusterStateCensus Q m N` is the closed form the theorem proves; the battery enumerates the
same cell as `elements(N, val_ge = 1) ^ m`, i.e. `(Q ^ (N − 1)) ^ m`.  The plan below is the
battery's own `part1` plan (its largest window per `(q, m)` pair). -/

section NumericCensus

/-- The census closed form of `card_clusterState`, as a computable numeral function. -/
def clusterStateCensus (Q m N : ℕ) : ℕ := Q ^ (m * (N - 1))

-- battery `part1` plan: (q, m, N) at the largest window of each row
#eval [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)].map
  fun p => clusterStateCensus p.1 p.2.1 p.2.2
  -- expect [1024, 32768, 4096, 6561, 19683, 6561]

#guard [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)].all
  fun p => clusterStateCensus p.1 p.2.1 p.2.2 == (p.1 ^ (p.2.2 - 1)) ^ p.2.1

#guard (clusterStateCensus 2 3 6, clusterStateCensus 3 3 4) == (32768, 19683)

end NumericCensus
