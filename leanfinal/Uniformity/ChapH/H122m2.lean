/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H65
import Uniformity.ChapH.H113
import Uniformity.ChapH.H121b
import Uniformity.ChapH.H28

/-!
# Uniformity.ChapH.H122m2 — the `m = 2` half of H.122, unconditionally

**⚠ THIS FILE IS NOT NODE H.122.**  The signed H.122 is
`RateSpecies (residueCard O) 1 1 1 (uClusterNorm O π m)` at `2 ≤ m ≤ 3`; it is **BLOCKED** and
its blueprint proof route is **REFUTED at its own constants** — see the committed record
`leanfinal/notes/RESCHEDULE_H121c_H122_2026-08-16.md` (finding F-H17.2).  What this file lands
is the `m = 2` slice of that statement, which needs no β leg at all and is therefore
unconditional today.  Nothing here discharges the signed node; the `m = 3` slice is exactly
where H.122's gap sits.

* `not_isBetaState_two` — at `m = 2` the β bucket is EMPTY;
* `uCluster_two_recursion` — the `m = 2` conservative recursion, an EQUALITY;
* `uCluster_two_eq_uTwo` — **the `P1(i)` tie**: `u_2 = ChapG`'s `uTwo` closed-form family;
* `uClusterNorm_rateSpecies_two` — `RateSpecies Q 1 1 1 (uClusterNorm O π 2)`.

## Why `m = 2` closes and `m = 3` does not

`HasChildAt` carries `2 ≤ μ` (H.109) and H.118's `betaChild_mult_lt` forces `μ < m` on a β
state, so at `m = 2` a β state would need `2 ≤ μ < 2`.  H.111 (b)'s third conjunct therefore
fails for every state: **every child at `m = 2` is full-multiplicity, i.e. α**.  Feeding that
into H.121a's split (which already empties the CS bucket at `m ≤ 3` and the DEC bucket always)
leaves exactly two cells, head and α, both of which are landed EQUALITIES — H.113's census and
H.121b's α leg.  The result is a closed recursion in `u_2` alone, with `clusterC 2 = 1`:

  `u(N) = Q^(N−1) + Σ_{1 ≤ k, 2k ≤ N−1} (Q − 1) · Q^k · u(N − 2k)`,

which is `uTwo`'s defining recursion (H.23) verbatim.  So the semantic object and the ChapG
closed-form family coincide, and H.28's `uTwo_ratio_le` transports the rate.

At `m = 3` the β cell is nonempty and this route stops: see the blocked record.

## What this is worth to the re-plan

Two things, both recorded in the blocked note and both now machine-checked here.

1. **The constants `(K, B, c) = (1, 1, 1)` are right.**  They close at `m = 2` with room, so
   H.122's target is not itself suspect — only H.121 (iii)'s envelope is.
2. **It is the child rate the degree descent needs.**  H.121 (iii) at `m = 3` prices its genre
   composition against the children's rate at `μ = 2`.  The blueprint routes that through §5's
   landed closed forms *precisely to avoid circularity* with H.122 (one theorem over both
   degrees).  `uCluster_two_eq_uTwo` is that bridge made explicit: it ties the CLUSTER-carrier
   count at `m = 2` to the §5 family, so the descent can consume H.26/H.28 without touching
   H.122.

## ⚠ The S-1 fence

`uCluster` and `uTwo` are both CONSERVATIVE-family objects (`u_{m,1}`, ChapG `hex3R`).  The tie
proved here is a tie BETWEEN CONSERVATIVE OBJECTS; it says nothing about the semantic
`undecidedCount`, and reading it as one is finding F-2's error.

DEPENDS: H.13 (`clusterC`), H.23 (`uTwo`), H.24 (`uTwo_one`), H.26/H.28 (`uTwo_ratio_le`),
H.65 (`RateSpecies`), H.109 (`HasChildAt`), H.111 (`IsBetaState`), H.113 (`card_drainState`),
H.118 (`betaChild_mult_lt`), H.119 (`uCluster`, `uCluster_one`, `uClusterNorm`), H.121a
(`uCluster_split`), H.121b (`uCluster_alpha_leg`) · landed `two_le_residueCard`.

**ENVIRONMENT — ENV-H17** + `[Finite (ResidueField O)]` + `[IsAdicComplete (maximalIdeal O) O]`,
`(O : Type)` (the universe the H.121 statements pin), every binder INLINE.

## TEETH (GC-8)

Battery `P1(i) tie u_2 = ChapG hex3R/uTwo closed form` + `P3 RateSpecies (K,B,c) = (1,1,1) on
true data` (the `m = 2` column) of `verification/openmath/OM2_genindb_battery.py`.  §5 checks
the tie's closed form against `hex3R_ref` and the rate at both battery characteristics, and
pins the `m = 3` column that this file does NOT cover — the two numbers whose ratio is finding
F-H17.2.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. The β bucket is empty at `m = 2` -/

/-- **No β state at `m = 2`.**  A β state has a child (H.111 (b)'s third conjunct), the child's
multiplicity satisfies `2 ≤ μ` (`HasChildAt`, H.109) and `μ < m` (H.118's
`betaChild_mult_lt`, since a full-multiplicity child would make the state α) — at `m = 2` that
is `2 ≤ μ < 2`. -/
theorem not_isBetaState_two {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {N : ℕ} (c : ClusterState O 2 N) : ¬ IsBetaState π c := by
  intro hβ
  obtain ⟨μ, k, z, hch⟩ := hβ.2.2.1
  have h1 : μ < 2 := betaChild_mult_lt hβ hch
  have h2 : 2 ≤ μ := hch.1
  omega

/-- The β cell of H.121a's split is empty at `m = 2`. -/
theorem card_betaUndecided_two {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} {N : ℕ} :
    Nat.card {c : ClusterState O 2 N // IsBetaState π c ∧ ClusterUndecided O π 2 N c} = 0 := by
  haveI : IsEmpty {c : ClusterState O 2 N // IsBetaState π c ∧ ClusterUndecided O π 2 N c} :=
    ⟨fun x => not_isBetaState_two x.1 x.2.1⟩
  exact Nat.card_of_isEmpty

/-! ## 2. The `m = 2` recursion, as an EQUALITY -/

/-- **The `m = 2` conservative recursion.**  H.121a's split with the CS cell empty (H.117), the
DEC cell decided (H.119), the β cell empty (§1), the head cell H.113's census and the α cell
H.121b's leg — every one of them an equality, so the recursion is one too. -/
theorem uCluster_two_recursion {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) (N : ℕ) (hN : 1 ≤ N) :
    uCluster O π 2 N
      = residueCard O ^ (N - 1)
        + ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 2 * k ≤ N - 1),
            (residueCard O - 1) * residueCard O ^ k * uCluster O π 2 (N - 2 * k) := by
  have hc2 : clusterC 2 = 1 := rfl
  rw [uCluster_split hπ (le_refl 2) (by omega) N hN, card_betaUndecided_two,
    card_drainState 2 N (by omega) hN, uCluster_alpha_leg hπ (le_refl 2) N hN, hc2]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul, mul_one, Nat.add_zero]

/-! ## 3. The `P1(i)` tie: the cluster count IS the `uTwo` family -/

/-- **The `P1(i)` tie.**  `u_{2,1}(N) = uTwo Q N` for `N ≥ 1`: the `m = 2` cluster-carrier
conservative complement is ChapG's landed closed-form family (H.23's recursion, H.26's closed
form).  Strong induction on the window; the base is H.119's `u(1) = 1` against H.24's
`uTwo Q 1 = 1`, and the step is §2's recursion against `uTwo`'s defining equation, term by term
(the recursion never consults window `0`, so the two families' differing conventions there are
never compared).

⚠ S-1: both sides are CONSERVATIVE objects.  This is not a statement about `undecidedCount`. -/
theorem uCluster_two_eq_uTwo {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) : ∀ N, 1 ≤ N → uCluster O π 2 N = uTwo (residueCard O) N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    match N, hN, ih with
    | 1, _, _ => rw [uCluster_one π hπ 2 (by omega), uTwo_one]
    | (M + 2), _, ih =>
      rw [uCluster_two_recursion hπ (M + 2) (by omega), uTwo]
      have hpow : M + 2 - 1 = M + 1 := by omega
      rw [hpow]
      congr 1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro k _
      by_cases hk : 1 ≤ k ∧ 2 * k ≤ M + 1
      · rw [if_pos hk, dif_pos hk, ih (M + 2 - 2 * k) (by omega) (by omega)]
      · rw [if_neg hk, dif_neg hk]

/-! ## 4. The `m = 2` rate species, at the ground constants -/

/-- **H.122 at `m = 2`, unconditionally.**  `RateSpecies Q 1 1 1 (uClusterNorm O π 2)`, i.e.
`û(N) ≤ N · Q^(−(N−1))` for `N ≥ 1`.  The tie of §3 transports H.28's `uTwo_ratio_le` — which
is `EFF.GENIND.150`'s leg C, the ONLY place in the chapter where the species is discharged at a
concrete degree — onto the cluster carrier.

**This is not the signed H.122**, which quantifies over `2 ≤ m ≤ 3`; the `m = 3` slice is
blocked and its blueprint route is refuted (finding F-H17.2, committed record). -/
theorem uClusterNorm_rateSpecies_two {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) :
    RateSpecies (residueCard O) 1 1 1 (fun N => uClusterNorm O π 2 N) := by
  intro M hM
  simp only [uClusterNorm]
  rw [uCluster_two_eq_uTwo hπ M hM]
  have h := uTwo_ratio_le (residueCard O) (two_le_residueCard O) hM
  calc (uTwo (residueCard O) M : ℝ) / (residueCard O : ℝ) ^ (2 * (M - 1))
      ≤ (M : ℝ) / (residueCard O : ℝ) ^ (M - 1) := h
    _ = 1 * (M : ℝ) ^ 1 * ((residueCard O : ℝ) ^ (M - 1))⁻¹ := by
        rw [pow_one, one_mul, div_eq_mul_inv]

end Uniformity.Density.Induction

/-! ## 5. TEETH

`hexR` is `OM2_genindb_battery.py`'s `hex3R_ref` (ChapG `hex3R`), transcribed verbatim — the
same transcription H.119/H.121a/H.121b pin.  `hexU` is `hex3U_ref`.  The gates:

* **the tie** (`P1(i)`) — `hexR` satisfies §2's recursion at both battery characteristics
  through window 8, i.e. the closed form and the cluster recursion agree term by term;
* **the rate at `m = 2`** (`P3`, the column this file proves) — `hexR q N · q^(N−1) ≤ N · q^(2N−2)`,
  the integer form of `û(N) ≤ N · Q^(−(N−1))`;
* **the `m = 3` column this file does NOT prove**, with the two numbers of finding F-H17.2 side
  by side: the true normalized β mass and H.121 (iii)'s envelope on it, in the integer form
  `β · q^(N−2) ≤ (m−1) · q^(m(N−1)) · q^(−(N−1))` (needed) versus `β ≤ N^m q^(m(N−1)) q^(−(N−2))`
  (supplied).  The needed bound HOLDS on true data; the supplied one is ~100× too weak to imply
  it.  That contrast is the finding, machine-checked.

⚠ S-1: `hexR`/`hexU` are CONSERVATIVE-family closed forms (finding F-2). -/

section NumericGate

/-- The battery's `hex3R_ref` — ChapG `hex3R`, the `m = 2` conservative complement. -/
private def hexR (q M : ℕ) : ℕ :=
  if M = 0 then 0 else if M = 1 then 1
  else q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- The battery's `hex3U_ref` — ChapG `hex3U`, the cubic per-centre conservative complement. -/
private def hexU (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (((List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hexR q (N - 3 * k))).sum

/-- §2's recursion, as a computation. -/
private def recTwo (q N : ℕ) : ℕ :=
  q ^ (N - 1)
    + (((List.range N).filter fun k => decide (1 ≤ k ∧ 2 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ k * hexR q (N - 2 * k)).sum

-- the tie (`P1(i)`): the closed form satisfies §2's recursion
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 9).drop 1).all fun N => hexR q N == recTwo q N

-- the rate at `m = 2` (`P3`), in integer form: `u(N) · q^(N−1) ≤ N · q^(2N−2)`
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 9).drop 1).all fun N =>
    decide (hexR q N * q ^ (N - 1) ≤ N * q ^ (2 * N - 2))

-- the `m = 3` column, NOT proved here: the β cell of the split
private def betaThree (q N : ℕ) : ℕ :=
  hexU q N - q ^ (2 * (N - 1))
    - (((List.range N).filter fun k => decide (1 ≤ k ∧ 3 * k ≤ N - 1)).map fun k =>
        (q - 1) * q ^ (3 * k) * hexU q (N - 3 * k)).sum

-- F-H17.1's needed budget HOLDS on true data: `β · q^(N−1) ≤ (m−1) · q^(m(N−1))`, `m = 3`
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 8).drop 1).all fun N =>
    decide (betaThree q N * q ^ (N - 1) ≤ 2 * q ^ (3 * (N - 1)))

-- but H.121 (iii)'s ENVELOPE does not imply it: the envelope exceeds the whole census
#guard ([2, 3] : List ℕ).all fun q =>
  ((List.range 8).drop 1).all fun N =>
    decide (q ^ (3 * (N - 1)) ≤ N ^ 3 * q ^ (3 * (N - 1)) / q ^ (N - 2))

-- the two sides at `q = 2, m = 3, N = 6`: true β mass 208, envelope 13.5 × the census
#guard (betaThree 2 6, 2 * 2 ^ (3 * 5) / 2 ^ 5, 6 ^ 3 * 2 ^ (3 * 5) / 2 ^ 4) == (208, 2048, 442368)

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.not_isBetaState_two
#print axioms Uniformity.Density.Induction.card_betaUndecided_two
#print axioms Uniformity.Density.Induction.uCluster_two_recursion
#print axioms Uniformity.Density.Induction.uCluster_two_eq_uTwo
#print axioms Uniformity.Density.Induction.uClusterNorm_rateSpecies_two

end AxCheck
