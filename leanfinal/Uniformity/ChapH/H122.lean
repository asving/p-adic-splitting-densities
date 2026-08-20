/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H30
import Uniformity.ChapH.H121
import Uniformity.ChapH.H122m2

/-!
# Uniformity.ChapH.H122 — the cluster rate species, CONDITIONAL on H.121 clause (iii)

**Chapter H, NODE H.122** [theorem] (`blueprint/CHAP-H_general_induction.md` §17, line 8468;
PROOF and ROUTE NOTE re-signed by AMENDMENT **A-H.6** §4, line 9389).

**⚠ THE SIGNED NODE IS NOT LANDED HERE.**  The signed statement is

```
theorem uClusterNorm_rateSpecies ... (hm : 2 ≤ m) (hm3 : m ≤ 3) :
    RateSpecies (residueCard O) 1 1 1 (fun N => uClusterNorm O π m N)
```

(`leanspec/Leanspec/ChapH.lean:3168-3172`, byte-frozen).  It is **BLOCKED**: its `m = 3` leg
consumes H.121 clause (iii) (`uCluster_beta_leg`), which is not landed anywhere in the corpus
and is itself RESCHEDULED behind H.116b's fibre count `betaExtract_fiber_card` — a recorded
research frontier (`leanfinal/notes/H116B4_OUTLINE_2026-08-18.md`: open lemmas GR-7, GR-9,
GR-10).  The blocked record for this node is
`leanfinal/Uniformity/ChapH/H122_BLOCKED_2026-08-20.md`.

What IS landed here is the whole of A-H.6's six-step local replay with the β envelope as an
EXPLICIT CARRIED HYPOTHESIS, in the exact frozen shape of clause (iii).  So

* `uClusterNorm_rateSpecies_of_betaLeg` is the signed conclusion at the signed constants
  `(K, B, c) = (1, 1, 1)` over the signed range `2 ≤ m ≤ 3`, under one hypothesis; and
* when H.121c lands, the signed node is
  `uClusterNorm_rateSpecies_of_betaLeg hπ hm hm3 (fun N hN => uCluster_beta_leg hπ hm hm3 N hN)`
  — nothing else is owed.

Nothing is weakened: the CONCLUSION is byte-identical to the frozen one, the constants are the
GROUND literals, and the added binder is the frozen clause (iii) verbatim (audited in §0).

## What is proved, leg by leg

* `cluster_closing_arith` — A-H.6's closing arithmetic `1 + (N−3)⁺/3 + N/3 ≤ N` for `N ≥ 2`
  (battery leg `E2`, `2 ≤ N < 400`, here for all `N`).
* `betaLeg_two` — the **non-vacuity witness for the added binder**: at `m = 2` the carried
  hypothesis is a THEOREM (the β bucket is empty, `H122m2.card_betaUndecided_two`).  A-H.1/D7
  was an inhabitation defect, so this obligation is not optional in this chapter.
* `uCluster_three_le_of_betaLeg` — the `m = 3` strong induction, in the ℕ-level form
  `u(N) ≤ N · Q^(2(N−1))` (equivalent to `û(N) ≤ N·Q^(−(N−1))` with NO real division, since
  `3(N−1) = 2(N−1) + (N−1)` exactly).
* `uClusterNorm_rateSpecies_of_betaLeg` — the split on `m`: `m = 2` cites the LANDED
  unconditional `H122m2.uClusterNorm_rateSpecies_two`, `m = 3` normalizes the induction.

## The six steps, as landed (A-H.6 §4's route, the ONLY sanctioned one)

1. Base `N = 1`: `u(1) = 1 ≤ 1·Q^0` (H.119 `uCluster_one`).
2. Split by H.121 (i) (`uCluster_split`, an EQUALITY at `2 ≤ m ≤ 3`).
3. Head: H.113 `card_drainState` is EXACT — `#DRAIN = Q^((m−1)(N−1)) = Q^(2(N−1))` at `m = 3`.
4. α: H.121 (ii) (`uCluster_alpha_leg`, an equality) + the induction hypothesis at the windows
   `M = N − 3k ≥ 1` (each `< N`, since `k ≥ 1`), then **H.30b**
   (`alpha_geom_partial_le_third`) at `c := clusterC 3 = 3 ≥ 2`.  The per-term exponent
   identity is `3k + 2(M−1) + 3k = 2(N−1)`, i.e. the `k`-th term carries `(Q^(3k))⁻¹`, and
   `M ≤ N − 3` bounds the polynomial factor.  H.30 (`≤ 1`, tight at `c = 1`) is NOT enough
   here — that is A-H.6's whole point.
5. β: the carried hypothesis, used ONCE, with no `RateSpecies.mono` inflation.
6. Sum and close by `cluster_closing_arith`.

⚠ **THE E3 FENCE (A-H.6 §4), OBSERVED.**  There is no uniform `2 ≤ m ≤ 3` induction through
clause (iii): at `m = 2` the α factor is H.30 at `clusterC 2 = 1`, where `Σ = 1` is TIGHT, and
`1 + (N−2) + N/3 ≤ N` fails from `N = 4`.  The `m = 2` leg MUST go through the empty β bucket,
and it does (it is a citation of the landed `uClusterNorm_rateSpecies_two`).

⚠ **`rate_close` (H.71) IS NOT USED AND IS NOT AN IMPORT.**  A-H.6 §4 REFUTED it as a route to
these constants: at any legs it returns `RateSpecies Q (1+K′) (m+B′+1) (c′+1)`, whose `B`-slot
is `≥ m+1 ≥ 3` and whose `c`-slot is `≥ 2`, and H.66's `RateSpecies.mono` moves constants
UPWARD only.

⚠ **S-1 fence.**  `uCluster` is the CONSERVATIVE cluster carrier `u_{m,1}`, never the semantic
`undecidedCount` (finding F-2).  Nothing here says anything about the semantic object.

## §0 BINDER-VACUITY AUDIT (mandatory, per `blueprint/CHAP-C_tower_grammar.md` A-C.8.4)

Verdict: **NO VACUOUS BINDER.**  Every hypothesis of the landed statements is either sharp at a
named counterexample or is a positively-inhabited instance hypothesis.  Item by item, against
the A-C.7 registry's four collapse shapes:

| binder | verdict | evidence |
|---|---|---|
| `hπ : Irreducible π` | LOAD-BEARING, inhabited | consumed by `uCluster_split`, `uCluster_alpha_leg`, `uCluster_one`; inhabited by any uniformizer of any DVR. Not a `Nonempty`-style inert guard (C.113 shape absent). |
| `hm : 2 ≤ m` | SHARP at `m = 1` | at `m ≤ 1` there is no child event at all: `HasChildAt` carries `2 ≤ μ` (H.109) and H.118's `betaChild_mult_lt` gives `μ < m`, so the α/β machinery of H.121 is empty and H.121's split is not the signed one. |
| `hm3 : m ≤ 3` | SHARP at `m = 4` | H.121 (i)'s three-cell split FAILS from `m = 4`: the CS bucket is no longer empty, and the identity needs a fourth term. The counterexample is machine-checked in `H121.lean` §3.1 (the toy reader with state `2` relabelled DEC → CS: `9 ≠ 8`). |
| `hm ∧ hm3` jointly | SATISFIABLE, both values used | `m = 2` and `m = 3` are both reached (`interval_cases m` produces exactly two goals, and the two goals have DIFFERENT proofs — the `m = 2` one does not use the β binder at all). Not an empty guard pair. |
| `hbeta` (the ADDED binder) | LOAD-BEARING, INHABITED, and NOT trivially true | (a) **inhabited**: `betaLeg_two` below PROVES it at `m = 2` (empty β bucket), so the hypothesis set is nonempty — the audit's inhabitation leg, in Lean, in this file; (b) **not trivially true**: the trivial census bound is `#(β ∧ undec) ≤ Q^(m(N−1))`, and `hbeta`'s right-hand side is strictly smaller at EVERY `N ≥ 1` and `Q ≥ 2` (it is `(1/3)·N·Q^(m(N−1))·Q^(−(N−1))`, and `(1/3)N < Q^(N−1)` for all `N ≥ 1`), so it genuinely restricts; (c) **used exactly once**, in step 5, and dropping it breaks the induction (finding F-H17.2: the FROZEN pre-A-H.6 envelope `N^m·Q^(−(N−2))` exceeds H.122's TOTAL budget `N·Q^(−(N−1))` at every `N ≥ 2`, certificate `verification/AH6_beta_envelope_check.py` checks C7/C8); (d) **certified true at `m = 3`** with margin `> 4.3×` for `q ∈ {2,3}`, `N ≤ 40`, exact rationals (same certificate, check C2) — so it is not a false hypothesis smuggling vacuity in. |
| `hN : 1 ≤ N` inside `hbeta` / the key | SHARP at `N = 0` | at `N = 0` the state space is a point with `u(0) = 1` while the bound reads `0`; `RateSpecies` itself quantifies `M ≥ 1` for this reason (H.65's own note). |
| instances `[Finite (ResidueField O)]`, `[IsAdicComplete (maximalIdeal O) O]` | LOAD-BEARING | `residueCard` finiteness and the `ClusterState`/`ChildAt` engine respectively; `ℤ_[p]` inhabits both. |

Collapse shapes checked and ABSENT: no unpinned carrier field (C.111 shape — there is no
structure here); no self-loop over a quantified relation (C.94 shape — the induction is over
`ℕ` with a strictly decreasing window `M < N`, and the decrease is forced by `k ≥ 1`); no inert
`Nonempty` (C.113 shape); no implication-guarded `≠ ⊤` / window-free stratum (C.118 shape).

**One honest asymmetry, recorded.**  `hbeta` restricts NOTHING at `m = 2` (it is provable
there, `betaLeg_two`) and is the entire open content at `m = 3`.  That is exactly the shape
A-H.6 signed, and the `m = 2` leg's proof does not consume it.

## DEPENDS (all landed)

H.13 (`clusterC`), H.30b (`alpha_geom_partial_le_third`), H.65 (`RateSpecies`), H.113
(`card_drainState`), H.119 (`uCluster`, `uClusterNorm`, `uCluster_one`), H.121a
(`uCluster_split`), H.121b (`uCluster_alpha_leg`), H.122's `m = 2` half
(`uClusterNorm_rateSpecies_two`, `card_betaUndecided_two`) · landed `two_le_residueCard`.
**NOT** H.71 (`rate_close`, refuted route), **NOT** H.121d (`beta_content_census` is clause
(iii)'s own pricing step, not this node's input).

**ENVIRONMENT.** ENV-H17 + `[Finite (ResidueField O)]` + `[IsAdicComplete (maximalIdeal O) O]`,
`(O : Type)`, `π` explicit — every binder inline, as the frozen signature has them.

## Status

Sorry-free. Axiom footprint: Lean core only, printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing

/-! ## 1. A-H.6's closing arithmetic -/

/-- **A-H.6 §4 step 6.**  `1 + (N−3)⁺/3 + N/3 ≤ N` for every `N ≥ 2`.  Two regimes: at
`N ≤ 3` the α range is empty and the claim is `1 + N/3 ≤ N`, i.e. `3 ≤ 2N`; at `N ≥ 4` the
left side is exactly `2N/3`.  `N = 1` is NOT covered and does not need to be — it is the
induction's base case. -/
theorem cluster_closing_arith {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) + ((N - 3 : ℕ) : ℝ) / 3 + (N : ℝ) / 3 ≤ (N : ℝ) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rcases Nat.lt_or_ge N 4 with h | h
  · have h0 : ((N - 3 : ℕ) : ℝ) = 0 := by
      have hz : N - 3 = 0 := by omega
      rw [hz]; norm_num
    rw [h0]; linarith
  · have h3 : (3 : ℕ) ≤ N := by omega
    have h0 : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
      rw [Nat.cast_sub h3]; norm_num
    have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    rw [h0]; linarith

/-! ## 2. The added binder is inhabited — the `m = 2` instance is a THEOREM -/

/-- **The non-vacuity witness for the carried β binder (§0, row `hbeta`).**  At `m = 2` clause
(iii) holds unconditionally: the β bucket is EMPTY (`H122m2.card_betaUndecided_two`, from
H.118's `betaChild_mult_lt` and H.109's `2 ≤ μ`), so the left side is `0` while the right side
is nonnegative.  This is what makes `uClusterNorm_rateSpecies_of_betaLeg`'s hypothesis set
provably nonempty rather than merely unrefuted. -/
theorem betaLeg_two {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O} (N : ℕ) :
    (Nat.card {c : ClusterState O 2 N //
        IsBetaState π c ∧ ClusterUndecided O π 2 N c} : ℝ)
      ≤ (1 / 3 : ℝ) * (N : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1))
          * ((residueCard O : ℝ) ^ (N - 1))⁻¹ := by
  rw [card_betaUndecided_two (π := π) (N := N), Nat.cast_zero]
  positivity

/-! ## 3. The `m = 3` strong induction -/

/-- **A-H.6 §4, the `m = 3` leg**, in the division-free ℕ-level form.  `3(N−1) = 2(N−1) +
(N−1)` exactly, so `û(N) ≤ N·Q^(−(N−1))` is `u(N) ≤ N·Q^(2(N−1))`. -/
theorem uCluster_three_le_of_betaLeg {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    (hbeta : ∀ N : ℕ, 1 ≤ N →
      (Nat.card {c : ClusterState O 3 N //
          IsBetaState π c ∧ ClusterUndecided O π 3 N c} : ℝ)
        ≤ (1 / 3 : ℝ) * (N : ℝ) * (residueCard O : ℝ) ^ (3 * (N - 1))
            * ((residueCard O : ℝ) ^ (N - 1))⁻¹) :
    ∀ N : ℕ, 1 ≤ N →
      (uCluster O π 3 N : ℝ) ≤ (N : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1)) := by
  classical
  have hQ2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQR : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hcast1 : ((residueCard O - 1 : ℕ) : ℝ) = (residueCard O : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ residueCard O := residueCard_pos O
    push_cast [Nat.cast_sub h1]
    ring
  have hc3 : clusterC 3 = 3 := by simp [clusterC]
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    rcases Nat.lt_or_ge N 2 with hN1 | hN2
    · -- base case `N = 1`: H.119 (i)
      have hN1' : N = 1 := by omega
      subst hN1'
      rw [uCluster_one π hπ 3 (by norm_num)]
      norm_num
    -- the inductive step at `N ≥ 2`
    · have hP : (0 : ℝ) < (residueCard O : ℝ) ^ (2 * (N - 1)) := pow_pos hQ0 _
      -- step 2: H.121 (i), an equality
      have hsplit := uCluster_split hπ (show (2 : ℕ) ≤ 3 by norm_num)
        (show (3 : ℕ) ≤ 3 by norm_num) N hN
      have hcast : (uCluster O π 3 N : ℝ)
          = (Nat.card {c : ClusterState O 3 N // IsDrainState c} : ℝ)
            + (Nat.card {c : ClusterState O 3 N //
                (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π 3 N c} : ℝ)
            + (Nat.card {c : ClusterState O 3 N //
                IsBetaState π c ∧ ClusterUndecided O π 3 N c} : ℝ) := by
        rw [hsplit]; push_cast; ring
      -- step 3: the head cell, EXACT (H.113)
      have hhead : (Nat.card {c : ClusterState O 3 N // IsDrainState c} : ℝ)
          = (residueCard O : ℝ) ^ (2 * (N - 1)) := by
        rw [card_drainState (O := O) 3 N (by norm_num) hN]
        norm_num
      -- step 4: the α cell — H.121 (ii), the IH, and H.30b at `clusterC 3 = 3 ≥ 2`
      have halpha : (Nat.card {c : ClusterState O 3 N //
            (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π 3 N c} : ℝ)
          ≤ ((N - 3 : ℕ) : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1)) := by
        rw [uCluster_alpha_leg hπ (show (2 : ℕ) ≤ 3 by norm_num) N hN, Nat.cast_sum]
        have hbound : ∀ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1),
            (((residueCard O - 1) * residueCard O ^ (k * clusterC 3)
                * uCluster O π 3 (N - 3 * k) : ℕ) : ℝ)
              ≤ ((N - 3 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1))
                  * (((residueCard O : ℝ) - 1) * ((residueCard O : ℝ) ^ (3 * k))⁻¹) := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          obtain ⟨hkN, hk1, hk3⟩ := hk
          have hM1 : 1 ≤ N - 3 * k := by omega
          have hMN : N - 3 * k < N := by omega
          have hM3 : N - 3 * k ≤ N - 3 := by omega
          have hih := ih (N - 3 * k) hMN hM1
          have hM3R : ((N - 3 * k : ℕ) : ℝ) ≤ ((N - 3 : ℕ) : ℝ) := by
            exact_mod_cast hM3
          have hexp : (residueCard O : ℝ) ^ (2 * (N - 1))
                * ((residueCard O : ℝ) ^ (3 * k))⁻¹
              = (residueCard O : ℝ) ^ (k * clusterC 3)
                * (residueCard O : ℝ) ^ (2 * (N - 3 * k - 1)) := by
            rw [mul_inv_eq_iff_eq_mul₀ (ne_of_gt (pow_pos hQ0 (3 * k))), ← pow_add, ← pow_add,
              hc3]
            congr 1
            omega
          push_cast [hcast1]
          calc ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ (k * clusterC 3)
                * (uCluster O π 3 (N - 3 * k) : ℝ)
              ≤ ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ (k * clusterC 3)
                  * (((N - 3 * k : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 3 * k - 1))) := by
                exact mul_le_mul_of_nonneg_left hih
                  (mul_nonneg (by linarith) (by positivity))
            _ = ((N - 3 * k : ℕ) : ℝ) * ((residueCard O : ℝ) ^ (2 * (N - 1))
                  * ((residueCard O : ℝ) ^ (3 * k))⁻¹) * ((residueCard O : ℝ) - 1) := by
                rw [hexp]; ring
            _ ≤ ((N - 3 : ℕ) : ℝ) * ((residueCard O : ℝ) ^ (2 * (N - 1))
                  * ((residueCard O : ℝ) ^ (3 * k))⁻¹) * ((residueCard O : ℝ) - 1) := by
                refine mul_le_mul_of_nonneg_right ?_ (by linarith)
                exact mul_le_mul_of_nonneg_right hM3R (by positivity)
            _ = ((N - 3 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1))
                  * (((residueCard O : ℝ) - 1) * ((residueCard O : ℝ) ^ (3 * k))⁻¹) := by ring
        have hgeom : ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1),
              (((residueCard O : ℝ) - 1) * ((residueCard O : ℝ) ^ (3 * k))⁻¹) ≤ 1 / 3 := by
          have hsub : (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1)
              ⊆ (Finset.range N).image (· + 1) := by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_range] at hk
            simp only [Finset.mem_image, Finset.mem_range]
            exact ⟨k - 1, by omega, by omega⟩
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => mul_nonneg (by linarith) (by positivity))) ?_
          rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
          exact alpha_geom_partial_le_third (residueCard O) 3 hQ2 (by norm_num) N
        calc ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1),
                (((residueCard O - 1) * residueCard O ^ (k * clusterC 3)
                  * uCluster O π 3 (N - 3 * k) : ℕ) : ℝ)
            ≤ ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1),
                ((N - 3 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1))
                  * (((residueCard O : ℝ) - 1) * ((residueCard O : ℝ) ^ (3 * k))⁻¹) :=
              Finset.sum_le_sum hbound
          _ = ((N - 3 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1))
                * ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ 3 * k ≤ N - 1),
                  (((residueCard O : ℝ) - 1) * ((residueCard O : ℝ) ^ (3 * k))⁻¹) := by
              rw [Finset.mul_sum]
          _ ≤ ((N - 3 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1)) * (1 / 3) :=
              mul_le_mul_of_nonneg_left hgeom (by positivity)
          _ = ((N - 3 : ℕ) : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1)) := by ring
      -- step 5: the β cell — the carried hypothesis, used ONCE
      have hbetaR : (Nat.card {c : ClusterState O 3 N //
            IsBetaState π c ∧ ClusterUndecided O π 3 N c} : ℝ)
          ≤ (N : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1)) := by
        have hpow2 : (residueCard O : ℝ) ^ (3 * (N - 1))
              * ((residueCard O : ℝ) ^ (N - 1))⁻¹
            = (residueCard O : ℝ) ^ (2 * (N - 1)) := by
          rw [mul_inv_eq_iff_eq_mul₀ (ne_of_gt (pow_pos hQ0 (N - 1))), ← pow_add]
          congr 1
          omega
        refine le_trans (hbeta N hN) (le_of_eq ?_)
        rw [mul_assoc, hpow2]
        ring
      -- step 6: sum, and A-H.6's closing arithmetic
      have hclose : (residueCard O : ℝ) ^ (2 * (N - 1))
            + ((N - 3 : ℕ) : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1))
            + (N : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1))
          ≤ (N : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1)) :=
        calc (residueCard O : ℝ) ^ (2 * (N - 1))
              + ((N - 3 : ℕ) : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1))
              + (N : ℝ) / 3 * (residueCard O : ℝ) ^ (2 * (N - 1))
            = (1 + ((N - 3 : ℕ) : ℝ) / 3 + (N : ℝ) / 3)
                * (residueCard O : ℝ) ^ (2 * (N - 1)) := by ring
          _ ≤ (N : ℝ) * (residueCard O : ℝ) ^ (2 * (N - 1)) :=
              mul_le_mul_of_nonneg_right (cluster_closing_arith hN2) hP.le
      rw [hcast, hhead]
      linarith

/-! ## 4. The node's conclusion, at the signed constants -/

/-- **NODE H.122, CONDITIONAL on H.121 clause (iii).**  The conclusion and the constants are
byte-identical to the frozen signature (`leanspec/Leanspec/ChapH.lean:3168`); the single added
binder `hbeta` IS clause (iii) (`uCluster_beta_leg`) verbatim.  `m = 2` is unconditional (it
cites the landed `uClusterNorm_rateSpecies_two` and never touches `hbeta`); `m = 3` is §3's
induction.  See §0 for the binder-vacuity audit and the module header for why the signed node
is not landed. -/
theorem uClusterNorm_rateSpecies_of_betaLeg {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 2 ≤ m) (hm3 : m ≤ 3)
    (hbeta : ∀ N : ℕ, 1 ≤ N →
      (Nat.card {c : ClusterState O m N //
          IsBetaState π c ∧ ClusterUndecided O π m N c} : ℝ)
        ≤ (1 / 3 : ℝ) * (N : ℝ) * (residueCard O : ℝ) ^ (m * (N - 1))
            * ((residueCard O : ℝ) ^ (N - 1))⁻¹) :
    RateSpecies (residueCard O) 1 1 1 (fun N => uClusterNorm O π m N) := by
  sorry

end Uniformity.Density.Induction

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.cluster_closing_arith
#print axioms Uniformity.Density.Induction.betaLeg_two
#print axioms Uniformity.Density.Induction.uCluster_three_le_of_betaLeg
#print axioms Uniformity.Density.Induction.uClusterNorm_rateSpecies_of_betaLeg

end AxCheck
