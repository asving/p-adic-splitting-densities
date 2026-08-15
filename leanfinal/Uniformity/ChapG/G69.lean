/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64
import Uniformity.ChapG.G66
import Uniformity.ChapG.G68

/-!
# Uniformity.ChapG.G69 — `hex3U_le`, THEOREM HEX3.B (the vanishing bound)

**Chapter G, NODE G.69** (`blueprint/CHAP-G_base_cases_menus.md` §9). *The HEX3.B vanishing
bound.* `u(q,N) ≤ N·q^(2N−2)` for `N ≥ 2`, `q ≥ 2`.

DEPENDS: G.64, G.66, G.68.

**PROOF (the blueprint's own five-step chain, done in ℕ throughout).**
1. Each `k`-summand of `hex3U` is bounded, doubled: `2·(q^(4k−1)(q^M−1)R(M)) ≤ (N−2)·q^(2N−2k−2)`
   (`M := N−3k`), via `q^M − 1 ≤ q^M` and G.68's `2R(M) ≤ (M+1)q^(M−1)` together with
   `M + 1 ≤ N − 2` for `k ≥ 1` — this is the private helper `hex3U_term_bound`.
2. Summing over `k`, `2·S ≤ (N−2)·T` where `S` is `hex3U`'s raw sum and
   `T = ∑ q^(2N−2k−2)`.
3. **`G.69a` (the geometric sum bound, split out per blueprint mandate as `geom_tele`):** a
   telescoping identity `(q²−1)·∑_{k=1}^K q^(2(L−k)) + q^(2(L−K)) = q^(2L)`, proved by plain
   induction on `K` via `Finset.sum_Icc_succ_top` (no closed-form geometric-series lemma
   needed — the telescoping identity `(q²−1)X + X = X·q²` closes each step). Instantiated at
   `L = N−1` this bounds `(q−1)(q+1)·T ≤ q^(2N−2)`.
4. Combine: `2(q−1)(q+1)·S ≤ (N−2)·q^(2N−2)`, and since `q ≥ 2 ⟹ q+1 ≥ 3 ⟹ 3(q−1) ≤ (q−1)(q+1)`,
   conclude `(q−1)·S ≤ 6(q−1)·S ≤ 2(q−1)(q+1)·S ≤ (N−2)q^(2N−2) ≤ (N−1)q^(2N−2)`.
5. `hex3U q N = q^(2N−2) + (q−1)·S ≤ q^(2N−2) + (N−1)q^(2N−2) = N·q^(2N−2)`.

**⚠ SOURCE-EVIDENCE NOTE.** `EFF.HEX3` §6.2 classes THEOREM HEX3.B as **PROOF-ONLY**: no
executable battery touches it. This node supplies the only available disposition.

**TEETH.** none.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- **G.69a**, the geometric sum bound. A telescoping identity in `ℕ`: multiplying the
finite geometric sum `∑_{k=1}^K q^(2(L−k))` by `q²−1` and adding back the smallest omitted
power `q^(2(L−K))` recovers the top power `q^(2L)` exactly. Proved by induction on `K` via
`Finset.sum_Icc_succ_top`, using only the single collapse fact `(q²−1)X + X = X·q²`
(`hkey`) at each step — no closed-form finite-geometric-series lemma is needed. -/
private lemma geom_tele (q L K : ℕ) (hq : 1 ≤ q) (hK : K ≤ L) :
    (q ^ 2 - 1) * ∑ k ∈ Finset.Icc 1 K, q ^ (2 * (L - k)) + q ^ (2 * (L - K)) = q ^ (2 * L) := by
  have hkey : ∀ X : ℕ, (q ^ 2 - 1) * X + X = X * q ^ 2 := by
    intro X
    have h1 : q ^ 2 - 1 + 1 = q ^ 2 := by
      have h0 : 1 ≤ q ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
      omega
    calc (q ^ 2 - 1) * X + X = (q ^ 2 - 1 + 1) * X := by ring
      _ = q ^ 2 * X := by rw [h1]
      _ = X * q ^ 2 := by ring
  induction K with
  | zero => simp
  | succ K ih =>
    have hK' : K ≤ L := by omega
    have key := ih hK'
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), Nat.mul_add]
    have hLK : 2 * (L - K) = 2 * (L - (K + 1)) + 2 := by omega
    rw [hLK, pow_add] at key
    rw [add_assoc, hkey]
    omega

/-- Termwise bound feeding `hex3U_le`: for `1 ≤ k ≤ (N−1)/3`, twice the `k`-summand of `hex3U`
is bounded by `(N−2) · q^(2N−2k−2)`, via G.68's bound on `hex3R` and `q^M − 1 ≤ q^M`
(`M := N − 3k`). -/
private lemma hex3U_term_bound (q N k : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N)
    (hk : k ∈ Finset.Icc 1 ((N - 1) / 3)) :
    2 * (q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k)))
      ≤ (N - 2) * q ^ (2 * N - 2 * k - 2) := by
  simp only [Finset.mem_Icc] at hk
  obtain ⟨hk1, hkK⟩ := hk
  have h3k : 3 * k ≤ N - 1 := by
    have := (Nat.le_div_iff_mul_le (by norm_num)).mp hkK
    omega
  set M := N - 3 * k with hM
  have hM1 : 1 ≤ M := by omega
  have hMbound : M + 1 ≤ N - 2 := by omega
  have hstep := two_mul_hex3R_le q M hq hM1
  have hsub : q ^ M - 1 ≤ q ^ M := Nat.sub_le _ _
  have hchain : (q ^ M - 1) * (2 * hex3R q M) ≤ q ^ M * ((M + 1) * q ^ (M - 1)) :=
    Nat.mul_le_mul hsub hstep
  have hexp : q ^ (4 * k - 1) * (q ^ M * ((M + 1) * q ^ (M - 1)))
      = (M + 1) * q ^ (2 * N - 2 * k - 2) := by
    have hpoweq : 4 * k - 1 + (M + (M - 1)) = 2 * N - 2 * k - 2 := by omega
    calc q ^ (4 * k - 1) * (q ^ M * ((M + 1) * q ^ (M - 1)))
        = (M + 1) * (q ^ (4 * k - 1) * q ^ M * q ^ (M - 1)) := by ring
      _ = (M + 1) * q ^ (4 * k - 1 + (M + (M - 1))) := by rw [← pow_add, ← pow_add]; ring_nf
      _ = (M + 1) * q ^ (2 * N - 2 * k - 2) := by rw [hpoweq]
  calc 2 * (q ^ (4 * k - 1) * ((q ^ M - 1) * hex3R q M))
      = q ^ (4 * k - 1) * ((q ^ M - 1) * (2 * hex3R q M)) := by ring
    _ ≤ q ^ (4 * k - 1) * (q ^ M * ((M + 1) * q ^ (M - 1))) :=
        Nat.mul_le_mul_left _ hchain
    _ = (M + 1) * q ^ (2 * N - 2 * k - 2) := hexp
    _ ≤ (N - 2) * q ^ (2 * N - 2 * k - 2) := Nat.mul_le_mul_right _ hMbound

/-- **G.69, THEOREM HEX3.B.** `u(q,N) ≤ N·q^(2N−2)` for `N ≥ 2`, `q ≥ 2`. `EFF.HEX3` §6.2
classes this as PROOF-ONLY (no executable battery touches it); this node is the sole
disposition. -/
theorem hex3U_le (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N ≤ N * q ^ (2 * N - 2) := by
  unfold hex3U
  set K := (N - 1) / 3 with hKdef
  set S := ∑ k ∈ Finset.Icc 1 K, q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))
    with hSdef
  set T := ∑ k ∈ Finset.Icc 1 K, q ^ (2 * N - 2 * k - 2) with hTdef
  have hstep1 : 2 * S ≤ (N - 2) * T := by
    have hsum := Finset.sum_le_sum
      (fun k hk => hex3U_term_bound q N k hq hN hk) (s := Finset.Icc 1 K)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
    exact hsum
  have hTeq : T = ∑ k ∈ Finset.Icc 1 K, q ^ (2 * ((N - 1) - k)) := by
    rw [hTdef]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h3k : 3 * k ≤ N - 1 := by
      have := (Nat.le_div_iff_mul_le (by norm_num)).mp hk.2
      omega
    congr 1
    omega
  have hKL : K ≤ N - 1 := by
    rw [hKdef]
    exact Nat.div_le_self _ _
  have hgeom := geom_tele q (N - 1) K (by omega) hKL
  have hL2 : 2 * (N - 1) = 2 * N - 2 := by omega
  rw [hL2] at hgeom
  have hstep2 : (q - 1) * (q + 1) * T ≤ q ^ (2 * N - 2) := by
    rw [hTeq]
    have hfact : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h := Nat.sq_sub_sq q 1
      simpa [mul_comm] using h
    rw [hfact] at hgeom
    omega
  have hq3 : 3 * (q - 1) ≤ (q - 1) * (q + 1) := by nlinarith
  have hstep3 : 2 * (q - 1) * (q + 1) * S ≤ (N - 2) * q ^ (2 * N - 2) := by
    calc 2 * (q - 1) * (q + 1) * S = (q - 1) * (q + 1) * (2 * S) := by ring
      _ ≤ (q - 1) * (q + 1) * ((N - 2) * T) := by
          exact Nat.mul_le_mul_left _ hstep1
      _ = (N - 2) * ((q - 1) * (q + 1) * T) := by ring
      _ ≤ (N - 2) * q ^ (2 * N - 2) := Nat.mul_le_mul_left _ hstep2
  have hstep4 : (q - 1) * S ≤ (N - 2) * q ^ (2 * N - 2) := by
    have h6 : 6 * ((q - 1) * S) ≤ 2 * (q - 1) * (q + 1) * S := by nlinarith [hq3]
    omega
  have hfinal : (q - 1) * S ≤ (N - 1) * q ^ (2 * N - 2) := by
    have : (N - 2) * q ^ (2 * N - 2) ≤ (N - 1) * q ^ (2 * N - 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  change q ^ (2 * N - 2) + (q - 1) * S ≤ N * q ^ (2 * N - 2)
  have : N * q ^ (2 * N - 2) = q ^ (2 * N - 2) + (N - 1) * q ^ (2 * N - 2) := by
    have hN1 : N = 1 + (N - 1) := by omega
    calc N * q ^ (2 * N - 2) = (1 + (N - 1)) * q ^ (2 * N - 2) := by rw [← hN1]
      _ = q ^ (2 * N - 2) + (N - 1) * q ^ (2 * N - 2) := by ring
  omega

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.hex3U_le

end AxCheck
