/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Uniformity.ChapH.H37 — the genre-count polynomial bound

**Chapter H, NODE H.37** (`blueprint/CHAP-H_general_induction.md` §6). The number of
`(partition-arrangement type, slope tuple)` pairs available to a β-genre at window `N` is at most
`p * N^m`, where `p` is the number of arrangement types at multiplicity `m`: each of at most `m`
sides carries one integer slope in `[1, N−1]`. This node proves the `N`-dependent half — the set
of slope tuples `{s : Fin m → ℕ | ∀ i, 1 ≤ s i ∧ s i ≤ N − 1}` has `Nat.card ≤ N ^ m`.

DEPENDS: none (mathlib only: `Nat.card_le_card_of_injective`, `Nat.card_fun`).

SOURCE: `EFF.GENIND.152` (`GENIND-C1`(iv)): *"a β-genre's datum at window `N` is a partition
arrangement of `m` (finitely many types for fixed `m`) plus one integer slope per side, each slope
`≤ v(a₀) ≤ N−1`: at most `p̃(m)·N^m` live genres — polynomial in `N` of degree `≤ m`"*.

⚠ SCOPE. `p̃(m)`, the number of *arrangement types*, is frame-grammar data (chapter C) and is NOT
computed here; it is `N`-independent and is absorbed into the rate closure's `K` (H.71 carries it
as an opaque `ℕ` parameter `p`).

Note the statement is unconditional in `N`: at `N = 0` the constraints `1 ≤ s i` and
`s i ≤ 0 − 1 = 0` are contradictory in `ℕ`, so the subtype is empty for `m ≥ 1` (and a singleton
for `m = 0`, matching `0 ^ 0 = 1`). The injection below discharges both uniformly, since
`1 ≤ s i` together with `s i ≤ N − 1` forces `s i < N` in truncated `ℕ`-arithmetic.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- **NODE H.37.** The slope-tuple count at window `N` with `m` sides is at most `N ^ m`. -/
theorem card_slopeTuples_le (m N : ℕ) :
    Nat.card {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1} ≤ N ^ m := by
  have hinj : Function.Injective
      (fun s : {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1} =>
        (fun i => (⟨s.1 i, by have := s.2 i; omega⟩ : Fin N))) := by
    intro s t hst
    apply Subtype.ext
    funext i
    have h := congrFun hst i
    simpa [Fin.ext_iff] using h
  calc Nat.card {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1}
      ≤ Nat.card (Fin m → Fin N) := Nat.card_le_card_of_injective _ hinj
    _ = N ^ m := by simp

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.card_slopeTuples_le

end AxCheck
