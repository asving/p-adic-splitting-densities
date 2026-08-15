/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64

/-!
# Uniformity.ChapG.G65 — `hex3R_rec`, the `R`-recursion

**Chapter G, NODE G.65** (`blueprint/CHAP-G_base_cases_menus.md` §9). The `R`-recursion:
`R(M) = q^(M−1) + (q−1)·∑_{j ≥ 1, 2j ≤ M−1} q^j·R(M−2j)`.

DEPENDS: G.64.

**⚠ THE SOURCE FLAGS THIS STEP AS ASSERTED** (blueprint's verbatim note carried forward).
`EFF.HEX3.27` records that HEX3 states the equivalence of the two forms without displaying it,
and that the 0a compiler verified it **numerically** (`q ∈ {2,3,4,5,7,8,9,11,13}`, `M = 1..20`,
360 checks, 0 failures) rather than symbolically. **This node is where that justification seam
is closed in Lean** — a genuine addition to the corpus's evidence, not a transcription.

**PROOF STRATEGY.** The blueprint's own recommended route (parity split on `M`) was superseded
here by a cleaner **two-step recursion** proved first as a private helper:
`hex3R q (M+2) = q²·hex3R q M + (q−1)·q^M` for `M ≥ 1` (`hex3R_two_step`), which needs no
parity case-split — the only ℕ-division fact it needs is `(a+2)/2 = a/2 + 1`, closed by
`omega`. The main recursion then follows by **strong induction on `M`** (base cases `M = 1, 2`
with an empty sum; step `M = m+3` using the induction hypothesis at `M − 2 = m+1`): the goal's
sum is converted to `Finset.range` form (`icc1_eq_range`, a private reindexing helper via
`Finset.sum_Ico_eq_sum_range`), its first term (`j = 1`) is peeled off with
`Finset.sum_range_succ'`, and the remaining sum is matched *pointwise* (not via a closed-form
geometric identity) against the sum in the `M−2` induction hypothesis, differing by exactly a
factor of `q`. Substituting the induction hypothesis and the two-step recursion reduces the goal
to a genuine commutative-semiring identity, closed by `ring` after rewriting `q = c + 1` (via
`obtain ⟨c, rfl⟩`) to eliminate the ℕ-truncated `q − 1` from the expression entirely.

**TEETH.** `HEX3-T-FLOOR` → executable regression (retained); the 0a numeric verification →
**Lean theorem** (this node).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- The two-step form of the `R`-recursion: incrementing the window by `2` multiplies `R` by
`q²` and adds a single correction term `(q−1)·q^M`. Needs no parity case-split; the only
ℕ-division fact used is `(a+2)/2 = a/2 + 1`, closed directly by `omega`. Feeds `hex3R_rec`'s
strong-induction step. -/
private lemma hex3R_two_step (q M : ℕ) (hM : 1 ≤ M) :
    hex3R q (M + 2) = q ^ 2 * hex3R q M + (q - 1) * q ^ M := by
  match M, hM with
  | 1, _ => simp [hex3R]
  | (m + 2), _ =>
    have hdiv : (m + 1 + 2) / 2 = (m + 1) / 2 + 1 := by omega
    have heq1 :
        hex3R q (m + 2 + 2) = q ^ (m + 3) + ((m + 1 + 2) / 2) * ((q - 1) * q ^ (m + 2)) := by
      change hex3R q (m + 4) = _
      unfold hex3R
      congr 2
    have heq2 : hex3R q (m + 2) = q ^ (m + 1) + ((m + 1) / 2) * ((q - 1) * q ^ m) := by
      unfold hex3R
      congr 2
    rw [heq1, heq2, hdiv]
    ring

/-- Reindex a sum over `Finset.Icc 1 K` as a sum over `Finset.range K`, shifting the summand by
one. Used to peel the bottom term (`j = 1`) of `hex3R_rec`'s sum via `Finset.sum_range_succ'`
and to match the remaining terms against the induction hypothesis's sum. -/
private lemma icc1_eq_range (K : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.Icc 1 K, f j = ∑ i ∈ Finset.range K, f (i + 1) := by
  rw [show Finset.Icc 1 K = Finset.Ico 1 (K + 1) from (Finset.Ico_add_one_right_eq_Icc 1 K).symm,
    Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- **G.65, the `R`-recursion.** `R(M) = q^(M−1) + (q−1)·∑_{j=1}^{⌊(M−1)/2⌋} q^j·R(M−2j)`. The
first symbolic proof of an identity the source only checked numerically (`EFF.HEX3.27`). -/
theorem hex3R_rec (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    hex3R q M
      = q ^ (M - 1) + (q - 1) * ∑ j ∈ Finset.Icc 1 ((M - 1) / 2), q ^ j * hex3R q (M - 2 * j) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    match M, hM, ih with
    | 1, _, _ => simp [hex3R]
    | 2, _, _ => simp [hex3R]
    | (m + 3), _, ih =>
      have ihM2 := ih (m + 1) (by omega) (by omega)
      simp only [show m + 1 - 1 = m from by omega] at ihM2
      have hdiv2 : (m + 3 - 1) / 2 = m / 2 + 1 := by omega
      rw [hdiv2, show m + 3 - 1 = m + 2 from by omega]
      rw [icc1_eq_range]
      rw [Finset.sum_range_succ']
      have hterm0 : q ^ (0 + 1) * hex3R q (m + 3 - 2 * (0 + 1)) = q * hex3R q (m + 1) := by
        rw [show m + 3 - 2 * (0 + 1) = m + 1 from by omega, pow_one]
      have hrest : ∑ i ∈ Finset.range (m / 2), q ^ (i + 1 + 1) * hex3R q (m + 3 - 2 * (i + 1 + 1))
          = q * ∑ i ∈ Finset.range (m / 2), q ^ (i + 1) * hex3R q (m + 1 - 2 * (i + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hexp : m + 3 - 2 * (i + 1 + 1) = m + 1 - 2 * (i + 1) := by omega
        rw [hexp]
        ring
      rw [hterm0, hrest,
        ← icc1_eq_range (m / 2) (fun x => q ^ x * hex3R q (m + 1 - 2 * x))]
      have hstep := hex3R_two_step q (m + 1) (by omega)
      have h3eq : m + 1 + 2 = m + 3 := by omega
      rw [h3eq] at hstep
      rw [hstep, ihM2]
      obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.hex3R_rec

end AxCheck
