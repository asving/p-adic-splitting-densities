/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E07 — the jump arithmetic (THEOREM HE7.C's bounds, exponent form)

**Chapter E, NODE E.07** (`blueprint/CHAP-E_sigma_ladder.md` §3, **as REPAIRED by amendment
A-E.1/E-D11**). Three clauses of pure `ℕ`-arithmetic, the cleared (division-free) form of
THEOREM HE7.C's mass bounds:

* `jump_floor` — **(i) the jump floor**: `2 ≤ m` and `2 ≤ p` give `4 ≤ m * p`. The corpus
  instance is `L_λ ≥ ℓ·m·d_r = m·(ℓ d_r) ≥ 2·2 = 4`, so `μ ≥ 4` at every level jump; the
  `[r1]` rider widens the hypothesis to the PRODUCT `ℓ·d_r ≥ 2`, covering both branches
  (`ℓ ≥ 2, d_r ≥ 1` and `ℓ = 1, d_r ≥ 2`).
* `jump_halving` — **(ii) the halving**: `2 ≤ p` and `μ₂ * p ≤ μ` give `2 * μ₂ ≤ μ`; the
  corpus's `μ₂ ≤ μ/(ℓ d_r) ≤ μ/2`, cleared of division.
* `jump_count_bound` — **(iii) the jump count**: `2 ^ (J + 1) ≤ μ 0`, the cleared form of
  `J ≤ log₂ μ − 1` (`EFF.HE7.15`).

## The A-E.1/E-D11 hypothesis repair (statement-level; the blueprint is authority)

Clause (iii) is signed at the **REPAIRED** hypotheses: the `4 ≤ μ i` floor ranges over
`∀ i < J` — the jump STARTS — and the conclusion is guarded by `hJ : 1 ≤ J`. The committed form
(`h4 : ∀ i ≤ J`, no `hJ`) put the floor on the jump TARGET as well, which the source does not do:
`EFF.HE7.15`'s CANONICAL STATEMENT asserts `μ ≥ 4` of the node *requiring* the jump and only the
halving `μ₂ ≤ μ/2` of the problem it *opens*, and its DERIVATION's floor-carrying levels `1..J`
are exactly the `J` jump-HOSTING levels. Under the blueprint's 0-based dictionary
`μ i := μ_{i+1}` that reads `4 ≤ μ i` for `i = 0..J−1`.

The committed floor is not merely slack: it excludes the corpus's own configurations (`n = 8`,
`μ = 4 → μ₂ = 2`; COROLLARY HE7.B(i)'s edge `μ = 7 → μ₂ = 3`; ANNEX R R1.3's machine-exhibited
`n = 16` family `8 → 4 → 2`), and it is what made E.60's clause 3 vacuous. The `1 ≤ J` guard is
forced and honest: with no jump the hypotheses are empty and `2 ^ (0+1) ≤ μ 0` — "the mass is at
least 2" — is not a corpus claim (a terminal `μ = 1` leaf is a configuration).

**Recorded divergence:** `leanspec/Leanspec/ChapE.lean` signed clause (iii) at the PRE-repair
hypotheses (statement-level defects are repaired blueprint-side, never patched in the stub file,
CHAP-H §15 rule 5). That stub is re-signed to the form below in this node's landing commit.

DEPENDS: none · mathlib `Nat.mul_le_mul`, `Nat.pow_succ`.

SOURCE: `EFF.HE7.15` (THEOREM HE7.C `[r1]`: "`μ ≥ L_λ = ℓ·deg R_λ ≥ ℓ·m·d_r = m·(ℓ·d_r) ≥ 2·2 =
4`", "`μ₂ ≤ … ≤ μ/(ℓd_r) ≤ μ/2`", "if jumps occur at levels 1..J then `μ_i ≥ 4` for `i ≤ J` and
`μ_J ≤ μ/2^{J−1}`, so `4 ≤ μ/2^{J−1}`, i.e. `J ≤ log₂ μ − 1`"); `EFF.HE7.14` (the
non-propagation arithmetic `L_{λ₂} ≥ m₂·(ℓ₂ deg r₂) ≥ 4`, hence `μ₂ ≥ 4`).

Consumed by E.60 and E.64. E.64 (`depth3_needs_16`) consumes only the necessary direction of the
`n = 16` sentence (ANNEX R R3's rider: the displays prove `J ≥ 2 ⟹ μ ≥ 8 ⟹ n ≥ 16`); no
chapter-E node states the existential.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.07(i)** the jump floor: a node requiring a level jump has mass at least `4`
(`EFF.HE7.15`'s `m·(ℓ·d_r) ≥ 2·2 = 4`). -/
theorem jump_floor {m p : ℕ} (hm : 2 ≤ m) (hp : 2 ≤ p) : 4 ≤ m * p := by
  calc (4 : ℕ) = 2 * 2 := by norm_num
    _ ≤ m * p := Nat.mul_le_mul hm hp

/-- **E.07(ii)** the halving: `μ₂ * p ≤ μ` with `2 ≤ p` gives `2 * μ₂ ≤ μ` — the corpus's
`μ₂ ≤ μ/(ℓ d_r) ≤ μ/2`, cleared of division. -/
theorem jump_halving {μ μ₂ p : ℕ} (hp : 2 ≤ p) (h : μ₂ * p ≤ μ) : 2 * μ₂ ≤ μ := by
  calc 2 * μ₂ = μ₂ * 2 := Nat.mul_comm 2 μ₂
    _ ≤ μ₂ * p := Nat.mul_le_mul (le_refl μ₂) hp
    _ ≤ μ := h

/-- **E.07(iii)** the jump count, at the A-E.1/E-D11 hypotheses: the `4 ≤ μ i` floor is carried
by the jump STARTS (`∀ i < J`), and the bound is guarded by `1 ≤ J`. Conclusion
`2 ^ (J + 1) ≤ μ 0` is the cleared form of `J ≤ log₂ μ − 1` (`EFF.HE7.15`). -/
theorem jump_count_bound (μ : ℕ → ℕ) (J : ℕ) (hJ : 1 ≤ J)
    (h4 : ∀ i < J, 4 ≤ μ i) (hh : ∀ i < J, 2 * μ (i + 1) ≤ μ i) :
    2 ^ (J + 1) ≤ μ 0 := by
  -- Induction on `J` started at `J = 1`, with the sequence generalized: the step applies the
  -- inductive hypothesis to the SHIFTED sequence `i ↦ μ (i + 1)`.
  have key : ∀ J : ℕ, ∀ ν : ℕ → ℕ, 1 ≤ J → (∀ i < J, 4 ≤ ν i) →
      (∀ i < J, 2 * ν (i + 1) ≤ ν i) → 2 ^ (J + 1) ≤ ν 0 := by
    intro J
    induction J with
    | zero => intro ν hJ0 _ _; exact absurd hJ0 (by omega)
    | succ J ih =>
      intro ν _ hν4 hνh
      rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
      · -- Base `J = 1`: `2 ^ 2 = 4 ≤ ν 0` is the floor at the single jump start `i = 0`.
        subst hJ0
        have h0 : 4 ≤ ν 0 := hν4 0 (by omega)
        calc 2 ^ (0 + 1 + 1) = 4 := by norm_num
          _ ≤ ν 0 := h0
      · -- Step: the shifted sequence has floors `hν4 (i+1)` and halvings `hνh (i+1)` for
        -- `i < J`, giving `2 ^ (J + 1) ≤ ν 1`; then halve once more at `i = 0`.
        have hshift : 2 ^ (J + 1) ≤ ν 1 :=
          ih (fun i => ν (i + 1)) hJpos (fun i hi => hν4 (i + 1) (by omega))
            (fun i hi => hνh (i + 1) (by omega))
        calc 2 ^ (J + 1 + 1) = 2 * 2 ^ (J + 1) := by ring
          _ ≤ 2 * ν 1 := Nat.mul_le_mul (le_refl 2) hshift
          _ ≤ ν 0 := hνh 0 (by omega)
  exact key J μ hJ h4 hh

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.jump_floor
#print axioms Uniformity.Density.Ladder.jump_halving
#print axioms Uniformity.Density.Ladder.jump_count_bound

end AxCheck
