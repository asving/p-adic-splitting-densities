/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-!
# Uniformity.ChapC.C32 — the jump-count bound, three clauses (`EFF.HE6R1.47`)

**Chapter C, NODE C.32** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §5, the descent
grammar; the A-C.1 amendment set governs). **ENV-C5** — `ℕ` and `Fin` only. One signed
declaration (`jump_count_bound`) plus the three companions the blueprint's SIGNATURE block names
(`jump_count_stage`, `jump_count_ambient`, `jump_count_ambient_sharp`).

A history's successive jumps carry multiplicities `a 0, a 1, …`; C.31 supplies the two facts
about them — `4 ≤ a j` at every jump (`jump_floor`) and `2·a (j+1) ≤ a j` at every step
(`jump_drop`). Iterating the halving against the floor bounds the NUMBER of jumps:

* **(a) any history:** `2^(J+2) ≤ 2μ` — the signed conclusion (the proof below in fact gives the
  sharper `2^(J+2) ≤ μ`, which is what the two companions consume);
* **(b) composite-stage-rooted** (`2 ≤ D′`, `n = D′μ`): `2^(J+3) ≤ n` — THE bound consumption
  sites cite, `J ≤ log₂ n − 2` cleared;
* **(c) ambient-rooted** (`D′ = 1`, `n = μ`): `2^(J+2) ≤ n` — `J ≤ log₂ n − 1` cleared, **and it
  is sharp** (`jump_count_ambient_sharp`).

## ⚠ THE INDEX SHIFT (read before citing any numeral)

The blueprint states the three clauses with `J` = **the number of jumps**; the signed Lean
signature indexes the multiplicities by `Fin (J + 1)`, so the Lean `J` is the number of
**drops**, one less:

`J_blueprint = J_lean + 1`.

Every displayed exponent therefore moves by one when it is transcribed: the blueprint's
(a) `2^(J+1) ≤ 2μ`, (b) `2^(J+2) ≤ n`, (c) `2^(J+1) ≤ n` become the Lean statements
`2^(J+2) ≤ 2μ`, `2^(J+3) ≤ n`, `2^(J+2) ≤ n` below. The signed `jump_count_bound` already
carries this shift (its own SIGNATURE comment spells it out: *"with `J+1` jumps ⇒
`2^{(J+1)+1} ≤ 2μ`"*), and the companions are stated in the same Lean indexing so that a
consumer never mixes the two conventions. **The sharpness witness is the place this matters
most**: the blueprint's "`J = 1`, `n = 4`" is `J_lean = 0` — one jump, no drop — and at
`J_lean = 0` clause (c) reads `4 ≤ 4` (equality, sharp) while clause (b) would read `8 ≤ 4`
(false). That contrast is exactly the frozen display's refutation, and it is landed as
arithmetic in `jump_count_ambient_sharp`.

## What is DEAD here (C-H8 discipline)

The frozen unconditional display `J ≤ log₂ n − 2` — clause (b)'s bound asserted at every root —
is **withdrawn at ambient roots and DEAD** (`EFF.HE6R1.43`'s obstruction record; the R7/A4
quartic witness `m = 2, ℓ = 1, d_r = 2`, side length `4 = μ = n`). It survives only in the
stage-rooted form (b), where `2 ≤ D′` supplies the missing factor of two. `EFF.HE6R1.47`'s own
consumer sweep is what re-displayed it: *"THEOREM HE7.C's bounds are stage-rooted (clause (b))
and unchanged."*

## Divergences and design notes (GC-6.5; none is a new node)

* **The proof gives more than the signed conclusion.** The chain yields `2^(J+2) ≤ a 0 ≤ μ`; the
  signed statement weakens this to `≤ 2μ`. The stronger form is landed as the private
  `pow_le_head` step and re-exported through the companions (which need it: (c) is
  `2^(J+2) ≤ n` with `n = μ`, unreachable from `2^(J+2) ≤ 2μ`). The signed conclusion is kept
  byte-for-byte — a signature is frozen even when the proof proves more.
* **`hfloor` is used only at the last index.** `∀ j, 4 ≤ a j` is signed; the argument consumes
  `4 ≤ a J` alone (the intermediate floors are implied by the drops). Kept as signed.
* **No import of C.31.** C.31 is the DEPENDS edge (it supplies `hfloor`/`hdrop` for real
  histories) but this node's statement and proof are self-contained `ℕ`/`Fin` arithmetic, so the
  edge is recorded by node ID (GC-13(b)) and not by an import — the same ruling as C.31's own
  forward edge to C.33/C.35.

**DEPENDS.** C.31 (whose (iv) `jump_drop` instantiates `hdrop`, and whose (i) `jump_floor`
instantiates `hfloor`, for real histories) — by committed node ID (GC-13(b)). Mathlib:
`Nat.pow_succ`, `Nat.mul_le_mul_left`, `Fin.succ`/`Fin.castSucc`.

**PROOF.** Induction on `k`: `2^k · a ⟨k⟩ ≤ a 0`, the step being `hdrop` at `⟨k⟩` multiplied by
`2^k` (`Nat.pow_succ` + associativity). At `k = J`, `4 ≤ a ⟨J⟩` gives `2^(J+2) = 2^J·4 ≤ a 0 ≤ μ`.
(b): `2μ ≤ D′μ = n`. (c): `n = μ`. Sharpness: the one-element history `a ≡ 4` at `μ = n = 4`.

**SOURCE.** `EFF.HE6R1.47` (the owner-directive re-display, all three clauses verbatim, with the
consumer sweep); `EFF.HE6R1.43` (the obstruction record and its exact counterexample: *"`J ≤
log₂4 − 2 = 0` is contradicted by `J = 1`"*); `EFF.HE6R1.09` (the superseded unconditional
display — carried as DEAD); `EFF.HE6R1.11` (both widened-box branches supply `ℓd_r ≥ 2`, so the
drop hypothesis is available at every jump).

**TEETH.** the A4 counterexample → **Lean theorem** (`jump_count_ambient_sharp`); the `n = 8`
one-jump and `n = 16` two-jump consumption values (`EFF.HE6R1.17`(i)) → **Lean theorem
instances** of (b), the two `example`s at the end.

**ENVIRONMENT.** ENV-C5.

## Status

Sorry-free, Lean-core axioms only.
-/

namespace Uniformity.Density.Tower

/-- the halving chain, run from the head: `2^k · a ⟨k⟩ ≤ a 0` for every `k ≤ J`. -/
private theorem pow_le_head {J : ℕ} (a : Fin (J + 1) → ℕ)
    (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) :
    ∀ (k : ℕ) (hk : k < J + 1), 2 ^ k * a ⟨k, hk⟩ ≤ a 0 := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : (⟨0, hk⟩ : Fin (J + 1)) = 0 := rfl
    rw [h0, Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    intro hk
    have hkJ : k < J := by omega
    have hk' : k < J + 1 := by omega
    have hstep : 2 * a ⟨k + 1, hk⟩ ≤ a ⟨k, hk'⟩ := hdrop ⟨k, hkJ⟩
    calc 2 ^ (k + 1) * a ⟨k + 1, hk⟩ = 2 ^ k * (2 * a ⟨k + 1, hk⟩) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ k * a ⟨k, hk'⟩ := Nat.mul_le_mul_left _ hstep
      _ ≤ a 0 := ih hk'

/-- the sharp head bound the companions consume: `2^(J+2) ≤ μ` (the signed
`jump_count_bound` weakens this to `≤ 2μ`). -/
private theorem pow_le_mu {J μ : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) :
    2 ^ (J + 2) ≤ μ := by
  have hJ : 2 ^ J * a ⟨J, by omega⟩ ≤ a 0 := pow_le_head a hdrop J (by omega)
  have h4 : 2 ^ J * 4 ≤ 2 ^ J * a ⟨J, by omega⟩ := Nat.mul_le_mul_left _ (hfloor _)
  have hpow : 2 ^ (J + 2) = 2 ^ J * 4 := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
  rw [hpow]
  exact le_trans h4 (le_trans hJ ha0)

/-- **C.32 (a) — the jump-count bound.** With `a : Fin (J+1) → ℕ` the multiplicities at a
history's successive jumps (`a 0 ≤ μ`; `4 ≤ a j` at every jump, C.31(i); `2·a (j+1) ≤ a j` at
every step, C.31(iv)): `2^(J+2) ≤ 2μ`. In the blueprint's jump-count indexing
(`J_blueprint = J_lean + 1`) this is `2^(J+1) ≤ 2μ`, i.e. `J ≤ log₂ μ − 1` cleared. -/
theorem jump_count_bound {J μ : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) :
    2 ^ (J + 2) ≤ 2 * μ :=
  le_trans (pow_le_mu a ha0 hfloor hdrop) (by omega)

/-- **C.32 (b) — the stage-rooted bound**, THE one consumption sites cite. At a composite frame
(`2 ≤ D′`) with `n = D′μ`: `2^(J+3) ≤ n` (blueprint indexing: `2^(J+2) ≤ n`, `J ≤ log₂ n − 2`). -/
theorem jump_count_stage {J μ D n : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc)
    (hD : 2 ≤ D) (hn : n = D * μ) : 2 ^ (J + 3) ≤ n := by
  have hμ : 2 ^ (J + 2) ≤ μ := pow_le_mu a ha0 hfloor hdrop
  have h2μ : 2 * μ ≤ n := by
    rw [hn]
    exact Nat.mul_le_mul_right μ hD
  have hpow : 2 ^ (J + 3) = 2 * 2 ^ (J + 2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  exact le_trans (Nat.mul_le_mul_left 2 hμ) h2μ

/-- **C.32 (c) — the ambient-rooted bound.** At an ambient root (`D′ = 1`, `n = μ`):
`2^(J+2) ≤ n` (blueprint indexing: `2^(J+1) ≤ n`, `J ≤ log₂ n − 1`). This is the clause that
survives where the frozen unconditional `J ≤ log₂ n − 2` does not. -/
theorem jump_count_ambient {J μ n : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc)
    (hn : n = μ) : 2 ^ (J + 2) ≤ n := by
  rw [hn]
  exact pow_le_mu a ha0 hfloor hdrop

/-- **C.32 — sharpness of (c), and the refutation of the frozen display** (`EFF.HE6R1.43`'s
R7/A4 quartic witness `m = 2, ℓ = 1, d_r = 2`, side length `4 = μ = n`). The one-jump history
`a ≡ 4` at `μ = n = 4` satisfies every hypothesis; clause (c) holds with EQUALITY (`2^2 = 4`),
and clause (b)'s conclusion `2^3 ≤ 4` is FALSE at that root. (`J_lean = 0` is the blueprint's
`J = 1` — one jump, no drop; see the index-shift block in the module docstring.) -/
theorem jump_count_ambient_sharp :
    ∃ a : Fin (0 + 1) → ℕ, a 0 ≤ 4 ∧ (∀ j, 4 ≤ a j) ∧
      (∀ j : Fin 0, 2 * a j.succ ≤ a j.castSucc) ∧
      2 ^ (0 + 2) = 4 ∧ ¬ 2 ^ (0 + 3) ≤ 4 :=
  ⟨fun _ => 4, le_refl 4, fun _ => le_refl 4, fun j => j.elim0, by decide, by decide⟩

/-! ### TEETH — `EFF.HE6R1.17`(i)'s consumption values

One jump at `n = 8` and two jumps at `n = 16`, read off clause (b): a stage-rooted history with
`J_lean` drops needs `n ≥ 2^{J_lean+3}`, so `n = 8` admits no drop and `n = 16` admits one. -/

example {μ D n : ℕ} (a : Fin (0 + 1) → ℕ) (ha0 : a 0 ≤ μ) (hfloor : ∀ j, 4 ≤ a j)
    (hdrop : ∀ j : Fin 0, 2 * a j.succ ≤ a j.castSucc) (hD : 2 ≤ D) (hn : n = D * μ) :
    8 ≤ n := jump_count_stage a ha0 hfloor hdrop hD hn

example {μ D n : ℕ} (a : Fin (1 + 1) → ℕ) (ha0 : a 0 ≤ μ) (hfloor : ∀ j, 4 ≤ a j)
    (hdrop : ∀ j : Fin 1, 2 * a j.succ ≤ a j.castSucc) (hD : 2 ≤ D) (hn : n = D * μ) :
    16 ≤ n := jump_count_stage a ha0 hfloor hdrop hD hn

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.jump_count_bound
#print axioms Uniformity.Density.Tower.jump_count_stage
#print axioms Uniformity.Density.Tower.jump_count_ambient
#print axioms Uniformity.Density.Tower.jump_count_ambient_sharp

end AxCheck
