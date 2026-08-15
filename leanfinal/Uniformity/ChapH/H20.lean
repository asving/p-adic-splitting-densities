/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H19

/-!
# Uniformity.ChapH.H20 — THE GENERAL BRACKET

**Chapter H, NODE H.20** (`blueprint/CHAP-H_general_induction.md` §4). The closed form of the
α-prefix aggregate `alphaBracket` (H.18): for `2 ≤ Q`, `1 ≤ c` and every `μ ≥ 1`,

`Q · alphaBracket Q c μ = (Q − 1) · Q ^ ((c + 1) · μ)`,

equivalently `b_{m,d}(μ) = alphaBracket Q c μ = (Q − 1) · Q ^ ((c + 1)μ − 1)`, the corpus's
display. The `Q *` form is the primary statement because it is **subtraction-free in the
exponent**; the displayed form is the three-line corollary `alphaBracket_eq` (the blueprint's
SPLIT MANDATE: two declarations, one node file, the first being what every §10 consumer uses).

## The proof, in words

Induction on `μ` from `1` (`Nat.le_induction`). At `μ = 1` the defining recursion has a single
composition, `alphaBracket Q c 1 = (Q−1)Q^c`, and `Q·(Q−1)Q^c = (Q−1)Q^{c+1} = (Q−1)Q^{(c+1)·1}`.
The step is H.19's telescoping recursion `alphaBracket Q c (μ+1) = Q^{c+1} · alphaBracket Q c μ`:
multiplying by `Q` and applying the induction hypothesis gives
`Q^{c+1} · (Q−1) Q^{(c+1)μ} = (Q−1) Q^{(c+1)(μ+1)}` by `pow_add`. The corollary cancels the `Q`
using `0 < Q` and `1 ≤ (c+1)μ`, so the `ℕ`-subtraction in the exponent is guarded.

DEPENDS: H.18 (`alphaBracket`), H.19 (`alphaBracket_succ`).

SOURCE: `EFF.GENIND.22` (the display and its proof); `EFF.GENIND.09` (`GENIND.A`(II)'s bracket
with the **WINDOW CONDITION** `mμ ≤ N−1`, `[r1, PE1-M1]`).

**⚠ THE WINDOW CONDITION IS NOT A HYPOTHESIS OF THIS NODE — DELIBERATELY** (blueprint,
mandatory). `EFF.GENIND.22`'s own CONDITIONALITY reads: *"The generating-function identity is
unconditional; the **realized-history** reading carries `mμ ≤ N−1`."* This node states the
identity, so it carries `2 ≤ Q`, `1 ≤ c`, `1 ≤ μ` and nothing else — hypotheses at their true
minimum (the G.28 lesson). The window condition belongs to the *consumer* that interprets
`alphaBracket` as a realized-history aggregate; it appears as a hypothesis of H.67/H.71, not here.

ARITHMETIC AUDIT (blueprint, recomputed at `Q = 2`, `Q = 3` AND `Q = 4`; all six cells are
re-executed in the numeric gate below):
* `Q = 4, c = 1, μ = 2`: compositions of `2` give `(4−1)·4² = 48` and `[(4−1)·4]² = 144`, sum
  `192`; closed form `(Q−1)Q^{(c+1)μ−1} = 3·4³ = 192`, and `Q·B = 768 = 3·4⁴`.
* `Q = 2, c = 1, μ = 3`: `(3) → 8`, `(2,1) → 8`, `(1,2) → 8`, `(1,1,1) → 8`, sum `32 = 1·2⁵`.
* `Q = 3, c = 1, μ = 2`: `(2) → 18`, `(1,1) → 36`, sum `54 = 2·3³`. **This is the check the G.23
  lesson demands** — at `Q = 2` the two composition terms are equal (`8 = 8`), which would hide a
  symmetry-factor error; at `Q = 3` they differ (`18 ≠ 36`), so the sum genuinely tests the
  convolution.
* `Q = 3, c = 3, μ = 2`: `(2) → 1458`, `(1,1) → 2916`, sum `4374 = 2·3⁷`.
* `Q = 2, c = 6, μ = 1`: `64 = 1·2⁶`.
* `Q = 2, c = 10, μ = 2`: `2²⁰ + 2²⁰ = 2²¹ = 1·2^{11·2−1}`.
The six cells cover `m ∈ {2,3,4,5}` and `Q ∈ {2,3,4}` — a strict superset of the corpus's own
24-cell tooth grid.

TEETH: `GT-BRACKETID [SYM]` (`EFF.GENIND.09`, `.22`; executable regression, symbolic identity
check at `m ∈ {2,3,4,5}`, `μ ∈ {1,2,3}`, `q ∈ {2,3}`, §S11 P-7 "24/24", tooth `GT-T-BRACKET` at
its preregistered count 24) → **Lean theorem**: this node is the general law those 24 cells
instantiate.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.20, THE GENERAL BRACKET.** `Q · b(μ) = (Q−1) · Q^{(c+1)μ}` for every `μ ≥ 1` — the
closed form of `GENIND-2(b)`'s α-prefix aggregate, written subtraction-free in the exponent. -/
theorem alphaBracket_closed (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    Q * alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ) := by
  induction μ, hμ using Nat.le_induction with
  | base =>
      -- `alphaBracket Q c 1` is the single composition `(1)` of `1`.
      have h1 : alphaBracket Q c 1 = (Q - 1) * Q ^ c := by
        rw [alphaBracket, Finset.sum_range_one]
        norm_num [alphaBracket]
      rw [h1, Nat.mul_one, pow_succ]
      ring
  | succ ν hν ih =>
      rw [alphaBracket_succ Q c hQ hc hν]
      have hexp : (c + 1) * (ν + 1) = (c + 1) * ν + (c + 1) := by ring
      calc Q * (Q ^ (c + 1) * alphaBracket Q c ν)
          = Q ^ (c + 1) * (Q * alphaBracket Q c ν) := by ring
        _ = Q ^ (c + 1) * ((Q - 1) * Q ^ ((c + 1) * ν)) := by rw [ih]
        _ = (Q - 1) * (Q ^ ((c + 1) * ν) * Q ^ (c + 1)) := by ring
        _ = (Q - 1) * Q ^ ((c + 1) * ν + (c + 1)) := by rw [← pow_add]
        _ = (Q - 1) * Q ^ ((c + 1) * (ν + 1)) := by rw [hexp]

/-- **NODE H.20, the corpus's displayed form.** `b(μ) = (Q−1) · Q^{(c+1)μ−1}`. The `ℕ`-subtraction
is guarded by `1 ≤ (c+1)μ`, which `1 ≤ μ` supplies; the cancellation of the leading `Q` uses
`0 < Q` from `hQ`. -/
theorem alphaBracket_eq (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ - 1) := by
  have hNpos : 0 < (c + 1) * μ := Nat.mul_pos (Nat.succ_pos c) hμ
  obtain ⟨N, hN⟩ : ∃ N, (c + 1) * μ = N + 1 := ⟨(c + 1) * μ - 1, by omega⟩
  rw [hN, Nat.add_sub_cancel]
  refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < Q) ?_
  rw [alphaBracket_closed Q c hQ hc hμ, hN, pow_succ]
  ring

end Uniformity.Density.Induction

/-! ## Numeric gate — the closed form against the definition.
`#guard` fails elaboration when the proposition evaluates to `false`, so these are build-time
checks. Both `Q = 2` and `Q ≥ 3` appear: at `Q = 2` the letter factor `(Q − 1) = 1` disappears and
the two `μ = 2` composition terms coincide, so a `Q = 2`-only audit can see neither a missing
`(Q − 1)` nor a symmetry-factor error. -/

section NumericGate

open Uniformity.Density.Induction

-- The stub's grid: `Q ∈ {2,3,4,5}`, `c ∈ {1,2,3}`, `μ ∈ {1,2,3,4}`, both declarations.
#guard [2, 3, 4, 5].all fun Q => [1, 2, 3].all fun c => [1, 2, 3, 4].all fun μ =>
  Q * alphaBracket Q c μ == (Q - 1) * Q ^ ((c + 1) * μ)

#guard [2, 3, 4, 5].all fun Q => [1, 2, 3].all fun c => [1, 2, 3, 4].all fun μ =>
  alphaBracket Q c μ == (Q - 1) * Q ^ ((c + 1) * μ - 1)

-- The blueprint's six audit cells, at their recomputed values.
#guard alphaBracket 4 1 2 == 192 && 4 * alphaBracket 4 1 2 == 768
#guard alphaBracket 2 1 3 == 32
#guard alphaBracket 3 1 2 == 54
#guard alphaBracket 3 3 2 == 4374
#guard alphaBracket 2 6 1 == 64
#guard alphaBracket 2 10 2 == 2 ^ 21

-- `μ = 0` is genuinely EXCLUDED (so `hμ` is load-bearing): `b(0) = 1`, while the closed form would
-- read `(Q−1)·Q⁰ = Q−1`.
#guard [2, 3, 4, 5].all fun Q => [1, 2, 3].all fun c =>
  !(Q * alphaBracket Q c 0 == (Q - 1) * Q ^ ((c + 1) * 0))

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaBracket_closed
#print axioms Uniformity.Density.Induction.alphaBracket_eq

end AxCheck
