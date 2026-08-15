/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H20

/-!
# Uniformity.ChapH.H21 — the `(CS-2)` numeric certificate, and the mass/letter reconciliation

**Chapter H, NODE H.21** (`blueprint/CHAP-H_general_induction.md` §4). Four closed numeric facts
about H.18's α-prefix aggregate `alphaBracket`, packaged as two theorems:

* `alphaBracket_audit` — the bracket audit,
  `alphaBracket 4 1 2 = 192` (`= 48 + 144`), `alphaBracket 3 1 2 = 54` (`= 18 + 36`),
  `alphaBracket 2 1 3 = 32`;
* `massNorm_eq_ghost_mul_letters` — the **ghost × letters = mass** reconciliation at `|K| = 4`,
  `μ = 2`, `c = 1`: `4 ^ 2 * ((4 − 1) * 4 ^ 1) = alphaBracket 4 1 2`, i.e. `16 · 12 = 192`.

Both are proved by evaluating the recursion (`Finset.sum_range_succ` on the defining equation),
not by `decide`: `alphaBracket` is a well-founded recursion, so the kernel does not unfold it.

DEPENDS: H.18 (`alphaBracket`), H.20 (`alphaBracket_eq`, used only for the cross-check in the
numeric gate — the theorems themselves are proved by evaluation).

SOURCE: `EFF.GENIND.64`'s in-line numeric certificate, verbatim: *"Checked numerically this round
at `(q, μ″) = (2, 2)`, `|K| = 4` (genre F, `c(2) = 1`): composition sum
`Σ_{(k₁..k_r), Σk_i=2} Π_i (|K|−1)|K|^{k_i} = 48 + 144 = 192 = (|K|−1)|K|³` (mass form);
letters-only `Σ (|K|−1)^r = 3 + 9 = 12 = (|K|−1)|K|¹` (GENH4 form); ghost `|K|² = 16`;
`16 · 12 = 192`."*; `EFF.GENHN.36` (the same reconciliation
`(|K|−1)|K|^{2κ−1} = |K|^{κ} · (|K|−1)|K|^{κ−1}`).

**⚠ WHY THE RECONCILIATION IS A NODE** (blueprint, mandatory). `EFF.GENIND.64`'s NORMALIZATION
DECLARATION is the corpus's own warning that *"a discharge of `(CS-2)` in the wrong normalization
would be off by the ghost factor `|K|^{μ″}`, invisible at genre E and visible at genre F"*.
`StageInterface.hbracket` (H.09) is stated in the **mass** normalization; the second theorem is
the machine check that the mass form is the one whose ghost factor is `|K|^{c(μ)μ}`, so a genre-F
instance built from `GENH4`'s letter-sum form fails to satisfy `hbracket` — loudly, at elaboration
time, which is the point.

ARITHMETIC AUDIT (blueprint; every cell is re-executed in the numeric gate below).
* Clause (i), `Q = 4, c = 1, μ = 2`: compositions of `2` contribute `(4−1)·4² = 48` and
  `[(4−1)·4]² = 144`; `48 + 144 = 192`.
* Clause (ii), `Q = 3, c = 1, μ = 2`: `(2) → 18`, `(1,1) → 36`, `18 + 36 = 54`. **This is the
  non-degenerate cell** the `q = 2`-only regime would have hidden (`18 ≠ 36`, whereas at `q = 2`
  the two composition terms coincide and a symmetry-factor error is invisible).
* Clause (iii), `Q = 2, c = 1, μ = 3`: `(3), (2,1), (1,2), (1,1,1) → 8 + 8 + 8 + 8 = 32`.
* Clause (iv): ghost `|K|^μ = 4² = 16`, letters `Σ_r (|K|−1)^r = 3 + 9 = 12 = (|K|−1)|K|¹`,
  product `16 · 12 = 192 = ` mass.
* Genre-E invisibility, recomputed: with `|K| = q` and `δ = 2μ″` integer `dv`-points the
  letter-sum reads `(q−1)q^{δ−1} = (q−1)q^{2μ″−1}`, which **equals** the mass form
  `(q−1)q^{(c(2)+1)μ″−1}` — so at genre E the two normalizations coincide numerically and the gap
  is genuinely invisible, exactly as `EFF.GENIND.64` claims. Genre-F gap: mass
  `(q²−1)(q²)^{2μ−1}` ÷ letters `(q²−1)(q²)^{μ−1} = (q²)^{μ}` = the ghost.

TEETH: `EFF.GENIND.64`'s **`arithmetic recount`** (a compiler-verifiable certificate embedded in
the statement) → **Lean theorem**. No battery row exercises `(CS-2)` at any genre (`signed vacuity
disclosure` at `EFF.GENIND.64`), so this node is the *only* machine guard on the normalization, at
any grade, anywhere.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-! The two base unfoldings of the recursion, shared by every clause below: `μ = 2` and `μ = 3`
then follow by `Finset.sum_range_succ`. These are file-private evaluation helpers, not part of
the node's contract. -/

/-- `alphaBracket Q c 0 = 1` — the empty composition. -/
private theorem alphaBracket_zero (Q c : ℕ) : alphaBracket Q c 0 = 1 := by
  rw [alphaBracket]

/-- `alphaBracket Q c 1 = (Q−1)·Q^c` — the single composition `(1)` of `1`. -/
private theorem alphaBracket_one (Q c : ℕ) : alphaBracket Q c 1 = (Q - 1) * Q ^ c := by
  rw [alphaBracket, Finset.sum_range_one, alphaBracket_zero]
  ring

/-- **NODE H.21, clauses (i)–(iii): the bracket audit.** The three `(CS-2)` certificate cells of
`EFF.GENIND.64`, at `|K| = 4` (genre F, `c(2) = 1`), at `q = 3` (the non-degenerate cell) and at
`q = 2, μ = 3`. -/
theorem alphaBracket_audit :
    alphaBracket 4 1 2 = 192 ∧ alphaBracket 3 1 2 = 54 ∧ alphaBracket 2 1 3 = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · -- `48 + 144 = 192`: the compositions `(2)` and `(1,1)` of `2`.
    rw [show (2 : ℕ) = 1 + 1 from rfl, alphaBracket, Finset.sum_range_succ,
      Finset.sum_range_one, alphaBracket_zero, alphaBracket_one]
    norm_num
  · -- `18 + 36 = 54`: the same two compositions at `Q = 3`, where they DIFFER.
    rw [show (2 : ℕ) = 1 + 1 from rfl, alphaBracket, Finset.sum_range_succ,
      Finset.sum_range_one, alphaBracket_zero, alphaBracket_one]
    norm_num
  · -- `8 + 8 + 8 + 8 = 32`: the four compositions of `3` at `Q = 2`.
    rw [show (3 : ℕ) = 2 + 1 from rfl, alphaBracket, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, alphaBracket_zero, alphaBracket_one]
    rw [show (2 : ℕ) - 0 = 1 + 1 from rfl, alphaBracket, Finset.sum_range_succ,
      Finset.sum_range_one, alphaBracket_zero, alphaBracket_one]
    norm_num

/-- **NODE H.21, clause (iv): the normalization reconciliation.** `ghost × letters = mass` at
`|K| = 4`, `μ = 2`, `c = 1`: the ghost factor `|K|^μ = 16` times the letters-only `GENH4` form
`(|K|−1)|K|^{μ−1} = 12` is the mass form `alphaBracket 4 1 2 = 192`. A `(CS-2)` discharge in the
letter normalization is off by exactly the ghost, and this is the machine guard that says so. -/
theorem massNorm_eq_ghost_mul_letters :
    (4 : ℕ) ^ 2 * ((4 - 1) * 4 ^ 1) = alphaBracket 4 1 2 := by
  rw [alphaBracket_audit.1]
  norm_num

end Uniformity.Density.Induction

/-! ## Numeric gate — the certificate's own arithmetic, re-executed.
`#guard` fails elaboration when the proposition evaluates to `false`, so every line below is a
build-time check, not a print-out. Both `q = 2` and `q = 3` appear (plus `Q = 4 = q²`, which is
the genre-F ambient the reconciliation is stated at), per the chapter's two-column rule. -/

section NumericGate

open Uniformity.Density.Induction

-- Clause (i): the mass sum at `|K| = 4`, term by term — `48 + 144 = 192`.
#guard alphaBracket 4 1 2 == 192
#guard (4 - 1) * 4 ^ 2 == 48
#guard ((4 - 1) * 4 ^ 1) * ((4 - 1) * 4 ^ 1) == 144
#guard 48 + 144 == 192

-- Clause (ii): the non-degenerate cell at `q = 3` — `18 + 36 = 54`, and `18 ≠ 36`.
#guard alphaBracket 3 1 2 == 54
#guard (3 - 1) * 3 ^ 2 == 18
#guard ((3 - 1) * 3 ^ 1) * ((3 - 1) * 3 ^ 1) == 36
#guard 18 + 36 == 54
#guard !((3 - 1) * 3 ^ 2 == ((3 - 1) * 3 ^ 1) * ((3 - 1) * 3 ^ 1))

-- The `q = 2` degeneracy the `q = 3` cell exists to expose: there the two terms COINCIDE.
#guard (2 - 1) * 2 ^ 2 == ((2 - 1) * 2 ^ 1) * ((2 - 1) * 2 ^ 1)

-- Clause (iii): four compositions of `3` at `q = 2`, all worth `8`.
#guard alphaBracket 2 1 3 == 32
#guard 8 + 8 + 8 + 8 == 32

-- Clause (iv): ghost × letters = mass, at `|K| = 4`, `μ = 2`, `c = 1`.
#guard (4 : ℕ) ^ 2 == 16                      -- ghost `|K|^μ`
#guard (4 - 1) + (4 - 1) * (4 - 1) == 12      -- letters-only `Σ_r (|K|−1)^r = 3 + 9`
#guard (4 - 1) * 4 ^ 1 == 12                  -- ... `= (|K|−1)|K|^{μ−1}`, the `GENH4` form
#guard 16 * 12 == 192
#guard (4 : ℕ) ^ 2 * ((4 - 1) * 4 ^ 1) == alphaBracket 4 1 2

-- The cross-check against H.20's closed form (`alphaBracket_eq`): mass `= (Q−1)Q^{(c+1)μ−1}`.
#guard alphaBracket 4 1 2 == (4 - 1) * 4 ^ ((1 + 1) * 2 - 1)
#guard alphaBracket 3 1 2 == (3 - 1) * 3 ^ ((1 + 1) * 2 - 1)
#guard alphaBracket 2 1 3 == (2 - 1) * 2 ^ ((1 + 1) * 3 - 1)

/-! ### The normalization gap itself, at both genres.
Genre E (`|K| = q`, `c(2) = 1`, so `δ = 2μ`): the letter form `(q−1)q^{δ−1}` and the mass form
`(q−1)q^{(c+1)μ−1}` are EQUAL — the gap is invisible, exactly as `EFF.GENIND.64` warns. Genre F
(`|K| = q²`): mass ÷ letters `= (q²)^μ = ` the ghost, i.e. the gap is visible and is a whole power
of `|K|`. -/

-- Genre E, `q ∈ {2,3,5}`, `μ ∈ {1,2,3,4}`: letters = mass (invisible).
#guard [2, 3, 5].all fun q => [1, 2, 3, 4].all fun μ =>
  (q - 1) * q ^ (2 * μ - 1) == alphaBracket q 1 μ

-- Genre F, same grid at `|K| = q²`: mass = ghost × letters, and the ghost is `> 1` for `μ ≥ 1`.
#guard [2, 3, 5].all fun q => [1, 2, 3, 4].all fun μ =>
  alphaBracket (q ^ 2) 1 μ == (q ^ 2) ^ μ * ((q ^ 2 - 1) * (q ^ 2) ^ (μ - 1))

#guard [2, 3, 5].all fun q => [1, 2, 3, 4].all fun μ =>
  !(alphaBracket (q ^ 2) 1 μ == (q ^ 2 - 1) * (q ^ 2) ^ (μ - 1))

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaBracket_audit
#print axioms Uniformity.Density.Induction.massNorm_eq_ghost_mul_letters

end AxCheck
