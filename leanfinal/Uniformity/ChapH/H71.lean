/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapH.H16
import Uniformity.ChapH.H17
import Uniformity.ChapH.H22
import Uniformity.ChapH.H30
import Uniformity.ChapH.H65

/-!
# Uniformity.ChapH.H71 — `RecursionLegs` and `rate_close`, at the A-H.2 signature

**Chapter H, NODE H.71** (`blueprint/CHAP-H_general_induction.md` §10, line 4394, as repaired by
AMENDMENT §A-H.2 at line 6838). `GENIND.C′`, the quantitative vanishing clause: package the three
legs of the `S5.2` recursion (head, α, β) as a structure, and conclude that the normalized
complement family `u` belongs to H.65's `RateSpecies` with constants `B = m + B' + 1`, `c = c' + 1`.

## Landed here

* `RecursionLegs Q m c u` — the three-leg hypothesis, at the **A-H.2** signature.
* `rate_close` — the closure theorem, at the **A-H.2** signature, PROVED (no `sorry`, Lean core
  axioms only).
* A **non-vacuity witness** (`legsHeadOnly`, `legsHeadOnly_rate`): the repaired structure is
  inhabited at `(Q, m, c) = (2, 2, 3)` — inside `rate_close`'s hypotheses, since `2 < 3` — and
  `rate_close` is fired on it. A-H.1/D7 was an inhabitation defect, so this obligation is not
  optional here.

## Re-landing record (read this before comparing against an earlier checkout)

An earlier version of this file landed `RecursionLegs` at the **A-H.1** signature and *withheld*
`rate_close`, because the then-signed statement was FALSE and this file machine-refuted it. The
refutation stands and is preserved below (§ *The refutation of the pre-A-H.2 statement*), now
framed against a **locally restated** copy of the old structure, `RecursionLegsPreAH2`, so that
the refuted claim never appears as an environment fact.

Two things changed with AMENDMENT §A-H.2, and BOTH are statement-level:

1. **`halpha` gained the WINDOW CONDITION** (`EFF.GENIND.09`'s `mμ ≤ N−1`, restored): the α-sum
   now runs over `k ∈ Finset.range n₀ with m * (k + 1) < N`, not over all `k < n₀`. This is a
   change to the `RecursionLegs` *structure*, so the structure landed here is **replaced**, not
   extended. Sanctioned because the structure had **no mathematical consumer** at replacement time
   (re-grepped 2026-08-15 across `leanfinal/`, `lean/`, `leancheck/`, `leanspec/`: the only
   occurrences were this file, the `leanspec` stub — already re-signed — and the chapter roll-up's
   status comment).
2. **`rate_close` gained `hmc : m < c`** — the rate regime. `hc : 1 ≤ c` is now implied by
   `hm + hmc` and is kept for signature stability.

The signature below is byte-compatible with `leanspec/Leanspec/ChapH.lean`'s re-signed stub.

## The two defects the A-H.2 signature repairs

**(α-0) — the window-`0` value `u D 0` was unconstrained, and the α-leg read it.** Machine-checked
below. The unwindowed sum hits `u D 0` at `N = m*(k+1)`, and `hu0` bounds that only from below;
since the conclusion is `∃ K, ∀ D`, a family whose window-`0` value is unbounded in `D` satisfies
every field and kills every `K`. Witness `uWindowZero D N := D · (2^N)⁻¹` at `Q = 2, m = c = 1`.
Under the restored window condition the summand's window `N − m*(k+1)` is `≥ 1` at every admissible
`k`, so the induction hypothesis exists where the proof uses it; at `N = 1` the α-range is EMPTY
(`alphaRange_window_one` below, from H.22(ii)) and the base case invokes no IH at all.

**(α-rate) — the α-leg's budget did not pay for its descent.** Each α-summand descends `m*(k+1)`
windows but is discounted only by `Q^(−c*(k+1))`; recomposed against the IH, the `k`-th term gains
`Q^((m−c)(k+1))`, divergent for `m > c` and *still* divergent at the boundary `m = c` (the weaker
candidate hypothesis `m ≤ c` is therefore refuted too — `verification/rate_close_ah2_check.py`
PART 3, two exact families forcing `K ≥ 4.9·10^17` and `K ≥ 1.3·10^36`; two cells are `#guard`ed at
the bottom of this file). With `hmc : m < c` the recomposed slope `γ := c − m` satisfies `1 ≤ γ`
and H.30's geometric bound fires at `γ`.

## The proof, as landed (blueprint PROOF steps 1–6)

`K := 1 + K'`, `B := m + B' + 1`, `ĉ := c' + 1`; strong induction on the window `N`.

* step 1 — `pow_sub_dominance_one_term`: `(N − m)^B + N^(B−1) ≤ N^B` for `1 ≤ m, 1 ≤ N, 1 ≤ B`.
  This is the **one-term sharpening** the blueprint records as H.35-adjacent: H.35's own
  `pow_sub_dominance` (`(N−m)^B + m*(N−m)^(B−1) ≤ N^B`) does not close step 6 near `N = m` with an
  `N`-free `K`, so the sharpening is proved here rather than cited.
* step 2 — the induction; the base `N = 1` is not special-cased, because the windowed α-range is
  automatically empty there (`alphaRange_window_one`, H.22(ii)).
* step 3 — head leg: `ĉ ≥ 1` gives `(Q^(N−1))⁻¹ ≤ (Q^(N−ĉ))⁻¹`.
* step 4 — α leg: the (LOCUS)/(GEOM) pair, abstracted as `locus_geom`. (LOCUS) is the IH times the
  nonnegative coefficient; (GEOM) is the exponent recomposition
  `γ*(k+1) + (N − ĉ) ≤ c*(k+1) + ((N − m*(k+1)) − ĉ)`, which holds because
  `c*(k+1) = γ*(k+1) + m*(k+1)` exactly (this is `hmc`). H.30 at `c := γ` then bounds the geometric
  factor by `1`. The tie to H.16/H.17 at the intended instantiation `c = m(m+1)/2` is recorded as
  two `example`s below (`γ = clusterC m`, and H.17's `k*clusterC m + m*W = alphaExp m W k` is this
  recomposition on the exponents).
* step 5 — β leg: `ĉ = c' + 1` makes `(Q^(N−c'−1))⁻¹ = (Q^(N−ĉ))⁻¹` exactly (ℕ-subtraction
  associativity).
* step 6 — the sum, closed by step 1 and `N^(m+B') ≥ 1`.

## Numeric leg

`verification/rate_close_ah2_check.py` (exact rationals, ALL CHECKS PASSED): 32 instantiation cells
× 90 windows for the MAXIMAL family solving the three legs with equality, with base-case ratio
exactly `1`; the two witness-exclusion checks; the two `c = m` divergences. Three of its cells are
mirrored in Lean at the bottom of this file (`ah2_base_tightness`, the (α-0) exclusion `example`,
and two `#guard`s for the `c = m` divergence).

DEPENDS: H.65 (`RateSpecies`) · H.22 (clause (ii), the empty α-range at `N = 1`) · H.30
(`alpha_geom_partial_le_one`, fired at `γ = c − m`) · H.16, H.17 (the intended-instantiation tie) ·
H.35 (the citable dominance node; the one-term sharpening is proved locally, see step 1) · H.66,
H.69, H.70 (interface/inputs at blueprint level).

SOURCE: `EFF.GENIND.153` (`ANNEX-THEOREM GENIND.C′`) with its `[ar1, MINOR-1]` `c`-choice rider
(*"`c := c′ + 1` … with `c = c′ + 1` the β-leg's `Q^{−(N−c′−1)} = Q^{−(N−c)}` EXACTLY"*).

TEETH: **PROOF-ONLY** (`EFF.GENIND.153`: *"the induction itself is unguarded — no battery row
exercises a lexicographic induction"*). The ground anchor is H.28; this file's own teeth are the
`RecursionLegsPreAH2` witness (which refutes the pre-A-H.2 statement) and the numeric mirrors.

⚠ SCOPE (unchanged): the SIMPLE SLICE only, and unconditional there. The CS-drain half is H.72's.

## Status

Sorry-free, axiom-free (Lean core only). **Node H.71 complete at the A-H.2 signature.**
-/

set_option linter.style.longLine false
-- `hdesc`'s `D` binder is unused BY DESIGN: A-H.1/D7 annotates it (`(D N k : ℕ)`) precisely
-- because the committed field left `D`'s type uninferable, and the signature is frozen, so the
-- binder stays and the unused-variable linter goes off for the file.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- The three-leg recursion hypothesis of `GENIND.C′`, packaged so the induction can be stated.

**Repair record [A-H.1/D6].** The committed SIGNATURE wrote `head alpha beta : ℕ → ℕ → ℝ` and
`B' c' n₀ : ℕ`. Lean 4 structure fields do not admit multiple names — `f a b : T` declares ONE
field `f : (a : _) → (b : _) → T` — so as committed the structure had no `alpha`, `beta`, `c'` or
`n₀` at all and every hypothesis field failed to elaborate. Split one name per field below.

**Repair record [A-H.1/D7].** `hdesc`'s binders are annotated (`D` occurs nowhere else in the
field, so its type was uninferable) and the `1 ≤ N` guard is restored, matching its three sibling
fields. Without the guard the field is FALSE at `N = 0, k = 0` whenever `1 ≤ m ∧ 1 ≤ n₀`
(`0 - m·1 < 0` in `ℕ`), so the structure was uninhabited and the α-leg silently switched off.

**Repair record [A-H.2/α-0].** `halpha` carries the WINDOW CONDITION `m * (k + 1) < N`
(`EFF.GENIND.09`'s `mμ ≤ N−1`, subtraction-free under this field's own `1 ≤ N` guard). The
unwindowed form read the unconstrained `u D 0` and made `rate_close` FALSE — machine-refuted in
this file (see `RecursionLegsPreAH2` and `legsWindowZero` below). -/
structure RecursionLegs (Q m c : ℕ) (u : ℕ → ℕ → ℝ) where
  /-- The head (no-drain) leg. -/
  head : ℕ → ℕ → ℝ
  /-- The α (drain-and-recur) leg. -/
  alpha : ℕ → ℕ → ℝ
  /-- The β (lower-degree) leg. -/
  beta : ℕ → ℕ → ℝ
  /-- The β-leg's coefficient, from H.69 at strictly lower degree. -/
  K' : ℝ
  /-- The β-leg's polynomial degree, from H.69. -/
  B' : ℕ
  /-- The β-leg's exponent offset, from H.69. -/
  c' : ℕ
  /-- The α-leg's multiplicity range. -/
  n₀ : ℕ
  hK' : 0 ≤ K'
  hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N
  hu0 : ∀ D N, 0 ≤ u D N
  hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹
  halpha : ∀ D N, 1 ≤ N → alpha D N ≤
    ∑ k ∈ Finset.range n₀ with m * (k + 1) < N,
      ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
  hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹
  hdesc : ∀ (D N k : ℕ), 1 ≤ N → k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N

/-! ### Step 2's base case: the α-range is empty at window `1` (H.22(ii)) -/

/-- **The base case's α-range, from H.22(ii).** At window `N = 1` the windowed α-range is empty:
`m * (k + 1) < 1` is impossible for `1 ≤ m`. This is exactly H.22's third clause
(`¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0` — no α-event exists at `N = 1`), transcribed onto the filter the
A-H.2 `halpha` carries. Consequently the induction's base case invokes no induction hypothesis. -/
theorem alphaRange_window_one (m n₀ : ℕ) (hm : 1 ≤ m) :
    {k ∈ Finset.range n₀ | m * (k + 1) < 1} = (∅ : Finset ℕ) := by
  have hno := (window_one_exponents 1 m hm).2.2
  refine Finset.eq_empty_of_forall_notMem ?_
  intro k hk
  rw [Finset.mem_filter] at hk
  exact hno ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), by omega⟩

/-! ### Step 1: the `K`-choice (the one-term dominance sharpening) -/

/-- **PROOF step 1, the dominance sharpening (H.35-adjacent).** For `1 ≤ m`, `1 ≤ N`, `1 ≤ B`:
`(N − m)^B + N^(B−1) ≤ N^B`, subtraction-free in the sense that both `ℕ`-subtractions are
truncations of quantities the statement never needs to be positive.

Near `N = m` this is strictly stronger than H.35's `pow_sub_dominance`
(`(N−m)^B + m*(N−m)^(B−1) ≤ N^B`), whose second summand collapses to `0` there; step 6 needs the
`N^(B−1)` form to absorb the β-leg with an `N`-free `K`. The blueprint records exactly this
("the display above is the one-term sharpening its own proof route yields"). -/
theorem pow_sub_dominance_one_term {N m B : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (hB : 1 ≤ B) :
    (N - m) ^ B + N ^ (B - 1) ≤ N ^ B := by
  obtain ⟨E, rfl⟩ : ∃ E, B = E + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  by_cases h : N ≤ m
  · have h0 : N - m = 0 := by omega
    rw [h0]
    simpa using Nat.pow_le_pow_right hN (Nat.le_succ E)
  · have h1 : (N - m) ^ E ≤ N ^ E := Nat.pow_le_pow_left (by omega) E
    calc (N - m) ^ (E + 1) + N ^ E
        = (N - m) * (N - m) ^ E + N ^ E := by ring
      _ ≤ (N - m) * N ^ E + N ^ E := Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _
      _ = (N - m + 1) * N ^ E := by ring
      _ ≤ N * N ^ E := Nat.mul_le_mul_right _ (by omega)
      _ = N ^ (E + 1) := by ring

/-! ### Step 4: the (LOCUS)/(GEOM) transport, abstracted -/

/-- **PROOF step 4, the (LOCUS)/(GEOM) pair.** The α-summand's transport, with the two exponent
forms carried as one hypothesis `hexp : a + f ≤ e + g`:

* `e = c*(k+1)`, `g = W_k − ĉ` — the LOCUS form, which is what the IH hands over;
* `a = γ*(k+1)`, `f = N − ĉ` — the GEOM form, which is what H.30's geometric sum consumes.

`x ≤ y` carries the polynomial factor (`W_k^B ≤ (N−m)^B`), and `C` is the nonnegative coefficient
`(Q − 1)`. The whole content is that `(Q^e)⁻¹ (Q^g)⁻¹ = (Q^(e+g))⁻¹ ≤ (Q^(a+f))⁻¹`. -/
theorem locus_geom {Q : ℕ} (hQ : 2 ≤ Q) {e g a f : ℕ} (hexp : a + f ≤ e + g)
    {C x y : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hxy : x ≤ y) :
    C * ((Q : ℝ) ^ e)⁻¹ * (x * ((Q : ℝ) ^ g)⁻¹)
      ≤ C * ((Q : ℝ) ^ a)⁻¹ * (y * ((Q : ℝ) ^ f)⁻¹) := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
  have h1 : C * ((Q : ℝ) ^ e)⁻¹ * (x * ((Q : ℝ) ^ g)⁻¹) = (C * x) * ((Q : ℝ) ^ (e + g))⁻¹ := by
    rw [pow_add, mul_inv]; ring
  have h2 : C * ((Q : ℝ) ^ a)⁻¹ * (y * ((Q : ℝ) ^ f)⁻¹) = (C * y) * ((Q : ℝ) ^ (a + f))⁻¹ := by
    rw [pow_add, mul_inv]; ring
  rw [h1, h2]
  have hinv : ((Q : ℝ) ^ (e + g))⁻¹ ≤ ((Q : ℝ) ^ (a + f))⁻¹ :=
    inv_anti₀ (pow_pos hQ0 _) (pow_le_pow_right₀ hQ1 hexp)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hxy hC) hinv (by positivity)
    (mul_nonneg hC (hx.trans hxy))

/-! ### The closure theorem -/

/-- **NODE H.71, `GENIND.C′` (`rate_close`), at the A-H.2 signature.** From the three legs of the
`S5.2` recursion — head `≤ Q^(−(N−1))`, the WINDOWED α-sum, and β `≤ K'·N^(m+B')·Q^(−(N−c'−1))` —
the normalized complement family `u` has H.65's rate species with `K = 1 + K'`,
`B = m + B' + 1`, `c = c' + 1`, uniformly in the degree index `D`.

`hmc : m < c` is the rate regime (A-H.2/α-rate): the recomposed slope `γ := c − m` must be `≥ 1`
for H.30's geometric sum to be bounded by `1`. Without it the statement is FALSE, and it is FALSE
already at the boundary `c = m`. `hc : 1 ≤ c` is implied by `hm + hmc`; it is kept for signature
stability. -/
theorem rate_close {Q m c : ℕ} (hQ : 2 ≤ Q) (hc : 1 ≤ c) (hm : 1 ≤ m) (hmc : m < c)
    {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D) := by
  have hK'0 : (0 : ℝ) ≤ L.K' := L.hK'
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
  have hQm1 : (0 : ℝ) ≤ (Q : ℝ) - 1 := by linarith
  have hKr0 : (0 : ℝ) ≤ 1 + L.K' := by linarith
  refine ⟨1 + L.K', hKr0, ?_⟩
  intro D N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    -- `P` is the common exponential factor `(Q ^ (N ∸ ĉ))⁻¹`, `ĉ = c' + 1`.
    have hP0 : (0 : ℝ) < ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by positivity
    -- ------------------------------------------------------------------ step 3: the head leg
    have hheadb : L.head D N ≤ 1 * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by
      refine (L.hhead D N hN).trans ?_
      rw [one_mul]
      exact inv_anti₀ (pow_pos hQ0 _) (pow_le_pow_right₀ hQ1 (by omega))
    -- ------------------------------------------------------------------ step 5: the β leg
    have hbetab : L.beta D N
        ≤ L.K' * (N : ℝ) ^ (m + L.B') * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by
      have h := L.hbeta D N hN
      have he : N - L.c' - 1 = N - (L.c' + 1) := by omega
      rwa [he] at h
    -- ------------------------------------------------------------------ step 4: the α leg
    have hterm : ∀ k ∈ {k ∈ Finset.range L.n₀ | m * (k + 1) < N},
        ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
          ≤ ((Q : ℝ) - 1) * ((Q : ℝ) ^ ((c - m) * (k + 1)))⁻¹
            * ((1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
              * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkn, hkw⟩ := hk
      -- the admissibility floor: `1 ≤ N − m*(k+1) < N`
      have hs1 : 1 ≤ m * (k + 1) := Nat.mul_pos hm (Nat.succ_pos k)
      have hW1 : 1 ≤ N - m * (k + 1) := by omega
      have hWN : N - m * (k + 1) < N := L.hdesc D N k hN hkn hs1
      -- (LOCUS): the IH times the nonnegative coefficient
      have hIH := ih (N - m * (k + 1)) hWN hW1
      have hcoef0 : (0 : ℝ) ≤ ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ :=
        mul_nonneg hQm1 (by positivity)
      refine le_trans (mul_le_mul_of_nonneg_left hIH hcoef0) ?_
      -- (GEOM): the exponent recomposition, exact because `hmc` makes `c = (c − m) + m`
      have hct : (c - m) * (k + 1) + m * (k + 1) = c * (k + 1) := by
        rw [← Nat.add_mul]
        congr 1
        omega
      have hexp : (c - m) * (k + 1) + (N - (L.c' + 1))
          ≤ c * (k + 1) + ((N - m * (k + 1)) - (L.c' + 1)) := by omega
      -- the polynomial factor: `W_k ≤ N − m` because `m ≤ m*(k+1)`
      have hmle : m ≤ m * (k + 1) := Nat.le_mul_of_pos_right m (Nat.succ_pos k)
      have hWm : ((N - m * (k + 1) : ℕ) : ℝ) ^ (m + L.B' + 1)
          ≤ ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1) := by
        have hnat : (N - m * (k + 1)) ^ (m + L.B' + 1) ≤ (N - m) ^ (m + L.B' + 1) :=
          Nat.pow_le_pow_left (by omega) _
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        simpa only [Nat.cast_pow] using this
      exact locus_geom hQ hexp hQm1
        (mul_nonneg hKr0 (by positivity))
        (mul_le_mul_of_nonneg_left hWm hKr0)
    have halphab : L.alpha D N
        ≤ (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
          * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by
      refine (L.halpha D N hN).trans ?_
      have hbig0 : (0 : ℝ) ≤ (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
          * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ :=
        mul_nonneg (mul_nonneg hKr0 (by positivity)) (by positivity)
      have hcoefγ : ∀ k : ℕ, (0 : ℝ) ≤ ((Q : ℝ) - 1) * ((Q : ℝ) ^ ((c - m) * (k + 1)))⁻¹ :=
        fun k => mul_nonneg hQm1 (by positivity)
      calc ∑ k ∈ Finset.range L.n₀ with m * (k + 1) < N,
              ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
          ≤ ∑ k ∈ Finset.range L.n₀ with m * (k + 1) < N,
              ((Q : ℝ) - 1) * ((Q : ℝ) ^ ((c - m) * (k + 1)))⁻¹
                * ((1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
                  * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹) := Finset.sum_le_sum hterm
        _ ≤ ∑ k ∈ Finset.range L.n₀,
              ((Q : ℝ) - 1) * ((Q : ℝ) ^ ((c - m) * (k + 1)))⁻¹
                * ((1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
                  * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => mul_nonneg (hcoefγ i) hbig0)
        _ = (∑ k ∈ Finset.range L.n₀, ((Q : ℝ) - 1) * ((Q : ℝ) ^ ((c - m) * (k + 1)))⁻¹)
              * ((1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
                * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * ((1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
                * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹) :=
            mul_le_mul_of_nonneg_right
              (alpha_geom_partial_le_one Q (c - m) hQ (by omega) L.n₀) hbig0
        _ = (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
              * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := one_mul _
    -- ------------------------------------------------------------------ steps 1 + 6: the sum
    have hdom : ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1) + (N : ℝ) ^ (m + L.B')
        ≤ (N : ℝ) ^ (m + L.B' + 1) := by
      have hnat : (N - m) ^ (m + L.B' + 1) + N ^ (m + L.B' + 1 - 1) ≤ N ^ (m + L.B' + 1) :=
        pow_sub_dominance_one_term hm hN (by omega)
      have hBn1 : m + L.B' + 1 - 1 = m + L.B' := by omega
      rw [hBn1] at hnat
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      simpa only [Nat.cast_add, Nat.cast_pow] using this
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (m + L.B') := by
      have h : (1 : ℕ) ≤ N ^ (m + L.B') := Nat.one_le_pow _ _ hN
      exact_mod_cast h
    have hscalar : 1 + (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
          + L.K' * (N : ℝ) ^ (m + L.B')
        ≤ (1 + L.K') * (N : ℝ) ^ (m + L.B' + 1) := by
      have h1 : (1 + L.K') * (((N - m : ℕ) : ℝ) ^ (m + L.B' + 1) + (N : ℝ) ^ (m + L.B'))
          ≤ (1 + L.K') * (N : ℝ) ^ (m + L.B' + 1) := mul_le_mul_of_nonneg_left hdom hKr0
      nlinarith [h1, hN1, hK'0]
    calc u D N ≤ L.head D N + L.alpha D N + L.beta D N := L.hsplit D N hN
      _ ≤ 1 * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹
            + (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1)
              * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹
            + L.K' * (N : ℝ) ^ (m + L.B') * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ :=
          add_le_add (add_le_add hheadb halphab) hbetab
      _ = (1 + (1 + L.K') * ((N - m : ℕ) : ℝ) ^ (m + L.B' + 1) + L.K' * (N : ℝ) ^ (m + L.B'))
            * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by ring
      _ ≤ ((1 + L.K') * (N : ℝ) ^ (m + L.B' + 1)) * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ :=
          mul_le_mul_of_nonneg_right hscalar hP0.le
      _ = (1 + L.K') * (N : ℝ) ^ (m + L.B' + 1) * ((Q : ℝ) ^ (N - (L.c' + 1)))⁻¹ := by ring

end Uniformity.Density.Induction

/-! ## Non-vacuity: the repaired structure is INHABITED in the `hmc` regime, and `rate_close` fires

`sorry`-free ≠ non-vacuous. A-H.1/D7 was precisely an inhabitation defect (the pre-repair `hdesc`
emptied the type), so the repaired structure owes a witness *inside* `rate_close`'s hypotheses —
i.e. at some `2 ≤ Q`, `1 ≤ m`, `m < c`. The head-only family below is that witness at
`(Q, m, c) = (2, 2, 3)`, the intended instantiation's smallest cell (`c = m(m+1)/2 = 3`,
recomposed slope `γ = clusterC 2 = 1`, the tight one). The head leg holds with EQUALITY; the α and
β legs are slack at `0`. `rate_close` is then fired on it, so the theorem is not vacuously true. -/

namespace Uniformity.Density.Induction

/-- The head-only family at `Q = 2`: `u D N = (2^(N−1))⁻¹`, constant in the degree index. -/
private noncomputable def uHead : ℕ → ℕ → ℝ := fun _ N => (((2 : ℕ) : ℝ) ^ (N - 1))⁻¹

/-- **Inhabitation witness at `(Q, m, c) = (2, 2, 3)`, inside `rate_close`'s hypotheses.**
`hhead` holds with equality; `alpha = beta = 0` are slack. -/
private noncomputable def legsHeadOnly : RecursionLegs 2 2 3 uHead where
  head := uHead
  alpha := fun _ _ => 0
  beta := fun _ _ => 0
  K' := 0
  B' := 0
  c' := 0
  n₀ := 4
  hK' := le_rfl
  hsplit := by intro D N _; simp
  hu0 := by intro D N; unfold uHead; positivity
  hhead := by intro D N _; exact le_rfl
  halpha := by
    intro D N _
    refine Finset.sum_nonneg ?_
    intro k _
    have : (0 : ℝ) ≤ uHead D (N - 2 * (k + 1)) := by unfold uHead; positivity
    have hq : (0 : ℝ) ≤ (((2 : ℕ) : ℝ) - 1) * ((((2 : ℕ) : ℝ)) ^ (3 * (k + 1)))⁻¹ := by
      norm_num
    exact mul_nonneg hq this
  hbeta := by intro D N _; simp
  hdesc := by intro D N k hN hk _; omega

/-- **`rate_close` fires on the witness** — the theorem is non-vacuous at `(Q, m, c) = (2, 2, 3)`,
with the conclusion `∀ D, RateSpecies 2 K 3 1 (uHead D)` for `K = 1 + K' = 1`. -/
private theorem legsHeadOnly_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D,
      RateSpecies 2 K (2 + legsHeadOnly.B' + 1) (legsHeadOnly.c' + 1) (uHead D) :=
  rate_close (Q := 2) (m := 2) (c := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    legsHeadOnly

end Uniformity.Density.Induction

/-! ## Step 4's tie to H.16/H.17 at the intended instantiation

The abstract (GEOM) step is `(c − m)*(k+1) + m*(k+1) = c*(k+1)` — the recomposition of the LOCUS
exponent into the GEOM slope `γ := c − m` plus the descent `m*(k+1)`. At the intended
instantiation the structure's `c` is the NORMALIZED α-locus slope `m(m+1)/2` (A-H.2's adjudication;
`clusterC m = m(m−1)/2` is the RECOMPOSED slope, not this one), and then `γ = clusterC m` and the
recomposition IS H.17's transport identity. Both facts are recorded here as `example`s so the tie
is machine-checked without adding declarations to the node's contract. -/

section IntendedInstantiation

open Uniformity.Density.Induction

/-- `γ = c − m = clusterC m` at `c = m(m+1)/2`, stated division- and subtraction-free:
`2*clusterC m + 2*m = m*(m+1)`, i.e. `clusterC m + m = m(m+1)/2`. Uses H.14(ii). -/
example (m : ℕ) : 2 * clusterC m + 2 * m = m * (m + 1) := by
  have h := two_mul_clusterC m
  cases m with
  | zero => simp [clusterC]
  | succ n =>
    rw [h]
    simp only [Nat.add_sub_cancel]
    ring

/-- (GEOM) at the intended instantiation is H.17's transport identity
`k * clusterC m + m * W = alphaExp m W k`. -/
example (m W k : ℕ) : k * clusterC m + m * W = alphaExp m W k :=
  ghost_add_child_eq_alphaExp m W k

/-- H.16(ii)'s closed-form reconciliation — the corpus's *other* exponent form
(`m(N−1) − k·m(m+1)/2`), subtraction-free. This is the second of the "two exponent forms" the
blueprint's step-4 flag names. -/
example (m W k : ℕ) : 2 * alphaExp m W k + k * (m * (m + 1)) = 2 * (m * (W + m * k)) :=
  two_mul_alphaExp_add m W k

end IntendedInstantiation

/-! ## The refutation of the PRE-A-H.2 statement, machine-checked

Preserved from the fleet's landing (the `G.23a` / A-H.1-D4/D8 precedent). `RecursionLegsPreAH2` is
a **local restatement** of the pre-A-H.2 structure — identical to `RecursionLegs` except that
`halpha` sums over ALL `k < n₀` with no window condition. It exists only to carry the refutation;
nothing downstream may consume it, and the refuted `rate_close` appears only as a HYPOTHESIS of an
`example : False`, never as an environment fact.

`uWindowZero D N := D · (2^N)⁻¹` is a legitimate three-leg family at `Q = 2`, `m = c = 1` for the
pre-A-H.2 fields: the head and β legs are identically `0`, and the α leg IS the family, because
`u D N = ½ · u D (N−1)` is exactly the single unwindowed α-summand at `Q = 2, c = 1, n₀ = 1`. Its
window-`0` value `u D 0 = D` is unbounded across `D`, which is what no pre-A-H.2 field forbids and
what the conclusion cannot survive. -/

namespace Uniformity.Density.Induction

/-- The PRE-A-H.2 three-leg structure (unwindowed `halpha`), restated locally so its refutation can
be kept as a machine-checked record. **Not** the node's contract; see `RecursionLegs`. -/
private structure RecursionLegsPreAH2 (Q m c : ℕ) (u : ℕ → ℕ → ℝ) where
  head : ℕ → ℕ → ℝ
  alpha : ℕ → ℕ → ℝ
  beta : ℕ → ℕ → ℝ
  K' : ℝ
  B' : ℕ
  c' : ℕ
  n₀ : ℕ
  hK' : 0 ≤ K'
  hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N
  hu0 : ∀ D N, 0 ≤ u D N
  hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹
  -- the defect: no `with m * (k + 1) < N` filter, so the summand reads `u D 0` at `N = m*(k+1)`
  halpha : ∀ D N, 1 ≤ N → alpha D N ≤
    ∑ k ∈ Finset.range n₀, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
  hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹
  hdesc : ∀ (D N k : ℕ), 1 ≤ N → k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N

/-- The (α-0) counterexample family: `u D N = D · (2^N)⁻¹`. Not part of the node's contract. -/
private noncomputable def uWindowZero : ℕ → ℕ → ℝ := fun D N => (D : ℝ) * ((2 : ℝ) ^ N)⁻¹

/-- Every summand of the pre-A-H.2 α-leg at `Q = 2, m = c = 1, n₀ = 1`, evaluated: for `N ≥ 1` the
sum is `½ · u D (N−1) = u D N`, so the unwindowed `halpha` holds with equality. -/
private theorem uWindowZero_alpha (D N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range 1,
        (((2 : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) ^ (1 * (k + 1)))⁻¹ * uWindowZero D (N - 1 * (k + 1))
      = uWindowZero D N := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  simp only [Finset.sum_range_one, uWindowZero, Nat.cast_ofNat]
  norm_num [pow_succ]
  ring

/-- **The witness.** `RecursionLegsPreAH2 2 1 1 uWindowZero` — every one of the fourteen pre-A-H.2
fields holds, `hsplit` and `halpha` with equality. -/
private noncomputable def legsWindowZero : RecursionLegsPreAH2 2 1 1 uWindowZero where
  head := fun _ _ => 0
  alpha := uWindowZero
  beta := fun _ _ => 0
  K' := 0
  B' := 0
  c' := 0
  n₀ := 1
  hK' := le_rfl
  hsplit := by intro D N _; simp
  hu0 := by intro D N; unfold uWindowZero; positivity
  hhead := by intro D N _; positivity
  halpha := by intro D N hN; exact (uWindowZero_alpha D N hN).ge
  hbeta := by intro D N _; simp
  hdesc := by intro D N k hN hk _; omega

/-- **DEFECT (α-0), machine-checked.** Had H.71's `rate_close` been landed at its PRE-A-H.2 type,
it would prove `False`: the hypothesis below is that statement verbatim (over the pre-A-H.2
structure), and `legsWindowZero` instantiates it at `Q = 2, m = 1, c = 1`, where its conclusion at
window `M = 1` demands `D/2 ≤ K` for every `D`.

This is an `example` taking the refuted theorem as a hypothesis rather than an `axiom`, precisely
so that nothing false enters the environment (the `G.23a` / D4 / D8 precedent). -/
private example
    (rate_close_preAH2 : ∀ {Q m c : ℕ}, 2 ≤ Q → 1 ≤ c → 1 ≤ m → ∀ {u : ℕ → ℕ → ℝ}
      (L : RecursionLegsPreAH2 Q m c u),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D)) :
    False := by
  obtain ⟨K, _, hK⟩ :=
    rate_close_preAH2 (Q := 2) (m := 1) (c := 1) (by norm_num) le_rfl le_rfl legsWindowZero
  -- Pick a degree index whose window-`0` mass exceeds anything `K` can pay for.
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * K)
  have h1 : uWindowZero D 1 ≤ K * ((1 : ℕ) : ℝ) ^ (1 + legsWindowZero.B' + 1)
      * ((((2 : ℕ)) : ℝ) ^ (1 - (legsWindowZero.c' + 1)))⁻¹ := hK D 1 le_rfl
  simp only [legsWindowZero, uWindowZero] at h1
  norm_num at h1
  linarith

/-- **The A-H.2 repair excludes the (α-0) witness** (mirror of
`verification/rate_close_ah2_check.py` PART 2). The same family fails the *windowed* `halpha`
already at `N = 1`: the α-range is empty there, so the bound reads `alpha D 1 ≤ 0`, while
`alpha 1 1 = uWindowZero 1 1 = 1/2`. (It also fails `hmc`, which at `m = c = 1` reads `1 < 1`.) -/
private example :
    ¬ (uWindowZero 1 1 ≤ ∑ k ∈ Finset.range 1 with 1 * (k + 1) < 1,
        (((2 : ℕ) : ℝ) - 1) * (((2 : ℕ) : ℝ) ^ (1 * (k + 1)))⁻¹
          * uWindowZero 1 (1 - 1 * (k + 1))) := by
  rw [alphaRange_window_one 1 1 le_rfl]
  simp [uWindowZero]

end Uniformity.Density.Induction

/-! ## Numeric mirrors of `verification/rate_close_ah2_check.py`

Three cheap cells. The exclusion mirror (PART 2) is the `example` just above; the base-case
tightness (PART 1) and the `c = m` divergence (PART 3) are here. -/

namespace Uniformity.Density.Induction

/-- **PART 1's base-case tightness, exactly.** At window `N = 1` the maximal family has
`u(1) = head(1) + 0 + β(1) = 1 + K'` and the bound is `(1 + K')·1^B·(Q^(1 ∸ (c'+1)))⁻¹`. Both
`ℕ`-truncated exponents are `0`, so the ratio is EXACTLY `1` — the `K`-choice `K := 1 + K'` is
sharp at the base, which is what the numeric leg reports (`max u/bound = 1.0000`). -/
theorem ah2_base_tightness (K' : ℝ) (Q B c' : ℕ) :
    (1 + K') * ((1 : ℕ) : ℝ) ^ B * ((Q : ℝ) ^ (1 - (c' + 1)))⁻¹ = 1 + K' := by
  have h : 1 - (c' + 1) = 0 := by omega
  rw [h]
  simp

end Uniformity.Density.Induction

/-! ## PART 3's `c = m` divergence, and the pre-A-H.2 (α-rate) divergence, as `#guard`s

These are **illustrations, not refutations** — a `#guard` cannot refute an `∃ K`. Each says that a
single `K` would have to exceed a stated bound at a stated window, in integer form.

Rows 1–2 (pre-A-H.2, `m > c`): `Q = 2, c = 1, m = 2, n₀ = 4`, `u D N = (9/10)^N`; the conclusion
`u D M ≤ K·M^3·(2^(M−1))⁻¹` rearranges to `9^M·2^(M−1) ≤ K·M^3·10^M`, forcing `K > 10^19` at
`M = 100` and `K > 10^43` at `M = 200` (the divergence `K ≥ 1.8^M/(2M³) → ∞`).

Rows 3–4 (A-H.2's own sharpness finding, `c = m` — the boundary the rejected candidate `m ≤ c`
would admit, `verification/rate_close_ah2_check.py` PART 3): `(Q,m,c,n₀) = (3,1,1,2)` with
`u = (9/10)^N` forces `K > 10^17` at `M = 50`, and `(3,2,2,2)` with `u = (11/20)^N` forces
`K > 10^36` at `M = 200`. Both families satisfy every repaired field except `hmc`, so the two
A-H.2 defects are genuinely independent and each repair is separately load-bearing. -/

section RateDivergence

#guard 9 ^ 100 * 2 ^ 99 > 10 ^ 19 * (100 ^ 3 * 10 ^ 100)
#guard 9 ^ 200 * 2 ^ 199 > 10 ^ 43 * (200 ^ 3 * 10 ^ 200)

#guard 9 ^ 50 * 3 ^ 49 > 10 ^ 17 * (50 ^ 2 * 10 ^ 50)
#guard 11 ^ 200 * 3 ^ 199 > 10 ^ 36 * (200 ^ 3 * 20 ^ 200)

end RateDivergence

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.RecursionLegs
#print axioms Uniformity.Density.Induction.RecursionLegs.mk
#print axioms Uniformity.Density.Induction.alphaRange_window_one
#print axioms Uniformity.Density.Induction.pow_sub_dominance_one_term
#print axioms Uniformity.Density.Induction.locus_geom
#print axioms Uniformity.Density.Induction.rate_close
#print axioms Uniformity.Density.Induction.ah2_base_tightness

end AxCheck
