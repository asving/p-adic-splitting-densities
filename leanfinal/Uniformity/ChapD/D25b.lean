/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D24

/-!
# Uniformity.ChapD.D25b — `(C6-lift)` clauses 3–4: the x-support pin and `(C6-x-free)`

**Chapter D, NODE D.25**, second half (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1 gauge
layer; **SPLIT MANDATED → 2**, this file being `D25b` = clauses 3–4, with
`Uniformity.ChapD.D25a` = clauses 1–2 plus the zero branch). Amendments A-1 and A-D.1 govern;
the SIGNATURE is the A-D.1/D-D4 + D-D6 re-signed one. ENV-D4 — the concrete level-1 arena over
the bundle. Two signed declarations.

Under the same hypotheses as `D25a` (`hσ`, `hσ0`, `hπ`, `he`, `hcop`, `hf`, the live-domain
`hM : e₁ * f₁ * h < M`, and `hl : l ≠ 0`):

3. **x-support** (`liftC6_support`, the A6/GENTOW6 support pin `EFF.T1.30`):
   `(liftC6 …).support = {i(M) + e₁·r : r < f₁, λ_r ≠ 0}`;
4. **the x-free criterion `(C6-x-free)`** (`liftC6_xfree`): `liftC6 …` is a monomial in `π`
   alone — `natDegree = 0` with the single support point `0` — **iff** `iexp e₁ h M = 0` and
   `λ_r = 0` for every `r ≠ 0`.

Both are the corpus's "distinct nonnegative `x` exponents" argument (`EFF.T1.20` step 4): the
`f₁` slots `i(M) + e₁r` are pairwise distinct because `0 < e₁`, so the support is the image of
the nonzero-coordinate set, no cancellation is possible, and the single-slot-at-`0` condition
splits into `i(M) = 0` and `r = 0`.

## DEFECT D-D6 (A-D.1), and the form chosen IN WRITING

Clause 3's `Finset.filter (fun r => l r ≠ 0)` has **no `DecidablePred`** over an abstract
residue field, so the statement as displayed does not elaborate. The blueprint offers two
admissible landed forms and requires the fleet to pick one in writing. **This file takes form
(a)**: `liftC6_support` is declared inside `section ClassicalSupport / open scoped Classical`,
which is what the stage-0e gate did (note SD-5) and what the blueprint signs as the default; it
keeps the `EFF.T1.30` display shape byte-for-byte. Form (b) — the membership restatement
`∀ j, j ∈ support ↔ ∃ r, l r ≠ 0 ∧ j = i(M) + e₁r` — is NOT used. Consumers of
`liftC6_support` inherit the classical `DecidablePred` instance baked into its statement; the
`ext`/`Finset.mem_image` reading used inside `liftC6_xfree` below is instance-agnostic and
shows the pattern.

Clause 4 is deliberately OUTSIDE the classical section (the blueprint's `end ClassicalSupport`
sits before it): its statement mentions no `filter`. Its proof opens `classical` locally in
order to consume clause 3.

## Why the private helpers are re-derived here

The slotwise coefficient reads (`coeff_liftC6`, `coeff_liftC6_at`, `exists_of_coeff_ne_zero`)
are `private` in `D25a` and therefore not importable; the split of one blueprint node into two
files forces one honest duplication rather than a new public name (which would breach GC-6.5
and the "a reusable helper triggers RE-PLAN, never a silent second public name" rule). They are
byte-identical to `D25a`'s. This file consequently imports **D.24 only** — it needs no chapter
B object, since clauses 3–4 speak about `support`/`natDegree`, not about `suppVal`.

## Faithfulness

* *clause 4 is an `↔`, and the corpus's criterion is exact.* The forward direction consumes
  only `support = {0}`; `natDegree = 0` is redundant there and is kept because the signature is
  frozen. The backward direction produces both conjuncts.
* *`hM`, `hcop`, `hf` are not consumed by either clause*, and `hπ` is consumed only through
  `π ≠ 0`. They are signed hypotheses of frozen statements and are KEPT (no weakening); the
  unused-variable linter is switched off per declaration, on the B.15 precedent.
* *the `r ≠ 0` in clause 4 is spelled `(r : ℕ) ≠ 0`*, as signed — deliberately, since
  `(0 : Fin f₁)` needs a `NeZero f₁` instance that the statement does not carry.

DEPENDS: D.13 (`iexp`, `aexp`) · D.24 (`liftC6`) · mathlib `Polynomial.finsetSum_coeff`,
`Polynomial.coeff_C_mul_X_pow`, `Polynomial.mem_support_iff`,
`Polynomial.natDegree_le_iff_coeff_eq_zero`, `Finset.eq_singleton_iff_unique_mem`,
`Finset.mem_image`, `Nat.eq_of_mul_eq_mul_left` — all name-verified at the v4.31.0 pin.

**PROOF.** Clause 3: `ext j` on `mem_support_iff`; `→` is `exists_of_coeff_ne_zero`, `←`
evaluates the slot by `coeff_liftC6_at` and uses that `σ(λ_r) ≠ 0` (its residue is `λ_r ≠ 0`)
together with `π ≠ 0` in a domain. Clause 4: rewrite the support by clause 3. `→` — the slot of
any nonzero coordinate lands in `{0}`, forcing `i(M) + e₁r = 0`, hence `i(M) = 0`, and then any
`r` with `(r : ℕ) ≠ 0` cannot carry a nonzero coordinate (`0 < e₁`). `←` — every nonzero
coordinate sits at `(r : ℕ) = 0`, so the image is exactly `{0}`
(`Finset.eq_singleton_iff_unique_mem`, nonempty because `l ≠ 0`), and `natDegree = 0` follows
from `natDegree_le_iff_coeff_eq_zero`.

SOURCE: `EFF.T1.20` (clauses 3–4 of the boxed `(C6-lift)` + step 4 of the derivation);
`EFF.T1.30` (the A6 support display `Supp_x L_M(λ) = {i(M)+e₁r : λ_r ≠ 0}` and the
zero/nonzero split).

**TEETH.** T1 §4.2 checks 1, 7, 10 → **Lean theorem** (this node, with `D25a`); the A1/A6
consumption regressions → §12 (retained; PARI-side).

ENVIRONMENT: ENV-D4 (CHAP-B's ENV-A′ MINUS its `{π : O}` — per defect D-D4 every declaration
binds `π` itself, explicitly and first, exactly as D.24 does).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open IsLocalRing Polynomial IsDiscreteValuationRing

-- ENV-D4 (blueprint §0.1) = CHAP-B's ENV-A′, MINUS its `{π : O}`: per defect D-D4 the nodes of
-- this file bind `π` themselves, explicitly and first.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Slotwise read of `liftC6`. Private helper, byte-identical to `D25a`'s (the mandated split
of NODE D.25 into two files forces the duplication; a shared public helper would breach
GC-6.5). -/
private theorem coeff_liftC6 (π : O) {f₁ : ℕ} (e₁ h : ℕ) (σ : ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → ResidueField O) (j : ℕ) :
    (liftC6 π e₁ h σ M l).coeff j
      = ∑ r : Fin f₁, if j = iexp e₁ h M + e₁ * (r : ℕ)
          then σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat else 0 := by
  simp only [liftC6, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

/-- The coefficient AT a slot `i(M) + e₁r`: the sum collapses because `r ↦ i(M) + e₁r` is
injective for `0 < e₁`. Private helper, byte-identical to `D25a`'s. -/
private theorem coeff_liftC6_at (π : O) {f₁ : ℕ} (e₁ h : ℕ) (he : 0 < e₁)
    (σ : ResidueField O → O) (M : ℕ) (l : Fin f₁ → ResidueField O) (r : Fin f₁) :
    (liftC6 π e₁ h σ M l).coeff (iexp e₁ h M + e₁ * (r : ℕ))
      = σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat := by
  rw [coeff_liftC6, Finset.sum_eq_single r]
  · simp
  · intro b _ hb
    refine if_neg fun heq => hb (Fin.ext ?_)
    exact (Nat.eq_of_mul_eq_mul_left he (Nat.add_left_cancel heq)).symm
  · intro hb
    exact absurd (Finset.mem_univ r) hb

/-- A nonzero coefficient of `liftC6` sits at a slot with a nonzero coordinate. Private helper,
byte-identical to `D25a`'s. -/
private theorem exists_of_coeff_ne_zero (π : O) {f₁ : ℕ} (e₁ h : ℕ)
    (σ : ResidueField O → O) (hσ0 : σ 0 = 0) (M : ℕ) (l : Fin f₁ → ResidueField O) {j : ℕ}
    (hj : (liftC6 π e₁ h σ M l).coeff j ≠ 0) :
    ∃ r : Fin f₁, j = iexp e₁ h M + e₁ * (r : ℕ) ∧ l r ≠ 0 := by
  by_contra hcon
  refine hj ?_
  rw [coeff_liftC6]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hjr : j = iexp e₁ h M + e₁ * (r : ℕ)
  · have hlr : l r = 0 := by
      by_contra hlr
      exact hcon ⟨r, hjr, hlr⟩
    rw [if_pos hjr, hlr, hσ0, zero_mul]
  · exact if_neg hjr

/-- `l ≠ 0` as a pointwise witness. Private helper. -/
private theorem exists_nonzero_coord {f₁ : ℕ} {l : Fin f₁ → ResidueField O} (hl : l ≠ 0) :
    ∃ r : Fin f₁, l r ≠ 0 := by
  by_contra hc
  apply hl
  funext r
  simp only [Pi.zero_apply]
  by_contra hlr
  exact hc ⟨r, hlr⟩

section ClassicalSupport
open scoped Classical

-- `hf`, `hcop` and `hM` are signed hypotheses of the frozen statement and are not consumed:
-- the support formula is slotwise and needs only `0 < e₁` (injectivity of the slot map),
-- `π ≠ 0`, and the two section clauses. Kept, not removed — the B.15 precedent.
set_option linter.unusedVariables false in
/-- **D.25 clause 3 — the A6/GENTOW6 x-support pin** (`EFF.T1.30`):
`Supp_x L_M(λ) = {i(M) + e₁r : λ_r ≠ 0}`.

⚠ **D-D6, form (a) taken IN WRITING.** The `Finset.filter` predicate `fun r => l r ≠ 0` is not
decidable over an abstract residue field, so this declaration lives inside
`section ClassicalSupport / open scoped Classical` — the blueprint's signed default, keeping the
`EFF.T1.30` display shape. The membership restatement (form (b)) is not used. -/
theorem liftC6_support (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (hl : l ≠ 0) :
    (liftC6 π e₁ h σ M l).support
      = (Finset.univ.filter (fun r : Fin f₁ => l r ≠ 0)).image
          (fun r : Fin f₁ => iexp e₁ h M + e₁ * (r : ℕ)) := by
  ext j
  simp only [Polynomial.mem_support_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hj
    obtain ⟨r, hjr, hr⟩ := exists_of_coeff_ne_zero π e₁ h σ hσ0 M l hj
    exact ⟨r, hr, hjr.symm⟩
  · rintro ⟨r, hr, rfl⟩
    have hσne : σ (l r) ≠ 0 := by
      intro hz
      apply hr
      rw [← hσ (l r), hz, map_zero]
    rw [coeff_liftC6_at π e₁ h he σ M l r]
    exact mul_ne_zero hσne (pow_ne_zero _ hπ.ne_zero)

end ClassicalSupport

-- `hf`, `hcop` and `hM` are again signed-but-unconsumed; `hσ0`/`hσ`/`hπ` reach this statement
-- only through clause 3. Kept, not removed.
set_option linter.unusedVariables false in
/-- **D.25 clause 4 — `(C6-x-free)`, the x-free criterion** (`EFF.T1.20` step 4).
The lift is a monomial in `π` alone (degree `0`, single support point `0`) **iff** the reduced
x-exponent vanishes and the only surviving coordinate is the `0`-th: "distinct nonnegative `x`
exponents prove the x-free equivalence".

The single support point is `i(M) + e₁r₀` for the unique nonzero coordinate, and it is `0`
exactly when `i(M) = 0` and `r₀ = 0` (using `0 < e₁`). Stated with `(r : ℕ) ≠ 0` rather than
`r ≠ (0 : Fin f₁)`, as signed: the latter would need a `NeZero f₁` instance the statement does
not carry. -/
theorem liftC6_xfree (π : O) (e₁ h f₁ : ℕ) (hπ : Irreducible π) (he : 0 < e₁) (hf : 0 < f₁)
    (hcop : Nat.Coprime h e₁) (σ : ResidueField O → O)
    (hσ : ∀ a, IsLocalRing.residue O (σ a) = a) (hσ0 : σ 0 = 0)
    (M : ℕ) (hM : e₁ * f₁ * h < M) (l : Fin f₁ → ResidueField O) (hl : l ≠ 0) :
    ((liftC6 π e₁ h σ M l).natDegree = 0 ∧ (liftC6 π e₁ h σ M l).support = {0})
      ↔ (iexp e₁ h M = 0 ∧ ∀ r : Fin f₁, (r : ℕ) ≠ 0 → l r = 0) := by
  classical
  have hsupp := liftC6_support π e₁ h f₁ hπ he hf hcop σ hσ hσ0 M hM l hl
  obtain ⟨r₀, hr₀⟩ := exists_nonzero_coord hl
  constructor
  · rintro ⟨-, hs⟩
    rw [hsupp] at hs
    have hmem : ∀ r : Fin f₁, l r ≠ 0 → iexp e₁ h M + e₁ * (r : ℕ) = 0 := by
      intro r hr
      have hin : iexp e₁ h M + e₁ * (r : ℕ) ∈ ({0} : Finset ℕ) := by
        rw [← hs]
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ r, hr⟩)
      simpa using hin
    refine ⟨by have := hmem r₀ hr₀; omega, ?_⟩
    intro r hrne
    by_contra hlr
    have h1 := hmem r hlr
    have h2 : e₁ * (r : ℕ) = 0 := by omega
    rcases Nat.mul_eq_zero.1 h2 with h' | h'
    · omega
    · exact hrne h'
  · rintro ⟨hi, hz⟩
    have hzero : ∀ r : Fin f₁, l r ≠ 0 → (r : ℕ) = 0 := by
      intro r hr
      by_contra hrne
      exact hr (hz r hrne)
    have himg : (Finset.univ.filter (fun r : Fin f₁ => l r ≠ 0)).image
        (fun r : Fin f₁ => iexp e₁ h M + e₁ * (r : ℕ)) = {0} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
      · refine Finset.mem_image.2 ⟨r₀, Finset.mem_filter.2 ⟨Finset.mem_univ r₀, hr₀⟩, ?_⟩
        simp [hi, hzero r₀ hr₀]
      · intro x hx
        obtain ⟨r, hrmem, rfl⟩ := Finset.mem_image.1 hx
        have hr := (Finset.mem_filter.1 hrmem).2
        simp [hi, hzero r hr]
    have hs : (liftC6 π e₁ h σ M l).support = {0} := by rw [hsupp, himg]
    refine ⟨?_, hs⟩
    have hle : (liftC6 π e₁ h σ M l).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      by_contra hne
      have hmem : m ∈ (liftC6 π e₁ h σ M l).support := Polynomial.mem_support_iff.2 hne
      rw [hs] at hmem
      simp only [Finset.mem_singleton] at hmem
      omega
    omega

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.liftC6_support
#print axioms Uniformity.Density.Gauge.liftC6_xfree

end AxCheck
