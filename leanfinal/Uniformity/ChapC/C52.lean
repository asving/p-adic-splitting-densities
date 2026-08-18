/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C43
import Uniformity.ChapC.C50
import Uniformity.ChapC.C51

/-!
# Uniformity.ChapC.C52 — GENTOW-1(a): the weight characterization / composed budget floors

**Chapter C, NODE C.52** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys
and the tower bridges — the GENTOW1 half; the A-C.1 amendment set governs, and the SIGNATURES are
`[signed: A-C.1 — elaborated in leanspec/Leanspec/ChapC.lean]`).

Two signed declarations, both transcribed byte-identically from the signed block:

* `budgetFloor T μ₂ j a b` — the composed budget floor: the r2-F2 display evaluated at
  `(E₂, w(a,b), e₁e₂)`, with `w(a,b) = slotOffset T a b` (C.50). The numeric-gate mirror is
  `budgetFloorN` (leanspec §13 gates).
* `towerLocus_iff_budget` — membership in the tower-entry locus `𝒯 = towerLocus T μ₂` (C.51)
  is EXACTLY the conjunction of per-slot valuation floors on the composed digits
  `dev F.key (dev (composedKey T) f j) b` (C.43's wrap-corrected composed key, B.02's `dev`).

## A-C.7 vacuity audit (registry rider, run before proving — PASSES)

The A-C.7 pattern registry (C.111 `hnode` / C.94 self-loop / C.113 `hne` / C.118 `Visible₂`)
mandates the one-line check on every unlanded A-C.1 signature whose hypotheses mention
`Nonempty`, `≠ ⊤`, or one-sided guards: *does each guard still bind on the degenerate stratum
(zero blocks, ⊤ heights, empty sides)?* Here the risky pattern sits inside `towerLocus`'s
∀-quantified pins (`hne`, `M₀`, `hp`). They BIND on-locus: `IsDvPure` — a conjunct of the same
membership — contains `0 ∈ dvSideSet`, which inhabits `hne`, and `DvOnSide`'s second conjunct
`dvHgt ≠ ⊤` forces a finite pin at `dvSideMin`. On the budget side the three ∀-ranges are
nonempty (`hμ₂`; `F.he₁ * F.hf₁`; `T.hcomp`). The `budgetFloor` ℕ-subtractions are guarded by
the `if` (underflow branch → floor `0`, the honest "no constraint" value). No vacuous stratum.

## The proof spine (EFF.GENTOW1.19–.22, at the dv-carrier)

* **Step 0** (`budgetFloor_spec` + `dvAbove_boxMonomial`): the floor is EXACTLY the least `v`
  with `gridWeight T v a b j ≥ μ₂E₂ + 1` (grid ceiling + pin), and a box monomial
  `C c · x^a · Φ′^b · Φ₂^j` has all level-1 slots at weight `≥ gridWeight T (v c) a b j` —
  the two carries (x-carry priced by the key's side, Φ′-carry priced by `E₂`), value-blind.
* **Step 1** (`dev_pow_self` + `composedKey_pow_mem_towerLocus`): `Φ₂^{μ₂}`'s own level-1 data —
  one-sided of slope `κ₂` with residual `r̃^{μ₂}` — via C.47's test-key hood and graded
  multiplicativity; i.e. `Φ₂^{μ₂} ∈ 𝒯` itself, plus its `Φ₂`-digits are `δ_{j,μ₂}`.
* **Step 2** (`mem_towerLocus_of_budget`, the ⟸): floors ⟹ `g = f − Φ₂^{μ₂}` sits strictly
  above the inner side (Step 0) ⟹ adding `Φ₂^{μ₂}` (Step 1) leaves the full side + residual
  exact (ultrametric min-rule; the outer-grammar chain of the source is absorbed by the
  dv-carrier's total `dvHgt`).
* **Step 3** (`budget_of_mem_towerLocus`, the ⟹): on `𝒯` the side-lattice reads of `f` equal
  `Φ₂^{μ₂}`'s (same residual, same normalizer convention), so the lattice digits cancel one
  digit up; off-lattice slots are strictly above by the pin-lattice class separation (C.20);
  Step 0's triangular conversion turns the slot bounds into the composed floors.

## Status

**SKELETON + step lemmas** — frozen statements committed first per the survival-floor rule;
the capstone iff is wired from the four step lemmas; per-leg fills in per-commit increments.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the composed budget floor (the r2-F2 display at `(E₂, w(a,b), e₁e₂)`); the numeric-gate
mirror is `budgetFloorN`. -/
def budgetFloor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ j a b : ℕ) : ℕ :=
  let w := slotOffset T a b
  let tgt := (μ₂ - j) * T.E₂ - w
  let d := F.e₁ * T.e₂
  if (μ₂ - j) * T.E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

/-! ### Step lemmas (helpers, NOT signed — the signed statement is `towerLocus_iff_budget`) -/

/-- All level-1 slots of `P` at weight `≥ w`, on the `(u, ℓ)` grid: the per-slot form of
"sits at-or-above the side value `w`" (`dvSupp`'s summand, unclipped to any range). -/
def DvAbove (F : KeyFrame O π) (P : Polynomial O) (u ℓ : ℕ) (w : ℕ∞) : Prop :=
  ∀ i : ℕ, w ≤ ℓ • dvHgt F P i + (u * i : ℕ∞)

/-- **Step 0, the grid ceiling** (`EFF.GENTOW1.19` arithmetic): `budgetFloor` is EXACTLY the
least `v` whose grid weight clears `μ₂E₂ + 1` — the r2-F2 ceiling-plus-pin display, unwound. -/
theorem budgetFloor_le_iff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ j : ℕ} (a b : ℕ) (hj : j < μ₂) (v : ℕ) :
    budgetFloor T μ₂ j a b ≤ v ↔ μ₂ * T.E₂ + 1 ≤ gridWeight T v a b j := by
  have hd : 0 < F.e₁ * T.e₂ := Nat.mul_pos F.he₁ T.he₂
  have hsplit : μ₂ * T.E₂ = (μ₂ - j) * T.E₂ + j * T.E₂ := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj.le]
  simp only [budgetFloor, gridWeight]
  set w := slotOffset T a b with hw
  set m := (μ₂ - j) * T.E₂ with hm
  set d := F.e₁ * T.e₂ with hdd
  by_cases hcase : m < w
  · simp only [if_pos hcase]
    constructor
    · intro _
      omega
    · intro _
      exact Nat.zero_le v
  · simp only [if_neg hcase]
    push Not at hcase
    -- the ceil-plus-pin display collapses to `⌊(m − w)/d⌋ + 1` in both mod classes
    have hqr := Nat.div_add_mod (m - w) d
    have hrlt : (m - w) % d < d := Nat.mod_lt _ hd
    have hkey : (m - w + d - 1) / d + (if (m - w) % d == 0 then 1 else 0)
        = (m - w) / d + 1 := by
      simp only [beq_iff_eq]
      by_cases h0 : (m - w) % d = 0
      · rw [if_pos h0]
        have hdback : d - 1 + 1 = d := Nat.sub_add_cancel hd
        have h1 : m - w + d - 1 = d * ((m - w) / d) + (d - 1) := by omega
        rw [h1]
        have hdiv : (d * ((m - w) / d) + (d - 1)) / d = (m - w) / d := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (Nat.sub_lt hd Nat.one_pos), Nat.add_zero]
        rw [hdiv]
      · rw [if_neg h0]
        have hrpos : 0 < (m - w) % d := Nat.pos_of_ne_zero h0
        have hmul : d * ((m - w) / d + 1) = d * ((m - w) / d) + d := by ring
        have h1 : m - w + d - 1 = d * ((m - w) / d + 1) + ((m - w) % d - 1) := by omega
        rw [h1]
        have hdiv : (d * ((m - w) / d + 1) + ((m - w) % d - 1)) / d
            = (m - w) / d + 1 := by
          rw [Nat.mul_add_div hd,
            Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hrlt), Nat.add_zero]
        rw [hdiv]
    rw [hkey, Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd, hsplit, Nat.mul_comm v d]
    constructor
    · intro h
      omega
    · intro h
      omega

/-- **Step 1, digit bookkeeping**: the `φ`-adic development of `φ^μ` is the Kronecker delta. -/
theorem dev_pow_self {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (μ j : ℕ) :
    dev φ (φ ^ μ) j = if j = μ then 1 else 0 := by
  have hone : φ ^ μ = (1 : Polynomial O) * φ ^ μ := (one_mul _).symm
  have hdeg1 : (1 : Polynomial O).degree < φ.degree :=
    Polynomial.degree_lt_degree (by simpa using hd)
  rcases lt_trichotomy j μ with hj | rfl | hj
  · rw [hone, dev_mul_pow_of_lt hφ _ _ _ hj, if_neg (Nat.ne_of_lt hj)]
  · have hshift := dev_mul_pow hφ j (1 : Polynomial O) 0
    rw [Nat.add_zero] at hshift
    rw [hone, hshift, if_pos rfl]
    change (1 : Polynomial O) %ₘ φ = 1
    exact (Polynomial.modByMonic_eq_self_iff hφ).mpr hdeg1
  · obtain ⟨m, hm⟩ : ∃ m, j = μ + m := ⟨j - μ, by omega⟩
    subst hm
    rw [hone, dev_mul_pow hφ, if_neg (by omega)]
    refine dev_eq_zero_of_lt hφ hd _ _ ?_
    have hm1 : 1 ≤ m := by omega
    have hmul : 1 * φ.natDegree ≤ m * φ.natDegree := Nat.mul_le_mul_right _ hm1
    simpa using by omega

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.budgetFloor
#print axioms Uniformity.Density.Tower.budgetFloor_le_iff
#print axioms Uniformity.Density.Tower.dev_pow_self

end AxCheck
