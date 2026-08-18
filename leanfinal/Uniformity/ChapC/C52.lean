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
  sorry

/-- **Step 0, the two carries** (`EFF.GENTOW1.19`, value-blind): a box monomial
`C c · x^a · Φ′^b · Φ₂^j` has every level-1 slot at weight `≥ gridWeight T v a b j` whenever
`v ≤ addVal c` — the x-carry priced by the key's one side, the `Φ′`-carry priced by `E₂`. -/
theorem dvAbove_boxMonomial {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (c : O) (a b j : ℕ) :
    DvAbove F (Polynomial.C c * Polynomial.X ^ a * F.key ^ b * composedKey T ^ j) T.u₂ T.e₂
      (((F.e₁ * T.e₂ : ℕ) : ℕ∞) * addVal O c + ((slotOffset T a b + j * T.E₂ : ℕ) : ℕ∞)) := by
  sorry

/-- **Step 1, digit bookkeeping**: the `φ`-adic development of `φ^μ` is the Kronecker delta. -/
theorem dev_pow_self {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (μ j : ℕ) :
    dev φ (φ ^ μ) j = if j = μ then 1 else 0 := by
  sorry

/-- **Step 1** (`EFF.GENTOW1.20`): `Φ₂^{μ₂}`'s own level-1 data, via C.47's test-key hood and
graded multiplicativity — the composed key's power lies on the locus it fences. -/
theorem composedKey_pow_mem_towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂) :
    composedKey T ^ μ₂ ∈ towerLocus T μ₂ := by
  sorry

/-- **Step 2** (`EFF.GENTOW1.21`, the ⟸ realizability): digits at-or-above the floors put every
slot of `g = f − Φ₂^{μ₂}` at weight `≥ μ₂E₂ + 1`; adding `Φ₂^{μ₂}` (Step 1) leaves the full
inner side with residual `r̃^{μ₂}` exact. -/
theorem mem_towerLocus_of_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂)
    (hbud : ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)) :
    f ∈ towerLocus T μ₂ := by
  sorry

/-- **Step 3** (`EFF.GENTOW1.22`, the ⟹ necessity): on `𝒯` the side-lattice reads of `f` equal
`Φ₂^{μ₂}`'s, so the lattice digits of `g = f − Φ₂^{μ₂}` cancel one digit up, off-lattice slots
clear by pin-lattice class separation, and Step 0 converts the slot bounds to the floors. -/
theorem budget_of_mem_towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) (hmem : f ∈ towerLocus T μ₂) :
    ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a) := by
  sorry

/-! ### The signed statement -/

/-- **NODE C.52** (GENTOW-1(a)) — the weight characterization: `f ∈ 𝒯` iff every composed digit
clears its budget floor. Signed A-C.1; statement byte-frozen from `leanspec/Leanspec/ChapC.lean`. -/
theorem towerLocus_iff_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) :
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a) :=
  ⟨budget_of_mem_towerLocus T hπ hh hμ₂ hf hdeg,
   mem_towerLocus_of_budget T hπ hh hμ₂ hf hdeg⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.budgetFloor
#print axioms Uniformity.Density.Tower.towerLocus_iff_budget

end AxCheck
