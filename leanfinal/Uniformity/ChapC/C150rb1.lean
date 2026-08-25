/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131y
import Uniformity.ChapC.C74
import Uniformity.ChapC.C64
import Uniformity.ChapC.C52
import Uniformity.ChapC.C53b

/-!
# Uniformity.ChapC.C150rb1 — READY batch 1: theta/faithful-band corollaries

Unit RB1. Lands three of the four names from `runs/wave-b/verdict_CCUR.md`'s "Batch 1 — the
theta/faithful-band corollaries" list, each wired to an already-proved differently-named
theorem landed by an earlier unit:

* `entry_band_faithful` (C.75) — a corollary of `Uniformity.Density.Tower.C131y.shadow_faithful_band`
  (the general faithful-band theorem) plus `TowerDatum.one_le_margin` (C.71): the hypothesis
  `m ≤ (μ₂ - j) * T.E₂` implies `m < T.theta μ₂ j = (μ₂ - j) * T.E₂ + T.margin` since
  `1 ≤ T.margin`, which is exactly `shadow_faithful_band`'s strict band hypothesis.
* `shadow_attained_of_certificate` (C.74 family) — `TouchCert T hπ μ₂ j` unfolds to a
  `dv2Hgt` equation on `shadowDev T (Φ₂^μ₂) j - dev Φ₂ (Φ₂^μ₂) j`; `dev_pow_self` (C.52) gives
  `dev (composedKey T) ((composedKey T) ^ μ₂) j = 0` for `j < μ₂` (the Kronecker-delta digit
  law), which discharges both conjuncts via `sub_zero`.
* `blockDeg_eq` (C.64) — a direct wrap of the already-proved `Uniformity.Density.Tower.C64.
  blockDeg_eq_resigned`, whose signature is byte-identical to the re-signed leanspec form
  (amendment A-C.10: `hlab`/`hdvd` riders restored after the naked form was machine-refuted).

## The fourth name, `towerLocus_fibration` (C.53): NOT landed here — genuinely BLOCKED

The verdict's batch-1 row 4 reads `towerLocus_fibration_of_leg1` (`C53b.lean:733`) as landing
"the FULL signed conclusion" of C.53's `towerLocus_fibration`, and asks this unit to "verify
the hypothesis list matches the signed axiom exactly." It does not, and the gap is real, not
cosmetic:

* The leanspec-signed `towerLocus_fibration` is **unconditional** in `T` — its hypothesis list
  is exactly `(T, hπ, hh, [IsAdicComplete …], [Finite (ResidueField O)], μ₂ N, hμ₂)`, nothing
  else.
* `towerLocus_fibration_of_leg1` proves the *same conclusion shape*, but only under an
  **additional explicit hypothesis** `h1 : TowerBudgetIff T μ₂` (leg 1 = C.52's signed
  `towerLocus_iff_budget`, both directions, for every monic `f` of the right degree).
* `TowerBudgetIff` is an *iff*: `mem_towerLocus_of_budget` (C.131ae, `⟸`) is landed, but the
  `⟹` direction (`budget_of_mem_towerLocus`, C.131af′, C.52 Step 3, the "reverse
  correspondence") is **not landed anywhere in the corpus** — confirmed by `rg` across
  `leanfinal/Uniformity/`: the only hits for `budget_of_mem_towerLocus` are prose references
  (`C52.lean`'s proof-spine comment, `C131ae.lean`'s own docstring naming it as future work).
  `leanfinal/scratch/DEC2_check.lean` (untracked scratch, another agent's in-flight file, not
  touched by this unit) contains an "elaboration only — no proof, no `sorry`, no axiom" stub
  for exactly this reverse direction, confirming it is still open, not a landed proof I can
  cite.

So `h1 : TowerBudgetIff T μ₂` cannot be constructed for a general `TowerDatum T` today, and
supplying it is genuine unattempted proof work (the reverse budget-correspondence), not a
30–60 minute wrap. Adding `h1` as an extra hypothesis to a declaration named `towerLocus_fibration`
would silently narrow the signed (unconditional) statement — exactly the kind of statement
change this campaign's honesty discipline forbids without explicit sign-off. Per the task's own
instructions, this row is left as an honest **BLOCKED**, not attempted here; see
`runs/wave-b/verdict_RB1.md` for the full disposition. No new declaration under the name
`towerLocus_fibration` is added by this file.

## DEPENDS

C.131y (`shadow_faithful_band`) · C.74 (`TouchCert`) · C.71 (`TowerDatum.theta`/`.margin`/
`.one_le_margin`, via C.74's import) · C.52 (`dev_pow_self`) · C.64 (`blockDeg_eq_resigned`) ·
C.53b (`composedKey_natDegree_D₂`) · C.47 (`composedKey_monic`, via C.53b's import).

## Status

Sorry-free, no new axiom. Axiom footprint: Lean core for every declaration in this file (AxCheck
footer) — no cite is inherited by any of the three wrapped theorems.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C131y (shadow_faithful_band)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### NODE C.75 — `entry_band_faithful` -/

/-- **NODE C.75 — `entry_band_faithful`** (leanspec-signed, verbatim). Below the CLIPPED band
`m ≤ (μ₂ - j) * T.E₂` (a weaker, purely-arithmetic guard than the strict `m < T.theta μ₂ j` of
C.72's `shadow_faithful_band`), the shadow digit still has exactly the honest digit's height and
coherent residual read: `1 ≤ T.margin` (C.71's `one_le_margin`) turns the non-strict bound into
the strict one `shadow_faithful_band` needs. -/
theorem entry_band_faithful {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {j : ℕ} (hj : j < μ₂) {m : ℕ} (hm : m ≤ (μ₂ - j) * T.E₂)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j) := by
  have hmar := T.one_le_margin
  have hlt : m < T.theta μ₂ j := by
    simp only [TowerDatum.theta]
    omega
  exact shadow_faithful_band T hπ hh hf hj hlt hval

/-! ### NODE C.74 (terminal layer, first clause) — `shadow_attained_of_certificate` -/

/-- **NODE C.74 — `shadow_attained_of_certificate`** (leanspec-signed, verbatim). The touch
certificate forces the honest (composed) digit of `Φ₂^{μ₂}` at coordinate `j < μ₂` to vanish
(`dev_pow_self`'s Kronecker-delta law, C.52), and consequently the shadow digit's level-two
height sits exactly at the threshold `Θ_j`. -/
theorem shadow_attained_of_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ j : ℕ} (hj : j < μ₂) (hc : TouchCert T hπ μ₂ j) :
    dev (composedKey T) ((composedKey T) ^ μ₂) j = 0 ∧
    dv2Hgt (T.levelDatum hπ) (shadowDev T ((composedKey T) ^ μ₂) j) = (T.theta μ₂ j : ℕ∞) := by
  have hpos : 0 < (composedKey T).natDegree := by
    rw [composedKey_natDegree_D₂ T hπ]
    exact Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) (Nat.mul_pos T.he₂ T.hf₂)
  have hzero : dev (composedKey T) ((composedKey T) ^ μ₂) j = 0 := by
    rw [dev_pow_self (composedKey_monic T) hpos, if_neg (Nat.ne_of_lt hj)]
  refine ⟨hzero, ?_⟩
  have hc' : dv2Hgt (T.levelDatum hπ)
      (shadowDev T ((composedKey T) ^ μ₂) j - dev (composedKey T) ((composedKey T) ^ μ₂) j)
        = (T.theta μ₂ j : ℕ∞) := hc
  rw [hzero, sub_zero] at hc'
  exact hc'

/-! ### NODE C.64 — `blockDeg_eq` -/

/-- **NODE C.64 — `blockDeg_eq`** (leanspec-signed, verbatim re-signed form, amendment A-C.10).
A direct wrap of `Uniformity.Density.Tower.C64.blockDeg_eq_resigned`: with the block's label and
`D′`-divisibility riders in hand, the block's degree is exactly `keyDeg₂ * mult₂`. -/
theorem blockDeg_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f)
    (hlab : HasLabel L (blockFactor L f))
    (hdvd : (F.e₁ * F.f₁) ∣ (blockFactor L f).natDegree) :
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f :=
  C64.blockDeg_eq_resigned L hπ hctx hlab hdvd

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.entry_band_faithful
#print axioms Uniformity.Density.Tower.shadow_attained_of_certificate
#print axioms Uniformity.Density.Tower.blockDeg_eq

end AxCheck
