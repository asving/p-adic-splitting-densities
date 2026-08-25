/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131y
import Uniformity.ChapC.C131ac
import Uniformity.ChapC.C80
import Uniformity.ChapC.C53c

/-!
# Uniformity.ChapC.C123r — re-firing C.123's five deferred row-groups (unit C123R)

**Chapter C, NODE C.123R** — the re-fire pass mandated after the 2026-08-24 dv-graded-engine
and S2-source landings.  `C123.lean` (unedited, untouched by this file) fired 16+ rows and
DEFERRED five row-groups with named missing objects.  This file re-checks each named object
against the corpus AS IT STANDS TODAY and fires whichever are now landed.

## Disposition table (the five deferred groups, in `C123.lean`'s order)

| # | row-group | named missing object (as deferred) | today |
|---|---|---|---|
| 1 | node floors `[21,11]/[29,15]/[13,7]` | C.54's NODE-EQ anchor frames (no `C54.lean`) | **STILL DEFERRED** — `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §5 plans C.131ah′/ai′/aj′ for exactly this (`C.54 node floor` / `sharp CRT realization` / `field floor`) but its own text records them as unbuilt: *"C.54 is currently a blueprint node, not a landed `C54.lean` file"* / *"C.54 consumers remain OPEN"*.  No `C131ah.lean`/`C131ai.lean`/`C131aj.lean` exist. |
| 2 | refine row A5-R1 (`p₀ = 2λ = 26`) | C.56/C.57 refine-row carrier (no `C56.lean`/`C57.lean`) | **STILL DEFERRED** — still no such files; every `C.56`/`C.57` hit in the corpus (`C99r`, `C84`, `C56a`, `C47`, `C43`, `C14`, `C14a`) is a reference to the DIFFERENT node `C.56a` (`k2DigitLift`), exactly as `C123.lean` already noted. |
| 3 | FAM-B BAND-2/3 window rows | C.72's `shadow_faithful_band` (statement carrier only) | **FIRED** — see Part 1 below. `shadow_floor` (C.131w′, `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §5) and `shadow_faithful_band` (C.131y′) are now PROVED theorems, Lean-core, no `sorry`. |
| 4 | the `(1,2)`-genre bite (`EFF.HE6.20`(3)) | σ-genre member carrier C.119/C.120/C.122 (no such files) | **STILL DEFERRED** — no such files exist; the corpus's only `EFF.HE6.20` hits (`C31.lean`, `C34.lean`) are item 1 (the `R = r^m` self-label), not item 3 (the `(1,2)`-genre); no σ-genre carrier `{(2,2),(2,2)}` is landed anywhere. |
| 5 | FR5X (C.96 negative control) | C.96 (no `C96.lean`) | **STILL DEFERRED** — no such file; no other file names C.96. |

Groups 1, 2, 4, 5 are recorded here for the audit trail only; nothing is claimed for them and
no Lean object is added.  Group 3 is fired below.

## Part 1 — group 3, C.72-BAND: `shadow_floor` and `shadow_faithful_band`

Both signed C.72 statements were OPEN in `C72.lean` (statement carriers only).  The
2026-08-24 dv-graded-engine v2 fleet landed both as real theorems:

* `Uniformity.Density.Tower.C131w.shadow_floor` — GENTOW-3(i), the FLOOR;
* `Uniformity.Density.Tower.C131y.shadow_faithful_band` — GENTOW-3(ii), the FAITHFUL BAND.

`C131w.lean` also lands the tie-in `shadow_floor_statement : ShadowFloorStatement T hπ μ₂ f j`
to C.72's frozen carrier; `C131y.lean` does NOT land the analogous tie-in for the band, so
this file supplies it (`shadow_faithful_band_statement`, mirroring `shadow_floor_statement`'s
shape exactly) — the one genuinely new declaration below, everything else is instantiation.

Both are then fired at the two q = 2 towers this gate already uses, `s2Tower` (C.80) and
`linTower` (C.53c), against the witness `composedKey T ^ 3 ∈ towerLocus T 3`, which is now
available for the first time via C.131ac's `composedKey_pow_mem_towerLocus` (C.52 Step 1) —
this is exactly the membership fact `C72.lean`'s own audit flagged as the thing that "could
make these two statements vacuous" for lack of a landed witness.  It carries the gate-(b)
cite `fgmn_dv_exact_mul` (C66b) in its footprint, inherited exactly as `C131ac.lean` documents.

**Honest disclosure on the BAND instantiation.**  `composedKey T ^ μ₂` is, digit-for-digit,
the Kronecker-delta polynomial in the composed-key basis (`dev_pow_self`, C.52): every digit
below coordinate `μ₂` is the ZERO polynomial, hence has level-two height `⊤` (`dv2Hgt_zero`).
So at THIS witness the band's hypothesis `hval : dv2Hgt (…) = (m : ℕ∞)` — a FINITENESS guard
— is never satisfiable for `j < μ₂`: the row fires (the landed theorem applies, non-vacuously
as a *statement*), but it certifies no live numeral pair `(j, m)` at this particular witness.
This is exactly C.72's own module docstring's pattern-4 disclosure (the drain stratum), now
machine-checked below (`s2_composedKey_pow_drain_top` / `lin_composedKey_pow_drain_top`)
rather than left as prose.  A witness that DOES exercise the band's live content needs
C.131ae's `mem_towerLocus_of_budget` fed a genuine budget-floor hypothesis `hbud` at concrete
box digits — not further supplied here; recorded as the honest remaining gap for group 3's
"window" numerals specifically (the FLOOR row itself is fully non-vacuous, see below).

## DEPENDS

C.131w (`shadow_floor`, its statement carrier tie-in) · C.131y (`shadow_faithful_band`) ·
C.131ac (`composedKey_pow_mem_towerLocus`, the cite-carrying witness) · C.131v
(`composedKey_natDegree_mul`) · C.52 (`dev_pow_self`) · C.71 (`TowerDatum.theta`,
`TowerDatum.margin`) · C.72 (`ShadowFaithfulBandStatement`) · C.80 (`s2Tower`) · C.53c
(`linTower`).

## Status

Sorry-free.  Axiom footprint: Lean core for every declaration except the four that
instantiate `composedKey_pow_mem_towerLocus` (the witness-membership facts and everything
built from them), which carry the DECLARED literature cite `fgmn_dv_exact_mul` (C66b,
allowlist member 7) — see the AxCheck footer for exactly which.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C123r

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C53c
open Uniformity.Density.Tower.C131v (composedKey_natDegree_mul)
open Uniformity.Density.Tower.C131w (shadow_floor)
open Uniformity.Density.Tower.C131y (shadow_faithful_band)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-! ### The one new declaration: the band's tie-in to C.72's frozen carrier
(mirrors `C131w.shadow_floor_statement` exactly; `C131y.lean` did not land it). -/

/-- The landing, tied to C.72's signed statement carrier: `ShadowFaithfulBandStatement` holds
at every locus member, coordinate `j < μ₂`, and band value `m < Θ_j`. -/
theorem shadow_faithful_band_statement {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂)
    {m : ℕ} (hm : m < T.theta μ₂ j) :
    ShadowFaithfulBandStatement T hπ f j m :=
  fun hval => shadow_faithful_band T hπ hh hf hj hm hval

/-! ### The shared witness: `Φ₂³ ∈ towerLocus T 3`, from C.131ac (now landed) -/

/-- **The witness at `s2Tower`.**  `composedKey_pow_mem_towerLocus` (C.131ac, C.52 Step 1)
instantiated at `μ₂ = 3`; carries the gate-(b) cite `fgmn_dv_exact_mul`. -/
theorem s2_composedKeyPow_mem (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    composedKey (s2Tower h2 hq) ^ 3 ∈ towerLocus (s2Tower h2 hq) 3 :=
  composedKey_pow_mem_towerLocus (s2Tower h2 hq) h2 (le_refl 1) (by norm_num)

/-- **The witness at `linTower`.**  Same instantiation over the linear frame. -/
theorem lin_composedKeyPow_mem (hπ : Irreducible π) :
    composedKey (linTower hπ) ^ 3 ∈ towerLocus (linTower hπ) 3 :=
  composedKey_pow_mem_towerLocus (linTower hπ) hπ (le_refl 1) (by norm_num)

/-! ### The FLOOR row, fired non-vacuously at both landed q = 2 towers -/

/-- **C.72-BAND ROW (i), at `s2Tower`.**  Every disagreeing `dv₂`-height between the
stage-shadow and composed reads of `Φ₂³` clears the concrete threshold `Θ_j`. -/
theorem s2_shadow_floor_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    {j : ℕ} (hj : j < 3) :
    ((s2Tower h2 hq).theta 3 j : ℕ∞) ≤
      dv2Hgt ((s2Tower h2 hq).levelDatum h2)
        (shadowDev (s2Tower h2 hq) (composedKey (s2Tower h2 hq) ^ 3) j
          - dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) j) :=
  shadow_floor (s2Tower h2 hq) h2 (le_refl 1) (s2_composedKeyPow_mem h2 hq) hj

/-- **C.72-BAND ROW (i), at `linTower`.**  Same instantiation over the linear frame. -/
theorem lin_shadow_floor_row (hπ : Irreducible π) {j : ℕ} (hj : j < 3) :
    ((linTower hπ).theta 3 j : ℕ∞) ≤
      dv2Hgt ((linTower hπ).levelDatum hπ)
        (shadowDev (linTower hπ) (composedKey (linTower hπ) ^ 3) j
          - dev (composedKey (linTower hπ)) (composedKey (linTower hπ) ^ 3) j) :=
  shadow_floor (linTower hπ) hπ (le_refl 1) (lin_composedKeyPow_mem hπ) hj

/-- **The concrete `Θ_j` numerals at `s2Tower`, `μ₂ = 3`** (`E₂ = 10`, `δ = 1`):
`Θ_0 = 31`, `Θ_1 = 21`, `Θ_2 = 11` — the numeral row `s2_shadow_floor_row` clears. -/
theorem s2_theta_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Tower h2 hq).theta 3 0 = 31 ∧ (s2Tower h2 hq).theta 3 1 = 21 ∧
      (s2Tower h2 hq).theta 3 2 = 11 :=
  ⟨rfl, rfl, rfl⟩

omit [Finite (IsLocalRing.ResidueField O)] in
/-- **The concrete `Θ_j` numerals at `linTower`, `μ₂ = 3`** (`E₂ = 6`, `δ = 1`):
`Θ_0 = 19`, `Θ_1 = 13`, `Θ_2 = 7`. -/
theorem lin_theta_row (hπ : Irreducible π) :
    (linTower hπ).theta 3 0 = 19 ∧ (linTower hπ).theta 3 1 = 13 ∧
      (linTower hπ).theta 3 2 = 7 :=
  ⟨rfl, rfl, rfl⟩

/-! ### The BAND row, fired as a statement at both landed q = 2 towers -/

/-- **C.72-BAND ROW (ii), at `s2Tower`.**  `ShadowFaithfulBandStatement` holds for the witness
`Φ₂³`, every `j < 3` and every candidate band value `m < Θ_j`. -/
theorem s2_shadow_faithful_band_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    {j : ℕ} (hj : j < 3) {m : ℕ} (hm : m < (s2Tower h2 hq).theta 3 j) :
    ShadowFaithfulBandStatement (s2Tower h2 hq) h2 (composedKey (s2Tower h2 hq) ^ 3) j m :=
  shadow_faithful_band_statement (s2Tower h2 hq) h2 (le_refl 1) (s2_composedKeyPow_mem h2 hq)
    hj hm

/-- **C.72-BAND ROW (ii), at `linTower`.**  Same instantiation over the linear frame. -/
theorem lin_shadow_faithful_band_row (hπ : Irreducible π) {j : ℕ} (hj : j < 3) {m : ℕ}
    (hm : m < (linTower hπ).theta 3 j) :
    ShadowFaithfulBandStatement (linTower hπ) hπ (composedKey (linTower hπ) ^ 3) j m :=
  shadow_faithful_band_statement (linTower hπ) hπ (le_refl 1) (lin_composedKeyPow_mem hπ) hj hm

/-! ### The honest disclosure, machine-checked: this witness is drain below `μ₂ = 3` -/

/-- `composedKey T ^ 3`'s `Φ₂`-digits below coordinate `3` are all zero (`dev_pow_self`'s
Kronecker delta) — the drain stratum C.72's own docstring names. -/
theorem s2_composedKeyPow_drain (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    {j : ℕ} (hj : j < 3) :
    dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) j = 0 := by
  have hpos : 0 < (composedKey (s2Tower h2 hq)).natDegree := by
    rw [composedKey_natDegree_mul (s2Tower h2 hq) h2]
    exact Nat.mul_pos (Nat.mul_pos (s2Tower h2 hq).he₂ (s2Tower h2 hq).hf₂)
      (s2Frame h2 hq).natDegree_key_pos
  rw [dev_pow_self (composedKey_monic (s2Tower h2 hq)) hpos, if_neg (Nat.ne_of_lt hj)]

/-- Consequently the honest digit's level-two height is `⊤` — `hval`'s finiteness guard is
never met at this witness, exactly the group-3 disclosure above, machine-checked. -/
theorem s2_composedKeyPow_drain_top (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    {j : ℕ} (hj : j < 3) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2)
      (dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) j) = ⊤ := by
  rw [s2_composedKeyPow_drain h2 hq hj, dv2Hgt_zero]

omit [Finite (IsLocalRing.ResidueField O)] in
/-- Same disclosure at `linTower`. -/
theorem lin_composedKeyPow_drain (hπ : Irreducible π) {j : ℕ} (hj : j < 3) :
    dev (composedKey (linTower hπ)) (composedKey (linTower hπ) ^ 3) j = 0 := by
  have hpos : 0 < (composedKey (linTower hπ)).natDegree := by
    rw [composedKey_natDegree_mul (linTower hπ) hπ]
    exact Nat.mul_pos (Nat.mul_pos (linTower hπ).he₂ (linTower hπ).hf₂)
      (linFrame hπ).natDegree_key_pos
  rw [dev_pow_self (composedKey_monic (linTower hπ)) hpos, if_neg (Nat.ne_of_lt hj)]

omit [Finite (IsLocalRing.ResidueField O)] in
/-- Same disclosure at `linTower`: the honest digit's height is `⊤`. -/
theorem lin_composedKeyPow_drain_top (hπ : Irreducible π) {j : ℕ} (hj : j < 3) :
    dv2Hgt ((linTower hπ).levelDatum hπ)
      (dev (composedKey (linTower hπ)) (composedKey (linTower hπ) ^ 3) j) = ⊤ := by
  rw [lin_composedKeyPow_drain hπ hj, dv2Hgt_zero]

end Uniformity.Density.Tower.C123r

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C123r.shadow_faithful_band_statement
#print axioms Uniformity.Density.Tower.C123r.s2_composedKeyPow_mem
#print axioms Uniformity.Density.Tower.C123r.lin_composedKeyPow_mem
#print axioms Uniformity.Density.Tower.C123r.s2_shadow_floor_row
#print axioms Uniformity.Density.Tower.C123r.lin_shadow_floor_row
#print axioms Uniformity.Density.Tower.C123r.s2_theta_row
#print axioms Uniformity.Density.Tower.C123r.lin_theta_row
#print axioms Uniformity.Density.Tower.C123r.s2_shadow_faithful_band_row
#print axioms Uniformity.Density.Tower.C123r.lin_shadow_faithful_band_row
#print axioms Uniformity.Density.Tower.C123r.s2_composedKeyPow_drain
#print axioms Uniformity.Density.Tower.C123r.s2_composedKeyPow_drain_top
#print axioms Uniformity.Density.Tower.C123r.lin_composedKeyPow_drain
#print axioms Uniformity.Density.Tower.C123r.lin_composedKeyPow_drain_top

end AxCheck
