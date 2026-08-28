/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39a
import Uniformity.ChapB.B43
import Uniformity.ChapB.B83Kit
import Uniformity.ChapC.C35b
import Uniformity.ChapC.C130s6
import Uniformity.ChapC.C131ae0

/-!
# Uniformity.ChapC.C130nv — S2-source plan nodes NV-0/NV-1 (the polynomial-value shell and the level-one universal product)

**S2-source plan nodes NV-0 and NV-1** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`
§3, §5.1 rows `value_mul`/`hgt`, §6 rows NV-0/NV-1): the CLEARED polynomial value functions
of the S2 depth-two tower at both live levels — integers via `C130s6.toZ`, cleared by the
S2 parameters — with their zero and addition law banks (NV-0), and the UNIVERSAL product law
for the first augmentation value, all zero cases included, with no monic/pure/degree fences
on the polynomial arguments (NV-1, the warm-up to the CORE chain NV-2..4).

## NV-0 — the two cleared value functions (the shell)

* **Level one** (`s2Hgt₁`, NEW): the cleared first-augmentation value
  `toZ ((s2Frame h2 hq).stageHeight A)`, i.e. `toZ (suppVal X A 1 2)` at the S2 level-one
  side `(u₁, ℓ₁) = (h, e₁) = (1, 2)` — the cleared `v₁` with `v₁(x) = 1/2`, in E.10's
  `WithTop ℤ` carrier.  Both identifications are `rfl` pins (`s2Hgt₁_eq_stageHeight`,
  `s2Hgt₁_eq_suppVal`); nothing fresh is invented.  Law bank: `s2Hgt₁_zero`,
  `s2Hgt₁_ne_top`/`s2Hgt₁_eq_top_iff` (+ the exact slot-fenced field shape
  `s2Hgt₁_ne_top_slot` at `Dcum 1`), the ultrametric inequality `s2Hgt₁_add_ge`, and the
  ultrametric equality off ties `s2Hgt₁_add_eq` — U12's `PolynomialValuation` law list
  (`scratch/U12_check.lean`, the elaboration authority), minus `map_mul` which is NV-1's.
  Teeth: `h₁(1) = 0`, `h₁(x) = 1` (the cleared `v(x) = 1/2`), `h₁(2) = 2` (the cleared
  `v(2) = 1`).
* **Level two** (LANDED, not restated): `C130s6.s2Hgt₂ = toZ (dvSupp (s2Frame h2 hq) A 5 2)`
  with its complete zero/addition bank (`s2Hgt₂_zero`, `s2Hgt₂_ne_top`, `s2Hgt₂_add_ge`,
  `s2Hgt₂_add_eq`, C130s6).  This file adds ONLY the two genuinely missing shell pieces:
  the finiteness-iff shape `s2Hgt₂_eq_top_iff` (U12's `finite_iff`), and the SHELL TIES
  `dvHgt_eq_stageHeight_dev` / `s2_dvHgt_eq_s2Hgt₁_dev` (`rfl`): the level-two value is the
  `(u₂, ℓ₂) = (5, 2)`-weighted development over the LEVEL-ONE value of the `Φ′`-development
  coefficients — the display the CORE chain NV-2..4 inducts on.

## NV-1 — the level-one universal product law

★ `s2Hgt₁_mul : s2Hgt₁ (A * B) = s2Hgt₁ A + s2Hgt₁ B` for ALL `A B` — no fences; the zero
cases ride the `⊤`-absorbing `WithTop ℤ` addition.  Engine: `suppVal_mul_univ`, the
universal (all zero cases) order-one product law at any key and any positive coprime side.

**Verification note (the NV-1 row's charge — which landed lemma actually gives it):** the
level-one product is given by **B39a's `suppVal_mul_gen`** (the general fenced product law),
with its finiteness/side witnesses discharged by B39b's `sideSet_nonempty_gen` and B43's
`suppVal_ne_top_of_ne_zero` + `exists_sideMin_height`, and the zero cases by B32b's
`suppVal_zero_eq_top`.  `B09.gaussVal_mul` is the order-0 (unweighted Gauss) template of the
same law; it is NOT consumed here — at the weighted side `(1, 2)` the landed general lemma
is `suppVal_mul_gen`, not `gaussVal_mul`.

## What this node does NOT claim (honesty scope)

* No level-TWO product law: `dvSupp (A*B) 5 2 = dvSupp A 5 2 + dvSupp B 5 2` is the CORE
  chain NV-2..4 (outer endpoints / outer convolution / level-two product) and is untouched.
* No `NodePointSource`/`SplitNodePointSource` is inhabited; no `valueOn`, points,
  localization, or `AddValuation` packaging (NV-5/NV-6, NP-0).
* No level-one DIGIT/FULL tables and no complete stage-law bank at `i = 1` (NP-1); the
  slot-shaped `s2Hgt₁_ne_top_slot` is provided because it is a pure value-shell fact.
* The generic `suppVal_mul_univ` fences (`0 < u`, `0 < ℓ`, coprimality, `IsKey φ`) are the
  plan's own SIDE parameters (instantiated by S2 numerals), not polynomial fences; the
  degenerate side `u = 0` is out of the plan's scope and NOT claimed.

**DEPENDS.** C130s6 (`toZ` + carrier dictionary, `s2Hgt₂` + bank) · C130s2 (`s2DepthTwo`,
`Dcum` numerals) · C.97 (`s2Frame`) · C35b (`sh_C`, `sh_C_pow`, `sh_X`, frame numerals) ·
C.02 (`stageHeight`) · C.06 (`dvHgt`, `dvSupp`) · B39a (`suppVal_mul_gen`,
`suppVal_eq_of_onSide`) · B39b (`sideSet_nonempty_gen`) · B43
(`suppVal_ne_top_of_ne_zero`, `exists_sideMin_height`) · B32b (`suppVal_zero_eq_top`,
`min_suppVal_le_suppVal_add`) · B.20 (`sideMin`, `onSide_of_mem_sideSet`) · B83Kit
(`GateKit.isKey_X`) · C131ae0 (`suppVal_add_eq_left_of_lt`, `[UNT 2026-08-28]` split out of
C131ae.lean to avoid importing C131ae's own C131ac dependency — see C131ae0.lean's header).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130nv

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6

/-! ## Part 1 — the carrier dictionary is additive

C130s6's `toZ : ℕ∞ → WithTop ℤ` carries `⊤`-absorbing addition to `⊤`-absorbing addition;
this is the lemma that lets every `ℕ∞`-level product/addition law ride into E.10's
`WithTop ℤ` carrier. -/

theorem toZ_add (x y : ℕ∞) : toZ (x + y) = toZ x + toZ y := by
  induction x using ENat.recTopCoe with
  | top => rw [top_add, toZ_top, top_add]
  | coe m =>
    induction y using ENat.recTopCoe with
    | top => rw [add_top, toZ_top, add_top]
    | coe n =>
      rw [← Nat.cast_add, toZ_coe, toZ_coe, toZ_coe, ← WithTop.coe_add, ← Nat.cast_add]

/-! ## Part 2 — the generic order-one layer: universal product, and equality off ties -/

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- ★ **NV-1's engine — the universal order-one product law.**  `suppVal` at any key `φ` and
any positive coprime side `(u, ℓ)` is additive on ALL products — no monicity, purity, degree,
or nonzeroness fence on `f` or `z`.  The zero cases ride B32b's `suppVal_zero_eq_top` and the
`⊤`-absorbing `ℕ∞` addition; the nonzero case is B39a's landed general product law
`suppVal_mul_gen`, its witnesses discharged by B39b's `sideSet_nonempty_gen` and B43's
`suppVal_ne_top_of_ne_zero`/`exists_sideMin_height`. -/
theorem suppVal_mul_univ (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (f z : Polynomial O) :
    suppVal φ (f * z) u ℓ = suppVal φ f u ℓ + suppVal φ z u ℓ := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_mul, suppVal_zero_eq_top hℓ u, top_add]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, suppVal_zero_eq_top hℓ u, add_top]
  have htf : suppVal φ f u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero hφ.monic hφ.pos hf
  have htz : suppVal φ z u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero hφ.monic hφ.pos hz
  have hnf : (sideSet φ f u ℓ).Nonempty := sideSet_nonempty_gen φ f u ℓ
  have hnz : (sideSet φ z u ℓ).Nonempty := sideSet_nonempty_gen φ z u ℓ
  obtain ⟨Hf, hHf⟩ := exists_sideMin_height hℓ htf hnf
  obtain ⟨Hz, hHz⟩ := exists_sideMin_height hℓ htz hnz
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * sideMin φ f u ℓ hnf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * sideMin φ z u ℓ hnz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  rw [suppVal_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz, hSf, hSz, ← Nat.cast_add]
  congr 1
  ring

/-- **`suppVal` ultrametric equality off ties**, in the symmetric `min` shape (the E.10
`hgt_add_eq` law shape at order one) — both directions of C131ae's landed
`suppVal_add_eq_left_of_lt`. -/
theorem suppVal_add_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) {a b : Polynomial O}
    (hne : suppVal φ a u ℓ ≠ suppVal φ b u ℓ) :
    suppVal φ (a + b) u ℓ = min (suppVal φ a u ℓ) (suppVal φ b u ℓ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact C131ae.suppVal_add_eq_left_of_lt hφ hd hℓ u h
  · rw [min_eq_right h.le, add_comm]
    exact C131ae.suppVal_add_eq_left_of_lt hφ hd hℓ u h

/-- **the SHELL TIE, generic form** (`rfl`): the level-two slot height at development
coordinate `j` IS the level-one (stage) value of the `j`-th `Φ′`-development coefficient —
C.06's tower recursion, pinned as an anti-drift equation for the NV-2..4 induction. -/
theorem dvHgt_eq_stageHeight_dev (F : KeyFrame O π) (A : Polynomial O) (j : ℕ) :
    dvHgt F A j = F.stageHeight (dev F.key A j) := rfl

end Generic

/-! ## Part 3 — NV-0: the S2 level-one cleared value `s2Hgt₁` -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **the S2 LEVEL-ONE cleared polynomial value** (NV-0): the corpus's stage height
`dv = e₁·v` at the S2 frame — the first augmentation value with `v₁(x) = h/e₁ = 1/2`,
cleared by `e₁ = 2` — in E.10's `WithTop ℤ` carrier via `toZ`. -/
noncomputable def s2Hgt₁ (A : Polynomial O) : WithTop ℤ :=
  toZ ((s2Frame h2 hq).stageHeight A)

/-- Anti-drift pin: the level-one value IS the frame's stage height — nothing fresh. -/
theorem s2Hgt₁_eq_stageHeight (A : Polynomial O) :
    s2Hgt₁ h2 hq A = toZ ((s2Frame h2 hq).stageHeight A) := rfl

/-- Anti-drift pin: the level-one value IS B.14's cleared support at the order-0 key `X`
and the S2 level-one side `(u₁, ℓ₁) = (h, e₁) = (1, 2)`. -/
theorem s2Hgt₁_eq_suppVal (A : Polynomial O) :
    s2Hgt₁ h2 hq A = toZ (suppVal Polynomial.X A 1 2) := rfl

/-- the level-one `hgt_zero` law (`EFF.T2.05`'s shape at `i = 1`): `h₁(0) = +∞`. -/
theorem s2Hgt₁_zero : s2Hgt₁ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2Hgt₁_eq_suppVal, suppVal_zero_eq_top (by norm_num : (0 : ℕ) < 2) 1, toZ_top]

/-- every nonzero polynomial has finite level-one value (B43's unfenced finiteness through
the carrier dictionary). -/
theorem s2Hgt₁_ne_top {A : Polynomial O} (hA : A ≠ 0) : s2Hgt₁ h2 hq A ≠ ⊤ := by
  rw [s2Hgt₁_eq_suppVal, ne_eq, toZ_eq_top_iff]
  exact suppVal_ne_top_of_ne_zero Polynomial.monic_X
    (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) hA

/-- the finiteness-iff shape (U12 `PolynomialValuation.finite_iff` at level one). -/
theorem s2Hgt₁_eq_top_iff {A : Polynomial O} : s2Hgt₁ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    exact s2Hgt₁_ne_top h2 hq hA h
  · rintro rfl
    exact s2Hgt₁_zero h2 hq

/-- the `hgt_ne_top` field shape at `i = 1` (slot fence `Dcum 1`), for the eventual
level-one stage row of the split node source. -/
theorem s2Hgt₁_ne_top_slot :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 1 →
      s2Hgt₁ h2 hq A ≠ ⊤ :=
  fun _ hA _ => s2Hgt₁_ne_top h2 hq hA

/-- the level-one `hgt_add_ge` law: the ultrametric inequality. -/
theorem s2Hgt₁_add_ge (A B : Polynomial O) :
    min (s2Hgt₁ h2 hq A) (s2Hgt₁ h2 hq B) ≤ s2Hgt₁ h2 hq (A + B) := by
  simp only [s2Hgt₁_eq_suppVal h2 hq]
  rw [← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_suppVal_le_suppVal_add Polynomial.monic_X
    (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) (by norm_num) 1 A B)

/-- the level-one `hgt_add_eq` law: ultrametric equality off ties. -/
theorem s2Hgt₁_add_eq (A B : Polynomial O) (hne : s2Hgt₁ h2 hq A ≠ s2Hgt₁ h2 hq B) :
    s2Hgt₁ h2 hq (A + B) = min (s2Hgt₁ h2 hq A) (s2Hgt₁ h2 hq B) := by
  have hne' : suppVal Polynomial.X A 1 2 ≠ suppVal Polynomial.X B 1 2 := by
    intro h
    exact hne (by simp only [s2Hgt₁_eq_suppVal h2 hq, h])
  simp only [s2Hgt₁_eq_suppVal h2 hq]
  rw [← toZ_min]
  exact congrArg toZ (suppVal_add_eq Polynomial.monic_X
    (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) (by norm_num) 1 hne')

/-! ### 3a. Teeth — the level-one value is the cleared `v₁` -/

/-- **tooth (value)**: `h₁(1) = 0` (U12 `map_one` at level one). -/
theorem s2Hgt₁_one : s2Hgt₁ h2 hq (1 : Polynomial O) = ((0 : ℤ) : WithTop ℤ) := by
  have hval : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = ((0 : ℕ) : ℕ∞) := by
    rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], C35b.sh_C h2 hq]
    simp
  rw [s2Hgt₁, hval, toZ_coe]
  norm_num

/-- **tooth (value)**: `h₁(x) = 1` — the cleared `v₁(x) = 1/2`. -/
theorem s2Hgt₁_X : s2Hgt₁ h2 hq (Polynomial.X : Polynomial O) = ((1 : ℤ) : WithTop ℤ) := by
  have hval : (s2Frame h2 hq).stageHeight (Polynomial.X : Polynomial O) = ((1 : ℕ) : ℕ∞) := by
    rw [C35b.sh_X h2 hq]
    norm_num
  rw [s2Hgt₁, hval, toZ_coe]
  norm_num

/-- **tooth (value)**: `h₁(2) = 2` — the cleared `v(2) = 1` (C35b's `sh_C_pow` at `k = 1`). -/
theorem s2Hgt₁_C_two : s2Hgt₁ h2 hq (Polynomial.C (2 : O)) = ((2 : ℤ) : WithTop ℤ) := by
  have hval : (s2Frame h2 hq).stageHeight (Polynomial.C (2 : O)) = ((2 : ℕ) : ℕ∞) := by
    have h := C35b.sh_C_pow h2 hq 1
    rw [pow_one] at h
    rw [h]
  rw [s2Hgt₁, hval, toZ_coe]
  norm_num

/-! ### 3b. NV-0's level-two half — the missing shell pieces over the LANDED `s2Hgt₂`

`C130s6.s2Hgt₂` and its zero/addition bank are landed and NOT restated.  What was missing
for the shell: the finiteness-iff shape, and the S2 instance of the shell tie. -/

/-- the finiteness-iff shape at level two (U12 `finite_iff`; forward half is C130s6's
`s2Hgt₂_ne_top`, backward is `s2Hgt₂_zero`). -/
theorem s2Hgt₂_eq_top_iff {A : Polynomial O} : s2Hgt₂ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    exact s2Hgt₂_ne_top h2 hq hA h
  · rintro rfl
    exact s2Hgt₂_zero h2 hq

/-- **the S2 SHELL TIE** (`rfl`): the level-two slot height at development coordinate `j`,
read in the carrier, IS the LEVEL-ONE value `s2Hgt₁` of the `j`-th `Φ′`-development
coefficient.  With C130s6's `s2Hgt₂_eq_dvSupp` and C.06's `dvSupp`, this displays `s2Hgt₂`
as the `(u₂, ℓ₂) = (5, 2)`-weighted development over `s2Hgt₁` — the shell NV-2..4 inducts
on. -/
theorem s2_dvHgt_eq_s2Hgt₁_dev (A : Polynomial O) (j : ℕ) :
    toZ (dvHgt (s2Frame h2 hq) A j)
      = s2Hgt₁ h2 hq (dev (s2Frame h2 hq).key A j) := rfl

/-! ## Part 4 — NV-1: the level-one UNIVERSAL product law -/

/-- ★ **NODE NV-1 — the universal product law for the first augmentation value.**
`h₁(A·B) = h₁(A) + h₁(B)` for ALL polynomials `A`, `B` — every zero case included (the
`WithTop ℤ` addition is `⊤`-absorbing), no monic/pure/degree fences.  The S2 instantiation
of `suppVal_mul_univ` at the key `X` (`GateKit.isKey_X`), the side `(1, 2)` (positive,
coprime), and the uniformizer `2` (`h2`). -/
theorem s2Hgt₁_mul (A B : Polynomial O) :
    s2Hgt₁ h2 hq (A * B) = s2Hgt₁ h2 hq A + s2Hgt₁ h2 hq B := by
  simp only [s2Hgt₁_eq_suppVal h2 hq]
  rw [← toZ_add]
  exact congrArg toZ (suppVal_mul_univ h2 GateKit.isKey_X Nat.one_pos (by norm_num)
    (by decide) A B)

/-- **tooth (product)**: `h₁(x·x) = 2 = 1 + 1`, through the product law. -/
theorem s2Hgt₁_X_sq :
    s2Hgt₁ h2 hq ((Polynomial.X : Polynomial O) * Polynomial.X) = ((2 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₁_mul h2 hq, s2Hgt₁_X h2 hq, ← WithTop.coe_add]
  exact WithTop.coe_inj.mpr (by norm_num)

/-- **tooth (product, mixed)**: `h₁(2x) = 3 = 2 + 1`, through the product law. -/
theorem s2Hgt₁_two_X :
    s2Hgt₁ h2 hq (Polynomial.C (2 : O) * Polynomial.X) = ((3 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₁_mul h2 hq, s2Hgt₁_C_two h2 hq, s2Hgt₁_X h2 hq, ← WithTop.coe_add]
  exact WithTop.coe_inj.mpr (by norm_num)

/-- **tooth (product, zero case)**: `h₁(0·B) = ⊤` THROUGH the product law — the `⊤`-absorbing
zero case fires, no fence needed. -/
theorem s2Hgt₁_zero_mul (B : Polynomial O) : s2Hgt₁ h2 hq (0 * B) = ⊤ := by
  rw [s2Hgt₁_mul h2 hq, s2Hgt₁_zero h2 hq, top_add]

end S2

end Uniformity.Density.Tower.C130nv

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130nv.toZ_add
#print axioms Uniformity.Density.Tower.C130nv.suppVal_mul_univ
#print axioms Uniformity.Density.Tower.C130nv.suppVal_add_eq
#print axioms Uniformity.Density.Tower.C130nv.dvHgt_eq_stageHeight_dev
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_eq_stageHeight
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_eq_suppVal
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_zero
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_ne_top
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_eq_top_iff
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_ne_top_slot
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_add_ge
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_add_eq
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_one
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_X
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_C_two
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₂_eq_top_iff
#print axioms Uniformity.Density.Tower.C130nv.s2_dvHgt_eq_s2Hgt₁_dev
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_mul
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_X_sq
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_two_X
#print axioms Uniformity.Density.Tower.C130nv.s2Hgt₁_zero_mul

end AxCheck
