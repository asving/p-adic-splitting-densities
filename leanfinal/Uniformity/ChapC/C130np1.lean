/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130nv

/-!
# Uniformity.ChapC.C130np1 — the S2 level-ONE stage-source table (S2-source plan node NP-1)

**S2-source plan node NP-1** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §5.1 rows
`hgt`/`dig`/`Full`/`lift`, §6 row NP-1: "Define level-one `hgt/dig/Full`; prove the complete
stage-law bank"): the concrete stage VALUE / DIGIT / FULL / LIFT source family at level 1 of
the S2 depth-two tower `s2DepthTwo h2 hq` (CC-2, C130s2), every stage law proved at `i = 1`
in its exact field shape, and the concrete `Ladder.SlotCarrier` these fields produce — the
literal one-level-down mirror of CC-6's level-2 table (C130s6), tied to CC-5's `stageCarrier`
interface (C130st) by the conditional `stageCarrier_*_eq_s2₁` pins below.

## The tables (what they are, and why they are not free)

* **VALUE**: NV-0/NV-1's landed `s2Hgt₁` (C130nv) — the cleared first-augmentation value
  `toZ ((s2Frame h2 hq).stageHeight A) = toZ (suppVal X A 1 2)` at the S2 level-one side
  `(u₁, ℓ₁) = (h, e₁) = (1, 2)`, in E.10's `WithTop ℤ` carrier.  **REUSED, not redefined**
  (the plan row's explicit instruction); its complete value bank is already landed there
  (`s2Hgt₁_zero`, `s2Hgt₁_ne_top`/`s2Hgt₁_ne_top_slot`, `s2Hgt₁_add_ge`, `s2Hgt₁_add_eq`,
  plus the NV-1 universal product `s2Hgt₁_mul`) and is consumed verbatim by the carrier —
  the reuse is pinned by `s2Slot₁_hgt` (`rfl`).
* **DIGIT** `s2Dig₁ A` := `0` at `A = 0`, else `1`.  The `q = 2` collapse APPLIES at level
  one: `|K₁| = Nat.card ((s2DepthTwo h2 hq).fld 1) = 2` — the tower's residue tower is
  CONSTANT (C.97's witness), so `fld 1` is definitionally the frame's stage field and the
  card fact IS C.80's landed `card_K₁` (`s2Fld₁_card`, definitional).  Hence `K₁^× = {1}`
  and EVERY lawful digit table is FORCED to this one on the slot range — `s2Dig₁_forced`,
  the "free tables" defense, exactly as at level 2.  Off slot range the value `1` is a junk
  extension no law and no future slot tie reads.
* **FULL** `S2Full₁ k` := `k` is realized by a nonzero slot-range polynomial (the maximal
  honest instance of `EFF.T2.09`'s predicate, as at CC-6).  At level one the characterization
  is COMPLETE: `S2Full₁ k ↔ 0 ≤ k` (`s2Full₁_iff`) — every non-negative `k = 2m + j`
  (`j < 2`) is realized by `2^m·x^j` (degree `j < 2 = Dcum 1`), through NV-1's product law;
  every negative `k` is refuted (`not_s2Full₁_of_neg`, and `s2Full₁_ne_trivial`: the
  predicate is live and source-bound, not `True`).  Named teeth at `0, 1, 2` with explicit
  witnesses `1, x, 2`.
* **LIFT** `s2Lift₁`: at a full height every nonzero digit is realized on slot range.  With
  `|K₁| = 2` the only nonzero digit is `1`, so `(LIFT)`'s content at this instance IS
  realizability — which is what `S2Full₁` certifies; the lift is a theorem, not a
  hypothesis, at this occurrence (same collapse as CC-6's `s2Lift₂`).

## The carrier and the interface tie

`s2Slot₁ : Ladder.SlotCarrier O ((s2DepthTwo h2 hq).fld 1)` packages the family with the
`(DEG-EF)` bookkeeping `D₁ = Dcum 1 = 2 = ê₁·f̂₁ = 2·1` (numeral pins `s2Slot₁_D/eC/fC`).
The `stageCarrier_*_eq_s2₁` ties are CONDITIONAL in the CC-6 style: no `NodePointSource`
instance exists yet (the S2 one is REFUTED as currently typed — U13/SF-0; the corrected
signature is SF-1/SF-2's), so the ties say: any future instance whose stage tables at
`i = 1` are these tables produces, via CC-5's `stageCarrier`, exactly `s2Slot₁` — table for
table (the `D`/`eC`/`fC` ties are unconditional `rfl`s).

## What this node does NOT claim (honesty scope)

* No `NodePointSource` is inhabited; no point fields, no slot ties `slot_value`/`slot_digit`
  (NP-0/NP-2/NP-3), no threshold/WINDOW (NP-4/NP-5), no reads (NP-6..8).
* No level-TWO fact is restated: `s2Hgt₂`/`s2Dig₂`/`S2Full₂`/`s2Slot₂` are CC-6's and
  untouched.
* The digit table is the FORCED one (`s2Dig₁_forced` is the proof it is not a free choice);
  its tie to an actual residual read at legal points is NP-3's (after RP-2), by design.

**DEPENDS.** C130nv (NV-0/NV-1: `s2Hgt₁` + complete value bank + `s2Hgt₁_mul`,
`s2Hgt₁_one/_X/_C_two`) · C130s6 (CC-6: `toZ` dictionary + `toZ_eq_intCast_iff`; the level-2
precedent mirrored) · C130s2 (CC-2: `s2DepthTwo`, `s2DepthTwo_Dcum_one`) · C130st (CC-5:
`stageCarrier` + pins, `fhat`, `Dcum_pos`, `Dcum_eq_ehat_mul_fhat`) · C130k (CC-1:
`NodePointSource`, `StageLive`) · C.80 (`card_K₁`) · C.97 (`s2Frame`, `s2Frame_pin`,
`s2Witness` — the constant residue tower making `s2Fld₁_card` definitional) · C.35b
(`sh_C_pow`) · C.87 (`ehat_pos`) · E.10 (`Ladder.SlotCarrier`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv

universe uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the `q = 2` collapse at level ONE: `|K₁| = 2`

C.97's witness carries a CONSTANT residue tower (`fld := fun _ => stageField`), so
`(s2DepthTwo h2 hq).fld 1` is definitionally the frame's stage field `K₁` and C.80's landed
`card_K₁` types verbatim — the same transport CC-6 used at `fld 2`, one level down. -/

/-- the level-1 residue field of the S2 depth-two tower has exactly two elements — C.80's
landed `card_K₁`, definitionally (`fld 1` IS the frame's stage field: C.97's constant
residue tower). -/
theorem s2Fld₁_card : Nat.card ((s2DepthTwo h2 hq).fld 1) = 2 :=
  C80.card_K₁ h2 hq

/-- private copy of C.80's `eq_one_of_card_two` at `fld 1` (the private-copy pattern of
CC-6's `fld₂_eq_one_of_ne_zero`: `private` does not export). -/
private theorem fld₁_eq_one_of_ne_zero {c : (s2DepthTwo h2 hq).fld 1} (hc : c ≠ 0) :
    c = 1 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 1) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₁_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 1)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₁_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 1)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : ((s2DepthTwo h2 hq).fld 1)ˣ) : (s2DepthTwo h2 hq).fld 1) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- `K₁` has characteristic 2: `1 + 1 = 0`.  This is what makes the level-1 `dig_add` law's
nonzero-sum hypothesis unsatisfiable on nonzero digits (as at level 2). -/
private theorem fld₁_one_add_one :
    (1 : (s2DepthTwo h2 hq).fld 1) + 1 = 0 := by
  by_contra h
  have h1 := fld₁_eq_one_of_ne_zero h2 hq h
  refine one_ne_zero (α := (s2DepthTwo h2 hq).fld 1) ?_
  linear_combination h1

/-! ## Part 2 — the DIGIT table (`EFF.T2.05` at level 1)

The VALUE table is NV-0/NV-1's landed `s2Hgt₁` (C130nv), reused, NOT redefined — its
complete bank (`s2Hgt₁_zero`, `s2Hgt₁_ne_top_slot`, `s2Hgt₁_add_ge`, `s2Hgt₁_add_eq`) is
consumed verbatim by the carrier in Part 4. -/

open Classical in
/-- **the S2 level-1 stage DIGIT table**: `0` at `0`, else `1` — the unique lawful table
over the 2-element `K₁` (see `s2Dig₁_forced`); the value off the slot range is a junk
extension no law and no future slot tie reads. -/
noncomputable def s2Dig₁ (A : Polynomial O) : (s2DepthTwo h2 hq).fld 1 :=
  if A = 0 then 0 else 1

/-- the `dig_zero` SOURCE FIELD at `i = 1` (`EFF.T2.05`: `dig(0) = 0`). -/
theorem s2Dig₁_zero : s2Dig₁ h2 hq (0 : Polynomial O) = 0 := if_pos rfl

/-- the table on nonzero polynomials. -/
theorem s2Dig₁_of_ne_zero {A : Polynomial O} (hA : A ≠ 0) : s2Dig₁ h2 hq A = 1 :=
  if_neg hA

/-- the `dig_ne_zero` SOURCE FIELD at `i = 1`, in its exact `NodePointSource` shape. -/
theorem s2Dig₁_ne_zero :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 1 →
      s2Dig₁ h2 hq A ≠ 0 :=
  fun _ hA _ => by rw [s2Dig₁_of_ne_zero h2 hq hA]; exact one_ne_zero

/-- **the "free tables" defense at level 1** (the plan row's forced-digit uniqueness): over
the 2-element `K₁`, ANY table satisfying the two zero/nonzero digit laws agrees with
`s2Dig₁` on the slot range and at `0` — the digit table is forced, not chosen. -/
theorem s2Dig₁_forced (d : Polynomial O → (s2DepthTwo h2 hq).fld 1)
    (hd0 : d 0 = 0)
    (hdne : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 1 → d A ≠ 0) :
    ∀ A : Polynomial O, A.natDegree < (s2DepthTwo h2 hq).Dcum 1 →
      d A = s2Dig₁ h2 hq A := by
  intro A hdeg
  by_cases hA : A = 0
  · rw [hA, hd0, s2Dig₁_zero]
  · rw [s2Dig₁_of_ne_zero h2 hq hA]
    exact fld₁_eq_one_of_ne_zero h2 hq (hdne A hA hdeg)

/-- the `dig_add` SOURCE FIELD at `i = 1` (`EFF.HE7.96`(c)'s mechanism, the value/digit
compatibility law).  In characteristic 2 with a single nonzero digit, the hypothesis
`dig A + dig B ≠ 0` forces one side to be `0`, whose height is `⊤ ≠ k` — the law holds with
no residual case, exactly as at level 2. -/
theorem s2Dig₁_add (A B : Polynomial O) (k : ℤ)
    (hA : s2Hgt₁ h2 hq A = (k : WithTop ℤ)) (hB : s2Hgt₁ h2 hq B = (k : WithTop ℤ))
    (hne : s2Dig₁ h2 hq A + s2Dig₁ h2 hq B ≠ 0) :
    s2Hgt₁ h2 hq (A + B) = (k : WithTop ℤ) ∧
      s2Dig₁ h2 hq (A + B) = s2Dig₁ h2 hq A + s2Dig₁ h2 hq B := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [s2Hgt₁_zero h2 hq] at hA
    exact WithTop.top_ne_coe hA
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [s2Hgt₁_zero h2 hq] at hB
    exact WithTop.top_ne_coe hB
  refine absurd ?_ hne
  rw [s2Dig₁_of_ne_zero h2 hq hA0, s2Dig₁_of_ne_zero h2 hq hB0, fld₁_one_add_one h2 hq]

/-! ## Part 3 — the FULL predicate and the LIFT law (`EFF.T2.09` at level 1) -/

/-- **the S2 level-1 FULL predicate**: `k` is realized by a nonzero slot-range polynomial —
the maximal honest instance of `EFF.T2.09`'s predicate, as at CC-6.  Live and source-bound,
NOT `True` (see `not_s2Full₁_of_neg` / `s2Full₁_ne_trivial`); at level one the
characterization is COMPLETE (`s2Full₁_iff`). -/
def S2Full₁ (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthTwo h2 hq).Dcum 1 ∧
    s2Hgt₁ h2 hq A = (k : WithTop ℤ)

/-- the `lift` SOURCE FIELD at `i = 1` (`EFF.T2.09` `(LIFT)`): with `|K₁| = 2` the only
nonzero digit is `1`, so realizability of the height IS the lift. -/
theorem s2Lift₁ (k : ℤ) (hk : S2Full₁ h2 hq k) (c : (s2DepthTwo h2 hq).fld 1)
    (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthTwo h2 hq).Dcum 1 ∧
      s2Hgt₁ h2 hq A = (k : WithTop ℤ) ∧ s2Dig₁ h2 hq A = c := by
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  exact ⟨A, hA0, hdeg, hgtA, by
    rw [s2Dig₁_of_ne_zero h2 hq hA0, fld₁_eq_one_of_ne_zero h2 hq hc]⟩

/-! ### 3a. Teeth — `Full` is live, with the COMPLETE level-one characterization

The witnesses are the S2 level-one ladder read off C130nv's teeth: `h₁(1) = 0`,
`h₁(x) = 1` (the cleared `v₁(x) = 1/2`), `h₁(2) = 2` (the cleared `v(2) = 1`); the general
non-negative height `k = 2m + j` (`j < 2`) is realized by `2^m·x^j` through NV-1's product
law.  Negatives are refuted: the table's heights are casts of naturals. -/

/-- **tooth (value, general powers of the uniformizer)**: `h₁(2^m) = 2m` — C35b's
`sh_C_pow` through the carrier dictionary; the witness engine of `s2Full₁_iff`. -/
theorem s2Hgt₁_C_two_pow (m : ℕ) :
    s2Hgt₁ h2 hq (Polynomial.C ((2 : O) ^ m)) = (((2 * m : ℕ) : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₁_eq_stageHeight, C35b.sh_C_pow h2 hq m, toZ_coe]

/-- **tooth (Full)**: `0` is full, witnessed by `1`. -/
theorem s2Full₁_zero : S2Full₁ h2 hq (0 : ℤ) :=
  ⟨1, one_ne_zero,
    by rw [Polynomial.natDegree_one, s2DepthTwo_Dcum_one h2 hq]; norm_num,
    by rw [s2Hgt₁_one h2 hq]⟩

/-- **tooth (Full)**: `1 = u₁` is full, witnessed by `x` (the level-one key input — the
table sees the frame height `h = 1`). -/
theorem s2Full₁_one : S2Full₁ h2 hq (1 : ℤ) :=
  ⟨Polynomial.X, Polynomial.X_ne_zero,
    by rw [Polynomial.natDegree_X, s2DepthTwo_Dcum_one h2 hq]; norm_num,
    by rw [s2Hgt₁_X h2 hq]⟩

/-- **tooth (Full)**: `2` is full, witnessed by the uniformizer `2` (the cleared
`v(2) = 1`). -/
theorem s2Full₁_two : S2Full₁ h2 hq (2 : ℤ) :=
  ⟨Polynomial.C (2 : O), by
      rw [ne_eq, Polynomial.C_eq_zero]
      exact h2.ne_zero,
    by rw [Polynomial.natDegree_C, s2DepthTwo_Dcum_one h2 hq]; norm_num,
    by rw [s2Hgt₁_C_two h2 hq]⟩

/-- ★ **the COMPLETE level-one fullness characterization**: `S2Full₁ k ↔ 0 ≤ k`.  Forward:
level-one heights are casts of naturals (the negative refuter).  Backward: `k = 2m + j`
with `j < 2` is realized by the slot-range witness `2^m·x^j`, through NV-1's universal
product law `s2Hgt₁_mul`.  (No such complete characterization is available one level up —
CC-6's `S2Full₂` carries teeth and refuters only; this is the level-one table's bonus.) -/
theorem s2Full₁_iff {k : ℤ} : S2Full₁ h2 hq k ↔ 0 ≤ k := by
  constructor
  · rintro ⟨A, _hA0, _hdeg, hgtA⟩
    rw [s2Hgt₁_eq_stageHeight] at hgtA
    obtain ⟨n, _hxn, hnk⟩ := toZ_eq_intCast_iff.mp hgtA
    omega
  · intro hk
    have hn : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
    rcases Nat.even_or_odd k.toNat with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨Polynomial.C ((2 : O) ^ m),
        Polynomial.C_ne_zero.mpr (pow_ne_zero m h2.ne_zero), ?_, ?_⟩
      · rw [Polynomial.natDegree_C, s2DepthTwo_Dcum_one h2 hq]; norm_num
      · have h2m : ((2 * m : ℕ) : ℤ) = k := by omega
        rw [s2Hgt₁_C_two_pow h2 hq m, h2m]
    · refine ⟨Polynomial.C ((2 : O) ^ m) * Polynomial.X,
        mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero m h2.ne_zero))
          Polynomial.X_ne_zero, ?_, ?_⟩
      · rw [Polynomial.natDegree_C_mul_X _ (pow_ne_zero m h2.ne_zero),
          s2DepthTwo_Dcum_one h2 hq]
        norm_num
      · have h2m : (((2 * m : ℕ) : ℤ) + 1 : ℤ) = k := by omega
        rw [s2Hgt₁_mul h2 hq, s2Hgt₁_C_two_pow h2 hq m, s2Hgt₁_X h2 hq,
          ← WithTop.coe_add, h2m]

/-- **tooth (Full, negative)**: no negative height is full — the level-one heights are
casts of naturals (the forward half of `s2Full₁_iff`). -/
theorem not_s2Full₁_of_neg {k : ℤ} (hk : k < 0) : ¬ S2Full₁ h2 hq k := fun h =>
  absurd ((s2Full₁_iff h2 hq).mp h) (not_le.mpr hk)

/-- **tooth (Full, non-vacuity)**: the predicate is NOT `True` (design §8 row C.130c's
demand, at level 1). -/
theorem s2Full₁_ne_trivial : S2Full₁ h2 hq ≠ fun _ => True := by
  intro h
  exact not_s2Full₁_of_neg h2 hq (show (-1 : ℤ) < 0 by norm_num)
    (show S2Full₁ h2 hq (-1) by rw [h]; trivial)

/-! ## Part 4 — the concrete `SlotCarrier` at S2 level 1 — `stageCarrier`'s literal image -/

/-- ★ **NODE NP-1 — the concrete E.10 `SlotCarrier` at the S2 level-1 occurrence.**
Field for field the image CC-5's `stageCarrier` produces at `i = 1` from a
`NodePointSource` whose stage tables are the ones above (the `stageCarrier_*_eq_s2₁` ties
pin this): `D = Dcum 1 = 2`, `(eC, fC) = (ê₁, f̂₁) = (2, 1)` with the PROVED `(DEG-EF)`
split (C130st), the REUSED NV-0/NV-1 VALUE table `s2Hgt₁` with its landed law bank
(C130nv, consumed verbatim — no fresh table), and this file's DIGIT/FULL/LIFT family with
every law proved — no hypothesis, no socket, no `True` field. -/
noncomputable def s2Slot₁ : Ladder.SlotCarrier O ((s2DepthTwo h2 hq).fld 1) where
  D := (s2DepthTwo h2 hq).Dcum 1
  hD := (s2DepthTwo h2 hq).Dcum_pos one_le_two
  eC := (s2DepthTwo h2 hq).ehat 1
  fC := (s2DepthTwo h2 hq).fhat 1
  hef := (s2DepthTwo h2 hq).Dcum_eq_ehat_mul_fhat 1
  heC := (s2DepthTwo h2 hq).ehat_pos one_le_two
  hfC := (s2DepthTwo h2 hq).fhat_pos one_le_two
  hgt := s2Hgt₁ h2 hq
  dig := s2Dig₁ h2 hq
  hgt_zero := s2Hgt₁_zero h2 hq
  dig_zero := s2Dig₁_zero h2 hq
  hgt_ne_top := s2Hgt₁_ne_top_slot h2 hq
  dig_ne_zero := s2Dig₁_ne_zero h2 hq
  hgt_add_ge := s2Hgt₁_add_ge h2 hq
  hgt_add_eq := s2Hgt₁_add_eq h2 hq
  dig_add := s2Dig₁_add h2 hq
  Full := S2Full₁ h2 hq
  hlift := s2Lift₁ h2 hq

/-- numeral pin: `D = 2` (C130s2's landed `Dcum` value — the row's named input
`s2DepthTwo_Dcum_one`). -/
theorem s2Slot₁_D : (s2Slot₁ h2 hq).D = 2 := s2DepthTwo_Dcum_one h2 hq

/-- numeral pin: `eC = ê₁ = 2`. -/
theorem s2Slot₁_eC : (s2Slot₁ h2 hq).eC = 2 := by
  change ∏ _j ∈ Finset.Icc 1 1, (2 : ℕ) = 2
  decide

/-- numeral pin: `fC = f̂₁ = 1`. -/
theorem s2Slot₁_fC : (s2Slot₁ h2 hq).fC = 1 := by
  change ∏ _j ∈ Finset.Icc 1 1, (1 : ℕ) = 1
  decide

/-- anti-drift pin (the REUSE pin): the carrier's value table IS NV-0/NV-1's landed
`s2Hgt₁` — reused, not redefined. -/
theorem s2Slot₁_hgt : (s2Slot₁ h2 hq).hgt = s2Hgt₁ h2 hq := rfl

/-- anti-drift pin: the carrier's digit table IS the level-1 source table. -/
theorem s2Slot₁_dig : (s2Slot₁ h2 hq).dig = s2Dig₁ h2 hq := rfl

/-- anti-drift pin: the carrier's `Full` IS the live level-1 predicate — not `True`. -/
theorem s2Slot₁_Full : (s2Slot₁ h2 hq).Full = S2Full₁ h2 hq := rfl

/-! ## Part 5 — the `stageCarrier` ties at `i = 1` (the "via CC-5" clause, honestly
conditional)

`stageCarrier` consumes a FULL `NodePointSource`, which no landed object inhabits (and the
present S2 signature is uninhabitable — U13; the corrected signature is SF-1/SF-2's).  What
IS provable now, exactly as at CC-6: the `D`/`eC`/`fC` fields of `stageCarrier` at `i = 1`
over `s2DepthTwo` equal `s2Slot₁`'s unconditionally (`rfl` — same tower bookkeeping), and
any instance whose stage tables at `i = 1` are this file's tables produces EXACTLY
`s2Slot₁`'s tables through `stageCarrier` (CC-5's own `rfl` pins make the proofs the
hypotheses themselves). -/

section StageCarrierTies

variable {Kt : Type} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2
  (s2DepthTwo h2 hq) Kt}
variable {K : KeyChain (s2DepthTwo h2 hq)}

/-- tie (unconditional): `stageCarrier`'s degree field at the S2 level 1 is `s2Slot₁`'s. -/
theorem stageCarrier_D_eq_s2₁
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 1) :
    (S.stageCarrier 1 hi).D = (s2Slot₁ h2 hq).D := rfl

/-- tie (unconditional): `stageCarrier`'s `(DEG-EF)` constants at the S2 level 1 are
`s2Slot₁`'s. -/
theorem stageCarrier_eC_fC_eq_s2₁
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 1) :
    (S.stageCarrier 1 hi).eC = (s2Slot₁ h2 hq).eC ∧
      (S.stageCarrier 1 hi).fC = (s2Slot₁ h2 hq).fC :=
  ⟨rfl, rfl⟩

/-- tie (conditional on the value table): an instance carrying the REUSED NV-0/NV-1 VALUE
table produces `s2Slot₁`'s height table through `stageCarrier`. -/
theorem stageCarrier_hgt_eq_s2₁
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 1)
    (hS : S.hgt 1 = s2Hgt₁ h2 hq) :
    (S.stageCarrier 1 hi).hgt = (s2Slot₁ h2 hq).hgt := hS

/-- tie (conditional on the digit table): an instance carrying this file's DIGIT table
produces `s2Slot₁`'s digit table through `stageCarrier`. -/
theorem stageCarrier_dig_eq_s2₁
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 1)
    (hS : S.dig 1 = s2Dig₁ h2 hq) :
    (S.stageCarrier 1 hi).dig = (s2Slot₁ h2 hq).dig := hS

/-- tie (conditional on the FULL predicate): an instance carrying this file's FULL
predicate produces `s2Slot₁`'s through `stageCarrier`. -/
theorem stageCarrier_Full_eq_s2₁
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 1)
    (hS : S.Full 1 = S2Full₁ h2 hq) :
    (S.stageCarrier 1 hi).Full = (s2Slot₁ h2 hq).Full := hS

end StageCarrierTies

end Uniformity.Density.Tower.C130np1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np1.s2Fld₁_card
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁_zero
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁_of_ne_zero
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁_ne_zero
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁_forced
#print axioms Uniformity.Density.Tower.C130np1.s2Dig₁_add
#print axioms Uniformity.Density.Tower.C130np1.S2Full₁
#print axioms Uniformity.Density.Tower.C130np1.s2Lift₁
#print axioms Uniformity.Density.Tower.C130np1.s2Hgt₁_C_two_pow
#print axioms Uniformity.Density.Tower.C130np1.s2Full₁_zero
#print axioms Uniformity.Density.Tower.C130np1.s2Full₁_one
#print axioms Uniformity.Density.Tower.C130np1.s2Full₁_two
#print axioms Uniformity.Density.Tower.C130np1.s2Full₁_iff
#print axioms Uniformity.Density.Tower.C130np1.not_s2Full₁_of_neg
#print axioms Uniformity.Density.Tower.C130np1.s2Full₁_ne_trivial
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_D
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_eC
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_fC
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_hgt
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_dig
#print axioms Uniformity.Density.Tower.C130np1.s2Slot₁_Full
#print axioms Uniformity.Density.Tower.C130np1.stageCarrier_D_eq_s2₁
#print axioms Uniformity.Density.Tower.C130np1.stageCarrier_eC_fC_eq_s2₁
#print axioms Uniformity.Density.Tower.C130np1.stageCarrier_hgt_eq_s2₁
#print axioms Uniformity.Density.Tower.C130np1.stageCarrier_dig_eq_s2₁
#print axioms Uniformity.Density.Tower.C130np1.stageCarrier_Full_eq_s2₁

end AxCheck
