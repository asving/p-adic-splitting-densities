/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130np1
import Uniformity.ChapC.C130np0
import Uniformity.ChapC.C130rp2

/-!
# Uniformity.ChapC.C130np3 — S2-source plan node NP-3

**S2-source plan node NP-3** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row NP-3:
"Prove `slot_digit` and `dig_add` from actual residual reads, not a free copy"): construct
`pointDig` (left undefined by NP-0 — see its "What this node does NOT deliver" list) and
prove `slot_digit` at both S2 live levels from RP-2's actual ϖ-reads, plus a point-level
digit-additivity fact built from RP-2's `twistRead_add_of_le` engine.

## The construction (not a free copy)

`pointDig i x A` is read off `A` itself via the SAME development/side machinery NV-2/NV-3
built for `pointHgt` (C130np0), one level down: for `A ≠ 0`, `dvSideMin (s2Frame h2 hq) A u ℓ`
picks the on-side development index `j` (C.07), `dev (s2Frame h2 hq).key A j` is the
resulting short (`natDegree ≤ 1`) coefficient (B.02/B.03), and RP-2's S2 ϖ-read normal form
`s2_twistRead_eq_digAt` reads a genuine residue digit off it at the on-line height. The
`(u, ℓ)` side is `(5, 1)` at `i ≤ 1` (mirroring NP-0's stage-1 augmentation `s2PHgt₁`) and
`(5, 2)` at `i ≥ 2` (mirroring CC-6's terminal table `s2Hgt₂`) — `s2NPPointDigAux` is the one
shared construction, instantiated at both sides exactly as NP-0's `s2NPValuation` instantiates
its two `AddValuation`s.

## The one genuine design finding: the read is UNFENCED, and forced

`dev (s2Frame h2 hq).key A j` is **always** of `natDegree ≤ 1` regardless of `A`'s own degree
(`degree_dev_lt`), and its stage height is finite (hence it is nonzero) exactly when `A ≠ 0`
(the on-side finiteness guard, C.07). So the leading-digit lemma `s2_leadDigit_ne_zero` — the
digit read at a *short* nonzero polynomial's own height is never zero (B.22's
`digAt_eq_zero_iff` at the exact valuation, transported through the two field
`algebraMap`s, both injective as maps out of a field, `RingHom.injective`) — applies to
`s2NPPointDigAux h2 hq u ℓ _ A` for **every** `A ≠ 0`, not just slot-range `A`. Since
`(s2DepthTwo h2 hq).fld i` has exactly two elements at both live levels (C.80's `card_K₁`,
transported), a nonzero read there IS `1`. Hence `s2NPPointDig` agrees with the intended
table `s2Dig₁`/`s2Dig₂` **UNFENCED** (`s2NPPointDig_eq_s2Dig₁`/`s2NPPointDig_eq_s2Dig₂`,
∀ `A`, not just slot range) — strictly stronger than the `slot_digit` field shape, exactly the
pattern NP-0 found for `pointHgt`'s two dictionaries.

## `dig_add` at the point level

`s2_twistRead_dev_add_of_le`: at a **common** floor `m` on a **shared** on-side slot `j` for
`A` and `B`, the digit read of `A + B` is the sum of the digit reads of `A` and `B` — `dev`
additivity (B32a's `dev_add_of_monic`) composed with RP-2's engine
(`twistRead_add_of_le`), verbatim. This is the point-level analogue of the table's `dig_add`
field (already discharged at NP-1/CC-6): the read, not merely the table, is additive at a
common height. No claim is made that two *different* polynomials' own `dvSideMin`s coincide
in general (they need not); the common-slot hypothesis is exactly RP-2's `s2GradedCoeff_add`
proof pattern, transplanted to the point read.

## What this node does NOT claim (honesty scope)

* No `NodePointSource`/`S2SourceFrontier` instance is assembled — that is SG-0, after every
  NP/RP/KP/FD node lands (this file touches none of them).
* `s2_twistRead_dev_add_of_le` is stated for a shared on-side slot `j`; it does not resolve
  whether two arbitrary polynomials' `dvSideMin`s coincide (they need not — no claim is made
  either way).
* The threshold/window fields (NP-4/NP-5, already landed independently), the letters/reads
  (NP-6/NP-7/NP-8, already landed independently) are untouched.

**DEPENDS.** C130np0 (`S2NPPoint`, the point-independence pattern) · C130np1 (`s2Dig₁` +
bank) · C130s6 (`s2Dig₂` + bank, `dvSupp`/`toZ` dictionary) · C130rp2 (`twistRead_add_of_le`,
`twistRead_eq_zero_of_lt`, `s2_twistRead_eq_digAt`, `slotRes`/`twistRead` bank) · C130nv2/nv3
(`dvSideMin`, `dvOnSide_dvSideMin`, generic endpoint bank) · C.06/C.07 (`dvHgt`, `dvSideSet`,
`DvOnSide`) · C.34 (`dvSideSet_nonempty`) · C35b (frame numerals) · C.80 (`card_K₁`) · C.97
(`s2Frame_pin`, `s2StageFieldInst`) · B.02/B.03 (`dev`, `degree_dev_lt`) · B32a
(`dev_add_of_monic`) · B.21/B.22 (`digAt`, `digAt_eq_zero_iff`) · mathlib
(`IsDiscreteValuationRing.addVal_le_iff_dvd`, `Irreducible.addVal_pow`, `ENat.toNat`,
`ENat.coe_toNat`, `RingHom.injective`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched; new
file only — no other unit's file edited.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C130np0 Uniformity.Density.Tower.C130np1
open Uniformity.Density.Tower.C130rp2

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — small ℕ∞ arithmetic helpers (private-copy pattern) -/

/-- an even-side EXACT floor: `(a:ℕ∞) = 2 • x` forces `x` finite with `a = 2·(the witness)`. -/
private theorem coe_eq_of_two_smul_eq {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) = 2 • x) :
    ∃ b : ℕ, x = (b : ℕ∞) ∧ a = 2 * b := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at h
    exact absurd h (ENat.coe_ne_top a)
  · obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hx
    refine ⟨b, hb.symm, ?_⟩
    rw [← hb, show (2 : ℕ) • ((b : ℕ) : ℕ∞) = ((2 * b : ℕ) : ℕ∞) by
      rw [nsmul_eq_mul]; push_cast; ring] at h
    exact_mod_cast h

/-- an odd-side EXACT floor: `(a:ℕ∞) = 2 • x + 1` forces `x` finite with `a = 2·(witness)+1`. -/
private theorem coe_eq_of_two_smul_add_one_eq {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) = 2 • x + 1) :
    ∃ b : ℕ, x = (b : ℕ∞) ∧ a = 2 * b + 1 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add] at h
    exact absurd h (ENat.coe_ne_top a)
  · obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hx
    refine ⟨b, hb.symm, ?_⟩
    rw [← hb, show (2 : ℕ) • ((b : ℕ) : ℕ∞) + 1 = ((2 * b + 1 : ℕ) : ℕ∞) by
      rw [nsmul_eq_mul]; push_cast; ring] at h
    exact_mod_cast h

/-- `π^k ∣ x` from a valuation floor (private-copy pattern: C131y/C131ae/C.26/RP-2). -/
private theorem dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

/-- **the leading-digit nonvanishing**: the digit read at an element's OWN exact valuation is
never zero (B.22's `digAt_eq_zero_iff`, the exactness half). -/
private theorem digAt_ne_zero_of_addVal_eq (hπ : Irreducible π) {c : O} {a : ℕ}
    (ha : addVal O c = (a : ℕ∞)) : digAt π a c ≠ 0 := by
  have hdvd : π ^ a ∣ c := dvd_of_le_addVal hπ (le_of_eq ha.symm)
  intro hz
  rw [digAt_eq_zero_iff hπ hdvd] at hz
  have hle : ((a + 1 : ℕ) : ℕ∞) ≤ addVal O c := by
    rw [← hπ.addVal_pow (a + 1)]
    exact addVal_le_iff_dvd.mpr hz
  rw [ha] at hle
  have : a + 1 ≤ a := by exact_mod_cast hle
  omega

/-- a ring hom out of a nonzero-argument stays nonzero (both maps below are field
homomorphisms, hence injective, `RingHom.injective`). -/
private theorem ne_zero_of_ringHom_ne_zero {A B : Type*} [Semiring A] [Semiring B]
    {f : A →+* B} (hf : Function.Injective f) {x : A} (hx : x ≠ 0) : f x ≠ 0 :=
  fun h => hx (hf (h.trans (map_zero f).symm))

/-- in the 2-element S2 stage field, every nonzero element is `1` (private-copy pattern of
NP-1's `fld₁_eq_one_of_ne_zero` / CC-6's `fld₂_eq_one_of_ne_zero`, at the shared stage field
both `fld 1` and `fld 2` reduce to). -/
private theorem eq_one_of_stageField_ne_zero
    {c : (s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)} (hc : c ≠ 0) : c = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  haveI : Finite ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    Nat.finite_of_card_ne_zero (by rw [C80.card_K₁ h2 hq]; norm_num)
  have hu : Nat.card ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))ˣ = 1 := by
    rw [Nat.card_units, C80.card_K₁ h2 hq]
  haveI : Subsingleton ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))ˣ :=
    (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit :
        ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))ˣ) :
        (s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) := (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-! ## Part 1 — the leading-digit lemma: a short nonzero polynomial's read, at its own
height, is nonzero -/

omit [Finite (ResidueField O)] in
/-- the order-0 key `X` is an order-1 key (private-copy pattern of C04's private `isKey_X`,
needed here to name the `Field (resField X)` instance `RingHom.injective` consumes). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- ★ **the leading-digit lemma**: for `w` of `natDegree ≤ 1`, nonzero, the ϖ-read at `w`'s
OWN (finite) stage height is nonzero.  Proof: `s2_stageHeight_linear` names the achieving
coefficient exactly (parity of the height picks `w.coeff 0` or `w.coeff 1`); B.22's
`digAt_eq_zero_iff` at the coefficient's own valuation gives a nonzero digit; both
`algebraMap`s of RP-2's `s2_twistRead_eq_digAt` are field homomorphisms, hence injective. -/
theorem s2_leadDigit_ne_zero {w : Polynomial O} (hw : w.natDegree ≤ 1) (hw0 : w ≠ 0)
    {m : ℕ} (hm : (s2Frame h2 hq).stageHeight w = (m : ℕ∞)) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m w ≠ 0 := by
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  rw [s2_twistRead_eq_digAt h2 hq]
  rw [s2_stageHeight_linear h2 hq hw] at hm
  rcases le_total ((2 : ℕ) • addVal O (w.coeff 0)) ((2 : ℕ) • addVal O (w.coeff 1) + 1)
    with hle | hle
  · rw [min_eq_left hle] at hm
    obtain ⟨a, haval, hmeq⟩ := coe_eq_of_two_smul_eq hm.symm
    have hme : m % 2 = 0 := by omega
    have hmd : m / 2 = a := by omega
    rw [hme, hmd]
    exact ne_zero_of_ringHom_ne_zero (RingHom.injective _)
      (ne_zero_of_ringHom_ne_zero (RingHom.injective _) (digAt_ne_zero_of_addVal_eq h2 haval))
  · rw [min_eq_right hle] at hm
    obtain ⟨b, hbval, hmeq⟩ := coe_eq_of_two_smul_add_one_eq hm.symm
    have hme : m % 2 = 1 := by omega
    have hmd : m / 2 = b := by omega
    rw [hme, hmd]
    exact ne_zero_of_ringHom_ne_zero (RingHom.injective _)
      (ne_zero_of_ringHom_ne_zero (RingHom.injective _) (digAt_ne_zero_of_addVal_eq h2 hbval))

/-! ## Part 2 — `pointDig`'s construction: read `A` off its own on-side development slot -/

/-- **the shared point-digit construction**, at a side `(u, ℓ)`: for `A ≠ 0`, take the
on-side development index `j = dvSideMin A u ℓ` (C.07) and read the ϖ-digit of the short
coefficient `dev key A j` at its own on-line height.  `A = 0` reads `0` (junk-free: it is
literally the digit of the zero coefficient at any height, `twistRead_zero`). -/
noncomputable def s2NPPointDigAux (u ℓ : ℕ) (hℓ : 0 < ℓ) (A : Polynomial O) :
    (s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq) :=
  open Classical in
  if hA0 : A = 0 then 0
  else
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq)
      (ENat.toNat (dvHgt (s2Frame h2 hq) A
        (dvSideMin (s2Frame h2 hq) A u ℓ (dvSideSet_nonempty (s2Frame h2 hq) hA0 u hℓ))))
      (dev (s2Frame h2 hq).key A
        (dvSideMin (s2Frame h2 hq) A u ℓ (dvSideSet_nonempty (s2Frame h2 hq) hA0 u hℓ)))

theorem s2NPPointDigAux_zero (u ℓ : ℕ) (hℓ : 0 < ℓ) :
    s2NPPointDigAux h2 hq u ℓ hℓ (0 : Polynomial O) = 0 := by
  unfold s2NPPointDigAux
  rw [dif_pos rfl]

/-- ★ **the read is nonvanishing for EVERY nonzero `A`** — unfenced in `A`'s degree (the
design finding: `dev key A j` is always short, so the leading-digit lemma applies
regardless of how large `A` itself is). -/
theorem s2NPPointDigAux_ne_zero {u ℓ : ℕ} (hℓ : 0 < ℓ) {A : Polynomial O} (hA0 : A ≠ 0) :
    s2NPPointDigAux h2 hq u ℓ hℓ A ≠ 0 := by
  unfold s2NPPointDigAux
  rw [dif_neg hA0]
  set hne := dvSideSet_nonempty (s2Frame h2 hq) hA0 u hℓ with hne_def
  set j := dvSideMin (s2Frame h2 hq) A u ℓ hne with j_def
  have hOnSide : DvOnSide (s2Frame h2 hq) A u ℓ j := dvOnSide_dvSideMin (s2Frame h2 hq) A u ℓ hne
  have hfin : dvHgt (s2Frame h2 hq) A j ≠ ⊤ := hOnSide.2
  have hw0 : dev (s2Frame h2 hq).key A j ≠ 0 := by
    intro h0
    apply hfin
    show (s2Frame h2 hq).stageHeight (dev (s2Frame h2 hq).key A j) = ⊤
    rw [h0]
    exact (s2Frame h2 hq).stageHeight_zero
  have hkd : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [C35b.key_eq h2 hq]
    exact s2Key_natDegree
  have hwdeg : (dev (s2Frame h2 hq).key A j).natDegree ≤ 1 := by
    have h := natDegree_lt_natDegree hw0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos A j)
    rw [hkd] at h
    omega
  exact s2_leadDigit_ne_zero h2 hq hwdeg hw0 (ENat.coe_toNat hfin).symm

/-- **the ties to the landed tables**, at both sides used by the two live levels: at
`(u, ℓ) = (5, 1)` the read agrees with NP-1's level-one table, at `(5, 2)` with CC-6's
level-two table — UNFENCED (every `A`, not only slot range): `s2Dig₁`/`s2Dig₂` are `0` at `0`
and the unique nonzero element of a 2-element field otherwise, and the read is exactly that
by `s2NPPointDigAux_ne_zero` plus `eq_one_of_stageField_ne_zero`. -/
theorem s2NPPointDigAux_eq_s2Dig₁ (A : Polynomial O) :
    s2NPPointDigAux h2 hq 5 1 (by norm_num) A = s2Dig₁ h2 hq A := by
  by_cases hA0 : A = 0
  · subst hA0
    rw [s2NPPointDigAux_zero h2 hq, s2Dig₁_zero]
    rfl
  · rw [s2Dig₁_of_ne_zero h2 hq hA0]
    exact eq_one_of_stageField_ne_zero h2 hq (s2NPPointDigAux_ne_zero h2 hq (by norm_num) hA0)

theorem s2NPPointDigAux_eq_s2Dig₂ (A : Polynomial O) :
    s2NPPointDigAux h2 hq 5 2 (by norm_num) A = s2Dig₂ h2 hq A := by
  by_cases hA0 : A = 0
  · subst hA0
    rw [s2NPPointDigAux_zero h2 hq, s2Dig₂_zero]
    rfl
  · rw [s2Dig₂_of_ne_zero h2 hq hA0]
    exact eq_one_of_stageField_ne_zero h2 hq (s2NPPointDigAux_ne_zero h2 hq (by norm_num) hA0)

/-! ## Part 3 — `pointDig` at the S2 node, and the intended table -/

/-- **the `pointDig` field, at S2**: point-independent (`S2NPPoint = Unit`, exactly as
NP-0's `pointHgt`), branching on the side per level as NP-0's `s2NPValuation` does. -/
noncomputable def s2NPPointDig (i : ℕ) (_x : S2NPPoint) (A : Polynomial O) :
    (s2DepthTwo h2 hq).fld i :=
  if i ≤ 1 then s2NPPointDigAux h2 hq 5 1 (by norm_num) A
  else s2NPPointDigAux h2 hq 5 2 (by norm_num) A

/-- the intended `dig` table of the future node instance: NP-1's level-one `s2Dig₁` at
`i ≤ 1`, CC-6's level-two `s2Dig₂` at `i ≥ 2` (mirrors NP-0's `s2NPHgt`). -/
noncomputable def s2NPDig (i : ℕ) : Polynomial O → (s2DepthTwo h2 hq).fld i :=
  if i ≤ 1 then s2Dig₁ h2 hq else s2Dig₂ h2 hq

theorem s2NPPointDig_one (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointDig h2 hq 1 x A = s2NPPointDigAux h2 hq 5 1 (by norm_num) A := rfl

theorem s2NPPointDig_two (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointDig h2 hq 2 x A = s2NPPointDigAux h2 hq 5 2 (by norm_num) A := rfl

theorem s2NPDig_one : s2NPDig h2 hq 1 = s2Dig₁ h2 hq := rfl

theorem s2NPDig_two : s2NPDig h2 hq 2 = s2Dig₂ h2 hq := rfl

/-- ★ **the point-read dictionaries, UNFENCED**: at both live levels the point digit read
agrees with the intended table for EVERY `A`, not merely the slot range (strictly stronger
than `slot_digit`'s field shape — exactly the pattern NP-0 found for `pointHgt`). -/
theorem s2NPPointDig_one_eq (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointDig h2 hq 1 x A = s2Dig₁ h2 hq A := by
  rw [s2NPPointDig_one h2 hq]
  exact s2NPPointDigAux_eq_s2Dig₁ h2 hq A

theorem s2NPPointDig_two_eq (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointDig h2 hq 2 x A = s2Dig₂ h2 hq A := by
  rw [s2NPPointDig_two h2 hq]
  exact s2NPPointDigAux_eq_s2Dig₂ h2 hq A

/-! ## Part 4 — ★ NODE NP-3, the `slot_digit` field shape -/

/-- ★ **the `slot_digit` field, exact shape, BOTH live levels**: on the slot range the point
digit read is the intended table — read off `interval_cases` plus the unfenced dictionaries
above. -/
theorem s2NP_slot_digit :
    ∀ i (_hi : StageLive 2 i) (x : S2NPPoint), s2NPPt h2 hq i x →
      ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum i →
        s2NPPointDig h2 hq i x A = s2NPDig h2 hq i A := by
  intro i hi x _hx A _hA0 _hdeg
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · rw [s2NPDig_one h2 hq]
    exact s2NPPointDig_one_eq h2 hq x A
  · rw [s2NPDig_two h2 hq]
    exact s2NPPointDig_two_eq h2 hq x A

/-! ## Part 5 — `dig_add` at the point level, RP-2's `twistRead_add_of_le` as the engine -/

/-- ★ **NODE NP-3, `dig_add` at the point level**: at a COMMON floor `m` on a SHARED on-side
slot `j`, the digit read of `A + B` is the sum of the digit reads of `A` and `B` — `dev`
additivity (B32a) plus RP-2's ϖ-read additivity (`twistRead_add_of_le`), the point-level
analogue of the table's `dig_add` field (already discharged at NP-1/CC-6).  No claim that
two arbitrary polynomials' OWN `dvSideMin`s coincide — the shared-slot hypothesis is exactly
what RP-2's own `s2GradedCoeff_add` consumes, transplanted to the point read. -/
theorem s2_twistRead_dev_add_of_le {A B : Polynomial O} {j m : ℕ}
    (hA : (m : ℕ∞) ≤ dvHgt (s2Frame h2 hq) A j) (hB : (m : ℕ∞) ≤ dvHgt (s2Frame h2 hq) B j) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m (dev (s2Frame h2 hq).key (A + B) j)
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m (dev (s2Frame h2 hq).key A j)
        + (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m (dev (s2Frame h2 hq).key B j) := by
  rw [dev_add_of_monic (s2Frame h2 hq).hmonic]
  exact twistRead_add_of_le (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) hA hB

/-- **tooth**: the point-level additivity is genuinely non-vacuous — at the S2 frame key
itself (`j = 1`, `m = 0`), `X + X = C 2 * X` reads `0 + 0 = 0` through the engine (both
summands read `0` at the constant-slot-clearing height `0`, consistent with `1 + 1 = 0` in
the 2-element field). -/
theorem tooth_twistRead_dev_add :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 0
        (dev (s2Frame h2 hq).key (Polynomial.X + Polynomial.X : Polynomial O) 0)
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 0
          (dev (s2Frame h2 hq).key (Polynomial.X : Polynomial O) 0)
        + (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) 0
            (dev (s2Frame h2 hq).key (Polynomial.X : Polynomial O) 0) := by
  have hh : (0 : ℕ∞) ≤ dvHgt (s2Frame h2 hq) (Polynomial.X : Polynomial O) 0 := zero_le'
  simpa using s2_twistRead_dev_add_of_le h2 hq hh hh

end S2

end Uniformity.Density.Tower.C130np3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np3.s2_leadDigit_ne_zero
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDigAux
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDigAux_zero
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDigAux_ne_zero
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDigAux_eq_s2Dig₁
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDigAux_eq_s2Dig₂
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDig
#print axioms Uniformity.Density.Tower.C130np3.s2NPDig
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDig_one
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDig_two
#print axioms Uniformity.Density.Tower.C130np3.s2NPDig_one
#print axioms Uniformity.Density.Tower.C130np3.s2NPDig_two
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDig_one_eq
#print axioms Uniformity.Density.Tower.C130np3.s2NPPointDig_two_eq
#print axioms Uniformity.Density.Tower.C130np3.s2NP_slot_digit
#print axioms Uniformity.Density.Tower.C130np3.s2_twistRead_dev_add_of_le
#print axioms Uniformity.Density.Tower.C130np3.tooth_twistRead_dev_add

end AxCheck
