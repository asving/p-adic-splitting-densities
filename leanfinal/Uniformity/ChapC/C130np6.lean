/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130s17

/-!
# Uniformity.ChapC.C130np6 — S2-source plan node NP-6

**S2-source plan node NP-6** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row NP-6:
"Construct `ambientLetter`, `psi_root`, and `letter_ne_zero` by live-index computation"): the
concrete residue-ambient letter data for the S2 depth-two tower `s2DepthTwo h2 hq` (CC-2,
C130s2), in the exact field shapes of SF1's re-typed `SplitNodePointSource.ambientLetter` /
`.psi_root` (C130s17) and of `FGMNSourceLaws.letter_ne_zero` (C130fg).

## Why the letters collapse to `1` at S2 — two DIFFERENT reasons for two DIFFERENT objects

Bridged via `s2Bridge_ψ` (C130s2), the depth-two witness's live residual is
`(s2DepthTwo h2 hq).ψ 1 = (s2Tower h2 hq).ψ₂ = X − C 1` (C.80's landed tower datum) — a
DEGREE-ONE polynomial whose unique root, in ANY ring whatsoever, is `1`.  Hence:

* **`ambientLetter`** (residue ambient `L`, any field with `[Algebra Kt L]`): the unit
  `1 : Lˣ` is a root of the transported `ψ` at the gauge-live index `i = 1` (`GaugeLive 2 i
  ↔ i = 1`).  No appeal to `|K₂| = 2` is needed for THIS half — `ψ = X − C 1` has the root
  `1` over every ring, because a ring hom fixes `1`.  This is `s2AmbientLetter`/`s2_psi_root`
  below, tied to CC-9's named receiver-level objects (`TerminalReceiver.ambientHom`,
  `.psiTransported`, `.psiTransported_root_ne_zero`, C130pt) by instantiation, not
  duplication.
* **`letter`** (the `FGMNSourceData` residue letter, valued in the ACTUAL 2-element field
  `(s2DepthTwo h2 hq).fld 2` — `s2Fld₂_card`, C130s6): here the collapse runs the OTHER
  way.  `letter_ne_zero`'s conclusion is only `≠ 0`, and the 2-element field forces EVERY
  nonzero candidate to equal `1` (`s2Letter_forced`, the "free letters" defense in the
  style of C130s6's `s2Dig₂_forced` / C130np1's `s2Dig₁_forced`) — so the concrete choice
  `s2Letter := 1` is not a convenience, it is the ONLY admissible nonzero value.

## What this node does NOT deliver (named per plan row)

No `FGMNSourceData`/`FGMNSourceLaws` instance is assembled (that is FD-0, after the RP-*/KP-*
residual cores); this node supplies exactly the three named field values/proofs, ready for
that later assembly.  No `canonicalRead`/`arenaRead`/`towerRead`/`peelUnit` (NP-7/NP-8).  No
`SplitNodePointSource` instance is claimed inhabited.

**DEPENDS.** C130s17 (`SplitNodePointSource` — the target field shapes for `ambientLetter`/
`psi_root`; `s2TerminalReceiver`, `S2DepthTwo`, `s2RepositoryRealization`) · C130pt (CC-9:
`TerminalReceiver.ambientHom`, `.ambientHom_def`, `.psiTransported`, `.psiTransported_def`,
`.psiTransported_root_ne_zero` — reused verbatim, not duplicated) · C130s2 (CC-2:
`s2Bridge_ψ`) · C.80 (`s2Tower`'s literal `ψ₂ := X − C 1`, transitively via C130s2) ·
C130s6 (CC-6: `s2Fld₂_card`) · C130fg (`FGMNSourceLaws.letter_ne_zero`'s exact field shape,
read only, not imported — no `FGMNSourceData`/`FGMNSourceLaws` instance is touched here).

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17

universe uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. The residue-ambient letter — `ambientLetter` and `psi_root` -/

section AmbientLetter

/-- Only the gauge-live index of a depth-two tower is `1` (`GaugeLive r j := 1 ≤ j ∧ j <
r`, C130a) — the index range `psi_root` quantifies over. -/
theorem gaugeLive_two_iff {i : ℕ} : GaugeLive 2 i ↔ i = 1 := by
  constructor
  · rintro ⟨h1, hlt⟩; omega
  · rintro rfl; exact ⟨le_rfl, by omega⟩

variable (L : Type uL) [Field L]

/-- **the `ambientLetter` field, live-index construction**: the unit `1`, at every index.
The only index `psi_root` constrains is the gauge-live `i = 1`; there `ψ 1 = X − C 1`
(`s2Bridge_ψ`) has the unique root `1` in `L`, for ANY field `L` whatsoever — no appeal to
the residue-field cardinality is needed for this half.  Off the constrained index the
value is a total-function convenience, exactly like C130s2's junk `keyAt` indices: no law
reads it. -/
noncomputable def s2AmbientLetter : ℕ → Lˣ := fun _ => 1

/-- Anti-drift pin: the ambient letter's `L`-value is `1`, at every index. -/
theorem s2AmbientLetter_coe (i : ℕ) : (s2AmbientLetter L i : L) = 1 := rfl

variable {h2 hq}

/-- the live residual at the gauge-live index is `X − C 1` (`s2Bridge_ψ`, C130s2, composed
with C.80's literal tower datum `ψ₂ := X − C 1`). -/
theorem s2_psi_one : (S2DepthTwo h2 hq).ψ 1 = Polynomial.X - Polynomial.C 1 :=
  s2Bridge_ψ h2 hq

variable {Kt : Type} [Field Kt] [Algebra Kt L]
  (receiver : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 (S2DepthTwo h2 hq) Kt)

/-- ★ **the `psi_root` field, exact shape**: the ambient letter is a root of the ambient
transport of the live residual, at every gauge-live index — `ψ 1 = X − C 1` evaluates to
`1 − φ(1) = 0` at the unit letter `1`, for the ambient transport `φ = (algebraMap Kt
L).comp (receiver.levelHom i)` of ANY receiver, ANY `Kt`, and ANY field `L` (ring homs fix
`1`). -/
theorem s2_psi_root :
    ∀ i, GaugeLive 2 i →
      Polynomial.eval₂ ((algebraMap Kt L).comp (receiver.levelHom i))
        (s2AmbientLetter L i : L) ((S2DepthTwo h2 hq).ψ i) = 0 := by
  intro i hi
  obtain rfl := gaugeLive_two_iff.mp hi
  have hφ : ((algebraMap Kt L).comp (receiver.levelHom 1)) 1 = 1 := map_one _
  rw [s2_psi_one, s2AmbientLetter_coe, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, hφ, sub_self]

/-- tied to CC-9's named receiver-level object (`TerminalReceiver.ambientHom`, C130pt): the
exact SAME fact, restated through `ambientHom` rather than its unfolded
`algebraMap.comp levelHom` definition — an instantiation of CC-9's transport, not a
duplicate of it. -/
theorem s2_psi_root_ambientHom :
    ∀ i, GaugeLive 2 i →
      Polynomial.eval₂ (receiver.ambientHom (L := L) i)
        (s2AmbientLetter L i : L) ((S2DepthTwo h2 hq).ψ i) = 0 := by
  intro i hi
  rw [receiver.ambientHom_def (L := L) i]
  exact s2_psi_root L receiver i hi

/-- ★ tied to CC-9's named transported polynomial (`TerminalReceiver.psiTransported`,
C130pt): the ambient letter, at the gauge-live index, is a root of `psiTransported` — an
instantiation of the general receiver-level object at the S2 numerals, not a duplicate of
it. -/
theorem s2AmbientLetter_isRoot {i : ℕ} (hi : GaugeLive 2 i) :
    (receiver.psiTransported (L := L) i).IsRoot (s2AmbientLetter L i : L) := by
  show (((S2DepthTwo h2 hq).ψ i).map (receiver.ambientHom (L := L) i)).eval
      (s2AmbientLetter L i : L) = 0
  rw [Polynomial.eval_map]
  exact s2_psi_root_ambientHom L receiver i hi

include receiver in
/-- ★ **decorrelated cross-check**: the ambient letter's nonzeroness, derived from CC-9's
FORCING theorem `psiTransported_root_ne_zero` (freeze v2 §4's `Lˣ`-forcing theorem) rather
than read off the `Lˣ` codomain (`Units.ne_zero`) — an independent route to the same fact,
through the root law alone. -/
theorem s2AmbientLetter_ne_zero_forced {i : ℕ} (hi : GaugeLive 2 i) :
    (s2AmbientLetter L i : L) ≠ 0 :=
  TerminalReceiver.psiTransported_root_ne_zero receiver (L := L) hi
    (s2AmbientLetter_isRoot L receiver hi)

end AmbientLetter

/-! ## 2. The FGMN residue letter — `letter_ne_zero` -/

section Letter

/-- private copy of C.80's `eq_one_of_card_two` at `fld 2` (the private-copy pattern of
C130s6's `fld₂_eq_one_of_ne_zero` / C130np1's `fld₁_eq_one_of_ne_zero`: `private` does not
export). -/
private theorem np6_fld₂_eq_one_of_ne_zero {c : (S2DepthTwo h2 hq).fld 2} (hc : c ≠ 0) :
    c = 1 := by
  haveI : Finite ((S2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((S2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((S2DepthTwo h2 hq).fld 2)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : ((S2DepthTwo h2 hq).fld 2)ˣ) : (S2DepthTwo h2 hq).fld 2) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- **the `FGMNSourceData.letter` field, live-index construction**: the constant `1`, at
every index — the unique value the 2-element field `(S2DepthTwo h2 hq).fld 2` admits for a
nonzero letter (`s2Letter_forced` below); junk (never read by `letter_ne_zero`) off the
live range `1 ≤ i ≤ 2`. -/
noncomputable def s2Letter : ℕ → (S2DepthTwo h2 hq).fld 2 := fun _ => 1

/-- ★ **the "free letters" defense**: over the 2-element `(S2DepthTwo h2 hq).fld 2`, ANY
candidate letter function satisfying the `letter_ne_zero` nonzero law on the live range
`1 ≤ i ≤ 2` agrees with `s2Letter` there — the value is FORCED, not chosen (mirror of
C130s6's `s2Dig₂_forced` / C130np1's `s2Dig₁_forced`). -/
theorem s2Letter_forced (ℓ : ℕ → (S2DepthTwo h2 hq).fld 2)
    (hne : ∀ i, 1 ≤ i → i ≤ 2 → ℓ i ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ 2 → ℓ i = s2Letter h2 hq i :=
  fun i h1 hi2 => np6_fld₂_eq_one_of_ne_zero h2 hq (hne i h1 hi2)

/-- ★ **the `letter_ne_zero` field, exact shape** (`FGMNSourceLaws.letter_ne_zero`,
C130fg, at `r = 2`): both live indices `1 ≤ i ≤ 2` — `s2Letter` is the constant `1`, and
`(1 : (S2DepthTwo h2 hq).fld 2) ≠ 0` is `one_ne_zero`, a fact of ANY field regardless of
cardinality (the live-index range is what the `fin_cases`-adjacent computation checks: it
is exactly `{1, 2}`, both covered by the same constant value). -/
theorem s2Letter_ne_zero : ∀ i, 1 ≤ i → i ≤ 2 → s2Letter h2 hq i ≠ 0 :=
  fun _ _ _ => one_ne_zero

end Letter

end Uniformity.Density.Tower.C130np6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np6.gaugeLive_two_iff
#print axioms Uniformity.Density.Tower.C130np6.s2AmbientLetter
#print axioms Uniformity.Density.Tower.C130np6.s2AmbientLetter_coe
#print axioms Uniformity.Density.Tower.C130np6.s2_psi_one
#print axioms Uniformity.Density.Tower.C130np6.s2_psi_root
#print axioms Uniformity.Density.Tower.C130np6.s2_psi_root_ambientHom
#print axioms Uniformity.Density.Tower.C130np6.s2AmbientLetter_isRoot
#print axioms Uniformity.Density.Tower.C130np6.s2AmbientLetter_ne_zero_forced
#print axioms Uniformity.Density.Tower.C130np6.s2Letter
#print axioms Uniformity.Density.Tower.C130np6.s2Letter_forced
#print axioms Uniformity.Density.Tower.C130np6.s2Letter_ne_zero

end AxCheck
