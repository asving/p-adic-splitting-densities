/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RungLift4

/-!
# Uniformity.ChapI.I10CalcBridge — UNIT CCT: the carrier→calculus transcription

SPB's named boundary (`runs/wave-c/verdict_SPB.md` §3): "the open leg is the
carrier→CALCULUS transcription (producing `FGMNCalculus` operators + B-1 grades from
`RungPack` data)".  This file lands that transcription — the generic map from the
completed pack chain (RUNG/W3P/R4K) into the A-C.11 hypothesis carrier `FGMNCalculus`
(C130pk), routed through the landed packaging `fgmn_model_calculus_nonempty` — and fires
it at the keystone.

## Charge 1 — the SCOPE adjudication (class field ⟷ pack export)

The pack chain supplies exactly the GRADED half of the class; the normalized/key/letter
half is genuinely extra (the OPEN-DICT frontier), carried here as the honest named
remainder structure `PackNormalizedLeg`:

| A-C.11 field | pack-chain export | verdict |
|---|---|---|
| `keyAt`/`keyAt_one`/`keyAt_deg` | — (a pack carries ONE key, `P.key`) | EXTRA — OPEN-DICT-1's `KeyChain`; consumed via `fgmnCalculusOf` + the leg's `key_deg` fence tie |
| `ExactGrade`/`AboveGrade` | `nextSupp` (exact / strictly-above line value) | DERIVED — definitions from the one `nextValue := natToInt ∘ nextSupp`, per U7 §3 |
| `PrevGrade` | — (no pack law rides it, see `Rgr_mul` row) | LEG-CHOSEN — the semantic realization stays the instantiator's obligation (U14/A-C.13); keystone takes the landed all-grades `S2Mu5PrevGrade` |
| `Rgr` | `(nextRead · ·).coeff 0` | DERIVED — CC-14's coefficient-zero projection at the pack residual |
| `Rgr_zero_of_above` | `nextRead_above` | FIRES |
| `Rgr_add` | `nextRead_add` | FIRES |
| `Rgr_mul` | `nextSupp_mul` + `nextRead_mul`, coefficientwise | FIRES **premise-free**: the §1-RUNG coboundary twist absorbed the carry, so the pack residual is exactly multiplicative and the `PrevGrade` premise is never consumed.  (No tension with A-C.13: the plain law is machine-refuted for the PUBLISHED-shape μ-layer residual — `C130rp2.tooth_graded_mul_plain_shape_refuted` — a different realization of the fields; see Honesty below.) |
| `Rgr_ne_zero` | `exact_ne` through the `j = 0` development collapse (`packRgr_ne_zero`) | FIRES — the B-1 grade nonvanishing |
| `Rres`/`Rres_mul`/`Rres_recipe`/`Rres_exists` | — | EXTRA — published Def 3.15 / Cor 4.12(3) / eq. (11) / Thm 5.7.  Thm 5.7 is RUNG §7's ADJUDICATED per-rung obligation (the `RungLift` genre: "NOT a field of the realization's chain data") — the same content, one interface over |
| `KP`/`KP_criterion`/`KP_irred`/`KP_keyAt` | — | EXTRA — §1.2 membership; Lem 5.2(2)+Cor 4.9; Lem 1.8+Cor 1.10; Prop 1.7(4) |
| `nuEquiv`/`nuEquiv_iff_Rres` | — | EXTRA — Def 1.2; Prop 5.6(2)⟷(3) |
| `letterZ`/`letterZ_ne_zero` | — | EXTRA — §3.3 letters (OPEN-DICT-4 territory) |

Count: the pack discharges 4 of the 10 data fields (+1 leg-chosen) and 4 of the 13 laws
— the ENTIRE graded layer; the remainder (5 data fields, 9 laws, the chain) is
`PackNormalizedLeg`, all of it landed content at the keystone (C136e2's μ₅ bank).

## Charge 2 — what is built

* §1 the grade coercion `natToInt : ℕ∞ → WithTop ℤ` and its two transfer iffs.
* §2 the `j = 0` development collapse: below the key-degree fence,
  `nextSupp = ℓ · supp` (`nextSupp_of_deg_lt`) and the pack's `exact_ne` becomes the
  class-shape scalar nonvanishing ★ `packRgr_ne_zero` (the B-1 grade transcription).
* §3 `PackNormalizedLeg` (the honest remainder) and the source records:
  `packSourceData` (`nextValue := natToInt ∘ nextSupp`, `gradedResidual := nextRead` —
  matching R4K's landed dictionary `s2_nextRead3_eq_mu5GradedRes` shape), the grade
  bridges `packExact_iff`/`packAbove_iff`, ★ `packSourceLaws` (all thirteen source laws:
  four from the pack, nine from the leg), and ★★ the transcription
  `fgmnCalculusOf_packs : PackNormalizedLeg → FGMNCalculus W e' f' u'` with
  `pack_calculus_nonempty`, plus rfl anti-drift teeth.  Uniform in `q` and the frame.
* §4 ★★ **the keystone fire**: `s2PackCalculusFour : FGMNCalculus (s2DepthFour) 1 1 171`
  — the depth-four calculus derived through the PACK route (rung-3 pack + C136e2's
  landed normalized bank), `s2_pack_calculus_discharge` its Nonempty form; the grade
  dictionary `s2_packExact_iff` (pack exact grade = landed μ₅ exact grade); the
  residual-agreement theorem with the landed μ-route (`s2PackCalculusFour_residual_agree`,
  R4K's dictionary in calculus coordinates); and the CONSUMER FIRE: C136d3's chain-level
  depth-four GENTOW normalizer read `s2Mu5_chainNormBelow_four_one_seventy_one_chain`
  fires at the pack calculus with `keyAt` pinned by `rfl`.

## Consumers (charge 2's check, frontier note)

Unconditional calculus instances ALREADY exist at every landed depth via the μ-operator
route (C130sg depth-1 `(2,1,5)`; C132kp6b depth-2 `(2,1,21)`; C136d3 depth-3 `(2,1,85)`;
C136e2 depth-4 `(1,1,171)`; C136c0 site) — so the depth-four consumers (C136t:397,
C136d3's `_chain` form) were already dischargeable.  What this unit adds is the ROUTE:
the calculus operators + B-1 grades now come from `RungPack` data (SPB's boundary), so
any future GENERAL-tower pack (RUNG §3's `rung2Pack` exists at EVERY level datum over a
finite residue field, uniform in `q`) transcribes by supplying only the normalized leg.

## Honesty classification

* **C.92 stands.**  No instance is declared (`@[implicit_reducible]` defs only, per the
  C130pk convention); `fgmnCalculusOf_packs` is CONDITIONAL on a pack and the leg —
  there is still no theorem from a bare `DeepTower` to `Nonempty (FGMNCalculus …)`.
  The keystone discharge is unconditional but consumes the PACKED tower (W3P/R4K's
  rung-3 pack) plus C136e2's landed normalized bank — strictly more than a bare tower.
* **Which residual the fields carry.**  The transcribed `gradedResidual` is the pack's
  raw-abscissa, twist-normalized iterated read (`nextRead`).  At unramified rungs
  (ℓ = 1 — the keystone rung 3) it IS the landed μ₅ graded residual on its lawful domain
  (R4K's dictionary; `s2PackCalculusFour_residual_agree` below).  At ramified rungs it
  is the ℓ-dilated read (W3P: `X ↦ X²`), eval-1-equal but not polynomial-equal to the
  published-shape operator.  Faithfulness of any landed instance's operators to the
  published `F_(r+1)` objects is OPEN-DICT-3's standing open — unchanged by this unit.
* **`PrevGrade`.**  The transcription imposes no law through it (the pack's product law
  is premise-free — lawful because the §1-RUNG coboundary twist makes the read exactly
  multiplicative); its semantic realization (preceding-group membership, U14 §8.1) stays
  the instantiator's obligation.  The keystone leg takes the LANDED all-grades
  `S2Mu5PrevGrade` (C136e0), byte-parallel with C136e2's `s2SourceDataFour`.
* No new axiom, no `sorry`, no `unsafe`, no statement weakened; the A-C.11 class,
  `FGMNSourceData`/`FGMNSourceLaws`, and `fgmnCalculusOf` are consumed verbatim.

DEPENDS: I10RungLift4 (R4K: the rung-3/4 packs + the μ₅ dictionaries) → I10RungLift3W
(W3P) → I10RungLift3 (RL3) → I10RungPacks (RUNG) → I10WeightedCarrier (WCC); C136e0/e1/e2
(the μ₅ operator bank), C136d3 (the depth-four `KeyChain` + the chain-level consumer),
C130pk/C130fg via the C136 chain (`FGMNCalculus`, the source records, `fgmnCalculusOf`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no instance declared.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10cct

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132rp10b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136e1
open Uniformity.Density.Tower.C136e2
open Uniformity.Density.Tower.I10wcc
open Uniformity.Density.Tower.I10rung
open Uniformity.Density.Tower.I10rl3
open Uniformity.Density.Tower.I10rl3w
open Uniformity.Density.Tower.I10rl4

/-! ## §1 — the grade coercion `ℕ∞ → WithTop ℤ` and its transfer iffs

`FGMNSourceData.nextValue` is `WithTop ℤ`-valued (the cleared Laurent-height codomain);
the pack's `nextSupp` is `ℕ∞`-valued.  The coercion and the two iffs are the entire
bridge. -/

/-- the cleared-grade coercion: `ℕ∞ → WithTop ℤ` by mapping `Nat.cast` under the `⊤`. -/
def natToInt (x : ℕ∞) : WithTop ℤ := WithTop.map (Nat.cast : ℕ → ℤ) x

/-- equality transfer: the coerced value hits a natural grade iff the `ℕ∞` value does. -/
theorem natToInt_eq_natCast_iff {x : ℕ∞} {n : ℕ} :
    natToInt x = ((n : ℤ) : WithTop ℤ) ↔ x = (n : ℕ∞) := by
  induction x using WithTop.recTopCoe with
  | top =>
      simp only [natToInt, WithTop.map_top]
      exact iff_of_false (by simp) (ENat.top_ne_coe n)
  | coe m =>
      simp only [natToInt, WithTop.map_coe, WithTop.coe_inj, Int.natCast_inj]
      exact (ENat.coe_inj).symm

/-- strict-order transfer: a natural grade sits strictly below the coerced value iff it
does below the `ℕ∞` value. -/
theorem natCast_lt_natToInt_iff {x : ℕ∞} {n : ℕ} :
    ((n : ℤ) : WithTop ℤ) < natToInt x ↔ (n : ℕ∞) < x := by
  induction x using WithTop.recTopCoe with
  | top =>
      simp only [natToInt, WithTop.map_top]
      exact iff_of_true (by simp) (ENat.coe_lt_top n)
  | coe m =>
      simp only [natToInt, WithTop.map_coe, WithTop.coe_lt_coe, Nat.cast_lt]
      exact ENat.coe_lt_coe.symm

section Generic

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}

/-! ## §2 — the `j = 0` development collapse and the B-1 grade transcription -/

/-- local guard twins of WCC/RUNG's private unfoldings (8th corpus repetition — flagged
for the standing dedup pass). -/
private theorem wcoeff_of_guard {K' : Type*} [CommRing K'] (C : WeightedCarrier O K')
    {u ℓ : ℕ} (P : CarrierKey C u ℓ) {β J : ℕ} {f : Polynomial O}
    (h1 : u * J ≤ β) (h2 : ℓ ∣ (β - u * J)) :
    wcoeff C P β f J = C.read ((β - u * J) / ℓ) (dev P.key f J) := if_pos ⟨h1, h2⟩

/-- below the key-degree fence, development slot `0` is the polynomial itself (the
`modByMonic` self case; local twin of the RUNG `dev_key_mul_one` step). -/
private theorem dev_zero_of_deg_lt {K' : Type*} [CommRing K'] {C : WeightedCarrier O K'}
    {u ℓ : ℕ} (P : CarrierKey C u ℓ) {g : Polynomial O}
    (hdeg : g.natDegree < P.key.natDegree) : dev P.key g 0 = g := by
  rw [C130nv2.dev_zero_pin]
  rcases eq_or_ne g 0 with rfl | h0
  · exact Polynomial.zero_modByMonic _
  · exact (Polynomial.modByMonic_eq_self_iff P.monic).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree P.monic.ne_zero]
          exact_mod_cast hdeg)

/-- below the key-degree fence, the positive development slots vanish. -/
private theorem dev_pos_of_deg_lt {K' : Type*} [CommRing K'] {C : WeightedCarrier O K'}
    {u ℓ : ℕ} (P : CarrierKey C u ℓ) {g : Polynomial O}
    (hdeg : g.natDegree < P.key.natDegree) {j : ℕ} (hj : 1 ≤ j) : dev P.key g j = 0 :=
  dev_eq_zero_of_lt P.monic P.deg_pos g j
    (lt_of_lt_of_le hdeg (Nat.le_mul_of_pos_left _ hj))

variable (K : KeyChain W) {u ℓ : ℕ} (R : RungPack O (W.fld r) u ℓ)

/-- ★ below the key-degree fence the iterated support is the pure `j = 0` line value:
`nextSupp g = ℓ · supp g` (positive slots price `⊤`). -/
theorem nextSupp_of_deg_lt {g : Polynomial O}
    (hdeg : g.natDegree < R.P.key.natDegree) :
    nextSupp R.C R.P g = (ℓ : ℕ∞) * R.C.supp g := by
  have htop : (ℓ : ℕ∞) * ⊤ = ⊤ :=
    WithTop.mul_top (Nat.cast_ne_zero.mpr R.P.ell_pos.ne')
  refine le_antisymm ?_ (le_iInf fun j => ?_)
  · calc nextSupp R.C R.P g
        ≤ (ℓ : ℕ∞) * R.C.supp (dev R.P.key g 0) + ((u * 0 : ℕ) : ℕ∞) := iInf_le _ 0
      _ = (ℓ : ℕ∞) * R.C.supp g := by
          rw [dev_zero_of_deg_lt R.P hdeg, Nat.mul_zero, Nat.cast_zero, add_zero]
  · match j with
    | 0 =>
        rw [dev_zero_of_deg_lt R.P hdeg, Nat.mul_zero, Nat.cast_zero, add_zero]
    | j + 1 =>
        rw [dev_pos_of_deg_lt R.P hdeg (Nat.le_add_left 1 j), R.C.supp_zero, htop,
          top_add]
        exact le_top

/-- ★ **the B-1 grade transcription** (`graded_scalar_nonzero` genre, class shape at the
pack fence): below the key-degree fence, the degree-zero coefficient of the iterated
read at the exact iterated grade is NONZERO — the pack's own `exact_ne`, read through the
`j = 0` development collapse. -/
theorem packRgr_ne_zero {β : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < R.P.key.natDegree)
    (hex : nextSupp R.C R.P g = (β : ℕ∞)) :
    (nextRead R.C R.P β g).coeff 0 ≠ 0 := by
  rw [nextSupp_of_deg_lt R hdeg] at hex
  have htop : (ℓ : ℕ∞) * ⊤ = ⊤ :=
    WithTop.mul_top (Nat.cast_ne_zero.mpr R.P.ell_pos.ne')
  rcases eq_or_ne (R.C.supp g) ⊤ with hT | hT
  · rw [hT, htop] at hex
    exact absurd hex (by simp)
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hA] at hex
  have hβ : ℓ * A = β := by exact_mod_cast hex
  rw [nextRead_coeff]
  have hg1 : u * 0 ≤ β := by omega
  have hg2 : ℓ ∣ (β - u * 0) := ⟨A, by omega⟩
  rw [wcoeff_of_guard R.C R.P hg1 hg2, dev_zero_of_deg_lt R.P hdeg,
    show (β - u * 0) / ℓ = A from by
      rw [Nat.mul_zero, Nat.sub_zero, ← hβ, Nat.mul_div_cancel_left _ R.P.ell_pos]]
  exact R.exact_ne hdeg hA.symm

/-! ## §3 — the honest remainder, the source records, and the transcription

(`K` is declared BEFORE the pack in every signature below, so the chain pins the tower
`W` at application sites — the pack argument then lands by the definitional field
identification, never the other way around.) -/

/-- ★ **The honest remainder of the carrier→calculus transcription** — the class fields
the pack chain does NOT export (the SCOPE table's EXTRA rows): the key-chain fence tie
(OPEN-DICT-1's degree dictionary), the normalized-residual layer (published Def 3.15,
Cor 4.12(3), eq. (11), Thm 5.7 — the last being RUNG §7's adjudicated per-rung
obligation, the `RungLift` genre), the key-polynomial predicate with its criterion/
irreducibility/carried-key clauses, the initial-form equivalence, the residue letters,
and the `PrevGrade` choice (no law rides it here — the pack's product law is
premise-free; the semantic realization stays the instantiator's obligation per U14).
Grade-mentioning clauses are stated in the PACK's coordinates (`nextSupp`/`nextRead`),
which the source-record assembly consumes without translation. -/
structure PackNormalizedLeg (K : KeyChain W) {u ℓ : ℕ}
    (R : RungPack O (W.fld r) u ℓ) (e' f' u' : ℕ) where
  /-- OPEN-DICT-1's fence tie: the chain's current key has the pack key's degree. -/
  key_deg : (K.keyAt r).natDegree = R.P.key.natDegree
  /-- the normalized residual operator (published Def 3.15). -/
  Rres : Polynomial O → Polynomial (W.fld r)
  /-- key-polynomial membership (published §1.2). -/
  KP : Polynomial O → Prop
  /-- the initial-form equivalence (published Def 1.2). -/
  nuEquiv : Polynomial O → Polynomial O → Prop
  /-- the residue letters (published §3.3; OPEN-DICT-4 territory). -/
  letterZ : ℕ → W.fld r
  /-- the preceding-group predicate (A-C.13/U14); UNCONSUMED by the pack laws. -/
  PrevGrade : ℕ → Prop
  /-- published Cor 4.12(3). -/
  normalized_mul : ∀ g h : Polynomial O, Rres (g * h) = Rres g * Rres h
  /-- published eq. (11)/Def 1.6 recipe expansion, scalar slots in pack coordinates. -/
  normalized_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → nextSupp R.C R.P (khat t) = (((f' - t) * u' : ℕ) : ℕ∞)) →
    (∀ t, t < f' → (khat t).natDegree < (K.keyAt r).natDegree) →
    Rres ((K.keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (K.keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
        Polynomial.C ((nextRead R.C R.P ((f' - t) * u') (khat t)).coeff 0) *
          Polynomial.X ^ t
  /-- published Thm 5.7 (RUNG §7's adjudicated per-rung obligation). -/
  normalized_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O, g.Monic ∧
        g.natDegree = e' * f' * (K.keyAt r).natDegree ∧ Rres g = ψ
  /-- published Lem 5.2(2) + Cor 4.9 + the Thm 5.7 degree display. -/
  key_criterion : ∀ g : Polynomial O, g.Monic →
    g.natDegree = e' * f' * (K.keyAt r).natDegree →
    Irreducible (Rres g) → (Rres g).natDegree = f' → (Rres g).coeff 0 ≠ 0 → KP g
  /-- published Lem 1.8 + Cor 1.10 (Gauss transport). -/
  key_irreducible : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g
  /-- published Prop 1.7(4). -/
  carried_key_is_key : 0 < r → KP (K.keyAt r)
  /-- published eq. (11): the carried key's residual is `1`. -/
  carried_key_residual : 0 < r → Rres (K.keyAt r) = 1
  /-- published Prop 5.6(2) iff (3). -/
  initial_iff_residual : ∀ g h : Polynomial O, KP g → KP h →
    (nuEquiv g h ↔ Rres g = Rres h)
  /-- published §3.3 letter nonvanishing on the live range. -/
  letter_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0

variable {e' f' u' : ℕ}

/-- ★ **the pack-realized source data** (CC-13's record from the pack chain): the
realized next valuation is the coerced iterated support, the polynomial-valued graded
residual is the iterated read (matching R4K's landed keystone dictionary
`s2_nextRead3_eq_mu5GradedRes` in shape), and the normalized layer is the leg's. -/
noncomputable def packSourceData (N : PackNormalizedLeg K R e' f' u') :
    FGMNSourceData W K e' f' u' where
  nextValue g := natToInt (nextSupp R.C R.P g)
  gradedResidual := nextRead R.C R.P
  normalizedResidual := N.Rres
  PrevGrade := N.PrevGrade
  keyPolynomial := N.KP
  initialEquiv := N.nuEquiv
  letter := N.letterZ

/-- grade bridge: the record's exact grade IS the pack's exact iterated line value. -/
theorem packExact_iff (N : PackNormalizedLeg K R e' f' u') {β : ℕ} {g : Polynomial O} :
    (packSourceData K R N).ExactGrade β g ↔ nextSupp R.C R.P g = (β : ℕ∞) := by
  show natToInt (nextSupp R.C R.P g) = (β : WithTop ℤ) ↔ _
  rw [← WithTop.coe_natCast]
  exact natToInt_eq_natCast_iff

/-- grade bridge: the record's above-grade IS the pack's strict line excess. -/
theorem packAbove_iff (N : PackNormalizedLeg K R e' f' u') {β : ℕ} {g : Polynomial O} :
    (packSourceData K R N).AboveGrade β g ↔ (β : ℕ∞) < nextSupp R.C R.P g := by
  show (β : WithTop ℤ) < natToInt (nextSupp R.C R.P g) ↔ _
  rw [← WithTop.coe_natCast]
  exact natCast_lt_natToInt_iff

/-- ★ **the thirteen source laws at the pack-realized record**: the four graded clauses
are PACK THEOREMS (`nextRead_above`/`nextRead_add`/`nextSupp_mul` + `nextRead_mul`/
`packRgr_ne_zero`); the nine normalized clauses are the leg's.  Note `graded_mul`
discards the `PrevGrade` premise — the pack's convolution law is exact (the coboundary
twist), so the premise is never consumed. -/
theorem packSourceLaws (N : PackNormalizedLeg K R e' f' u') :
    FGMNSourceLaws W K e' f' u' (packSourceData K R N) where
  graded_zero_of_above := fun _ g h =>
    nextRead_above R ((packAbove_iff K R N).mp h)
  graded_add := fun _ g h hg hh _ =>
    nextRead_add R (le_of_eq ((packExact_iff K R N).mp hg).symm)
      (le_of_eq ((packExact_iff K R N).mp hh).symm)
  graded_mul := fun β β' g h hg hh _ => by
    have hg' := (packExact_iff K R N).mp hg
    have hh' := (packExact_iff K R N).mp hh
    refine ⟨(packExact_iff K R N).mpr ?_, nextRead_mul R hg' hh'⟩
    rw [nextSupp_mul R, hg', hh', ← Nat.cast_add]
  graded_scalar_nonzero := fun β g hex hdeg _ =>
    packRgr_ne_zero R (N.key_deg ▸ hdeg) ((packExact_iff K R N).mp hex)
  normalized_mul := N.normalized_mul
  normalized_recipe := fun khat hgr hdeg =>
    N.normalized_recipe khat (fun t ht => (packExact_iff K R N).mp (hgr t ht)) hdeg
  normalized_exists := N.normalized_exists
  key_criterion := N.key_criterion
  key_irreducible := N.key_irreducible
  carried_key_is_key := N.carried_key_is_key
  carried_key_residual := N.carried_key_residual
  initial_iff_residual := N.initial_iff_residual
  letter_ne_zero := N.letter_ne_zero

/-- ★★ **THE CARRIER→CALCULUS TRANSCRIPTION** (SPB's named boundary leg): a rung pack at
the tower's terminal field, together with the honest normalized remainder, yields the
A-C.11 calculus — through the landed CC-16 packaging `fgmnCalculusOf`, no new route into
the class.  Uniform in `q` and the frame; deliberately a `def`, NOT an `instance`
(C92_VACUITY: no `[FGMNCalculus …]` binder may be silently satisfied). -/
@[implicit_reducible] noncomputable def fgmnCalculusOf_packs
    (N : PackNormalizedLeg K R e' f' u') : FGMNCalculus W e' f' u' :=
  fgmnCalculusOf K (packSourceData K R N) (packSourceLaws K R N)

/-- ★★ the Nonempty form: pack + leg ⟹ the calculus is inhabited.  (The C.92
adjudication stands: the pack and the leg are strictly more than a bare `DeepTower`.) -/
theorem pack_calculus_nonempty (N : PackNormalizedLeg K R e' f' u') :
    Nonempty (FGMNCalculus W e' f' u') :=
  ⟨fgmnCalculusOf_packs K R N⟩

/-! ### anti-drift teeth: the transcribed operators ARE the pack reads, definitionally -/

section Teeth

variable (N : PackNormalizedLeg K R e' f' u')

example : (fgmnCalculusOf_packs K R N).Rgr
    = fun β g => (nextRead R.C R.P β g).coeff 0 := rfl

example : (fgmnCalculusOf_packs K R N).keyAt = K.keyAt := rfl

example : (fgmnCalculusOf_packs K R N).Rres = N.Rres := rfl

example : (fgmnCalculusOf_packs K R N).KP = N.KP := rfl

example : (fgmnCalculusOf_packs K R N).nuEquiv = N.nuEquiv := rfl

example : (fgmnCalculusOf_packs K R N).letterZ = N.letterZ := rfl

example : (fgmnCalculusOf_packs K R N).PrevGrade = N.PrevGrade := rfl

example : (fgmnCalculusOf_packs K R N).ExactGrade
    = fun (β : ℕ) (g : Polynomial O) =>
        natToInt (nextSupp R.C R.P g) = (β : WithTop ℤ) := rfl

end Teeth

end Generic

/-! ## §4 — ★★ the keystone fire: the depth-four calculus through the PACK route -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- pack-key pin: the rung-3 pack's key IS `g16` (the `ofRootF1` construction,
definitionally). -/
theorem s2Rung3Pack_key : (s2Rung3Pack h2 hq).P.key = g16 h2 hq := rfl

/-- the keystone fence tie: the depth-four chain's current key `keyAt 4 = g16` carries
exactly the pack key's degree. -/
theorem s2_key_deg :
    ((s2DepthFourKeyChain h2 hq).keyAt 4).natDegree
      = (s2Rung3Pack h2 hq).P.key.natDegree := by
  rw [s2DepthFourKeyChain_keyAt_four h2 hq, s2Rung3Pack_key h2 hq]

/-- ★ **the keystone grade dictionary in calculus coordinates**: the rung-3 pack's exact
iterated grade IS the landed μ₅ exact grade (R4K's support dictionary
`s2_nextSupp3_eq_dv4Supp` + the landed `S2Mu5ExactGrade_iff_dv4Supp`). -/
theorem s2_packExact_iff {β : ℕ} {f : Polynomial O} :
    nextSupp (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P f = (β : ℕ∞) ↔
      S2Mu5ExactGrade h2 hq β f := by
  rw [s2_nextSupp3_eq_dv4Supp h2 hq]
  exact (S2Mu5ExactGrade_iff_dv4Supp h2 hq).symm

/-- floor extractor for R4K's residual dictionary. -/
private theorem s2_floor_of_exact {β : ℕ} {f : Polynomial O}
    (h : S2Mu5ExactGrade h2 hq β f) :
    (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1 :=
  le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp h).symm

set_option maxHeartbeats 1600000 in
/-- ★ **the keystone normalized leg — every field LANDED content** (C136e2's μ₅ bank,
byte-parallel with `s2SourceDataFour`/`s2SourceLawsFour`'s normalized rows): `Rres` is
`s2Mu5NormRes`, `KP` is `S2Mu5KeyPoly`, `nuEquiv` is `S2Mu5InitialEquiv`, the letters are
the forced constant-`1` `s2LetterFour`, `PrevGrade` is the landed all-grades
`S2Mu5PrevGrade`; the recipe clause is D4-17's `s2Mu5_normalized_recipe_field` read
through the grade/residual dictionaries (`s2_packExact_iff`,
`s2_nextRead3_eq_mu5GradedRes`). -/
noncomputable def s2PackLegFour :
    PackNormalizedLeg (s2DepthFourKeyChain h2 hq) (s2Rung3Pack h2 hq) 1 1 171 where
  key_deg := s2_key_deg h2 hq
  Rres := s2Mu5NormRes h2 hq
  KP := S2Mu5KeyPoly h2 hq
  nuEquiv := S2Mu5InitialEquiv h2 hq
  letterZ := s2LetterFour h2 hq
  PrevGrade := S2Mu5PrevGrade
  normalized_mul := s2Mu5NormRes_mul h2 hq
  normalized_recipe := fun khat hgr hdeg => by
    have hgr' : ∀ t, t < 1 → S2Mu5ExactGrade h2 hq ((1 - t) * 171) (khat t) :=
      fun t ht => (s2_packExact_iff h2 hq).mp (hgr t ht)
    -- assemble the identity in the pack's own field typing ((s2DepthTwo).fld 2, the
    -- definitional unfolding of (s2DepthFour).fld 4), then hand it over by `exact`
    have hrec := s2Mu5_normalized_recipe_field h2 hq khat hgr' hdeg
    have hread : nextRead (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P
        ((1 - 0) * 171) (khat 0)
          = s2Mu5GradedRes h2 hq ((1 - 0) * 171) (khat 0) :=
      s2_nextRead3_eq_mu5GradedRes h2 hq
        (s2_floor_of_exact h2 hq (hgr' 0 (by omega)))
    simp only [Finset.sum_range_one] at hrec ⊢
    rw [← hread] at hrec
    exact hrec
  normalized_exists := fun _ ψ hm hirr hd hc => s2Mu5_hex h2 hq ψ hm hirr hd hc
  key_criterion := s2Mu5_key_criterion h2 hq
  key_irreducible := fun _ hkp _ => s2Mu5_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => S2Mu5KeyPoly_keyAt_four h2 hq
  carried_key_residual := fun _ => s2Mu5NormRes_keyAt_four h2 hq
  initial_iff_residual := fun g h hg hh => s2Mu5_initial_iff_residual h2 hq g h hg hh
  letter_ne_zero := fun i h1 hr => s2LetterFour_ne_zero h2 hq i h1 hr

set_option maxHeartbeats 1600000 in
/-- ★★ **THE DEPTH-FOUR CALCULUS THROUGH THE PACK ROUTE**: the transcription fired at
the keystone rung-3 pack (W3P/R4K) with the landed normalized leg — the pack-route
counterpart of C136r3's μ-layer `s2Mu5Calculus`, same tower, same `(1, 1, 171)`. -/
@[implicit_reducible] noncomputable def s2PackCalculusFour :
    FGMNCalculus (s2DepthFour h2 hq) 1 1 171 :=
  fgmnCalculusOf_packs (s2DepthFourKeyChain h2 hq) (s2Rung3Pack h2 hq)
    (s2PackLegFour h2 hq)

/-- ★★ the Nonempty form — the same statement as C136e2's landed
`s2Mu5_calculus_nonempty`, now derived through the PACK route: an independent second
derivation of the deep-tower calculus discharge (the depth-one anchor's
`C130sg.s2_calculus_discharge` genre, at depth FOUR). -/
theorem s2_pack_calculus_discharge :
    Nonempty (FGMNCalculus (s2DepthFour h2 hq) 1 1 171) :=
  ⟨s2PackCalculusFour h2 hq⟩

/-! ### anti-drift teeth and the μ-route agreement -/

set_option maxHeartbeats 800000 in
/-- rfl tooth: the pack calculus's scalar residual IS the rung-3 pack's iterated read at
coefficient zero — the B-1 grade reads come from the pack, definitionally. -/
theorem s2PackCalculusFour_Rgr :
    (s2PackCalculusFour h2 hq).Rgr
      = fun β g => (nextRead (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β g).coeff 0 :=
  rfl

/-- rfl tooth: the pack calculus's keys are the depth-four chain's. -/
theorem s2PackCalculusFour_keyAt :
    (s2PackCalculusFour h2 hq).keyAt = (s2DepthFourKeyChain h2 hq).keyAt := rfl

/-- rfl tooth: the normalized residual is the landed μ₅ operator. -/
theorem s2PackCalculusFour_Rres :
    (s2PackCalculusFour h2 hq).Rres = s2Mu5NormRes h2 hq := rfl

/-- rfl tooth: `PrevGrade` is the landed all-grades predicate (C136e0), byte-parallel
with C136e2's realization. -/
theorem s2PackCalculusFour_PrevGrade :
    (s2PackCalculusFour h2 hq).PrevGrade = S2Mu5PrevGrade := rfl

/-- ★ **the μ-route agreement** (R4K's residual dictionary in calculus coordinates): on
its lawful domain the pack calculus's polynomial-valued graded residual IS the landed μ₅
graded residual — the two routes to the depth-four calculus carry the SAME operator. -/
theorem s2PackCalculusFour_residual_agree {β : ℕ} {f : Polynomial O}
    (hβ : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1) :
    (packSourceData (s2DepthFourKeyChain h2 hq) (s2Rung3Pack h2 hq)
        (s2PackLegFour h2 hq)).gradedResidual β f
      = s2Mu5GradedRes h2 hq β f :=
  s2_nextRead3_eq_mu5GradedRes h2 hq hβ

set_option maxHeartbeats 1600000 in
/-- ★ **the consumer fire** (charge 2's check): C136d3's chain-level depth-four GENTOW
normalizer read fires at the pack calculus — `keyAt` is rfl-pinned to the depth-four
chain, so the one `hkey` premise is `rfl`. -/
example : (s2PackCalculusFour h2 hq).chainNormBelow 4 171 = s2Mu5Lambda h2 hq :=
  s2Mu5_chainNormBelow_four_one_seventy_one_chain h2 hq (s2PackCalculusFour h2 hq) rfl

end S2

end Uniformity.Density.Tower.I10cct

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10cct.natToInt_eq_natCast_iff
#print axioms Uniformity.Density.Tower.I10cct.natCast_lt_natToInt_iff
#print axioms Uniformity.Density.Tower.I10cct.nextSupp_of_deg_lt
#print axioms Uniformity.Density.Tower.I10cct.packRgr_ne_zero
#print axioms Uniformity.Density.Tower.I10cct.packSourceData
#print axioms Uniformity.Density.Tower.I10cct.packExact_iff
#print axioms Uniformity.Density.Tower.I10cct.packAbove_iff
#print axioms Uniformity.Density.Tower.I10cct.packSourceLaws
#print axioms Uniformity.Density.Tower.I10cct.fgmnCalculusOf_packs
#print axioms Uniformity.Density.Tower.I10cct.pack_calculus_nonempty
#print axioms Uniformity.Density.Tower.I10cct.s2Rung3Pack_key
#print axioms Uniformity.Density.Tower.I10cct.s2_key_deg
#print axioms Uniformity.Density.Tower.I10cct.s2_packExact_iff
#print axioms Uniformity.Density.Tower.I10cct.s2PackLegFour
#print axioms Uniformity.Density.Tower.I10cct.s2PackCalculusFour
#print axioms Uniformity.Density.Tower.I10cct.s2_pack_calculus_discharge
#print axioms Uniformity.Density.Tower.I10cct.s2PackCalculusFour_Rgr
#print axioms Uniformity.Density.Tower.I10cct.s2PackCalculusFour_residual_agree

end AxCheck
