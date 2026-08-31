/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10SiteCalc
import Uniformity.ChapI.I10LadderRead
import Uniformity.ChapI.I10RungLift4

/-!
# Uniformity.ChapI.I10SpineBridge — SPB: the carrier→calculus spine bridge — the wiring
laws dissected at the wired-read genre, and the keystone fire through the completed
tower packs [SPB 2026-08-31]

**Unit SPB** — the realization-side successor of the completed tower-pack campaign
(R4K: the keystone tower side is COMPLETE at rungs 2/3/4; RL3 §7's fence: "the
multiplicativity half is what the packs export at every rung; kernel-agreement + peel
tie remain realization-side").  The charge: do the three wiring laws — `BankWiredAt`'s
GC-13 read law (SCS), `CarrierReadLaw`'s kernel-agreement and peel tie (LRS) — FIRE at
the keystone realization, now that the packs are rfl-pinned there?

## THE ADJUDICATION (charge 1's question, answered exactly)

**The kernel-agreement is NOT `rfl`/defeq — and the wiring laws DO fire.**  The
keystone realization's exported read was NOT wired to the tower's pack reads: it was
wired at construction to the CONSTANT `1` (IFC4's P3 licence, mandated at depth ≥ 4 by
the GCW-6 fence; `C136c0.s2Four_towerReadFamily_live`).  The tower's own reads — the
pack reads of `s2Rung2Pack`/`s2Rung3Pack`/`s2Rung4Pack` and the site calculus's `Rgr` —
agree with that export VALUEWISE, not definitionally: every one of them is NONZERO on
its lawful domain (the packs' `exact_ne`, the bank's B-1 `Rgr_ne_zero` rows — the same
FGMN `graded_scalar_nonzero` mechanism), and every nonzero value of a 2-element field
is `1`.  So the spine bridge at the keystone is: **wired constant read + card-2
collapse + the tower's own nonvanishing** — one `c0`-collapse per law, no `rfl`, no
new structure.  The machine pins: `s2Rung2_read_eq_one`/`s2Rung3_read_eq_one`/
`s2Rung4_read_eq_one` (§5 — the pack reads are constantly `1` on their exact-grade
domains, i.e. the exports and the tower's own reads take the SAME value everywhere both
are lawful), and the §4 keystone fire below.

## Charge 2 — the generic/keystone dissection (the TWD/WSS pattern)

The genre pin is `ReadOneAt X j` (NEW STATEMENT, review): the exported tower read at
level `j` is constantly `1` — the shape EVERY wired witness of the IFC4/GCW-6 genre
(`s2SplitNodeWired`, `s2SplitNodeFour`, any threshold/payload) exports by construction.
At that genre the three wiring laws dissect EXACTLY (iffs, uniform in `q`, the frame,
the tower, the bank, the realization):

| law | at `ReadOneAt` the residue is EXACTLY (iff) | card-2 discharge |
|---|---|---|
| `BankWiredAt X j hj B` (GC-13) | `φ(Rgr(e'·s·u', chainNormBelow(s·u'))) = 1` per window `s` | the bank's OWN B-1 nonvanishing + `φ` injective (fields) + card-2 collapse — `bankWiredAt_of_read_one_card` |
| `CarrierReadLaw.read_ker_pow` | `res k = 1` for every height-kernel element | card-2 unit group is trivial — `carrierReadLaw_of_read_one_card` |
| `CarrierReadLaw.tie` | `peelUnit = 1` | same collapse |

So the GENERIC layer (§§1–3) is: the two dissection iffs + the card-2 constructors +
the multiplicativity pin `read_mult_of_read_one` (the constant read trivially realizes
the `read_mul` shape the packs export — LRS's `carrierReadLaw_of_mult_agree` input).
The KEYSTONE-specific inputs are exactly three: the genre pin (`s2Four_towerReadFamily_live`),
the terminal-field cardinality (`s2R7Fld_card`), and the bank (`s2FourSiteBank`, `(h2, hq)`
alone).  At a GENERAL-`q` wired-constant witness the residue does NOT vanish: the iffs
show it demands `res ≡ 1` on the kernel and `peelUnit = 1` — genuinely false in general
— so beyond card 2 the wired genre must wire the read NON-constantly (to the receiver
image of the bank's own reads, GC-13's formula as the construction), which is the
per-realization residue's honest character, unchanged.

## §4 ★★ THE GENRE THEOREM AND THE KEYSTONE FIRE

★★ `wiredSiteSupply_of_bankFamily_read_one_card` — at ANY realization of the wired
card-2 genre, the deepTwist SITE HALF (WSS's `WiredSiteSupply` = `SiteCalculusSupply` ∧
`LadderReadSupply`) reduces to the TOWER-SIDE BANK FAMILY ALONE: the per-realization
wiring residue VANISHES at this genre.  Keystone fire: `s2FourBankFamily` +
★ `s2Four_bankWiringSupply` (the first named `BankWiringSupply` instance) and the
coherence examples re-deriving `SiteCalculusSupply`/`CarrierReadSupply`/
`WiredSiteSupply` at every depth-4 keystone witness through the spine route — agreeing
with the landed direct instances (`s2Four_siteCalculusSupply`, `s2Four_carrierReadSupply`,
`s2Four_wiredSiteSupply`) on the wired genre.

## Charge 3 — the deepTwist boundary after SPB (site half; tau rows out of territory)

Per the landed iff (`deepTwistField_iff_universalPerWitness`) the boundary is UNCHANGED
in strength.  The sufficient surface for the SITE HALF is now, per arising realization:

* a `LevelSiteBank` family at the deep-live truncations (tower side — the L2E program:
  the weighted absolute-read convolution carrier, the calculus-side key lifting, B-1
  normalizer grades; NOTE the CARRIER side of that program is now closed generically at
  `f' = 1` and completely at the keystone — R4K/RL3 — the open mathematics is the
  carrier→CALCULUS transcription, i.e. producing `FGMNCalculus` operators from
  `RungPack` data), AND
* the per-realization wiring residue, which THIS unit stratifies: at wired card-2
  witnesses it is EMPTY (the genre theorem); at wired general-`q` witnesses it is
  exactly the unit equations of the §1/§2 iffs; at arbitrary witnesses it is
  `BankWiringSupply` + `LadderReadSupply` as before (SCS/LRS's named remainder).

The tau half (`UniversalTauWordDescentSupply`) awaits the O-TAU owner amendment and is
untouched here.

## Honesty

* Nothing weakened: `BankWiredAt`/`CarrierReadLaw`/`BankWiringSupply`/`SiteCalculusSupply`/
  `WiredSiteSupply` consumed verbatim on the conclusion side; every new `Prop` sits
  hypothesis-side of proved reductions or inside proved iffs.
* The genre theorems are SUFFICIENT-ONLY as supply routes (no converse claimed at the
  supply level); the per-law dissections are exact iffs.
* The pack teeth consume the packs' own `exact_ne` — the R4K campaign's export — making
  the pack linkage machine-visible; no type-level hom from the pack host
  `(s2DepthTwo).fld 2` into the realization's `Kt` is landed or claimed (the agreement
  is valuewise, as adjudicated above).
* Local twins flagged for the standing dedup: `spb_eq_one_of_ne_zero` (the card-2
  collapse, 4th+ corpus repetition, here universe-polymorphic) and `spb_unit_eq_one`
  (the unit-group collapse, twin of `C136r4.s2FourUnit_eq_one`'s mechanism).

**Flagged for human review** (new statements): `ReadOneAt` (supplier-side genre pin
below the signed surface; no leanspec name touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is
the audit.  Verdict: `runs/wave-c/verdict_SPB.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

/-! ## §0 The card-2 collapses (local twins, universe-polymorphic — dedup-flagged) -/

/-- Local universe-polymorphic twin of `C136c0.c0_eq_one_of_ne_zero` (flagged for the
standing dedup): every nonzero element of a 2-element field is `1`. -/
private theorem spb_eq_one_of_ne_zero {F : Type*} [Field F] (hcard : Nat.card F = 2)
    {c : F} (hc : c ≠ 0) : c = 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : Fˣ) : F) := (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- Local twin of `C136r4.s2FourUnit_eq_one`'s mechanism (flagged for the standing
dedup): the unit group of a 2-element field is trivial. -/
private theorem spb_unit_eq_one {F : Type*} [Field F] (hcard : Nat.card F = 2)
    (u : Fˣ) : u = 1 :=
  Units.val_eq_one.mp (spb_eq_one_of_ne_zero hcard u.ne_zero)

section Suppliers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-! ## §1 The genre pin and the GC-13 dissection -/

/-- **[SPB §1] The wired-read genre pin at one level**: the realization's exported tower
read at level `j` is constantly `1` — the value EVERY witness of the IFC4/GCW-6 wired
genre exports by construction (P3's law-satisfying choice; keystone:
`s2Four_towerReadFamily_live`).  NEW STATEMENT (review). -/
def ReadOneAt (X : RealizedInput core Aℛ) (j : ℕ) : Prop :=
  ∀ g : GaugeLattice.{uG} core.r, towerReadFamily.{0, uG, uKt, uL} X j g = 1

/-- ★ **[SPB §1] THE GC-13 DISSECTION AT THE GENRE** — at a wired-constant read, the
per-realization wiring law `BankWiredAt` is EXACTLY the window unit-equation family on
the bank's own normalizer reads: `φ(Rgr(e'·(s·u'), chainNormBelow(s·u'))) = 1` for
`1 ≤ s ≤ f'`.  Exact (an iff), uniform in `q`, the frame, the tower, and the bank. -/
theorem bankWiredAt_iff_of_read_one (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : DeepLive core.r j) (B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ReadOneAt.{uG, uKt, uL} X j) :
    BankWiredAt.{uG, uKt, uL} X j hj B ↔
      ∀ s : ℕ, 1 ≤ s → s ≤ B.f' →
        Aℛ.receiver.levelHom j
          (B.calculus.Rgr (B.e' * (s * B.u'))
            (B.calculus.chainNormBelow j (s * B.u'))) = 1 := by
  constructor
  · intro h s hs1 hsf
    exact (IFC3.GC13Wiring.read_norm h s hs1 hsf).symm.trans (hread _)
  · intro h
    exact IFC3.GC13Wiring.mk fun s hs1 hsf => (hread _).trans (h s hs1 hsf).symm

/-- ★ **[SPB §1] the card-2 discharge of the GC-13 residue** — at the genre, the bank's
OWN B-1 nonvanishing rows (the FGMN `graded_scalar_nonzero` mechanism — the same export
genre as the tower packs' `exact_ne`) close the wiring law outright: the normalizer
reads are nonzero, receivers between fields are injective, and every nonzero value of a
2-element terminal field is `1`.  No `GC13Wiring` instance is consumed — this IS the
spine-bridge route. -/
theorem bankWiredAt_of_read_one_card (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : DeepLive core.r j) (B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ReadOneAt.{uG, uKt, uL} X j) (hcard : Nat.card Kt = 2) :
    BankWiredAt.{uG, uKt, uL} X j hj B := by
  refine (bankWiredAt_iff_of_read_one X hj B hread).mpr fun s hs1 hsf => ?_
  have hne : B.calculus.Rgr (B.e' * (s * B.u'))
      (B.calculus.chainNormBelow j (s * B.u')) ≠ 0 :=
    B.calculus.Rgr_ne_zero _ _ (B.norm_grade s hs1 hsf) (B.norm_deg s hs1 hsf)
      (B.norm_ne s hs1 hsf)
  exact spb_eq_one_of_ne_zero hcard fun h0 =>
    hne ((Aℛ.receiver.levelHom j).injective (h0.trans (map_zero _).symm))

/-! ## §2 The carrier-law dissection: kernel-agreement and peel tie at the genre -/

/-- ★ **[SPB §2] THE CARRIER-LAW DISSECTION AT THE GENRE** — at a wired-constant read,
LRS's `CarrierReadLaw` (kernel-agreement + power multiplicativity + peel tie) is
EXACTLY the pair of unit equations: every height-kernel arena residue is `1`, and the
peel unit is `1`.  Exact (an iff), uniform in `q`. -/
theorem carrierReadLaw_iff_of_read_one (X : RealizedInput core Aℛ) (hr : 1 < core.r)
    (j : ℕ) (hread : ReadOneAt.{uG, uKt, uL} X j) :
    CarrierReadLaw.{uG, uKt, uL} X hr j ↔
      ((∀ k : MonoidHom.ker (arenaFamily.{0, uG, uKt, uL} X hr j).v,
          (arenaFamily.{0, uG, uKt, uL} X hr j).res k = 1) ∧
        Aℛ.node.peelUnitFamily j = 1) := by
  have hR : ∀ g : GaugeLattice.{uG} core.r,
      towerReadFamily.{0, uG, uKt, uL} X j g = 1 := hread
  constructor
  · intro h
    constructor
    · intro k
      have h1 := h.read_ker_pow k 1
      simp only [hR, one_pow, mul_one] at h1
      exact Units.val_eq_one.mp h1.symm
    · have h2 := h.tie
      simp only [hR] at h2
      exact Units.val_eq_one.mp h2
  · rintro ⟨hres, hpeel⟩
    refine ⟨fun k s => ?_, ?_⟩
    · simp only [hR, hres k, Units.val_one, one_mul, one_pow]
    · simp only [hR, hpeel, Units.val_one]

/-- ★ **[SPB §2] the card-2 discharge of the carrier residue** — kernel-agreement and
peel tie close outright at a 2-element terminal field (the unit group is trivial). -/
theorem carrierReadLaw_of_read_one_card (X : RealizedInput core Aℛ) (hr : 1 < core.r)
    (j : ℕ) (hread : ReadOneAt.{uG, uKt, uL} X j) (hcard : Nat.card Kt = 2) :
    CarrierReadLaw.{uG, uKt, uL} X hr j :=
  (carrierReadLaw_iff_of_read_one X hr j hread).mpr
    ⟨fun k => spb_unit_eq_one hcard _, spb_unit_eq_one hcard _⟩

/-! ## §3 The multiplicativity pin: the pack shape realized at the genre -/

/-- **[SPB §3] the wired-constant read is multiplicative on the whole synchronized
lattice** — the `read_mul` shape the tower packs export at every rung (RL3 §7's
"multiplicativity half"), trivially realized by the genre's constant read.  This is the
`hmul` input of LRS's coarse supplier shape `carrierReadLaw_of_mult_agree`. -/
theorem read_mult_of_read_one (X : RealizedInput core Aℛ) (j : ℕ)
    (hread : ReadOneAt.{uG, uKt, uL} X j) :
    ∀ g g' : GaugeLattice.{uG} core.r,
      towerReadFamily.{0, uG, uKt, uL} X j (g * g') =
        towerReadFamily.{0, uG, uKt, uL} X j g *
          towerReadFamily.{0, uG, uKt, uL} X j g' := by
  have hR : ∀ g : GaugeLattice.{uG} core.r,
      towerReadFamily.{0, uG, uKt, uL} X j g = 1 := hread
  intro g g'
  simp only [hR, one_mul]

/-- Coherence pin: at the genre + card 2, LRS's coarse supplier route (`mult_agree` —
the exact shape a full carrier realization of the node's W-leg would export) fires and
agrees with the §2 constructor. -/
example (X : RealizedInput core Aℛ) (hr : 1 < core.r) (j : ℕ)
    (hread : ReadOneAt.{uG, uKt, uL} X j) (hcard : Nat.card Kt = 2) :
    CarrierReadLaw.{uG, uKt, uL} X hr j := by
  have hR : ∀ g : GaugeLattice.{uG} core.r,
      towerReadFamily.{0, uG, uKt, uL} X j g = 1 := hread
  refine carrierReadLaw_of_mult_agree X hr j (read_mult_of_read_one X j hread)
    (fun k => ?_) ?_
  · rw [hR, spb_unit_eq_one hcard ((arenaFamily.{0, uG, uKt, uL} X hr j).res k),
      Units.val_one]
  · rw [hR, spb_unit_eq_one hcard (Aℛ.node.peelUnitFamily j), Units.val_one]

/-! ## §4 ★★ The genre theorem: the site half from the bank family alone -/

/-- **[SPB §4] the wiring supply at the genre** — at wired card-2 levels the
per-realization `BankWiringSupply` residue closes from the bank family's own fields. -/
theorem bankWiringSupply_of_read_one_card (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ∀ j, DeepLive core.r j → ReadOneAt.{uG, uKt, uL} X j)
    (hcard : Nat.card Kt = 2) :
    BankWiringSupply.{uG, uKt, uL} X bF :=
  fun j hj => bankWiredAt_of_read_one_card X hj (bF j hj) (hread j hj) hcard

/-- ★ **[SPB §4] rows C0/C1 at the genre**: the full `SiteCalculusSupply` from the
tower-side bank family alone. -/
theorem siteCalculusSupply_of_bankFamily_read_one_card (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ∀ j, DeepLive core.r j → ReadOneAt.{uG, uKt, uL} X j)
    (hcard : Nat.card Kt = 2) :
    SiteCalculusSupply.{uG, uKt, uL} X :=
  siteCalculusSupply_of_bankFamily X bF
    (bankWiringSupply_of_read_one_card X bF hread hcard)

/-- ★ **[SPB §4] row C2 at the genre**: the carrier-read supply (hence WSS's
`LadderReadSupply`) closes with NO per-realization data beyond the genre pins. -/
theorem carrierReadSupply_of_read_one_card (X : RealizedInput core Aℛ)
    (hread : ∀ j, DeepLive core.r j → ReadOneAt.{uG, uKt, uL} X j)
    (hcard : Nat.card Kt = 2) :
    CarrierReadSupply.{uG, uKt, uL} X :=
  fun j hj => carrierReadLaw_of_read_one_card X _ j (hread j hj) hcard

/-- ★★ **[SPB §4] THE GENRE THEOREM** — at ANY arising realization of the wired card-2
genre (exported reads constantly `1` on the deep-live range; 2-element terminal field),
the deepTwist SITE HALF — WSS's full `WiredSiteSupply` — reduces to the TOWER-SIDE BANK
FAMILY ALONE: the per-realization wiring residue VANISHES at this genre.  Uniform in
the frame and the tower; the two genre pins are the only witness data consumed. -/
theorem wiredSiteSupply_of_bankFamily_read_one_card (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ∀ j, DeepLive core.r j → ReadOneAt.{uG, uKt, uL} X j)
    (hcard : Nat.card Kt = 2) :
    WiredSiteSupply.{uG, uKt, uL} X :=
  wiredSiteSupply_of_bank_carrierRead X
    (siteCalculusSupply_of_bankFamily_read_one_card X bF hread hcard)
    (carrierReadSupply_of_read_one_card X hread hcard)

/-- Corollary: the genre inputs fire the `GentowW` per-witness exporter (the WSS §3
chain's endpoint). -/
theorem gentowPerWitnessExporter_of_read_one_card (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hread : ∀ j, DeepLive core.r j → ReadOneAt.{uG, uKt, uL} X j)
    (hcard : Nat.card Kt = 2) :
    GentowPerWitnessExporter.{uG, uKt, uL} X :=
  gentowPerWitnessExporter_of_wiredSiteSupply X
    (wiredSiteSupply_of_bankFamily_read_one_card X bF hread hcard)

end Suppliers

/-! ## §5 The keystone fire and §6 the pack value teeth -/

section Wired

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

/-- **[SPB §5] the keystone genre pin**: every depth-4 keystone witness is of the
wired-read genre at every gauge-live level (`C136c0.s2Four_towerReadFamily_live`,
repackaged at the §1 interface). -/
theorem s2Four_readOneAt {j : ℕ} (hj : GaugeLive 4 j) :
    ReadOneAt.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) j :=
  fun g =>
    s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj g

/-- ★ **[SPB §5] `BankWiredAt` NAMED at the keystone** — the wiring law at the standalone
bank, assembled through the SPINE route (§1: genre pin + card-2 collapse + the bank's
OWN B-1 nonvanishing).  NO `GC13Wiring` instance is consumed — compare the landed
direct route `s2Four_gc13Wiring`, with which this agrees on the wired genre (the
coherence example below re-derives SCS's supply). -/
theorem s2Four_bankWiredAt (hj : DeepLive 4 3) :
    BankWiredAt.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      3 hj (s2FourSiteBank h2 hq) :=
  bankWiredAt_of_read_one_card
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    hj (s2FourSiteBank h2 hq)
    (s2Four_readOneAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive)
    (s2R7Fld_card h2 hq 4)

/-- **[SPB §5] the keystone bank FAMILY** — SCS's standalone `(h2, hq)`-only bank at the
unique deep-live level, in the shape `BankWiringSupply`/`siteCalculusSupply_of_bankFamily`
thread. -/
noncomputable def s2FourBankFamily :
    ∀ j, (hj : DeepLive (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).r j) →
      LevelSiteBank.{0}
        ((s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).T.trunc j hj.2.le) :=
  fun j hj => by
    have hj' : 3 ≤ j ∧ j < 4 := hj
    have hj3 : j = 3 := by omega
    subst hj3
    exact s2FourSiteBank h2 hq

/-- ★★ **[SPB §5] THE FIRST NAMED `BankWiringSupply` INSTANCE** — the per-realization
wiring residue of SCS's factorization, closed at every depth-4 keystone witness through
the spine route.  Conditionality: exactly the keystone's. -/
theorem s2Four_bankWiringSupply :
    BankWiringSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourBankFamily h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop) :=
  bankWiringSupply_of_read_one_card
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2FourBankFamily h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
    (fun j hj =>
      s2Four_readOneAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive)
    (s2R7Fld_card h2 hq 4)

/-- Coherence pin: the spine route re-derives SCS's keystone `SiteCalculusSupply`
(the factored normal form at the named family + the named wiring supply). -/
example :
    SiteCalculusSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  siteCalculusSupply_of_bankFamily
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2FourBankFamily h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_bankWiringSupply h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

/-- Coherence pin: the spine route re-derives LRS's keystone `CarrierReadSupply`
(kernel-agreement + peel tie through the §2 card-2 discharge). -/
example :
    CarrierReadSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  carrierReadSupply_of_read_one_card
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (fun j hj =>
      s2Four_readOneAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive)
    (s2R7Fld_card h2 hq 4)

/-- ★★ Coherence pin (charge 1's fire): the deepTwist SITE HALF at every depth-4
keystone witness through the SPINE ROUTE ALONE — the §4 genre theorem at the named bank
family and the two genre pins; agrees with the landed `s2Four_wiredSiteSupply` on the
wired genre. -/
example :
    WiredSiteSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  wiredSiteSupply_of_bankFamily_read_one_card
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2FourBankFamily h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
    (fun j hj =>
      s2Four_readOneAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive)
    (s2R7Fld_card h2 hq 4)

/-- Coherence pin: the chain's endpoint — the `GentowW` per-witness exporter through the
spine route (agrees with the landed `s2Four_gentowPerWitnessExporter`). -/
example :
    GentowPerWitnessExporter.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  gentowPerWitnessExporter_of_read_one_card
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2FourBankFamily h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
    (fun j hj =>
      s2Four_readOneAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive)
    (s2R7Fld_card h2 hq 4)

/-! ### §6 the pack value teeth — "the exports ARE the tower's own reads", made exact

The keystone tower packs (W3P/R4K: rungs 2/3/4, host field `(s2DepthTwo).fld 2`) export
`exact_ne` — nonvanishing of the read at every exact grade below the key fence.  In the
2-element host that pins the read's VALUE: constantly `1` on its lawful domain — the
SAME value the realization's wired export takes on the live range
(`s2Four_towerReadFamily_live`).  This is the exact sense in which the exports are the
tower's own reads: VALUEWISE agreement through the card-2 collapse, NOT `rfl` (the
export was wired to the constant `1` at construction, not to the pack reads; no
type-level hom from the pack host into the realization's `Kt` is landed or needed). -/

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- ★ **[SPB §6] the rung-2 pack read is constantly `1` on its lawful domain** — the
pack's own `exact_ne` (the R4K campaign's export) + the card-2 collapse. -/
theorem s2Rung2_read_eq_one {m : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < (I10rl3w.s2Rung2Pack h2 hq).P.key.natDegree)
    (hsupp : (I10rl3w.s2Rung2Pack h2 hq).C.supp g = (m : ℕ∞)) :
    (I10rl3w.s2Rung2Pack h2 hq).C.read m g = 1 :=
  spb_eq_one_of_ne_zero (s2Fld₂_card h2 hq)
    ((I10rl3w.s2Rung2Pack h2 hq).exact_ne hdeg hsupp)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- ★ **[SPB §6] the rung-3 pack read is constantly `1` on its lawful domain**. -/
theorem s2Rung3_read_eq_one {m : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < (I10rl3w.s2Rung3Pack h2 hq).P.key.natDegree)
    (hsupp : (I10rl3w.s2Rung3Pack h2 hq).C.supp g = (m : ℕ∞)) :
    (I10rl3w.s2Rung3Pack h2 hq).C.read m g = 1 :=
  spb_eq_one_of_ne_zero (s2Fld₂_card h2 hq)
    ((I10rl3w.s2Rung3Pack h2 hq).exact_ne hdeg hsupp)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- ★ **[SPB §6] the rung-4 (keystone-terminal) pack read is constantly `1` on its
lawful domain** — the last landed key's read takes exactly the wired export's value. -/
theorem s2Rung4_read_eq_one {m : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < (I10rl4.s2Rung4Pack h2 hq).P.key.natDegree)
    (hsupp : (I10rl4.s2Rung4Pack h2 hq).C.supp g = (m : ℕ∞)) :
    (I10rl4.s2Rung4Pack h2 hq).C.read m g = 1 :=
  spb_eq_one_of_ne_zero (s2Fld₂_card h2 hq)
    ((I10rl4.s2Rung4Pack h2 hq).exact_ne hdeg hsupp)

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.ReadOneAt
#print axioms Uniformity.Density.DeepExport.bankWiredAt_iff_of_read_one
#print axioms Uniformity.Density.DeepExport.bankWiredAt_of_read_one_card
#print axioms Uniformity.Density.DeepExport.carrierReadLaw_iff_of_read_one
#print axioms Uniformity.Density.DeepExport.carrierReadLaw_of_read_one_card
#print axioms Uniformity.Density.DeepExport.read_mult_of_read_one
#print axioms Uniformity.Density.DeepExport.bankWiringSupply_of_read_one_card
#print axioms Uniformity.Density.DeepExport.siteCalculusSupply_of_bankFamily_read_one_card
#print axioms Uniformity.Density.DeepExport.carrierReadSupply_of_read_one_card
#print axioms Uniformity.Density.DeepExport.wiredSiteSupply_of_bankFamily_read_one_card
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_read_one_card
#print axioms Uniformity.Density.DeepExport.s2Four_readOneAt
#print axioms Uniformity.Density.DeepExport.s2Four_bankWiredAt
#print axioms Uniformity.Density.DeepExport.s2FourBankFamily
#print axioms Uniformity.Density.DeepExport.s2Four_bankWiringSupply
#print axioms Uniformity.Density.DeepExport.s2Rung2_read_eq_one
#print axioms Uniformity.Density.DeepExport.s2Rung3_read_eq_one
#print axioms Uniformity.Density.DeepExport.s2Rung4_read_eq_one

end AxCheck
