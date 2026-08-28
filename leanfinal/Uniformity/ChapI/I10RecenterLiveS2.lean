/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RecenterLive
import Uniformity.ChapC.C130sg
import Uniformity.ChapC.C132fd0
import Uniformity.ChapC.C132sg2

/-!
# Uniformity.ChapI.I10RecenterLiveS2 — the S2-instance recenter-step export: the landed
prefix, and the named open (AMENDMENT A-I.7 step 5, unit AI7E, 2026-08-28)

The A-I.7 plan (`runs/wave-c/verdict_REX.md`, "Export design" + the cite mapping table)
requires the S2-instance `RecenterStep` export construction to land AS FAR AS THE LANDED
PRODUCER DATA ALLOWS, with anything genuinely missing becoming a NAMED OPEN — not a
forced proof.  The three declarations below are PROMOTED byte-for-byte from
`scratch/REX_probe.lean` ("Landed S2 prefix" section; Lean-core, exit 0, archived at
commit `05f067b7`).

## What the landed S2/μ₃ bank supplies (the prefix, machine-real below)

`S2LandedPrefix`: the depth-two chain, the full μ₃ source record + laws
(`C132fd0.s2SourceDataTwo` with `s2Mu3_hex`/`s2Mu3_hconv`), the exact carried key `Φ₂`,
its key-polynomialhood (`C132kp4.s2Mu3KeyPoly_Φ₂`), and monicity (`C132nv1.s2Φ₂_monic`).
And one NEGATIVE certificate: `s2LandedPrefix_tangentClass_impossible` — the only exact
key presently tied to the μ₃ source is the CARRIED tangent key itself, which fails GN15
Thm 2.3's `φ ≁_μ φ_r` hypothesis (`C132kp0.S2Mu3InitialEquiv_refl`), so the landed bank
cannot yet select a recentered successor at all.

## ⚠ NAMED OPEN — `S2-RECENTER-EXPORT` (the supply campaign's next node)

The GAP rows of REX's cite mapping table, none fabricated here: a recentered external
`B'` with an exact key ≁ the carried tangent key; the selected slope of `N⁻_{r+1}` with
its exact slope-residual interpretation; the selected prime factor `ψ` of the input
residual with multiplicity one; the exact GN leaf identification (`exactLeaf`); the
same-chain recentering equality under the SAME existential witness (C.110 has generic
shift algebra, no S2 successor export); and the peel core (`MP1StepCore`: no S2 successor
quotient/interface export is landed).  Until these land, NO `RecenterStep` instance
exists at the S2 socket — which is exactly why `MP1CarrierLive` stays honestly OPEN
there rather than machine-refuted.  Campaign ledger:
`docs/in-progress/LADDER_SUPPLY_2026-08-27.md` ([AI7E] entry).

Statement provenance: all three bodies byte-identical to `scratch/REX_probe.lean`
(machine byte-diff at enactment: `runs/wave-c/verdict_AI7E.md`).  Zero `sorry`, zero new
axiom; AxChk footer expects Lean core only.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uW uG uKt uL uR

/-! ## §1 Landed S2 prefix: the exact point where the full export stops -/

/-- The part of a cite payload that the landed S2/μ₃ bank really supplies. -/
structure S2LandedPrefix {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) where
  source : Tower.FGMNSourceData
    (Tower.C130s17.S2DepthTwo h2 hq)
    (Tower.C130s2.s2DepthTwoKeyChain h2 hq) 2 1 21
  source_eq : source = Tower.C132fd0.s2SourceDataTwo h2 hq
  sourceLaws : Nonempty (Tower.FGMNSourceLaws
    (Tower.C130s17.S2DepthTwo h2 hq)
    (Tower.C130s2.s2DepthTwoKeyChain h2 hq) 2 1 21 source)
  exactKey : Polynomial O
  exactKey_eq : exactKey = Tower.C130s2.s2DepthTwoKeyAt h2 hq 2
  keyPolynomial : source.keyPolynomial exactKey
  monic : exactKey.Monic

/-- S2 supplies the depth-two chain, μ₃ source record, and key-polynomialhood of `Φ₂`.
It does not supply a recentered external `B'`, tangent non-equivalence, a selected slope/factor
of the input residual with multiplicity one, the exact GN leaf identification, or the peel core.
-/
noncomputable def s2LandedPrefix {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) : S2LandedPrefix h2 hq where
  source := Tower.C132fd0.s2SourceDataTwo h2 hq
  source_eq := rfl
  sourceLaws := ⟨Tower.C132fd0.s2SourceLawsTwo_of h2 hq
    (Tower.C132rp10b.s2Mu3_hex h2 hq) (Tower.C132kp6b.s2Mu3_hconv h2 hq)⟩
  exactKey := Tower.C130s2.s2DepthTwoKeyAt h2 hq 2
  exactKey_eq := rfl
  keyPolynomial := Tower.C132kp4.s2Mu3KeyPoly_Φ₂ h2 hq
  monic := Tower.C132nv1.s2Φ₂_monic h2 hq

/-- The only exact key presently tied to the S2 μ₃ source is the carried tangent key itself,
so it fails GN15's required `phi`-not-equivalent-to-`phi_r` hypothesis. -/
theorem s2LandedPrefix_tangentClass_impossible {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    ¬ (¬ (Tower.C132fd0.s2SourceDataTwo h2 hq).initialEquiv
      (Tower.C130s2.s2DepthTwoKeyAt h2 hq 2)
      ((Tower.C130s2.s2DepthTwoKeyChain h2 hq).keyAt 2)) := by
  intro hne
  apply hne
  exact Tower.C132kp0.S2Mu3InitialEquiv_refl h2 hq _

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only. -/

#print axioms Uniformity.Density.IFC5.S2LandedPrefix
#print axioms Uniformity.Density.IFC5.s2LandedPrefix
#print axioms Uniformity.Density.IFC5.s2LandedPrefix_tangentClass_impossible
