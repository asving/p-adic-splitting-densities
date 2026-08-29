/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10Universal

/-!
# Uniformity.ChapI.I10Suppliers — USUP: the two universal suppliers at general witnesses,
scoped against every arising realization's own data [USUP 2026-08-29]

**Unit USUP** — the remaining leg of the capstone `deepTwist` field after G10U's exit gate
(`deepTwistField_iff_universalPerWitness`): the two universal suppliers
(`UniversalVarthetaSupplier` / `UniversalGentowSupplier`) at GENERAL arising witnesses.
Charge 1 (scope) is settled here as machine-checked theorems where the answer is
"derivable", and as named minimal `Prop`s + proved reductions where it is not.

## The scope verdict (charge 1)

Can the C3 tau-letter source and the G3 site package be CONSTRUCTED from an arbitrary
arising realization's own fields (`receiver`/`keys`/`normalizer`/`node` + the
`RealizedInput` view equalities), the way the keystone instances were built?

* **Vartheta leg** (`CanonicalTauLetterSource`, four fields):
  - `view` — **DERIVABLE**: `X.gaugeFamilyViewEq` is a producing equality carried by
    EVERY `RealizedInput` (C130vw), and at the canonical socket (`eG = MulEquiv.refl`)
    it is definitionally the demanded transported view (the keystone instance's own
    pattern, now used generically).
  - `tau_mem` — **DERIVABLE**: `canonical_tau_mem` (C136c0 Part A, already stated at
    every witness) + the `gaugeHeightFamily` live-index `dif_pos` collapse.  The
    keystone's `s2Four_tau_mem` proof was generic in shape; only its binders were
    witness-specific.  Landed here as `canonical_tau_mem_family` (§1).
  - `tau_word` — **NOT derivable**: at the keystone it held with `m = 0, t = 0` only
    because the level-3 canonical read is constantly `1` (the card-2 collapse
    `s2CanonicalReadFour3_eq_one`).  Generally this is the triangular-spanning research
    row **C3** (DWR §11.5: "research, 5–12 working days").  Named here as
    `CanonicalTauWordAt` (§2).
  - `generator_descent` — **NOT derivable**: nothing in a general realization ties the
    canonical values `wrapValue`/`letterValue : Lˣ` to the image of `Ktˣ` (at the
    keystone every unit is `1`, which descends trivially).  Row **R5** (OPEN-LETTERS).
    The landed `CanonicalGeneratorDescent` is reused verbatim — no new name.
* **`GentowW` leg** (G3 site package + the three consumer dictionaries): **NOT
  derivable, structurally** — the post-PK/U15 `ChainRealization` carries
  `receiver`/`keys`/`normalizer`/`node` ONLY; the FGMN legs and the `(e', f', u')`
  parameters were deliberately factored out into the standalone packaging map
  `fgmnCalculusOf`.  No field of a general realization supplies the site calculus, the
  `GENTOW5WCleared` law (rows **C0/C1**), the GC-13 wiring, or the theta/peel/range
  dictionaries (row **C2** = GCW-4/GCW-5 at general residue cardinality).  At the
  keystone ALL of these came from the landed μ₄ operator bank (the D3 stack) plus the
  card-2 collapses.  Named here as `WiredSiteSupply` (§3) — verbatim the landed
  compiler's hypothesis shape, so the reduction is exact by construction.

## What lands (charges 2/3)

* **§1 the generic legs as theorems**: `canonical_tau_mem_family` — tau membership at
  every witness's own exported height family, every gauge-live level (the `tau_mem`
  field of C3's record is FREE at every arising realization).
* **§2 the vartheta reduction** (the new theorem content): `CanonicalTauWordAt` (row
  C3's exact remaining content as a per-realization `Prop`), and
  ★ `canonicalTauLetterSource_of_word_descent` — the FULL C3 record from `tau_word` +
  `CanonicalGeneratorDescent` ALONE, the `view`/`tau_mem` legs supplied generically.
  The landed compiler (`varthetaPerWitnessExporter_of_tauSources`) demanded all four
  fields; after this unit the vartheta supplier's open boundary is 2 of 4 fields.
  `TauWordDescentSupply` + `varthetaPerWitnessExporter_of_tauWordDescent` package the
  per-witness form.
* **§3 the `GentowW` missing datum named**: `WiredSiteSupply` (per-realization: the
  ∃-site + three dictionaries at every deep-live level) and its one-line reduction
  `gentowPerWitnessExporter_of_wiredSiteSupply`.  Nothing smaller is honest: without a
  calculus field on `ChainRealization` there is no partial generic construction.
* **§4 the universal supply forms and the capstone reduction**:
  `UniversalTauWordDescentSupply n` / `UniversalWiredSiteSupply n`, their supplier
  compilations, and ★ `deepTwistField_of_supplies` — the capstone `deepTwist` field
  from the two named supply `Prop`s, through G10U's fully-polymorphic assembly
  direction.  **SUFFICIENT only, no converse claimed**: the exact boundary remains
  `deepTwistField_iff_universalPerWitness`; these supplies are the constructive route
  the campaign rows C1/C2/C3/R5 would discharge.
* **§5 keystone nonvacuity + vacuity teeth**: the new supply `Prop`s are inhabited at
  EVERY depth-4 keystone witness (`s2Four_canonicalTauWordAt`,
  `s2Four_tauWordDescentSupply`, `s2Four_wiredSiteSupply` — full parametric payload),
  and hold vacuously at depth `r ≤ 3` (the shallow teeth), so their content sits
  exactly at the deep witnesses the campaign is about.

## Honesty scope

**The capstone `deepTwist` field does NOT close in this unit.**  Per the landed iff, the
gap IS the field.  What remains open, now at its minimal named boundary, per arising
realization and deep-live level:

1. `CanonicalTauWordAt` (row C3) — the canonical read of every tau class is a word in
   the realization's own canonical generators.  Genuinely new general-depth mathematics
   (triangular spanning); NOT keystone-threshold-like — the keystone discharged it by
   the card-2 collapse, which no general residue cardinality inherits.
2. `CanonicalGeneratorDescent` (row R5, OPEN-LETTERS) — the canonical generator values
   descend to `Ktˣ`.  Parametric in FORM (a per-level descent datum), research in
   content: at general witnesses the descent is the open same-receiver letter theory.
3. `WiredSiteSupply` (rows C0/C1/C2) — a positive cleared FGMN site with wiring and the
   theta/peel/range dictionaries at every deep-live level.  Genuinely new: per-level
   operator banks at general towers (the L2E-genre engine) plus GCW-4/GCW-5 at general
   residue cardinality.

No statement is weakened: the suppliers' quantifier discipline, the socket views, and
the landed record shapes are consumed verbatim; the reductions only REORDER what was
already demanded (and §2 strictly shrinks the demanded surface, never the concluded
one).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`CanonicalTauWordAt`, `TauWordDescentSupply`, `WiredSiteSupply`,
`UniversalTauWordDescentSupply`, `UniversalWiredSiteSupply` (supplier-side interface
`Prop`s below the signed surface; no leanspec name touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_USUP.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

section Suppliers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-! ## §1 The generic legs: what every arising realization already supplies -/

/-- **[USUP §1] Tau membership at the witness's own exported height family is FREE at
every arising realization** — the generic form of the keystone's `s2Four_tau_mem`: the
exported family collapses to `levelHeight` at every gauge-live index (`dif_pos`), where
the landed `canonical_tau_mem` fires from the normalizer's `exact_height`.  This is the
`tau_mem` field of C3's `CanonicalTauLetterSource`, derived from the realization's own
data — one of the two generically-derivable fields (with `view`; see
`canonicalTauLetterSource_of_word_descent`). -/
theorem canonical_tau_mem_family (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j) (a b : ℤ) :
    (((Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau
        a b : GaugeLattice.{uG} core.r)) ∈
      MonoidHom.ker (gaugeHeightFamily X j) := by
  have hker : gaugeHeightFamily X j
      = (levelHeight core.T ⟨j, hj⟩ :
          GaugeLattice.{uG} core.r →* Multiplicative ℤ) := by
    simp only [gaugeHeightFamily]
    rw [dif_pos hj]
  rw [hker]
  exact canonical_tau_mem X hj a b

/-! ## §2 The vartheta reduction: rows C3/R5 as the EXACT per-realization boundary -/

/-- **[USUP §2] Row C3's exact remaining content as a per-realization `Prop`** — the
canonical read of every tau class at level `j` is a word in the realization's own
canonical generator values (C130cr's `wrapValue`/`letterValue`).  This is the `tau_word`
field of `CanonicalTauLetterSource` at the canonical socket, isolated: at the keystone
it holds with `m = 0, t = 0` by the card-2 collapse (§5); at general witnesses it is
the OPEN triangular-spanning row C3.  NEW STATEMENT (review). -/
def CanonicalTauWordAt (X : RealizedInput core Aℛ) (j : ℕ) (hj : GaugeLive core.r j) :
    Prop :=
  ∀ s : ℕ, ∃ (m : ℤ) (t : Fin (j - 1) → ℤ),
    canonicalResFamily.{0, uKt, uL, uG} X j
        ⟨(Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau
            ((s : ℤ) * useHeightFamily X j) (useHeightFamily X j),
          canonical_tau_mem_family X hj _ _⟩ =
      Aℛ.node.wrapValue hj.stageLive ^ m *
        ∏ a, Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a ^ t a

/-- ★ **[USUP §2] THE VARTHETA REDUCTION** — the FULL C3 `CanonicalTauLetterSource` at
the canonical socket from `tau_word` + `CanonicalGeneratorDescent` ALONE: the `view`
leg is the realization's own producing equality (`X.gaugeFamilyViewEq`), and the
`tau_mem` leg is §1's generic theorem.  The landed compiler demanded all four fields;
after this theorem the vartheta supplier's open boundary is exactly rows C3 + R5. -/
theorem canonicalTauLetterSource_of_word_descent (X : RealizedInput core Aℛ)
    {j : ℕ} (hj : GaugeLive core.r j)
    (hword : CanonicalTauWordAt.{uG, uKt, uL} X j hj)
    (hdesc : CanonicalGeneratorDescent Aℛ j hj) :
    CanonicalTauLetterSource X (GaugeLattice.{uG} core.r) (MulEquiv.refl _)
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) j hj where
  view := X.gaugeFamilyViewEq
  tau_mem := fun s => canonical_tau_mem_family X hj _ _
  tau_word := hword
  generator_descent := hdesc

/-- **[USUP §2] The per-witness tau supply** — rows C3 + R5 at every deep-live level of
one realization: the minimal missing vartheta datum, per-realization (NOT
per-witness-genre).  NEW STATEMENT (review). -/
def TauWordDescentSupply (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    CanonicalTauWordAt.{uG, uKt, uL} X j hj.gaugeLive ∧
      CanonicalGeneratorDescent Aℛ j hj.gaugeLive

/-- The vartheta per-witness exporter from the tau supply (through §2's reduction and
the landed generic compiler). -/
theorem varthetaPerWitnessExporter_of_tauWordDescent (X : RealizedInput core Aℛ)
    (h : TauWordDescentSupply.{uG, uKt, uL} X) :
    VarthetaPerWitnessExporter.{uG, uKt, uL} X :=
  varthetaPerWitnessExporter_of_tauSources X fun j hj =>
    canonicalTauLetterSource_of_word_descent X hj.gaugeLive (h j hj).1 (h j hj).2

/-- Vacuity tooth: at depth `r ≤ 3` the tau supply holds vacuously — its content sits
exactly at deep witnesses. -/
theorem tauWordDescentSupply_of_shallow (X : RealizedInput core Aℛ)
    (hr : core.r ≤ 3) : TauWordDescentSupply.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

/-! ## §3 The `GentowW` missing datum: rows C0/C1/C2 as the per-realization boundary -/

/-- **[USUP §3] The per-witness wired-site supply** — rows C0/C1 (the positive cleared
FGMN site with its own-export wiring) + C2 (the theta/peel/range dictionaries) at every
deep-live level of one realization: the minimal missing `GentowW` datum,
per-realization.  This is VERBATIM the landed compiler's hypothesis shape
(`gentowPerWitnessExporter_of_sites`), recorded as a named `Prop` because the scope
finding is structural: the post-PK/U15 `ChainRealization` carries NO calculus field, so
no strictly smaller per-realization datum exists to reduce to.
NEW STATEMENT (review). -/
def WiredSiteSupply (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    ∃ S : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le,
      ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S ∧
      PeelCompatibleAt X S ∧
      RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S

/-- The `GentowW` per-witness exporter from the wired-site supply (the landed generic
compiler, verbatim — the reduction is exact by construction). -/
theorem gentowPerWitnessExporter_of_wiredSiteSupply (X : RealizedInput core Aℛ)
    (h : WiredSiteSupply.{uG, uKt, uL} X) :
    GentowPerWitnessExporter.{uG, uKt, uL} X :=
  gentowPerWitnessExporter_of_sites X h

/-- Vacuity tooth: at depth `r ≤ 3` the wired-site supply holds vacuously. -/
theorem wiredSiteSupply_of_shallow (X : RealizedInput core Aℛ)
    (hr : core.r ≤ 3) : WiredSiteSupply.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

end Suppliers

/-! ## §4 The universal supply forms and the capstone reduction -/

/-- **[USUP §4] The universal tau supply**: rows C3 + R5 at EVERY arising realization of
degree `n` — all `O/Kt/E/L`, every `ChainRealization`, every `RealizedInput`.
NEW STATEMENT (review). -/
def UniversalTauWordDescentSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    TauWordDescentSupply.{uG, uKt, uL} X

/-- **[USUP §4] The universal wired-site supply**: rows C0/C1/C2 at EVERY arising
realization of degree `n`.  NEW STATEMENT (review). -/
def UniversalWiredSiteSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    WiredSiteSupply.{uG, uKt, uL} X

/-- The universal tau supply compiles to G10U's universal vartheta supplier. -/
theorem universalVarthetaSupplier_of_tauSupply {n : ℕ}
    (h : UniversalTauWordDescentSupply.{uG, uKt, uL} n) :
    UniversalVarthetaSupplier.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X
  exact varthetaPerWitnessExporter_of_tauWordDescent X (h O Kt E L core Aℛ X)

/-- The universal wired-site supply compiles to G10U's universal `GentowW` supplier. -/
theorem universalGentowSupplier_of_siteSupply {n : ℕ}
    (h : UniversalWiredSiteSupply.{uG, uKt, uL} n) :
    UniversalGentowSupplier.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X
  exact gentowPerWitnessExporter_of_wiredSiteSupply X (h O Kt E L core Aℛ X)

/-- ★ **[USUP §4] THE CAPSTONE REDUCTION** — the capstone `deepTwist` field at degree
`n` from the two named universal supply `Prop`s, at every universe profile (G10U's
fully-polymorphic assembly direction).  SUFFICIENT ONLY — no converse is claimed: the
exact boundary remains `deepTwistField_iff_universalPerWitness`, and per that iff the
gap left open by this unit (the supplies at general witnesses, rows C1/C2/C3/R5) IS the
field. -/
theorem deepTwistField_of_supplies {n : ℕ}
    (hv : UniversalTauWordDescentSupply.{uG, uKt, uL} n)
    (hw : UniversalWiredSiteSupply.{uG, uKt, uL} n) :
    IFC0.DeepTwistField.{uG, uKt, uL} n :=
  deepTwistField_of_universalPerWitness
    (universalVarthetaSupplier_of_tauSupply hv)
    (universalGentowSupplier_of_siteSupply hw)

/-! ## §5 Keystone nonvacuity and the wired-genre instances of the supply `Prop`s -/

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

/-- **[USUP §5] Row C3's isolated `tau_word` clause at EVERY depth-4 keystone witness**
(`m = 0, t = 0` — the level-3 canonical read is constantly `1`, the card-2 collapse).
This is the nonvacuity tooth of `CanonicalTauWordAt`: the S2 collapse is exactly what a
general residue cardinality does NOT inherit. -/
theorem s2Four_canonicalTauWordAt (hj : GaugeLive 4 3) :
    CanonicalTauWordAt.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj := by
  intro s
  refine ⟨0, 0, ?_⟩
  refine (s2Four_canonicalResFamily_eq_one h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock
    hcop hj
    (canonical_tau_mem_family
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj _ _)
    (canonical_tau_mem
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      hj _ _)).trans ?_
  simp

/-- ★ **[USUP §5] The tau supply at EVERY depth-4 keystone witness** — the per-witness
minimal vartheta datum is inhabited at the whole wired genre (`DeepLive 4 j` forces
`j = 3`; descent = the keystone's `s2Four_canonicalGeneratorDescent`).  Conditionality:
exactly the keystone's. -/
theorem s2Four_tauWordDescentSupply :
    TauWordDescentSupply.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact ⟨s2Four_canonicalTauWordAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive,
    s2Four_canonicalGeneratorDescent h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive⟩

/-- ★ **[USUP §5] The wired-site supply at EVERY depth-4 keystone witness** — the C0
site with the three C2 dictionaries, packaged in the new per-realization shape.
Conditionality: exactly the keystone's. -/
theorem s2Four_wiredSiteSupply :
    WiredSiteSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact ⟨s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj,
    s2Four_thetaCompatibleAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj,
    s2Four_peelCompatibleAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj,
    s2Four_rangeCompleteAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj⟩

/-- Coherence pin: the two keystone supplies re-derive both per-witness exporters
through the NEW reductions (the supply route and the landed direct route agree on the
wired genre). -/
example :
    VarthetaPerWitnessExporter.{uG, 0, uL}
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) ∧
      GentowPerWitnessExporter.{0, 0, uL}
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  ⟨varthetaPerWitnessExporter_of_tauWordDescent _
      (s2Four_tauWordDescentSupply h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop),
    gentowPerWitnessExporter_of_wiredSiteSupply _
      (s2Four_wiredSiteSupply h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)⟩

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.canonical_tau_mem_family
#print axioms Uniformity.Density.DeepExport.CanonicalTauWordAt
#print axioms Uniformity.Density.DeepExport.canonicalTauLetterSource_of_word_descent
#print axioms Uniformity.Density.DeepExport.TauWordDescentSupply
#print axioms Uniformity.Density.DeepExport.varthetaPerWitnessExporter_of_tauWordDescent
#print axioms Uniformity.Density.DeepExport.tauWordDescentSupply_of_shallow
#print axioms Uniformity.Density.DeepExport.WiredSiteSupply
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_wiredSiteSupply
#print axioms Uniformity.Density.DeepExport.wiredSiteSupply_of_shallow
#print axioms Uniformity.Density.DeepExport.UniversalTauWordDescentSupply
#print axioms Uniformity.Density.DeepExport.UniversalWiredSiteSupply
#print axioms Uniformity.Density.DeepExport.universalVarthetaSupplier_of_tauSupply
#print axioms Uniformity.Density.DeepExport.universalGentowSupplier_of_siteSupply
#print axioms Uniformity.Density.DeepExport.deepTwistField_of_supplies
#print axioms Uniformity.Density.DeepExport.s2Four_canonicalTauWordAt
#print axioms Uniformity.Density.DeepExport.s2Four_tauWordDescentSupply
#print axioms Uniformity.Density.DeepExport.s2Four_wiredSiteSupply

end AxCheck
