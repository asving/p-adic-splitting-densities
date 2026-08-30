/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10SiteSupply

/-!
# Uniformity.ChapI.I10SiteCalc — SCS: the site-calculus supply dissected against the
frame-generic L2E engine; the bank/wiring factorization [SCS 2026-08-30]

**Unit SCS** — the per-field verification of WSS's working hypothesis
("`SiteCalculusSupply` is exactly what the frame-generic L2E engine produces"), and the
exact factorization of the supply into its tower-side and realization-side halves.

## Charge 1 — the per-field dissection (VERDICT: the hypothesis is TRUE in FORM for the
bank half, and needs TWO corrections in substance)

`SiteCalculusSupply X` (WSS §2) demands, per deep-live level `j`: a positive triple
`(e', f', u')`, an `FGMNCalculus` on `core.T.trunc j`, the four B-1 normalizer supplies,
and the own-export `GC13Wiring` leg.  Field by field, against the landed corpus:

* **The triple `(e', f', u')`, `0 < f'`** — no landed generic assignment.  The natural
  candidate is the tower's own rung data (`DeepTower` carries `e f u : ℕ → ℕ` as data
  fields, C83); the keystone pin `(2, 1, 85)` is the S2 tower's depth-4 rung.  Parametric
  in form; part of the bank datum below.
* **`I : FGMNCalculus (core.T.trunc j) e' f' u'`** — NOT generically producible, by the
  standing C92_VACUITY adjudication (C130pk: "there is still no faithful theorem from a
  bare `DeepTower` to `Nonempty (FGMNCalculus …)`"; structurally: `KeyChain` demands monic
  keys of degree `Dcum` but NOT irreducibility, while `KP_keyAt + KP_irred` force the top
  key irreducible — genuine arithmetic content a bare tower does not carry).  The
  packaging map `fgmnCalculusOf` (KeyChain + FGMNSourceData + FGMNSourceLaws → calculus)
  IS generic; the operators and laws are per-frame.  **Where the S2 frame enters the
  keystone bank, exactly** (provenance audit, 2026-08-30, this unit):
  - the seven operators of `C136c0.s2SiteSourceData` are the S2 μ₄ bank (`s2Hgt₄`,
    `s2Mu4GradedRes`, `s2Mu4NormRes`, `S2Mu4PrevGrade`, `S2Mu4KeyPoly`,
    `S2Mu4InitialEquiv`, the card-2 constant-`1` letter `s2SiteLetter`);
  - of the thirteen source-law suppliers in `C136c0.s2SiteSourceLaws`, FIVE
    (`s2Mu4_graded_mul`, `s2Mu4NormRes_mul`, `s2Mu4_hex`, `s2Mu4_key_criterion`,
    `s2Mu4KeyPoly_g8`) consume the L2E layer, and every such path funnels through the
    SINGLE declaration `C136l2e4.s2Mu4Coeff_mul` — the S2-pinned `(85, 2)` fixed-grade
    coefficient convolution, proved through the μ₃ mirror `s2Mu3GradedRes`, NOT through
    the generic engine;
  - the generic counterpart of that one lemma is REFUTED as stated: the unweighted
    fixed-grade read law (`hconv`) fails at the bare normalized carrier
    (`C136l2e4.fixedGrade_unweighted_add_forces_letter_one` — L2E4's adjudication; the
    honest generic law is the WEIGHTED absolute-read convolution), and the
    `LevelDatum` depth-adapter D3-03 is absent (L2E3 RED);
  - two suppliers are S2-parity artifacts outright: `s2Mu4_normalized_recipe` is
    discharged by VACUITY (grade 85 is odd; every exact μ₄ grade below degree 8 is even
    — at a general frame the recipe law has genuine content), and
    `letter_ne_zero := one_ne_zero` reads the card-2 letter;
  - the remaining suppliers are μ₃-mirror/coefficient bookkeeping (S2 computation, no
    L2E).
  So: the frame-generic L2E engine (`C136l2e0`–`l2e3`, verified 100% `LevelDatum`-rooted
  with no S2 mention) supplies the level-2 multiplicative VOCABULARY of the source laws,
  but the landed generic layer does NOT yet produce a calculus at a general tower — the
  remaining L2E program work (weighted convolution carrier + depth adapter + key lifting)
  is mathematics, not transcription.  **Correction 1 to the hypothesis.**
* **The four B-1 supplies** (`PrevGrade` at `f' ≥ 2`; exact grade, degree-below-key,
  nonvanishing of `chainNormBelow` at the window grades) — generic IN FORM (stated at an
  arbitrary calculus; they are verbatim the cleared engine's input, machine-pinned by
  `LevelSiteBank.cleared` below).  The keystone discharge is S2-numeral: the exponent
  solve `s2Trunc_towerNorm_two_eighty_five` (`towerNorm 2 85 = (8, 0, ![0, 1])`), the
  grade-170 tooth, `4 < 8`, and the `f' = 1` vacuity of the `PrevGrade` leg.  No landed
  generic supplier; owned by the same bank program.
* **`GC13Wiring`** — NOT a tower-side product AT ALL: the law couples the realization's
  OWN exports (`towerReadFamily X`, `useHeightFamily X`, `Aℛ.receiver.levelHom`) to the
  calculus; it is per-realization BY DESIGN (IFC3's D-D12 anti-cook signing; the IFC3
  module fence records that no universal wired supplier is statable today, and
  `IFC3.s2_wiring_refuted_at_landed_exports` machine-pins that the law is FALSE at the
  landed zero-read witness — the leg carries genuine information about `X`).  No L2E
  (tower-side) engine can produce it.  **Correction 2 to the hypothesis**: the wiring leg
  belongs with `LadderReadSupply`'s per-realization export-coherence character, not with
  the bank.

**Consequence, stated prominently: `UniversalSiteCalculusSupply n` does NOT fire in this
unit** — and cannot fire from any tower-side engine alone, because of the wiring leg.
What this unit lands instead is the exact factorization along the fault line found above.

## Charges 2/3 — what lands (namespace `Uniformity.Density.DeepExport`)

* **§1 `LevelSiteBank`** (NEW STATEMENT, review) — the tower-side bank DATUM: one
  positive triple + calculus + the four B-1 supplies at a bare `DeepTower`, no
  realization, no `q`, no `Kt`-side data.  Generic teeth: ★ `LevelSiteBank.cleared` (the
  bank fires the landed general-depth cleared engine — the machine pin that the bank
  fields are EXACTLY the L2E-genre engine's demanded output), `baseRead_ne_zero`,
  `thetaRatioCleared_one`, and the `f' = 1` constructor
  `levelSiteBank_of_inertia_trivial` (the keystone genre: `PrevGrade` leg vacuous, the
  three window clauses collapse to `d = 1`).
* **§2 the factorization**: `BankWiredAt` (NEW STATEMENT, review — the per-realization
  residue: ONE read law at a given bank, no calculus data, no B-1 clause), ★
  `siteCalculusSupply_iff_wiredBank` — an IFF (unlike WSS/USUP's sufficient-only
  reductions, this one is exact: the supply IS "per level, some bank, wired"), ★
  `siteCalculusSupply_of_bankFamily` (the factored normal form: bank FAMILY as data +
  `BankWiringSupply`, the strictly smaller per-realization remainder), and the honest
  `TowerBankSupply` (the tower-side research Prop, with its shallow-vacuity tooth).
  `LevelSiteBank.toWleExport`: bank + wiring + nothing else already assembles the full
  G3 site package (the "`WleCleared` truncation exporter" of IFC3's fence, at the bank
  interface).
* **§3 wrappers**: bank family + wiring + ladder law ⟹ `WiredSiteSupply` and the
  `GentowW` per-witness exporter (through WSS §3).
* **§4 universal forms**: `UniversalWiredBankSupply n` (NEW STATEMENT, review) + ★ the
  universal IFF with WSS's `UniversalSiteCalculusSupply n`.
* **§5 keystone nonvacuity + THE CONDITIONALITY SPLIT**: `s2FourSiteBank` — the keystone
  bank as a standalone tower-side datum whose conditionality is `(h2, hq)` ALONE (no
  witness thresholds, no `IsAdicComplete`, no R8r payload); the wiring instance carries
  the full witness payload (`s2Four_siteCalculusSupply_of_bank` re-derives WSS's keystone
  supply through the new factorization).  The split makes the two halves' costs visible:
  the bank is frame data, the wiring is witness data.

## Honesty scope

The named remainder after this unit, per arising realization (both strictly smaller than
`SiteCalculusSupply`, jointly EXACTLY it — the §2 iff):

| leftover | side | discharging math | character |
|---|---|---|---|
| a `LevelSiteBank` family at the tower's deep-live truncations | tower | the L2E program's remaining generic work: the weighted absolute-read convolution carrier (L2E4's adjudication), the D3-03 depth adapter, key lifting at general frames, and the B-1 normalizer-grade computation | research (DWR §11.7); parametric in FORM |
| `BankWiringSupply` at that family | realization | the GC-13 read law on the realization's own exports at the bank's calculus | per-realization export coherence (same character as `LadderReadSupply`); ONE equation family per level |

No statement is weakened: `SiteCalculusSupply` is consumed verbatim on both sides of an
iff; every new declaration sits on the hypothesis side of proved reductions or is a
repackaging pinned by that iff.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`LevelSiteBank`, `BankWiredAt`, `BankWiringSupply`, `TowerBankSupply`,
`UniversalWiredBankSupply` (supplier-side interface shapes below the signed surface; no
leanspec name touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_SCS.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

/-! ## §1 The tower-side bank datum and its generic teeth -/

section Bank

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
  {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- **[SCS §1] The tower-side site bank** — the per-level datum whose per-level existence
is EXACTLY the tower-side half of WSS's `SiteCalculusSupply` (the §2 iff): one positive
triple, one site calculus, and the four B-1 normalizer supplies, at a bare `DeepTower` —
no realization, no exports, no residue-cardinality assumption.  This is the L2E-genre
bank program's per-level output shape (research half); its fields are verbatim the
cleared engine's input (`LevelSiteBank.cleared`).  NEW STATEMENT (review). -/
structure LevelSiteBank (W : DeepTower.{0, uKt} F H₀ hpin r) where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  calculus : FGMNCalculus W e' f' u'
  f_pos : 0 < f'
  prev : 2 ≤ f' → calculus.PrevGrade (e' * u')
  norm_grade : ∀ d, 0 < d → d ≤ f' →
    calculus.ExactGrade (e' * (d * u')) (calculus.chainNormBelow r (d * u'))
  norm_deg : ∀ d, 0 < d → d ≤ f' →
    (calculus.chainNormBelow r (d * u')).natDegree < (calculus.keyAt r).natDegree
  norm_ne : ∀ d, 0 < d → d ≤ f' → calculus.chainNormBelow r (d * u') ≠ 0

variable {W : DeepTower.{0, uKt} F H₀ hpin r}

/-- ★ **[SCS §1] the bank fires the cleared engine** — the machine pin of WSS's genre
claim: the bank's fields are EXACTLY the input of the landed general-depth cleared law
(`C136c0.gentow5w_cleared_of_B1`, engine `C132sg3.ratio_power_law_cleared`), uniform in
the residue cardinality and the depth. -/
theorem LevelSiteBank.cleared (B : LevelSiteBank.{uKt} W) :
    GENTOW5WCleared W B.e' B.f' B.u' B.calculus :=
  Tower.C136c0.gentow5w_cleared_of_B1 W B.e' B.f' B.u' B.calculus B.f_pos B.prev
    B.norm_grade B.norm_deg B.norm_ne

/-- **[SCS §1] the base read at the bank is nonzero** (the canonical cleared witness;
`Rgr_ne_zero` at the `d = 1` window clause). -/
theorem LevelSiteBank.baseRead_ne_zero (B : LevelSiteBank.{uKt} W) :
    B.calculus.Rgr (B.e' * B.u') (B.calculus.chainNormBelow r B.u') ≠ 0 := by
  have h := B.calculus.Rgr_ne_zero (B.e' * (1 * B.u'))
    (B.calculus.chainNormBelow r (1 * B.u'))
    (B.norm_grade 1 one_pos B.f_pos) (B.norm_deg 1 one_pos B.f_pos)
    (B.norm_ne 1 one_pos B.f_pos)
  simp only [one_mul] at h
  exact h

/-- **[SCS §1] `thetaRatioCleared 1 = 1` at any bank** — WSS §1's general-`q` lemma, now
supplied by the bank's own B-1 clauses (no card-2 input anywhere). -/
theorem LevelSiteBank.thetaRatioCleared_one (B : LevelSiteBank.{uKt} W) :
    B.calculus.thetaRatioCleared 1 = 1 :=
  thetaRatioCleared_one_of_ne_zero B.calculus B.baseRead_ne_zero

/-- **[SCS §1] the `f' = 1` constructor** (the keystone genre — trivial residual inertia):
the `PrevGrade` leg is vacuous and the three window clauses collapse to their `d = 1`
instances. -/
def levelSiteBank_of_inertia_trivial {e' u' : ℕ} (I : FGMNCalculus W e' 1 u')
    (hgrade : I.ExactGrade (e' * u') (I.chainNormBelow r u'))
    (hdeg : (I.chainNormBelow r u').natDegree < (I.keyAt r).natDegree)
    (hne : I.chainNormBelow r u' ≠ 0) :
    LevelSiteBank.{uKt} W where
  e' := e'
  f' := 1
  u' := u'
  calculus := I
  f_pos := one_pos
  prev := fun hcon => absurd hcon (by norm_num)
  norm_grade := by
    intro d hd hd1
    have hd' : d = 1 := by omega
    subst hd'
    simpa only [one_mul] using hgrade
  norm_deg := by
    intro d hd hd1
    have hd' : d = 1 := by omega
    subst hd'
    simpa only [one_mul] using hdeg
  norm_ne := by
    intro d hd hd1
    have hd' : d = 1 := by omega
    subst hd'
    simpa only [one_mul] using hne

/-- **[SCS §2] The tower-side research Prop** — per-level bank existence at the tower's
deep-live truncations: the exact tower-side half of the factorization, and the L2E
program's per-tower target.  NOTE the composition subtlety recorded at
`siteCalculusSupply_of_bankFamily`: this `Nonempty` form does NOT compose with a wiring
Prop (the wired bank must be the SAME bank), which is why the factored normal form
threads the bank FAMILY as data.  NEW STATEMENT (review). -/
def TowerBankSupply (T : DeepTower.{0, uKt} F H₀ hpin r) : Prop :=
  ∀ j, (hj : DeepLive r j) → Nonempty (LevelSiteBank.{uKt} (T.trunc j hj.2.le))

/-- Vacuity tooth: at depth `r ≤ 3` the tower-side supply holds vacuously. -/
theorem towerBankSupply_of_shallow (T : DeepTower.{0, uKt} F H₀ hpin r) (hr : r ≤ 3) :
    TowerBankSupply.{uKt} T := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

/-- A bank family yields the tower-side supply (the data-to-Prop direction). -/
theorem towerBankSupply_of_family (T : DeepTower.{0, uKt} F H₀ hpin r)
    (bF : ∀ j, (hj : DeepLive r j) → LevelSiteBank.{uKt} (T.trunc j hj.2.le)) :
    TowerBankSupply.{uKt} T :=
  fun j hj => ⟨bF j hj⟩

end Bank

/-! ## §2 The factorization: `SiteCalculusSupply` ⟺ per level, some bank, wired -/

section Suppliers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-- **[SCS §2] The per-realization wiring residue at a given bank** — ONE read-law
family: the realization's exported tower read at the normalized ladder points is the
receiver image of the bank calculus's cleared normalizer read (`IFC3.GC13Wiring` at the
bank's calculus and the realization's own exports).  No calculus datum, no B-1 clause is
demanded — those live in the bank.  NEW STATEMENT (review). -/
def BankWiredAt (X : RealizedInput core Aℛ) (j : ℕ) (hj : DeepLive core.r j)
    (B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le)) : Prop :=
  IFC3.GC13Wiring
    (Aℛ.normalizer.arenaNormSection0.transport
      (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
        gaugeLatticeEquiv core.r).symm)
    (useHeightFamily X j) (towerReadFamily X j) B.calculus
    (Aℛ.receiver.levelHom j)

/-- ★ **[SCS §2] THE FACTORIZATION IFF** — WSS's `SiteCalculusSupply` is EXACTLY "at
every deep-live level, some tower-side bank, wired to the realization's own exports".
Unlike the WSS/USUP reductions (sufficient-only), this is an equivalence: nothing is
lost in the split, so the two named halves jointly ARE the supply. -/
theorem siteCalculusSupply_iff_wiredBank (X : RealizedInput core Aℛ) :
    SiteCalculusSupply.{uG, uKt, uL} X ↔
      ∀ j, (hj : DeepLive core.r j) →
        ∃ B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le),
          BankWiredAt.{uG, uKt, uL} X j hj B := by
  constructor
  · intro h j hj
    obtain ⟨e', f', u', I, f_pos, hprev, hnorm, hnormdeg, hnormz, hwiring⟩ := h j hj
    exact ⟨⟨e', f', u', I, f_pos, hprev, hnorm, hnormdeg, hnormz⟩, hwiring⟩
  · intro h j hj
    obtain ⟨B, hw⟩ := h j hj
    exact ⟨B.e', B.f', B.u', B.calculus, B.f_pos, B.prev, B.norm_grade, B.norm_deg,
      B.norm_ne, hw⟩

/-- **[SCS §2] The per-realization remainder at a bank family** — the wiring supply:
strictly smaller than `SiteCalculusSupply` (one `GC13Wiring` instance per level; the
calculus and B-1 content sit in the family, not in the demand).  NEW STATEMENT
(review). -/
def BankWiringSupply (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le)) : Prop :=
  ∀ j, (hj : DeepLive core.r j) → BankWiredAt.{uG, uKt, uL} X j hj (bF j hj)

/-- ★ **[SCS §2] THE FACTORED NORMAL FORM** — a bank family (tower-side data: the L2E
program's product) plus its wiring supply (per-realization residue) yields the full
`SiteCalculusSupply`.  This is the constructive reading of the iff; the family is
threaded as DATA because a `Nonempty`-bank Prop cannot name which bank is wired. -/
theorem siteCalculusSupply_of_bankFamily (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hw : BankWiringSupply.{uG, uKt, uL} X bF) :
    SiteCalculusSupply.{uG, uKt, uL} X :=
  (siteCalculusSupply_iff_wiredBank X).mpr fun j hj => ⟨bF j hj, hw j hj⟩

/-- **[SCS §2] the bank-interface site exporter** — bank + wiring + NOTHING ELSE already
assembles the full G3 site package (cleared law derived by `LevelSiteBank.cleared`):
the "`WleCleared` truncation exporter" that IFC3's module fence records as the missing
mechanism, realized at the bank interface. -/
def LevelSiteBank.toWleExport (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : DeepLive core.r j) (B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hw : BankWiredAt.{uG, uKt, uL} X j hj B) :
    WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le where
  e' := B.e'
  f' := B.f'
  u' := B.u'
  f_pos := B.f_pos
  calculus := B.calculus
  cleared := B.cleared
  wiring := hw

/-! ## §3 Wrappers through WSS §3: bank family + wiring + ladder ⟹ the wired supply -/

/-- ★ **[SCS §3] the per-level assembly at the bank interface** — WSS's
`wleSiteExists_of_supplies` with its nine bank-side hypotheses folded into the bank
datum: bank + wiring + the calculus-free ladder-read law give the full per-level
`WiredSiteSupply` content.  Uniform in `q`. -/
theorem wleSiteExists_of_bank (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : DeepLive core.r j) (B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hw : BankWiredAt.{uG, uKt, uL} X j hj B)
    (hlad : LadderReadLaw.{uG, uKt, uL} X (by rcases hj with ⟨hj3, hjr⟩; omega) j) :
    ∃ S : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le,
      ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S ∧
      PeelCompatibleAt X S ∧
      RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S :=
  wleSiteExists_of_supplies X hj B.f_pos B.calculus B.prev B.norm_grade B.norm_deg
    B.norm_ne hw hlad

/-- ★ **[SCS §3] bank family + wiring + ladder ⟹ `WiredSiteSupply`** (through WSS's
per-realization reduction). -/
theorem wiredSiteSupply_of_bankFamily (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hw : BankWiringSupply.{uG, uKt, uL} X bF)
    (hlad : LadderReadSupply.{uG, uKt, uL} X) :
    WiredSiteSupply.{uG, uKt, uL} X :=
  wiredSiteSupply_of_supplies X (siteCalculusSupply_of_bankFamily X bF hw) hlad

/-- Corollary: the three factored inputs fire the `GentowW` per-witness exporter. -/
theorem gentowPerWitnessExporter_of_bankFamily (X : RealizedInput core Aℛ)
    (bF : ∀ j, (hj : DeepLive core.r j) →
      LevelSiteBank.{uKt} (core.T.trunc j hj.2.le))
    (hw : BankWiringSupply.{uG, uKt, uL} X bF)
    (hlad : LadderReadSupply.{uG, uKt, uL} X) :
    GentowPerWitnessExporter.{uG, uKt, uL} X :=
  gentowPerWitnessExporter_of_wiredSiteSupply X
    (wiredSiteSupply_of_bankFamily X bF hw hlad)

end Suppliers

/-! ## §4 The universal factorization -/

/-- **[SCS §4] The universal wired-bank supply**: at EVERY arising realization of degree
`n` and every deep-live level, some tower-side bank wired to the realization's own
exports.  NEW STATEMENT (review). -/
def UniversalWiredBankSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    ∀ j, (hj : DeepLive core.r j) →
      ∃ B : LevelSiteBank.{uKt} (core.T.trunc j hj.2.le),
        BankWiredAt.{uG, uKt, uL} X j hj B

/-- ★ **[SCS §4] THE UNIVERSAL FACTORIZATION IFF** — WSS's `UniversalSiteCalculusSupply n`
(half of half of the capstone `deepTwist` boundary) IS the universal wired-bank supply:
the pointwise transfer of the §2 iff.  The bank/wiring fault line is therefore exact at
the universal level too. -/
theorem universalSiteCalculusSupply_iff_wiredBank {n : ℕ} :
    UniversalSiteCalculusSupply.{uG, uKt, uL} n ↔
      UniversalWiredBankSupply.{uG, uKt, uL} n := by
  constructor
  · intro h O _ _ _ Kt _ E _ L _ _ core Aℛ X
    exact (siteCalculusSupply_iff_wiredBank X).mp (h O Kt E L core Aℛ X)
  · intro h O _ _ _ Kt _ E _ L _ _ core Aℛ X
    exact (siteCalculusSupply_iff_wiredBank X).mpr (h O Kt E L core Aℛ X)

/-! ## §5 Keystone nonvacuity and THE CONDITIONALITY SPLIT -/

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

/-- ★ **[SCS §5] THE KEYSTONE BANK AS A STANDALONE TOWER-SIDE DATUM** — the μ₄
`(2, 1, 85)` bank at the truncated depth-four S2 tower, through the `f' = 1` genre
constructor.  THE CONDITIONALITY SPLIT, machine-visible: this datum needs `(h2, hq)`
ALONE — no witness thresholds `w₁…w₄`, no `IsAdicComplete`, no R8r payload, no realized
input.  (Compare `s2Four_siteCalculusSupply`, whose wiring half carries the full witness
payload.)  The bank half of the factorization is FRAME data; the wiring half is WITNESS
data. -/
noncomputable def s2FourSiteBank : LevelSiteBank.{0} (s2TruncThree h2 hq) :=
  levelSiteBank_of_inertia_trivial (s2SiteMu4Calculus h2 hq)
    (by
      have h := s2Site_B1_exact_grade_supply h2 hq 1 one_pos le_rfl
      simpa only [one_mul] using h)
    (by
      have h := s2Site_B1_degree_supply h2 hq 1 one_pos le_rfl
      simpa only [one_mul] using h)
    (by
      have h := s2Site_B1_nonzero_supply h2 hq 1 one_pos le_rfl
      simpa only [one_mul] using h)

/-- ★ **[SCS §5] the keystone supply RE-DERIVED through the factorization** — the same
`Prop` as WSS's `s2Four_siteCalculusSupply`, now assembled from the standalone bank
(`(h2, hq)` only) + the wiring instance (full witness payload), through the §2 iff: the
coherence pin that the factored route and WSS's direct route agree on the wired genre. -/
theorem s2Four_siteCalculusSupply_of_bank :
    SiteCalculusSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  refine (siteCalculusSupply_iff_wiredBank _).mpr ?_
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact ⟨s2FourSiteBank h2 hq,
    s2Four_gc13Wiring h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive _ _ _⟩

/-- Coherence pin: the keystone bank + WSS's ladder supply re-derive the landed
`WiredSiteSupply` instance through the factored route. -/
example :
    WiredSiteSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  wiredSiteSupply_of_supplies _
    (s2Four_siteCalculusSupply_of_bank h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_ladderReadSupply h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.LevelSiteBank
#print axioms Uniformity.Density.DeepExport.LevelSiteBank.cleared
#print axioms Uniformity.Density.DeepExport.LevelSiteBank.baseRead_ne_zero
#print axioms Uniformity.Density.DeepExport.LevelSiteBank.thetaRatioCleared_one
#print axioms Uniformity.Density.DeepExport.levelSiteBank_of_inertia_trivial
#print axioms Uniformity.Density.DeepExport.TowerBankSupply
#print axioms Uniformity.Density.DeepExport.towerBankSupply_of_shallow
#print axioms Uniformity.Density.DeepExport.towerBankSupply_of_family
#print axioms Uniformity.Density.DeepExport.BankWiredAt
#print axioms Uniformity.Density.DeepExport.siteCalculusSupply_iff_wiredBank
#print axioms Uniformity.Density.DeepExport.BankWiringSupply
#print axioms Uniformity.Density.DeepExport.siteCalculusSupply_of_bankFamily
#print axioms Uniformity.Density.DeepExport.LevelSiteBank.toWleExport
#print axioms Uniformity.Density.DeepExport.wleSiteExists_of_bank
#print axioms Uniformity.Density.DeepExport.wiredSiteSupply_of_bankFamily
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_bankFamily
#print axioms Uniformity.Density.DeepExport.UniversalWiredBankSupply
#print axioms Uniformity.Density.DeepExport.universalSiteCalculusSupply_iff_wiredBank
#print axioms Uniformity.Density.DeepExport.s2FourSiteBank
#print axioms Uniformity.Density.DeepExport.s2Four_siteCalculusSupply_of_bank

end AxCheck
