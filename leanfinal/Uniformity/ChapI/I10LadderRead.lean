/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10SiteSupply

/-!
# Uniformity.ChapI.I10LadderRead — LRS: row C2's residue dissected — the derivable
fields of the D.44 ladder-read law, and its carrier normal form [LRS 2026-08-30]

**Unit LRS** — the second of WSS's two per-realization supply `Prop`s:
`LadderReadSupply` (row C2's exact calculus-free residue — the D.44 ladder law
`R(n̂(s·q)) = θ(s)·R(n̂(q))^s`, its `s = 0` head, and the peel tie
`(peelUnit : Kt) = R(n̂(q))`; no FGMN operator).  This unit dissects the law per clause
at a GENERAL arising realization: what does it need that the realization's own exports
and the landed carrier machinery do not already provide?

## Charge 1 — the dissection (derivable vs demanded, per clause)

The exports unfold to raw node data: `towerReadFamily X j` reads the
`SplitNodePointSource.towerRead` field ("an arbitrary function `R : G → K`, evaluated
only at the ladder points" — D.44 faithfulness, C130ar §4), `peelUnitFamily` IS the
`peelUnit` field verbatim, and `(arenaFamily X hr j).theta q s` is the arena read of the
section element `thetaEl q s = n̂(s·q)·(n̂(q)^s)⁻¹` (D.04/D.08).  The three fields
`arenaRead`/`towerRead`/`peelUnit` are FREE source fields of `SplitNodePointSource`
(C130k2) — no structure law relates them (CC-11's mechanized separateness audit), and the
bank side cannot help: `GC13Wiring`'s single clause `read_norm` pins `R` only at window
ladder points `1 ≤ s ≤ f'` and never mentions `theta` or the peel unit.  Per clause:

| clause | status at a general realization |
|---|---|
| `law` at `s = 1` | **DERIVABLE OUTRIGHT** — `θ(q,1) = res(n̂(q)·n̂(q)⁻¹) = 1` (`IFC2.theta_one`); landed as `ladderRead_law_one`, uniform in `q`, no hypothesis |
| `head` | **collapses to the read normalization** — `θ(q,0) = 1` (`IFC2.theta_zero`) and `n̂(0) = 1`, so the clause is exactly `R(1) = 1` (`ladderReadLaw_head_iff_read_one`); NOT generically closable (free field) |
| `law` at `s ≥ 2` | the group identity `n̂(s·q) = thetaEl(q,s)·n̂(q)^s` holds in the section (PROVED inside `ladderReadLaw_of_carrierRead`), so the whole family is FORCED by one kernel-equivariance law of the read — the carrier normal form below; NOT generically closable (free field) |
| `tie` | genuinely independent — `peelUnit` is a third free field; demanded verbatim by the normal form |

**The scope answer**: `LadderReadSupply` does NOT close at every arising realization —
a generic proof would inhabit a law on free source data (the C92-vacuity genre; the
supplier obligation is exactly C130ar's fence "NO B-law instance is claimed at any
level").  The honest content is (i) the `s = 1` rung and the theta collapses, proved
here, and (ii) THE CARRIER NORMAL FORM: the ladder law in the shape the landed carrier
machinery produces (RUNG's `rung2Read.read_mul` is a ladder-type multiplicativity; WCC's
`WeightedCarrier.read_mul` likewise) —

* `CarrierReadLaw X hr j` (NEW STATEMENT, review): (i) `read_ker_pow` — the exported
  read is equivariant over the arena read along the height kernel and power-multiplicative
  on the ladder base: `R(k·n̂(q)^s) = res(k)·R(n̂(q))^s` for every kernel element `k` and
  every `s`; (ii) the peel tie, verbatim.
* ★ `ladderReadLaw_of_carrierRead` — `CarrierReadLaw ⟹ LadderReadLaw`: head is the
  instance `k = 1, s = 0`; the `s`-rung is the instance `k = thetaEl(q,s)` through the
  section identity.  Uniform in `q`; no cardinality, no numeral, no calculus.
* `carrierReadLaw_of_mult_agree` — the coarser supplier shape: a fully multiplicative
  read that agrees with the arena read on the kernel (+ tie) is a `CarrierReadLaw`.

## Charges 2/3 — what lands, and the boundary after LRS

* §1 the derivable fields (`ladderRead_law_one`, `ladderReadLaw_head_iff_read_one`).
* §2 the normal form (`CarrierReadLaw`, `CarrierReadSupply`, vacuity tooth) and the
  ★ reductions (`ladderReadLaw_of_carrierRead`, `ladderReadSupply_of_carrierReadSupply`,
  `wiredSiteSupply_of_bank_carrierRead`).
* §3 universal form (`UniversalCarrierReadSupply`) and the capstone composition
  ★ `deepTwistField_of_carrier_supplies` — the `deepTwist` field from tau supply + bank
  supply + CARRIER supply, through WSS's `deepTwistField_of_bank_supplies`.
* §4 keystone nonvacuity: `s2Four_carrierReadSupply` at EVERY depth-4 keystone witness
  (full parametric payload, conditionality exactly the keystone's), and the coherence
  pin re-deriving WSS's `s2Four_ladderReadSupply` through the normal form.

**The deepTwist boundary after LRS** (exact): unchanged in strength — per-realization it
is `SiteCalculusSupply ∧ LadderReadSupply` (WSS), and `LadderReadSupply` remains row
C2's minimal named residue.  What changed: its two non-derivable clauses now have the
carrier-shaped SUFFICIENT normal form `CarrierReadSupply` (strictly stronger per level;
sufficient-only, no converse claimed), so the supplier target for the L2E/D3-spine
carrier program is the same `read_mul` shape RUNG already produces at rung 2 — the
remaining research is the D3-03 spine adapter + the tie, not a new law genre.  The site
half's residue does NOT shrink to the bank alone; that outcome is REFUTED for this
route by the free-field adjudication above.

No statement is weakened: `LadderReadLaw`/`LadderReadSupply` are consumed verbatim on
the conclusion side; every new `Prop` sits on the hypothesis side of a proved reduction.

**Flagged for human review** (new statements): `CarrierReadLaw`, `CarrierReadSupply`,
`UniversalCarrierReadSupply` (supplier-side interface `Prop`s below the signed surface;
no leanspec name touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_LRS.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

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

/-! ## §1 The derivable fields of the ladder-read law -/

/-- **[LRS §1] The `s = 1` rung is a THEOREM at every arising realization** — the first
ladder instance of `LadderReadLaw.law` holds unconditionally: `θ(q,1) = 1`
(`IFC2.theta_one`) and both sides are the base read.  Uniform in `q`. -/
theorem ladderRead_law_one (X : RealizedInput core Aℛ) (hr : 1 < core.r) (j : ℕ) :
    towerReadFamily.{0, uG, uKt, uL} X j
        ((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).n
          (((1 : ℕ) : ℤ) * useHeightFamily X j)) =
      ((arenaFamily.{0, uG, uKt, uL} X hr j).theta (useHeightFamily X j) 1 : Kt) *
        (towerReadFamily.{0, uG, uKt, uL} X j
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j))) ^ 1 := by
  rw [IFC2.theta_one, Units.val_one, one_mul, pow_one, Nat.cast_one, one_mul]

/-- **[LRS §1] The head clause IS the read normalization** — since `θ(q,0) = 1`
(`IFC2.theta_zero`) and `n̂(0) = 1` (the section's zero pin), `LadderReadLaw.head` is
equivalent to `R(1) = 1` on the exported read.  This is the exact per-realization content
of the `s = 0` clause; nothing else hides in it. -/
theorem ladderReadLaw_head_iff_read_one (X : RealizedInput core Aℛ) (hr : 1 < core.r)
    (j : ℕ) :
    (towerReadFamily.{0, uG, uKt, uL} X j
        ((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).n 0) =
      ((arenaFamily.{0, uG, uKt, uL} X hr j).theta (useHeightFamily X j) 0 : Kt)) ↔
    towerReadFamily.{0, uG, uKt, uL} X j (1 : GaugeLattice.{uG} core.r) = 1 := by
  rw [(Aℛ.normalizer.arenaNormSection0.transport
    (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
      gaugeLatticeEquiv core.r).symm).n_zero, IFC2.theta_zero, Units.val_one]

/-! ## §2 The carrier normal form of the residue -/

/-- **[LRS §2] The carrier normal form of row C2's residue** — the exported tower read
is equivariant over the exported arena read along the height kernel and
power-multiplicative on the ladder base (`read_ker_pow`), and the exported peel unit is
the base read (`tie`).  This is the shape the landed carrier machinery produces: RUNG's
`rung2Read` satisfies `WeightedCarrier.read_mul` — exactly a ladder-type
multiplicativity — and any multiplicative read agreeing with the arena read on the
kernel is an instance (`carrierReadLaw_of_mult_agree`).  Strictly STRONGER per level
than `LadderReadLaw` (sufficient-only; the ladder law is its trace on the ladder
points).  NEW STATEMENT (review). -/
structure CarrierReadLaw (X : RealizedInput core Aℛ) (hr : 1 < core.r) (j : ℕ) :
    Prop where
  read_ker_pow : ∀ (k : MonoidHom.ker (arenaFamily.{0, uG, uKt, uL} X hr j).v) (s : ℕ),
    towerReadFamily.{0, uG, uKt, uL} X j
        ((k : GaugeLattice.{uG} core.r) *
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j)) ^ s) =
      (((arenaFamily.{0, uG, uKt, uL} X hr j).res k : Ktˣ) : Kt) *
        (towerReadFamily.{0, uG, uKt, uL} X j
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j))) ^ s
  tie : ((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) =
    towerReadFamily.{0, uG, uKt, uL} X j
      ((Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j))

/-- **[LRS §2] The carrier-read supply**: the normal form at every deep-live level.
NEW STATEMENT (review). -/
def CarrierReadSupply (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    CarrierReadLaw.{uG, uKt, uL} X (by rcases hj with ⟨hj3, hjr⟩; omega) j

/-- Vacuity tooth: at depth `r ≤ 3` the carrier-read supply holds vacuously. -/
theorem carrierReadSupply_of_shallow (X : RealizedInput core Aℛ)
    (hr : core.r ≤ 3) : CarrierReadSupply.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

/-- ★ **[LRS §2] THE GENERIC DERIVATION** — the carrier normal form implies the FULL
`LadderReadLaw`: the head is the instance `k = 1, s = 0`; the `s`-rung is the instance
`k = thetaEl(q,s)` through the section identity `n̂(s·q) = thetaEl(q,s)·n̂(q)^s`; the tie
is verbatim.  Uniform in `q`: no cardinality, no S2 datum, no numeral, no calculus. -/
theorem ladderReadLaw_of_carrierRead (X : RealizedInput core Aℛ) (hr : 1 < core.r)
    (j : ℕ) (h : CarrierReadLaw.{uG, uKt, uL} X hr j) :
    LadderReadLaw.{uG, uKt, uL} X hr j := by
  -- the base-read normalization: the instance `k = 1, s = 0`
  have hone : towerReadFamily.{0, uG, uKt, uL} X j (1 : GaugeLattice.{uG} core.r) = 1 := by
    have h0 := h.read_ker_pow 1 0
    simpa using h0
  refine ⟨?_, ?_, h.tie⟩
  · -- head: `n̂(0) = 1`, the normalization, and the theta collapse at `s = 0`
    rw [(Aℛ.normalizer.arenaNormSection0.transport
      (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
        gaugeLatticeEquiv core.r).symm).n_zero, hone, IFC2.theta_zero, Units.val_one]
  · -- the `s`-rung: the instance `k = thetaEl(q,s)` through the section identity
    intro s hs
    have hsplit : (Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm).n ((s : ℤ) * useHeightFamily X j) =
        ((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).thetaEl (useHeightFamily X j) s) *
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j)) ^ s := by
      rw [NormSection.thetaEl, inv_mul_cancel_right]
    rw [hsplit]
    exact h.read_ker_pow
      ⟨(Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).thetaEl (useHeightFamily X j) s,
        (arenaFamily.{0, uG, uKt, uL} X hr j).thetaEl_mem_ker (useHeightFamily X j) s⟩ s

/-- **[LRS §2] The coarse supplier shape**: a read that is multiplicative on the whole
synchronized lattice and agrees with the arena read on the height kernel (plus the peel
tie) is a `CarrierReadLaw`.  This is the shape a full carrier realization of the node's
W-leg would export. -/
theorem carrierReadLaw_of_mult_agree (X : RealizedInput core Aℛ) (hr : 1 < core.r)
    (j : ℕ)
    (hmul : ∀ g g' : GaugeLattice.{uG} core.r,
      towerReadFamily.{0, uG, uKt, uL} X j (g * g') =
        towerReadFamily.{0, uG, uKt, uL} X j g * towerReadFamily.{0, uG, uKt, uL} X j g')
    (hagree : ∀ k : MonoidHom.ker (arenaFamily.{0, uG, uKt, uL} X hr j).v,
      towerReadFamily.{0, uG, uKt, uL} X j (k : GaugeLattice.{uG} core.r) =
        (((arenaFamily.{0, uG, uKt, uL} X hr j).res k : Ktˣ) : Kt))
    (htie : ((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) =
      towerReadFamily.{0, uG, uKt, uL} X j
        ((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j))) :
    CarrierReadLaw.{uG, uKt, uL} X hr j := by
  have hone : towerReadFamily.{0, uG, uKt, uL} X j (1 : GaugeLattice.{uG} core.r) = 1 := by
    have h1 := hagree 1
    simpa using h1
  have hpow : ∀ m : ℕ,
      towerReadFamily.{0, uG, uKt, uL} X j
        (((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j)) ^ m) =
      (towerReadFamily.{0, uG, uKt, uL} X j
        ((Aℛ.normalizer.arenaNormSection0.transport
          (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
            gaugeLatticeEquiv core.r).symm).n (useHeightFamily X j))) ^ m := by
    intro m
    induction m with
    | zero => simpa using hone
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  refine ⟨fun k s => ?_, htie⟩
  rw [hmul, hagree, hpow]

/-- ★ **[LRS §2] The supply-level reduction**: the carrier normal form at every
deep-live level yields WSS's `LadderReadSupply`. -/
theorem ladderReadSupply_of_carrierReadSupply (X : RealizedInput core Aℛ)
    (h : CarrierReadSupply.{uG, uKt, uL} X) : LadderReadSupply.{uG, uKt, uL} X :=
  fun j hj => ladderReadLaw_of_carrierRead X _ j (h j hj)

/-- ★ **[LRS §2] Row C0/C1 bank + row C2 carrier form ⟹ the wired-site supply** — the
per-realization site half from the bank supply and the carrier normal form, through
WSS's `wiredSiteSupply_of_supplies`. -/
theorem wiredSiteSupply_of_bank_carrierRead (X : RealizedInput core Aℛ)
    (hbank : SiteCalculusSupply.{uG, uKt, uL} X)
    (hcar : CarrierReadSupply.{uG, uKt, uL} X) :
    WiredSiteSupply.{uG, uKt, uL} X :=
  wiredSiteSupply_of_supplies X hbank (ladderReadSupply_of_carrierReadSupply X hcar)

end Suppliers

/-! ## §3 The universal form and the capstone composition -/

/-- **[LRS §3] The universal carrier-read supply**: the normal form at EVERY arising
realization of degree `n`.  NEW STATEMENT (review). -/
def UniversalCarrierReadSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    CarrierReadSupply.{uG, uKt, uL} X

/-- ★ **[LRS §3] The universal reduction**: the universal carrier supply fires WSS's
`UniversalLadderReadSupply n`. -/
theorem universalLadderReadSupply_of_carrierRead {n : ℕ}
    (h : UniversalCarrierReadSupply.{uG, uKt, uL} n) :
    UniversalLadderReadSupply.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X
  exact ladderReadSupply_of_carrierReadSupply X (h O Kt E L core Aℛ X)

/-- ★ **[LRS §3] The capstone `deepTwist` field from tau + bank + CARRIER supplies** —
WSS's `deepTwistField_of_bank_supplies` with the ladder leg superseded by its carrier
normal form.  SUFFICIENT ONLY; the exact boundary remains
`deepTwistField_iff_universalPerWitness`. -/
theorem deepTwistField_of_carrier_supplies {n : ℕ}
    (hv : UniversalTauWordDescentSupply.{uG, uKt, uL} n)
    (hbank : UniversalSiteCalculusSupply.{uG, uKt, uL} n)
    (hcar : UniversalCarrierReadSupply.{uG, uKt, uL} n) :
    IFC0.DeepTwistField.{uG, uKt, uL} n :=
  deepTwistField_of_bank_supplies hv hbank
    (universalLadderReadSupply_of_carrierRead hcar)

/-! ## §4 Keystone nonvacuity: the carrier normal form at every depth-4 keystone witness -/

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

/-- ★ **[LRS §4] The carrier normal form at EVERY depth-4 keystone witness** — the
card-2 collapses confined exactly as in WSS §5: the wired read is `1` on the live range
and every arena-read value and the peel unit are units of the 2-element terminal field.
Conditionality: exactly the keystone's. -/
theorem s2Four_carrierReadSupply :
    CarrierReadSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  refine ⟨?_, ?_⟩
  · intro k s
    simp only [s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock
      hcop hj.gaugeLive, one_pow, mul_one]
    exact Eq.symm (c0_eq_one_of_ne_zero (s2R7Fld_card h2 hq 4) (Units.ne_zero _))
  · rw [s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive _]
    exact (congrArg Units.val (s2FourUnit_eq_one h2 hq _)).trans Units.val_one

/-- Coherence pin: the normal form re-derives WSS's keystone ladder supply through the
NEW generic derivation (the carrier route and WSS's direct route agree on the wired
genre). -/
example :
    LadderReadSupply.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  ladderReadSupply_of_carrierReadSupply _
    (s2Four_carrierReadSupply h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.ladderRead_law_one
#print axioms Uniformity.Density.DeepExport.ladderReadLaw_head_iff_read_one
#print axioms Uniformity.Density.DeepExport.CarrierReadLaw
#print axioms Uniformity.Density.DeepExport.CarrierReadSupply
#print axioms Uniformity.Density.DeepExport.carrierReadSupply_of_shallow
#print axioms Uniformity.Density.DeepExport.ladderReadLaw_of_carrierRead
#print axioms Uniformity.Density.DeepExport.carrierReadLaw_of_mult_agree
#print axioms Uniformity.Density.DeepExport.ladderReadSupply_of_carrierReadSupply
#print axioms Uniformity.Density.DeepExport.wiredSiteSupply_of_bank_carrierRead
#print axioms Uniformity.Density.DeepExport.UniversalCarrierReadSupply
#print axioms Uniformity.Density.DeepExport.universalLadderReadSupply_of_carrierRead
#print axioms Uniformity.Density.DeepExport.deepTwistField_of_carrier_supplies
#print axioms Uniformity.Density.DeepExport.s2Four_carrierReadSupply

end AxCheck
