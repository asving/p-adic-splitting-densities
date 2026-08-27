/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10_I15_I18
import Uniformity.ChapF.F28
import Uniformity.ChapF.F04w
import Uniformity.ChapF.F12w
import Uniformity.ChapH.H09

/-!
# Uniformity.ChapI.IFC0 — the capstone interface nodes L0 / DT0 / W0 / WIN0

Unit CIFACE, 2026-08-26/27 (`docs/in-progress/CAPSTONE_IFACE_2026-08-26.md`; supply map
`docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md`, rows CHFD-L0/DT0/W0/WIN0).

**⚠ TRUST BOUNDARY — every `def`/`structure` here is a NEW statement**, flagged for the
standing review.  Nothing here is signed; binding any of these names into leanspec is a
LATER RECORDED AMENDMENT.  This file proves NO open mathematics: the theorems are exact
decomposition bookkeeping (record constructors / projections) plus fence teeth.  Zero
`sorry`, zero new axiom; AxChk footer expects Lean core only.

* §1 **L0**: the capstone `ladder` field split into four supplier `Prop`s
  (HE7A / LB1 / MP1 / ϑ), with the machine-checked exactness `iff`.
* §2 **DT0**: the `deepTwist` field split into the sitewise-ϑ and per-level-`GentowW`
  suppliers, with the exactness `iff` and per-live projections on the conjunct.
* §3 **W0**: the guarded weld-site supply socket (three legs bound together per A-I.1's
  I-D7/I-D8 ruling), its F.28 degeneration, and the F12w-transported teeth showing the
  guard is load-bearing.  The guard's canonical body is OPEN (no landed site exporter).
* §4 **WIN0**: the pre-`hwin` stage-window datum and the guarded window-pinning body,
  typed against `StageInterface.hwin` without asserting it, with refutation teeth for
  the unguarded reading.

Non-swallowing audit discipline per `C130s18.lean` §5; per-node audit notes in the
design doc.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC0

open Uniformity.Density

universe uW uG uKt uL

/-! ## §1 NODE L0 — the four-way split of the capstone `ladder` field

The field (`I10_I15_I18.lean:154-160`) maps the arising-configuration guard to E.24's
four-field `LadderSupply` record.  Each supplier below carries the field's EXACT binder
block and guard and concludes in exactly ONE record field.  None weakens the guard, none
adds a residue-law hypothesis (the D.62 trap fence — C130s18 §5's audit applies verbatim
because the guard context is identical). -/

/-- The capstone `ladder` field's exact type at degree `n` (a name for pinning; the
`example` below fails the build if this drifts from `CapstoneHypotheses.ladder`). -/
def LadderField (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q

/-- Anti-drift pin: `LadderField` IS the field's type, definitionally. -/
example {n : ℕ} (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) :
    LadderField.{uW, uG, uKt, uL} n := h.ladder

/-- **L0 supplier 1 (HE7A leg)**: every arising degree-`n` ladder configuration admits a
rung interface (`Nonempty (RungInterface C B)`, E.12/E.24). NEW STATEMENT (review). -/
def LadderPackageSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    Ladder.HE7APackage.{0, 0, uW} C B

/-- **L0 supplier 2 (LB1 leg)**: … admits the A-E.2 block-suite carrier (E.39).
NEW STATEMENT (review). -/
def LadderLB1Supplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    Ladder.LB1Carrier.{0, 0, uW} C B

/-- **L0 supplier 3 (MP1 leg)**: … admits the A-E.2 mid-peel-emission carrier (E.40).
NEW STATEMENT (review). -/
def LadderMP1Supplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    Ladder.MP1Carrier.{0, 0, uW} C B

/-- **L0 supplier 4 (ϑ leg)**: … satisfies the sitewise `(H-VARTHETA-RES)_i` socket at
every `i ≥ 3` (E.61 at D.62's A-D.2 form, at the guard's pinned canonical read).
NEW STATEMENT (review). -/
def LadderVarthetaSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    ∀ i ≥ 3, Ladder.VarthetaRes G Kt L N v ρ q i

/-- ★ **L0 exit gate — the split is EXACT**: the four suppliers are jointly equivalent
to the capstone `ladder` field.  Forward: record projections.  Backward: the E.24 record
constructor.  No mathematics is proved; the obligation is repartitioned, byte-exactly. -/
theorem ladderField_iff_suppliers {n : ℕ} :
    LadderField.{uW, uG, uKt, uL} n ↔
      LadderPackageSupplier.{uW, uG, uKt, uL} n ∧ LadderLB1Supplier.{uW, uG, uKt, uL} n ∧
      LadderMP1Supplier.{uW, uG, uKt, uL} n ∧ LadderVarthetaSupplier.{uG, uKt, uL} n := by
  constructor
  · intro h
    exact ⟨fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).package,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).lb1,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).mp1,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).vartheta⟩
  · rintro ⟨hp, hl, hm, hv⟩
    exact fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
      ⟨hp O K C B G Kt L N v ρ q hcfg, hl O K C B G Kt L N v ρ q hcfg,
       hm O K C B G Kt L N v ρ q hcfg, hv O K C B G Kt L N v ρ q hcfg⟩

/-- The assembly direction alone, in consumable form: four supplier proofs give the
capstone `ladder` field. -/
theorem ladderField_of_suppliers {n : ℕ}
    (hp : LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hm : LadderMP1Supplier.{uW, uG, uKt, uL} n)
    (hv : LadderVarthetaSupplier.{uG, uKt, uL} n) :
    LadderField.{uW, uG, uKt, uL} n :=
  ladderField_iff_suppliers.mpr ⟨hp, hl, hm, hv⟩

/-! ## §2 NODE DT0 — the per-live-level split of the capstone `deepTwist` field

The field (`I10_I15_I18.lean:164-171`) maps the joint-witness guard to
`DeepTwistConjunctLive r v ρ q A R w = ∀ i, DeepLive r i → VarthetaRes … i ∧ WFrame … i`.
The cumulative `WFrame` legs over all live `i` flatten to the per-level `GentowW` family
on `3 ≤ j < r` (each live `j` is its own witness), so TWO suppliers suffice — and the
`GentowW` supplier is stated at D.44's raw identity so per-level campaign endpoints
(e.g. the μ₃ chain's depth-2 tooth) plug in without repackaging. -/

/-- The capstone `deepTwist` field's exact type at degree `n` (pin below). -/
def DeepTwistField (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
    Ladder.DeepTwistConjunctLive r v ρ q A R w

/-- Anti-drift pin: `DeepTwistField` IS the field's type, definitionally. -/
example {n : ℕ} (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) :
    DeepTwistField.{uG, uKt, uL} n := h.deepTwist

/-- **DT0 supplier 1 (sitewise ϑ leg)**: at every arising joint witness, the sitewise
`(H-VARTHETA-RES)_i` socket holds at every deep-live level `3 ≤ i < r`.
NEW STATEMENT (review). -/
def DeepVarthetaSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
    ∀ i, Tower.DeepLive r i → Ladder.VarthetaRes G Kt L N v ρ q i

/-- **DT0 supplier 2 (per-level `GentowW` leg)**: at every arising joint witness, D.44's
`[GENTOW5-W(j)]` identity `R j (N.n (s·q j)) = ϑ(q j, s) · (w j)^s` holds at every level
`3 ≤ j < r`.  NEW STATEMENT (review). -/
def DeepGentowSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
    ∀ j, 3 ≤ j → j < r → Gauge.GentowW (A j) (q j) (R j) (w j)

/-- ★ **DT0 exit gate — the split is EXACT**: the two suppliers are jointly equivalent to
the capstone `deepTwist` field.  Forward: per-live projections (`GentowW` at level `j` is
read off the conjunct at the live index `i := j`).  Backward: rebuild each live level's
`WFrame` from the flat family via `j ≤ i < r`. -/
theorem deepTwistField_iff_suppliers {n : ℕ} :
    DeepTwistField.{uG, uKt, uL} n ↔
      DeepVarthetaSupplier.{uG, uKt, uL} n ∧ DeepGentowSupplier.{uG, uKt, uL} n := by
  constructor
  · intro h
    refine ⟨fun O _ K _ C B G _ Kt _ L _ _ N v ρ q A R w r hcfg i hi =>
              (h O K C B G Kt L N v ρ q A R w r hcfg i hi).1,
            fun O _ K _ C B G _ Kt _ L _ _ N v ρ q A R w r hcfg j h3 hjr =>
              ((h O K C B G Kt L N v ρ q A R w r hcfg j ⟨h3, hjr⟩).2).supplied j h3
                le_rfl⟩
  · rintro ⟨hv, hw⟩
    intro O _ K _ C B G _ Kt _ L _ _ N v ρ q A R w r hcfg i hi
    exact ⟨hv O K C B G Kt L N v ρ q A R w r hcfg i hi,
           ⟨fun j h3 hji =>
             hw O K C B G Kt L N v ρ q A R w r hcfg j h3
               (lt_of_le_of_lt hji hi.2)⟩⟩

/-- The assembly direction alone, in consumable form. -/
theorem deepTwistField_of_suppliers {n : ℕ}
    (hv : DeepVarthetaSupplier.{uG, uKt, uL} n)
    (hw : DeepGentowSupplier.{uG, uKt, uL} n) :
    DeepTwistField.{uG, uKt, uL} n :=
  deepTwistField_iff_suppliers.mpr ⟨hv, hw⟩

/-! Per-live-index projections ON the conjunct itself (the supply-map row's ask): any
`DeepTwistConjunctLive` proof yields the sitewise ϑ carrier at each live level and the
raw `GentowW` identity at each level `3 ≤ j < r`. -/

/-- Sitewise ϑ projection of the live deep-twist conjunct. -/
theorem deepTwistConjunctLive_vartheta_at {r : ℕ} {G : Type*} [CommGroup G]
    {Kt : Type*} [Field Kt] {L : Type*} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ}
    (h : Ladder.DeepTwistConjunctLive r v ρ q A R w) {i : ℕ}
    (hi : Tower.DeepLive r i) : Ladder.VarthetaRes G Kt L N v ρ q i :=
  (h i hi).1

/-- Per-level `GentowW` projection of the live deep-twist conjunct. -/
theorem deepTwistConjunctLive_gentowW_at {r : ℕ} {G : Type*} [CommGroup G]
    {Kt : Type*} [Field Kt] {L : Type*} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ}
    (h : Ladder.DeepTwistConjunctLive r v ρ q A R w) {j : ℕ}
    (h3 : 3 ≤ j) (hjr : j < r) : Gauge.GentowW (A j) (q j) (R j) (w j) :=
  ((h j ⟨h3, hjr⟩).2).supplied j h3 le_rfl

/-! ## §3 NODE W0 — the guarded weld-site supply socket

A-I.1's ruling (I-D7/I-D8): the all-sites shapes are refutable (gate item (13), landed
negative in F12w), so the three weld legs must bind TOGETHER through a site-supply
socket at the ARISING sites — the I.10a pattern.  No landed declaration exports weld
sites from chapter-C/H stage objects, so the arising guards `AV/AC/AF` are PARAMETERS
here, to be pinned by the WELD-SITE-SUPPLY campaign's canonical exporter before any
capstone-field binding (the empty-guard example below is the standing fabricability
disclosure; the total-guard refutation shows the guard is load-bearing). -/

section W0

open Uniformity.Density.Weld

variable {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ]
variable {Site CSite FSite : Type*}

/-- **The W0 socket**: the three weld obligations at ledger strength, bound together
(A-I.1's re-pointed L-1/L-2 trigger, `w1` debt included), each leg guarded by its
arising predicate; the `w1` leg restricted to the arising line subtype.
NEW STATEMENT (review). -/
structure ArisingWeldSiteSupply
    (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K)
    (AV : Site → Prop) (AC : CSite → Prop) (AF : FSite → Prop) : Prop where
  jd0box2 : ∀ s, AV s → JD0Box2 (vsite s)
  genhnBox2 : ∀ s, AC s → GenhnBox2 (csite s)
  w1 : W1Transport (fun l : {l // AF l} => Rh l.1) (fun l => RG l.1)

/-- Degeneration pin: at the TOTAL guards the socket is EXACTLY F.28's all-sites
`WeldObligations` — the shape A-I.1 refuted.  Machine-pinned so the socket's content is
visibly "the old bundle, guarded". -/
theorem arisingWeldSiteSupply_total_iff
    (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K) :
    ArisingWeldSiteSupply vsite csite Rh RG
        (fun _ => True) (fun _ => True) (fun _ => True) ↔
      WeldObligations vsite csite Rh RG := by
  constructor
  · rintro ⟨hj, hg, c, hc⟩
    exact ⟨fun s => hj s trivial, fun s => hg s trivial,
           ⟨fun l => c ⟨l, trivial⟩, fun l => hc ⟨l, trivial⟩⟩⟩
  · rintro ⟨hj, hg, c, hc⟩
    exact ⟨fun s _ => hj s, fun s _ => hg s, ⟨fun l => c l.1, fun l => hc l.1⟩⟩

/-- ★ TOOTH (F12w transported): the total-guard socket is REFUTED at the mismatched
vanishing-loci instance (`Rh = 1`, `RG = 0` over `ZMod 3`) — the arising guard is
load-bearing, exactly A-I.1's gate-item-(13) argument at this socket. -/
example :
    ¬ ArisingWeldSiteSupply (K := ZMod 3) (Γ := ℤ)
        (fun s : Empty => s.elim) (fun s : Empty => s.elim)
        (fun _ : Fin 1 => (1 : ZMod 3)) (fun _ => (0 : ZMod 3))
        (fun _ => True) (fun _ => True) (fun _ => True) := by
  rintro ⟨-, -, c, hc⟩
  have h := hc ⟨0, trivial⟩
  rw [mul_zero] at h
  exact one_ne_zero h

/-- FABRICABILITY DISCLOSURE: at the EMPTY guards the socket is trivially inhabited.
This is WHY the guards may never be left free at a capstone-field binding (the D-D12
fabricable-shape genre): the future owner amendment must pin them to the canonical site
exporter, which does not exist yet (BLOCKED-BECAUSE, design doc W0). -/
example (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K) :
    ArisingWeldSiteSupply vsite csite Rh RG
      (fun _ => False) (fun _ => False) (fun _ => False) where
  jd0box2 := fun _ h => h.elim
  genhnBox2 := fun _ h => h.elim
  w1 := ⟨fun l => l.2.elim, fun l => l.2.elim⟩

/-- Fold half at guarded sites (F04w's `JD0SiteStrike.jd0Box2`, composed): per-arising-
site strikes with site/ledger pins, plus the other two legs, assemble the socket. -/
theorem ArisingWeldSiteSupply.of_strikes
    {vsite : Site → ValueDictSite Γ K} {csite : CSite → CarrySite K}
    {Rh RG : FSite → K} {AV : Site → Prop} {AC : CSite → Prop} {AF : FSite → Prop}
    (str : ∀ s, AV s → JD0SiteStrike Γ K)
    (hsite : ∀ s (h : AV s), (str s h).site = vsite s)
    (hledger : ∀ s (h : AV s),
      (str s h).site.ledgerAct = gaugeCobdry fun γ => (str s h).z ^ (str s h).a γ)
    (hgen : ∀ s, AC s → GenhnBox2 (csite s))
    (hw1 : W1Transport (fun l : {l // AF l} => Rh l.1) (fun l => RG l.1)) :
    ArisingWeldSiteSupply vsite csite Rh RG AV AC AF where
  jd0box2 := fun s h => hsite s h ▸ (str s h).jd0Box2 (hledger s h)
  genhnBox2 := hgen
  w1 := hw1

end W0

/-! ## §4 NODE WIN0 — the real `WindowPinningAt` body, typed against `hwin`, not asserted

`WindowPinningAt n` is the signed `True` placeholder (I-D12; its re-sign is a later
recorded owner amendment — NOT made here).  The signed docstring's literal reading
("assert `hwin` over `StageInterface` instances") is vacuous, since `hwin` is a FIELD;
the contentful body speaks of the stage's window/loss numbers BEFORE the interface
exists.  As with W0, the unguarded reading is refutable (tooth below), so the body is
guarded by an arising predicate whose canonical instance (the GENHN-CAP-GEN reader rule)
is not yet formalized — H.89w supplies consulted-height LEMMAS at `e₁ = 2` only. -/

section WIN0

open Uniformity.Density.Induction

/-- The PRE-`hwin` stage-window datum: what a degree-`n` stage presents before the
interface exists — its consulted window and loss.  Indexing matches `StageInterface`.
NEW STATEMENT (review). -/
structure StageWindowData (G : GenreDatum) (N H S : ℕ) where
  stageWindow : ℕ
  stageLoss : ℕ

/-- `(CS-1Q.a)` at a datum — the BYTE-TIE to `StageInterface.hwin` (`H09.lean:93`),
pinned below; asserted nowhere.  NEW STATEMENT (review). -/
def StageWindowData.Pinned {G : GenreDatum} {N H S : ℕ}
    (d : StageWindowData G N H S) : Prop :=
  G.e₁ * (N - 1 - H) ≤ d.stageWindow + d.stageLoss

/-- Anti-drift pin: `Pinned` IS the `hwin` clause's statement, definitionally. -/
example {G : GenreDatum} {N H S : ℕ} (d : StageWindowData G N H S) :
    d.Pinned ↔ G.e₁ * (N - 1 - H) ≤ d.stageWindow + d.stageLoss := Iff.rfl

/-- The window datum of a full stage interface … -/
def stageWindowDataOf {G : GenreDatum} {N H S : ℕ}
    (st : StageInterface G N H S) : StageWindowData G N H S :=
  ⟨st.stageWindow, st.stageLoss⟩

/-- … is pinned, BY `hwin` and nothing else (the projection direction of the tie). -/
theorem stageWindowDataOf_pinned {G : GenreDatum} {N H S : ℕ}
    (st : StageInterface G N H S) : (stageWindowDataOf st).Pinned := st.hwin

/-- The extension direction of the tie: a PINNED datum is exactly the `hwin` ingredient
missing from a full `StageInterface` — given the remaining fields' data and laws, it
completes the interface.  (Bookkeeping: every hypothesis is a verbatim H.09 field.) -/
def stageInterfaceOfPinned {G : GenreDatum} {N H S : ℕ} (d : StageWindowData G N H S)
    (hd : d.Pinned) (entryCodim slack : ℕ) (bracket : ℕ → ℕ) (drainFrac : ℕ → ℝ)
    (stageSigma : FactorizationType) (hS : G.sideLen ≤ S)
    (hprice : 2 * (G.f₁ * d.stageLoss) ≤ 2 * entryCodim + (S - 2 * G.keyDeg) * H + 2 * slack)
    (hbracket : ∀ κ, 1 ≤ κ →
      bracket κ * G.stageCard = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ))
    (hdrain_nonneg : ∀ M, 0 ≤ drainFrac M) (hdrain_le_one : ∀ M, drainFrac M ≤ 1)
    (hsigma : G.μ = 2 → stageSigma.degree = 2 * G.keyDeg) : StageInterface G N H S :=
  { stageWindow := d.stageWindow, stageLoss := d.stageLoss, entryCodim := entryCodim,
    slack := slack, bracket := bracket, drainFrac := drainFrac, stageSigma := stageSigma,
    hS := hS, hwin := hd, hprice := hprice, hbracket := hbracket,
    hdrain_nonneg := hdrain_nonneg, hdrain_le_one := hdrain_le_one, hsigma := hsigma }

/-- **The intended I.05 body, GUARDED (the WIN0 interface)**: every ARISING degree-`n`
stage-window datum satisfies `(CS-1Q.a)`.  The degree tie and the reader rule live
INSIDE the guard family `Arises` (WIN0 invents no numeric degree formula on
`GenreDatum`); the canonical guard is the WINDOW-PINNING-RESOLUTION campaign's first
target.  NEW STATEMENT (review). -/
def WindowPinningBody
    (Arises : ℕ → ∀ ⦃G : GenreDatum⦄ ⦃N H S : ℕ⦄, StageWindowData G N H S → Prop)
    (n : ℕ) : Prop :=
  ∀ (G : GenreDatum) (N H S : ℕ) (d : StageWindowData G N H S), Arises n d → d.Pinned

/-- ★ TOOTH: the UNGUARDED reading is refuted — a concrete legal genre
(`Q=2, e₁=1, f₁=2, μ=2, h=1`) at `N=2, H=0` with the zero datum violates `(CS-1Q.a)`.
The arising guard is load-bearing (the I-D13 genre, defeated at the typed stage body). -/
example (n : ℕ) : ¬ WindowPinningBody (fun _ _ _ _ _ _ => True) n := by
  intro h
  have hc : (1 : ℕ) * (2 - 1 - 0) ≤ 0 + 0 :=
    h ⟨2, 1, 2, 2, 1, by omega, by omega, by omega, by omega, by omega, by decide⟩
      2 0 4 ⟨0, 0⟩ trivial
  omega

/-- FABRICABILITY DISCLOSURE: at the EMPTY guard the body is trivially inhabited — the
guard parameter may never be left free at the I.05 re-sign (same fence as W0). -/
example (n : ℕ) : WindowPinningBody (fun _ _ _ _ _ _ => False) n :=
  fun _ _ _ _ _ hfalse => hfalse.elim

end WIN0

end Uniformity.Density.IFC0

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Every declaration is a statement carrier or decomposition bookkeeping; nothing here may
add to the trusted base. -/

#print axioms Uniformity.Density.IFC0.LadderField
#print axioms Uniformity.Density.IFC0.LadderPackageSupplier
#print axioms Uniformity.Density.IFC0.LadderLB1Supplier
#print axioms Uniformity.Density.IFC0.LadderMP1Supplier
#print axioms Uniformity.Density.IFC0.LadderVarthetaSupplier
#print axioms Uniformity.Density.IFC0.ladderField_iff_suppliers
#print axioms Uniformity.Density.IFC0.ladderField_of_suppliers
#print axioms Uniformity.Density.IFC0.DeepTwistField
#print axioms Uniformity.Density.IFC0.DeepVarthetaSupplier
#print axioms Uniformity.Density.IFC0.DeepGentowSupplier
#print axioms Uniformity.Density.IFC0.deepTwistField_iff_suppliers
#print axioms Uniformity.Density.IFC0.deepTwistField_of_suppliers
#print axioms Uniformity.Density.IFC0.deepTwistConjunctLive_vartheta_at
#print axioms Uniformity.Density.IFC0.deepTwistConjunctLive_gentowW_at
#print axioms Uniformity.Density.IFC0.ArisingWeldSiteSupply
#print axioms Uniformity.Density.IFC0.arisingWeldSiteSupply_total_iff
#print axioms Uniformity.Density.IFC0.ArisingWeldSiteSupply.of_strikes
#print axioms Uniformity.Density.IFC0.StageWindowData
#print axioms Uniformity.Density.IFC0.StageWindowData.Pinned
#print axioms Uniformity.Density.IFC0.stageWindowDataOf
#print axioms Uniformity.Density.IFC0.stageWindowDataOf_pinned
#print axioms Uniformity.Density.IFC0.stageInterfaceOfPinned
#print axioms Uniformity.Density.IFC0.WindowPinningBody
