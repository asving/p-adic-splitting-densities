/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136c0
import Uniformity.ChapI.I10RecenterDirect

/-!
# Uniformity.ChapI.I10Universal — G10: the occurrence→universal exporter family and the
deepTwist universal-supplier boundary [G10U 2026-08-29]

**Campaign row G10** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` (§6.1 [DWR]
row + §11.4, as re-scoped by §12.5: the `MP1EmissionPerWitnessExporter` half is DELETED —
the generic A-I.8 compiler supersedes it — and the deep-level/vartheta universal half is
retained).  This file lands the universal side of the deep-witness campaign's supplier
boundary:

## What lands

* **§1 the view-transport engine** — `hvarthetaRes_of_view` / `gentowW_of_view`: the two
  sitewise Display-A carriers transport from a witness's OWN exports to any external
  socket data tied to them by the landed CC-12 view equalities along a lattice
  equivalence `e`.  This is exact bookkeeping (no new mathematics): `HVarthetaRes` and
  `GentowW` are built from the `KernelRead` pair, the normalizer values, the read, and
  the peel unit — precisely the data the views pin at live indices.
* **§2 the G10 per-witness exporter shapes** (DWR §11.4's quantifier discipline, at the
  deep-live range): `VarthetaPerWitnessExporter X` and `GentowPerWitnessExporter X`, plus
  the generic compilers `varthetaPerWitnessExporter_of_tauSources` (per-level
  `CanonicalTauLetterSource` → exporter; engine = C0123's
  `varthetaRes_of_canonicalTauLetterSource`) and `gentowPerWitnessExporter_of_sites`
  (per-level G3 site package + the three WLE consumer dictionaries → exporter; engine =
  G345's `wiredDemand_of_level_export`).  Shallow-witness vacuity teeth included.
* **§3 the per-witness → external transports** at one realized witness: the exporters at
  the witness's own exports yield `VarthetaRes`/`GentowW` at ANY socket data bound to the
  same witness by `GaugeFamilyViewEq`/`ArenaFamilyViewEq` (the I.10b joint-witness view
  shapes, verbatim).
* **§4 the conjunct assemblies**: `deepTwistConjunctLive_own_of_exporters` (the two
  exporters ARE the own-export deep-twist conjunct) and
  `deepTwistConjunctLive_of_perWitness_views` (the external conjunct at any joint-witness
  view binding).
* **§5 ★ THE EXACT SUPPLIER BOUNDARY**: `UniversalVarthetaSupplier n` /
  `UniversalGentowSupplier n` (the per-witness exporters at EVERY arising realization),
  and the machine-checked exactness

  `deepTwistField_iff_universalPerWitness :
     IFC0.DeepTwistField n ↔ UniversalVarthetaSupplier n ∧ UniversalGentowSupplier n`

  (the iff at the ARISING universe profile `uKt = 0` — the signed socket's `K` binder is
  `Type`, A-I.3's "0 is the universe of every arising instance" disclosure; the assembly
  direction `deepTwistField_of_universalPerWitness` is fully polymorphic).
  Assembly: unpack the joint witness and transport (§3/§4).  Converse: every witness
  exports its own configuration (C130s18's CC-18 socket application
  `realizedInput_deepTwistConfigData`), and IFC0's per-live projections read the
  exporters off the conjunct.  **This is the honest answer to "what does the capstone's
  `deepTwist` field demand beyond G10": exactly the two universal suppliers — the
  quantification of the per-witness exporters over EVERY arising realization** (all
  `O/Kt/E/L`, every `ChainRealization`, every `RealizedInput`), not only the wired
  keystone genre.  The field does NOT close today: the suppliers are OPEN at general
  witnesses (campaign rows C1/C2 — the theta/peel/range dictionaries at general residue
  cardinality — and C3/R5 — the tau-word triangular spanning and OPEN-LETTERS).
* **§6 the superseded MP1 half, recorded**: `mp1PerWitnessEmission` — the per-witness
  "every same-witness exported recenter step" quantifier of DWR §11.4's second exporter
  is HELD, as a one-line projection of the generic A-I.8 compiler
  `midPeelEmission_of_recenterStepDirect` (per §12.5 this half is superseded, not
  re-introduced: no new statement shape, a theorem only).
* **§7 the wired-genre instances (G10 at the SplitNodeWired/keystone genre)**: at EVERY
  depth-4 keystone witness — quantified over the full parametric payload
  `(F₀, hF₀, μ, hμ, hdeg, hblock, hcop)`, the four thresholds and `L` —
  `s2Four_varthetaPerWitnessExporter`, `s2Four_gentowPerWitnessExporter`, and
  ★ `s2Four_deepTwistConjunctLive`: the full own-export deep-twist conjunct at the whole
  genre (generalizing C56R's one-payload tooth `s2C6_deepTwistTooth` to every payload).
  These inhabit the §2 exporter shapes — the occurrence teeth are the nonvacuity of the
  §5 supplier boundary at the wired genre.

## Honesty scope

* Nothing here discharges the capstone `deepTwist` field: §5 REPARTITIONS it, byte-exactly
  against IFC0's DT0 split, into the two named universal suppliers, and §7 inhabits those
  suppliers' per-witness cores at the S2 depth-4 keystone genre ONLY.  The wired-genre
  instances inherit exactly the keystone's conditionality (the four open threshold datums
  `w₁ w₂ w₃ w₄`, the parametric R8r payload, `IsAdicComplete`); nothing new is assumed.
* `package`/`lb1` (HE7A/LB1) are NOT touched — separate campaigns, exactly as the ladder
  record's honest asymmetry records.
* The §1/§3 transports are stated at the landed view equalities verbatim — no view is
  weakened, no owner or view is spliced (the D-D12 anti-cook fences are inherited from
  the view definitions themselves).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`VarthetaPerWitnessExporter`, `GentowPerWitnessExporter`, `UniversalVarthetaSupplier`,
`UniversalGentowSupplier` (the four supplier-side interface `Prop`s below the signed
surface; no leanspec name is touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_G10U.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uW uG uKt uL

/-! ## §1 The view-transport engine (generic; exact bookkeeping) -/

section ViewTransport

universe u₁ u₂

variable {G : Type u₁} [CommGroup G] {G' : Type u₂} [CommGroup G']
  {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]

/-- Definitional pin: the transported arena's residue read is the source read at the
pulled-back element. -/
theorem GaugeArena.transport_res_apply {N : NormSection G} (A : GaugeArena G Kt N)
    (e : G ≃* G') (x : G') (hx : x ∈ MonoidHom.ker (A.transport e).v) :
    (A.transport e).res ⟨x, hx⟩ = A.res ⟨e.symm x, hx⟩ := rfl

/-- **The sitewise ϑ carrier transports along a lattice equivalence at pinned view data**:
if the primed datum `(N', v', ρ', q')` is the `e`-pullback of `(N, v, ρ, q)` — normalizer
values through `e`, the `KernelRead` pair through `e.symm`/`kerComapAlong`, equal
use-height — then `HVarthetaRes` at the primed datum yields it at the source datum.
Exact bookkeeping: `varthetaEl` is a word in normalizer values, and the reads agree on it
through the pair equality. -/
theorem hvarthetaRes_of_view {N : NormSection G} {N' : NormSection G'} (e : G ≃* G')
    {v : G →* Multiplicative ℤ} {v' : G' →* Multiplicative ℤ}
    {ρ : MonoidHom.ker v →* Lˣ} {ρ' : MonoidHom.ker v' →* Lˣ} {q q' : ℤ}
    (hn : ∀ k, e (N.n k) = N'.n k)
    (hpair : (⟨v.comp e.symm.toMonoidHom, ρ.comp (C130s18.kerComapAlong e v)⟩ :
      KernelRead G' Lˣ) = ⟨v', ρ'⟩)
    (hq : q = q')
    (h : HVarthetaRes G' Kt L N' v' ρ' q') : HVarthetaRes G Kt L N v ρ q := by
  subst hq
  intro s
  obtain ⟨h', u, hu⟩ := h s
  have hel : e (N.varthetaEl q s) = N'.varthetaEl q s := by
    rw [NormSection.varthetaEl, NormSection.varthetaEl, map_mul, map_pow, map_inv,
      hn, hn]
  have hv' : v.comp e.symm.toMonoidHom = v' := congrArg Sigma.fst hpair
  have hcast : N'.varthetaEl q s ∈ MonoidHom.ker (v.comp e.symm.toMonoidHom) := by
    rw [hv']; exact h'
  have hmem : N.varthetaEl q s ∈ MonoidHom.ker v := by
    have hc := hcast
    rw [MonoidHom.mem_ker] at hc ⊢
    rw [← hel] at hc
    simpa using hc
  refine ⟨hmem, u, ?_⟩
  have hval : ρ ⟨N.varthetaEl q s, hmem⟩ = ρ' ⟨N'.varthetaEl q s, h'⟩ := by
    have h1 := kernelRead_snd_congr hpair hcast h'
    rw [← h1]
    show ρ ⟨N.varthetaEl q s, hmem⟩ =
      ρ (C130s18.kerComapAlong e v ⟨N'.varthetaEl q s, hcast⟩)
    congr 1
    ext
    show N.varthetaEl q s = e.symm (N'.varthetaEl q s)
    rw [← hel, e.symm_apply_apply]
  rw [hval]
  exact hu

/-- **The sitewise B-law transports along a lattice equivalence at pinned view data**:
if the primed arena/read/peel data are the `e`-pullback of `(A, q, R, w)` — the
transported arena's `KernelRead` pair equal to the primed arena's, the read through
`e.symm`, equal use-height and peel unit — then `GentowW` at the primed data yields it at
the source data.  Exact bookkeeping: `theta` reads a normalizer word through the arena's
residue read. -/
theorem gentowW_of_view {N : NormSection G} {N' : NormSection G'} (e : G ≃* G')
    {A : GaugeArena G Kt N} {A' : GaugeArena G' Kt N'}
    {q q' : ℤ} {R : G → Kt} {R' : G' → Kt} {w w' : Ktˣ}
    (hn : ∀ k, e (N.n k) = N'.n k)
    (hpair : (⟨(A.transport e).v, (A.transport e).res⟩ : KernelRead G' Ktˣ) =
      ⟨A'.v, A'.res⟩)
    (hq : q = q') (hR : ∀ g : G', R (e.symm g) = R' g) (hw : w = w')
    (h : GentowW A' q' R' w') : GentowW A q R w := by
  subst hq
  subst hw
  intro s
  have hth : e (N.thetaEl q s) = N'.thetaEl q s := by
    rw [NormSection.thetaEl, NormSection.thetaEl, map_mul, map_inv, map_pow, hn, hn]
  have hL : R (N.n (s * q)) = R' (N'.n (s * q)) := by
    rw [← hn (s * q), ← hR (e (N.n (s * q))), e.symm_apply_apply]
  have hmem : N'.thetaEl q s ∈ MonoidHom.ker (A.transport e).v := by
    rw [MonoidHom.mem_ker, ← hth]
    show A.v (e.symm (e (N.thetaEl q s))) = 1
    rw [e.symm_apply_apply]
    exact A.thetaEl_mem_ker q s
  have htheta : A'.theta q s = A.theta q s := by
    have h1 := kernelRead_snd_congr hpair hmem (A'.thetaEl_mem_ker q s)
    rw [GaugeArena.theta, GaugeArena.theta, ← h1]
    show A.res ⟨e.symm (N'.thetaEl q s), hmem⟩ = A.res ⟨N.thetaEl q s, _⟩
    congr 1
    ext
    show e.symm (N'.thetaEl q s) = N.thetaEl q s
    rw [← hth, e.symm_apply_apply]
  rw [hL, h s, htheta]

end ViewTransport

/-! ## §2 The G10 per-witness exporter shapes and their generic compilers -/

section Exporters

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-- **[G10] The per-witness sitewise-ϑ exporter** (DWR §11.4's quantifier discipline at
the vartheta half): after the witness is explicit, EVERY deep-live level carries the
sitewise `VarthetaRes` at the witness's OWN canonical exports.  Deep inhabitants at the
wired genre are §7; general inhabitants are campaign rows C3/R5 (OPEN).
NEW STATEMENT (review). -/
def VarthetaPerWitnessExporter (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, DeepLive core.r j →
    Ladder.VarthetaRes (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) j

/-- **[G10] The per-witness `GentowW` exporter** (the `𝒲`-frame half): after the witness
is explicit, EVERY deep-live level carries D.44's raw `[GENTOW5-W(j)]` identity at the
witness's OWN arena/use-height/read/peel-unit exports.  Deep inhabitants at the wired
genre are §7; general inhabitants are campaign rows C1/C2 (OPEN).
NEW STATEMENT (review). -/
def GentowPerWitnessExporter (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    GentowW
      (arenaFamily.{0, uG, uKt, uL} X (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j)

/-- **[G10] The generic vartheta compiler**: a per-level canonical tau-letter source at
every deep-live level compiles to the per-witness exporter — pointwise C0123's
`varthetaRes_of_canonicalTauLetterSource` at the canonical socket view (`eG = refl`,
view = the witness's own producing equality).  This is a universally quantified theorem
at every witness; one `j = 3` source is only its nonvacuity tooth. -/
theorem varthetaPerWitnessExporter_of_tauSources (X : RealizedInput core Aℛ)
    (h : ∀ j, (hj : DeepLive core.r j) →
      CanonicalTauLetterSource X (GaugeLattice.{uG} core.r) (MulEquiv.refl _)
        (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
        (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) j
        hj.gaugeLive) :
    VarthetaPerWitnessExporter.{uG, uKt, uL} X :=
  fun j hj => varthetaRes_of_canonicalTauLetterSource (h j hj)

/-- **[G10] The generic `GentowW` compiler**: a G3 site package WITH its three WLE
consumer dictionaries at every deep-live level compiles to the per-witness exporter —
pointwise G345's `wiredDemand_of_level_export` (the signed sitewise demand), projected at
its `gentowW` leg.  Universally quantified at every witness; the depth-4 keystone site is
only its nonvacuity tooth. -/
theorem gentowPerWitnessExporter_of_sites (X : RealizedInput core Aℛ)
    (h : ∀ j, (hj : DeepLive core.r j) →
      ∃ S : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le,
        ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S ∧
        PeelCompatibleAt X S ∧
        RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S) :
    GentowPerWitnessExporter.{uG, uKt, uL} X := by
  intro j hj
  obtain ⟨S, hθ, hw, hrange⟩ := h j hj
  exact (wiredDemand_of_level_export hj S hθ hw hrange).gentowW

/-- **[G10] The bridge from the LANDED G4 exporter**: the shared-record per-witness
exporter (`DeepLevelPerWitnessExporter`, G345 shape / C0123 witness instance) plus the
three WLE consumer dictionaries at every site compile to the `GentowW` exporter — the G4
record's `site` projection feeds the signed sitewise demand.  (The dictionary hypothesis
quantifies over ALL sites because the G4 exporter supplies its site only up to
`Nonempty`.) -/
theorem gentowPerWitnessExporter_of_deepExports (X : RealizedInput core Aℛ)
    (hexp : DeepLevelPerWitnessExporter.{uG, uKt, uL} X)
    (hdict : ∀ j, (hj : DeepLive core.r j) →
      ∀ S : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le,
        ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S ∧
        PeelCompatibleAt X S ∧
        RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S) :
    GentowPerWitnessExporter.{uG, uKt, uL} X := by
  intro j hj
  obtain ⟨D⟩ := hexp j hj
  obtain ⟨hθ, hw, hrange⟩ := hdict j hj D.site
  exact (wiredDemand_of_level_export hj D.site hθ hw hrange).gentowW

/-- Vacuity tooth: at depth `r ≤ 3` the vartheta exporter holds vacuously — shallow
witnesses supply NO deep evidence (the same fence as
`deepLevelPerWitnessExporter_of_shallow`). -/
theorem varthetaPerWitnessExporter_of_shallow (X : RealizedInput core Aℛ)
    (hr : core.r ≤ 3) : VarthetaPerWitnessExporter.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

/-- Vacuity tooth: at depth `r ≤ 3` the `GentowW` exporter holds vacuously. -/
theorem gentowPerWitnessExporter_of_shallow (X : RealizedInput core Aℛ)
    (hr : core.r ≤ 3) : GentowPerWitnessExporter.{uG, uKt, uL} X := by
  intro j hj
  rcases hj with ⟨hj3, hjr⟩
  omega

/-! ## §3 The per-witness → external transports (one witness, the joint-view binding) -/

/-- The witness's own-export `VarthetaRes` at a gauge-live level transports to ANY
external socket datum bound to the same witness by the I.10b gauge view along `eG`. -/
theorem varthetaRes_of_perWitness_view
    {G : Type uG} [CommGroup G] {N : NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)} {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ}
    {q : ℕ → ℤ}
    (X : RealizedInput core Aℛ) (eG : G ≃* GaugeLattice.{uG} core.r)
    (hgauge : GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (C130s18.kerComapAlong eG (v j))) q)
    {j : ℕ} (hj : GaugeLive core.r j)
    (h : Ladder.VarthetaRes (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) j) :
    Ladder.VarthetaRes G Kt L N v ρ q j := by
  have hgv := RealizedInput.gaugeFamilyViewEq.{0, uKt, uL, uG} X
  refine ⟨hvarthetaRes_of_view eG (fun k => congrFun hgauge.1 k)
    (((hgauge.2 j hj).1).trans ((hgv.2 j hj).1).symm)
    (((hgauge.2 j hj).2).trans ((hgv.2 j hj).2).symm)
    h.supplied⟩

/-- The witness's own-export `GentowW` at a gauge-live level transports to ANY external
arena/read/peel datum bound to the same witness by the I.10b arena view along `eG` (the
gauge view supplies the normalizer and use-height ties). -/
theorem gentowW_of_perWitness_view
    {G : Type uG} [CommGroup G] {N : NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)} {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ}
    {q : ℕ → ℤ}
    {A : ℕ → GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ}
    (X : RealizedInput core Aℛ) (eG : G ≃* GaugeLattice.{uG} core.r)
    (hgauge : GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (C130s18.kerComapAlong eG (v j))) q)
    (harena : ArenaFamilyViewEq X (N.transport eG)
      (fun j => (A j).transport eG) (fun j g => R j (eG.symm g)) w)
    {j : ℕ} (hj : GaugeLive core.r j) (hr : 1 < core.r)
    (h : GentowW (arenaFamily.{0, uG, uKt, uL} X hr j) (useHeightFamily X j)
      (towerReadFamily X j) (Aℛ.node.peelUnitFamily j)) :
    GentowW (A j) (q j) (R j) (w j) := by
  have hown := X.arenaFamilyViewEq hr
  have hgv := RealizedInput.gaugeFamilyViewEq.{0, uKt, uL, uG} X
  exact gentowW_of_view eG (fun k => congrFun hgauge.1 k)
    (((harena j hj).1).trans ((hown j hj).1).symm)
    (((hgauge.2 j hj).2).trans ((hgv.2 j hj).2).symm)
    (fun g => ((harena j hj).2.1 g).trans ((hown j hj).2.1 g).symm)
    (((harena j hj).2.2).trans ((hown j hj).2.2).symm)
    h

/-! ## §4 The conjunct assemblies -/

/-- **The two exporters ARE the own-export deep-twist conjunct**: at the witness's own
exports, `DeepTwistConjunctLive` is exactly the vartheta exporter paired with the
`GentowW` exporter accumulated over `3 ≤ j ≤ i` (every such `j` is deep-live). -/
theorem deepTwistConjunctLive_own_of_exporters (X : RealizedInput core Aℛ)
    (hr : 1 < core.r)
    (hvar : VarthetaPerWitnessExporter.{uG, uKt, uL} X)
    (hgen : GentowPerWitnessExporter.{uG, uKt, uL} X) :
    Ladder.DeepTwistConjunctLive core.r
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X)
      (arenaFamily.{0, uG, uKt, uL} X hr) (towerReadFamily X)
      Aℛ.node.peelUnitFamily := by
  intro i hi
  refine ⟨hvar i hi, ⟨fun j hj3 hji => ?_⟩⟩
  exact hgen j ⟨hj3, lt_of_le_of_lt hji hi.2⟩

/-- **The external deep-twist conjunct at any joint-witness view binding**: the two
per-witness exporters, transported through the I.10b views along `eG`, assemble the full
`DeepTwistConjunctLive` at the EXTERNAL socket data `(v, ρ, q, A, R, w)` and the
witness's own depth. -/
theorem deepTwistConjunctLive_of_perWitness_views
    {G : Type uG} [CommGroup G] {N : NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)} {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ}
    {q : ℕ → ℤ}
    {A : ℕ → GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ}
    (X : RealizedInput core Aℛ) (eG : G ≃* GaugeLattice.{uG} core.r)
    (hgauge : GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (C130s18.kerComapAlong eG (v j))) q)
    (harena : ArenaFamilyViewEq X (N.transport eG)
      (fun j => (A j).transport eG) (fun j g => R j (eG.symm g)) w)
    (hvar : VarthetaPerWitnessExporter.{uG, uKt, uL} X)
    (hgen : GentowPerWitnessExporter.{uG, uKt, uL} X) :
    Ladder.DeepTwistConjunctLive core.r v ρ q A R w := by
  intro i hi
  have hr : 1 < core.r := by rcases hi with ⟨hi3, hir⟩; omega
  refine ⟨varthetaRes_of_perWitness_view X eG hgauge hi.gaugeLive (hvar i hi),
    ⟨fun j hj3 hji => ?_⟩⟩
  have hjd : DeepLive core.r j := ⟨hj3, lt_of_le_of_lt hji hi.2⟩
  exact gentowW_of_perWitness_view X eG hgauge harena hjd.gaugeLive hr (hgen j hjd)

end Exporters

/-! ## §5 ★ The exact supplier boundary: the capstone `deepTwist` field IS the universal
per-witness supplier pair -/

/-- **The universal vartheta supplier**: the per-witness sitewise-ϑ exporter at EVERY
arising realization of degree `n` — all `O/Kt/E/L`, every chain realization, every
realized input.  This (with its `GentowW` twin) is EXACTLY what the capstone `deepTwist`
field demands beyond the wired-genre occurrences (`deepTwistField_iff_universalPerWitness`
below).  OPEN at general witnesses (campaign rows C3/R5); inhabited per-witness at the
wired genre (§7).  NEW STATEMENT (review). -/
def UniversalVarthetaSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    VarthetaPerWitnessExporter.{uG, uKt, uL} X

/-- **The universal `GentowW` supplier**: the per-witness `𝒲`-frame exporter at EVERY
arising realization of degree `n`.  OPEN at general witnesses (campaign rows C1/C2);
inhabited per-witness at the wired genre (§7).  NEW STATEMENT (review). -/
def UniversalGentowSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    GentowPerWitnessExporter.{uG, uKt, uL} X

/-- The universal vartheta supplier discharges IFC0's DT0 sitewise-ϑ leg: unpack the
joint witness, transport its exporter through the views. -/
theorem deepVarthetaSupplier_of_universal {n : ℕ}
    (h : UniversalVarthetaSupplier.{uG, uKt, uL} n) :
    IFC0.DeepVarthetaSupplier.{uG, uKt, uL} n := by
  intro O _ K _ C B G _ Kt _ L _ _ N v ρ q A R w r hcfg i hi
  obtain ⟨-, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrr, -, -, hgauge, harena⟩ := hcfg
  letI := dom
  letI := dvr
  letI := fE
  subst hrr
  exact varthetaRes_of_perWitness_view X eG hgauge hi.gaugeLive
    (h O Kt E L core Aℛ X i hi)

/-- The universal `GentowW` supplier discharges IFC0's DT0 per-level-`GentowW` leg. -/
theorem deepGentowSupplier_of_universal {n : ℕ}
    (h : UniversalGentowSupplier.{uG, uKt, uL} n) :
    IFC0.DeepGentowSupplier.{uG, uKt, uL} n := by
  intro O _ K _ C B G _ Kt _ L _ _ N v ρ q A R w r hcfg j h3 hjr
  obtain ⟨-, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrr, -, -, hgauge, harena⟩ := hcfg
  letI := dom
  letI := dvr
  letI := fE
  subst hrr
  have hjd : DeepLive core.r j := ⟨h3, hjr⟩
  have hr : 1 < core.r := by omega
  exact gentowW_of_perWitness_view X eG hgauge harena hjd.gaugeLive hr
    (h O Kt E L core Aℛ X j hjd)

/-- Converse: the capstone `deepTwist` field yields the universal vartheta supplier —
every witness exports its own configuration (CC-18's literal socket application), and the
field's conjunct projects to the exporter at every deep-live level.

UNIVERSE NOTE: stated at the ARISING profile `uKt = 0` — the signed socket's `K` binder is
`Type` (A-I.3's disclosure: "`0` is the universe of every arising instance"), so the
witness's own stage carrier `core.T.fld core.i` can be the socket's `K` exactly when the
terminal-field universe is `0`.  The assembly direction below is fully polymorphic. -/
theorem universalVartheta_of_deepTwistField {n : ℕ}
    (h : IFC0.DeepTwistField.{uG, 0, uL} n) :
    UniversalVarthetaSupplier.{uG, 0, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X j hj
  have hr : 1 < core.r := by rcases hj with ⟨hj3, hjr⟩; omega
  have hconj := h O (core.T.fld core.i)
    (X.stageCarrierTransport (RingEquiv.refl (core.T.fld core.i)))
    (X.inputBlockTransport (RingEquiv.refl (core.T.fld core.i)))
    (GaugeLattice.{uG} core.r) Kt L
    (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
    (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X)
    (arenaFamily X hr) (towerReadFamily X) Aℛ.node.peelUnitFamily core.r
    (C130s18.realizedInput_deepTwistConfigData X (RingEquiv.refl _) hr)
  exact IFC0.deepTwistConjunctLive_vartheta_at hconj hj

/-- Converse: the capstone `deepTwist` field yields the universal `GentowW` supplier
(same arising-profile universe note as `universalVartheta_of_deepTwistField`). -/
theorem universalGentow_of_deepTwistField {n : ℕ}
    (h : IFC0.DeepTwistField.{uG, 0, uL} n) :
    UniversalGentowSupplier.{uG, 0, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X j hj
  have hr : 1 < core.r := by rcases hj with ⟨hj3, hjr⟩; omega
  have hconj := h O (core.T.fld core.i)
    (X.stageCarrierTransport (RingEquiv.refl (core.T.fld core.i)))
    (X.inputBlockTransport (RingEquiv.refl (core.T.fld core.i)))
    (GaugeLattice.{uG} core.r) Kt L
    (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
    (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X)
    (arenaFamily X hr) (towerReadFamily X) Aℛ.node.peelUnitFamily core.r
    (C130s18.realizedInput_deepTwistConfigData X (RingEquiv.refl _) hr)
  exact IFC0.deepTwistConjunctLive_gentowW_at hconj hj.1 hj.2

/-- The assembly direction, in consumable form and FULLY POLYMORPHIC: the two universal
suppliers give the capstone `deepTwist` field, at every universe profile. -/
theorem deepTwistField_of_universalPerWitness {n : ℕ}
    (hv : UniversalVarthetaSupplier.{uG, uKt, uL} n)
    (hw : UniversalGentowSupplier.{uG, uKt, uL} n) :
    IFC0.DeepTwistField.{uG, uKt, uL} n :=
  IFC0.deepTwistField_of_suppliers
    (deepVarthetaSupplier_of_universal hv) (deepGentowSupplier_of_universal hw)

/-- ★ **THE G10 EXIT GATE — the supplier boundary is EXACT**: the capstone `deepTwist`
field at degree `n` is EQUIVALENT to the pair of universal per-witness suppliers, at the
arising universe profile (`uKt = 0`; see `universalVartheta_of_deepTwistField`'s note —
the assembly direction holds at every profile).  Nothing is discharged: the field's open
content is repartitioned, machine-exactly, into the two named universal suppliers — the
site-package quantification over every arising realization.  The wired-genre instances
(§7) inhabit the per-witness cores at the depth-4 keystone genre; the general suppliers
remain the campaign's open boundary. -/
theorem deepTwistField_iff_universalPerWitness {n : ℕ} :
    IFC0.DeepTwistField.{uG, 0, uL} n ↔
      UniversalVarthetaSupplier.{uG, 0, uL} n ∧
        UniversalGentowSupplier.{uG, 0, uL} n :=
  ⟨fun h => ⟨universalVartheta_of_deepTwistField h, universalGentow_of_deepTwistField h⟩,
   fun h => deepTwistField_of_universalPerWitness h.1 h.2⟩

/-! ## §6 The superseded MP1 half, recorded (no new statement shape) -/

section MP1Record

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-- **DWR §11.4's second exporter, HELD via the superseding compiler** (§12.5: the
`MP1EmissionPerWitnessExporter` shape is deleted, not re-introduced — this is a theorem
recording that the per-witness quantifier over every same-witness exported recenter step
is subsumed): at any witness's own exported carrier and block, EVERY direct recenter step
emits.  Proof: the generic A-I.8 compiler, verbatim. -/
theorem mp1PerWitnessEmission (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K)
    {G : Type uG} [CommGroup G] {N : Gauge.NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)} {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ}
    {q : ℕ → ℤ}
    (B' : Ladder.BlockData (X.stageCarrierTransport eK)) (Λ : Polynomial O)
    (hstep : IFC5.RecenterStepDirect.{uW, uG, uKt, uL}
      (X.stageCarrierTransport eK) (X.inputBlockTransport eK) B' G Kt L N v ρ q n Λ) :
    Nonempty (Ladder.MidPeelEmission.{0, 0, uW} (X.inputBlockTransport eK) B') :=
  IFC5.midPeelEmission_of_recenterStepDirect hstep

end MP1Record

/-! ## §7 The wired-genre instances: G10 at the SplitNodeWired/keystone genre -/

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

/-- ★ **[G10 wired instance, vartheta half]** — the per-witness sitewise-ϑ exporter at
EVERY depth-4 keystone witness (full parametric payload; `DeepLive 4 j` forces `j = 3`,
where C0123's `s2Four_varthetaRes` fires).  Conditionality: exactly the keystone's. -/
theorem s2Four_varthetaPerWitnessExporter :
    VarthetaPerWitnessExporter.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact s2Four_varthetaRes h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj.gaugeLive

/-- ★ **[G10 wired instance, `𝒲`-frame half]** — the per-witness `GentowW` exporter at
EVERY depth-4 keystone witness (C0123's wired sitewise demand, projected at its raw
`GentowW` leg).  Conditionality: exactly the keystone's. -/
theorem s2Four_gentowPerWitnessExporter :
    GentowPerWitnessExporter.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact (s2Four_wiredGentowDemand h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
    hj).gentowW

/-- ★★ **[G10 wired exit] THE GENRE-WIDE DEEP-TWIST CONJUNCT** — the full own-export
`DeepTwistConjunctLive` at EVERY depth-4 keystone witness, assembled from the two wired
exporters.  This generalizes C56R's one-payload tooth (`s2C6_deepTwistTooth`, at
`F₀ = leaf·(g16+1)`) to the whole parametric genre — the occurrence→universal boundary at
the wired genre is CLOSED; what remains open for the capstone field is §5's universal
supplier pair at general (non-wired) witnesses. -/
theorem s2Four_deepTwistConjunctLive :
    Ladder.DeepTwistConjunctLive 4
      (gaugeHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (arenaFamily.{0, 0, 0, uL}
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
        (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop))
      (towerReadFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily :=
  deepTwistConjunctLive_own_of_exporters
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_varthetaPerWitnessExporter h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (s2Four_gentowPerWitnessExporter h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.GaugeArena.transport_res_apply
#print axioms Uniformity.Density.DeepExport.hvarthetaRes_of_view
#print axioms Uniformity.Density.DeepExport.gentowW_of_view
#print axioms Uniformity.Density.DeepExport.VarthetaPerWitnessExporter
#print axioms Uniformity.Density.DeepExport.GentowPerWitnessExporter
#print axioms Uniformity.Density.DeepExport.varthetaPerWitnessExporter_of_tauSources
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_sites
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_deepExports
#print axioms Uniformity.Density.DeepExport.varthetaPerWitnessExporter_of_shallow
#print axioms Uniformity.Density.DeepExport.gentowPerWitnessExporter_of_shallow
#print axioms Uniformity.Density.DeepExport.varthetaRes_of_perWitness_view
#print axioms Uniformity.Density.DeepExport.gentowW_of_perWitness_view
#print axioms Uniformity.Density.DeepExport.deepTwistConjunctLive_own_of_exporters
#print axioms Uniformity.Density.DeepExport.deepTwistConjunctLive_of_perWitness_views
#print axioms Uniformity.Density.DeepExport.UniversalVarthetaSupplier
#print axioms Uniformity.Density.DeepExport.UniversalGentowSupplier
#print axioms Uniformity.Density.DeepExport.deepVarthetaSupplier_of_universal
#print axioms Uniformity.Density.DeepExport.deepGentowSupplier_of_universal
#print axioms Uniformity.Density.DeepExport.universalVartheta_of_deepTwistField
#print axioms Uniformity.Density.DeepExport.universalGentow_of_deepTwistField
#print axioms Uniformity.Density.DeepExport.deepTwistField_iff_universalPerWitness
#print axioms Uniformity.Density.DeepExport.deepTwistField_of_universalPerWitness
#print axioms Uniformity.Density.DeepExport.mp1PerWitnessEmission
#print axioms Uniformity.Density.DeepExport.s2Four_varthetaPerWitnessExporter
#print axioms Uniformity.Density.DeepExport.s2Four_gentowPerWitnessExporter
#print axioms Uniformity.Density.DeepExport.s2Four_deepTwistConjunctLive

end AxCheck
