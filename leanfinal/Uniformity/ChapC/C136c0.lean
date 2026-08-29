/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136r4
import Uniformity.ChapD.D62w
import Uniformity.ChapI.IFC5

/-!
# Uniformity.ChapC.C136c0 — the deep-witness consumer legs C0/C1/C2/C3 [C0123 2026-08-29]

**Rows C0–C3** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.5, at the R67
keystone (`C136r4`): the G3 site package is built at the exact realized witness and the
unique deep-live level `j = 3`, the shared G4 `DeepLevelExport` is INHABITED through the
keystone's `s2Four_deepLevelExport_of_site`, the three WLE consumer dictionaries are
proved and the signed `WiredGentowDemand` fired at the witness's own exports, and the
canonical tau/vartheta chain lands **the project's first live-index `VarthetaRes`**.

## What lands (row → artifact)

* **C1 (the single-`w` law).**  The site calculus `s2SiteMu4Calculus` — the SAME seven μ₄
  operators as D3-18/19, repackaged by `fgmnCalculusOf` at the truncated tower
  `s2TruncThree := (s2DepthFour).trunc 3` (R5's recorded site-calculus truncation
  transport: `DeepTower.trunc` is data-definitional and every S2 stage field is the
  constant `stageField`, so the landed D3 law bank discharges the trunc-typed records
  verbatim) — and ★ `s2Site_gentow5w :
  GENTOW5WCleared (s2TruncThree) 2 1 85 (s2SiteMu4Calculus)`, the corrected per-level top
  law at `j = 3`, through the depth-generic mirror `gentow5w_cleared_of_B1` of
  `C132sg3.gentow5w_two_cleared` (same engine `ratio_power_law_cleared`; the B-1 supplies
  are T4's `chainNormBelow 3 85 = 2⁸Φ₂` re-proved at the trunc + D3-13's tower-free
  grade-170/degree/nonzero bank).
* **C0 (the shared export inhabitant).** ★ `s2FourWleSite` — the G3
  `WleClearedLevelExport` at the exact `X = s2FourRealizedInputOf …` and `j = 3`:
  `(e', f', u') = (2, 1, 85)`, `f_pos`, the C1 calculus/cleared law, and the own-export
  `GC13Wiring` leg (both sides of `read_norm` are the unit `1`: the wired read by the
  keystone's live pin, the FGMN read by `Rgr_ne_zero` + the card-2 collapse).  Then
  ★★ `s2Four_deepLevelExport` — the G4 record INHABITED (the keystone's constructor fired
  at `hletterZ := rfl`: both calculi carry the constant-`1` letters), the four dictionary
  projections, and ★ `s2Four_deepLevelPerWitnessExporter` — DWR §11.4's per-witness
  exporter at the witness (`DeepLive 4 j` forces `j = 3`).
* **C2 (the WLE dictionaries).** ★ `s2Four_thetaCompatibleAt` / `s2Four_peelCompatibleAt`
  / `s2Four_rangeCompleteAt` at the site (all three collapse in the card-2 terminal
  field: units read `1`, the wired read is `1` on the live range,
  `thetaRatioCleared 1 = 1`), and ★★ `s2Four_wiredGentowDemand` — the LANDED
  `DeepExport.wiredDemand_of_level_export` fired: the signed sitewise
  `IFC3.WiredGentowDemand` at the witness's own arena/use-height/read/peel-unit exports,
  at the first deep-live site.
* **C3 (canonical tau/vartheta).**  The production `CanonicalTauLetterSource` (promoted
  byte-identically from `scratch/TAU_probe.lean`, descent leg = the landed G4
  `CanonicalGeneratorDescent`), `canonical_tau_mem` (promoted), the conversion
  `varthetaRes_of_canonicalTauLetterSource` (probe proof, `tau_value` inlined), the
  witness instance `s2Four_canonicalTauLetterSource` at the canonical socket view
  (`eG := MulEquiv.refl`, `view := X.gaugeFamilyViewEq` — C130s18's socket-application
  pattern; `tau_word` holds at `m = 0, t = 0` because the witness's level-3 canonical
  read `s2CanonicalReadFour3` is CONSTANTLY `1` — every ambient letter is the unit `1`),
  and ★★★ `s2Four_varthetaRes` — **THE FIRST LIVE-INDEX `VarthetaRes` IN THE PROJECT**,
  at the witness's own exported `(N, v, ρ, q)` and `j = 3`.

## Honesty scope

* Everything at the witness inherits EXACTLY the keystone's conditionality: the four open
  threshold datums `w₁ w₂ w₃ w₄`, the parametric R8/R8r payload
  (`F₀`/monic/`μ`/degree-block/key-coprimality — NO payload instance is invented, G9's
  gate), and `IsAdicComplete`.  Nothing new is assumed.
* The `tau_word` clause is proved AT THIS WITNESS by the S2 collapse (the read is
  constantly `1`); the general triangular spanning (`LVS-TAU-WORD`) remains OPEN — the
  record keeps it as an honest field for future non-collapsed witnesses.
* `s2Site_thetaRatioCleared_one`-genre collapses are proofs about the 2-element terminal
  field; no general-depth theta/peel/range law is claimed (GCW-4/GCW-5 at general
  residue cardinality stay open consumer laws, exactly as I10DeepExport §3 records).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`CanonicalTauLetterSource` (production promotion), `s2FourWleSite`,
`s2Four_deepLevelExport`, `s2Four_wiredGentowDemand`, `s2Four_varthetaRes`.
General helpers (flagged as general lemmas): `kernelRead_snd_congr`,
`gentow5w_cleared_of_B1`, `c0_eq_one_of_ne_zero`.

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_C0123.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-! ## Part A — [C3] the production tau-source surface (scratch `TAU_probe.lean`,
promoted byte-identically; the descent leg is the landed G4 `CanonicalGeneratorDescent`) -/

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

/-- General helper (flagged): applying the second component of an equal `KernelRead` pair
to the same group element (memberships on either side) gives equal values — `subst` +
proof irrelevance. -/
theorem kernelRead_snd_congr {G : Type uG} [CommGroup G] {L : Type uL} [Field L]
    {p q : KernelRead G Lˣ} (h : p = q) {x : G}
    (hp : x ∈ MonoidHom.ker p.1) (hq' : x ∈ MonoidHom.ker q.1) :
    p.2 ⟨x, hp⟩ = q.2 ⟨x, hq'⟩ := by
  subst h
  rfl

/-- Tau membership is not new source data: at the realization's own canonical normalizer
and height it follows from the landed exact-height arena.  (Byte-identical promotion of
`TAUProbe.canonical_tau_mem`.) -/
theorem canonical_tau_mem
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) {j : ℕ} (hj : GaugeLive core.r j) (a b : ℤ) :
    (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau a b ∈
      MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
        GaugeLattice.{uG} core.r →* Multiplicative ℤ) := by
  have hexact (k : ℤ) :
      levelHeight core.T ⟨j, hj⟩
        ((Aℛ.normalizer.arenaNormSection0.transport
          (gaugeLatticeEquiv core.r).symm).n k) = Multiplicative.ofAdd k := by
    simpa [NormSection.transport, LaurentNormalizer.arenaNormSection0,
      levelHeight, levelHeight0] using
        Aℛ.normalizer.exact_height j hj.stageLive k
  rw [MonoidHom.mem_ker, NormSection.tau, map_mul, map_mul, map_inv,
    hexact, hexact, hexact, ← ofAdd_add]
  simp

/-- **[C3] The source-faithful per-level tau mechanism, production form** (byte-identical
promotion of `TAUProbe.CanonicalTauLetterSource`; the `generator_descent` leg is the
landed G4 `CanonicalGeneratorDescent`).  `tau_word` is the general-depth exponent
descent, stated at the exact external view but with the right side fixed to this
realization's existing canonical wrap and letter values; no field mentions
`HVarthetaRes`, `VarthetaRes`, or the desired embedded value of the tau word itself.
NEW STATEMENT (review). -/
structure CanonicalTauLetterSource
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ)
    (G : Type uG) [CommGroup G] (eG : G ≃* GaugeLattice.{uG} core.r)
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop where
  view : GaugeFamilyViewEq X (N.transport eG)
    (fun k ↦ (v k).comp eG.symm.toMonoidHom)
    (fun k ↦ (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q
  tau_mem : ∀ s : ℕ,
    N.tau ((s : ℤ) * q j) (q j) ∈ MonoidHom.ker (v j)
  tau_word : ∀ s : ℕ, ∃ (m : ℤ) (t : Fin (j - 1) → ℤ),
    ρ j ⟨N.tau ((s : ℤ) * q j) (q j), tau_mem s⟩ =
      Aℛ.node.wrapValue hj.stageLive ^ m *
        ∏ a, Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a ^ t a
  generator_descent : CanonicalGeneratorDescent Aℛ j hj

/-- **[C3] The vartheta consumer, production form**: the tau-letter source discharges
D62w's landed tau reduction — once tau is a word in canonical generators and each
generator descends, the whole tau word descends, and `hvarthetaRes_of_tau_letters`
closes the sitewise carrier.  (Promotion of
`TAUProbe.varthetaRes_of_canonicalTauLetterSource`, the intermediate record inlined.) -/
theorem varthetaRes_of_canonicalTauLetterSource
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ}
    {G : Type uG} [CommGroup G] {eG : G ≃* GaugeLattice.{uG} core.r}
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {j : ℕ} {hj : GaugeLive core.r j}
    (S : CanonicalTauLetterSource X G eG N v ρ q j hj) :
    Ladder.VarthetaRes G Kt L N v ρ q j := by
  refine ⟨hvarthetaRes_of_tau_letters (v j) (ρ j) (q j) S.tau_mem ?_⟩
  intro s
  obtain ⟨m, t, hword⟩ := S.tau_word s
  obtain ⟨u₀, hu₀⟩ := S.generator_descent.wrap
  choose u hu using S.generator_descent.letter
  refine ⟨u₀ ^ m * ∏ a, u a ^ t a, ?_⟩
  have hUnits :
      ρ j ⟨N.tau ((s : ℤ) * q j) (q j), S.tau_mem s⟩ =
        unitAlgebraMap (u₀ ^ m * ∏ a, u a ^ t a) := by
    rw [hword, hu₀]
    simp_rw [hu]
    rw [map_mul, map_zpow, map_prod]
    simp only [map_zpow]
  exact congrArg Units.val hUnits

end Uniformity.Density.DeepExport

/-! ## Parts B–E — the S2 witness legs -/

namespace Uniformity.Density.Tower.C136c0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Gauge
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
open Uniformity.Density.Tower.C136r4
open Uniformity.Density.DeepExport

universe uG uKt uL

/-! ### Part B.0 — the depth-generic cleared-law mirror (general; flagged)

`C132sg3.gentow5w_two_cleared` is fenced to `r = 2` only by its binder; its proof is the
depth-generic `ratio_power_law_cleared` + `Rgr_ne_zero`.  The mirror below re-runs that
proof at arbitrary depth (the unused signed-scope binders `he'`/`hcop`/`hfloor` of the
C.89 twin are dropped — this is a supply lemma, not a signed twin). -/

/-- General (flagged): the cleared top `𝒲` law from the B-1 supplies, any depth. -/
theorem gentow5w_cleared_of_B1 {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : FGMNCalculus W e' f' u') (hf' : 0 < f')
    (hprev : 2 ≤ f' → I.PrevGrade (e' * u'))
    (hnorm : ∀ d, 0 < d → d ≤ f' →
      I.ExactGrade (e' * (d * u')) (I.chainNormBelow r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow r (d * u') ≠ 0) :
    GENTOW5WCleared W e' f' u' I := by
  refine ⟨I.Rgr (e' * u') (I.chainNormBelow r u'), ?_, fun t ht => ?_⟩
  · have h := I.Rgr_ne_zero (e' * (1 * u')) (I.chainNormBelow r (1 * u'))
      (hnorm 1 one_pos hf') (hnormdeg 1 one_pos hf') (hnormz 1 one_pos hf')
    simpa using h
  · exact C132sg3.ratio_power_law_cleared W e' f' u' I hf' hprev hnorm hnormdeg hnormz ht

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ### Part B.1 — the truncated tower and the trunc-typed μ₄ records (row C1's carrier)

`DeepTower.trunc` is data-definitional (every data field re-scoped, values unchanged), so
`s2TruncThree` carries `s2DepthFour`'s own `e/f/u/fld/ψ` — in particular `u 4 = 85`, the
junk-index divergence from `s2DepthThree` that makes this a genuinely different tower
term (R5's recorded transport handoff).  Every stage field is the constant `stageField`,
so the landed μ₄ operator bank serves the trunc typing verbatim. -/

/-- **the site tower**: the depth-four occurrence truncated to the deep-live depth 3. -/
noncomputable def s2TruncThree : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 3 :=
  (s2DepthFour h2 hq).trunc 3 (by omega)

/-- pin: the trunc's data is the depth-four data (representative reads, all `rfl`). -/
theorem s2TruncThree_data :
    (s2TruncThree h2 hq).u 3 = 21 ∧ (s2TruncThree h2 hq).u 4 = 85 ∧
      (s2TruncThree h2 hq).e 3 = 2 ∧ (s2TruncThree h2 hq).f 3 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- the trunc's stage fields have exactly two elements (the constant residue tower). -/
theorem s2TruncFld_card (i : ℕ) : Nat.card ((s2TruncThree h2 hq).fld i) = 2 :=
  C80.card_K₁ h2 hq

/-- local copy of R1/R67's private card-2 collapse (flagged, general): every nonzero
element of a 2-element field is `1`. -/
theorem c0_eq_one_of_ne_zero {F : Type} [Field F] (hcard : Nat.card F = 2)
    {c : F} (hc : c ≠ 0) : c = 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : Fˣ) : F) := (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- **the site `KeyChain`**: the T2 chain `Φ′/Φ₂/g₈`, re-scoped to the trunc (the chain
function is `(s2DepthThreeKeyChain).keyAt` VERBATIM, so every landed law's key mention
matches by projection; the degree law re-proves against the trunc's own `Dcum`, which is
the depth-four `Dcum` definitionally). -/
noncomputable def s2SiteKeyChain : KeyChain (s2TruncThree h2 hq) where
  keyAt := (s2DepthThreeKeyChain h2 hq).keyAt
  keyAt_one := (s2DepthThreeKeyChain h2 hq).keyAt_one
  keyAt_monic := fun i hi => (s2DepthThreeKeyChain h2 hq).keyAt_monic i hi
  keyAt_degree := by
    intro i hi
    obtain ⟨hi1, hi3⟩ := hi
    have htr : ∀ k, (s2TruncThree h2 hq).Dcum k = (s2DepthFour h2 hq).Dcum k :=
      fun k => rfl
    interval_cases i
    · rw [htr, s2DepthFour_Dcum_one h2 hq]
      exact s2DepthThreeKeyAt_natDegree_one h2 hq
    · rw [htr, s2DepthFour_Dcum_two h2 hq]
      exact s2DepthThreeKeyAt_natDegree_two h2 hq
    · rw [htr, s2DepthFour_Dcum_three h2 hq]
      exact s2DepthThreeKeyAt_natDegree_three h2 hq

/-- **the trunc-typed letter field**: the forced constant `1` (the unique nonzero value
of the 2-element stage field), at the trunc typing. -/
noncomputable def s2SiteLetter : ℕ → (s2TruncThree h2 hq).fld 3 := fun _ => 1

/-- **[C1] the trunc-typed DATA record**: the SAME seven landed μ₄ operators as D3-18's
`s2SourceDataThree`, at the truncated tower (the operator fields are tower-free or land
in the shared constant stage field). -/
noncomputable def s2SiteSourceData :
    FGMNSourceData (s2TruncThree h2 hq) (s2SiteKeyChain h2 hq) 2 1 85 where
  nextValue := s2Hgt₄ h2 hq
  gradedResidual := s2Mu4GradedRes h2 hq
  normalizedResidual := s2Mu4NormRes h2 hq
  PrevGrade := S2Mu4PrevGrade
  keyPolynomial := S2Mu4KeyPoly h2 hq
  initialEquiv := S2Mu4InitialEquiv h2 hq
  letter := s2SiteLetter h2 hq

/-- **[C1] the trunc-typed LAWS record** — the D3-14..18 bank discharges every projection
verbatim (byte-parallel to `C136d3.s2SourceLawsThree`; the key mentions match through the
chain-function reuse). -/
theorem s2SiteSourceLaws :
    FGMNSourceLaws (s2TruncThree h2 hq) (s2SiteKeyChain h2 hq) 2 1 85
      (s2SiteSourceData h2 hq) where
  graded_zero_of_above := fun _ _ h => s2Mu4GradedRes_zero_of_above h2 hq h
  graded_add := fun _ _ _ hg hh hgh => s2Mu4GradedRes_add h2 hq hg hh hgh
  graded_mul := s2Mu4_graded_mul h2 hq
  graded_scalar_nonzero := s2Mu4_graded_scalar_nonzero h2 hq
  normalized_mul := fun g h => s2Mu4NormRes_mul h2 hq g h
  normalized_recipe := fun khat hgr hdeg => s2Mu4_normalized_recipe h2 hq khat hgr hdeg
  normalized_exists := fun _ ψ hm hirr hd hc => s2Mu4_hex h2 hq ψ hm hirr hd hc
  key_criterion := s2Mu4_key_criterion h2 hq
  key_irreducible := fun _ hkp _ => s2Mu4_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => s2Mu4KeyPoly_g8 h2 hq
  carried_key_residual := fun _ => s2Mu4NormRes_g8 h2 hq
  initial_iff_residual := fun g h hg hh => s2Mu4_initial_iff_residual h2 hq g h hg hh
  letter_ne_zero := fun i h1 hr => one_ne_zero

/-- ★ **[C1] THE SITE CALCULUS** — the `(2, 1, 85)` μ₄ calculus at the truncated
depth-four tower, through the CC-16 packaging map (D3-19's construction, one transport
over). -/
@[implicit_reducible] noncomputable def s2SiteMu4Calculus :
    FGMNCalculus (s2TruncThree h2 hq) 2 1 85 :=
  fgmnCalculusOf (s2SiteKeyChain h2 hq) (s2SiteSourceData h2 hq) (s2SiteSourceLaws h2 hq)

/-- packaging tooth: the trunc-typed calculus is literally nonempty (campaign exit gate 4
uses only `fgmn_model_calculus_nonempty` after the records). -/
theorem s2Site_calculus_nonempty :
    Nonempty (FGMNCalculus (s2TruncThree h2 hq) 2 1 85) :=
  fgmn_model_calculus_nonempty (s2SiteKeyChain h2 hq) (s2SiteSourceData h2 hq)
    (s2SiteSourceLaws h2 hq)

/-- read pin: the site calculus's keys are the T2 chain function, definitionally. -/
theorem s2SiteMu4Calculus_keyAt :
    (s2SiteMu4Calculus h2 hq).keyAt = (s2DepthThreeKeyChain h2 hq).keyAt := rfl

/-- read pin: the site calculus's letters are the forced constant-`1` letters,
definitionally. -/
theorem s2SiteMu4Calculus_letterZ :
    (s2SiteMu4Calculus h2 hq).letterZ = s2SiteLetter h2 hq := rfl

/-- read pin: the site calculus's exact-grade predicate is the landed μ₄ predicate,
definitionally. -/
theorem s2SiteMu4Calculus_ExactGrade :
    (s2SiteMu4Calculus h2 hq).ExactGrade = S2Mu4ExactGrade h2 hq := rfl

/-! ### Part B.2 — T4's normalizer formula at the trunc, and the B-1 supplies (row C1) -/

/-- **T4's exponent pin at the trunc**: `towerNorm 2 85 = (8, 0, ![0, 1])` — the same rung
solves as `C136t.s2DepthThree_towerNorm_two_eighty_five` (`towerNorm 2` reads only the
`u/e` data at rungs `≤ 3`, where the trunc carries the identical values). -/
theorem s2Trunc_towerNorm_two_eighty_five :
    (s2TruncThree h2 hq).towerNorm 2 85 = (8, 0, ![0, 1]) := by
  have hu3 : (s2TruncThree h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2TruncThree h2 hq).e (1 + 2) = 2 := rfl
  have hu2 : (s2TruncThree h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2TruncThree h2 hq).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  have hb2 : towerSolve 21 2 85 = 1 := rfl
  have hb1 : towerSolve 5 2 32 = 0 := rfl
  have hsl : (s2Frame h2 hq).slotIdx 16 = 0 := by
    change ((List.range 2).find? (fun i => (i * 1) % 2 == 16 % 2)).getD 0 = 0
    rfl
  simp only [DeepTower.towerNorm, hu3, he3, hu2, he2, hh, he1, hb2, hb1]
  norm_num [hsl, Prod.ext_iff]
  funext j
  fin_cases j <;> rfl

/-- **T4's normalizer polynomial at the trunc**: `chainNormBelow 3 85 = 2⁸ · Φ₂` for any
trunc-typed calculus carrying the T2 chain. -/
theorem s2Site_chainNormBelow_three_eighty_five
    (I : FGMNCalculus (s2TruncThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    I.chainNormBelow 3 85 =
      Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2 := by
  rw [FGMNCalculus.chainNormBelow, FGMNCalculus.chainNorm,
    s2Trunc_towerNorm_two_eighty_five h2 hq, hkey]
  simp [Fin.prod_univ_two]

/-- the trunc-typed grade-170 fact (D3-13's tooth at the trunc formula). -/
theorem s2Site_chainNormBelow_exactGrade
    (I : FGMNCalculus (s2TruncThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    S2Mu4ExactGrade h2 hq 170 (I.chainNormBelow 3 85) := by
  rw [s2Site_chainNormBelow_three_eighty_five h2 hq I hkey]
  exact s2Mu4_chainNormBelow_tooth_exactGrade h2 hq

/-- **[C1] B-1 exact-grade supply at the site calculus** (grades `2·(d·85)`, `d ∈ {1}`). -/
theorem s2Site_B1_exact_grade_supply :
    ∀ d, 0 < d → d ≤ 1 →
      (s2SiteMu4Calculus h2 hq).ExactGrade (2 * (d * 85))
        ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 (d * 85)) := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  show S2Mu4ExactGrade h2 hq (2 * (1 * 85))
    ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 (1 * 85))
  rw [show (1 : ℕ) * 85 = 85 from one_mul 85,
    show (2 : ℕ) * (1 * 85) = 170 from by norm_num]
  exact s2Site_chainNormBelow_exactGrade h2 hq (s2SiteMu4Calculus h2 hq) rfl

/-- **[C1] B-1 degree supply at the site calculus** (`4 < 8`). -/
theorem s2Site_B1_degree_supply :
    ∀ d, 0 < d → d ≤ 1 →
      ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 (d * 85)).natDegree
        < ((s2SiteMu4Calculus h2 hq).keyAt 3).natDegree := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  rw [one_mul, s2Site_chainNormBelow_three_eighty_five h2 hq (s2SiteMu4Calculus h2 hq) rfl,
    s2SiteMu4Calculus_keyAt h2 hq]
  exact s2Mu4_chainNormBelow_tooth_degree_lt_key h2 hq

/-- **[C1] B-1 nonvanishing supply at the site calculus**. -/
theorem s2Site_B1_nonzero_supply :
    ∀ d, 0 < d → d ≤ 1 →
      (s2SiteMu4Calculus h2 hq).chainNormBelow 3 (d * 85) ≠ 0 := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  rw [one_mul, s2Site_chainNormBelow_three_eighty_five h2 hq (s2SiteMu4Calculus h2 hq) rfl]
  exact s2Mu4_chainNormBelow_tooth_ne_zero h2 hq

/-- ★★ **[C1] THE CORRECTED PER-LEVEL TOP `GENTOW5WCleared` LAW AT `j = 3`** — the
single-`w` law at the site calculus, every leg discharged (the `hprev` fence is vacuous
at `f' = 1`). -/
theorem s2Site_gentow5w :
    GENTOW5WCleared (s2TruncThree h2 hq) 2 1 85 (s2SiteMu4Calculus h2 hq) :=
  gentow5w_cleared_of_B1 (s2TruncThree h2 hq) 2 1 85 (s2SiteMu4Calculus h2 hq)
    one_pos
    (fun hcon => absurd hcon (by norm_num))
    (s2Site_B1_exact_grade_supply h2 hq)
    (s2Site_B1_degree_supply h2 hq)
    (s2Site_B1_nonzero_supply h2 hq)

/-! ### Part B.3 — the card-2 value collapses (the C0/C2 read identities) -/

/-- the FGMN read at the cleared grade is the unit `1` (nonzero by `Rgr_ne_zero` at the
B-1 supplies; `1` by the card-2 collapse). -/
theorem s2Site_Rgr_eq_one :
    (s2SiteMu4Calculus h2 hq).Rgr (2 * (1 * 85))
      ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 (1 * 85)) = 1 :=
  c0_eq_one_of_ne_zero (s2TruncFld_card h2 hq 3)
    ((s2SiteMu4Calculus h2 hq).Rgr_ne_zero _ _
      (s2Site_B1_exact_grade_supply h2 hq 1 one_pos le_rfl)
      (s2Site_B1_degree_supply h2 hq 1 one_pos le_rfl)
      (s2Site_B1_nonzero_supply h2 hq 1 one_pos le_rfl))

/-- the cleared ϑ-carrier at the site is the unit `1` (`a · a⁻¹` at the nonzero read). -/
theorem s2Site_thetaRatioCleared_one :
    (s2SiteMu4Calculus h2 hq).thetaRatioCleared 1 = 1 := by
  unfold FGMNCalculus.thetaRatioCleared
  rw [pow_one]
  have h := s2Site_Rgr_eq_one h2 hq
  rw [one_mul] at h
  rw [show (1 : ℕ) * 85 = 85 from one_mul 85, h]
  norm_num

end S2

/-! ### Parts C/D/E — the witness legs (rows C0, C2, C3) -/

section Witness

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

/-! #### C.i — the wired export computes at the witness (IFC4's §2, one tower deeper) -/

/-- ★ the exported tower read of the realized witness is `1` on the gauge-live range
(the keystone's wired-at-construction value, through the CC-12 export). -/
theorem s2Four_towerReadFamily_live {j : ℕ} (hj : GaugeLive 4 j)
    (g : GaugeLattice.{uG} 4) :
    towerReadFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) j g = 1 := by
  show (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).towerReadFamily0 j (gaugeLatticeEquiv 4 g) = 1
  rw [SplitNodePointSource.towerReadFamily0_live _ hj]
  rfl

/-- disclosure (no swallowing): off the gauge-live range the export is the CC-11 junk
`0`, not the wired value. -/
theorem s2Four_towerReadFamily_junk {j : ℕ} (hj : ¬ GaugeLive 4 j)
    (g : GaugeLattice.{uG} 4) :
    towerReadFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) j g = 0 := by
  show (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).towerReadFamily0 j (gaugeLatticeEquiv 4 g) = 0
  exact SplitNodePointSource.towerReadFamily0_junk _ hj _

/-- projection-reduction pin: the witness core's depth exceeds `1` (the `hr` datum the
theta/range dictionaries and the arena family consume; `norm_num` cannot see through the
structure projection, so the reduction is packaged once here). -/
theorem s2FourCore_one_lt_r :
    1 < (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).r := by
  show (1 : ℕ) < 4
  norm_num

/-! #### C.ii — the GC-13 wiring leg at the witness's own exported read -/

/-- ★ **the signed GC-13 law at the witness's own exported read and the site calculus**,
universal in the norm section, height, and receiver (both sides are the unit `1`: the
wired read by construction, the FGMN read by `s2Site_Rgr_eq_one`). -/
theorem s2Four_gc13Wiring {j : ℕ} (hj : GaugeLive 4 j)
    (N : NormSection (GaugeLattice.{uG} 4)) (q : ℤ)
    (φ : (s2TruncThree h2 hq).fld 3 →+* (s2DepthFour h2 hq).fld 4) :
    IFC3.GC13Wiring N q
      (towerReadFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) j)
      (s2SiteMu4Calculus h2 hq) φ :=
  ⟨fun s hs1 hsf => by
    have hs : s = 1 := by omega
    subst hs
    rw [s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj,
      s2Site_Rgr_eq_one h2 hq, map_one]⟩

/-! #### C.iii — ★★ row C0: the G3 site package at the witness, `j = 3` -/

/-- ★★ **[C0] THE G3 SITE PACKAGE AT THE WITNESS** — the `WleClearedLevelExport` at the
exact realized input and the unique deep-live level `j = 3`: one `(e', f', u') =
(2, 1, 85)` (the μ₄ triple), positive `f' = 1`, the C1 site calculus and cleared law, and
the own-export GC-13 wiring leg.  NEW STATEMENT (review). -/
noncomputable def s2FourWleSite (hj : DeepLive 4 3) :
    WleClearedLevelExport.{0, 0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      3 hj.2.le where
  e' := 2
  f' := 1
  u' := 85
  f_pos := one_pos
  calculus := s2SiteMu4Calculus h2 hq
  cleared := s2Site_gentow5w h2 hq
  wiring := s2Four_gc13Wiring h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
    hj.gaugeLive _ _ _

/-- pins: the site's triple, calculus, and cleared law are the C1 data, definitionally. -/
theorem s2FourWleSite_pins (hj : DeepLive 4 3) :
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).e' = 2 ∧
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).f' = 1 ∧
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).u' = 85 ∧
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).calculus
      = s2SiteMu4Calculus h2 hq :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! #### C.iv — ★★★ row C0's exit: the shared G4 record INHABITED -/

/-- ★★★ **[C0] THE SHARED `DeepLevelExport` INHABITED AT THE WITNESS** — the keystone's
`s2Four_deepLevelExport_of_site` fired at the C0 site; the letter tie `hletterZ` is
definitional (both the site calculus and the μ₄ calculus carry the forced constant-`1`
letters).  Conditionality: exactly the keystone's (thresholds + parametric payload +
`IsAdicComplete`).  NEW STATEMENT (review). -/
noncomputable def s2Four_deepLevelExport (hj : DeepLive 4 3) :
    DeepLevelExport.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj :=
  s2Four_deepLevelExport_of_site h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)
    (fun _ => rfl)

/-- ★ the literal nonvacuity tooth: the shared record's type is INHABITED at the witness
and `j = 3`. -/
theorem s2Four_deepLevelExport_nonempty (hj : DeepLive 4 3) :
    Nonempty (DeepLevelExport.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj) :=
  ⟨s2Four_deepLevelExport h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj⟩

/-- the four dictionary projections at the inhabitant (C0's "project the dictionaries"):
the WLE site, the TAU descent, the top cleared law, and the wiring leg all fire. -/
example (hj : DeepLive 4 3) :
    CanonicalGeneratorDescent
      (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) 3 hj.gaugeLive :=
  (s2Four_deepLevelExport h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).tauDictionary

example (hj : DeepLive 4 3) :
    WleClearedLevelExport.{0, 0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      3 hj.2.le :=
  (s2Four_deepLevelExport h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).wleExport

/-- ★ **[C0/DWR §11.4] the per-witness deep-level exporter at the witness**: every
deep-live level of the depth-four witness exports the shared record (`DeepLive 4 j`
forces `j = 3`). -/
theorem s2Four_deepLevelPerWitnessExporter :
    DeepLevelPerWitnessExporter.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) := by
  intro j hj
  have hj' : 3 ≤ j ∧ j < 4 := hj
  have hj3 : j = 3 := by omega
  subst hj3
  exact ⟨s2Four_deepLevelExport h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj⟩

/-- corollary (the G3 projection): the WLE per-level exporter at the witness. -/
theorem s2Four_wleClearedPerLevelExporter :
    WleClearedPerLevelExporter.{0, 0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  wleClearedPerLevelExporter_of_deep
    (s2Four_deepLevelPerWitnessExporter h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)

/-! #### D — row C2: the three consumer dictionaries at the site, and the wired demand -/

/-- ★ **[C2] the theta dictionary at the site** (GCW-4 at the witness): both factors are
the unit `1` in the card-2 terminal field. -/
theorem s2Four_thetaCompatibleAt (hj : DeepLive 4 3) :
    ThetaCompatibleAt
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj) := by
  intro s hs1 hsf
  have hf : (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).f' = 1 :=
    rfl
  rw [hf] at hsf
  have hs : s = 1 := by omega
  subst hs
  have hmap : (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).receiver.levelHom 3
      ((s2SiteMu4Calculus h2 hq).thetaRatioCleared 1) = 1 := by
    rw [s2Site_thetaRatioCleared_one h2 hq]
    exact map_one _
  exact c0_eq_one_of_ne_zero (s2R7Fld_card h2 hq 4)
    (mul_ne_zero (Units.ne_zero _) (fun hzero => one_ne_zero (hmap.symm.trans hzero)))

/-- ★ **[C2] the peel dictionary at the site** (the single-`w` tie): the cleared witness
`wC = 1` is the witness's own exported peel unit (both are the unit `1`). -/
theorem s2Four_peelCompatibleAt (hj : DeepLive 4 3) :
    PeelCompatibleAt
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj) := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · intro t ht
    have hf : (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).f' = 1 :=
      rfl
    rw [hf] at ht
    have ht0 : t = 0 := by omega
    subst ht0
    show (s2SiteMu4Calculus h2 hq).Rgr (2 * ((1 - 0) * 85))
        ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 ((1 - 0) * 85))
        * (s2SiteMu4Calculus h2 hq).thetaRatioCleared (1 - 0) = 1 ^ (1 - 0)
    show (s2SiteMu4Calculus h2 hq).Rgr (2 * (1 * 85))
        ((s2SiteMu4Calculus h2 hq).chainNormBelow 3 (1 * 85))
        * (s2SiteMu4Calculus h2 hq).thetaRatioCleared 1 = 1 ^ 1
    rw [s2Site_Rgr_eq_one h2 hq, s2Site_thetaRatioCleared_one h2 hq, one_mul]
    exact (one_pow 1).symm
  · exact (congrArg Units.val (s2FourUnit_eq_one h2 hq
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily 3))).trans
      (map_one _).symm

/-- ★ **[C2] the range dictionary at the site** (GCW-5 at the witness): D.44's `s = 0`
clause and the `s > f' = 1` tail, both by the card-2 collapses. -/
theorem s2Four_rangeCompleteAt (hj : DeepLive 4 3) :
    RangeCompleteAt
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj) := by
  constructor
  · refine (s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive _).trans (Eq.symm ?_)
    exact c0_eq_one_of_ne_zero (s2R7Fld_card h2 hq 4) (Units.ne_zero _)
  · intro s hs
    refine (s2Four_towerReadFamily_live h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
      hj.gaugeLive _).trans (Eq.symm ?_)
    exact c0_eq_one_of_ne_zero (s2R7Fld_card h2 hq 4)
      (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)))

/-- ★★ **[C2] THE SIGNED SITEWISE `WiredGentowDemand` AT THE WITNESS'S OWN EXPORTS AND
THE FIRST DEEP-LIVE SITE** — the landed `wiredDemand_of_level_export` fired at the C0
site with the three dictionaries.  NEW STATEMENT (review). -/
theorem s2Four_wiredGentowDemand (hj : DeepLive 4 3) :
    IFC3.WiredGentowDemand
      (arenaFamily.{0, 0, 0, uL}
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
        (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop) 3)
      (useHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3)
      (towerReadFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3)
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily 3)
      (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj).calculus
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).receiver.levelHom 3) :=
  wiredDemand_of_level_export hj
    (s2FourWleSite h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)
    (s2Four_thetaCompatibleAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)
    (s2Four_peelCompatibleAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)
    (s2Four_rangeCompleteAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)

/-! #### E — row C3: the canonical tau source and the first live-index vartheta -/

omit [Algebra ((s2DepthFour h2 hq).fld 4) L] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- the witness's level-3 canonical read is CONSTANTLY the unit `1` — every ambient
letter is the unit `1` (the S2 collapse that makes the witness's `tau_word` clause
provable with `m = 0, t = 0`; the general triangular spanning stays open). -/
theorem s2CanonicalReadFour3_eq_one
    (g : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) 3)) :
    s2CanonicalReadFour3 h2 hq L g = 1 := by
  rw [s2CanonicalReadFour3_coe]
  simp [s2AmbientLetterFour]

/-- the canonical residue export of the witness at `j = 3` is constantly `1`. -/
theorem s2Four_canonicalResAt_eq_one (hj : GaugeLive 4 3)
    (σ : MonoidHom.ker (levelHeight (s2DepthFour h2 hq) ⟨3, hj⟩ :
      GaugeLattice.{uG} 4 →* Multiplicative ℤ)) :
    canonicalResAt
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj σ = 1 := by
  show s2CanonicalReadFour h2 hq L 3
    (kerLevelProj0 (s2DepthFour h2 hq) ⟨3, hj⟩
      (kerGaugeEquiv (s2DepthFour h2 hq) ⟨3, hj⟩ σ)) = 1
  rw [s2CanonicalReadFour_three]
  exact s2CanonicalReadFour3_eq_one h2 hq L _

/-- the canonical residue FAMILY at `j = 3` is constantly `1` (the family value is the
`canonicalResAt` read, through the CC-12 view's `KernelRead` equality). -/
theorem s2Four_canonicalResFamily_eq_one (hj : GaugeLive 4 3) {x : GaugeLattice.{uG} 4}
    (hx : x ∈ MonoidHom.ker (gaugeHeightFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3))
    (hx' : x ∈ MonoidHom.ker (levelHeight (s2DepthFour h2 hq) ⟨3, hj⟩ :
      GaugeLattice.{uG} 4 →* Multiplicative ℤ)) :
    canonicalResFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3
      ⟨x, hx⟩ = 1 :=
  (kernelRead_snd_congr
    (((s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
      F₀ hF₀ μ hμ hdeg hblock hcop).gaugeFamilyViewEq.2 3 hj).1) hx hx').trans
    (s2Four_canonicalResAt_eq_one h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj
      ⟨x, hx'⟩)

/-- tau membership at the witness's canonical height family. -/
theorem s2Four_tau_mem (hj : GaugeLive 4 3) (a b : ℤ) :
    (((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
      (gaugeLatticeEquiv 4).symm).tau a b : GaugeLattice.{uG} 4) ∈
      MonoidHom.ker (gaugeHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3) := by
  have hker : gaugeHeightFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3
      = (levelHeight (s2DepthFour h2 hq) ⟨3, hj⟩ :
          GaugeLattice.{uG} 4 →* Multiplicative ℤ) := by
    have hlive : GaugeLive
        (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop).r 3 := hj
    simp only [gaugeHeightFamily]
    rw [dif_pos hlive]
    rfl
  show gaugeHeightFamily
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3
      (((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm).tau a b) = 1
  rw [hker]
  exact canonical_tau_mem.{uG, 0, uL}
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj a b

/-- ★★ **[C3] THE CANONICAL TAU-LETTER SOURCE AT THE WITNESS** — the exact `X`, the
canonical socket view (`eG := MulEquiv.refl`, view = `X.gaugeFamilyViewEq`), and
`j = 3`: `tau_word` holds with `m = 0, t = 0` (the level-3 canonical read is constantly
`1`), and the descent leg is the keystone's `s2Four_canonicalGeneratorDescent`.
NEW STATEMENT (review). -/
theorem s2Four_canonicalTauLetterSource (hj : GaugeLive 4 3) :
    CanonicalTauLetterSource
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      (GaugeLattice.{uG} 4) (MulEquiv.refl _)
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      3 hj where
  view := (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
    F₀ hF₀ μ hμ hdeg hblock hcop).gaugeFamilyViewEq
  tau_mem := fun s => s2Four_tau_mem h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj
    _ _
  tau_word := fun s => ⟨0, 0, by
    refine Eq.trans (s2Four_canonicalResFamily_eq_one h2 hq L w₁ w₂ w₃ w₄
      F₀ hF₀ μ hμ hdeg hblock hcop hj
      (s2Four_tau_mem h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj _ _)
      (canonical_tau_mem
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj _ _))
      ?_
    simp⟩
  generator_descent := s2Four_canonicalGeneratorDescent h2 hq L w₁ w₂ w₃ w₄
    F₀ hF₀ μ hμ hdeg hblock hcop hj

/-- ★★★ **[C3] THE FIRST LIVE-INDEX `VarthetaRes` IN THE PROJECT** — the sitewise
Display-A carrier at the witness's own exported `(N, v, ρ, q)` and the deep-live level
`j = 3`, through D62w's landed tau reduction.  Conditionality: exactly the keystone's.
NEW STATEMENT (review). -/
theorem s2Four_varthetaRes (hj : GaugeLive 4 3) :
    Ladder.VarthetaRes (GaugeLattice.{uG} 4) ((s2DepthFour h2 hq).fld 4) L
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily
        (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)) 3 :=
  varthetaRes_of_canonicalTauLetterSource
    (s2Four_canonicalTauLetterSource h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop hj)

end Witness

end Uniformity.Density.Tower.C136c0

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.kernelRead_snd_congr
#print axioms Uniformity.Density.DeepExport.canonical_tau_mem
#print axioms Uniformity.Density.DeepExport.CanonicalTauLetterSource
#print axioms Uniformity.Density.DeepExport.varthetaRes_of_canonicalTauLetterSource
#print axioms Uniformity.Density.Tower.C136c0.gentow5w_cleared_of_B1
#print axioms Uniformity.Density.Tower.C136c0.s2TruncThree
#print axioms Uniformity.Density.Tower.C136c0.s2TruncThree_data
#print axioms Uniformity.Density.Tower.C136c0.s2TruncFld_card
#print axioms Uniformity.Density.Tower.C136c0.c0_eq_one_of_ne_zero
#print axioms Uniformity.Density.Tower.C136c0.s2SiteKeyChain
#print axioms Uniformity.Density.Tower.C136c0.s2SiteLetter
#print axioms Uniformity.Density.Tower.C136c0.s2SiteSourceData
#print axioms Uniformity.Density.Tower.C136c0.s2SiteSourceLaws
#print axioms Uniformity.Density.Tower.C136c0.s2SiteMu4Calculus
#print axioms Uniformity.Density.Tower.C136c0.s2Site_calculus_nonempty
#print axioms Uniformity.Density.Tower.C136c0.s2SiteMu4Calculus_keyAt
#print axioms Uniformity.Density.Tower.C136c0.s2SiteMu4Calculus_letterZ
#print axioms Uniformity.Density.Tower.C136c0.s2SiteMu4Calculus_ExactGrade
#print axioms Uniformity.Density.Tower.C136c0.s2Trunc_towerNorm_two_eighty_five
#print axioms Uniformity.Density.Tower.C136c0.s2Site_chainNormBelow_three_eighty_five
#print axioms Uniformity.Density.Tower.C136c0.s2Site_chainNormBelow_exactGrade
#print axioms Uniformity.Density.Tower.C136c0.s2Site_B1_exact_grade_supply
#print axioms Uniformity.Density.Tower.C136c0.s2Site_B1_degree_supply
#print axioms Uniformity.Density.Tower.C136c0.s2Site_B1_nonzero_supply
#print axioms Uniformity.Density.Tower.C136c0.s2Site_gentow5w
#print axioms Uniformity.Density.Tower.C136c0.s2Site_Rgr_eq_one
#print axioms Uniformity.Density.Tower.C136c0.s2Site_thetaRatioCleared_one
#print axioms Uniformity.Density.Tower.C136c0.s2Four_towerReadFamily_live
#print axioms Uniformity.Density.Tower.C136c0.s2Four_towerReadFamily_junk
#print axioms Uniformity.Density.Tower.C136c0.s2Four_gc13Wiring
#print axioms Uniformity.Density.Tower.C136c0.s2FourWleSite
#print axioms Uniformity.Density.Tower.C136c0.s2FourWleSite_pins
#print axioms Uniformity.Density.Tower.C136c0.s2Four_deepLevelExport
#print axioms Uniformity.Density.Tower.C136c0.s2Four_deepLevelExport_nonempty
#print axioms Uniformity.Density.Tower.C136c0.s2Four_deepLevelPerWitnessExporter
#print axioms Uniformity.Density.Tower.C136c0.s2Four_wleClearedPerLevelExporter
#print axioms Uniformity.Density.Tower.C136c0.s2Four_thetaCompatibleAt
#print axioms Uniformity.Density.Tower.C136c0.s2Four_peelCompatibleAt
#print axioms Uniformity.Density.Tower.C136c0.s2Four_rangeCompleteAt
#print axioms Uniformity.Density.Tower.C136c0.s2Four_wiredGentowDemand
#print axioms Uniformity.Density.Tower.C136c0.s2CanonicalReadFour3_eq_one
#print axioms Uniformity.Density.Tower.C136c0.s2Four_canonicalResAt_eq_one
#print axioms Uniformity.Density.Tower.C136c0.s2Four_canonicalResFamily_eq_one
#print axioms Uniformity.Density.Tower.C136c0.s2Four_tau_mem
#print axioms Uniformity.Density.Tower.C136c0.s2Four_canonicalTauLetterSource
#print axioms Uniformity.Density.Tower.C136c0.s2Four_varthetaRes

end AxCheck
