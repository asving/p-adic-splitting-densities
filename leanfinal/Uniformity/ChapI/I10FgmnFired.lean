/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10FgmnCite
import Uniformity.ChapI.IFCG51
import Uniformity.ChapI.IFCG55
import Uniformity.ChapI.IFCG72
import Uniformity.ChapI.IFCG74

/-!
# Uniformity.ChapI.I10FgmnFired — the census consumers FIRED by the signed FGMN cite

Unit SIGN's consumer walk: with `fgmn_cite_packageF` declared (`I10FgmnCite.lean`,
owner-signed 2026-08-31), every census row and master conditional on
`FactorCorrespondenceAt` fires through
`I10CitePkgF.factorCorrespondence_cite : ∀ D, 2 ≤ D → FactorCorrespondenceAt D`.
This file lands the unconditional forms at the capstone-level surfaces:

* **§1 MASS 4 CLOSES, ALL TYPES** — ★★★ `coneRemainderLaw_four_all σ` outright
  (IFCG55's all-types row at `FactorCorrespondenceAt 2`; the sole remaining mass-4
  gate, `ZcURLim (e1DdDecFam σ)`, closes with it, as does `PowerFullSpanLaw 4 σ`).
  This also discharges every `hR4` binder in the clusterGeom lineage
  (IFCG59/60/66/69/71/72/73/74's `decidedSliceAt_all_of_visCensus*` fronts).
* **§2 THE STEEP-CENSUS MASTER, POST-SIGNATURE** — IFCG72's
  `decidedSliceAt_all_of_MASTER_CENSUS` / `capstoneHypotheses_of_MASTER_CENSUS` with
  the `hFC` premise GONE; the census master now rests on exactly
  {`hEis` (EisFullSpan remainder at composite ramified masses),
  `hSD`/`hPD` (the two convolution-defect rows), `hCensus` (the r ≥ 2
  `SteepDecCensusLaw` at non-special frames)}.
* **§3 THE CLUSTERGEOM MASTER, POST-SIGNATURE** — IFCG74's weight-trimmed masters with
  `hR4` (slice) / `hFC` (capstone) GONE; resting on
  {`hCG` (weight-matched `VisEntryClusterGeom` — unit TSV in flight), `hCL`/`hPCL`
  (collision laws), `hPF` (power full-span), `hLeafSub` (leaf subface), and for the
  capstone `hEis`}.

NOT fired (a DIFFERENT carrier, not covered by the signed package — IFCG75's own
docstring: leg E is exactly the `h = 1` instance): the slope-Bézout sites
`IFCG75.slopeBezoutCellTypeScalingAt_of_correspondence` /
`bez_transport_decidedAt_iff_of_correspondence` on
`SlopeBezoutFactorCorrespondenceAt h k` — the slope-`h ≥ 2` deep-primary step stays
conditional (carrier gap before cite gap, as recorded in I10CitePkgF's honest scope).

Every theorem here inherits Lean core + `fgmn_cite_packageF` + whatever the consumed
census spine already carried (the owner-signed `exists_slope_factorization` on the
slice masters; + `agnprw_termination` on the capstone masters) — see the AxCheck
footer's expectations.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.I10FgmnFired

open Uniformity.Density.I10CitePkgF (factorCorrespondence_cite)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ConeRemainderLaw)
open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG41 (CollisionLaw)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisGenre powerCollisionTotal)
open Uniformity.Density.IFCG66 (subFrames)
open Uniformity.Density.IFCG71 (VisEntryClusterGeom)
open Uniformity.Density.IFCG72 (SteepDecCensusLaw)

/-! ## §1 — MASS 4 CLOSES, ALL TYPES -/

/-- ★★★ **MASS 4 CLOSES — every type, unconditional**: the degree-4 cone-remainder
law at ALL 11 quartic types, from the signed cite's `D = 2` correspondence alone
(IFCG55's all-types row; the leaf premise was already discharged by IFCG37). -/
theorem coneRemainderLaw_four_all (σ : FactorizationType) : ConeRemainderLaw 4 σ :=
  Uniformity.Density.IFCG55.coneRemainderLaw_four_all
    (factorCorrespondence_cite 2 le_rfl) σ

/-- The last conditional mass-4 sector limit, unconditional: the E1 double-decker
decided family has a uniform rational limit at EVERY type (ASM's row, fired). -/
theorem zcURLim_e1DdDecFam_all (σ : FactorizationType) :
    ZcURLim (Uniformity.Density.IFCG34.e1DdDecFam σ) :=
  Uniformity.Density.IFCG51.zcURLim_e1DdDecFam
    (factorCorrespondence_cite 2 le_rfl) σ

/-- The mass-4 power full-span law, unconditional at every type (ASM's row, fired). -/
theorem powerFullSpanLaw_four_all (σ : FactorizationType) : PowerFullSpanLaw 4 σ :=
  Uniformity.Density.IFCG51.powerFullSpanLaw_four
    (factorCorrespondence_cite 2 le_rfl) σ

/-! ## §2 — THE STEEP-CENSUS MASTER, POST-SIGNATURE (IFCG72 lineage)

Binders byte-identical to `IFCG72.decidedSliceAt_all_of_MASTER_CENSUS` /
`capstoneHypotheses_of_MASTER_CENSUS` minus the `hFC` row, which the signed cite
discharges. -/

/-- ★★★ **THE CENSUS MASTER, POST-SIGNATURE**: the full count `∀ n, DecidedSliceAt n`
now rests on exactly {`hEis`, `hSD`, `hPD`, `hCensus`} — the `hFC` literature premise
is GONE (signed). -/
theorem decidedSliceAt_all_of_MASTER_SIGNED
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hCensus : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SteepDecCensusLaw (e - p.2.1 * p.2.2) p.1 p.2.1
            ⟨σ.data.erase (p.2.1, p.2.2)⟩) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG72.decidedSliceAt_all_of_MASTER_CENSUS
    factorCorrespondence_cite hEis hSD hPD hCensus

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, POST-SIGNATURE** (steep-census lineage): the `hFC`
literature premise is GONE (signed); ID12's honesty frame applies verbatim. -/
theorem capstoneHypotheses_of_MASTER_SIGNED (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hCensus : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SteepDecCensusLaw (e - p.2.1 * p.2.2) p.1 p.2.1
            ⟨σ.data.erase (p.2.1, p.2.2)⟩) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG72.capstoneHypotheses_of_MASTER_CENSUS.{uW, uG, uKt, uL} n
    hladder hdeepTwist factorCorrespondence_cite hEis hSD hPD hCensus

/-! ## §3 — THE CLUSTERGEOM MASTER, POST-SIGNATURE (IFCG74 lineage)

Binders byte-identical to `IFCG74.decidedSliceAt_all_of_clusterGeom_matched` /
`capstoneHypotheses_of_clusterGeom_matched` minus the `hR4` row (discharged by §1's
mass-4 closure) resp. the `hFC` row (signed). -/

/-- ★★ **THE CLUSTERGEOM CENSUS MASTER, POST-SIGNATURE**: `hR4` is GONE (mass 4
closed by the signed cite); rests on {`hCG`, `hCL`, `hPCL`, `hPF`, `hLeafSub`}. -/
theorem decidedSliceAt_all_of_clusterGeom_signed
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
          (⟨part⟩ : FactorizationType).degree = n₁ →
          (⟨σ.data - part⟩ : FactorizationType).degree = n₂ →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG74.decidedSliceAt_all_of_clusterGeom_matched
    hCG hCL hPCL hPF hLeafSub (fun σ _ _ _ => coneRemainderLaw_four_all σ)

/-- ★★ **THE CLUSTERGEOM CAPSTONE MASTER, POST-SIGNATURE**: `hFC` is GONE (signed);
rests on {`hEis`, `hCG`, `hCL`, `hPCL`, `hLeafSub`} (+ the ladder/deepTwist config
blocks). -/
theorem capstoneHypotheses_of_clusterGeom_signed (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
          (⟨part⟩ : FactorizationType).degree = n₁ →
          (⟨σ.data - part⟩ : FactorizationType).degree = n₂ →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG74.capstoneHypotheses_of_clusterGeom_matched.{uW, uG, uKt, uL}
    n hladder hdeepTwist factorCorrespondence_cite hEis hCG hCL hPCL hLeafSub

end Uniformity.Density.I10FgmnFired

end

/-! ## Axiom footprint — every line expects Lean core + `fgmn_cite_packageF` + the
census spine's previously-declared cites: the slice masters and the mass-4 rows
additionally carry the owner-signed B.42 `exists_slope_factorization`; the two
capstone masters additionally carry `agnprw_termination` (ID12's, previously
declared).  C.33 and `AX_cellRecursion` must NOT occur. -/

section AxCheck
#print axioms Uniformity.Density.I10FgmnFired.coneRemainderLaw_four_all
#print axioms Uniformity.Density.I10FgmnFired.zcURLim_e1DdDecFam_all
#print axioms Uniformity.Density.I10FgmnFired.powerFullSpanLaw_four_all
#print axioms Uniformity.Density.I10FgmnFired.decidedSliceAt_all_of_MASTER_SIGNED
#print axioms Uniformity.Density.I10FgmnFired.capstoneHypotheses_of_MASTER_SIGNED
#print axioms Uniformity.Density.I10FgmnFired.decidedSliceAt_all_of_clusterGeom_signed
#print axioms Uniformity.Density.I10FgmnFired.capstoneHypotheses_of_clusterGeom_signed
end AxCheck
