/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10CitePkgF

/-!
# Uniformity.ChapI.I10FgmnCite — the FGMN cite package, DECLARED (gate-(b), row 9)

**The SEVENTH landed literature-cite axiom** (the OM-5/BBox1 declaration pattern: one
small file, one `axiom`, the provenance recorded here and in the faithfulness ledger).
`FGMNCitePackageF` — the signable `Prop` staged and machine-typed by unit CPF
(`I10CitePkgF.lean` §1: the three OM-tower pointwise steps with their per-factor `(e, f)`
conclusions in the SOURCE'S OWN CURRENCY, `HasClassicalType` over `IFCG76.DVRClosure`) —
is here declared true by citation.

## Signature

* **Owner sign-off (Asvin, 2026-08-31, verbatim):** "Okay with the CUR landing, I think
  the FGMN cite is fine to go."  Recorded in `docs/REVIEW_QUEUE_2026-08-26.md` (row 9)
  and `docs/PROJECT_STATE.md`.  The signed surface is `FGMNCitePackageF` exactly as
  staged — statement bytes untouched by this file.
* **Faithfulness ledger:** `docs/AXIOM_FAITHFULNESS.md`, seventh entry
  (`fgmn_cite_packageF`, 2026-08-31) — the standing per-axiom audit format.

## Provenance (pointers, not restatements — the staging files carry the full record)

* **Source:** FGMN — J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of
  MacLane valuations*, J. Algebra 427 (2015) 30–75, DOI 10.1016/j.jalgebra.2014.12.022 —
  **Theorem 6.2 + Theorem 6.4 + Corollary 6.6** (§6.1), print-read VERBATIM 2026-08-31
  against the repo PDF (`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`);
  the three quotes are in the `I10CitePkgF.lean` module docstring.  Companion (same
  content, MacLane–Vaquié currency, Henselian case): AGNPRW, *Polynomial factorization
  over Henselian fields*, Found. Comput. Math. (2024), Thm 2.11 + Thm 4.17 (repo PDF
  `docs/references/s10208-024-09646-x.pdf`; same source as the signed row-1
  `agnprw_termination`).
* **Dictionary:** the corpus↔source dictionary is CP2's staging record
  (`I10CitePkg.lean` docstring, hypothesis vectors inherited byte-identically) plus
  CPF's conclusion-side delta (`I10CitePkgF.lean` docstring: every per-factor clause is
  `HasClassicalType h e f`, the authors' own field invariants).  Standing background
  fact riding INSIDE the statement: Serre, *Corps Locaux* II §2 Prop. 3 (integral
  closure of a complete DVR in a finite extension is a DVR, finite free of full rank,
  no separability) — the existence of the `DVRClosure` realization each conclusion
  asserts.
* **CUR's bridge (why the corpus currency is DERIVED, never trusted):** the gcd-currency
  package `FGMNCitePackage` follows from this axiom by the Lean-core theorem
  `fgmn_package_of_packageF` through `IFCG76.inertiaDegOf_eq_inertiaDeg'_of_closure`
  (the currency lemma).  Caveat A of the CP2 staging (order-gcd vs. field-invariant
  reading) is RESOLVED — no per-equality currency reading remains trusted.
* **Carried caveats (B/C/D/E, adjudicated at signing; full text in `I10CitePkgF.lean`):**
  (B) legs E/U quantify over inseparable/repeated-factor `g` beyond the classical
  separable statements; (C) the transform currency (`devT`) vs. Thm 6.4's residual-ideal
  indexing is the trusted dictionary (C66b genre; AGNPRW Thm 4.17); (D) leg R consumes
  only normalization-robust residual reads; (E) sufficiency only — no converse, no
  exhaustiveness.

## Non-vacuity / consistency teeth (Lean-core, landed BEFORE the signature)

`unramifiedLegSourceAt_zero` (leg U's `k = 0` instance proved outright);
`hasClassicalType_eisKey` (leg E's key reads `(e', 1)` — Thm 6.2's totally ramified
read); `hasClassicalType_of_irreducible_map` (leg U's key reads `(1, deg)`);
`hasClassicalType_unique` (the carrier is single-valued); IFCG76 §2/§5 anchors
(`efPair_eisKey`, `inertiaDegOf_of_irreducible_map`, `hasResidueDegree_of_isDVR`).

## Downstream (§1 below: the unconditional forms)

`fgmn_cite_package` makes the old signing surface `FGMNCitePackage` a THEOREM; the eight
CP2/CPF consumer re-exports fire unconditionally (`*_cite` forms below); every consumer's
`#print axioms` shows `fgmn_cite_packageF` (the H-14 inheritance pattern).  The declared
allowlist grows to SEVEN: `{exists_slope_factorization, graded_factorization_unique,
fgmn_residual_mul, agnprw_termination, bBox1_cite, tier1_typeOf, fgmn_cite_packageF}`
(+ the gentow5w pair's file-scoped rows, per the ledger's current accounting) + Lean core.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.I10CitePkgF

open IsLocalRing Polynomial
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG39 (devT eisKey)
open Uniformity.Density.IFCG22 (NPAttains NPVisibleAt)
open Uniformity.Density.IFCG35 (classResidualPoly MinFaceAt)
open Uniformity.Density.IFCG47 (scaleType CellTypeScalingAt CellTypeScaling)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt DeepWildTypeScalingStatement)
open Uniformity.Density.IFCG64 (unramScaleType towerScaleType)
open Uniformity.Density.IFCG43 (cellTransport)
open Uniformity.Density.IFCG44 (alphaBox)
open Uniformity.Density.IFCG76
open Uniformity.Density.I10CitePkg

attribute [local instance] Classical.propDecidable

/-! ## §0 — THE DECLARATION -/

/-- **FGMN `[cite:FGMN 2015 Thm 6.2 + Thm 6.4 + Cor 6.6; AGNPRW 2024 Thm 2.11 + 4.17
companion; Serre CL II §2 Prop. 3 riding inside]` (gate (b), row 9).**  The
source-currency FGMN cite package — the three OM-tower pointwise factorization steps
(Eisenstein / unramified / pure-face residual dissection) with the authors' own
per-factor `(e, f)` conclusions — declared true by citation.  Signed by the owner
2026-08-31 ("Okay with the CUR landing, I think the FGMN cite is fine to go"); the full
provenance is the module docstring + the seventh `docs/AXIOM_FAITHFULNESS.md` entry;
the statement is `I10CitePkgF.lean` §1, bytes untouched. -/
axiom fgmn_cite_packageF : FGMNCitePackageF

/-! ## §1 — THE UNCONDITIONAL FORMS (every CP2/CPF consumer, fired)

Signatures byte-identical to I10CitePkgF §3 minus the `hpkg` binder (which see for the
full docstrings); bodies are one-line applications of the axiom.  Everything downstream
of `FGMNCitePackage` / `FactorCorrespondenceAt` / the legs now fires from these. -/

/-- The gcd-currency package is now a THEOREM (`fgmn_package_of_packageF` at the
axiom): the old signing surface, unconditional. -/
theorem fgmn_cite_package : FGMNCitePackage :=
  fgmn_package_of_packageF fgmn_cite_packageF

/-- Leg E, statement form, unconditional. -/
theorem eisensteinLeg_cite : EisensteinLegStatement :=
  fgmn_cite_package.1

/-- Leg U, statement form, unconditional. -/
theorem unramifiedLeg_cite : UnramifiedLegStatement :=
  fgmn_cite_package.2.1

/-- Leg R, statement form, unconditional. -/
theorem pureFaceResidualLeg_cite : PureFaceResidualLegStatement :=
  fgmn_cite_package.2.2

/-- ★ **The FC_D family, unconditional** (row 9's old recommended surface; the census
master's `hFC` premise, GONE): `FactorCorrespondenceAt D` at every depth `D ≥ 2`. -/
theorem factorCorrespondence_cite : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D :=
  factorCorrespondence_of_packageF fgmn_cite_packageF

/-- IFCG48 §1's raw deep-wild surface, unconditional. -/
theorem deepWildTypeScaling_cite : DeepWildTypeScalingStatement :=
  deepWildTypeScaling_of_packageF fgmn_cite_packageF

/-- The COMPLETE pointwise scaling law, unconditional. -/
theorem cellTypeScaling_cite : CellTypeScaling :=
  cellTypeScaling_of_packageF fgmn_cite_packageF

/-- The `D = 2` supply for ER4's dd terms, unconditional. -/
theorem cellTypeScalingAt_two_cite : CellTypeScalingAt 2 :=
  cellTypeScalingAt_two_of_packageF fgmn_cite_packageF

section LegEConsumers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π w : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- IFCG48 §6's decision-transport iff, unconditional. -/
theorem transport_decidedAt_iff_cite
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {D N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  transport_decidedAt_iff_of_packageF fgmn_cite_packageF hπ hw he' hDN hF hbox σ'

end LegEConsumers

section LegUConsumers

/-- MFL's named missing pointwise law, unconditional. -/
theorem unram_typeScaling_cite
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
    {k : ℕ} {g : Polynomial O} (hg : g.Monic) (hdeg : g.natDegree = φ.natDegree * k)
    (hcell : ∀ t, t < k → algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) :
    typeOf g = unramScaleType φ.natDegree (typeOf (devT φ k g)) :=
  unram_typeScaling_of_packageF fgmn_cite_packageF hπ hφ hg hdeg hcell

/-- The mixed-tower composite (`towerScaleType` currency), unconditional. -/
theorem tower_typeScaling_cite
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
    [IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)]
    [Finite (ResidueField (AdjoinRoot φ))]
    {w₁ : AdjoinRoot φ} (hw₁ : IsLocalRing.residue (AdjoinRoot φ) w₁ ≠ 0)
    {e' D : ℕ} (he' : 2 ≤ e')
    [IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e'))]
    {g : Polynomial O} (hg : g.Monic) (hdeg : g.natDegree = φ.natDegree * (e' * D))
    (hcell : ∀ t, t < e' * D →
      algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t))
    (hlat : ∀ j, j < e' * D →
      (algebraMap O (AdjoinRoot φ) π) ^ ((e' * D - j + (e' - 1)) / e')
        ∣ (devT φ (e' * D) g).coeff j)
    (hbox : ∀ t, t < D →
      (AdjoinRoot.root (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e')) ^ (e' * (D - t) + 1)
        ∣ AdjoinRoot.mk (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e')
            (dev (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e') (devT φ (e' * D) g) t)) :
    typeOf g = towerScaleType e' φ.natDegree
        (typeOf (devT (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e') D
          (devT φ (e' * D) g))) :=
  tower_typeScaling_of_packageF fgmn_cite_packageF hπ hφ hw₁ he' hg hdeg hcell hlat hbox

end LegUConsumers

section LegRConsumers

/-- The census pure-face decision socket, unconditional. -/
theorem decidedAt_of_squarefree_residual_cite
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    (hm : 0 < m) (hh : 0 < h) (he' : 0 < e') (hcop : Nat.Coprime h e')
    {c : Coeff O m N} (h0 : NPAttains c h e' 0) (hAm : NPAttains c h e' m)
    (hvis : NPVisibleAt c h e')
    (hsf : Squarefree ((classResidualPoly π c h e').map
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O))) :
    DecidedAt O m
      ⟨(UniqueFactorizationMonoid.normalizedFactors
          ((classResidualPoly π c h e').map
            ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
              resField (X : Polynomial O) →+* ResidueField O))).map
        (fun ψ => (e', ψ.natDegree))⟩ N c :=
  decidedAt_of_squarefree_residual_of_packageF fgmn_cite_packageF hπ hm hh
    he' hcop h0 hAm hvis hsf

end LegRConsumers

end Uniformity.Density.I10CitePkgF

/-! ## Axiom footprint — expect EXACTLY `fgmn_cite_packageF` (+ Lean core on the
derived forms): the declaration file consumes no other cite. -/

section AxCheck
#print axioms Uniformity.Density.I10CitePkgF.fgmn_cite_packageF
#print axioms Uniformity.Density.I10CitePkgF.fgmn_cite_package
#print axioms Uniformity.Density.I10CitePkgF.eisensteinLeg_cite
#print axioms Uniformity.Density.I10CitePkgF.unramifiedLeg_cite
#print axioms Uniformity.Density.I10CitePkgF.pureFaceResidualLeg_cite
#print axioms Uniformity.Density.I10CitePkgF.factorCorrespondence_cite
#print axioms Uniformity.Density.I10CitePkgF.deepWildTypeScaling_cite
#print axioms Uniformity.Density.I10CitePkgF.cellTypeScaling_cite
#print axioms Uniformity.Density.I10CitePkgF.cellTypeScalingAt_two_cite
#print axioms Uniformity.Density.I10CitePkgF.transport_decidedAt_iff_cite
#print axioms Uniformity.Density.I10CitePkgF.unram_typeScaling_cite
#print axioms Uniformity.Density.I10CitePkgF.tower_typeScaling_cite
#print axioms Uniformity.Density.I10CitePkgF.decidedAt_of_squarefree_residual_cite
end AxCheck
