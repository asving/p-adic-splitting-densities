/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10CitePkg
import Uniformity.ChapI.IFCG76

/-!
# Uniformity.ChapI.I10CitePkgF — UNIT CPF: the FGMN cite package in SOURCE CURRENCY
(the theorem statements as the authors wrote them; the gcd-currency package a corollary)

**Owner direction (Asvin, 2026-08-31, verbatim):** "lets import the theorem statement
exactly as the authors intended and prove the currency lemma to translate into our
language."  The currency lemma LANDED as `IFCG76.inertiaDegOf_eq_inertiaDeg'_of_closure`
(unit CUR): through any closure realization (`IFCG76.DVRClosure` — a rank-`deg` free DVR
extension receiving the monogenic order, mathematically the integral closure `O_L`), the
corpus's gcd read `inertiaDegOf` IS the classical residue degree, Lean-core, no
completeness.  This file RESTATES the three legs of the consolidated FGMN cite package
(`I10CitePkg.lean`, unit CP2) with their conclusions in the SOURCE'S OWN CURRENCY — each
matched factor `h` *has a closure realization* with classical ramification index `e` and
classical residue degree `f` (`HasClassicalType h e f`, §0: existence INSIDE the
statement, per CUR's recommendation) — and PROVES the translations: each source-currency
leg implies the corresponding gcd-currency leg through the unconditional bridge, so
`FGMNCitePackage` (the old signing surface) becomes a COROLLARY of `FGMNCitePackageF`
(§2) and every landed consumer fires from the new package with no re-wiring (§3).
**Nothing here is asserted**: no axiom is declared; the owner signs ONE statement
(`FGMNCitePackageF`) — the authors' statements, not a currency reading.

## Why this is the source's ontology (the caveat-A elimination at the statement level)

FGMN's `F` is a prime polynomial with a root `θ ∈ K̄_v`: the source's invariants
`e(F), f(F)` and residue field `F_F` live in the GENUINE field extension `L = K_v(θ)`,
whose ring of integers `O_L` is a DVR, finite free of rank `deg F` over the complete
`O_v`, receiving `O_v[x]/(F)` by `x ↦ θ` (Serre, *Corps Locaux* II §2 Prop. 3 — no
separability needed over a complete base; injectivity because monic-`F` makes
`O_v[x]/(F)` a full-rank free submodule of `K_v[x]/(F) = L`).  So the source's own
assertion carries the realization: stating the legs with `HasClassicalType` conclusions
is stating what the authors wrote, with `DVRClosure` as the formal proxy for `O_L`
(IFCG76's docstring records the uniqueness argument: ANY realization is integrally
closed with fraction field `L`, hence IS `O_L`).  The old caveat A — "the `(e, f)`
currencies are order gcd reads tied to field invariants by a trusted reading" — is
GONE: the tie is now the machine-checked bridge (`inertiaDegOf_eq_of_hasClassicalType`,
§0, from IFCG76), and what remains trusted is the source theorem itself.

Two structural notes for the signing read (recorded honestly, not caveats):
* *Separate vs. coupled existentials.*  The source reads `e, f` of one factor over two
  bases from ONE tower `L/K'/K`; the restated clauses carry one realization per
  (factor, base) pair.  No content drifts: each carrier is single-valued
  (`hasClassicalType_unique` — all realizations of a factor read the same `(e, f)`,
  because both equal the gcd reads), so the separate existentials pin exactly the
  numbers the coupled reading would.
* *Completeness on the upper floor (leg U/E `H`-side).*  The transform factors `H` live
  over `O' = AdjoinRoot φ`, whose completeness is not in the binder list (mirroring the
  gcd legs); the realization assertion for `H` is nonetheless the source's own — in
  every consumer instance `O'` is genuinely complete (finite free over complete `O`),
  and the source's `O_{v'}` is complete by construction.

## THE PROPOSED GATE-(b) CITE — source-currency faithfulness DRAFT (stated, NOT asserted)

**Proposed statement:** `axiom …fgmn_cite_packageF : FGMNCitePackageF` (§1) — the
conjunction of the three source-currency legs.  Signing it yields the old package
`FGMNCitePackage` by the Lean-core theorem `fgmn_package_of_packageF` (§2), hence every
consumer in I10CitePkg §2–§4 (re-exported §3).  Each leg is also a standalone named Prop
should the owner prefer to sign a subset.

**Source (print-read 2026-08-31 by unit CP2 against the repo PDFs):** FGMN —
J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane valuations*,
J. Algebra 427 (2015) 30–75 (repo PDF
`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`) — **Theorem 6.2, Theorem 6.4,
Corollary 6.6** (§6.1, "Prime polynomials and inductive valuations"); companion (same
statements in MacLane–Vaquié currency, Henselian case): AGNPRW — Alberich-Carramiñana,
Guàrdia, Nart, Poteaux, Roé, Weimann, *Polynomial factorization over Henselian fields*,
Found. Comput. Math. (2024), Thm 2.11 + Thm 4.17 (repo PDF
`docs/references/s10208-024-09646-x.pdf`; already the source of the row-1 cite
`agnprw_termination`).  Verbatim quotes (FGMN, author PDF), carried over from
I10CitePkg's staging:

> **Theorem 6.2.** Let F ∈ P be a prime polynomial and θ ∈ K̄_v a root of F. Let φ be a
> key polynomial for the inductive valuation µ. Then, φ |_µ F if and only if
> v(φ(θ)) > µ(φ). Moreover, if this condition holds, then: (1) Either F = φ, or the
> Newton polygon N_{µ,φ}(F) is one-sided of slope −ν, where ν = v(φ(θ)) − µ(φ) ∈ Q_{>0}.
> (2) Let ℓ = ℓ(N_{µ,φ}(F)). Then, F ∼_µ φ^ℓ and deg F = deg φ^ℓ. In particular, R(F)
> is a power of the maximal ideal R(φ).

> **Theorem 6.4.** Let φ be a proper key polynomial for the inductive valuation µ.
> Then, every monic g ∈ O_v[x] factorizes into a product of monic polynomials in
> O_v[x]:  g = g₀ · φ^{ord_φ(g)} · ∏_{(ν,L)} g_{ν,L},  where −ν runs on the slopes of
> N⁻_{µ,φ}(g). For each ν, let µ_ν := [µ; (φ, ν)]; then, L runs on the maximal ideals
> of ∆(µ_ν) dividing R_{µ_ν}(g). If e_ν is the least denominator of e(µ)ν, then
> deg g₀ = deg g − ℓ(N⁻_{µ,φ}(g)) deg φ,   deg g_{ν,L} = e_ν ord_L(R_{µ_ν}(g)) deg L deg φ.
> Moreover, if ord_L(R_{µ_ν}(g)) = 1, then g_{ν,L} is irreducible in O_v[x].

> **Corollary 6.6.** With the above notation, let θ_φ ∈ K̄_v be a root of φ.
> (1) For any polynomial g ∈ K[x] with deg g < deg φ, we have v(g(θ_φ)) = v(g(θ)).
> In particular, e(φ) | e(F).  (2) There is a canonical embedding F_φ → F_F, given by
> g(θ_φ) + m_φ ↦ g(θ) + m_F for any g ∈ K[x] with deg g < deg φ such that v(g(θ_φ)) ≥ 0.

(FGMN's §6.1 preamble: Theorem 6.4 "has to be considered as a generalization of
Hensel's lemma".  All three legs are instances of Thm 6.4's dissection at an order-1
base valuation, with the per-factor `(e, f)` reads supplied by Thm 6.2 + Cor 6.6.)

**Dictionary (corpus ↔ source) — the DELTA against I10CitePkg's standing dictionary
(which is inherited wholesale for the hypothesis vectors, byte-identical here):**
* Every per-factor conclusion clause is now `HasClassicalType h e f`: "`h` has a closure
  realization with classical `(ramificationIdx', inertiaDeg') = (e, f)`" ↔ the source's
  "`e(F) = e, f(F) = f` in the extension generated by a root of `F`".  The realization
  existence is PART of the source's assertion (`F` has a root; `O_L` exists — Serre II
  §2 Prop. 3), riding inside the cite exactly as CUR recommended.
* Leg E (`FactorCorrespondenceSourceAt`): matched pair `(h, H)` carries
  `HasClassicalType H eH fH ∧ HasClassicalType h (e'·eH) fH` — Cor 6.6 across the
  totally ramified step (`e(K'/K) = e'`, `f(K'/K) = 1`): `e(L/K) = e'·e(L/K')`,
  `f(L/K) = f(L/K')` — plus Thm 6.4's degree formula `deg h = e'·deg H`.
* Leg U (`UnramifiedLegSourceAt`): matched pair carries
  `HasClassicalType H eH fH ∧ HasClassicalType h eH (d·fH)` — Cor 6.6(2) across the
  unramified step (`F_φ = F_{q^d} ↪ F_F`): `e(L/K) = e(L/K')`, `f(L/K) = d·f(L/K')` —
  plus `deg h = d·deg H`.
* Leg R (`PureFaceResidualSourceStatement`): matched pair `(g', ψ)` carries
  `HasClassicalType g' e' (deg ψ)` — Thm 6.4's `(e, f) = (e_ν, deg L) = (e', deg ψ)`
  read at the block — plus `deg g' = e'·deg ψ`.
* The gcd-currency clauses of I10CitePkg are IMPLIED (never assumed): the bridge
  `inertiaDegOf_eq_of_hasClassicalType` (§0, = IFCG76's currency lemma) turns each
  source clause into the gcd clause; the `e`-components, classically redundant given
  `f` and the degree (the fundamental identity `e·f = deg` holds in every realization),
  are carried because the source asserts them, and give the corpus's `ramIndexOf`/
  `efPair` reads directly (`efPair_eq_of_hasClassicalType`).

**Scope caveats (the signing read must adjudicate):**
1. *Caveat A — RESOLVED, no longer on the ledger.*  Formerly: the order-gcd vs.
   field-invariant reading, trusted per equality.  Now: the legs state the field
   invariants themselves; the translation to the corpus currency is the machine-checked
   IFCG76 bridge; the realization existence inside each conclusion is the source's own
   standing fact (Serre, *Corps Locaux* II §2 Prop. 3, complete base, no separability).
2. *Caveat B (multiplicity / inseparability) — carried verbatim from I10CitePkg.*
   Legs E and U match factors WITH multiplicity over ALL monic `g` in their cells —
   including inseparable / repeated-factor `g`.  The classical sources state the
   correspondence for separable (often squarefree) `g`.  The signing read must confirm
   the cells exclude/handle this fringe or add a separability hypothesis.  For leg R
   the `Squarefree` residual hypothesis excludes the repeated-block fringe at the
   residual level; the inseparable-`g` reading still applies.
3. *Caveat C (transform aggregation — legs E and U) — carried verbatim.*  Thm 6.4's
   conclusion is indexed by maximal ideals `L` of `∆(µ_ν)`; the corpus conclusion is in
   TRANSFORM currency (`monicFactors (devT φ k g)` over `O'`).  The identification of
   the `O'`-factorization of the transform with the `(ν, L)`-indexed blocks is part of
   the trusted dictionary (FGMN §5 + §6; the standing C66b dictionary; AGNPRW Thm 4.17).
4. *Caveat D (leg R residual normalization) — carried verbatim.*  `classResidualPoly`
   is one concrete normalization of FGMN's `R_{µ_ν}` (fixed up to slot-wise
   homogeneous-unit rescalings, Cor 4.9(3)); leg R consumes only normalization-robust
   reads (degrees, squarefreeness).
5. *Caveat E (sufficiency only) — carried verbatim.*  Each leg asserts its
   correspondence FOR the stated cell/face hypotheses; no converse, no exhaustiveness.

## Map

* **§0** `HasClassicalType` (the classical-pair carrier over `DVRClosure`) + the bridges
  into every corpus currency (`inertiaDegOf`/`ramIndexOf`/`efPair`), uniqueness,
  non-vacuity (identity realization on the maximal locus; `eisKey` and unramified
  anchors in full pair currency).
* **§1** the three SOURCE-currency legs + `FGMNCitePackageF` (stated, NOT asserted).
* **§2** THE TRANSLATIONS: each source leg ⟹ its gcd leg (one theorem per leg), and
  ★ `fgmn_package_of_packageF : FGMNCitePackageF → FGMNCitePackage` — the old signing
  surface as a corollary.
* **§3** consumer re-exports: every I10CitePkg consumer fired from the NEW package
  through the old one (one-line compositions; nothing downstream re-wires).
* **§4** vacuity tooth: `unramifiedLegSourceAt_zero` (leg U's `k = 0` instance, proved
  outright).  Source-currency analogues of I10CitePkg's `pureFaceResidualLeg_irr_instance`
  need realization EXISTENCE off the maximal locus, which is exactly the content that
  rides inside the cite — the maximal-locus anchors (§0; IFCG76 §2/§5) are the honest
  Lean-core teeth here.

Every declaration in this file is PURE LEAN CORE (`#print axioms` footer): the package
is staged, never asserted; consumers take it as an explicit hypothesis until signed.

## Honest scope

Identical to I10CitePkg's (this file changes the CURRENCY of the signing surface, not
its coverage): signing `FGMNCitePackageF` closes the literature content of the census
master's `hFC` premise, MFL's unramified pointwise step and the mixed-tower composite,
and the squarefree-residual pure-face type pin.  It does NOT cover: **the slope-`h ≥ 2`
deep-primary recentring step** (no statement carrier yet — the general-slope key
generates a non-DVR order; MFL's Bézout-ring route must be built first), the `ZcURLim`
census assemblies, the convolution-defect and leaf-subface premises, and the
general-position `FracFaceForcesRamStatement` — all flagged in I10CitePkg's docstring.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.I10CitePkgF

open IsLocalRing Polynomial
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG39 (devT devT_coeff devT_monic eisKey eisKey_monic eisKey_natDegree)
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

/-- A monic irreducible has positive degree (kit; IFCG48 §4's private replica). -/
private theorem natDegree_pos_of_monic_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {g : Polynomial R} (hg : g.Monic) (hirr : Irreducible g) : 0 < g.natDegree := by
  by_contra hcon
  have h1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp (by omega)
  rw [h1] at hirr
  exact hirr.not_isUnit isUnit_one

/-! ## §0 — The classical-pair carrier: `HasClassicalType`

`HasClassicalType g e f` = some closure realization of the monogenic order `O[x]/(g)`
(IFCG76's `DVRClosure`: a rank-`deg g` free DVR extension of `O` receiving the order
injectively — mathematically the integral closure `O_L`) has classical ramification
index `e` and classical residue degree `f`.  This is the source's own `(e(F), f(F))`;
the bridges below (all from IFCG76's currency lemma, Lean-core) translate it into every
corpus currency. -/

section Carrier

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The source-currency `(e, f)` read**: `g` has a closure realization with classical
ramification index `e` AND classical residue degree `f`.  (Single-valued by
`hasClassicalType_unique`; the `f`-component alone is CUR's `HasResidueDegree`.) -/
def HasClassicalType (g : Polynomial O) (e f : ℕ) : Prop :=
  ∃ D : DVRClosure g,
    (IsLocalRing.maximalIdeal D.carrier).ramificationIdx' O = e ∧
    (IsLocalRing.maximalIdeal D.carrier).inertiaDeg' O = f

/-- Projection to CUR's carrier: the `f`-component is `HasResidueDegree`. -/
theorem hasResidueDegree_of_hasClassicalType {g : Polynomial O} {e f : ℕ}
    (h : HasClassicalType g e f) : HasResidueDegree g f := by
  obtain ⟨D, -, hDf⟩ := h
  exact ⟨D, hDf⟩

/-- **THE BRIDGE, f-leg** (= IFCG76's currency lemma through the carrier): a
source-currency residue-degree read IS the corpus's gcd read. -/
theorem inertiaDegOf_eq_of_hasClassicalType {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) {e f : ℕ} (h : HasClassicalType g e f) :
    inertiaDegOf g = f := by
  obtain ⟨D, -, hDf⟩ := h
  rw [← hDf]
  exact inertiaDegOf_eq_inertiaDeg'_of_closure hg hd D.basis D.emb D.emb_injective

/-- **THE BRIDGE, e-leg**: a source-currency ramification read IS the corpus's
`ramIndexOf`. -/
theorem ramIndexOf_eq_of_hasClassicalType {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) {e f : ℕ} (h : HasClassicalType g e f) :
    ramIndexOf g = e := by
  obtain ⟨D, hDe, -⟩ := h
  rw [← hDe]
  exact ramIndexOf_eq_ramificationIdx'_of_closure hg hd D.basis D.emb D.emb_injective

/-- The pair form: a source-currency read pins the corpus's `efPair` outright. -/
theorem efPair_eq_of_hasClassicalType {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) {e f : ℕ} (h : HasClassicalType g e f) :
    efPair g = (e, f) := by
  rw [efPair, ramIndexOf_eq_of_hasClassicalType hg hd h,
    inertiaDegOf_eq_of_hasClassicalType hg hd h]

/-- `HasClassicalType` is single-valued: all realizations read the same `(e, f)` (both
components equal the gcd reads).  The separate per-factor existentials of the restated
legs therefore pin exactly what the source's coupled reading would. -/
theorem hasClassicalType_unique {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    {e₁ f₁ e₂ f₂ : ℕ} (h₁ : HasClassicalType g e₁ f₁) (h₂ : HasClassicalType g e₂ f₂) :
    e₁ = e₂ ∧ f₁ = f₂ := by
  constructor
  · rw [← ramIndexOf_eq_of_hasClassicalType hg hd h₁,
      ← ramIndexOf_eq_of_hasClassicalType hg hd h₂]
  · rw [← inertiaDegOf_eq_of_hasClassicalType hg hd h₁,
      ← inertiaDegOf_eq_of_hasClassicalType hg hd h₂]

/-- Any closure realization carries the gcd reads as its classical pair. -/
theorem hasClassicalType_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (D : DVRClosure g) :
    HasClassicalType g (ramIndexOf g) (inertiaDegOf g) :=
  ⟨D, (ramIndexOf_eq_ramificationIdx'_of_closure hg hd D.basis D.emb D.emb_injective).symm,
    (inertiaDegOf_eq_inertiaDeg'_of_closure hg hd D.basis D.emb D.emb_injective).symm⟩

/-- **Non-vacuity on the maximal locus**: when `AdjoinRoot g` is itself a DVR the
identity embedding realizes the closure and the classical pair is the gcd pair. -/
theorem hasClassicalType_of_isDVR {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    HasClassicalType g (ramIndexOf g) (inertiaDegOf g) :=
  hasClassicalType_of_closure hg hd
    { carrier := AdjoinRoot g
      basis := (AdjoinRoot.powerBasis' hg).basis.reindex
        (finCongr (AdjoinRoot.powerBasis'_dim hg))
      emb := AlgHom.id O (AdjoinRoot g)
      emb_injective := Function.injective_id }

/-- The full ⟺, conditional on realization existence (mirror of IFCG76's
`hasResidueDegree_iff_of_closure`, pair form): given ANY realization, the
source-currency pair read and the gcd-currency pair read are interchangeable.  The
restated legs assert the `→`-consumable form; existence rides inside them. -/
theorem hasClassicalType_iff_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (D : DVRClosure g) {e f : ℕ} :
    HasClassicalType g e f ↔ (ramIndexOf g = e ∧ inertiaDegOf g = f) := by
  constructor
  · intro h
    exact ⟨ramIndexOf_eq_of_hasClassicalType hg hd h,
      inertiaDegOf_eq_of_hasClassicalType hg hd h⟩
  · rintro ⟨he, hf⟩
    exact ⟨D,
      (ramIndexOf_eq_ramificationIdx'_of_closure hg hd D.basis D.emb
        D.emb_injective).symm.trans he,
      (inertiaDegOf_eq_inertiaDeg'_of_closure hg hd D.basis D.emb
        D.emb_injective).symm.trans hf⟩

/-- The Eisenstein-key anchor in FULL pair currency: at the package's own leg-E key,
`HasClassicalType (eisKey π c e') e' 1` — Thm 6.2's totally ramified read `(e', 1)`,
Lean-core on the DVR locus (where `eis_isDVR` puts every consumer instance). -/
theorem hasClassicalType_eisKey {π c : O} (hπ : Irreducible π)
    (hc : IsLocalRing.residue O c ≠ 0) {e' : ℕ} (he' : 0 < e')
    [IsDomain (AdjoinRoot (eisKey π c e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π c e'))] :
    HasClassicalType (eisKey π c e') e' 1 := by
  have hd : 0 < (eisKey π c e').natDegree := by rw [eisKey_natDegree he']; omega
  have h := hasClassicalType_of_isDVR (eisKey_monic he') hd
  have hram : ramIndexOf (eisKey π c e') = e' := by
    rw [ramIndexOf, inertiaDegOf_eisKey hπ hc he', Nat.div_one, eisKey_natDegree he']
  rwa [hram, inertiaDegOf_eisKey hπ hc he'] at h

/-- The unramified anchor in FULL pair currency: `ḡ` irreducible forces
`HasClassicalType g 1 (deg g)` — Cor 6.6(2)'s unramified read, Lean-core (the DVR
instance is the quarried `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`). -/
theorem hasClassicalType_of_irreducible_map {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (h : Irreducible (g.map (residue O)))
    [IsDomain (AdjoinRoot g)] :
    HasClassicalType g 1 g.natDegree := by
  haveI : IsDiscreteValuationRing (AdjoinRoot g) :=
    (AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hg
      (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)) h).2.1
  have hh := hasClassicalType_of_isDVR hg hd
  have hin : inertiaDegOf g = g.natDegree := inertiaDegOf_of_irreducible_map hg hd h
  have hram : ramIndexOf g = 1 := by
    rw [ramIndexOf, hin, Nat.div_self hd]
  rwa [hram, hin] at hh

end Carrier

/-! ## §1 — THE SOURCE-CURRENCY CITE SURFACE (stated, NOT asserted)

Hypothesis vectors BYTE-IDENTICAL to the gcd-currency legs (I10CitePkg §1 / IFCG48 §5 —
they were read off the source and are unchanged); only the per-factor conclusion clauses
are restated, in the authors' own ontology. -/

section CiteSurface

/-- **Leg E (Eisenstein / deep-wild), SOURCE currency** — `IFCG48.FactorCorrespondenceAt`
with the per-factor conclusion restated classically: each matched pair `(h, H)` carries
closure realizations reading `e(L/K) = e'·e(L/K')` and `f(L/K) = f(L/K')` (Cor 6.6
across the totally ramified step `e(K'/K) = e', f(K'/K) = 1`) plus Thm 6.4's degree
formula.  Source: FGMN Thm 6.2 + Thm 6.4 at the Eisenstein key `eisKey π w e'`. -/
def FactorCorrespondenceSourceAt (D : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π w : O, Irreducible π → IsLocalRing.residue O w ≠ 0 →
  ∀ e' : ℕ, 2 ≤ e' →
  ∀ [IsDomain (AdjoinRoot (eisKey π w e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))],
  ∀ g : Polynomial O, g.Monic → g.natDegree = e' * D →
    (∀ j, j < e' * D → π ^ ((e' * D - j + (e' - 1)) / e') ∣ g.coeff j) →
    (∀ t, t < D → (AdjoinRoot.root (eisKey π w e')) ^ (e' * (D - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') g t)) →
    Multiset.Rel
      (fun h H => (∃ eH fH, HasClassicalType H eH fH ∧ HasClassicalType h (e' * eH) fH)
        ∧ h.natDegree = e' * H.natDegree)
      (monicFactors g) (monicFactors (devT (eisKey π w e') D g))

/-- Leg E quantified over the census depths (the signing surface's first conjunct;
mirrors `EisensteinLegStatement`). -/
def EisensteinLegSourceStatement : Prop := ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceSourceAt D

/-- **Leg U (unramified) at depth `k`, SOURCE currency** — `I10CitePkg.UnramifiedLegAt`
with the per-factor conclusion restated classically: each matched pair `(h, H)` carries
closure realizations reading `e(L/K) = e(L/K')` and `f(L/K) = d·f(L/K')` (Cor 6.6(2)'s
residue embedding `F_φ = F_{q^d} ↪ F_F` across the unramified step) plus the degree
formula `deg h = d·deg H`.  Source: FGMN Thm 6.2(2) + Thm 6.4 + Cor 6.6 at an order-1
key lift `φ` (`IsKey φ`: monic, irreducible reduction of degree `d`). -/
def UnramifiedLegSourceAt (k : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π : O, Irreducible π →
  ∀ φ : Polynomial O, IsKey φ →
  ∀ [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)],
  ∀ g : Polynomial O, g.Monic → g.natDegree = φ.natDegree * k →
    (∀ t, t < k → algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) →
    Multiset.Rel
      (fun h H => (∃ eH fH, HasClassicalType H eH fH
          ∧ HasClassicalType h eH (φ.natDegree * fH))
        ∧ h.natDegree = φ.natDegree * H.natDegree)
      (monicFactors g) (monicFactors (devT φ k g))

/-- Leg U quantified over every depth (the signing surface's second conjunct). -/
def UnramifiedLegSourceStatement : Prop := ∀ k : ℕ, UnramifiedLegSourceAt k

/-- **Leg R (the pure-face residual dissection), SOURCE currency** —
`I10CitePkg.PureFaceResidualLegStatement` with the per-factor conclusion restated
classically: each matched pair `(g', ψ)` carries a closure realization reading
`(e(g'), f(g')) = (e', deg ψ)` (Thm 6.4's degree formula at `ord_L = 1`, `deg φ = 1`,
`e_ν = e'`, with Cor 6.6's per-block reads) plus `deg g' = e'·deg ψ`. -/
def PureFaceResidualSourceStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π : O, Irreducible π →
  ∀ m N h e' : ℕ, 0 < m → 0 < h → 0 < e' → Nat.Coprime h e' →
  ∀ c : Coeff O m N, NPAttains c h e' 0 → NPAttains c h e' m → NPVisibleAt c h e' →
  Squarefree ((classResidualPoly π c h e').map
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O)) →
  ∀ a : Fin m → O, proj O m N a = c →
    Multiset.Rel
      (fun g' ψ => HasClassicalType g' e' ψ.natDegree ∧ g'.natDegree = e' * ψ.natDegree)
      (monicFactors (monicPoly a))
      (UniqueFactorizationMonoid.normalizedFactors
        ((classResidualPoly π c h e').map
          ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
            resField (X : Polynomial O) →+* ResidueField O)))

/-- **THE SOURCE-CURRENCY CITE PACKAGE — stated, NOT asserted**: the three OM-tower
pointwise steps with their conclusions as the authors wrote them, one signing decision.
A future owner-signed `axiom … : FGMNCitePackageF` makes the gcd-currency package
`FGMNCitePackage` a theorem (§2's `fgmn_package_of_packageF`), hence fires every
consumer in I10CitePkg §2–§4 (re-exported §3) with the axiom name visible in every
downstream `#print axioms`.  Until then, every consumer takes the package (or a single
leg) as an explicit hypothesis. -/
def FGMNCitePackageF : Prop :=
  EisensteinLegSourceStatement ∧ UnramifiedLegSourceStatement
    ∧ PureFaceResidualSourceStatement

end CiteSurface

/-! ## §2 — THE TRANSLATIONS: source currency ⟹ gcd currency (one theorem per leg)

All Lean-core: per matched factor, the §0 bridges (= IFCG76's currency lemma) turn the
classical reads into the gcd reads; the factors' monicity/irreducibility (hence positive
degree) comes from `monicFactors_spec`.  The old package is then a corollary. -/

section Translations

/-- **Leg E translation**: the source-currency correspondence implies the gcd-currency
correspondence at every depth.  Per pair `(h, H)`: `inertiaDegOf h = fH = inertiaDegOf H`
by the f-bridge on both floors. -/
theorem factorCorrespondenceAt_of_sourceAt {D : ℕ}
    (hsrc : FactorCorrespondenceSourceAt D) : FactorCorrespondenceAt D := by
  intro O _ _ _ _ _ π w hπ hw e' he' _ _ g hg hdeg hlat hbox
  have he'' : 0 < e' := by omega
  have hkeyd : 0 < (eisKey π w e').natDegree := by
    rw [eisKey_natDegree he'']; omega
  have hdeg' : g.natDegree = (eisKey π w e').natDegree * D := by
    rw [eisKey_natDegree he'']; exact hdeg
  obtain ⟨hGm, -⟩ := devT_monic (eisKey_monic he'') hkeyd hg hdeg'
  refine (hsrc O π w hπ hw e' he' g hg hdeg hlat hbox).mono ?_
  intro h hhmem H hHmem hr
  obtain ⟨⟨eH, fH, hHcl, hhcl⟩, hdeq⟩ := hr
  obtain ⟨hhm, hhirr⟩ := (monicFactors_spec hg).1 h hhmem
  obtain ⟨hHm, hHirr⟩ := (monicFactors_spec hGm).1 H hHmem
  refine ⟨?_, hdeq⟩
  rw [inertiaDegOf_eq_of_hasClassicalType hhm
      (natDegree_pos_of_monic_irreducible hhm hhirr) hhcl,
    inertiaDegOf_eq_of_hasClassicalType hHm
      (natDegree_pos_of_monic_irreducible hHm hHirr) hHcl]

/-- Leg E translation, statement form. -/
theorem eisensteinLeg_of_source (hsrc : EisensteinLegSourceStatement) :
    EisensteinLegStatement :=
  fun D hD => factorCorrespondenceAt_of_sourceAt (hsrc D hD)

/-- **Leg U translation**: per pair `(h, H)`,
`inertiaDegOf h = d·fH = d·inertiaDegOf H` by the f-bridge on both floors. -/
theorem unramifiedLegAt_of_sourceAt {k : ℕ} (hsrc : UnramifiedLegSourceAt k) :
    UnramifiedLegAt k := by
  intro O _ _ _ _ _ π hπ φ hφ _ _ g hg hdeg hcell
  obtain ⟨hGm, -⟩ := devT_monic hφ.monic hφ.pos hg hdeg
  refine (hsrc O π hπ φ hφ g hg hdeg hcell).mono ?_
  intro h hhmem H hHmem hr
  obtain ⟨⟨eH, fH, hHcl, hhcl⟩, hdeq⟩ := hr
  obtain ⟨hhm, hhirr⟩ := (monicFactors_spec hg).1 h hhmem
  obtain ⟨hHm, hHirr⟩ := (monicFactors_spec hGm).1 H hHmem
  refine ⟨?_, hdeq⟩
  rw [inertiaDegOf_eq_of_hasClassicalType hhm
      (natDegree_pos_of_monic_irreducible hhm hhirr) hhcl,
    inertiaDegOf_eq_of_hasClassicalType hHm
      (natDegree_pos_of_monic_irreducible hHm hHirr) hHcl]

/-- Leg U translation, statement form. -/
theorem unramifiedLeg_of_source (hsrc : UnramifiedLegSourceStatement) :
    UnramifiedLegStatement :=
  fun k => unramifiedLegAt_of_sourceAt (hsrc k)

/-- **Leg R translation**: per pair `(g', ψ)`, `inertiaDegOf g' = deg ψ` is the f-bridge
at `f := deg ψ`. -/
theorem pureFaceResidualLeg_of_source (hsrc : PureFaceResidualSourceStatement) :
    PureFaceResidualLegStatement := by
  intro O _ _ _ _ _ π hπ m N h e' hm hh he' hcop c h0 hAm hvis hsf a ha
  refine (hsrc O π hπ m N h e' hm hh he' hcop c h0 hAm hvis hsf a ha).mono ?_
  intro g' hg'mem ψ hψmem hr
  obtain ⟨hcl, hdeq⟩ := hr
  obtain ⟨hg'm, hg'irr⟩ := (monicFactors_spec (monicPoly_monic a)).1 g' hg'mem
  exact ⟨inertiaDegOf_eq_of_hasClassicalType hg'm
    (natDegree_pos_of_monic_irreducible hg'm hg'irr) hcl, hdeq⟩

/-- ★★★ **THE OLD PACKAGE IS A COROLLARY**: the source-currency package implies the
gcd-currency package, Lean-core.  Signing `FGMNCitePackageF` therefore fires every
landed consumer of `FGMNCitePackage` with no re-wiring. -/
theorem fgmn_package_of_packageF (hpkg : FGMNCitePackageF) : FGMNCitePackage :=
  ⟨eisensteinLeg_of_source hpkg.1, unramifiedLeg_of_source hpkg.2.1,
    pureFaceResidualLeg_of_source hpkg.2.2⟩

end Translations

/-! ## §3 — CONSUMER RE-EXPORTS: every I10CitePkg consumer fires from the NEW package

Signatures byte-identical to I10CitePkg §2–§4 (which see for the full docstrings);
bodies are one-line compositions through `fgmn_package_of_packageF`.  Nothing
downstream re-wires: consumers keep firing from the old package, and the old package
fires from this one. -/

section LegEConsumers

/-- Leg E's projection, from the source package (row 9's old recommended surface). -/
theorem factorCorrespondence_of_packageF (hpkg : FGMNCitePackageF) :
    ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D :=
  factorCorrespondence_of_package (fgmn_package_of_packageF hpkg)

/-- IFCG48 §1's raw surface, from the source package. -/
theorem deepWildTypeScaling_of_packageF (hpkg : FGMNCitePackageF) :
    DeepWildTypeScalingStatement :=
  deepWildTypeScaling_of_package (fgmn_package_of_packageF hpkg)

/-- The COMPLETE pointwise scaling law, from the source package. -/
theorem cellTypeScaling_of_packageF (hpkg : FGMNCitePackageF) : CellTypeScaling :=
  cellTypeScaling_of_package (fgmn_package_of_packageF hpkg)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π w : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- IFCG48 §6's decision-transport iff, from the source package. -/
theorem transport_decidedAt_iff_of_packageF (hpkg : FGMNCitePackageF)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {D N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  transport_decidedAt_iff_of_package (fgmn_package_of_packageF hpkg) hπ hw he' hDN hF
    hbox σ'

/-- The `D = 2` supply for ER4's dd terms, from the source package. -/
theorem cellTypeScalingAt_two_of_packageF (hpkg : FGMNCitePackageF) :
    CellTypeScalingAt 2 :=
  cellTypeScalingAt_two_of_package (fgmn_package_of_packageF hpkg)

end LegEConsumers

section LegUConsumers

/-- MFL's named missing pointwise law, from the source package. -/
theorem unram_typeScaling_of_packageF (hpkg : FGMNCitePackageF)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
    {k : ℕ} {g : Polynomial O} (hg : g.Monic) (hdeg : g.natDegree = φ.natDegree * k)
    (hcell : ∀ t, t < k → algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) :
    typeOf g = unramScaleType φ.natDegree (typeOf (devT φ k g)) :=
  unram_typeScaling_of_package (fgmn_package_of_packageF hpkg) hπ hφ hg hdeg hcell

/-- The mixed-tower composite (`towerScaleType` currency), from the source package. -/
theorem tower_typeScaling_of_packageF (hpkg : FGMNCitePackageF)
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
  tower_typeScaling_of_package (fgmn_package_of_packageF hpkg) hπ hφ hw₁ he' hg hdeg
    hcell hlat hbox

end LegUConsumers

section LegRConsumers

/-- The census pure-face decision socket, from the source package. -/
theorem decidedAt_of_squarefree_residual_of_packageF (hpkg : FGMNCitePackageF)
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
  decidedAt_of_squarefree_residual_of_package (fgmn_package_of_packageF hpkg) hπ hm hh
    he' hcop h0 hAm hvis hsf

end LegRConsumers

/-! ## §4 — VACUITY TOOTH

Mirrors I10CitePkg §5's `unramifiedLegAt_zero` in source currency: the statement shape
is non-vacuously satisfiable-and-true in the trivial regime (empty factor multisets).
Source-currency analogues of `pureFaceResidualLeg_irr_instance` would require proving
realization EXISTENCE off the maximal locus — exactly the Serre II §2 content that rides
inside the cite — so the honest Lean-core teeth beyond `k = 0` are the maximal-locus
anchors: `hasClassicalType_eisKey` (leg E's key reads `(e', 1)`),
`hasClassicalType_of_irreducible_map` (leg U's key reads `(1, d)`), and IFCG76 §2/§5. -/

section Teeth

/-- The empty factorization of `1` (kit; IFCG48 §0's private replica, ring-generic). -/
private theorem monicFactors_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : monicFactors (1 : Polynomial R) = 0 :=
  monicFactors_eq ⟨fun g hg => absurd hg (Multiset.notMem_zero g), Multiset.prod_zero⟩

/-- ★ **Leg U's depth-`0` instance in SOURCE currency, proved outright**: at `k = 0`
the block and its transform are both the constant `1` with empty factor multisets. -/
theorem unramifiedLegSourceAt_zero : UnramifiedLegSourceAt 0 := by
  intro O _ _ _ _ _ π hπ φ hφ _ _ g hg hdeg hcell
  have hg1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp (by omega)
  subst hg1
  have hdevT : devT φ 0 (1 : Polynomial O) = 1 := by
    have h1 : dev φ (1 : Polynomial O) 0 = 1 := by
      show (1 : Polynomial O) %ₘ φ = 1
      refine (Polynomial.modByMonic_eq_self_iff hφ.monic).mpr ?_
      rw [Polynomial.degree_one]
      exact Polynomial.natDegree_pos_iff_degree_pos.mp hφ.pos
    rw [devT, Finset.range_one, Finset.sum_singleton, h1, map_one, pow_zero, mul_one,
      Polynomial.C_1]
  rw [hdevT, monicFactors_one, monicFactors_one]
  exact Multiset.Rel.zero

end Teeth

end Uniformity.Density.I10CitePkgF

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}`
on EVERY line: the package is staged, never asserted; no cite occurs in this file. -/

section AxCheck
#print axioms Uniformity.Density.I10CitePkgF.HasClassicalType
#print axioms Uniformity.Density.I10CitePkgF.hasResidueDegree_of_hasClassicalType
#print axioms Uniformity.Density.I10CitePkgF.inertiaDegOf_eq_of_hasClassicalType
#print axioms Uniformity.Density.I10CitePkgF.ramIndexOf_eq_of_hasClassicalType
#print axioms Uniformity.Density.I10CitePkgF.efPair_eq_of_hasClassicalType
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_unique
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_of_closure
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_of_isDVR
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_iff_of_closure
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_eisKey
#print axioms Uniformity.Density.I10CitePkgF.hasClassicalType_of_irreducible_map
#print axioms Uniformity.Density.I10CitePkgF.FactorCorrespondenceSourceAt
#print axioms Uniformity.Density.I10CitePkgF.EisensteinLegSourceStatement
#print axioms Uniformity.Density.I10CitePkgF.UnramifiedLegSourceAt
#print axioms Uniformity.Density.I10CitePkgF.UnramifiedLegSourceStatement
#print axioms Uniformity.Density.I10CitePkgF.PureFaceResidualSourceStatement
#print axioms Uniformity.Density.I10CitePkgF.FGMNCitePackageF
#print axioms Uniformity.Density.I10CitePkgF.factorCorrespondenceAt_of_sourceAt
#print axioms Uniformity.Density.I10CitePkgF.eisensteinLeg_of_source
#print axioms Uniformity.Density.I10CitePkgF.unramifiedLegAt_of_sourceAt
#print axioms Uniformity.Density.I10CitePkgF.unramifiedLeg_of_source
#print axioms Uniformity.Density.I10CitePkgF.pureFaceResidualLeg_of_source
#print axioms Uniformity.Density.I10CitePkgF.fgmn_package_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.factorCorrespondence_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.deepWildTypeScaling_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.cellTypeScaling_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.transport_decidedAt_iff_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.cellTypeScalingAt_two_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.unram_typeScaling_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.tower_typeScaling_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.decidedAt_of_squarefree_residual_of_packageF
#print axioms Uniformity.Density.I10CitePkgF.unramifiedLegSourceAt_zero
end AxCheck
