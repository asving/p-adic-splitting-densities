/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG48
import Uniformity.ChapI.IFCG64
import Uniformity.ChapI.IFCG37
import Uniformity.ChapI.IFCG29

/-!
# Uniformity.ChapI.I10CitePkg — UNIT CP2: the CONSOLIDATED FGMN cite package
(ONE signing surface for every OM-tower pointwise step)

Three units hit the same literature wall from different sides: CTS/CTS2 staged the
Eisenstein-leg factor matching (`IFCG48.FactorCorrespondenceAt`, REVIEW_QUEUE row 9);
MFL found the frame laws need the UNRAMIFIED tower leg (`(e, f) ↦ (e, d·f)` matching
over `AdjoinRoot φ`) and refused to invent its hypothesis vector
(`runs/wave-c/verdict_MFL.md`, THE HONEST FINDING (2)); CN2 left the `e' < m` pure-face
TYPE PIN open (`runs/wave-c/verdict_CN2.md` §7, remainder item 2).  This file states the
minimal Prop family covering all three — hypothesis vectors READ OFF THE SOURCE (both
repo PDFs print-read by this unit, quotes below) — and proves the Lean-core REDUCTIONS
from the consolidated surface to every consumer.  **Nothing here is asserted**: no
axiom is declared; the owner signs ONE statement (`FGMNCitePackage`) or its legs.

## THE PROPOSED GATE-(b) CITE — consolidated faithfulness DRAFT (stated, NOT asserted)

**Proposed statement:** `axiom …fgmn_cite_package : FGMNCitePackage` (§1) — the
conjunction of the three legs.  Signing the package = signing the three legs at once;
each leg is also a standalone named Prop should the owner prefer to sign a subset.

**Source (print-read 2026-08-31 against the repo PDFs):** FGMN — J. Fernández,
J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane valuations*, J. Algebra 427
(2015) 30–75 (repo PDF `docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`) —
**Theorem 6.2, Theorem 6.4, Corollary 6.6** (§6.1, "Prime polynomials and inductive
valuations"); companion (same statements in MacLane–Vaquié currency, Henselian case):
AGNPRW — Alberich-Carramiñana, Guàrdia, Nart, Poteaux, Roé, Weimann, *Polynomial
factorization over Henselian fields*, Found. Comput. Math. (2024), Thm 2.11 + Thm 4.17
(repo PDF `docs/references/s10208-024-09646-x.pdf`; already the source of the row-1
cite `agnprw_termination`).  Verbatim quotes (FGMN, author PDF):

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
Hensel's lemma".  All three legs below are instances of Thm 6.4's dissection at an
order-1 base valuation, with the per-factor `(e, f)` reads supplied by Thm 6.2 +
Cor 6.6: the totally ramified step `e(φ) = e_ν, f = 1` for the Eisenstein leg, the
unramified step `e = 1, f(φ) = deg φ̄` for the key-lift leg, and the residual-indexed
block dissection with the `ord_L = 1` irreducibility clause for the pure-face leg.)

**Dictionary (corpus ↔ source), extending IFCG48's and C66b's standing dictionaries:**
* Leg E (`FactorCorrespondenceAt`, IFCG48 §5 — RE-EXPORTED here, byte-identical
  consumer): µ = the order-1 valuation attached to the slope-`1/e'` side at the key
  `x`; φ = `eisKey π w e'` (Eisenstein, `e(K'/K) = e'`, `f = 1`); the full-span
  lattice + deep-box hypotheses ↔ `g` concentrated on `φ`'s branch with residual a
  power of the maximal ideal `R(φ)` (Thm 6.2(2)); conclusion ↔ Thm 6.4's dissection
  read in transform currency over `O' = O[x]/(φ)`.
* Leg U (`UnramifiedLegAt`, NEW): µ = the Gauss valuation µ₀; φ = an order-1 key lift
  (`IsKey φ`: monic, `φ̄` irreducible of degree `d` — FGMN's key polynomials of the
  depth-0 valuation); the digit hypothesis `π ∣ mk (dev φ g t)`, `t < k` ↔
  `ḡ = φ̄^k`, i.e. `g ∼_{µ₀} φ^k` (Thm 6.2(2): `g` concentrated on `φ`'s branch);
  conclusion ↔ Thm 6.4's dissection at the unramified step, per matched factor pair
  `e(L/K) = e(L/K')` and `f(L/K) = d·f(L/K')` (Cor 6.6: `F_φ = F_{q^d} ↪ F_F`).
* Leg R (`PureFaceResidualLegStatement`, NEW): µ = µ₀, φ = `x`, `g` = any monic lift of
  a class `c` whose polygon is one-sided on the visible face of slope `−h/e'` attained
  at `0` and `m` (the corpus's class-level well-definedness vector, CN2 §2–§4:
  visibility makes every lift x-pure and pins the true polygon); `R_{µ_ν}(g)` ↔
  `classResidualPoly π c h e'` (B.29's side residual at the class, IFCG35), read over
  `ResidueField O` through `resFieldXEquiv.symm` (B.59a); the `Squarefree` hypothesis ↔
  "`ord_L(R_{µ_ν}(g)) = 1` for every `L`" (Thm 6.4's irreducibility clause, imposed at
  every block); conclusion ↔ Thm 6.4's degree formula
  `deg g_{ν,L} = e' · 1 · deg L · 1` + irreducibility + the `(e, f)` read
  `(e, f) = (e', deg L)` (Cor 6.6(1)/(2) at the block's key: `e' ∣ e`, `deg L ∣ f`,
  pinned to equality by `e·f = deg`).

**Scope caveats (the signing read must adjudicate; A–B inherited verbatim from
IFCG48's staged draft, C–D new to this consolidation):**
1. *Caveat A (order vs. field / gcd read).*  All three legs' `(e, f)` currencies are
   the ORDERS' gcd reads (`inertiaDegOf` = gcd of `addVal ∘ norm` over `O[x]/(h)`),
   not field invariants; the classical `f` equalities imply the gcd equalities only
   through the reading "`inertiaDegOf` = the true residue degree" (any order with
   fraction field `L` has norm-valuation gcd exactly `f`).  Not formalized; part of
   the trusted surface (IFCG48 caveat 1, verbatim).
2. *Caveat B (multiplicity / inseparability).*  Legs E and U match factors WITH
   multiplicity over ALL monic `g` in their cells — including inseparable /
   repeated-factor `g` (`devT` is not multiplicative).  The classical sources state
   the correspondence for separable (often squarefree) `g`.  The signing read must
   confirm the cells exclude/handle this fringe or add a separability hypothesis
   (statement-shape decision at the owner gate; IFCG48 caveat 2, verbatim).  For leg R
   the `Squarefree` residual hypothesis excludes the repeated-block fringe at the
   residual level — the leg R statement is therefore NOT exposed to the `ord ≥ 2`
   fringe, but the inseparable-`g` reading of caveat B still applies to it.
3. *Caveat C (transform aggregation — legs E and U).*  Thm 6.4's conclusion is indexed
   by maximal ideals `L` of `∆(µ_ν)`; the corpus conclusion is in TRANSFORM currency
   (`monicFactors (devT φ k g)` over `O' = O[x]/(φ)`).  The identification of the
   `O'`-factorization of the transform with the `(ν, L)`-indexed blocks and their
   recursion is part of the trusted dictionary (FGMN §5's residual ideals + §6's
   iterated key extension; the standing C66b dictionary; AGNPRW Thm 4.17 is the same
   aggregation in Henselian currency).  This caveat is why the legs are cites and not
   theorems.
4. *Caveat D (leg R residual normalization).*  FGMN's `R_{µ_ν}` is fixed only up to
   slot-wise homogeneous-unit rescalings (the paper's own normalization, Cor 4.9(3));
   the corpus's `classResidualPoly` is one concrete choice (B.29 at the x-frame).
   Different choices move the residual's ROOTS but preserve `Squarefree`-ness and the
   DEGREE multiset of the monic irreducible factors — and leg R's conclusion consumes
   only `ψ.natDegree`, so the statement is normalization-robust.  (Recorded because
   the A-C.24″ saga showed twist conventions are load-bearing at order 2; at this
   order-1 x-frame surface only twist-insensitive reads are consumed.)
5. *Caveat E (sufficiency only).*  Each leg asserts its correspondence FOR the stated
   cell/face hypotheses; no converse, no exhaustiveness over cells is claimed
   (IFCG48 caveat 3, extended to all legs).

## Map

* **§1** the three legs + `FGMNCitePackage` (stated, NOT asserted).
* **§2** leg E reductions: every IFCG48 consumer re-fired from the package
  (`factorCorrespondence_of_package` → `deepWildTypeScaling_of_package`,
  `cellTypeScaling_of_package`, `transport_decidedAt_iff_of_package`,
  `cellTypeScalingAt_two_of_package`).
* **§3** leg U reductions: `typeOf_eq_unramScaleType_of_rel` (the Lean-core multiset
  reduction — the `(e, f) ↦ (e, d·f)` bookkeeping is machine-checked, mirroring
  IFCG48 §4) + `unram_typeScaling_of_package` (MFL's named missing pointwise law) +
  ★ `tower_typeScaling_of_package` (the mixed-tower composite in `towerScaleType`
  currency — legs U and E composed through `scaleType_unramScaleType_comm`; exactly
  the `(1, d)`/`(h, d)` frame laws' missing pointwise step, per verdict_MFL's
  consumption note).
* **§4** leg R reduction: `decidedAt_of_squarefree_residual_of_package` — the census
  DECISION-LEG socket: at a spanning visible pure face with squarefree residual the
  CLASS is `DecidedAt` with the residual-indexed type
  `⟨factors.map (fun ψ => (e', deg ψ))⟩` (class data: `classResidualPoly` is
  lift-independent).  CN2's `e' = m` criterion and IFCG37's irreducible-residual leaf
  are the landed `deg-1` and one-factor instances of this shape.
* **§5** vacuity/consistency teeth: `unramifiedLegAt_zero` (the `k = 0` instance of
  leg U, proved outright) and `pureFaceResidualLeg_irr_instance` (leg R's conclusion
  PROVED at irreducible residual from the landed `decidedAt_of_spanning_irr` — the
  Rel currency validated against the landed law, no cite).

Every declaration in this file is PURE LEAN CORE (`#print axioms` footer): the package
is staged, never asserted; consumers take it as an explicit hypothesis until signed.

## Honest scope

Signing the package closes the LITERATURE content of: the census master's `hFC`
premise (`IFCG62.decidedSliceAt_all_of_MASTER_MIXED`, verbatim leg E), the unramified
pointwise step of the mixed-frame decision legs (MFL remainder item 2 and the
unramified half of item 3, through `unram_typeScaling_of_package` +
`tower_typeScaling_of_package`), and the squarefree-residual pure-face type pin
(CN2 remainder item 2's squarefree case, through
`decidedAt_of_squarefree_residual_of_package`).

**It does NOT cover (flagged loudly):**
* **the slope-`h ≥ 2` deep-primary recentring step** (MFL remainder item 1 and the
  ramified half of item 3): leg E's key is `eisKey π w e' = X^{e'} + C(w·π)` —
  slope `1/e'` ONLY — and leg R is silent on the `(X − y)^k`-primary residual of the
  `(h, 1)` slope cells (`Squarefree` fails at `k ≥ 2`).  The general-slope analogue
  `X^{e'} − w·π^h` generates a NON-DVR order at `h ≥ 2` (its value semigroup is
  `⟨e', h⟩/e' ≠ ℕ`), so the transform-currency statement cannot even be WRITTEN
  against the landed carriers; MFL's recorded route is the Bézout Eisenstein ring
  (`γ^{e'} = z^s·π`, `s·h ≡ 1 mod e'`).  A future unit must land that carrier before
  the slope-`h` leg can join the package — deliberately NOT smuggled in here.
* the `ZcURLim` census assemblies (face/centre partition + squeezes — Lean-core
  work, separate units; MFL's consumption notes),
* the convolution-defect and leaf-subface premises of the master (different genre),
* the general-position `FracFaceForcesRamStatement` (CN2 §7 remainder item 1 — the
  face-factorization Hensel-grade input; leg R covers only the SPANNING face,
  `sideMin = 0`, `sideMax = m`, which is the census's live case).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.I10CitePkg

open IsLocalRing Polynomial
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG39 (devT devT_coeff devT_monic eisKey)
open Uniformity.Density.IFCG29 (irreducible_algebraMap_adjoinRoot)
open Uniformity.Density.IFCG22 (NPAttains NPVisibleAt)
open Uniformity.Density.IFCG35 (classResidualPoly classResidualPoly_eq)
open Uniformity.Density.IFCG47 (scaleType scaleType_data scaleType_degree
  CellTypeScalingAt CellTypeScaling transport_decidedAt_iff)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt DeepWildTypeScalingStatement
  deepWildTypeScaling_of_correspondence cellTypeScaling_of_cite
  transport_decidedAt_iff_of_correspondence cellTypeScalingAt_two_of_correspondence)
open Uniformity.Density.IFCG64 (unramScaleType unramScaleType_data towerScaleType
  scaleType_unramScaleType_comm)

attribute [local instance] Classical.propDecidable

/-! ## §1 — THE CONSOLIDATED CITE SURFACE (stated, NOT asserted) -/

section CiteSurface

/-- **Leg E (Eisenstein / deep-wild)** — byte-identical to the surface CTS2 staged and
row 9 recommended: the OM factor correspondence across the totally ramified step, at
every census depth.  See `IFCG48.FactorCorrespondenceAt` for the hypothesis vector and
IFCG48's module docstring for its staged faithfulness draft (superseded by this
file's consolidated draft).  Source: FGMN Thm 6.2 + Thm 6.4 at the Eisenstein key. -/
def EisensteinLegStatement : Prop := ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D

/-- **Leg U (unramified) at depth `k`** — the pointwise step MFL named and declined to
invent (`verdict_MFL.md`, THE HONEST FINDING (2)), its hypothesis vector now READ OFF
FGMN Thm 6.2(2) + Thm 6.4 + Cor 6.6 at an order-1 key lift `φ` (`IsKey φ`: monic,
irreducible reduction `φ̄` of degree `d`):

* the cell hypothesis `∀ t < k, π ∣ mk (dev φ g t)` says exactly `ḡ = φ̄^k`
  (each digit has degree `< d`, so vanishing mod `(π)·O'` = vanishing mod `π`) —
  Thm 6.2(2)'s "`g ∼_µ φ^k`, `R(g)` a power of the maximal ideal `R(φ)`" at the
  Gauss valuation;
* the conclusion is Thm 6.4's dissection in transform currency (caveat C): the monic
  irreducible `O`-factors of `g` are matched, as a multiset relation, with the monic
  irreducible `O'`-factors of the transform `devT φ k g`, each matched pair `(h, H)`
  carrying the unramified tower reads `f(L/K) = d·f(L/K')` (Cor 6.6(2): the residue
  embedding `F_φ = F_{q^d} ↪ F_F`) and `deg h = d · deg H` — the `e`-leg
  `e(L/K) = e(L/K')` is then the machine-checked bookkeeping
  (`typeOf_eq_unramScaleType_of_rel`, §3).

The source poses no restriction on `d ≥ 1` and none is imposed here; the corpus
consumers instantiate at `d ≥ 2`.  No slope/lattice hypothesis appears: the unramified
step sits at slope `0`, and the transform carries whatever polygon `g` has into `O'`
(the recursion is the transform's own factorization, per Thm 6.4's iteration). -/
def UnramifiedLegAt (k : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π : O, Irreducible π →
  ∀ φ : Polynomial O, IsKey φ →
  ∀ [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)],
  ∀ g : Polynomial O, g.Monic → g.natDegree = φ.natDegree * k →
    (∀ t, t < k → algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) →
    Multiset.Rel
      (fun h H => inertiaDegOf h = φ.natDegree * inertiaDegOf H
        ∧ h.natDegree = φ.natDegree * H.natDegree)
      (monicFactors g) (monicFactors (devT φ k g))

/-- Leg U quantified over every depth (the signing surface's second conjunct). -/
def UnramifiedLegStatement : Prop := ∀ k : ℕ, UnramifiedLegAt k

/-- **Leg R (the pure-face residual dissection)** — CN2's `e' < m` TYPE PIN
(`verdict_CN2.md` §7, remainder item 2), its hypothesis vector READ OFF FGMN Thm 6.4
at `µ = µ₀`, `φ = x`, specialized to a polygon one-sided on the spanning face:

* the face hypotheses (`NPAttains … 0`, `NPAttains … m`, `NPVisibleAt`) are the
  corpus's class-level well-definedness vector (CN2 §2–§4: strict visibility makes
  every lift x-pure with the class polygon as its true polygon) — the source-side
  content is "`N_{µ₀,x}(g)` is one-sided of slope `−h/e'` from `(0, hm/e')` to
  `(m, 0)`";
* `Squarefree` of the class residual (read over `ResidueField O` through B.59a's
  `resFieldXEquiv.symm` — caveat D: only normalization-robust data is consumed) is
  Thm 6.4's `ord_L(R_{µ_ν}(g)) = 1` clause imposed at every block;
* the conclusion is Thm 6.4's dissection + irreducibility clause + the per-block
  `(e, f)` pin: the monic irreducible factors of EVERY lift are matched, as a multiset
  relation, with the monic irreducible factors of the class residual, each matched
  pair `(g', ψ)` carrying `f(g') = deg ψ` (Cor 6.6(2)) and `deg g' = e' · deg ψ`
  (Thm 6.4's degree formula at `ord_L = 1`, `deg φ = 1`, `e_ν = e'`) — whence
  `e(g') = e'` by bookkeeping (§4).

The source poses no restriction on the slope; `0 < h`, `0 < e'`, coprimality are the
face's shape data (at `e' = 1` this is the integer-slope/Hensel instance, included
because the source includes it).  CN2's `decidedAt_of_eisenstein_face` (`e' = m`) and
IFCG37's `decidedAt_of_spanning_irr` (irreducible residual) are landed instances of
this shape — the latter is re-derived as the tooth `pureFaceResidualLeg_irr_instance`
(§5), validating the Rel currency against the landed law. -/
def PureFaceResidualLegStatement : Prop :=
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
      (fun g' ψ => inertiaDegOf g' = ψ.natDegree ∧ g'.natDegree = e' * ψ.natDegree)
      (monicFactors (monicPoly a))
      (UniqueFactorizationMonoid.normalizedFactors
        ((classResidualPoly π c h e').map
          ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
            resField (X : Polynomial O) →+* ResidueField O)))

/-- **THE CONSOLIDATED CITE PACKAGE — stated, NOT asserted** (the OM-5 /
`BBox1CiteStatement` staging pattern): the three OM-tower pointwise steps, one signing
decision.  A future owner-signed `axiom … : FGMNCitePackage` makes every consumer in
§2–§4 fire unconditionally, with the axiom name visible in every downstream
`#print axioms`.  Until then, every consumer takes the package (or a single leg) as an
explicit hypothesis. -/
def FGMNCitePackage : Prop :=
  EisensteinLegStatement ∧ UnramifiedLegStatement ∧ PureFaceResidualLegStatement

end CiteSurface

/-! ## §2 — LEG E REDUCTIONS: the package re-fires every IFCG48 consumer -/

section LegE

/-- The package's first projection is byte-identical to row 9's recommended surface. -/
theorem factorCorrespondence_of_package (hpkg : FGMNCitePackage) :
    ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D := hpkg.1

/-- The package fires IFCG48 §1's raw surface. -/
theorem deepWildTypeScaling_of_package (hpkg : FGMNCitePackage) :
    DeepWildTypeScalingStatement :=
  deepWildTypeScaling_of_correspondence hpkg.1

/-- The package fires the COMPLETE pointwise scaling law (every depth, composing with
the machine-checked `D = 0, 1` witnesses — IFCG48 §0/§1, DTR's IFCG47). -/
theorem cellTypeScaling_of_package (hpkg : FGMNCitePackage) : CellTypeScaling :=
  cellTypeScaling_of_cite (deepWildTypeScaling_of_package hpkg)

open Uniformity.Density.IFCG39 (eisKey)
open Uniformity.Density.IFCG43 (cellTransport)
open Uniformity.Density.IFCG44 (alphaBox)
open Uniformity.Density.IFCG35 (MinFaceAt)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π w : O} {e' : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- ★★ **The transport socket from the package** — IFCG48 §6's decision-transport iff
(DTR's assembly entry point on the composite-mass census front) fires from the
consolidated surface. -/
theorem transport_decidedAt_iff_of_package (hpkg : FGMNCitePackage)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {D N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  transport_decidedAt_iff_of_correspondence hpkg.1 hπ hw he' hDN hF hbox σ'

/-- The `D = 2` supply for ER4's dd terms, from the package. -/
theorem cellTypeScalingAt_two_of_package (hpkg : FGMNCitePackage) :
    CellTypeScalingAt 2 :=
  cellTypeScalingAt_two_of_correspondence hpkg.1

end LegE

/-! ## §3 — LEG U REDUCTIONS: the `(e, f) ↦ (e, d·f)` bookkeeping machine-checked,
MFL's pointwise law, and the mixed-tower composite -/

section LegU

/-- A monic irreducible has positive degree (kit; IFCG48 §4's private replica). -/
private theorem natDegree_pos_of_monic_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {g : Polynomial R} (hg : g.Monic) (hirr : Irreducible g) : 0 < g.natDegree := by
  by_contra hcon
  have h1 : g = 1 := (Polynomial.Monic.natDegree_eq_zero hg).mp (by omega)
  rw [h1] at hirr
  exact hirr.not_isUnit isUnit_one

/-- ★★ **The per-factor `(e, f) ↦ (e, d·f)` scaling, bookkeeping form** (the leg U
analogue of IFCG48's `efPair_eq_scale`): the `d`-scaled inertia gcd (f-leg, Cor 6.6(2))
+ `d`-scaled degree force `efPair h = (e_H, d·f_H)` — exactly `unramScaleType`'s member
map, with the `e`-invariance `e(L/K) = e(L/K')` emerging as pure arithmetic.
Ring-generic in BOTH rings (MFL repair-log lesson 6). -/
theorem efPair_eq_unramScale {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {O' : Type*} [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] {d : ℕ} (hd : 0 < d)
    {H : Polynomial O'} {h : Polynomial O}
    (hf : inertiaDegOf h = d * inertiaDegOf H)
    (hdeg : h.natDegree = d * H.natDegree) :
    efPair h = ((efPair H).1, d * (efPair H).2) := by
  simp only [efPair, ramIndexOf]
  rw [hf, hdeg, Nat.mul_div_mul_left _ _ hd]

/-- ★★★ **THE MULTISET REDUCTION, leg U** (mirroring IFCG48 §4's
`typeOf_eq_scaleType_of_rel`): the unramified factor correspondence — matched factors
with `d`-scaled inertia gcd and `d`-scaled degree — fires the full type read
`typeOf g = unramScaleType d (typeOf G)`, for ANY monic `g` over `O` and monic `G`
over any second DVR.  Every `(e, f)` read downstream of leg U is machine-checked
here; ONLY the factor matching is trusted. -/
theorem typeOf_eq_unramScaleType_of_rel {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {O' : Type*} [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] {d : ℕ} (hd : 0 < d)
    {g : Polynomial O} {G : Polynomial O'}
    (hrel : Multiset.Rel
      (fun h H => inertiaDegOf h = d * inertiaDegOf H
        ∧ h.natDegree = d * H.natDegree)
      (monicFactors g) (monicFactors G)) :
    typeOf g = unramScaleType d (typeOf G) := by
  apply FactorizationType.ext
  rw [unramScaleType_data, typeOf_data, typeOf_data, Multiset.map_map]
  refine Multiset.rel_eq.mp (Multiset.rel_map.mpr (hrel.mono ?_))
  intro h hhmem H hHmem hr
  obtain ⟨hf, hdeg⟩ := hr
  show efPair h = ((efPair H).1, d * (efPair H).2)
  exact efPair_eq_unramScale hd hf hdeg

/-- ★★★ **MFL's named missing pointwise law, from the package**: across the unramified
tower step `O → O' = AdjoinRoot φ` (`IsKey φ`, `d = deg φ`), a `φ̄`-primary monic block
of degree `d·k` has `typeOf g = unramScaleType d (typeOf (devT φ k g))` — the exact
type side MFL prescribed (`towerScaleType`'s first factor; `verdict_MFL.md`,
consumption note for the `(1, d)` law unit).  The instances on `O'` are Prop-class
binders; consumers discharge them by IFCG27's cascade
(`keyIsDomain`/`adjoinRoot_isDVR`). -/
theorem unram_typeScaling_of_package (hpkg : FGMNCitePackage)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
    {k : ℕ} {g : Polynomial O} (hg : g.Monic) (hdeg : g.natDegree = φ.natDegree * k)
    (hcell : ∀ t, t < k → algebraMap O (AdjoinRoot φ) π ∣ AdjoinRoot.mk φ (dev φ g t)) :
    typeOf g = unramScaleType φ.natDegree (typeOf (devT φ k g)) := by
  exact typeOf_eq_unramScaleType_of_rel hφ.pos
    (hpkg.2.1 k O π hπ φ hφ g hg hdeg hcell)

/-- ★★★ **THE MIXED-TOWER COMPOSITE, from the package** — the `(1, d)`/`(h, d)` frame
laws' missing pointwise step in exactly the `towerScaleType` currency MFL prescribed
(`verdict_MFL.md`, consumption note): across the full mixed tower
`O → O₁ = AdjoinRoot φ → O₂ = AdjoinRoot (eisKey π₁ w₁ e')` (unramified stage of
degree `d = deg φ`, then Eisenstein stage of degree `e'` over `O₁`, uniformizer
`π₁ = algebraMap π` — `e(K₁/K) = 1`), a `φ̄`-primary block of degree `d·e'·D` whose
first transform sits in the depth-`D` Eisenstein cell over `O₁` has

  `typeOf g = towerScaleType e' d (typeOf G₂)`,  `G₂` = the second transform.

Leg U crosses the unramified stage, leg E (through `cellTypeScaling_of_package`, so
the `D = 0, 1` witnesses fire without the cite) crosses the ramified stage AT `O₁`,
and IFCG64's `scaleType_unramScaleType_comm` composes the two scale maps.  The `O₁`
lattice/box hypotheses are the named Prop's own cell shapes at `O₁`, byte-mirrored
from `FactorCorrespondenceAt`; `π₁`'s irreducibility is derived
(`irreducible_algebraMap_adjoinRoot` — the unramified stage preserves uniformizers). -/
theorem tower_typeScaling_of_package (hpkg : FGMNCitePackage)
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
          (devT φ (e' * D) g))) := by
  have hstep1 : typeOf g = unramScaleType φ.natDegree (typeOf (devT φ (e' * D) g)) :=
    unram_typeScaling_of_package hpkg hπ hφ hg hdeg hcell
  obtain ⟨hG₁m, hG₁deg⟩ := devT_monic hφ.monic hφ.pos hg hdeg
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  have hstep2 : typeOf (devT φ (e' * D) g)
      = scaleType e' (typeOf (devT (eisKey (algebraMap O (AdjoinRoot φ) π) w₁ e') D
          (devT φ (e' * D) g))) :=
    cellTypeScaling_of_package hpkg D (AdjoinRoot φ)
      (algebraMap O (AdjoinRoot φ) π) w₁ hπ₁ hw₁ e' he'
      (devT φ (e' * D) g) hG₁m hG₁deg hlat hbox
  rw [hstep1, hstep2]
  exact (scaleType_unramScaleType_comm e' φ.natDegree _).symm

end LegU

/-! ## §4 — LEG R REDUCTION: the census DECISION-LEG socket -/

section LegR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **The pure-face decision socket, from the package**: at a spanning visible
pure face of slope `h/e'` with SQUAREFREE class residual, the CLASS is decided with
the residual-indexed type `⟨factors.map (fun ψ => (e', deg ψ))⟩` — a genuine
`DecidedAt` because `classResidualPoly` is class data (lift-independent, IFCG35).
This is CN2 §7 remainder item 2's TYPE PIN: CN2's landed
`decidedAt_of_eisenstein_face` is the `e' = m` (degree-1 residual) instance of this
shape, IFCG37's `decidedAt_of_spanning_irr` the one-factor instance (§5's tooth).
The `(e, f)` reads (`e = e'` from `deg = e'·deg ψ` and `f = deg ψ`) are machine-checked
here; only leg R's factor matching is trusted. -/
theorem decidedAt_of_squarefree_residual_of_package (hpkg : FGMNCitePackage)
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
        (fun ψ => (e', ψ.natDegree))⟩ N c := by
  intro a ha
  have hrel := hpkg.2.2 O π hπ m N h e' hm hh he' hcop c h0 hAm hvis hsf a ha
  apply FactorizationType.ext
  rw [typeOf_data]
  refine Multiset.rel_eq.mp (Multiset.rel_map.mpr (hrel.mono ?_))
  intro g' hg'mem ψ hψmem hr
  obtain ⟨hf, hdeg⟩ := hr
  have hψirr : Irreducible ψ :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor ψ hψmem
  have hψ0 : 0 < ψ.natDegree := hψirr.natDegree_pos
  show efPair g' = (e', ψ.natDegree)
  simp only [efPair, ramIndexOf]
  rw [hf, hdeg, Nat.mul_div_cancel _ hψ0]

end LegR

/-! ## §5 — VACUITY / CONSISTENCY TEETH -/

section Teeth

/-- The empty factorization of `1` (kit; IFCG48 §0's private replica, ring-generic). -/
private theorem monicFactors_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : monicFactors (1 : Polynomial R) = 0 :=
  monicFactors_eq ⟨fun g hg => absurd hg (Multiset.notMem_zero g), Multiset.prod_zero⟩

/-- ★ **Leg U's depth-`0` instance, proved outright** (the vacuity tooth, mirroring
IFCG48 §0's `cellTypeScalingAt_zero`): at `k = 0` the block is the constant `1`, the
transform is the constant `1`, and both factor multisets are empty — the statement
shape is non-vacuously satisfiable-and-true in the trivial regime. -/
theorem unramifiedLegAt_zero : UnramifiedLegAt 0 := by
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

open Uniformity.Density.Induction (levelZeroStratum)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG37 (decidedAt_of_spanning_irr)

/-- `X` is an order-1 key (kit; IFCG23/IFCG64's private replica). -/
private theorem isKey_X {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- `sideSet` membership unfolds to the `OnSide` predicate (kit; IFCG51/IFCG64's
private replica). -/
private theorem mem_sideSet_iff' {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · intro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩
    exact this

/-- Kit: at a SPANNING visible face (attained at `0` and `m`) the class residual has
`natDegree = m / e'` — the residual-degree read of Thm 6.4's `deg L` bookkeeping
(the spanning instance of IFCG64's `slope_lattice_pins` degree pin, without the
`h < e'` restriction of `MinFaceAt`). -/
private theorem residual_natDegree_of_spanning {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    (hm : 0 < m) (he' : 0 < e') (hcop : Nat.Coprime h e')
    {c : Coeff O m N} (h0 : NPAttains c h e' 0) (hAm : NPAttains c h e' m)
    (hvis : NPVisibleAt c h e') {a : Fin m → O} (ha : proj O m N a = c) :
    (classResidualPoly π c h e').natDegree = m / e' := by
  obtain ⟨hOn0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis h0 ha
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAm ha
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have h0mem : 0 ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := ⟨0, h0mem⟩
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) = ((w : ℕ) : ℕ∞) :=
    hw.symm
  have hcrp : classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne w :=
    classResidualPoly_eq hπ he' hvis ha hne hw'
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hw'
  have hmin : sideMin X (monicPoly a) h e' hne = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  rw [hcrp, hnd.1]
  unfold sideDeg
  rw [hmin, hmax, Nat.sub_zero]

/-- ★★ **Leg R's conclusion PROVED at irreducible residual** (the consistency tooth,
NO cite consumed): at a spanning visible pure face over the `X^m` stratum with
IRREDUCIBLE class residual, the leg R multiset relation holds outright — derived from
the LANDED spanning-leaf law (`IFCG37.decidedAt_of_spanning_irr`, itself Lean-core).
This validates leg R's Rel currency against the landed corpus: the landed law's
`⟨{(e', d)}⟩` decision is exactly the singleton instance of leg R's conclusion. -/
theorem pureFaceResidualLeg_irr_instance {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m N h e' d : ℕ}
    (hm : 0 < m) (hh : 0 < h) (he' : 0 < e') (hd : 0 < d) (hcop : Nat.Coprime h e')
    (hmd : m = e' * d)
    {c : Coeff O m N} (hstr : c ∈ levelZeroStratum O m N (Polynomial.X ^ m))
    (h0 : NPAttains c h e' 0) (hAm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    (hirr : Irreducible ((classResidualPoly π c h e').map
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O)))
    {a : Fin m → O} (ha : proj O m N a = c) :
    Multiset.Rel
      (fun g' ψ => inertiaDegOf g' = ψ.natDegree ∧ g'.natDegree = e' * ψ.natDegree)
      (monicFactors (monicPoly a))
      (UniqueFactorizationMonoid.normalizedFactors
        ((classResidualPoly π c h e').map
          ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
            resField (X : Polynomial O) →+* ResidueField O))) := by
  classical
  -- (a) transport the irreducibility through the coefficient iso to the raw carrier
  have hirr' : Irreducible (classResidualPoly π c h e') := by
    refine (MulEquiv.irreducible_iff
      (Polynomial.mapEquiv ((Uniformity.Density.Leaf.resFieldXEquiv O).symm))).mp ?_
    rw [Polynomial.mapEquiv_apply]
    exact hirr
  -- (b) the landed spanning-leaf decision pins the lift's type
  have htype : typeOf (monicPoly a) = ⟨{(e', d)}⟩ :=
    decidedAt_of_spanning_irr hd hπ hm hh he' hcop hmd hstr h0 hAm hvis hirr' a ha
  -- (c) extract the singleton factorization
  have hdata : (monicFactors (monicPoly a)).map efPair = {(e', d)} := by
    have h1 := congrArg FactorizationType.data htype
    rwa [typeOf_data] at h1
  obtain ⟨g', hgf, hef⟩ := Multiset.map_eq_singleton.mp hdata
  have hprod : (monicFactors (monicPoly a)).prod = monicPoly a :=
    (monicFactors_spec (monicPoly_monic a)).2
  rw [hgf, Multiset.prod_singleton] at hprod
  -- (d) the residual degree is `d`
  have hQdeg0 : (classResidualPoly π c h e').natDegree = m / e' :=
    residual_natDegree_of_spanning hπ hm he' hcop h0 hAm hvis ha
  have hmde : m / e' = d := by
    rw [hmd]
    exact Nat.mul_div_cancel_left d he'
  have hinj : Function.Injective
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O) :=
    (Uniformity.Density.Leaf.resFieldXEquiv O).symm.injective
  have hQdeg : ((classResidualPoly π c h e').map
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O)).natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective hinj, hQdeg0, hmde]
  -- (e) the normalized factorization of the irreducible residual is a singleton
  rw [hgf, UniqueFactorizationMonoid.normalizedFactors_irreducible hirr]
  have hnQdeg : (normalize ((classResidualPoly π c h e').map
      ((Uniformity.Density.Leaf.resFieldXEquiv O).symm :
        resField (X : Polynomial O) →+* ResidueField O))).natDegree = d := by
    have h2 : ∀ q : Polynomial (ResidueField O), (normalize q).natDegree = q.natDegree := by
      intro q
      simp only [Polynomial.natDegree]
      rw [Polynomial.degree_normalize]
    rw [h2, hQdeg]
  -- (f) assemble the singleton relation
  refine Multiset.Rel.cons ⟨?_, ?_⟩ Multiset.Rel.zero
  · have h2 : inertiaDegOf g' = d := congrArg Prod.snd hef
    rw [h2, hnQdeg]
  · rw [hprod, monicPoly_natDegree, hnQdeg, hmd]

end Teeth

end Uniformity.Density.I10CitePkg

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}`
on EVERY line: the package is staged, never asserted; no cite occurs in this file. -/

section AxCheck
#print axioms Uniformity.Density.I10CitePkg.EisensteinLegStatement
#print axioms Uniformity.Density.I10CitePkg.UnramifiedLegAt
#print axioms Uniformity.Density.I10CitePkg.UnramifiedLegStatement
#print axioms Uniformity.Density.I10CitePkg.PureFaceResidualLegStatement
#print axioms Uniformity.Density.I10CitePkg.FGMNCitePackage
#print axioms Uniformity.Density.I10CitePkg.factorCorrespondence_of_package
#print axioms Uniformity.Density.I10CitePkg.deepWildTypeScaling_of_package
#print axioms Uniformity.Density.I10CitePkg.cellTypeScaling_of_package
#print axioms Uniformity.Density.I10CitePkg.transport_decidedAt_iff_of_package
#print axioms Uniformity.Density.I10CitePkg.cellTypeScalingAt_two_of_package
#print axioms Uniformity.Density.I10CitePkg.efPair_eq_unramScale
#print axioms Uniformity.Density.I10CitePkg.typeOf_eq_unramScaleType_of_rel
#print axioms Uniformity.Density.I10CitePkg.unram_typeScaling_of_package
#print axioms Uniformity.Density.I10CitePkg.tower_typeScaling_of_package
#print axioms Uniformity.Density.I10CitePkg.decidedAt_of_squarefree_residual_of_package
#print axioms Uniformity.Density.I10CitePkg.unramifiedLegAt_zero
#print axioms Uniformity.Density.I10CitePkg.pureFaceResidualLeg_irr_instance
end AxCheck
