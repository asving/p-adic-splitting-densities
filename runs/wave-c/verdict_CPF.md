# UNIT CPF — VERDICT: THE FGMN CITE PACKAGE RESTATED IN SOURCE CURRENCY (the
theorems as the authors wrote them; the gcd-currency package a Lean-core corollary;
caveat A GONE from the signing ledger) — 2026-08-31

**Re-grounding.** The consolidated FGMN cite package (`I10CitePkg.lean`, unit CP2) staged
three legs whose per-factor `(e, f)` conclusions were the corpus's ORDER-GCD reads
(`inertiaDegOf`), tied to the source's field invariants only by a trusted reading (caveat
A).  Unit CUR then LANDED the currency lemma (`IFCG76`): through any closure realization
(`DVRClosure` = a rank-`deg` free DVR extension receiving the monogenic order,
mathematically the integral closure `O_L`), the gcd read IS the classical residue degree
— Lean-core, no completeness.  Owner direction (2026-08-31, verbatim): "lets import the
theorem statement exactly as the authors intended and prove the currency lemma to
translate into our language."  This unit executes the restatement.

**Deliverable:** `leanfinal/Uniformity/ChapI/I10CitePkgF.lean` — 713 lines, 32 public
declarations (+2 private kit replicas), ZERO sorries, zero errors/warnings;
**32/32 `#print axioms` lines exactly Lean core {propext, Classical.choice, Quot.sound}**
(checked by unique-bracket-set extraction over the whole output: exactly one axiom set
appears).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/I10CitePkgF.lean` (5 increments, EVERY ONE
GREEN FIRST TRY — zero repair rounds in the whole unit); targeted
`lake build Uniformity.ChapI.I10CitePkgF` GREEN (9043 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the sanctioned one-line import
(I10CitePkg → I10CitePkgF → I10RungLift3W).  `docs/REVIEW_QUEUE_2026-08-26.md` row 9
REWRITTEN in place (superseded, not appended).  I10CitePkg.lean, IFCG76.lean,
I10WrapPinned.lean all byte-untouched; no git ops.

## ★★★ THE RESULT — the owner signs the authors' statements

    def FGMNCitePackageF : Prop :=
      EisensteinLegSourceStatement ∧ UnramifiedLegSourceStatement
        ∧ PureFaceResidualSourceStatement

with (all in `Uniformity.Density.I10CitePkgF`) hypothesis vectors BYTE-IDENTICAL to
CP2's gcd legs, and each per-factor conclusion clause restated in the source's ontology
through the new carrier

    def HasClassicalType (g : Polynomial O) (e f : ℕ) : Prop :=
      ∃ D : DVRClosure g,
        (maximalIdeal D.carrier).ramificationIdx' O = e ∧
        (maximalIdeal D.carrier).inertiaDeg' O = f

("the factor HAS a closure realization with classical ramification `e` and residue
degree `f`" — existence INSIDE the statement, per CUR's recommendation; both invariants
carried because the source asserts both, Cor 6.6 + Thm 6.4's degree formula):

* **leg E** (`FactorCorrespondenceSourceAt D`): matched pair `(h, H)` carries
  `∃ eH fH, HasClassicalType H eH fH ∧ HasClassicalType h (e'·eH) fH` — Cor 6.6 across
  the totally ramified step (`e(L/K) = e'·e(L/K')`, `f(L/K) = f(L/K')`) — plus
  `deg h = e'·deg H`;
* **leg U** (`UnramifiedLegSourceAt k`): pair carries
  `∃ eH fH, HasClassicalType H eH fH ∧ HasClassicalType h eH (d·fH)` — Cor 6.6(2)'s
  residue embedding `F_φ = F_{q^d} ↪ F_F` (`e` preserved, `f` scaled by `d`) — plus
  `deg h = d·deg H`;
* **leg R** (`PureFaceResidualSourceStatement`): pair `(g', ψ)` carries
  `HasClassicalType g' e' (deg ψ)` — Thm 6.4's `(e, f) = (e_ν, deg L)` block read —
  plus `deg g' = e'·deg ψ`.

## THE TRANSLATIONS (charge 2 — all Lean-core, the currency lemma consumed per factor)

| theorem | statement |
|---|---|
| `inertiaDegOf_eq_of_hasClassicalType` / `ramIndexOf_eq_of_hasClassicalType` / `efPair_eq_of_hasClassicalType` | the §0 bridges: a source-currency read pins `inertiaDegOf` / `ramIndexOf` / `efPair` (from IFCG76's `inertiaDegOf_eq_inertiaDeg'_of_closure` + `ramIndexOf_eq_ramificationIdx'_of_closure`) |
| `factorCorrespondenceAt_of_sourceAt` | leg E source ⟹ `IFCG48.FactorCorrespondenceAt D` (per pair: `inertiaDegOf h = fH = inertiaDegOf H` by the f-bridge on both floors; factor monicity/irreducibility from `monicFactors_spec`) |
| `unramifiedLegAt_of_sourceAt` | leg U source ⟹ `I10CitePkg.UnramifiedLegAt k` (`inertiaDegOf h = d·fH = d·inertiaDegOf H`) |
| `pureFaceResidualLeg_of_source` | leg R source ⟹ `I10CitePkg.PureFaceResidualLegStatement` (the bridge at `f := deg ψ`) |
| ★★★ `fgmn_package_of_packageF` | **`FGMNCitePackageF → FGMNCitePackage`** — the old signing surface is a COROLLARY; nothing downstream re-wires |

All eight CP2 consumers re-exported from the new package (§3, one-line compositions):
`factorCorrespondence_of_packageF`, `deepWildTypeScaling_of_packageF`,
`cellTypeScaling_of_packageF`, `transport_decidedAt_iff_of_packageF`,
`cellTypeScalingAt_two_of_packageF`, `unram_typeScaling_of_packageF`,
`tower_typeScaling_of_packageF`, `decidedAt_of_squarefree_residual_of_packageF`.

Teeth (§0/§4, Lean-core, no cite): `unramifiedLegSourceAt_zero` (leg U `k = 0`,
outright); `hasClassicalType_of_isDVR` (identity realization on the maximal locus);
`hasClassicalType_eisKey` (leg E's key reads `(e', 1)` — Thm 6.2's totally ramified
read); `hasClassicalType_of_irreducible_map` (leg U's key reads `(1, deg)`);
`hasClassicalType_unique` (the carrier is single-valued — all realizations agree);
`hasClassicalType_iff_of_closure` (the full ⟺ given any realization).

## Why caveat A is GONE (the honesty accounting)

Old ledger: "the `(e, f)` currencies are order gcd reads, tied to field invariants by
the standard any-order-with-fraction-field-`L` reading — trusted, not formalized."
New ledger: the legs STATE the field invariants (`ramificationIdx'`/`inertiaDeg'` of a
`DVRClosure`); the tie to the corpus currency is the machine-checked IFCG76 bridge; the
realization existence inside each conclusion is the source's own standing assertion
(FGMN's `F` has a root `θ ∈ K̄_v` generating `L = K_v(θ)`, whose integer ring `O_L` is a
rank-`deg F` free DVR over the complete base receiving `O_v[x]/(F)` by `x ↦ θ` — Serre,
*Corps Locaux* II §2 Prop. 3, no separability needed; injectivity because monic-`F`
makes the order a full-rank free submodule of `L`).  Nothing was weakened: the source
legs IMPLY the gcd legs (proved), never conversely assumed.

Two structural notes recorded in the docstring (not caveats): (i) separate per-factor
existentials vs. the source's coupled tower reading — no drift, the carrier is
single-valued; (ii) upper-floor completeness (`AdjoinRoot φ`) absent from the binders,
mirroring the gcd legs — every consumer instance is genuinely complete, as is the
source's `O_{v'}`.

Caveats B (inseparable/repeated-factor fringe, legs E/U — separability adjudication at
signing), C (transform currency vs. residual-ideal indexing — the trusted dictionary,
C66b genre), D (leg R normalization-robustness), E (sufficiency only) carried VERBATIM.

## FAITHFULNESS ENTRY DRAFT (for docs/AXIOM_FAITHFULNESS.md — NOT enacted; to be
appended verbatim at signing; supersedes CP2's draft)

> ## `fgmn_cite_packageF` (I10CitePkgF, PROPOSED — not yet declared)
>
> **Ports:** FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015)
> 30–75, DOI 10.1016/j.jalgebra.2014.12.022 — Theorem 6.2 (theorem of the polygon,
> factor level) + Theorem 6.4 (the generalized-Hensel dissection: block factorization,
> degree formula, ord-1 irreducibility clause) + Corollary 6.6 (`e(φ) ∣ e(F)`;
> residue-field embedding `F_φ ↪ F_F`), print-read VERBATIM 2026-08-31 against the
> author-posted PDF (repo copy); quotes in the I10CitePkgF.lean module docstring.
> Companion: AGNPRW FoCM 2024 Thm 2.11 + Thm 4.17 (repo PDF; same source as the signed
> row-1 `agnprw_termination`).  Standing background fact carried INSIDE the statement:
> Serre, *Corps Locaux*, ch. II §2 Prop. 3 (the integral closure of a complete DVR in a
> finite extension is a DVR, finite free of full rank — no separability), entering as
> the existence of the `DVRClosure` realization each conclusion asserts.
> **Faithfulness surface:** three legs, one conjunction (`FGMNCitePackageF`); hypothesis
> vectors identical to the CP2 staging (see that entry's per-leg dictionary, inherited
> wholesale); conclusions are the authors' own per-factor invariants:
> `HasClassicalType h e f` = some closure realization of `O[x]/(h)` has classical
> `(ramificationIdx', inertiaDeg') = (e, f)` — the formal proxy for "`e(F), f(F)` in
> `L = K_v(θ)`" (any realization IS `O_L`; `hasClassicalType_unique` makes the reads
> invariant).  The corpus's gcd currency is DERIVED, never assumed
> (`fgmn_package_of_packageF`, Lean-core, via IFCG76's currency lemma).
> **Caveats requiring adjudication at signing:** (B) legs E/U quantify over
> inseparable/repeated-factor `g` while the classical statements assume separable `g` —
> confirm the cells exclude the fringe or add a separability hypothesis; (C) the corpus
> conclusions are in `devT` transform currency while Thm 6.4 is indexed by residual
> maximal ideals — the identification is the trusted dictionary (C66b genre); (D) leg R
> consumes only normalization-robust residual reads; (E) sufficiency only.  Caveat A of
> the CP2 draft is RESOLVED (machine-checked bridge; no per-equality currency reading
> remains).  Owner secondary review: REVIEW_QUEUE row 9 (rewritten 2026-08-31, CPF).

(Per-leg split: `fgmn_eisenstein_source` / `fgmn_unramified_source` /
`fgmn_pure_face_source`, each inheriting the Ports paragraph and its leg's rows.)

## Honest remainder (this unit's fence)

1. The package is UNSIGNED — nothing fires unconditionally until the owner declares the
   axiom with the caveat adjudications (B, C are the live ones).
2. The slope-`h ≥ 2` deep-primary recentring leg: NOT in the package (carrier gap before
   cite gap — unchanged from CP2, flagged in the docstring's honest scope and row 9).
3. No source-currency analogue of CP2's `pureFaceResidualLeg_irr_instance` tooth: it
   would require proving realization EXISTENCE off the maximal locus (exactly the Serre
   II §2 content that rides inside the cite).  The maximal-locus anchors are the honest
   Lean-core teeth; a future unit could prove Serre II §2 Prop. 3 outright (mathlib
   route: Henselian/`spectralNorm` theory) and upgrade them.
4. The `e`-components of the clauses are classically redundant given the `f`-components
   + degree formulas (fundamental identity in every realization) — carried because the
   source asserts them; translations consume only `f` + degrees.

## File map (`leanfinal/Uniformity/ChapI/I10CitePkgF.lean`, 32 public declarations)

§0 `HasClassicalType`, `hasResidueDegree_of_hasClassicalType`, the three bridges,
`hasClassicalType_unique`, `hasClassicalType_of_closure`/`_of_isDVR`/`_iff_of_closure`,
`hasClassicalType_eisKey`, `hasClassicalType_of_irreducible_map` ·
§1 `FactorCorrespondenceSourceAt`, `EisensteinLegSourceStatement`,
`UnramifiedLegSourceAt`/`UnramifiedLegSourceStatement`,
`PureFaceResidualSourceStatement`, `FGMNCitePackageF` · §2 the three translations +
★ `fgmn_package_of_packageF` · §3 the eight consumer re-exports · §4
`unramifiedLegSourceAt_zero` · AxCheck footer (32 lines) · private kit:
`natDegree_pos_of_monic_irreducible`, `monicFactors_one` (corpus-practice replicas).
Imports: I10CitePkg + IFCG76.  Aggregator: one line in `Uniformity/ChapI.lean`
(I10CitePkg → I10CitePkgF → I10RungLift3W).

## New definitions (trust boundary — flag for review)

`HasClassicalType`, `FactorCorrespondenceSourceAt`, `EisensteinLegSourceStatement`,
`UnramifiedLegSourceAt`/`UnramifiedLegSourceStatement`,
`PureFaceResidualSourceStatement`, `FGMNCitePackageF` (statement carriers — the point
of the unit; reviewed via row 9).  NO landed statement changed; I10CitePkg, IFCG76,
IFCG48, I10WrapPinned all byte-untouched.

## Repair log

ZERO error rounds: all five increments green on first verification (the unit is
statement-authoring over CUR's landed bridges; the only proofs are Rel.mono transports
and one replicated k=0 computation).
