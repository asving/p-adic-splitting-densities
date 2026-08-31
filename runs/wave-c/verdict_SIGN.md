# UNIT SIGN — VERDICT: THE FGMN CITE DECLARED (the seventh axiom) AND THE CENSUS
CONSUMERS FIRED — MASS 4 CLOSES AT ALL TYPES; hFC GONE FROM BOTH MASTER LINEAGES —
2026-08-31

**Re-grounding.** Unit CPF staged `FGMNCitePackageF` (I10CitePkgF.lean §1): the three
OM-tower pointwise factorization steps (Eisenstein leg E / unramified leg U / pure-face
residual leg R) with per-factor `(e, f)` conclusions in the SOURCE's own currency
(`HasClassicalType` over IFCG76's `DVRClosure`), the gcd-currency package
`FGMNCitePackage` a Lean-core corollary (`fgmn_package_of_packageF`).  The owner signed
2026-08-31 (verbatim): "Okay with the CUR landing, I think the FGMN cite is fine to go."
This unit enacts the signature: declares the axiom, lands the faithfulness entry, and
fires every census consumer.

**Deliverables (all verified; ZERO repair rounds in the whole unit):**

1. `leanfinal/Uniformity/ChapI/I10FgmnCite.lean` (NEW, 256 lines) — ★
   `axiom fgmn_cite_packageF : FGMNCitePackageF` (namespace
   `Uniformity.Density.I10CitePkgF`) + the OM-5/BBox1-pattern provenance docstring
   (source theorems FGMN 2015 Thm 6.2 + Thm 6.4 + Cor 6.6, AGNPRW 2024 companion, Serre
   CL II §2 Prop. 3 riding inside; owner quote verbatim; pointers to CPF's
   quotes/dictionary/caveats + CUR's bridge) + **12 unconditional `*_cite` forms**:
   `fgmn_cite_package : FGMNCitePackage`, the three leg statements,
   ★ `factorCorrespondence_cite : ∀ D, 2 ≤ D → FactorCorrespondenceAt D` (THE FC_D
   family — discharges every `hFC` binder in the tree), `deepWildTypeScaling_cite`,
   `cellTypeScaling_cite`, `cellTypeScalingAt_two_cite`, `transport_decidedAt_iff_cite`
   (the deep-wild decision transport at every depth — CTS2's consumer),
   `unram_typeScaling_cite` + `tower_typeScaling_cite` (MFL's pointwise law + the
   mixed-tower composite), `decidedAt_of_squarefree_residual_cite` (the census pure-face
   socket).  `lake env lean` GREEN FIRST TRY; 13/13 AxCheck lines = Lean core +
   `fgmn_cite_packageF` EXACTLY.
2. `docs/AXIOM_FAITHFULNESS.md` — the SEVENTH entry appended
   (`fgmn_cite_packageF (I10FgmnCite, declared 2026-08-31)`), CPF's draft enacted in the
   standing format: Declared / Ports / Faithfulness surface / Caveats adjudicated
   (B, C, D, E carried; A RESOLVED by the machine-checked IFCG76 bridge) / Non-vacuity
   teeth / Footprint discipline.
3. `leanfinal/Uniformity/ChapI/I10FgmnFired.lean` (NEW, the consumer walk) — GREEN
   FIRST TRY, contents below.
4. Aggregator: two lines in `Uniformity/ChapI.lean`
   (I10CitePkgF → I10FgmnCite → I10FgmnFired → I10RungLift3W).
5. Full `timeout 580 lake build Uniformity.ChapI` **GREEN (9183 jobs)** — including the
   concurrent units' churn (I10DoublyPinned etc. appeared mid-unit; no collision; the
   only warnings are pre-existing linter notes in files not mine).

## ★★★ THE FIRED CONSUMERS (I10FgmnFired.lean, namespace Uniformity.Density.I10FgmnFired)

| theorem | statement | footprint |
|---|---|---|
| ★★★ `coneRemainderLaw_four_all` | `∀ σ : FactorizationType, ConeRemainderLaw 4 σ` — **MASS 4 CLOSES, ALL 11 TYPES, unconditional** (IFCG55's all-types row at `factorCorrespondence_cite 2 le_rfl`; also discharges every `hR4` binder in the clusterGeom lineage) | core + `fgmn_cite_packageF` + `exists_slope_factorization` |
| `zcURLim_e1DdDecFam_all` | `∀ σ, ZcURLim (e1DdDecFam σ)` — the LAST conditional mass-4 sector limit (ASM's row), fired | core + `fgmn_cite_packageF` |
| `powerFullSpanLaw_four_all` | `∀ σ, PowerFullSpanLaw 4 σ` (ASM's row), fired | core + `fgmn_cite_packageF` |
| ★★★ `decidedSliceAt_all_of_MASTER_SIGNED` | the IFCG72 census master with `hFC` GONE (statement below) | core + `fgmn_cite_packageF` + `exists_slope_factorization` |
| ★★★ `capstoneHypotheses_of_MASTER_SIGNED` | the IFCG72 capstone master with `hFC` GONE | + `agnprw_termination` |
| ★★ `decidedSliceAt_all_of_clusterGeom_signed` | the IFCG74 census master with `hR4` GONE (mass 4 closed) | core + `fgmn_cite_packageF` + `exists_slope_factorization` |
| ★★ `capstoneHypotheses_of_clusterGeom_signed` | the IFCG74 capstone master with `hFC` GONE | + `agnprw_termination` |

Subsumed (not separately restated — covered by `coneRemainderLaw_four_all` at their σ):
IFCG51's three `coneRemainderLaw_four_{ramPair,type22,type41}_of_correspondence`,
IFCG54's `coneRemainderLaw_four_ramPair_of_fc2` (DDT's conditional row), IFCG55's
`coneRemainderLaw_four_{type22,type41}`.  DTR (IFCG47) was already cite-free — nothing
to fire.  All superseded masters (IFCG55 `MASTER`, IFCG57 `MASTER'`, IFCG59 `MASTER''`,
IFCG60 `MASTER'''`, IFCG62 `MASTER_MIXED`, IFCG66 `MASTER_FRAMES`, IFCG69
`MASTER_FRAMES_r2`, IFCG71/73 `clusterGeom`) fire identically from
`factorCorrespondence_cite` — not restated (the two CO-LATEST lineages above are the
capstone-level surfaces; nothing imports the older fronts for census purposes).

## THE POST-SIGNATURE MASTER, EXACTLY (the capstone-level surface)

Two co-latest lineages (neither imports the other); `hFC` is gone from BOTH.

**Steep-census lineage** (IFCG72 → `capstoneHypotheses_of_MASTER_SIGNED (n)`), rests on
exactly — beyond the ladder/deepTwist config blocks (`hladder`, `hdeepTwist`, carried
verbatim) — FOUR census rows, each guarded by
`(∀ k < e, decided value laws) → σ.degree = e → Witnessed e σ → (∃ p ∈ σ.data, p.1 ≠ 1)`:

* `hEis` (`m ≥ 6` composite): `EisFullSpanRemainderLaw m σ` — **EisFullSpan's frame
  laws, the h ≥ 2/mixed remainder** (the slope-Bézout carrier gap, see fence below);
* `hSD` (`e ≥ 5`): `SplitConvolutionDefectLaw e σ`;
* `hPD` (`e ≥ 5`): `PowerConvolutionDefectLaw e σ` — the two convolution-defect rows;
* `hCensus` (`e ≥ 5`, `2 ≤ card σ.data`, non-special frames `e ≠ h·d + 1`):
  `SteepDecCensusLaw (e − h·d) h e'` at every subframe — **the r ≥ 2 SteepDecCensusLaw
  at non-special frames**.

**ClusterGeom lineage** (IFCG74 → `capstoneHypotheses_of_clusterGeom_signed (n)`),
rests on exactly (same guards): `hEis` + `hCG` (**the weight-matched
`VisEntryClusterGeom` censuses — unit TSV in flight, IFCG77**) + `hCL` (`CollisionLaw`)
+ `hPCL` (the power-collision `ZcURLim`) + `hLeafSub` (`LeafSubfaceLaw`); the slice
master additionally `hPF` (`PowerFullSpanLaw e σ`, `e ≥ 5`).  NOTE an available further
reduction not enacted (no landed master carries the needed rows as premises): with the
cite signed, `IFCG51.powerFullSpanLaw_of_correspondence`'s FC premise discharges, so
`hPF` is reducible to its `{hDV, hZC, hRem}` dissection rows.

## AxCheck discipline (charge 4 — verified)

* The axiom appears in EXACTLY the consumers' footprints: 13/13 lines of
  I10FgmnCite.lean and 7/7 lines of I10FgmnFired.lean print it; grep-verified that the
  ONLY files referencing/importing I10FgmnCite are I10FgmnFired.lean and the aggregator
  — no previously-existing proof term can contain it.
* Previously-Lean-core/previously-conditional surfaces spot-checked UNCHANGED post-build
  (`/tmp/sign_spotcheck.lean`): `IFCG72.decidedSliceAt_all_of_MASTER_CENSUS` = core +
  `exists_slope_factorization` (no new axiom); `IFCG72/74.capstoneHypotheses_*` = + 
  `agnprw_termination` only; `I10CitePkgF.fgmn_package_of_packageF` and
  `FGMNCitePackageF` = pure Lean core.  The capstone assemblies gain the axiom ONLY
  through the `_SIGNED`/`_signed` forms that legitimately consume it.
* No live `#axiom_core`/`#axiom_reg` guards exist in leanfinal (prose mentions only) —
  nothing to amend.

## NOTE FOR THE ORCHESTRATOR — PROJECT_STATE §3 ledger edit (not enacted here)

Trusted base: **SIX → SEVEN declared cites.**  Suggested row: `fgmn_cite_packageF`
(I10FgmnCite.lean, declared 2026-08-31, owner-signed row 9) — FGMN 2015 Thm 6.2 + Thm
6.4 + Cor 6.6 (+ AGNPRW 2024 companion; Serre CL II §2 Prop. 3 inside the statement),
faithfulness entry #7 in docs/AXIOM_FAITHFULNESS.md; consumers: the mass-4 closure, the
FC_D family, the deep-wild transports, both post-signature master lineages
(I10FgmnFired.lean).  Caveat A resolved (IFCG76 bridge); caveats B/C/D/E carried in the
entry.

## Honest remainder (this unit's fence)

1. **NOT covered by the signed package** (a DIFFERENT carrier — IFCG75's own docstring:
   leg E is exactly the `h = 1` instance): `SlopeBezoutFactorCorrespondenceAt h k` and
   its two consumers (IFCG75:1477, :1608) stay conditional — the slope-`h ≥ 2`
   deep-primary recentring step is a carrier gap before a cite gap (unchanged from
   CPF's honest scope; would be a separately-signable statement).
2. The masters remain conditional on their non-FC rows (the lists above) — the
   signature closes the LITERATURE premise, not the census work in flight (TSV's
   VisEntryClusterGeom at IFCG77 untouched, per the charge; the EisFullSpan h ≥ 2
   remainder; the r ≥ 2 steep census at non-special frames; the convolution-defect and
   leaf-subface rows).
3. Concurrency note: the ChapI aggregator churned mid-unit (concurrent units added
   imports, e.g. I10DoublyPinned); the final full build (9183 jobs) is green WITH that
   churn included — no per-file fallback was needed; my edits were scoped to the two
   new files + two aggregator lines + the ledger append.

## File map

`leanfinal/Uniformity/ChapI/I10FgmnCite.lean` — §0 the axiom; §1 the 12 unconditional
`*_cite` forms; AxCheck footer (13 lines) ·
`leanfinal/Uniformity/ChapI/I10FgmnFired.lean` — §1 mass-4 closure (3 theorems); §2 the
steep-census post-signature masters (2); §3 the clusterGeom post-signature masters (2);
AxCheck footer (7 lines) · `docs/AXIOM_FAITHFULNESS.md` — entry #7 appended ·
`Uniformity/ChapI.lean` — 2 import lines.  Statements: every new theorem is a
byte-identical restatement of a landed conditional theorem minus the discharged
binder(s); the ONE new assertion in this unit is the owner-signed axiom itself.

## Repair log

ZERO error rounds. Both new files green on first `lake env lean`; the only mechanical
hiccup was building I10FgmnCite's olean before compiling the firing file (not an error).
