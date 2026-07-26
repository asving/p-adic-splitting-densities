# MOVES Lean campaign — FINAL consolidation census (2026-07-26)

Full machine census of **every** `.lean` file in `lean/LeanUrat/Moves/` (65 files: 4 Defs
files + 61 unit files across waves base / `_R3` / `_R4` / `_R5` / `_final`). Supersedes
`MOVES_LEAN_CENSUS1_2026-07-26.md` (which covered 45 files, pre-R4/R5).

**Method (per file, exactly as the wave agents built).** `cd lean && lake env lean -o
<olean> LeanUrat/Moves/<f>.lean`, run in topological import order so each dep's `.olean`
is freshly built per-file via `lake env lean -o` — **never `lake build`**. Compile status =
exit code (0 = green). Real sorries = compiler `declaration uses \`sorry\`` diagnostics
(NOTE: Lean emits these on **stdout**, backtick-quoted). Axiom footprint = `#print axioms`
on each declaration via a per-module scratch importing the built olean. Fence = the
governing-manifest `statement` string matched in the file. All 65 built green; no non-core
axiom other than `sorryAx` appears anywhere.

Governing manifest by suffix: base→`MANIFEST.json`, `_R3`→`MANIFEST_R3`, `_R4`→`MANIFEST_CORE`,
`_R5`/`_final`→`MANIFEST_FINAL`. Toolchain `leanprover/lean4:v4.31.0`, mathlib cache present.

---

## 1. Per-file status

`cat` = census category: **clean** (proved, no `sorryAx` in cone) · **cond** (sorry-free file,
but main theorem inherits `sorryAx` via an import) · **sorry** (own `sorry`) · **defs** (Defs
foundation file, no manifest unit). `sec` = `lake env lean -o` wall time.

| file | compile | sec | sorry-warns | main decl | main footprint | fence | cat |
|---|---|---|---|---|---|---|---|
| Defs | green | 6 | 0 | — | core | n/a | defs |
| L0_GRg | green | 6 | 0 | L0_GRg | core | byte-exact | clean |
| DefsT | green | 5 | 0 | — | core | n/a | defs |
| L0_FactA_exists | green | 5 | 0 | L0_FactA_exists | core | token-id (wrapped) | clean |
| L0_FactB_unique | green | 5 | 0 | L0_FactB_unique | core | byte-exact | clean |
| L0_GRa | green | 5 | 0 | L0_GRa | core | byte-exact | clean |
| L0_GRb | green | 5 | 0 | L0_GRb | core | byte-exact | clean |
| L0_GRc | green | 5 | 0 | L0_GRc | core | byte-exact | clean |
| L0_GRd | green | 5 | 0 | L0_GRd | core | byte-exact | clean |
| L0_GRe | green | 5 | 0 | L0_GRe | core | byte-exact | clean |
| L0_GRf | green | 5 | 0 | L0_GRf | core | byte-exact | clean |
| L1_gaussVal | green | 5 | 0 | L1_gaussVal_mul | core | byte-exact | clean |
| L2_anchorCong | green | 5 | 0 | L2_anchorCong | core | byte-exact | clean |
| L2_iaugRecenter | green | 5 | 0 | L2_iaugRecenter | core | byte-exact | clean |
| L2_iaugRoot | green | 5 | 0 | L2_iaugRoot | core | byte-exact | clean |
| L2_keyResidualPow | green | 5 | 0 | L2_keyResidualPow | core | byte-exact | clean |
| L2_strideRule | green | 5 | 0 | L2_strideRule | core | byte-exact | clean |
| L3_liftExists | green | 5 | 0 | L3_liftExists | core | byte-exact | clean |
| L3_liftMonic | green | 5 | 0 | L3_liftMonic | core | token-id (wrapped) | clean |
| L3_liftWeight | green | 6 | 0 | L3_liftWeight | core | byte-exact | clean |
| L4_TRANSii | green | 5 | 0 | L4_TRANSii | core | byte-exact | clean |
| L4_TRANSiv | green | 5 | 0 | L4_TRANSiv | core | byte-exact | clean |
| L5_realConclusion | green | 5 | 0 | L5_realConclusion | core | byte-exact | clean |
| L6_ledgerCount | green | 4 | 0 | L6_ledgerCount | core | byte-exact | clean |
| L6_moveAffineBij | green | 5 | 0 | L6_moveAffineBij | core | byte-exact | clean |
| DefsCore | green | 6 | 0 | — | core | n/a | defs |
| L1_baseWeight_R3 | green | 4 | 1 | L1_baseWeight_valuation | **+sorryAx** | byte-exact | sorried |
| L2_P6ii_R3 | green | 5 | 0 | L2_P6ii | core | token-id (wrapped) | clean |
| L2_slotDecomp_R4 | green | 6 | 0 | L2_slotDecomp | core | byte-exact | clean |
| L4_TRANSviii_b_R3 | green | 5 | 1 | L4_TRANSviii_b | **+sorryAx** | byte-exact | sorried |
| L5_landTransport_R3 | green | 5 | 1 | L5_landTransport | **+sorryAx** | byte-exact | sorried |
| L5_realCofin_R3 | green | 6 | 0 | L5_realCofin | core | byte-exact | clean |
| L5_realDomination_R3 | green | 5 | 0 | L5_realDomination | core | byte-exact | clean |
| L5_realRecursion_R3 | green | 7 | 0 | L5_realRecursion | core | byte-exact | clean |
| L6_moveReduceCommute_R3 | green | 5 | 1 | L6_moveReduceCommute | **+sorryAx** | byte-exact | sorried |
| L2_widthBound | green | 6 | 0 | L2_widthBound | core | byte-exact | clean |
| L3_liftResidual | green | 7 | 0 | L3_liftResidual | core | byte-exact | clean |
| DefsL | green | 6 | 0 | — | core | n/a | defs |
| L1_baseResidual_R4 | green | 5 | 0 | L1_baseResidual_laws | core | byte-exact | clean |
| L4_TRANSvii_R4 | green | 5 | 0 | L4_TRANSvii | core | byte-exact | clean |
| L5_landTransport_R4 | green | 5 | 0 | L5_landTransport | core | byte-exact | clean |
| L5_recLiftIndep_R4 | green | 5 | 0 | L5_recLiftIndep | core | byte-exact | clean |
| L5_recRSland_R4 | green | 7 | 0 | L5_recRSland | core | byte-exact | clean |
| L5_recSpecies_R4 | green | 5 | 0 | L5_recSpecies | core | byte-exact | clean |
| L5_recSubst_R4 | green | 7 | 0 | L5_recSubst | core | byte-exact | clean |
| L6_moveReduceCommute_R4 | green | 5 | 0 | L6_moveReduceCommute | core | byte-exact | clean |
| L6_measureExact_R4 | green | 5 | 2 | L6_measureExact | **+sorryAx** | byte-exact | sorried |
| L4_TRANSv_R3 | green | 4 | 0 | L4_TRANSv | **+sorryAx** | byte-exact | conditional |
| L2_psiNotDvd_R3 | green | 5 | 0 | L2_psiNotDvd | core | byte-exact | clean |
| L3_digPrime_nonzero | green | 5 | 0 | L3_digPrime_nonzero | core | byte-exact | clean |
| L3_K1 | green | 6 | 0 | L3_K1 | core | byte-exact | clean |
| L5_landBox | green | 6 | 0 | L5_landBox | core | byte-exact | clean |
| L5_landVertex | green | 7 | 0 | L5_landVertex | core | byte-exact | clean |
| L5_landVertexDigit | green | 5 | 1 | L5_landVertexDigit | **+sorryAx** | byte-exact | sorried |
| L2_P6i_R5 | green | 6 | 1 | L2_P6i | **+sorryAx** | byte-exact | sorried |
| L2_P6i_R5_final | green | 6 | 0 | L2_P6i | core | byte-exact | clean |
| L4_TRANSviii_a_R5 | green | 5 | 1 | L4_TRANSviii_a | **+sorryAx** | byte-exact | sorried |
| L4_TRANSviii_a_R5_final | green | 5 | 0 | L4_TRANSviii_a | core | byte-exact | clean |
| L3_DIV | green | 6 | 0 | L3_DIV | core | byte-exact | clean |
| L5_recVV_R4 | green | 6 | 0 | L5_recVV | core | byte-exact | clean |
| L2_iaugStep | green | 5 | 1 | L2_iaugStep | **+sorryAx** | byte-exact | sorried |
| L4_TRANSi_R3 | green | 7 | 0 | L4_TRANSi | core | byte-exact | clean |
| L4_TRANSviii_b_R4 | green | 9 | 0 | L4_TRANSviii_b | core | byte-exact | clean |
| L5_landTwoSided_R5 | green | 8 | 1 | L5_landTwoSided | **+sorryAx** | byte-exact | sorried |
| L4_TRANSiii_R3 | green | 12 | 0 | L4_TRANSiii | core | byte-exact | clean |

Longest compile: `L4_TRANSiii_R3` 12s. All others 4-9s. `core` footprint = exactly
`{propext, Classical.choice, Quot.sound}`.

---

## 2. Sorry inventory (11 real sorries across 10 files)

Each is a compiler `declaration uses \`sorry\`` diagnostic (ground truth), with its one-line
in-file reason. `L4_TRANSviii_a_R5` and `L6_measureExact_R4` each carry 2 sorry terms; every
other listed file carries 1. Total sorry-warned **declarations = 11**.

| file | decl | line(s) | reason (from file comments) |
|---|---|---|---|
| L1_baseWeight_R3 | L1_baseWeight_valuation | 62 | honest gap: statement TRUE under the hyps, the min-formula valuation proof is outstanding work; sorry is the placeholder. |
| L2_iaugStep | L2_iaugStep | 72 | the reducible case is the single localized sorry, flagged in-file as a manifest-level gap. |
| L2_P6i_R5 | L2_P6i | 74 | clause (4) image ⊆ additive span of slot images (needs Φ-adic development + slot drop). SUPERSEDED by L2_P6i_R5_final (clean). |
| L4_TRANSviii_a_R5 | L4_TRANSviii_a | 71,107 | one decl, two sorries: :71 conjunct-1 forward needs Φ-adic development of B∈C_Φ̂; :107 conjunct-2 single-slot realizers (∃m∀c) only sketched. SUPERSEDED by L4_TRANSviii_a_R5_final (clean). |
| L4_TRANSviii_b_R3 | L4_TRANSviii_b | 98 | surjectivity once the threshold is cleared; honest sorry on exactly the I-aug/prev-read bridge. SUPERSEDED by L4_TRANSviii_b_R4 (clean). |
| L5_landTransport_R3 | L5_landTransport | 50 | REFUTED AS STATED (machine counterexample in-file); only honest body is sorry. SUPERSEDED by L5_landTransport_R4 (clean, restated with the slot-tie hypothesis). |
| L5_landTwoSided_R5 | L5_landTwoSided | 964 | anchor exactness is NOT encoded in the cylinder; flagged as the proposed round-6 repair. |
| L5_landVertexDigit | L5_landVertexDigit (private core) | 70 | K1 minimizing-slot residual content of the open deps; comment says 'pending L3.K1/L5.landVertex' but BOTH are now on disk and CLEAN — comment is STALE. |
| L6_measureExact_R4 | L6_measureExact | 143,189 | two sorries: :143 inlined placeholder L5_landTwoSided_missing (dep landTwoSided not imported); :189 main body `exfalso; sorry` — the zero-coordinate leg (no hypothesis pins E.IsSolution at Θ(code 0)), a genuine faithfulness gap the fenced statement omits. |
| L6_moveReduceCommute_R3 | L6_moveReduceCommute | 78 | the M=0 branch is genuinely FALSE (machine-checked disproof L6_moveReduceCommute_statement_false in-file); honest sorry, statement fenced. SUPERSEDED by L6_moveReduceCommute_R4 (clean, +1≤M). |

**5 of these 10 sorried files are SUPERSEDED** by a later sorry-free file for the same unit
(the campaign's repair chain): `L2_P6i_R5`→`_R5_final`, `L4_TRANSviii_a_R5`→`_R5_final`,
`L4_TRANSviii_b_R3`→`_R4`, `L5_landTransport_R3`→`_R4`, `L6_moveReduceCommute_R3`→`_R4`. The
remaining 5 (`L1_baseWeight_R3`, `L2_iaugStep`, `L5_landTwoSided_R5`, `L5_landVertexDigit`,
`L6_measureExact_R4`) are the genuinely-open units — no clean file exists for them.

---

## 3. Axiom footprint summary

`#print axioms` was run on **every** top-level declaration (294 decls across 61 unit files
+ 2 lemmas in `DefsL`), via per-module scratch files importing the freshly built oleans.

- **No declaration anywhere carries a non-core axiom other than `sorryAx`.** No GMN /
  Denef–Igusa / tame-FE axiom, no stray `axiom` — the campaign's "no new axioms" discipline
  holds across all 65 files. Clean footprint = exactly `{propext, Classical.choice, Quot.sound}`.
- **11 declarations transitively touch `sorryAx`** (their `#print axioms` lists it). 10 do so
  from their own `sorry`; **1 does so purely through an import** (see §5).
- Every sorried file's **fenced main theorem** carries `sorryAx` (no file hides a sorry in a
  helper while presenting a clean main): the set {main-has-sorryAx} = {any-decl-has-sorryAx}.

---

## 4. Fence report

Each on-disk unit file's fenced statement was matched against its governing manifest
(§ header). Result: **0 semantic fence breaks.** 58 statements are byte-identical,
3 are token-identical (line-wrapped whitespace-only diffs), 4 Defs files carry no
manifest unit (fence n/a).

Token-identical (line-wrapped, whitespace-only — elaborate to the same statement):
- `L0_FactA_exists` (L0.FactA_exists)
- `L3_liftMonic` (L3.liftMonic)
- `L2_P6ii_R3` (L2.P6ii)

Every `_R3`/`_R4`/`_R5`/`_final` file fences its restated statement in the correct manifest
(`MANIFEST_R3` / `MANIFEST_CORE` / `MANIFEST_FINAL` respectively); the 3 machine-checked
corrections in `MANIFEST_CORE` (`L4.TRANSviii_b`, `L5.landTransport`, `L6.moveReduceCommute`)
match their `_R4` files byte-exact. No statement was weakened to make a goal provable.

---

## 5. Sorry-dependency graph

`#print axioms` is proof-path-sensitive: a theorem lists `sorryAx` iff its *actual proof term*
(transitively, through imports) references a `sorry`. The complete propagation:

- **10 files carry `sorryAx` from their OWN `sorry`** (the §2 inventory).
- **1 file is sorry-free yet its main theorem carries `sorryAx` through an import:**
  `L4_TRANSv_R3` (`theorem L4_TRANSv`, clean body) imports `L4_TRANSviii_b_R3`, whose main
  `L4_TRANSviii_b` is sorried, and uses it — so `#print axioms L4_TRANSv` lists `sorryAx`.
  This is the ONLY transitive-only case. (Its sibling `L4_TRANSviii_b_R4` IS clean; re-pointing
  the import would discharge it — flagged.)
- **No other file imports a sorried file on its proof path.** Each sorried file is either a
  DAG leaf or imported only by files that don't touch its sorried declaration.

**Verified note-claim (the task's flagged case).** `L3_K1.lean`'s in-file comment (lines 42-43)
claims its footprint inherits `slotDecomp`'s sorry via `L2.widthBound`. **REFUTED by**
**`#print axioms`:** `L3_K1`, `L2_widthBound`, and `L2_slotDecomp_R4` are ALL clean
(`{propext, Classical.choice, Quot.sound}`). `L2_slotDecomp_R4` is itself sorry-free this
campaign, and `L3_K1` does not even import it. `L3.K1` is genuinely proved-CLEAN; the comment
is stale.

---

## 6. FINAL SCORECARD

### File level (65 files)
- **proved-clean: 50** unit files (no `sorryAx` in cone, footprint = Lean core).
- **proved-conditional: 1** file — `L4_TRANSv_R3` (`sorryAx` via import only).
- **sorried: 10** files (own `sorry`; §2).
- **Defs foundation: 4** files (`Defs`, `DefsT`, `DefsCore`, `DefsL`; sorry-free,
  core footprint, no manifest unit).

### Unit level (61 MANIFEST.json units — the campaign's semantic units)
Rolls the wave files up per unit (a unit is CLEAN if any of its files is clean; the campaign's
repair waves superseded 5 sorried early files with clean later files).

- **proved-clean: 50 units.**
- **proved-conditional: 1 unit** — `L4.TRANSv` (only file `_R3` inherits
  `sorryAx` from `L4_TRANSviii_b_R3`).
- **sorried (genuinely open, no clean file): 5 units** — `L1.baseWeight`, `L2.iaugStep`, `L5.landTwoSided`, `L5.landVertexDigit`, `L6.measureExact`.
- **boundary-deferred: 5 units** (the gr-campaign / graded-ring
  boundary; SEMAUDIT5 FAITHLESS set; **never filed on disk**):
  - `L1.baseStage_exists`
  - `L1.base_nonvacuity_gate`
  - `L4.TRANSvi`
  - `L4.TRANSstage`
  - `L5.recTRANSRS`

These 5 boundary-deferred units are exactly SEMAUDIT5's 5 FAITHLESS units. Their statements
live only in `MANIFEST_FINAL`/`MANIFEST_CORE`; the audit STOPPED THE LINE because a full
`StageCoreL` certificate silently consumes the graded-localization identification (the
`grRes`-from-`R` façade) that the blueprint defers to a future graded-ring campaign.

**Headline: 50/61 units proved-clean, 1 conditional,
5 sorried-open, 5 boundary-deferred; all 65 files
compile green; 0 fence breaks; 0 non-core axioms beyond `sorryAx`.**
