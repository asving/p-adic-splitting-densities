# FGMN pass 12 (Fable, fresh context, WITH execution) — verdict CLEAN

**Target:** `lean/notes/openmath/FGMN_REDERIVATION_2026-08-08.md` at REVISION 10
(HEAD 5107b7a for the note).  **Charge:** hostile verify (1) the REVISION-10
acceptance list — completeness, fidelity to what the eleven passes verified, sweep
for surviving normative pre-application perimeter claims and overstated
impossibility/totality language; (2) the standing mathematics (double-scaling
diagnosis vs the pinned extraction; row-A; the branch+meter; the rescopes;
JuncForge/D0/S8 honesty).  Mandatory execution leg certifying acceptance item (e).
No `FGMN_pass*_report.md` was read.  Nothing was fixed.

## 1. Execution leg (item (e)) — ALL EXACT

1. **Both sha256 pins byte-identical**: PDF `651b0cef…f615f35`, layout extraction
   `8d30f15e…76e848b` (`sha256sum`, this session).
2. **Layout extraction independently REGENERATED** from the pinned PDF
   (`pdftotext -layout`, poppler 22.02.0 on this box) → byte-identical hash.
   (Same tool version as the pin: this confirms determinism and pin integrity; it
   does NOT add the second-extractor leg — the §S7 single-extractor residual
   stands exactly as disclosed.)
3. **Battery re-run**: `python3 verification/openmath/fgmn_rederivation_check.py`
   → exit 0, TOTAL 1093, ALL GREEN, R1/R2/R4 at 336 each, R0=28, R5=56, R3=1.
   Console **byte-identical** to the pinned record
   `fgmn_rederivation_rerun_r1.txt` (diff empty, timings included);
   `fgmn_rederivation_results.json` untouched (git-clean) and its meters match
   the console (`misread` per-row {A:24,B:48,C:24,K:28,L:24,M:48,N:48};
   `r2_support` {2:264,3:68,5:4}).  The raw console prints the sorted set
   `[6, 12]` at the row-A compiled display — exactly what the §S8 REV3/REV4
   bracket discloses ("the raw file prints the sorted set [6,12]; this render
   lists per-slot [12,6] … the raw file is the record").
4. **The four JuncForge/D0 theorems compile-exist with the claimed meanings.**
   `Scaffold/HDischarge/H1/JuncForge.lean` has no importer and no olean (outside
   the root import graph), so I compiled it directly: `lake env lean … JuncForge.lean`
   → **exit 0** (lint warnings only), and the file's own `#print axioms` block
   prints Lean-core `[propext, Classical.choice, Quot.sound]` for ALL of:
   `juncforge_no_e2_junction` (:276 — SideReads recording of the row-A read
   forces ν.e = 1), `juncforge_deep_wall` (:385 — ¬SideReads … Φ2A at char-2),
   `juncforge_junc_bundle_false` (:554 — the junc_bundle core existential false),
   `juncforge_D0_instanceFalse` (:686 — B₀ = 0 by Fact B vs clause (ii)'s
   B₀ ≠ 0 demand at the recorded hpat0), plus `juncforge_clauseIII_derivable`,
   `juncforge_deep_wall_F4`, `juncforge_gate_hbundle_false`,
   `juncforge_gluePacket_false`.  Every one of the four binds `SideReads` BY NAME,
   so the REVISION-10 retention clause is exactly right: the new-definition route
   byte-freezes them and their compiled meanings (theorems about the OLD clause)
   are retained.
5. **The three-token diff sites verified**: `def SideReads` at `HC2/Defs.lean:280`;
   the ONLY `ν.σ.w (B …)` tokens in the definition are at **:285/:287/:292**
   (grep census; :151 is a different declaration and shape); the §S3 OLD block
   matches the compiled text verbatim; clause (ii)'s residual leg is already at
   `ν.σ.wPrev` in the T-exponent (:296) — as §S3 states.

**Bonus decorrelated leg (toward the standing F2c expectation):** I re-implemented
the R1 window/support check, the R2 any-gam′ collapse law, and the row-A record
**from the note's §S1/§S2/§S4/ADDENDUM displays alone** (my own check code,
sharing only the sealed tower state, R4-style): 336 sites, R1 violations 0, R2
violations 0, support meter **{2:264, 3:68, 5:4}** — identical to the record —
and the sealed closed form `e·gam − j·h·(e−1)` agreed with the direct compiled
value at every supported slot of all 336 sites (assertion never fired).  Row A
from note math: slots [0,2], wPrev = [3,0], corrected {0:6, 2:6}, compiled
{0:12, 2:6}.  (A literal "from this note alone" FULL battery is not constructible —
the note imports the sealed roster/family builders rather than displaying them —
so this leg re-implements the check logic, which is what the battery adds over
the harness.)

## 2. Standing mathematics — all verified, nothing survived hostile reading

* **Diagnosis vs the pinned extraction.** Every §S1 quote verified at its cited
  line: Nᵢ := N_{µᵢ₋₁,φᵢ} (l.869–871); cloud ordinates µᵢ₋₁(aₛφᵢˢ) (l.937–939);
  eq (13) (l.940–944); sⱼ/αⱼ (l.923, l.934); Lemma 2.3's µ′ = µ + sλ (l.415);
  Def 3.16 (l.916–923); Cor 4.4(2) (l.1085–1087); Def 3.15 (l.910–912); eq (12)
  (l.881); Thm 4.2 (l.1028–1029); Lemma 4.1 (l.1017–1019); Def 3.18 (l.994–1000);
  Cor 5.6(2) (l.1263–1265); eq (14) (l.1004).  The stage-vocabulary translation
  re-derived by hand: e(µᵢ)µᵢ(Bⱼφʲ) = eᵢ·e(µᵢ₋₁)µᵢ₋₁(Bⱼ) + j·e(µᵢ)(wᵢ+λᵢ) =
  ν.e·σ.wPrev(Bⱼ) + j·ν.h — exact.  The corpus-side anchors verified:
  `RegradeOf.w_coeff` (MovesC/Defs.lean:651), U31's stage literally sets
  `w := bw, wPrev := bw` (U31_gateReadsOf.lean:635–636).
* **Def 3.15 column arithmetic recomputed** (python over the pinned extraction):
  the ′ at codepoint column **52** on l.911; the FIRST ℓ at column 51 with its
  subscript i at column **52**; the second ℓᵢ at columns 59–60 unprimed — the
  print reads ǫᵢ(α) = zᵢ^{ℓ′ᵢs(α) − ℓᵢu(α)}, exactly §S7.  The print's Bézout
  convention (l.815–816: ℓᵢhᵢ + ℓ′ᵢeᵢ = 1, 0 ≤ ℓᵢ < eᵢ; l.883) matches the
  script's `bezout` (l = ℓ, lp = ℓ′), so mode C = ℓ′s − ℓu is the column reading
  and mode P is the misread; the misread meter discriminates on every roster row
  (24–48 sites), as claimed.
* **Row-A**, hand-recomputed from scratch: fA = (X+2)² + 24, so B₀ = 24, B₁ = 0,
  B₂ = 1, slots {0,2}; wPrev(24) = 3; corrected functional {2·3+0, 0+2·3} = {6,6}
  = gam; compiled {2·6+0, 0+2·3} = {12,6} at slots 0,2 respectively — no single
  gam.  Battery R3 record (2,3,6,0,2,(1,1),1,1) exact.
* **The branch + meter.** `check_compiled_unsat` implements precisely the claimed
  any-gam′ semantics: violation iff ≤ 1 distinct compiled value at the supported
  stride slots (empty = vacuously solvable; ANY singleton counts).  The sealed
  ADDENDUM derivation is correct (at a supported slot the corrected tie gives
  w(Bⱼ) = gam − j·h, so compiled = e·gam − j·h·(e−1); distinct slots → distinct
  values when e ≥ 2, h > 0), and its roster premise verified against the sealed
  `juncforge_stage1.ROWS`: e1 = 2 on A,C,K,L,N and 3 on B,M — all ≥ 2.  Family
  count 12 (excl. D4) × 28 instances = 336 confirmed by direct import.  The
  ADDENDUM preserves the original (refuted) sealed R2 text as historical record —
  honest.
* **The rescopes are what the code does.** R1 (`check_corrected`) instantiates
  ONLY (i-a)/(i-b)/(ii-support)/(iii-window-length) — no σ.R residual leg
  anywhere — matching the REVISION-1 rescope.  The from-print operator consumes
  certified Tower state (`T.w1`, `T.res_digit`, `T.K1`, `T.z1`, keys/chain
  parameters — confirmed in `R0_print`/`R1_print`/`eps1_print`/`R2_print`) and is
  independent only in recursion/exponent code — matching the rescoped §S7
  "DIFFERENTIAL falsifier" scope.  Both imported harness modules are git-clean
  and last touched pre-FGMN (53f5d03) — "imported, not edited" holds.
* **JuncForge/D0/S8 honesty.** eq (14) is in the print (l.1004); the D0 proof
  mechanism read in source (unique development B₀ = 0 vs clause (ii)'s demand);
  R5 (56 checks) confirms the source's own degeneracy; §S8 keeps the
  falsifier-only framing ("GREEN does not prove it").  The informative-preview
  sites all verify at their recorded lines: `SideClauseR1` Locality.lean:272,
  `sideReads_r1` :280, `SideClauseR2` :735 (σ.w functional at :738),
  `sideReads_r2` :744, `lastRead_of_readsOf_snoc` Window.lean:506,
  `DIterJunctionSupplier` GlueRun.lean:875.

## 3. The REVISION-10 acceptance list — complete, faithful, no surviving overreach

**Completeness.** Every section of substantive content maps into (a)–(e):
§S1/§S2→(a); §S4→(b); §S3-diff+§S5→(c); §S7→(d); §S0/§S8→(e); §S9 is the honesty
fence; §S6 and §S3's application-time obligations are out of scope per REVISION 9
item 2 (explicit).  All FIVE §S5 fixed-point rows are covered after the pass-11
extension: rows 1/2/4 named in (c); row 3 (parity wall) = (b) + the
`juncforge_no_e2_junction` retention; row 5 (D0) = the `juncforge_D0_instanceFalse`
retention + R5.  The REVISION-10 word "include" leaves room for the two
byte-tie corollaries (`juncforge_gate_hbundle_false`/`juncforge_gluePacket_false`),
whose retention follows from the same byte-freeze.  Each list item corresponds to
content the pass record confirmed (diagnosis: pass 1; row-A: pass 1 + execution
legs; diff sites: passes 3/5/6/7-record and this pass; PIN-GEN-i: pass 1 + column
recomputes; pins/battery: the execution legs incl. this pass).

**Sweep for surviving normative pre-application perimeter claims: none inside
acceptance.** REVISIONS 4–8 are explicitly demoted (REV9 items 2–3; REV8's "This
is checkable, implementer-independent, and total" sits inside the
refuted-and-recorded fifth specification); REVISION 3's "enumerated exactly" was
declared FALSE by REVISION 4 on the record; REVISION 2's "must carry the mirror
sites" is a necessary-condition observation (execution-verified: SideClauseR1/R2
ARE verbatim copies), folded into REV9's informative map ("the R1+R2 mirrors,
the (†)-transfer sites, Window/CU1, the named binders"), not a completeness
procedure.  §S3's obligations paragraph is expressly "for the adjudicated unit,
not this one" and outside the (a)–(e) binding.

**Sweep for overstated impossibility/totality language: none surviving.** The
REV9 bold impossibility ("no pre-application textual or build-error procedure
can…") is rescoped by REV10 item 2 to the five demonstrated execution failures;
REV9's "the only total oracle" is superseded in substance by REV10's "STRONGEST
AVAILABLE adjudication (not a formal totality oracle)".  Candidates weighed and
dismissed, for the record: (i) REV10's "the demonstrated reliable path" — read as
artifact-level adjudication (the arc's eleven execution legs and five
execution-refutations ARE its demonstration), and immediately hedged by the
totality disclaimer in the same sentence; (ii) the title/§S3 "four-token" —
superseded explicitly by REVISION 2 item 3 under the note's append-only
convention; (iii) the §S8 render's residual representational divergences beyond
the disclosed slot-order item (pat/vtx tuple flattening, dropped progress/elapsed
lines) — numbers identical (verified against the raw file), covered by the
in-place EDITED RENDER label and "the raw file is the record".

**Standing residuals (disclosed in the note; none new):** single extractor
pass/version at §S7 (my regeneration confirms determinism, not decorrelation);
PDF provenance via the litunit fetch (§S0 disclosure); the queue-#9 Lean-side
corrected-bundle construction owed; ITER-LAW open; the full F2c from-note battery
remains impossible in the literal sense (the note does not display the roster
builders) — this pass's from-note re-implementation of the check logic +
closed-form law is the achievable core of it and is now on record.

## Findings

**0 critical, 0 gaps.**  The execution leg is EXACT on every pinned artifact; the
standing mathematics survived independent recomputation at every point probed;
the REVISION-10 acceptance list is complete, matches the verified record, and
carries no surviving normative pre-application perimeter claim and no surviving
overstated impossibility/totality language.

**VERDICT: CLEAN** (first of the two consecutive clean passes REVISION 10
requires; pass 13 decides the second).

— FGMN pass 12, Fable, 2026-08-08 (wallclock 2026-08-03).
