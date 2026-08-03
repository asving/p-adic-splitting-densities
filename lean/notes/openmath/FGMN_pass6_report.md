# FGMN pass 6 — hostile verification of FGMN_REDERIVATION_2026-08-08.md (REVISION 4)

**Verifier:** Fable, fresh context (no FGMN_pass*_report.md consumed; the af88f12
commit MESSAGE was incidentally displayed by a provenance check AFTER my own DictIII
sweep was already complete and had independently reproduced the same site lists).
**Charge:** REVISION-4 perimeter first (own complete DictIII sweep + reconciliation;
grep-discipline rule; re-derived-readCeil pricing honesty; §S8 header disclosure),
then the standing perimeter (diagnosis, row-A, branch+meter, rescopes, JuncForge/D0
honesty, three-token diff). Quote-and-classify; nothing fixed.
**Verdict: GAPS-ONLY — 0 critical, 2 justification gaps.**

## Independent execution leg (all EXACT)

* **Pins:** `sha256sum` run by me: PDF `651b0cef…f615f35`, layout extraction
  `8d30f15e…76e848b` — both byte-identical to §S0's table.
* **Battery:** `python3 fgmn_rederivation_check.py` executed by me, exit 0, `ALL
  GREEN`, TOTAL 1093 (R0 28 / R1 336 / R2 336 / R3 1 / R4 336 / R5 56), meters
  MISREAD `{A:24,B:48,C:24,K:28,L:24,M:48,N:48}` and R2-SUPPORT `{2:264,3:68,5:4}`
  — identical to `fgmn_rederivation_rerun_r1.txt`. `fgmn_rederivation_results.json`
  was overwritten by my run and `git status` stayed CLEAN: my execution reproduced
  the committed JSON byte-identically (violations `[]`, counts as above).
* **Print quotes:** every §S1 display re-read in the pinned `_layout.txt` at the
  cited lines (869–871, 384, 415, 881, 910–912, 916–923, 937–944, 994–1004,
  1017–1019, 1028–1029, 1085–1087, 1263–1265) — all faithful, including eq (13)'s
  parent-level on-line law and Thm 4.2's graded-side glue.
* **Def 3.15 column arithmetic recomputed** (python over codepoints): the ′ on
  l.911 sits at codepoint column 52; the FIRST ℓ on l.912 spans columns 51–52
  (second ℓ at 59) — the ℓ′ᵢs(α) − ℓᵢu(α) reading confirmed. Genericity ranges
  (0 ≤ i < r / 0 ≤ i ≤ r / 1 ≤ i ≤ r) confirmed at l.910/916/994.
* **Stage translation re-derived:** e(µᵢ)µᵢ(Bⱼφʲ) = eᵢ·[e(µᵢ₋₁)µᵢ₋₁(Bⱼ)] + j·e(µᵢ)(wᵢ+λᵢ)
  via Lemma 2.3 + e(µᵢ) = eᵢ·e(µᵢ₋₁) — §S1's boxed functional is exact.
* **No `.lean` touched** by any FGMN-arc commit (303b11e/236d85c/0170d68/f64307e/
  fa2180e: zero .lean files in every stat) — proposal-only status holds.

## PRIORITY: my own DictIII sweep vs the REVISION-4 list

Sweep run by me over `lean/LeanUrat/Scaffold/DictIII/` (14 files, 13,204 lines) on
`SideClause` / `sideReads` / `σ.w` / `readCeil` / `read_locality`, PLUS a
case-corrected `SideReads` pass and a repo-wide mirror scan. Reconciliation:

* **R1 pair** `SideClauseR1` :272 + `sideReads_r1` :280 — EXACT.
* **R2 pair** `SideClauseR2` :735 (σ.w functional at :738, T-exponent already at
  σ.wPrev at :741) + `sideReads_r2` :744 — EXACT.
* **(†)/hdag transfer layer** — my census of statement-level dagger rows
  (`ν.gam < ν.e·σ.w(B j − B′ j) + j·h` shapes) is exactly
  {:322, :381, :398, :658, :794, :828, :847, :1327} — EXACT match to the list
  (remaining σ.w-diff hits :347/:367–369/:668–671/:804–807/:1337 are proof bodies).
* **Window.lean σ.w sites** — exactly {:177, :258, :260, :266, :544, :554, :557} —
  EXACT match.
* **R5 family + assembly** — `SideClauseR5` :915 / `sideReads_r5` :922 / transfers
  :982/:1029/:1064 and `sideReads_mono` :1214 / `read_locality_rows` :1278 /
  `read_locality` :1380 all fall under the two family bullets. Consistent.
* **Re-derived-readCeil pricing honesty — CONFIRMED, and mathematically right.**
  With the stretch law w = e·wPrev on the carrier, the primed dagger row
  gam < e·wPrev(diff) + j·h equals gam < w(diff) + j·h, while the compiled row is
  gam < e·w(diff) + j·h — corrected ⟹ compiled, strictly stronger at e ≥ 2 on the
  supplied locus (w(diff) ≥ readCeil·strFrame ≥ 1). The current supply chain proves
  only gam/e < readCeil·strFrame (`readCeil_strict_middle`, :594–:616; readCeil's
  body prices ⌈(gam/e)/strFrame⌉, :607), which does NOT yield the corrected row at
  j = 0 (needs gam < L·E). So "re-derived readCeil arithmetic, not renames" is the
  honest price, correctly flagged into the Asvin decision.
* **§S8 header disclosure — CONFIRMED accurate.** The REV4 bracket at the block
  header discloses the order divergence; raw file prints the sorted set `[6, 12]`
  (script sorts: `sorted({...})`), the render lists per-slot `[12,6]` at slots
  [0,2]; same two values, same UNSAT conclusion; raw declared the record.

### GAP 1 — a genuine DictIII perimeter site invisible to the grep discipline

Quote (REVISION 4): "The COMPLETE application perimeter, per the verifier's own
DictIII grep, now of record: … any residual site found later joins the change-set
under the same rule (the perimeter is defined by the grep discipline, not by this
list's completeness claim)."

**`lastRead_of_readsOf_snoc` (Window.lean:506–:521)** concludes
`… IsDevelopment ν'.σ.Φ f B Nd ∧ SideReads ν' B Nd Φnext` — it binds `SideReads`
BY NAME, is the extraction lemma the listed `m6c_noPhantom` consumes at :565, and
is on NO bullet of the REVISION-4 list (none of the listed Window lines fall in
[506,521]). Worse for the rule: I ran the sweep's term set against its statement —
`SideClause`/`sideReads`/`σ.w`/`readCeil`/`read_locality` produce ZERO hits
(case-sensitive `sideReads` does not match capital `SideReads`; the statement has
σ.Φ but no σ.w token). So the self-repair rule cannot fold this class in: the note
never records the discipline's term set or case rule, and the natural
pass-5-shaped instantiation is structurally blind to by-name `SideReads` bindings
that carry no σ.w token. Failure scenario: the application executor restates
`m6c_noPhantom` against `SideReads'` per the list; `lastRead_of_readsOf_snoc`
still emits OLD `SideReads` — a mid-edit type mismatch under the recommended
new-definition route, or (in-place variant) a silent re-key of an unlisted
theorem, the exact defect class REVISION 2 established the perimeter to prevent.
CLASSIFICATION: justification gap (nothing is applied; the site is reachable from
a listed consumer; but the "COMPLETE … of record" sentence is again not complete,
and the perimeter-defining grep needs `SideReads` (exact case) added ON RECORD).

### GAP 2 — CU1's grep-visible read_locality/readCeil consumer cluster unlisted

`CU1.lean` is a DictIII file with 36 lines matching the sweep terms: the III-U6
support layer — `cu1_lvl` (:2017, binder `hmaj : NstarMaj Nstar readCeil dress`),
`nstarMaj_readCeil_le` (:2118), and `readsOf_transfer_at_nstar_level` (:2140,
"the ONE `read_locality` application at the top site"). The REVISION-4 list's last
bullet stops at "The R5 tie family / read_locality assembly — restated against the
primed set" (the assembly = III-T10 in Locality.lean); the downstream CU1 ring is
nowhere itemized, although under the in-place variant it silently diverges
(read_locality re-keys ⇒ cu1_lvl re-keys — the note's own REVISION-2 membership
criterion), and under the recommended route the corrected chain stops short of
CU-1-LVL unless these join the change-set. Treatment is inconsistent with Window's
consumers (which the list DOES carry). CLASSIFICATION: justification gap — grep-
visible, so the residual-site rule genuinely covers it once run; but a list
labeled COMPLETE, adopted specifically to end the pass-5 completeness failure,
should have carried the one DictIII consumer ring its own grep surfaces.

## Standing perimeter (all CONFIRMED)

* **Diagnosis (§S2):** compiled functional at σ.w verified at HC2/Defs.lean:285/
  287/292; clause-(ii) residual leg already at σ.wPrev (:295); row-A hand-check —
  d1 = [24, 0, 1] against Φ1A = X+2, w1(24) = 3, corrected {2·3+0, 2·0+2·3} = {6,6}
  = gam, compiled {12, 6}, no single gam′; parity collision (σ.w(24) = 3 odd vs
  graded tie 6 even) matches `juncforge_no_e2_junction`'s own docstring mechanism.
  Invisibility cites verified: `RegradeOf.w_coeff` (MovesC/Defs.lean:651, e★ = 1
  face of the stretch law) and U31 `bStage` literally `w := bw / wPrev := bw`
  (U31_gateReadsOf.lean:635–636).
* **Row-A record (R3):** re-executed; (2,3,6,0,2,(1,1),1,1) with vtx digit (1,)
  nonzero; att = [0,2].
* **Branch + meter (R2):** repaired semantics sound in the correct direction
  (equality-subsystem any-gam′ UNSAT ⟹ compiled clause-(ii) UNSAT; violation iff
  ≤ 1 distinct compiled value, singleton counted regardless of recorded gam); the
  sealed support-meter derivation re-derived by me (supported slot j ⟹ compiled
  value e·gam − j·h·(e−1); distinct j ⟹ distinct values since h(e−1) > 0); measured
  {2:264, 3:68, 5:4} pools to 336 with no site ≤ 1. The ADDENDUM's "sealed before
  rerun" ordering is not externally checkable (one commit, 236d85c), but the
  prediction is forced by the derivation, so tuning risk is nil.
* **Rescopes:** R1-as-window/support-satisfiability (no σ.R leg) present at §S4,
  §S5, §S8 readings, §S9 and the script ADDENDUM (a) — and matches the actual
  implementation (`check_corrected` tests (i-a)/(i-b)/(ii-support+equality)/
  (iii-window-length) only; note that gam := min makes (i-a) green by
  construction, which is exactly correct for a SATISFIABILITY reading and only
  for that reading — the note's chosen word). R4-as-differential-falsifier present
  at §S7/§S8/ADDENDUM (b) and matches the code (Tower state consumed; recursion/
  exponent code independent; misread meter discriminates on every row, 24–48/row).
* **JuncForge/D0 honesty:** `juncforge_no_e2_junction` (JuncForge.lean:276)
  concludes ν.e = 1 from the COMPILED `SideReads` — "true theorem about the
  compiled clause shape" is exact; `juncforge_clauseIII_derivable` (:578) pins
  hwP = 3 / hw24 = 6 and is untouched by the diff; `juncforge_D0_instanceFalse`
  (:686) rests on clause (ii)'s scale-independent B₀ ≠ 0 demand, so "not
  resurrected under either scale" is exact, with R5 (56 checks, eq (14) verified
  in the print at l.1004) as the source-degeneracy leg. Supplier statement
  `DIterJunctionSupplier` confirmed at GlueRun.lean:875 with the mode-conditional
  reading of §S6.1 on record (REVISION 3).
* **Three-token diff:** §S3's OLD block is verbatim in HC2/Defs.lean:284–293;
  exactly THREE `ν.σ.w` tokens in the clause-(i)/(ii) functional legs
  (285/287/292); the REVISION-2 supersession of every "four-token" occurrence
  stands (title/§S3 wording unedited by design, superseded on record).

## Verdict

0 critical / 2 justification gaps (both on the REVISION-4 perimeter list's
completeness and the under-specified grep discipline; the diagnosis, proposal
content, numerics, source leg, and every honesty rescope survived full independent
re-execution). **GAPS-ONLY.** Acceptance counter does not advance (0/2).
Recommended REVISION-5 content, for the orchestrator (not applied by me): add
`lastRead_of_readsOf_snoc` and the CU1 III-U6 ring to the perimeter list, and pin
the grep discipline's term set ON RECORD including exact-case `SideReads`.

— FGMN pass 6 (Fable), 2026-08-08 (wallclock 2026-08-03).
