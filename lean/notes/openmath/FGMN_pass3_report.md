# FGMN_REDERIVATION_2026-08-08.md (REVISION 1) — hostile verification pass 3 (Fable, fresh context)

**Charge:** full pass on the note + `verification/openmath/fgmn_rederivation_check.py` +
`fgmn_rederivation_rerun_r1.txt` + the `docs/references/` pins; MANDATORY prover-independent
re-execution of the battery; quote-and-classify (CRITICAL / GAP); fix nothing.  Discipline
honored: no `*_pass*_report.md` read (all findings independent); `/tmp/litunit/fgmn.txt`
consumed ONLY to audit the note's corruption claim about it, never as source evidence.
Numerics treated as falsifiers, never proofs.

## 0. THE MANDATORY EXECUTION LEG — exact agreement

* Ran `python3 verification/openmath/fgmn_rederivation_check.py` (exit 0).  Console is
  **byte-identical** to the recorded `fgmn_rederivation_rerun_r1.txt` — `diff` empty
  including the timing lines (`0.1/0.1/0.3/0.6s`, `elapsed 0.6s`).  All rows GREEN at the
  recorded counts: R0 28, R1 336, R2 336, R3 1, R4 336, R5 56 = 1093 checks; sites 336;
  misread meter `{A:24,B:48,C:24,K:28,L:24,M:48,N:48}`; R2 support meter
  `{2:264,3:68,5:4}` (sum 336, min key 2).
* The regenerated `fgmn_rederivation_results.json` is **byte-identical** to the recorded
  one (sha256 `089cf845…89aab8` before and after my run).
* Provenance pins re-verified by me: PDF sha256 `651b0cef64e6aea11526965d3ef7879d69ce7c0a3
  1af497978c3e6192f615f35`, layout extraction `8d30f15e6d37a52be20634545c95f32e372a2331
  66c5dab8d995c3d5f76e848b` — both match §S0's table exactly.
* **Decorrelation beyond the charge:** this box's `pdftotext` is poppler **22.02.0**;
  re-running `pdftotext -layout` on the pinned PDF myself reproduces the pinned layout
  extraction **byte-identically** (same sha256).  The extraction is exactly what the tool
  produces from the pinned PDF — no hand edits possible.  Title page + margin stamp
  confirm the print: `arXiv:1305.0775v3 [math.NT] 26 Jul 2013` (extraction l.8),
  Fernández–Guàrdia–Montes–Nart, *Residual ideals of MacLane valuations*.

## 1. VERIFIED PERIMETER (independently established)

**(a) The double-scaling diagnosis against the pinned print — CONFIRMED.**  Every cited
display located at the cited line: `Nᵢ := N_{µᵢ₋₁,φᵢ}` (l.869–871); cloud ordinates
`(s, µ(aₛφˢ))` (l.384) and `Qₛ := (s, µᵢ₋₁(aₛφᵢˢ))` (l.937–939); eq (13) two-case law
(l.942–944); `sⱼ := s(α)+jeᵢ`, `αⱼ := α − sⱼ(wᵢ+λᵢ)` (l.923, l.934); Lemma 2.3 proof
`µ′(aₛφˢ) = µ(aₛφˢ) + sλ` (l.415); Def 3.16 recursion with parent-level reads
`ǫᵢ₋₁(αⱼ)·R_{i−1,αⱼ}(aₛⱼ)(zᵢ₋₁)` (l.916–923); Cor 4.4(2) support law (quote at
l.1086–1087); eq (12) (l.881); Def 3.15 (l.910–915); Def 3.18 with `j₀ = ⌊s(g)/eᵢ⌋`
(l.994–1000); eq (14) (l.1004); Lemma 4.1 `ϕᵢ(g) := xᵢ^{s(g)}pᵢ^{u(g)}` (l.1017–1019);
Thm 4.2 `H_µ(g) = ϕᵣ(g)Rᵣ(g)(yᵣ)` (l.1028–1029); Cor 5.6(2) `Rᵢ(φᵢ₊₁) = ψᵢ`
(l.1263–1265).  The window/digit machinery is keyed at µᵢ₋₁ throughout; the residual
lands in Gr(µ) — the two-scale law is in the print as §S1 claims.  The stage translation
checks: µᵢ(Bφʲ) = µᵢ₋₁(B) + j(wᵢ+λᵢ) (Lemma 2.3) with e(µᵢ) = eᵢ·e(µᵢ₋₁) gives
`e(µᵢ)µᵢ(Bφʲ) = ν.e·σ.wPrev(B) + j·ν.h` exactly; harness `w2_data` computes verbatim
`e1*w1(B_j) + j*gamma2`.  Lean side: `SideReads` (HC2/Defs.lean:280) carries `ν.σ.w` at
lines 285/287/292 and `ν.σ.wPrev` at 295 (residual T-exponent); `RegradeOf`
(MovesC/Defs.lean:631) sets `σV.wPrev f = σ.w f` pointwise + `IsSlotMinWeight σV.w`
(Moves/Defs.lean:247: `w'(ΣBⱼΦ̂ʲ) = minⱼ (e′·w(Bⱼ) + j·h′)`), so on the coefficient
carrier σV.w = e★·σV.wPrev — the compiled functional at a read-pair-graded junction is
`e·(e·wPrev(Bⱼ)) + j·h`, double-scaled, exactly as §S2 diagnoses.  Invisibility:
`RegradeOf.w_coeff` (e★ = 1) exists as cited; `U31.bStage` (U31_gateReadsOf.lean:622)
literally sets `w := bw, wPrev := bw`.

**(b) Def 3.15 prime placement — column arithmetic independently recomputed.**  Layout
l.911 has ′ at 1-indexed codepoint column **52**; l.912 has the first ℓ at column **51**
(its subscript i at 52) and the second ℓ at column **59**.  The prime attaches to the
FIRST ℓ: exponent `ℓ′ᵢs(α) − ℓᵢu(α)` = the mode-C reading, exactly as §S7 states.  The
shared `/tmp/litunit/fgmn.txt` (sha256 `695412d2…fae1516`, matching §S0) is corrupted
exactly as described: Def 3.15 at its l.1238, the prime ORPHANED on bare l.1239 at
column 1 (no column information), the exponent line 1241 with both ℓ's unprimed —
placement unrecoverable there.  Genericity ranges verified in the print: Def 3.15
"For 0 ≤ i < r" (l.910), Def 3.16 "For 0 ≤ i ≤ r" (l.916), Def 3.18 "For 1 ≤ i ≤ r"
(l.994–995); I read l.865–1006 and found no side condition restricting i.

**(c) Row-A record arithmetic — recomputed by hand, exact.**  fA = X²+4X+28 = Φ₂+2⁴
(Φ₂ = X²+4X+12) = Φ₁²+24 (Φ₁ = X+2), so slots {0,2} with B₀ = 24, B₂ = 1.  Row-A tower
(d0=1,(e0,h0)=(1,1),(e1,h1)=(2,1)): w1(24) = v₂(24) = 3; γ₂ = e1·w1Φ1 + h1 = 2·1+1 = 3.
Corrected functional: slot 0 → 2·3+0 = 6, slot 2 → 2·0+2·3 = 6 ⇒ gam = 6, s0 = 0,
wSide = 2, pat = (1,1) = 1+y = ψ₁ (deg 1, nonzero constant — Cor 4.4(4) l.1089),
μ = ord_{y+1}(1+y) = 1, vtx = digit of d2[1] = 1.  Compiled: slot 0 → 2·6+0 = 12,
slot 2 → 6 ⇒ display [6,12], no single gam.  All match §S2/§S4 and the console record.

**(d) The repaired any-gam′ branch + support meter — semantics match the claim.**
`check_compiled_unsat`: violation iff `len(oldvals) ≤ 1` where `oldvals` = compiled
values `e·(e·vals[j]) + j·h` over supported stride slots — empty counts (vacuously
solvable) and ANY singleton counts (solvable by its element, recorded-gam or not): the
pass-1 false-negative branch is gone; GREEN certifies ≥ 2 distinct values, hence any-gam
UNSAT.  The meter tallies `len(oldvals)` per site BEFORE the branch.  The sealed
derivation re-checked: at a supported slot the corrected tie gives compiled value
`e·gam − j·h·(e−1)`; h = γ₂ > 0, e = e1 ≥ 2 on every roster row, so distinct supported
slots give distinct values; ≥ 2 nonzero digits per pattern is both argued (Def 3.18
strip + Cor 4.4(4) + nonzero leading digit, g1 ≥ 1 on all rows) and measured (meter min
key 2).  Direction of inference is sound: equality-subsystem UNSAT ⇒ full compiled
clause-(ii) UNSAT at the site's recorded data.

**(e) Rescoped R1/R4 — accurate to the code.**  `check_corrected` checks exactly
(i-a) lower bound, (i-b) equality-set = pattern-stride-set, (ii-support) nonzero + on
line at stride slots, (iii-window-length) `wSide % e = 0 ∧ wSide/e + 1 ≥ len(pat)` — no
σ.R residual-leg instantiation anywhere, exactly the REVISION-1 rescope ("NOT full
corrected-bundle `SideReads` satisfiability"); the sealed header rows stand as declared
historical record with the ADDENDUM superseding.  R4's from-print operator consumes
certified Tower STATE (`T.w1`, `T.res_digit`, `T.K1`, `T.z1`, keys/chain params) with
local recursion/exponent code only — the "differential falsifier" rescope is accurate.
Misread meter reconciled: rows pool 4 ring configs; instances with z₁ = 1 (e.g. row A at
p = 2, where K1 = F₂) cannot discriminate ǫ-modes, and the per-row counts 24–48 with
every row > 0 are exactly consistent with that structure.

**(f) Blast radius NOW + D0 — honest.**  Unit commits 303b11e/236d85c touch only
`docs/references/`, the note, `BRIDGE_ADJUDICATIONS` (flag queue), and
`verification/openmath/` — **no `.lean` file**; working tree clean.  The JuncForge
theorems verified in place: `juncforge_no_e2_junction` (JuncForge.lean:276, binds
`SideReads` by name, concludes ν.e = 1 at the row-A read), `juncforge_clauseIII_derivable`
(:578, pins hwP wPrev(24)=3 / hw24 w(24)=6 — the two-scale pins verbatim),
`juncforge_D0_instanceFalse` (:686, kills via B₀ = 0 vs `hpat0` — scale-independent, so
the §S3 re-key cannot resurrect it), `gate_glue_conditional` (GlueRun.lean:1161),
`DIterJunctionSupplier` (GlueRun.lean:875 — line as cited; docstring carries the
two-constant + fibration fence and the NOT-CYCLIC fence, matching §S6.2–3).  eq (14)
(l.1004) + R5 green (56 checks) confirm the source's own D0 degeneracy.

**(g) The §S3 proposal diff — applies verbatim.**  Machine-checked: every OLD line
occurs verbatim and UNIQUELY in HC2/Defs.lean (count 1 each); the NEW block differs
from OLD exactly at the `ν.σ.w →ν.σ.wPrev` sites and nowhere else; `σ.wPrev` is an
existing `Stage` field of the same signature (already used at Defs.lean:295), so the
edit is type-plausible.  Untouched-with-warrant items verified: the clause-(ii)
residual T-exponent is already at `ν.σ.wPrev` (:295); the recentering rider's two
`ν.σ.w` tokens (RecenterLiftSpec, Defs.lean:151, echoed in `junc_bundle`/
`juncforge_D0_instanceFalse`) are a lift-vs-key CURRENT-scale tie, not a window read.
`junc_bundle` (GlueRun.lean:260) and the supplier reference `SideReads` by name.

**(h) Spec gate + riders.**  JUNCFORGE_S2 §R3 charter and the four SYNTHESIS_PASS7 F1
riders located; the note folds all four ((i)→§S4/§S8, (ii)→§S7, (iii)→§S0, (iv)→§S5/§S6).
PIN-GEN-i is a named pin in TR3S3_2026-08-08.md stating the owed fresh-extraction leg,
as §S7 describes.  Rider (i)'s "corrected clauses instantiated numerically" is
discharged in the honestly-rescoped window/support form with the residual leg displayed
as owed (§S8/§S9) — disclosed, not papered over.

## 2. FINDINGS (quote-and-classify; ranked most severe first)

### GAP 1 — the application blast radius omits the DictIII mirror layer, which cannot survive the diff

§S3: "One definition changes: `SideReads` … No other clause, definition, or statement is
touched; `junc_bundle`/`ReadsOf`/`DIterJunctionSupplier` inherit textually unchanged";
obligation (b) lists consumers as "(U19–U25 projections, ReadsOf, GlueRun, JuncForge)".
Nowhere does the note mention `Scaffold/DictIII`: `SideClauseR1`
(Locality.lean:272 — docstring "**The (R1) side-support clause** — `MovesJ.SideReads`
clause (i), VERBATIM (`HC2/Defs.lean`)", body carrying the σ.w functional) with its
definitional tie `sideReads_r1 … := h.1` (:280), the σ.w-shape locality/transfer
theorems built on it (e.g. `sideClauseR1_transfer_iff`), and the Window.lean:553–558
harvest statement restating the clause-(ii) endpoint equalities at `ν'.σ.w`.  After the
in-place re-key, `sideReads_r1 := h.1` is a type error (clause (i) becomes the wPrev
shape while `SideClauseR1` keeps the w shape), so application NECESSARILY touches
other declarations, and the mirror definitions host the same mis-scaled functional the
note diagnoses — an undisplayed piece of both the defect census and the application
cost.  The generic grep-census obligation would catch it, but the note's displayed
radius is materially incomplete.

### GAP 2 — "statements unedited, meanings unchanged" for the JuncForge theorems is impossible under the in-place re-key

§S3(c): "the JuncForge theorems are NOT edited — they bind the old shape and become the
historical record of the mis-scale"; §S6.4: "statements unedited, meanings unchanged
(they bind the OLD clause shape)".  `juncforge_no_e2_junction` (JuncForge.lean:276)
takes `(hside : SideReads ν B Nd Φnext)` — it binds `SideReads` BY NAME, exactly the
mechanism §S6's own preamble relies on for the supplier ("inherits the corrected
`SideReads` textually unchanged").  Under the in-place diff an unedited statement
re-binds to the NEW clause: its meaning changes, its parity proof (clause-(ii) σ.w
equalities) cannot close, and — by the note's own §S4/§S6.1 — the re-bound statement is
expected FALSE once the queue-#9 junction instance exists.  Keeping the old-clause
record as compiled theorems requires an old-shape copy or a move, i.e. edits the note
rules out.  The intended CONTENT (the theorems remain true of the old clause shape) is
mathematically right; the displayed mechanism is self-contradictory.

### GAP 3 — "exactly FOUR tokens" miscounts the displayed three-token diff

Title: "a four-token `SideReads` re-key"; §S3: "`ν.σ.w` → `ν.σ.wPrev` at exactly FOUR
tokens" (also the sealed commit message 303b11e: "four-token w -> wPrev re-key").
Machine count: the OLD block (and the compiled `SideReads`) contains exactly THREE
`ν.σ.w` occurrences (Defs.lean:285, :287, :292 — two in clause (i), one in clause
(ii)'s functional-equality leg), and the NEW block replaces exactly those three; no
fourth site exists in the definition (line 295 is already `wPrev`; the only other σ.w
tokens in the file are RecenterLiftSpec's, explicitly untouched).  The displayed diff
is authoritative, verbatim-appliable, and internally consistent — but the note's own
count of its central artifact is wrong, in the title, §S3, and the commit record.

### GAP 4 — §S8's "re-quoted" rerun output block is an edited render, not a verbatim quote

§S8 introduces the block as "REVISION 1 rerun output (console saved at
`fgmn_rederivation_rerun_r1.txt` …)" and the header says "output re-quoted in §S8".
Against the artifact (and my byte-identical re-execution): the note collapses
`obs   0` → `obs 0`; drops "from-print" from the misread-meter label and the quote
marks/spaces in both meter dicts; renders `pat=[((1,),), ((1,),)]` as `pat=[1,1]` and
`vtx_digit=(1,)` as `vtx_digit=1`; merges `TOTAL checks 1093  elapsed 0.6s` +
`VERDICT: ALL GREEN` into one line, dropping the elapsed field; drops the four ring
progress lines.  Every number and verdict is identical and the flattenings are
semantically faithful (the tuple encodings are the K1-element representations of 1) —
but in a unit whose subject is transcription fidelity, a block presented as output
should be verbatim or marked as edited.

**Non-counted nit:** §S1(C) cites Cor 4.4(2) as "l.1085–1087"; the quoted sentence sits
at l.1086–1087 (l.1085 is item (1)).  The cited range contains the quote; no content
error.

## 3. VERDICT

The mandatory execution leg agrees exactly (console byte-identical, JSON byte-identical,
pins verified, extraction independently regenerated byte-identical from the pinned PDF).
The confirmed perimeter of passes 1–2 (parent-scale diagnosis, row-A arithmetic,
PIN-GEN-i column leg, D0/blast-radius present-tense honesty) independently re-verifies,
and the REVISION-1 repairs (any-gam′ branch, R1/R4 rescopes, prover-side re-execution)
are real and accurate to the code.  No critical error found.  Four gaps, all in the
note's self-description and application-plan display, none touching the mathematical
diagnosis, the numerics, or the proposal diff's verbatim applicability.

FGMN-P3 FINDINGS: 0 critical, 4 gaps
VERDICT: GAPS-ONLY

— FGMN pass 3 (Fable, fresh context), 2026-08-08 (wallclock 2026-08-03).
