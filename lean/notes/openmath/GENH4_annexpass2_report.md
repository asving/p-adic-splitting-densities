# GENH4 ANNEX-PASS #2 — HOSTILE VERIFIER REPORT (scoped: the ANNEX STACK = PE5 + R + R2, post-R2 text)

**VERDICT: CLEAN at annex-stack scope — 0 CRITICAL, 0 GAP, 3 MINOR
(all display/transcription slips whose conclusions survive
machine-verified; none consumed, none load-bearing). The annex stack
takes its FIRST clean mark: the annex-acceptance count moves
0/2 → 1/2.** GAP-1's repair (ANNEX R2) survived every attack: the
corrected clause (c′) was re-derived from scratch (all three u₀
branches, the band-zero-membership claim, both 2w = N existence
arguments) and then machine-exercised on SIX fresh cells — including
the first machine contact of the 2w = N leg anywhere (both residue
characteristics, inert witnesses found exactly where the trace/coset
arguments put them) and the first non-prime-q (q = 4, W(F₄)) exercise
of the consumed clause GENH4-7′(b) — GREEN, 0 violations. All three
annex machine legs re-ran isolated (two BIT-IDENTICAL, one
elapsed-only); every byte-freeze verified 3-way; the R2 withdrawal
quotes are verbatim against the frozen ANNEX R text.

Scope and provenance: target = the POST-R2 annex stack of
`GENH4_PROOF_2026-08-08.md` — ANNEX PE5 (lines 1209–1477, baf05ed),
ANNEX R (1478–1885, b10a5a7), ANNEX R2 (1886–end, 760d20f). Stack
arc: pass #1 (`GENH4_annexpass_report.md`, a8dec16) returned NOT
CLEAN — 0 CRITICAL + 1 GAP (GAP-1: R2's N-even band-pinned +
refine-deeper legs machine-refuted) + 4 MINOR + 2 remarks; ANNEX R2
withdrew the two refuted legs, restated clause (c) as (c′) at the
key level, and landed the four minors + the Remark-1 rider. This
pass attacks the post-R2 text with fresh context and zero prior
stake; quote-and-classify, fix nothing. The frozen accepted body's
2/2 is NOT at stake and nothing here touches it. Read for context:
GENH4-1F/S2.3/GENH4-CAP/GENH4-3 (S4), GENH4-2/S3, S6.1/S6.3, S7, the
pass #1 report, and `CODEX_GENH4RAT_2026-08-09.md`.

## S1. Findings (3 MINOR; quoted and classified, nothing fixed)

### MINOR-1 — R2's provenance paragraph mis-pins the fresh-leg results artifact: displayed `71535780…`, actual md5 `7153578c…`

**Quoted (ANNEX R2, provenance):** "Machine support: the annex-pass
fresh leg `verification/openmath/genh4annexpass_fresh.py` (md5
`f044c491…`, output `bf8f94f5…`, results `71535780…`, committed at
fed3cff; GREEN, 0 violations)".

**Failure scenario:** a re-verifier who checks the displayed 8-hex
prefix against `genh4annexpass_fresh_results.json` gets a MISMATCH —
the committed file's md5 is `7153578c0948d773830f58c193dcb62d` (8th
nibble c, not 0) — and must chase provenance to rule out artifact
replacement. Ruled out here: the blob at fed3cff (the commit R2
itself cites, landed BEFORE R2's 760d20f) already has md5
`7153578c…` == HEAD, and the file has exactly one commit in its
history — so R2 transcribed the last displayed character of a pin it
was reading correctly. The script and output pins (`f044c491…`,
`bf8f94f5…`) verify as displayed. Transcription slip in a pin
display; the machine record itself is intact.

### MINOR-2 — (c′)'s disc-automatic parenthetical is false in EQUAL characteristic 2; the conclusion survives via disc = A₁²

**Quoted ((c′) proof, ANNEX R2):** "disc ≠ 0 is automatic at both
witnesses (v(4A₀) = u + 2v(2) is odd either characteristic,
≠ 2w = v(A₁²), so v(disc) < ∞)".

**Failure scenario:** in equal characteristic 2 (the F_q[[t]] ring
type at q even — half of every q = 2 cell's coverage, and (c′)(i)
claims its pair "both characteristics"), 4A₀ = 0: v(4A₀) = ∞, not
"u + 2v(2) odd" — the displayed justification evaluates to nonsense
exactly there. The CONCLUSION survives on a one-line different
route: disc = A₁² − 4A₀ = A₁² with v(disc) = 2w < ∞ (A₁ ≠ 0 since
dv(A₁) = w is pinned finite). In mixed characteristic 2 the display
is right (v(2) = 1, u + 2 odd); in odd characteristic both types
right (v(2) = 0, u odd). Machine: this pass's FAeq leg verified
disc ≠ 0 (exact F₂[t] gcd) AND the (c′)(i) σ-contrast (0 vs 4 roots
in F₄[[t]]) on the F₂[[t]] witnesses at (2,7,2) and (2,12,2) — the
pair does differ in equal characteristic, as (c′) concludes. Display
slip in a proof parenthetical; no consumer moves.

### MINOR-3 — R2's machine-instance sentence inflates FR4's band-zero contrast count: "(6/6 at each cell)" — the truth is 6/6 TOTAL, 3 per cell

**Quoted (ANNEX R2, consumption-status paragraph):** "at the two FR4
cells the {(2,2)} side is carried by the band-pinned strata (24/24)
and the {(1,2),(1,2)} side by band-zero members of the same keys
(6/6 at each cell)".

**Failure scenario:** a reader auditing the FR4 artifact looks for 6
contrast members per cell and finds 3 (the committed
`genh4annexpass_fresh.py` builds contrastC = 3 pins at (2,8,2) + 3
pins at (2,10,2); its output line reads "band-zero contrast members
of the SAME keys: 6/6" — total). Pass #1's own phrasing ("6/6 at
both cells") was ambiguous-but-true; R2's "at each cell" asserts a
per-cell count that is false. Substance intact: ≥ 1 (in fact 3/3)
contrast member per cell is all the key-level cross-stratum pair
needs, and the 24/24 and 9/9 numbers in the same sentence are exact.
Transcription slip in a machine-record display; the (c′) instance
pattern itself is machine-true (re-confirmed by this pass's isolated
FR re-run and extended by the fresh legs below).

### Notes (no grade)

* **Note 1 (FB1's disc-zero '1sq' member, disclosure).** At the
  fresh (3,10,1) cell, the u = 2w member with S₁ = 2, d₀ = 1 has
  EXACT disc 0 (A₁² = 4A₀ on the nose) — PARI sentinel, correctly
  outside every clause's disc ≠ 0 antecedent; the two other decided
  '1sq'-adjacent members read {(2,2)} after refine. (c′) claims
  nothing about '1sq' members; recorded ungated, no conflict.
* **Note 2 (pass #1's GAP-1 wording, for the record).** Pass #1's
  failure-scenario-2 sentence "σ = {(2,2)} CONSTANT, in BOTH
  characteristics (12/12 machine)" attaches the machine count to
  both characteristics while FR4's 12 lifts were PARI = mixed
  characteristic only (the equal-char half is the derivation, which
  is value-layer and characteristic-blind). R2 did NOT inherit this
  (its 24/24 sentence makes no characteristic claim). Pass #1's
  report is not this pass's target; noted for hygiene only.

## S2. The attack log (each charge executed; none broke GAP-or-worse)

1. **The corrected (c′), re-derived from scratch (the never-attacked
   R2 text).** (i) The u₀ := least odd height ≥ max(N, 4k+1)
   trichotomy is EXHAUSTIVE (N odd ≥ 4k+1 / N even ≥ 4k+2 / N ≤ 4k
   — no fourth case: N even = 4k+1 is impossible) and all three
   displayed inequalities re-derive: N odd ≥ 4k+1 → u₀ = N < 2w;
   N even ≥ 4k+2 → u₀ = N+1 ≤ 2w−1 (2w > N, both even → 2w ≥ N+2);
   N ≤ 4k → u₀ = 4k+1 ≤ 2w−1 from w ≥ 2k+1, which is GENH4-1F's
   stage-initial node v₁(A₁) ≥ 2k+1 (floors only rise — the S2.3
   cite checks). Both witness heights are realizable at a band-zero
   member (≥ max(N, 4k+1) → in GENH4-1F's budget AND a lift
   position; the 2w+1 witness: 2w+1 ≥ 4k+3 > 4k+1, > N). The legs
   consumed are S7's F-RAM (u odd ≤ 2w → {(2,2)}) and F-2SIDED
   (u > 2w → {(1,2),(1,2)}) bullets, value-layer only — checked
   against S7 as frozen. HELD (MINOR-2 is a parenthetical inside
   this proof, not the chain).
2. **The band-zero-membership claim.** "Every leaf key contains
   band-zero members" checks against the key structure: S6.3's
   genre-F UND law prices deep₀ = q^{k−1} as a FREE factor INSIDE
   the key (per (ψ, H₂)), so the key's member set sweeps all band
   values including zero; at k = 1 the band is empty. Verified in
   the sealed `law_F` and both fresh typings (the annex-pass leg's
   my_law_F multiplies `band` into the UND key). HELD.
3. **The 2w = N leg's existence citations.** R2.M2's coset count
   re-derived line-by-line: the negation covers exactly the cosets
   through realizable s = S₁²/4 (S₁² sweeps the nonzero squares Sq:
   squaring 2-to-1 onto Sq, 4 a nonzero square); U := union of
   cosets meeting Sq satisfies Sq ⊆ U ⊆ Sq ∪ {0} and q | |U|; both
   branches contradict (|U| ≡ ±2⁻¹ mod q, q odd). SOUND — and
   machine-witnessed fresh (FB1: 8 inert members at (3,10,1)). The
   char-2 trace argument (pass-verified per R2.REM) spot-checked
   (Artin–Schreier criterion, trace transitivity, Frobenius sweep,
   kernel count q of q²) and machine-witnessed fresh (FB2: inert
   exactly at S₁ ∈ {ȳ, ȳ+1}, the τ ≠ 0 members; the τ-degenerate
   S₁ = 1 member reads {(1,2),(1,2)} — the honest-scope sentence's
   exact geography). HELD.
4. **The transport-error display (dv(A₁′) forced / dv(A₀′) capped),
   re-derived at (2,10,2).** λ = ŝ²π¹⁰ + ŝπ⁵A₁: the second term has
   height 5 + w = 12, so corrections land at {10} ∪ {≥ 12} and the
   height-11 band letter (d₁ ≠ 0, ȳ-component — un-killable by any
   a₀-side correction, GENH4-2(F)) survives: dv(A₀′) = 11 forced,
   11 odd ≤ 2w → RAM(11) → {(2,2)} — matching FR4's 6/6 exactly
   (isolated re-run this pass). The dv(A₁′) fork (= w equal-char via
   s₁ = √S₀ ∈ F_q carry-kill; = dμ+1 mixed via the 2w_re revival)
   matches pass #1's FR4 derivation verbatim, and BOTH forks land in
   RAM(11)'s antecedent (11 ≤ 12 and 11 ≤ 14). HELD.
5. **Withdrawal hygiene.** The two refuted displays are
   QUOTED-AND-WITHDRAWN, not edited: both R2.G1 quotes occur exactly
   TWICE in the note (frozen ANNEX R original + R2.G1's quotation;
   whitespace-normalized string match), and the byte-freeze prefix
   md5 `863c2160…` (113,738 bytes) verifies 3-WAY (working file =
   HEAD blob = ca3754d blob = 760d20f blob). The elisions in the
   refine-deeper quote drop only the census-nonemptiness
   parenthetical and the post-conclusion sentences — nothing
   meaning-bearing for the withdrawal. HELD.
6. **R2.M1–M4 + R2.REM, one by one.** M1: the height-h letter is
   structurally zero for h < 4k+1 on BOTH components (a₀ at h <
   4k+1; a₁ at h−k < 3k+1) — the corrected sweep {max(N,4k+1), …}
   re-derives, the band-pinned range is nonempty (band heights m ≥
   max(N+1, 4k+1)), and (b)'s immunity is exact (SPLTAIL forces
   N ≥ 4k+3; u = N lifts exercised at C5/FR2A/FR2B as cited, and
   now also at FC's q = 4 cell). M2: sound (charge 3). M3: the
   degenerate digit is the single d₀ = S₁²/(4c) WHEN that value lies
   in F_q^× (else none) — "at most one" exact; pair survives at
   q−2 ≥ 1 non-degenerate digits, q odd ≥ 3; char-2 exactness
   confirmed at FR5's cell (residue char 2). M4: the corrected
   inventory is now accurate (hypothesis + (a)-parenthetical
   replaced, band cap ADDED, (c)-proof REPLACED, (b) untouched) —
   checked against R1.0/R1.1/R2.G1. REM: Remark 1 rider matches
   pass #1's Remark 1; Remark 2's citation status ("pass-verified")
   is true. ALL HELD (MINOR-1/-3 sit in R2's provenance and
   machine-instance displays, not in M1–M4).
7. **Cross-annex coherence (GENH4-7 → 7′ → (c′)).** Each
   supersession states itself: PE5's GENH4-7 is superseded by R1's
   GENH4-7′ (R1.1 re-points THEOREM GENH4.C's F-SPLTAIL leg; the
   ANNEX R what-does-not-move box names it); 7′'s clause (c) and
   R2's per-stratum display are replaced by (c′) (R2.G1 names both
   targets; the frozen "(re-proved per band stratum in R2 below)"
   pointer inside 7′ is covered by the named replacement). Repo
   grep: every "GENH4-7" site outside the note (PROJECT_STATE,
   BRIDGE_ADJUDICATIONS, GENIND note/report, the rat scaffold, the
   leg docstrings) is an arc RECORD, not a consumer; W-12.D's one
   consumption path routes through GENH4.C's F-SPLTAIL leg =
   7′(b), whose conclusion is byte-identical across the chain. NO
   site consumes a superseded form. HELD.
8. **Free hunt.** GENH4-BOX-1's R2 append checked against pass #1's
   actual verdict/commits/numbers (all exact, including "6/6 + 6/6"
   = refine-path + contrast, which is the correct TOTAL reading);
   the what-does-not-move box's five named targets + one rider
   reconcile exactly with GAP-1 + the four minors + Remark 1; R2's
   FR5 sentence ("both sides live at one band-pinned stratum,
   9/9") matches the artifact; the (c′)(ii) u > 2w realizability
   parenthetical ("m ≥ N+1 > 2w = N when the band is pinned")
   re-derives from the band heights. Findings: only MINOR-1/-2/-3
   above.

## S3. Machine legs — pins, isolated re-runs, instrument audit

**Pins at HEAD (2026-08-09).** Byte-freezes: R2's prefix
`863c21600fa48ae755d0d87b77b894d4` over the first 113,738 bytes
verified 3-way (working tree = ca3754d = 760d20f); ANNEX R's
`a584cb3e…` over 89,530 bytes verified. Script seals:
`genh4annexr_supp.py` d1d5288f ✓, `genh4annex_supp.py` bcb87498 ✓
(the disclosed post-smoke state), `genh4annexpass_fresh.py`
f044c491 ✓, its output bf8f94f5 ✓, its results — actual
`7153578c…` vs R2's displayed `71535780…` = MINOR-1 (blob at
fed3cff == HEAD, single-commit history: transcription, not
tampering). The 5 sealed-artifact pins inside both annex legs'
PINS dicts re-verified against the committed files.

**Isolated re-runs** (fresh /tmp sandbox; pinned artifacts + the
traced transitive import closure copied in; nothing sealed touched):
* PE5 leg `genh4annex_supp.py`: GREEN, exit 0 — artifacts
  **BIT-IDENTICAL** to committed.
* R leg `genh4annexr_supp.py`: GREEN, exit 0, 0 violations —
  artifacts **BIT-IDENTICAL** to committed.
* Annex-pass FR leg `genh4annexpass_fresh.py` (R2's cited
  adjudication, FR4/FR5): GREEN, exit 0, 0 violations — diff vs
  committed = **elapsed-only** (0.3s → 0.4s in both artifacts).

**Instrument audit.** The FR leg's σ oracle (PARI factorpadic +
per-factor nfinit/idealprimedec) is the same GP routine as the
sealed battery's GH-SIGMA; this pass's fresh leg REIMPLEMENTED the
member constructions independently (same conventions, different
cells and code paths) and added two oracle routes the arc had never
used: the F₂[[t]] Panayi/gcd route driven from a NEW script (import
of the sealed module's functions, fresh inputs), and a W(F₄)
relative-σ route (absolute-octic idealprimedec with the inert-2
f-halving) that shares nothing with factorpadic's code path.

## S4. Fresh route — `genh4annexpass2_fresh.py`, sealed BEFORE run (510c0cf), GREEN 0 violations exit 0 (9049823)

Six cells, all untouched by any prior leg (PE5: k = 1 rows; R:
(2,11,2); pass #1: (2,15,3)/(3,11,2)/54-grid/(2,8,2)/(2,10,2)/
(2,9,2)):
* **FA — (c′)(i)'s u₀ construction, one cell per branch.**
  FA1 (2,7,2), the DELICATE N ≤ 4k branch (max(N,4k+1) switches:
  u₀ = 9 = 4k+1 > N; the A₀ slot string is EMPTY): 18/18 PARI
  (u₀-lifts incl. a b₁-route → {(2,2)}; 2w+1-lifts →
  {(1,2),(1,2)}), w ∈ {5,6}. FA2 (2,12,2), N even ≥ 4k+2 (u₀ =
  13): 9/9 incl. a band-pinned u = 13 = m RAM member. FA3
  (3,13,2), N odd ≥ 4k+1 (u₀ = N): 8/8, odd q. EQUAL-CHAR
  differ-leg (F₂[[t]], exact disc + Panayi roots): 4/4 — the
  (c′)(i) pair differs in BOTH characteristics at (2,7,2) and
  (2,12,2) (RAM: 0 roots in F₄[[t]]; 2SIDED: 4 in F₄[[t]], 0 in
  F₂[[t]]).
* **FB — the 2w = N leg (c′)(ii): FIRST machine exercise anywhere,
  both residue characteristics.** FB1 (3,10,1) char odd: all 8 pin
  letters × {d₀ = 1, 2} u = 2w reads + u = 11 lifts; the in-script
  F₉ residual computation (disc = S₁² − d₀; square → '11' →
  {(1,2),(1,2)}; non-square → '2' → {(1,4)}) matched PARI 20/20 on
  the decided reads; INERT continuations EXIST (8 members — R2.M2's
  count argument machine-witnessed) each with the same-member
  u = 11 lift {(1,2),(1,2)}: the (c′)(ii) differing pair at ONE
  member. FB2 (2,14,2) residue char 2: the trace-leg predictions
  (inert ⟺ Tr(1/S₁²) = 1 ⟺ S₁ ≠ 1) matched PARI 9/9 — INERT
  {(1,4)} at S₁ ∈ {ȳ, ȳ+1}, the τ-degenerate S₁ = 1 member
  {(1,2),(1,2)} on every lift, A₀ = 0 corners included.
* **FC — non-prime q, the CONSUMED clause.** (4,11,2) over
  K = ℚ(y)/(y²+y+1) (2 inert, residue field F₄; φ = x² + 4x + 16y,
  ψ = t² + t + ω irreducible): 36/36 members (3 pins × 3 band
  values × 4 lifts incl. A₀ = 0 and u = N) read RELATIVE σ over
  K_v = {(1,2),(1,2)}; u ≥ N and u ≤ m verified on the valuation
  layer; wrong-floor teeth (b₀@9, ± band digit) FIRED 2/2 →
  {(2,2)}. GENH4-7′(b) is not a prime-q accident.
* Disclosures: no smoke corrections were needed on this leg (first
  run GREEN); FB1's exact-disc-0 '1sq' member recorded (S1 Note 1).

## S5. Grade line

**CLEAN at annex-stack scope: 0 CRITICAL + 0 GAP + 3 MINOR (+2
notes). Nothing GAP-or-worse survived verification. The annex stack
takes its first clean mark: the annex-acceptance count moves 0/2 →
1/2 (one more model-diverse clean pass required for stack
acceptance, per the standing bar).** The frozen accepted body's 2/2
is untouched. Owed for a future dated rider (does NOT block the
clean mark; all three are display-layer with conclusions
machine-verified intact): fix the results-pin transcription
`71535780…` → `7153578c…` (MINOR-1); re-route (c′)'s disc
parenthetical through disc = A₁² in equal characteristic 2
(MINOR-2); correct "(6/6 at each cell)" → "6/6 total, 3 per cell"
(MINOR-3). Report artifacts:
`verification/openmath/genh4annexpass2_fresh.py` + output/results
(sealed 510c0cf before run, artifacts 9049823); isolated re-run
sandbox in /tmp (session-local).
