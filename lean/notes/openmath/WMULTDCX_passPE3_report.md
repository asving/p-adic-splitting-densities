# WMULTDCX-PE3 — round-3 hostile content verification (fresh context)

Object: `lean/notes/openmath/WMULTDCX_2026-08-08.md` at commit **a0e266c**
(the W-r2 text; confirmed via `git log -1 --format=%h -- <file>`; working
tree = commit, diff empty).  Arc: round 1 PE1 NOT-CLEAN 1C/2G+2n; round 2
PE2 GAPS-ONLY 0C/2G+2n; W-r2 applied the PE2 remedies (diff 03635d0 →
a0e266c re-read hunk by hunk: exactly five hunks — the S0 trailer pin, the
W-D6 gloss pin, the S6 fence replacement, the (SURV) box gloss, the W-r2
tail record — NO lemma statement or proof body touched).  Charge: (1)
hostile discharge check of the three W-r2 remedies; (2) full spine sweep
on the repaired text; (3) machine re-run + 2 fresh divergence spot-checks;
(4) fresh eyes.  Role: verify only; nothing fixed.  New file added by this
pass: `verification/openmath/wmultdcx_pe3_ext.py` (spot instrument riding
PE1's independent machinery read-only, on two instances no prior pass
audited in detail).

## Part A — machine section (charge 3)

* **Pins.**  `wmultdcx_derive_checks.py` md5
  bea1a43d619a3c91a9a0b2f32c0920c0, output
  2b5395adca632fa0c2e3564db12e668d, results
  000ac228dc4aa4ea6309cf24d0a648ec — all three MATCH the note's S0 and
  dependency-line pins.  Stress chain on disk unchanged (15315cca… /
  2ff1cdc7… / 41cbf2f1… — match the PE1/PE2-recorded pins).  Committed
  artifacts untouched by this pass (all runs in /tmp/pe3_rerun sandbox
  copies; md5s re-verified after).
* **Read-only re-run.**  `wmultdcx_derive_checks.py` re-executed in the
  sandbox: exit 0, all 11 DCK families GREEN [0 violations]; output
  IDENTICAL to the committed output modulo elapsed/per-tower timings;
  results JSON IDENTICAL modulo `elapsed`.  Counters reproduce the note
  verbatim: 412 rows (= sealed selection), 858 Q¹ cells, 112
  beyond-floor, 801 junk-free, minnz 286/0, stock 302 ok / 0 fail,
  greedy 218.
* **Censuses re-computed from the committed JSONs (independent script,
  this pass).**  Derive results: 412 = 286 live + 126 dead; **every one
  of the 126 dead rows has ncells = 0** (126/126 zero-cell — the S9/box
  absence datum); all 858 cells sit on live rows; every live row has
  ≥ 1 cell.  **Path existence ⟺ the e₀-clause (c_{m−1} ≥ k): 0
  mismatches on all 412 rows** — the S6 W-r2 bracket's battery datum
  verified, and the four g₀ = 2 towers (W3G2A/W3G2B/W3G2P5/XM3B, 110
  rows) are in the selection, so "including the four g₀ = 2 towers" is
  accurate.  (clause ⟺ live also 0 mismatches; with the zero-cell census
  this gives path existence ⟺ live ⟺ clause on every probed row.)
  Stress JSON: 72 PID-MAX divergence records, none joinable to a dead
  row (dead rows carry zero cells, a fortiori zero nonzero parts).
* **Spot re-derivations (2 sealed divergence records; both towers absent
  from PE1's 8-instance list AND from PE2's 2).**  Instrument:
  `wmultdcx_pe3_ext.py`.  Hand derivations FIRST (this report), machine
  second:
  - **W3G2B (1067,1067)** (reads (2,1,2),(3,2,1),(2,3,1),(2,1,1); m = 3,
    g₀ = 2, d₀ = 2 — a g₀ ≥ 2 tower never spot-audited).  Hand, with the
    engine's weight recursion w₁Φ₁ = e₀g₀h₀, w_{j+1}Φ_{j+1} =
    e_jg_jγ_{j+1}: γ-chain 1, 14, 87, 349; u-chain u₃ = 349, s₃ = 1
    (349 odd, h₂ = 3), u₂ = (349−87)/2 = 131, s₂ = 1 (131 ≡ 2, 2s ≡ 2
    mod 3), u₁ = (131−14)/3 = 39, s₁ = 1.  Split of 1067: s₄ = 1
    (TRACK), β₃ = 533−174 = 359, s₃ = 1, β₂ = 178−42 = 136, s₂ = 2,
    β₁ = 44−8 = 36, s₁ = 0, tail 18; σ = (0,4,2).  pool₁ = 1, c₁ = 0;
    pool₂ = 4+1+0 = 5, c₂ = 1; D = 3, k = 1; clause 3+1 ≥ 4 live.
    P-divisor pools (P₀ = 4, P₁ = 3): ĉ = (0,1) — the level-1 divergent
    mass MUST ride an excess channel.  Machine: HAND-DERIVATION TIE OK
    (u/su also re-checked against the sealed stress JSON tower record —
    exact); maxnz = [1,1]; **sealed record (level 1: 1 > 0) CONFIRMED**;
    W-D4/W-D6/W-D6c 0 fails; 3 beyond-floor cells, all on the live row.
    Cell dump verified the mechanism EXACTLY: the two d-cells are
    jD = (1,1,1) (principal) and jD = (3,1,1) = (s₁(u₁)+1·e₀, s₂(u₂),
    s₃(u₃)) — the W-D2(iv) t-inventory verbatim at t ∈ {0,1}; every
    π₁ = 1 cell carries dmp ≠ 0 or the t = 1 d-cell; the dump-free
    principal cells sit at π = (0,1) = ĉ exactly.  W-D4 hand-checked:
    π₂ = 1 = k + 2r + j₂ with r = 0, j₂ = 0 on all three pc = [1,1,2]
    cells ✓.
  - **W4DEEP (1483,1483)** (reads (3,1,1),(2,1,1),(2,1,1),(2,1,1),
    (2,1,1); m = 4 — never in a detailed list).  Hand: γ-chain 1, 7, 29,
    117, 469; u = (44, 88, 176, 469), su = (2, 0, 0, 1); split of 1483 =
    (2,1,1,1,1), tail 12, σ = (4,2,2,2); pools → cs = (2,2,2); D = 3,
    k = 1, clause 5 ≥ 4 live.  W-D7(i) hand-checked: a = (1,1,1),
    r = (1,1,1), b = (1,1,1); a+b = (2,2,2) = cs ✓; (STK): σ₄+a₃ = 3 ≥ 2
    ✓; second-exit stock 1+1+1 = 3 ≥ 2 ⟺ clause ✓.  Machine: HAND TIE
    OK (u/su tie the sealed JSON exactly); maxnz = [3,2,2]; **sealed
    record (level 1: 3 > 2) CONFIRMED**; W-D4/W-D6/W-D6c 0 fails; 2
    beyond-floor cells, both pc = [3,2,1,2] riding dmp₀ = 3 (dump
    channel, principal d-cell); the W-D7 greedy cascade cell is visible
    at pc = [2,2,2,2], dmp = 0, ncorr = 0, principal — the (STK) ∧
    clause maximizer on the nose.
  PE3 SPOT VERDICT: ALL CONFIRMED (exit 0).
  (Transcription remark, not a finding against the note: my first W3G2B
  hand chain used a g-free weight recursion and MISSED the sealed
  u-chain; the correct recursion carries g — w_{j+1}Φ_{j+1} =
  e_jg_jγ_{j+1} — and with it the hand chain ties exactly.  PE1's report
  prose lists W3FMID's reads as "(2,1,1),(1,1,1),(2,1,2 top),(2,1,1)";
  the committed roster line 532 has all-g = 1 reads [(2,1,1),(1,1,1),
  (2,1,1),(2,1,1)] — a slip in PE1's REPORT transcription only (PE1's
  arithmetic used the correct all-g = 1 values; P = [2,1,2] there is the
  P-vector).  The note itself is untouched by this.)

## Part B — the three W-r2 remedies, hostile discharge check (charge 1)

* **(a) PE2-G-1, the two attainment pins — the W-D6 gloss DISCHARGED;
  the S0 sites discharged FOR THE CLAUSE, with a residual scope
  under-display of the same genre (finding G-1).**  The W-D6 gloss now
  reads "the S6.1 floors CAP the dump-free promotion counts (attainment
  of the max is W-D7(iii)'s clause-pinned statement, (STK) ∧
  D + c_{m−1} ≥ 2e_{m−1})" and sits under the lemma's own "Under (H3)
  with g₀ = 1" header — accurate to exactly what W-D6 proves (cap ≤)
  and consistent with W-D7(iii) as proved (attainment under (STK) ∧
  clause at (H3) ∧ g₀ = 1): fully pinned ✓.  The S0 trailer now carries
  "on the clause-satisfying rows ((STK) ∧ D + c_{m−1} ≥ 2e_{m−1} — the
  same pins as above; on clause-failing rows only the cap ≤ holds and
  the max may be over the empty set)" — the clause pin PE2-G-1 demanded
  is present and accurate; the empty-max caveat matches the 126/126
  zero-cell census ✓.  Residual: neither S0 site displays the (H3) ∧
  g₀ = 1 scope that the attainment ALSO consumes — see G-1.
* **(b) PE2-G-2, the S6 fence replacement — DISCHARGED.**  Genre grep
  over the full note ("no … argument can", "irreducibly", "provably
  not", "not closable", "cannot be closed", "impossib", "can never"):
  exactly 4 hits, ALL inside labeled withdrawal brackets/records (S6
  W-r2 bracket quoting the withdrawn sentence; S9 W-r1 bracket; the
  (SURV) claims row; S11) — no surviving ∀-over-arguments or
  impossibility claim anywhere in the live text ✓.  The replacement's
  positive content re-verified: "the W-D dump-free machinery does not
  produce the e₀-divisor at g₀ ≥ 2 (its base divisor there is P₀ =
  e₀g₀)" is exactly W-D6 as proved ✓; the battery datum (path existence
  ⟺ e₀-clause, all 412 rows incl. the four g₀ = 2 towers) re-computed
  from the committed JSON — 0 mismatches ✓ (Part A); "EVIDENCE that a
  counting/emptiness argument may yet reach the divisor; whether it
  does is part of the open (SURV)/(EMPTY) question, not settled either
  way here" — honest, coherent with the S9 (EMPTY-(m+1)) display (which
  stays CONJECTURE-graded, "measured, not derived on any class") ✓.
  Fence F2 unchanged and consistent with the replacement ✓.  One
  cosmetic residue in the RETAINED pre-repair sentence: see N-2.
* **(c) PE2-n, the (SURV) box gloss — DISCHARGED, and the box remains
  exactly the law's residual.**  The box now reads "deadness = their
  absence or cancellation (on every probed instance: ABSENCE — 126/126
  zero-cell dead rows; the (EMPTY-(m+1)) route targets exactly this)".
  Precision check: given W-D4 (all Q¹ cells at depth ≥ max(k,0)),
  Q¹ = 0 ⟺ the depth-≥ max(k,0) parts are absent or cancel — the
  disjunction is exhaustive and no longer vacuous-compatible-by-
  omission; the absence datum is explicitly instance-labeled ("on every
  probed instance") ✓.  The (i)/(ii) display itself is byte-unchanged;
  PE1's verification of "EXACTLY LAW-DCX-(m+1) minus the proved layers"
  (locus clause automatic on TRACK) carries over ✓.  Box = the law's
  residual given W-D4: intact.

## Part C — spine sweep on the repaired text (charge 2)

* **W-D0–W-D7 chain.**  The W-r2 diff touches no lemma statement or
  proof body (five hunks, all display/record layer — re-read hunk by
  hunk).  PE1 re-derived every lemma with a fresh instrument (set-equal
  72, 28-edge hand audit); PE2 re-derived W-D7(i)/(iii), W-D4's
  specialization, W-D6's induction, W-D2(0); this pass independently
  re-checked: the W-D4 rearrangement (LED_{m−1} with dmp = 0,
  j(D) = s_m(u_m), cons = (2+r)e_{m−1} ⟹ π_{m−1} = k + e_{m−1}r +
  j_{m−1}) ✓; the W-D6 induction (π_lP_{l−1} ≤ cons_{l−1} ≤ σ_l +
  s_l(u_l) + π_{l−1}, floor monotone, ĉ_l ≤ c_l from P ≥ e) ✓; the
  W-D7(i) carry-split identity (algebraically + by hand on W4DEEP,
  Part A) ✓; W-D2(iv)'s t-inventory machine-witnessed on a fresh
  g₀ = 2 instance (W3G2B: jD = (1,1,1)/(3,1,1) = t ∈ {0,1} exactly)
  ✓; the (EMPTY-(m+1)) reduction re-derived once more (W-D4 forces
  π_{m−1} ≥ k > c_{m−1}, i.e. beyond-floor at the top; W-D6 excludes
  dump-free principal; W-D6c leaves exactly the two channels the
  sufficient statement excludes) — VALID at (H1)–(H2) as displayed ✓.
* **PID† assembly.**  (a)–(e) match their lemmas; (b) carries
  (H3) ∧ g₀ = 1 + (STK) ∧ clause + the empty-max caveat ✓.  Nothing
  graded PROVED consumes (SURV) or (EMPTY): re-checked every claims-row
  consumption column and every proof body on the r2 text — the S4(b)
  minnz census and S5 depth-0 remark stay marked "input to S9, not a
  proved claim"; the S6 W-r2 bracket's battery datum is marked
  EVIDENCE; the S7 "Reading" paragraph assigns deciding-ness to
  (SURV-(m+1)) explicitly ✓.
* **Refutation section.**  Row 11c literal stays REFUTED (sealed
  d3950f2/d774ecb), mechanism W-D6c 112/112; my two fresh instances
  exhibit the channels concretely (dump mass on both; the t = 1 d-cell
  present at W3G2B).  No wording change in S8's refutation paragraph.
* **Grades/fences/claims table.**  Header "0/2 CLEAN" correct after two
  rounds (PE1 NOT-CLEAN, PE2 GAPS-ONLY — the round-2 verdict recorded in
  the S11 W-r2 record; the head bracket remains W-r1-only, which the
  header's "see the bracket below and S11" covers).  W-D6 row: cap-only
  ✓.  W-D7 row: pins ✓.  (SURV) row: OPEN + withdrawal record ✓.
  **LAW-DCX-(m+1) row + F5: UNCHANGED (m = 1 proved, m ≥ 2 conjecture)**
  ✓.  F1–F7 match the proof bodies; F2 consistent with the new S6 text;
  F6 carries clause + census denominator ✓.
* **No silent RM-GEN row-11c upgrade.**  RMENGINE_2026-08-08.md at HEAD:
  S8 row 11c still reads "**HEURISTIC — conjecture-supported** (DCX3
  C2/C3 seals, S9 D5, PE census); NOT derived" — no upgrade (checked at
  a0e266c and at HEAD c308d26; the commit's RMENGINE round-6 edits are
  record-layer per its own log).
* **W-r2 record accuracy.**  Verdict line, finding classes, remedy list,
  and the two fresh-instance claims all match the PE2 report
  one-for-one; "md5 pins match; sandbox re-run identical" re-verified
  here ✓.  One unverifiable cell: see N-3.

## Part D — findings (quote-and-classify)

### G-1. JUSTIFICATION GAP — the two S0 attainment sites display the (STK) ∧ clause pins but not the (H3) ∧ g₀ = 1 scope the attainment equally consumes

Quotes (S0, reconciliation paragraph — the bold and the W-r2-pinned
trailer):

> the max ATTAINED under (STK) ∧ the law clause D + c_{m−1} ≥ 2e_{m−1}
> — W-D6+W-D7, see S8(b)

> Row 11c as worded is false on the full tree and true verbatim on the
> dump-free principal subtree on the clause-satisfying rows ((STK) ∧
> D + c_{m−1} ≥ 2e_{m−1} — the same pins as above; …)

Derivation.  Attainment of the e-divisor floors c_l (row 11c "verbatim")
is proved ONLY by W-D7, whose hypotheses are (H3) ∧ g₀ = 1 in addition
to (STK) ∧ clause; W-D6 at g₀ ≥ 2 caps at the P-divisor pools ĉ_l ≤ c_l
and proves no attainment.  The note's own fence F2 says exactly this:
"At g₀ ≥ 2 the two-sided identification (b) FAILS structurally".  So
read alone, the trailer asserts, for a clause-satisfying (STK) row at
g₀ ≥ 2, an equality the note elsewhere declares structurally
unavailable — an intra-note tension resolved only by chasing "W-D6+W-D7,
see S8(b)" (S8(b) does display [(H3) ∧ g₀ = 1]) or by reading "the same
pins" expansively.  The note's own S1 convention is "(H3, only where
flagged)"; these two sites consume it unflagged.  Instance status: no
traced-battery counterexample (my W3G2B clause-satisfying instance
happens to attain ĉ = c because pool₁ < e₀ there), but the sealed m = 2
record the note itself cites (live deficit-1 rows at pool₁ = 2 = e₀ <
4 = P₀, hence c₁ = 1 > 0 = ĉ₁) is precisely the regime where the
unscoped reading fails.  This is the identical genre PE1-G1/PE2-G-1
classified as gaps (attainment language missing a consumed hypothesis);
neither prior pass charged the g-scope leg — fresh-eyes item.
Mitigation: every GRADED claim (W-D6, W-D7(iii), S8(b), both claims
rows) carries the full scope; the S0 sites are summary prose with a
correct citation.  Classification: JUSTIFICATION GAP (display/scope
residual; repair = add "(H3) ∧ g₀ = 1" / "at all-g = 1" — or "row 11c's
e-divisor floors read on W-D7's scope" — at the two S0 sites).

### N-1. NOTE — the S7 "Reading" paragraph retains the pre-repair cancellation vocabulary at one site the W-r2 box fix did not cover

Quote (S7): "The law therefore asserts precisely: *the cascade decides
liveness* — its residue survives when it exits, and everything it
cannot fund cancels."  Same status as PE2's N-1 on the box: as a gloss
of what the LAW asserts it is vacuous-compatible (an absent family
"cancels" trivially), and the box directly above now says
absence-or-cancellation; but a reader of S7 alone can re-import the
cancellation picture the W-r1 withdrawal removed.  Cosmetic; repair is
three words ("fails to appear or cancels").

### N-2. NOTE — the retained S6 sentence "reachable only through recycled dump mass", read class-wide, excludes the non-principal-d-cell channel that W-D6c itself displays

The sentence is explicitly sourced to the sealed m = 2 record
("Sharper, from the sealed m = 2 record (DCX3/RM2C, DS7): … reachable
only through recycled dump mass (the C_k partial-consumption children
… plus level-≥1 correction dumps)"), and the follow-on "the literal-e₀
floor is reachable only through the recycled-mass economy, which this
note does NOT derive" is fenced as not derived.  But W-D6c's excess
dichotomy at g₀ ≥ 2 is dumps OR non-principal d-cells, and nothing
shown excludes a dump-free t ≥ 1-cell route to the e₀ boundary on
unprobed instances; "only through … dump mass / the recycled-mass
economy" is measured-instance shorthand that a class-wide reader could
over-take.  Instance-grade + "does NOT derive" + F2 keep it honest —
cosmetic, but worth a word ("on the sealed record, only through …").

### N-3. NOTE — the W-r2 disposition cell "tracked in the ledger" names no ledger, and no repo ledger entry was found

The PE2-n disposition row says the queued cross-note RMENGINE row-11c
refutation bracket is "tracked in the ledger".  Searched: PROJECT_STATE,
the synthesis-pass docs, RMENGINE and stress notes, the openmath
directory — no entry tracking this queued item was found in the repo.
If the ledger is an extra-repo orchestrator artifact, the record should
name it; otherwise the tracking claim is currently unbacked (the QUEUED
status itself is honest either way — RMENGINE row 11c verified
unchanged at HEAD).

---

## Verdict block

The W-r2 repair discharges what it claims: the W-D6 gloss is now
fully pinned and exactly matches what W-D6/W-D7(iii) prove; the
withdrawn-genre grep is clean everywhere outside labeled withdrawal
brackets, and the S6 replacement's battery datum (path existence ⟺
e₀-clause, 412/412 incl. the four g₀ = 2 towers) re-computes exactly
from the committed JSON; the (SURV) box's absence-or-cancellation gloss
is precise and the box remains exactly the law's residual given W-D4.
Machine legs reproduce byte-identically (md5 pins, sandbox re-run,
censuses), and two never-before-audited sealed divergence records
(W3G2B (1067,1067) at g₀ = 2, d₀ = 2; W4DEEP (1483,1483) at m = 4)
were hand-derived from the reads and machine-confirmed via a new
instrument riding PE1's independent machinery — both CONFIRMED, with
the W-D2(iv) t-inventory, the W-D6c channels, and the W-D7 greedy cell
exhibited on the fresh instances.  No claim graded PROVED consumes
(SURV)/(EMPTY); LAW-DCX-(m+1) stays m ≥ 2 conjecture; RM-GEN row 11c
stays HEURISTIC at HEAD.  One justification gap survives fresh eyes:
the two S0 attainment sites carry the (STK) ∧ clause pins the prior
rounds demanded but still omit the (H3) ∧ g₀ = 1 scope the attainment
equally consumes — the identical under-display genre, one hypothesis
over (and in facial tension with fence F2 at g₀ ≥ 2 until the S8(b)
citation is chased).  Three notes, all cosmetic/record-layer.  No
critical: nothing false-against-artifacts survives, and every graded
claim carries its full hypothesis package.

WMULTDCX-PE3 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
