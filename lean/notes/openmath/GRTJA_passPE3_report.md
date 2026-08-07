# GRTJA pass PE3 — third hostile pass (acceptance attempt) on GRTJA_PROOF_2026-08-08.md (post-r2)

**Verifier:** JA-PE3 (fresh hostile Fable context; fixes nothing). Round 3
of the acceptance arc (rounds 1–2 = the 2026-08-04 JA-PE1 pass and the
JA-PE2 pass at 9040961, both repaired in place).

**Target pin:** note at HEAD 50af570, md5 `b81258df` == `git show 5d95805:`
(the JA-r2 repair commit); `git log 5d95805..HEAD` over the note + all three
J-A artifacts = EMPTY (the one post-r2 commit, 50af570, touches none of
them). Artifact seals verified by md5 at worktree AND at the pin commits:
runner `grt_ja_checks.py` `5972d412` == @696eae8 (commit 1, SEAL); output
`0d6d0522` and JSON `13ab52ab` == @1cbf8ca (commit 2, VERDICT) — the r2
round was note-only as claimed ("runner + artifacts BYTE-FROZEN" TRUE).

**Charge executed:** (1) the r2 diff (9040961 → 5d95805) line by line: the
root-inclusive (R-coll) extension re-derived as a cure for PE2 FINDING 1,
the witness census independently reproduced by my own /tmp probe over the
sealed engines, and 3 witnesses spot-checked by hand-level order
arithmetic; the §3.3 JB quotes byte-checked at the 4c4ee56 pin; the §4
TW-INST bracket re-read against the runner source; the §8 arc-record
blocks checked against the git record. (2) The whole note fresh; chosen
untouched vein = the JA-QO/JA-D0 legs (extraction, PARI full-type gate,
d₀ specs, transported-boundary split), which neither PE1 nor PE2 dug.
(3) The arc-accounting system post-normalization (header/§7.3/§8,
counters, strike-through, report-name collision, ledger cross-refs).
Machine leg re-run in a /tmp sandbox (committed artifacts untouched).

---

## 1. Machine leg — RE-RUN BIT-IDENTICAL

Re-ran `grt_ja_checks.py` (full battery) in a /tmp copy: **exit 0, all 17
families GREEN, TOTAL samples 10,311, 0 violations, CK-RES boundary 16,
CK-BPREF 26** — stdout differs from the committed
`grt_ja_checks_output.txt` ONLY at wall-clock/timing lines; the
regenerated JSON is identical to the committed one on EVERY key except
`elapsed_s` (5.5 vs 7.4; deep-compared key-for-key). Independent recounts
from the committed JSON: 25 `run_families` instances = 16 roster + 5 QO +
4 d₀; scored 443 = 396 main-roster + 14 QO + 33 d₀; boundary 16 = main
(T3B 4, I4B 5) + transported (T3B 3, I4B 4) with every other instance 0;
bpref 26 on 10 roster rows + 4 d₀ rows; TW-INST ledgers = exactly 20.
All of §7.1's figures confirmed.

## 2. Charge (1a): the root-inclusive (R-coll) extension — RE-DERIVED, CURES FINDING 1

The extended definition (quantifier 2 ≤ q ≤ m, root included) makes the
displayed conclusion TRUE; re-derivation of the induction from the note's
own theorems: (VD-1) at every level-1 node unconditionally (W2-L3); for a
level-(q+1) node N, its on-line digits are level-q nodes where (VD-q)
holds by induction — exactly THEOREM JA-RES's per-digit proviso — so the
per-slot law holds at N, and the level-(q+1) instance of the JA-VDIND
condition (now IN the quantifier range for every 2 ≤ q+1 ≤ m, including
the root q+1 = m) fires COROLLARY JA-VDIND's forward direction to give
(VD-(q+1)) at N. The old range stopped the character condition at m−1,
leaving the top JA-VDIND application unfed — the defect PE2 witnessed.
The extension supplies precisely the missing hypothesis and nothing else;
the per-slot-law half of the display never needed the root condition and
is only strengthened by the smaller perimeter. CURED. Also verified in
the runner source (line 394): CK-VDM's `triv` gate is byte-for-byte the
q = m root condition (`z_{m−1}^{i·A_{m−1}} == 1` at every attained i of A
itself), evaluated on scored (proviso-holding) samples — the §3.4
bracket's "CK-VDM's triv gate IS the q = m root condition" is exact, and
the note's careful phrasing ("keys the extended form's INDUCTION STEP",
not the full perimeter recursion) is the right claim.

## 3. Charge (1b): the witness census — INDEPENDENTLY REPRODUCED, 5/5

My own probe (`ja_pe3_witness_probe.py`, /tmp, written from the sealed
engines' primitives + an independent recursion-tree walk for the deep-node
condition and independent letter-order arithmetic):

* Main-roster scored total **396** (= PE2's fresh-leg figure; = the
  committed JSON's 443 minus QO 14 minus d₀ 33).
* **P1:** scored samples with (VD-m) FALSE = **66 = 58 at m = 2 + 8 at
  m = 3** — PE2's census exact; m = 3 rows = T3B (1), T3F (3), I4B (4).
* **P2:** all **8/8** m = 3 witnesses sit ON the OLD root-exclusive
  perimeter (every level-2 node character trivial — walked by my own
  frontier recursion, not the runner's code path).
* **P3:** **66/66** witnesses have the root character visible ⟹ all 66
  OFF the extended perimeter, excluded EXACTLY by the new q = m condition
  (for the 8 at m = 3 it is the only failed condition; at m = 2 it is the
  only condition).
* **P4:** scored samples ON the extended perimeter = **330, (VD-m) TRUE
  on every one (0 violations)**; 330 + 66 = 396 exactly.
* **P5 spot-checks (3 witnesses, independent order arithmetic):**
  - **T3B** (Zp, p=3): deg A = 6, attained {1}, A₂ = 7, ord(z₂) = 2 ⟹
    root exponent 1·7 ≡ 1 (mod 2) ≠ 0 — character visible, excluded;
    level-2 node exponents all ≡ 0; proviso TRUE; (VD-3) FALSE. Matches
    PE2's quoted witness field-for-field.
  - **T3F** (Zp, p=3): deg A = 12, attained {0, 2}, A₂ = 13, ord(z₂) = 4
    ⟹ exponent at i = 2: 26 ≡ 2 (mod 4) ≠ 0 — excluded; A₁ = 0 makes
    every level-2 node trivial; (VD-3) FALSE. (PE2's exact example, third
    of T3F's three witnesses in pool order.)
  - **I4B** (Zp, p=3): deg A = 6, attained {1}, A₂ = 13, ord(z₂) = 2 ⟹
    exponent 13 ≡ 1 (mod 2) ≠ 0 — excluded; level-2 nodes trivial
    (A₁ = 4 ≡ 0 mod ord(z₁) = 2); (VD-3) FALSE. Matches PE2's quote.

Every figure in the §3.4 [r2] bracket and the §8 r2 record checks.

## 4. Charge (1c): the rest of the r2 diff, edit site by edit site

* **§3.3 (FINDING 2 repair):** the discharge sentence now scoped to
  "every PRINT-SIDE consumption site IN THIS NOTE" with the defining
  parenthetical — the scoping PE2's cure line asked for; the implication
  (tex 1167–1168 hypothesis ⟹ u ≥ 0) was verified real by PE2 and
  re-checked here. Both JB quotes **byte-verified at the 4c4ee56 pin**:
  "CARRIED AND UNDISCHARGED (r2, G2-5; r1's \"discharge\" retracted)" and
  the [r5, F-3] STATUS-NARROWED block are byte-identical segments of JB
  §0M's column-(b) definition cell (the attribution "§0M column (b)" is
  CORRECT — I located the quote inside the "The columns" block, item (b);
  no WM-PE3-style attribution slip). The three disclosed ellipses elide
  (i) a parenthetical cite, (ii) the r6-struck "~~exactly~~", (iii) the
  membership elaboration — all faithful; eliding a struck token is right.
* **§3.4 bracket cross-note claims:** PE2's "the false clause has no
  accepted consumer" and "after which both displays are true, CK-VDM keys
  them" quoted byte-true from the 9040961 report; JB col (c)'s operative
  fence ("at every m ≥ 2 a HYPOTHESIS (JA-VDIND's ABSOLUTE
  character-triviality…)") byte-true at 4c4ee56; the ledger entry exists
  at 3626f55 (BRIDGE_ADJUDICATIONS: JB erratum annotation owed at the
  fold; WM r4 companion) — and WM r4 (14706f5, 6 minutes before r2)
  indeed carries the companion (R-coll) range extension per its commit
  record.
* **§4 TW-INST bracket (FINDING 3 repair):** matches the runner source
  exactly — `tw_inst` re-runs ja_pin (retagged), ck_val, ck_res1, ck_res
  (CK-RES/CK-VDM logic under the TW-INST label) inside the chamber;
  CK-EPS/CK-GRID/ORB-EPS/ORB-RES are absent from it; called
  unconditionally on all 16 + 4 specs (20 JSON ledger entries). Both of
  PE2's counts corrected accurately.
* **§4(ii) W̃ := W_{m−1} (FINDING 5 repair):** I re-derived the transported
  law's exponents from u_i = β_i + i·W_{m−1}, i_j = s₀ + j·e_{m−1},
  β_{i_j} = β₀ − j·γ_m: constant part −κ(β₀ + s₀W_{m−1}), j-part
  κ(γ_m − e_{m−1}W_{m−1}) — the display is exact with W̃ = W_{m−1}.
* **JA-BOX-2:** the [r2] bracket + retained [r1] bracket are mutually
  coherent under the new definition (cancellation off the smaller
  perimeter remains possible; converse still unsealed). Grades line's
  "(root-inclusive as defined above, [r2])" correct — the per-slot law on
  the smaller perimeter is a fortiori unconditional.
* **§8 r2 record:** every factual claim checked — PE2 verdict figures,
  the dispatch-name collision + "filed as PE2" adoption, the five repairs
  enumerated = the five findings, "Grade changes: NONE" TRUE (no §7.2 row
  or ∎-grade changed; the r2 record honestly does NOT repeat r1's "no
  statement's mathematical content altered" since the definition DID
  change — the honest cure), seals re-verified, o1–o4 explicitly left
  standing.

## 5. Charge (2): fresh vein — the JA-QO / JA-D0 legs (undug by PE1/PE2)

* `QO_SHAPES` = x⁴−2, x⁴+4x+4, x⁴+2x²+2, x⁴+12 (p = 2), x³−3 (p = 3) —
  the note's "5 concrete wild polynomials". JSON: `status: complete` 5/5;
  `pari_full` = ((4,1),)×3, ((2,2),), ((3,1),) — the PARI leg genuinely
  ran and is recorded per shape.
* The `qo_leg` PARI gate logic is SOUND as a tie: when extracted
  E·F = deg f it demands the full type be exactly ((E,F),); otherwise
  (E,F) ∈ the factor multiset — read from `pari_fulltype` (fresh
  factorpadic + idealprimedec per factor). No vacuous branch: all five
  shapes hit the E·F = deg branch or record membership.
* `qo_extract` re-read: fresh polygon/hull construction, single-side
  gate, residual factoring capped at deg ≤ 2 with explicit
  'split'/'depth-cap' statuses — extraction failure cannot silently pass
  (status != complete ⟹ violation). Three of the five extracted towers
  are 1-read (scored 0 at m ≥ 2 — the monomial-pool NR = 1 guard from the
  disclosed smoke); §7.1's JA-QO row claims extraction + PARI + families,
  which is what runs — no overclaim.
* `D0_SPECS` vs the note's fences: JD5A p=5 d₀=2 (F₂₅), JD3A p=2 d₀=3
  (F₈), JD3B p=3 d₀=3, JD3C Fpt p=2 d₀=3 — §0's "d₀ = 3 root keys and a
  p = 5 row" and §7.3's "F₈/F₂₅ via the d₀ leg" both exact; the
  engine_ext double-leg certificate (irr_certificate + the committed
  tower's no-root gate) + PARI (e,f) tie on the Zp top lifts all present
  in code as billed.
* Transported boundary split re-read from JSON: tw T3B 3 + I4B 4 —
  §7.1's "(4 + 3 transported)/(5 + 4 transported)" census exact from a
  surface PE1/PE2 did not decompose (the per-tag tw records).

Vein verdict: clean — the leg is billed accurately.

## 6. Charge (3): arc accounting post-normalization — CONSISTENT AND TRUE

* Header (arc OPEN, rounds 1–2 named with correct dates and verdicts,
  counter "0 CLEAN passes of the 2 consecutive required", next = JA-PE3),
  §7.3 fence ("acceptance arc OPEN, counter 0/2 CLEAN … next = PE3"), and
  §8 ("rounds 1–2 complete; counter 0/2 CLEAN; next pass = JA-PE3") now
  agree — PE2 FINDING 4's contradiction is gone. Grep sweep: the only
  remaining "0/1"/"no acceptance arc"/"Codex leg" strings are inside the
  properly struck r1 tail (~~…~~ + supersession bracket) and the [r2]
  normalization bracket quoting them historically; the only remaining
  "2 ≤ q ≤ m−1" strings are historical quotes inside repair brackets.
* Round-record facts vs git: PE1 report committed 5e70442 (2026-08-04) ✓;
  PE2 report = 9040961 (2026-08-06) filed under the collision-safe name ✓;
  r2 = 5d95805 note-only +146/−29 ✓; ledger arcs-opened entry = 3626f55 ✓.
  Bracket census: 11 grep hits for r2 brackets (8 `[JA-r2` + 3 short-form
  `[r2]`) — matches the commit message's figure.
* The counter convention (0/2-CLEAN = 0 clean passes of 2 consecutive
  required) is used identically at all three surfaces; the r1 tail's
  denominator wobble is struck, not silently rewritten — the accepted-text
  discipline (dated annotations, no silent edits) held.

---

## FINDINGS: NONE (0 critical, 0 justification gaps, 0 minor)

**Ungraded observations (recorded, not graded):**

* (o1) The r2 witness re-check probe is /tmp-only and uncommitted; its
  "preregistered 5/5 PASS" is therefore unauditable from the repo (the
  two-commit seal vocabulary without a seal). Not graded because the note
  discloses the /tmp status, claims no seal, and every load-bearing figure
  (66 = 58+8; 8/8 on the old perimeter; 66/66 root-visible; 330/0;
  330 + 66 = 396) was independently reproduced here from the sealed
  engines by a differently-constructed probe.
* (o2) The §3.4 bracket's "over the sealed engines and pools" does not
  restate the census scope (main 16-tower roster pools; QO/d₀/transported
  excluded) — inherited from PE2's census definition and recoverable from
  the 9040961 report; the extension THEOREM itself is scope-independent
  and CK-VDM's 443/0 already covers all pools.
* (o3) PE2's (o2) debt — the [ILN]† as-of pin — is explicitly deferred
  again in the §8 r2 record ("owed at the next round/fold"); now one
  round older.
* (o4) "the WM companion line is being fixed in parallel by the WM arc"
  (§3.4 bracket) — WM r4 (14706f5) landed 6 minutes before r2, so at HEAD
  the companion has LANDED; present-tense pointer is fold-owed per the
  LIFTCORNER round-record convention.

**What survived this hostile pass (for the record):** the r2 diff correct
at every edit site; the root-inclusive extension re-derived as the exact
cure and machine-confirmed by an independent probe incl. 3 hand-level
witness spot-checks; both JB pin quotes byte-true with correct column
attribution; the TW-INST bracket now matches the runner verbatim; the
QO/d₀ vein clean; arc accounting consistent and true; machine bracket
bit-identical with all seals intact.

JA-PE3 FINDINGS: 0 critical, 0 gaps, 0 minor
VERDICT: CLEAN — first clean pass of the arc (counter advance 0/2 → 1/2
is the orchestrator's ledger action, per convention)
