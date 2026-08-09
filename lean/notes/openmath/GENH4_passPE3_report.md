# GENH4 passPE3 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE3 (quote-and-classify; fixes
nothing). **Target:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` at HEAD
(dd83bc5; note body frozen at r2 fd35416 + 5279a11). **Arc:** seal 121d9ab →
RED 3eb1667 → GREEN 4b5c085 → PE1 263a36f → r1 dff23f8 → PE2 2618e9b → r2 →
**PE3 = this**. **Charges:** (1) the r2 census correction and its propagation
(S1/S6.1/S6.3/P-3 concordance; silent Q−1 consumers in the product algebra);
(2) the corrected dv0 = N trichotomy vs committed counter-keys + fresh cells
of my own; (3) the re-pinned W-12.D firing at r5; (4) the new supp leg
`genh4r2_supp.py` audited for tautology; (5) the eleven R_τ by a route
different from all prior passes; (6) free hunt over every [r1]/[r2] tag.

## VERDICT: NOT CLEAN — 0 CRITICAL + 0 GAPS + 1 MINOR (+2 remarks).

Every r2 repair is verified correct in substance: the comp-weighted census
is concordant at all four charged sites and confirmed by my own raw walker
at two never-measured cells; the corrected trichotomy's CONTENT is right
(committed counter-keys + fresh cells); the W-12.D re-pin is accurate and
the fired clause is genuinely supplied by GENH4.C; the supp leg is not a
tautology; the machine leg reproduces bit-identically; the eleven R_τ
survive a wild-prime mechanism-free measurement. The one minor is inside
the NEW [r2] text itself: the dv0 = N "trichotomy" display's clauses
overlap with conflicting conclusions on a committed-realizable stratum.

### FINDINGS

* **MINOR 1 (GENH4-CAP(F) [r2] box + S4 [r2] bracket — the trichotomy's
  first clause omits its one-side condition; the three clauses overlap with
  conflicting conclusions on a realizable stratum).** The [r2] box reads:
  > "The reader's exits at dv0 = N are a trichotomy: ODD N → DECIDED RAM(N)
  > (the one-side shape and the stable value suffice, no residual consulted
  > — S7's RAM bullet); dv0 = N > 2w → DECIDED 2SIDED(w, N−w) (shape-only);
  > UND EXACTLY at EVEN dv0 = N = 2dμ"
  and S4's [r2] bracket likewise: "odd u = N is decided RAM(N) and
  u = N > 2w decided 2SIDED(w, N−w)". The antecedents {odd N} and {N > 2w}
  are NOT mutually exclusive: at ODD N > 2w both fire, with contradictory
  conclusions, and the correct exit is 2SIDED, not RAM — the committed
  (Zp,2,7,k1) row itself carries 384 members with u = N = 7 odd, w = 3
  (2w = 6 < 7) keyed 2SIDED(3,4), and my fresh (Fqt,2,8,k1) walker (below)
  realizes the even analogue 2SIDED(3,5) = 1,536 at u = N = 8. **Failure
  scenario:** a fresh implementer applying the box's clauses in listed
  order classifies (u = N odd, N > 2w) as RAM(N), predicting RAM(7) = 512 /
  2SIDED(3,4) = 0 at (Zp,2,7,k1) against the committed 128 / 384. The
  condition is recoverable in-note — LEMMA GENH4-3(i) states "(needs
  u ≤ 2w: one side; else (ii))", S7's RAM bullet is "(u odd, u ≤ 2w)", and
  the box's own second clause covers the overlap — and the runner, every
  committed number, and GENH4.B are correct, so this is display-level:
  MINOR. Repair owed: "ODD N ≤ 2w → DECIDED RAM(N)" (one token per site,
  two sites). Note this defect is INHERITED from PE2's own GAP-1 sentence
  ("at odd N it is a DECIDED RAM(N) …"), which r2 transcribed faithfully.

* **REMARK A (unscoped mnemonic, not a finding).** GENH4.A's closing
  "Equivalently: W-12.A's cell law with (e₁, f₁)-re-based inputs — census
  field F_{q^{f₁}}, ladder density e₁" and S6.1's closing "= W-12.A's cell
  law with census field F_{q^{f₁}} and ladder density e₁" survive r2
  unmodified. At genre-F boundary-band pins the census is q^{comp}−1 = q−1,
  NOT the F_{q²}-census — the band is precisely where the re-based frame
  breaks and comp-weighting enters, i.e. the mnemonic is exact only away
  from the band. No number can be extracted wrongly (the [r2] census clause
  sits adjacent and governs), but the next repair should scope the
  equivalence ("away from the boundary band" or "with comp-weighted pin
  censuses").

* **REMARK B (stack-currency photo-finish, not a finding).** S10-BOX-1
  [r2](iii) says "GENIND: … passPE1 adjudicated (4259a93 …), r1 dispatched,
  counter 0/2". GENIND r1 (66200f2) landed 2026-08-08 23:18:53 — 49 seconds
  BEFORE r2 commit 1 (fd35416, 23:19:42) — so "r1 dispatched" was already
  "r1 complete" at commit. Within write-to-commit latency (the two repairs
  ran concurrently in the same wave); minimum grade over the stack
  unchanged at 0/2; P(4)'s conditionality display unaffected. Recorded
  because this arc has now hit stack-staleness three times (PE1 minor, PE2
  MINOR 2, this): the display is structurally a race, and the accepted
  practice ("as-of" pins + verdict-time refresh) already prices it.

---

## Charge 1 — the r2 census correction: CONCORDANT at all four sites; no silent Q−1 consumer

* **S1 (GENH4.A [r2] clause):** "q^{comp}−1 per RAM and per 2SIDED pin"
  with comp DEFINED inline (S2.3's slot dimension: 1 at E; 2 at F for
  m ≤ N−1; 1 on the band N ≤ m ≤ N+k−1). **S6.1 [r2]:** "comp-weighted
  exponents AND comp-weighted pin censuses — q^{comp(m)}−1 per RAM/2SIDED
  pin, i.e. q−1 at boundary-band pin heights m ≥ N". **S6.3:** the even-N
  band term's leading factor is cw(N) = q−1 and the interior S₁-slot factor
  q^{comp(N/2)} = q² — checked against the committed (Zp,2,8,k1) UND
  = 1024 = q^{2⌊N/2⌋+2k−1} + (q−1)q^{N+2k−1} = 512+512 by my own slot
  arithmetic. **P-3:** consF (Zp,7,5,k1) RAM(5) = 21·(q−1)·q⁵ = 2,117,682
  re-verified from the committed `genh4_checks_results.json` (86% of the
  2,470,629-member row). All four sites concordant.
* **Product algebra at every census consumer:** RAM(u): cw(u)·q^{Σcomp};
  2SIDED(w,d): cw(u)·cw(w)·q^{Σcomp} (BOTH pins comp-weighted — verified:
  2SIDED(3,5) at (2,8,1) = (q−1)(q²−1)·2⁹ = 1,536 ✓, mixed comp across the
  two pins); SPLITEQ/INERT keep the F_{q²} censuses (their residual events
  sit at 2dμ < N, always interior — no band interaction); SPLTAIL's pin
  cw(w) interior; UND band pin cw(N) = q−1. My OWN comp-weighted law
  evaluator built from the r2 display alone reproduces every key of both
  fresh cells and both committed comparison rows (below) — the correction
  propagates consistently through every product.
* **No downstream Q−1 remnant:** the S1 statement's surviving Q−1's are
  the SPLITEQ/INERT/entry censuses (correct — interior residual events);
  the S9 density assembly is band-insensitive (boundary families drain
  into (A2); independently confirmed by the wild-prime density leg below);
  the runner's `law_F` implements `ex0 = q**comp(dv0) − 1` and
  `q**comp(dv1) − 1` (read directly at lines ~201–223). Only REMARK A's
  mnemonic sentence still glosses the census as a single field.

## Charge 2 — the corrected trichotomy: committed counter-keys verified + TWO FRESH CELLS constructed (equal characteristic, first ever)

Committed counter-keys re-read directly from the artifacts: RAM(5) =
2,117,682 at (Zp,7,5,k1) [odd N decided RAM]; 2SIDED(3,4) = 384 at
(Zp,2,7,k1) [odd N > 2w decided 2SIDED — the MINOR-1 overlap stratum];
2SIDED(3,5) = 1,536 and UND = 1,024 at (Zp,2,8,k1) [even N: > 2w decided,
≤ 2w UND].

**Fresh construction (`/tmp/pe3/legA_walker.py`, no runner/reader import):
cells (Fqt, q=2, N=8, k=1) and (Fqt, q=5, N=5, k=1)** — neither appears in
any committed artifact or any prior pass; FIRST equal-characteristic
genre-F cells anywhere (the roster's Fqt F-rows are (2,7) and (3,5)). Entry
enumerated from the LEVEL-1 POLYGON definition directly on raw B-tuples
(v(B₀) = 4k exact, residual ψ² digit pins — not via the GENH4-1F
fibration); state recomputed at every node by raw polynomial division in
F_q[t]/t^N; residual reads brute-forced over F_{q²}; refine recentering
φ′ = φ − (ŝ_a t^{dμ−k}x + ŝ_b t^{dμ}) with floor + ψ-invariant assertions
armed at every re-entry (12,288 refine events at (2,8), zero violations).

* **(Fqt,2,8,1):** 262,144 members, 10 keys: RAM(5) 196,608 · SPLITEQ(3)
  12,288 · INERT(3) 24,576 · 2SIDED(3,4) 9,216 · **2SIDED(3,5) 1,536**
  [even-N boundary DECIDED] · SPLTAIL(3) 1,536 · RAM(7) 3,072 · UND 1,024
  [= 512 stratum-1 + 512 even-N band, the two-term law] · H₂=(3,): RAM(7)
  9,216, UND 3,072. **= the committed (Zp,2,8,k1) row KEY-FOR-KEY (0
  mismatches)** — characteristic uniformity confirmed on fresh territory —
  and = my own comp-weighted law evaluator (0 mismatches).
* **(Fqt,5,5,1):** 156,250 members (10 ψ), exactly 2 keys: **RAM(5) =
  125,000** [odd-N boundary DECIDED, 80% of the row] and UND = 31,250.
  = committed (Zp,5,5,k1) key-for-key (0 mismatches) = my law (0).
* **Armed counter-hypotheses, both FIRED at both cells:** (i) the pre-r2
  exit rule "u = N → UND always" mismatches (2 keys per cell — RAM(5)/
  2SIDED(3,5) would drain to UND); (ii) the pre-r2 Q−1 census at band pins
  mismatches (3 keys at (2,8), 1 at (5,5)). My cells DECIDE both r2
  corrections in fresh territory.

## Charge 3 — the W-12.D re-pin at r5: VERIFIED

* W-12's note at HEAD is byte-identical to ee17210 (r5) — the pin is
  current. The claimed arc (PE3 c9c5c0e → r3 b17238a/b8dfe62 → PE4 26689da
  1C → r4 d2d91b7/5728258 → PE5 c3e2f8e → r5 be4a1dc/ee17210) exists
  commit-for-commit with matching subjects.
* **The clause says what GENH4 needs:** (A1) [r4] reads "each with a
  splitting type σ_F [and such that EVERY member of every class (F, x) is
  σ-DECIDED in the S1 Conventions' pinned lift-certification sense, with
  forced σ = σ_F — the σ-LABELING clause; this is what Step 4's lower bound
  consumes]", and W-12's Step-4 [r5] gloss restates it as "every disc ≠ 0
  lift of every member of every visible core class has type σ_F" — GENH4's
  S11 [r2] quotation is a faithful splice of the (A1) opener + that gloss
  (the ellipsis is honest; the certification half is supplied by GENH4.C's
  decided-leaf quantifier, so no content is lost at this firing).
* **The fired-clause row:** W-12's [r4] FIRING CHECK n = 4 row rules
  "SUPPLIED. THEOREM GENH4.C: 'At every decided stage leaf of either genre
  (any history, any window), EVERY lift with disc ≠ 0 has the σ claimed by
  the leaf dictionary'…" — I checked the row's quotation BYTE-FAITHFUL
  against GENH4's S1 statement of GENH4.C, and the dictionary displayed in
  the row matches GENH4.C's. The n = 4 menu's composite families are
  exactly GENH4.C's decided stage leaves (SPLTAIL included, σ as 2SIDED);
  the non-composite families were already supplied at the order-1 layer +
  P(2)/P(3). Step-4's upper bound applies the same clause at F over its own
  truncation — no other σ-statement enters. The firing is sound at the
  current pin.

## Charge 4 — `genh4r2_supp.py`: NOT a tautology

* **Code audit (216 lines, read in full):** the LEFT side (T_τ) is built
  exclusively from literals hardcoded in the script — HM3.D's five R_τ
  closed forms, the level-0 separable censuses, and HM3.D S5.5's four n = 2
  block densities — inverted through R_τ = SEP_τ + (q−1)c²_{τ″} + q·T_τ.
  I verified every literal VERBATIM against the accepted HMENU3 note
  (HM3.D display L247–252; S5.5 block densities and assembly L475–487).
  The engine feeds ONLY the right side (`ENG.beta(3)`) plus the sympy
  symbol q; `genh4_checks` is imported only for its PINS dict (md5
  re-verification). No hmenu3/qscout22/genh4 model code touches the
  derivation.
* **Provenance independence:** HMENU3's displayed R_τ come from ITS OWN
  Group-I-series/amplifier assembly (T_τ = (T⁰_τ + β_τ)(q⁶−1)/(q⁶−q)),
  not from the engine — the β₃ tie was HMENU3's discovered identity
  (HM3-RTAU), so left and right routes are genuinely decorrelated. The
  supp leg's content substantially re-executes the supplier's HM3-RTAU
  check inside GENH4's own artifact set — exactly what PE2 MINOR 1 asked
  (the battery-claim accuracy), honestly labeled "additive".
* **The tooth is real:** corrupting the INERTDEEP block density ×2
  perturbs the derived T_τ and must break the tie — fired in the committed
  run and in my sandbox re-run.
* **Sandbox re-execution:** GREEN, 0 violations, 1.9 s; results-JSON
  leaf-diff vs committed = the elapsed-time leaf ONLY; output ex-timing
  IDENTICAL. Committed artifact md5s (8ce5faa8…, c966d311…) match the
  note's S9.2 [r2] display.

## Charge 5 / FRESH ROUTE — the eleven R_τ at the WILD primes, mechanism-free (new instrument territory)

Prior routes: PE1 = tuple scans + Zp walkers + own level-0 assembly + own
NP derivation of R_{(4,1)} + symbolic Σ = 1 + E[#roots]; PE2 = symbolic
GENH4-1F + 504-case ledger closure + fresh TAME primes 11/13 + mechanism-
free σ-density at 11/13. **This pass:** (leg A above — equal-char raw
walkers at two new cells) + **(leg B) the mechanism-free σ-density
measurement AT THE WILD PRIMES p = 2 and p = 3** — the note's boldest
claim ("wild primes included, both characteristics") measured directly
where all six ramified types are wild or boundary-wild, with the deepest
predicted masses (R_{(4,1)}(2) = 107/1533 ≈ 0.070 is 100× its tame-prime
size). Instrument (`/tmp/pe3/legB_wild.py`): 150,000 monic quartics per
prime, coefficients uniform in [0, p¹⁴), σ read from PARI
`nfinit([f,[p]])` + `idealprimedec` on the p-maximal order — no polygon,
no window, no slot string, no engine, no runner code. The eleven S9.4
closed forms were typed BY HAND, checked Σ_τ R_τ = 1 symbolically, and
pinned against the note's displayed q = 2, 3 anchors: MATCH (both primes,
all 11 — transcription-guarded).

**Result (149,986 samples at p = 2 [14 reducible over ℚ excluded],
150,000 at p = 3 [0 reducible]):**

| τ | R_τ(2) pred | obs | z | R_τ(3) pred | obs | z |
|---|---|---|---|---|---|---|
| (1,1)⁴ | 0.0024129 | 0.0023736 (356) | −0.31 | 0.0053872 | 0.0054600 (819) | +0.39 |
| (1,1)²(1,2) | 0.0916889 | 0.0925753 (13885) | +1.19 | 0.1317885 | 0.1325667 (19885) | +0.89 |
| (1,1)²(2,1) | 0.0515400 | 0.0509448 (7641) | −1.04 | 0.0520559 | 0.0519200 (7788) | −0.24 |
| (1,1)(1,3) | 0.2545294 | 0.2555705 (38332) | +0.93 | 0.2971276 | 0.2966933 (44504) | −0.37 |
| (1,1)(3,1) | 0.1160280 | 0.1155908 (17337) | −0.53 | 0.0636349 | 0.0635733 (9536) | −0.10 |
| (1,2)² | 0.0288758 | 0.0285160 (4277) | −0.83 | 0.0533592 | 0.0525200 (7878) | −1.45 |
| (1,2)(2,1) | 0.1000217 | 0.0995426 (14930) | −0.62 | 0.0906253 | 0.0906400 (13596) | +0.02 |
| (1,4) | 0.1941292 | 0.1941115 (29114) | −0.02 | 0.2240855 | 0.2241667 (33625) | +0.08 |
| (2,1)² | 0.0317460 | 0.0316830 (4752) | −0.14 | 0.0216346 | 0.0213800 (3207) | −0.68 |
| (2,2) | 0.0592303 | 0.0588055 (8820) | −0.70 | 0.0348212 | 0.0354733 (5321) | +1.38 |
| (4,1) | 0.0697978 | 0.0702866 (10542) | +0.74 | 0.0254801 | 0.0256067 (3841) | +0.31 |

χ² = 5.30 (p = 2) and 5.35 (p = 3) on 10 df — comfortable fits; every
|z| ≤ 1.45; **exactly the eleven displayed types in 299,986 wild-prime
samples** (a twelfth type at density ≳ 2×10⁻⁵ would have appeared). The
displayed R_τ(q), evaluated at the two WILD primes in mixed
characteristic, match a maximal-order oracle that shares no code, no
method, and no supplier with the note.

## Charge 6 — free hunt: all 14 [r2] tags visited; r2 diff audited

`git diff 2618e9b..5279a11` on the note: every removed line is one of the
repaired displays (the census clause, the two dv0 = N parentheticals,
S6.1's parenthetical, S0/S1 admissibility phrases, S9.2/S12 ν₃ labels,
S13.2 arc line); every replacement is [r2]-tagged; no frozen number moved;
the sealed runner + artifacts are byte-untouched through r2 (the
`*_smoke.*` artifacts were committed at the wave-fold 0089f9b —
housekeeping for the seal-disclosed smoke, consistent with S12's
disclosure: GREEN 17.4 s, all five teeth). Tag-by-tag: S0/S1 admissibility
floors ✓ (the (N,k) = (4,1) failure instance re-derived: true budget slots
3 vs form 2); S1 census ✓; the CAP/S4 trichotomy → MINOR 1; S4's "u = N
read shape-only through the in-window a₁-component at position N−k" ✓;
S6.1 ✓; S9.2 supp ✓; S10-BOX-1 → REMARK B (HEX3 0/2 at r3 ✓ current;
W-12 r5 0/2 ✓; HMENU3 2/2 + ANNEX A ✓; W-11 2/2 ✓; min grade 0/2 ✓);
S11 W-12 re-pin ✓; S12 GH-DENS relabel ✓ (matches the runner's actual
dchecks); S13.2 arc line ✓ (commit hashes verified).

## MACHINE LEG: GREEN, bit-identical; instrument honest

* **Pins:** runner md5 `ee8024b7…` IDENTICAL at worktree = HEAD = 5279a11 =
  fd35416 = 2618e9b = dff23f8 = 4b5c085 = 3eb1667; seal 121d9ab =
  `e5e435c3…` (the one disclosed repaired line). Supp md5 `7d0445c5…`
  first at 5279a11, identical at HEAD. Artifacts at HEAD: output
  `9e6ca9b3…`, results `cbcff562…`, supp output `8ce5faa8…`, supp results
  `c966d311…`, qscout22 `cb885663…`/`6c2441a1…`, engine `7240a916…` — all
  match the note's pins.
* **Isolated re-run** (full battery, fresh copy of `verification/` in
  /tmp/pe3/run; committed artifacts never written): **exit 0, GREEN,
  1224.4 s**, all families 6/481/54/5/192,000/8/46,590/92/157/115/6,185 =
  245,693 checks, 0 violations; teeth LAT 19 / CEN 14 / ALPH 4 / SIG 2 /
  DENS 1. Results-JSON leaf-diff vs committed: **1 leaf, the elapsed-time
  leaf; 0 non-timing**. Output txt ex-timing identical. Supp leg re-run:
  GREEN 1.9 s, leaf-diff = elapsed only, output ex-timing identical.
* **Tautology audit:** `law_E`/`law_F` are the runner's own S6
  implementations (comp-weighted census read in the source); the pinned
  qscout22 reader `read22` is consumed only as the fresh-row READER; the
  qscout22 MODEL functions are never called. Independently corroborated by
  leg A: my from-scratch walker + law evaluator reproduce the committed
  rows the battery ties to.

## Clean charges (executed, nothing found)

Charge 1 (census propagation — concordant, no silent consumer, REMARK A
only); charge 2 (trichotomy content — correct; the display overlap is
MINOR 1); charge 3 (W-12.D re-pin — accurate, clause supplied); charge 4
(supp leg — independent, toothed, reproducible); charge 5 (eleven R_τ —
wild-prime confirmation, anchors re-pinned); charge 6 (r2 diff honest,
tags accurate, stack current up to REMARK B's 49-second race).

## GRADE LINE

**NOT CLEAN: 0C + 0G + 1m.** The 2-clean count does NOT start (counter
stays 0/2; the r3 owed is a two-token display repair at GENH4-CAP(F)/S4
plus, optionally, the two REMARK scopings). No frozen number, no theorem
statement, no conclusion moves; the note's substance survived every charge
including two fresh-territory instruments.

## Verifier's session artifacts (all under /tmp/pe3; repo untouched except this report)

* `/tmp/pe3/legA_walker.py` — the equal-char raw walker + own law
  evaluator + armed counter-hypotheses (cells (Fqt,2,8,1), (Fqt,5,5,1)).
* `/tmp/pe3/legB_wild.py`, `/tmp/pe3/legB.log` — the wild-prime
  mechanism-free σ-density measurement (p = 2, 3; 150k each).
* `/tmp/pe3/run/` — the isolated battery + supp re-run
  (`/tmp/pe3/rerun.log`, `/tmp/pe3/supp.log`).
