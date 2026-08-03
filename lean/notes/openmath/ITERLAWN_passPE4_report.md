# ITERLAWN-PE4 — Fable round-4 hostile pass on the general-n note as amended at 4e8f027

## §0 VERDICT BLOCK

**VERDICT: NOT-CLEAN — 0 critical / 1 justification gap (0 nits).**

* **Text of record:** `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` @ 4e8f027
  (md5 `c088101c9676118566a54ad3bb18dfdf`, 1307 lines).
* **PE4-F1 [GAP — display-grade, structural-completeness branch; the third
  finding of the PE2-F1/PE3-F1 genre, one DAG edge deeper]:** the S7
  [IL3]-failure branch's row-4 exemption ("the L6 chain (#4) are NOT
  affected"), re-affirmed by the round-3 erratum ("Rows 1/2/4 of THIS branch
  stand as written"), is FALSE by the note's own dependency structure:
  L6-(n) at every rung ≥ 2 consumes S4.1 — the class's canonical lifts
  Φ₂,…,Φ_n are certified by WELL-DEF-(n) (S0.1 line 138: "well-definedness
  on the class: Lemma WELL-DEF-(n), S4.1"), and the S4.2 degree telescope's
  input deg Φ_{j+1} = e_jg_j·deg Φ_j requires REALIZE-(m)'s (R1) degree
  bound plus lift existence — and S4.1's m = 1 base legs consume [IL3]†
  WELL-DEF(i)/(ii) (the note's own operative bracket, lines 513–527; the
  r3-corrected row 3). Under the branch's hypothetical, row 4 at rungs ≥ 2
  falls WITH row 3 to "open at the [IL3] WELL-DEF m = 1 displays" (same
  elementary recovery); only rung 1 (no canonical lifts) is exempt. Full
  statement, failure scenario, ripple sites, and cure in §4.
* **Round-3 erratum fidelity: VERIFIED** — `git diff cb1a66d..4e8f027` on the
  note = exactly the two additive brackets (S4.4 union-precision note +
  S7 row-3 erratum); the row-3 correction independently RE-DERIVED RIGHT,
  the ⊆-note RE-DERIVED RIGHT (§2). The correction is right as far as it
  goes; PE4-F1 is that it did not go one edge further (row 4 rides row 3).
* **Re-runs:** `iterlawn_pe_reimpl.py` — 940 pairs / **0 violations**,
  mutations **7/7 caught**, 22,916 family-checks incl. I_m-asserts;
  output content-identical to stored, ONE wall-clock digit differs ("0.1s"
  → "0.2s" in the I4A progress line; every check count, census figure, and
  verdict line byte-identical). `iterlawn_diag.py` — 5,311 checks / **0
  violations**, output **md5-identical** (`7c72c4c6c0a953ebd41a56eab1e266e1`).
* **Everything else swept clean** (§5): integer layer, EXP-KIT, S4.1,
  W-MULT all legs incl. the r1/r2 erratum brackets, DCX, corollaries,
  T-notation, rule-8 under the incorporation convention, S8-vs-output tie.
* **Consequence:** the 2-clean bar is NOT met at round 4 regardless of PC3's
  result. Owed: errata round 4 (one clause + attribution brackets) then a
  fresh dual round.

## §1 Charge and identity

Round-4 Fable pass (with Codex PC3 concurrent on the same text; both CLEAN =
acceptance). Charge: erratum-r3 fidelity; EXHAUSTIVE row-by-row audit of BOTH
S7 failure-display branches against the note's ACTUAL dependency structure
(S2/S3/S4.1 consumption sites), every row exemption verified or killed;
byte-exact re-runs; fresh full content sweep. Scripts:
`verification/openmath/iterlawn_pe_reimpl.py` md5
`cae45db2318b89520dd5484466ef3604` (unchanged since e7e9151, matching the
S4.3 head-erratum citation) and `iterlawn_diag.py` md5
`cd7581b7fd9df555e517b69556199ef3` (matches the note's S8 claim).

## §2 Round-3 erratum fidelity (VERIFIED, and re-derived)

`git diff cb1a66d..4e8f027`: two files. On the note, exactly two hunks, both
purely additive brackets (surrounding sentences resume verbatim):

1. **S4.4 precision note (PE3-N1 cure), lines 686–690:** "⊆, not = — the
   union of the II-* case predicates is CONTAINED in CII_n, and only the
   containment is ever consumed downstream; equality is neither claimed
   elsewhere nor needed." **Re-derived RIGHT:** union of II-* =
   (g_{n−1}=1) ∧ (δ_n^{pl}=1 ∨ (E₁ᴵᴴ≠0 ∧ T_n=e_{n−1}−1)); (P-DS) certifies
   only E₁ᴵᴴ≠0 ⟹ CII_{n−1} (the "only" direction), giving ⊆; downstream
   consumption is exactly the per-case implication II-* ⟹ CII_n (the (P-DS)
   propagation) — containment only ✓. Cross-check against the S4.3 link
   paragraph's "CII₂ = its CASE-SPLIT Cases II-1∪II-2∪II-3 predicate on the
   nose" (line 648–649): NO conflict — [IL3]'s rung-2 case conditions are
   keyed to the inner-case predicate ("inner Case II" = CII₁) rather than to
   the E₁-export, so that r = 2 identity is syntactic and true; the bracket's
   ⊆ concerns the general-n E₁-keyed cases. ✓
2. **S7 row-3 erratum (PE3-F1 cure), lines 1139–1149:** row 3 falls under
   the [IL3]-failure hypothetical to "open at the [IL3] WELL-DEF m = 1
   displays". **Re-derived RIGHT:** REALIZE-(m) proof, line 482 — "m = 1 is
   [IL3] WELL-DEF(i)'s display"; WELL-DEF-(n), line 511 — "(At m = 1 this is
   [IL3] WELL-DEF(ii) verbatim.)"; the S4.1 operative bracket (513–527) —
   "the m = 1 base legs of REALIZE-(m)/WELL-DEF-(n) above consume [IL3]
   WELL-DEF(i)/(ii)". Recovery claim verified: the m = 1 realizer is a
   monomial sum over realize₀ = lift·π^w; the (I₁) ⟹ admissibility bridge is
   already derived inline (483–484); (R1)/(R2)/(R3) at m = 1 are one-line
   checks from the S0.2 base facts — elementary, independently re-derivable,
   same genre as rows 1/2's open-at-L1. ✓ The historical-frame note
   (arc closed clean, display-only branch) matches f726b36/the r38 bracket. ✓

Ledger leg of the diff: the round-3 record block appended to
`BRIDGE_ADJUDICATIONS_2026-07-30.md` (+19 lines, append-only). ✓

## §3 Execution re-runs (both exit 0)

| artifact | stored | re-run (PE4) | verdict |
|---|---|---|---|
| `iterlawn_pe_reimpl_output.txt` | md5 `cfad7943…` | md5 `ecf7cd49…` | content-identical; sole diff = one timing digit, line 5: "I4A … 0.1s" → "0.2s" (wall-clock nondeterminism in a progress line; all 940 pairs, all per-instance check dicts, TOTALS block, BASELINE VIOLATIONS: 0, and the 7/7 mutation table byte-identical) |
| headline | 940 pairs, 0 violations; mutations 7/7 caught+visible; 22,916 family-checks (incl. 94 I_m-asserts) | same | **CLEAN** |
| `iterlawn_diag_output.txt` | md5 `7c72c4c6c0a953ebd41a56eab1e266e1` | **identical md5** | **byte-exact** |
| headline | 5,311 checks / 0 violations (A-leg 1,143 + B-leg 4,168), 2.5 s | same | **CLEAN** |

S8-vs-output tie re-checked figure by figure: B1 56/56, B2/B2′/B3 544 each,
B4 544+544, B5 24/56/224, B6 topcontrol 128 + passthroughs 416+128+416 = 960,
A1/A2 464, A3 36, A5 144, A4 35 outer-locus law checks; ~5,300 = 5,311. ✓

## §4 THE S7 FAILURE-DISPLAY BRANCHES — exhaustive row-by-row, BOTH branches

Method: for each of the 11 ledger rows, the row's claims were traced to their
actual consumption sites in S2/S3/S4.0–S4.2 (proof bodies re-read for silent
consumptions, not just citations), then each branch's treatment of the row
was verified or killed.

### 4.1 Branch A — the [IL3]-failure branch (lines 1135–1156, as amended r3)

| # | row | branch's treatment | actual dependency (consumption sites) | verdict |
|---|---|---|---|---|
| 1 | integer layer | NOT affected | S2 consumes L1 = [IL S2 L1] only; no [IL3] token or object anywhere in S2 (SHIFT/D-INT/(★)/WINDOW/cocycle/descent all L1 + elementary; the descent identity φ_{γ+E}=π·φ_γ is formal monomial bookkeeping, no reads) | **EXEMPTION HOLDS** |
| 2 | EXP-KIT | NOT affected | S3 proofs re-displayed in full; (b)/(c) consume L1 ([IL]); "[IL3] S3 verbatim" (line 438) is provenance, not consumption ("re-displayed with proof … self-contained modulo the ACCEPTED [IL] alone") | **EXEMPTION HOLDS** |
| 3 | REALIZE/WELL-DEF/READ-ADD | falls to "open at the [IL3] WELL-DEF m = 1 displays" (r3 erratum) | m = 1 base legs consume [IL3] WELL-DEF(i)/(ii) (lines 482, 511, 513–527); READ-ADD is [IL3]-free but the row falls with its REALIZE/WELL-DEF legs | **CORRECTION RIGHT** (re-derived, §2) |
| 4 | L6 chain | NOT affected; r3 erratum: "Rows 1/2/4 … stand as written" | S4.2 consumes: [IL] base + TRUNC + IH + the degree telescope. The telescope input deg Φ_{j+1} = e_jg_j·deg Φ_j (line 553, uncited) requires (R1) deg C_k < deg Φ_m + existence of the C_k — i.e. S4.1 (the S0.1 line-138 certificate); S4.1's m = 1 base = [IL3]. Every rung ≥ 2 tower invokes realize₁ (Φ₂) | **EXEMPTION KILLED — PE4-F1** (below) |
| 5 | W-MULT Case I | falls, rung ≥ 2 → "open at the rung-2 link" | rung 2 = [IL3]; rung ≥ 3 rides #6 | CORRECT |
| 6 | W-MULT II off DCX | falls, rung ≥ 2 | [IL3]'s DEV-1 = RM-1; + (RM-m) | CORRECT |
| 7 | W-MULT on DCX | not listed | already OPEN at every rung ≥ 2 — no certified status to lose | N/A, CORRECT |
| 8 | THE THEOREM off DCX | falls, rung ≥ 2 | [IL3] + (RM-m) chain | CORRECT |
| 9 | integer corollaries | not listed | = restatements of S2 lemmas (row-1 content); [IL3]-free | COVERED (rides row 1, exempt) |
| 10 | field corollaries | not listed in the branch | table cell is literally "per #8" — falls definitionally with #8 | COVERED BY THE TABLE |
| 11 | measured evidence | not listed | evidence-only ("never proof") — no proof status to lose | N/A, CORRECT |

### 4.2 Branch B — the [IL]†-failure branch (the E4 bracket, lines 1158–1181, as amended r2)

| # | row | branch's treatment | actual dependency | verdict |
|---|---|---|---|---|
| 1 | integer layer | falls to "open at L1"; "its sole [IL] consumption is EQ12-ADD" | verified SOLE: every S2 proof uses L1 + elementary arithmetic only | **CORRECT** |
| 2 | EXP-KIT | falls to "open at L1" (r2 erratum, PE2-F1) | (b)/(c) each cite L1; (a) elementary | **CORRECTION RIGHT** |
| 3 | REALIZE/WELL-DEF/READ-ADD | stands: "rides only the S0.2 elementary base facts and [IL3]†'s m = 1 displays" | dependency set verified COMPLETE: {S0.2 base facts; [IL3] m = 1 displays}; no L1 anywhere in S4.1 (no pair-addition occurs). The [IL3] leg is unaffected by THIS branch. The S0.2 base facts survive an [IL] STRUCTURAL failure: they are textbook facts LISTED in [IL S1] (division algorithm for monic divisors, valuation axioms, res on strict π-excess, q a ring hom), not [IL]-proved lemmas — the genuine asymmetry vs L1, which is [IL]'s own proved lemma ([IL S2]) and so falls with it | **EXEMPTION HOLDS** |
| 4 | L6 chain | falls ("loses its base, every rung") | ✓ (also rides S4.1, dominated by the base loss) | CORRECT |
| 5/6/8 | value layer | fall ("the whole value layer") | ✓ | CORRECT |
| 10 | field clauses | fall (explicitly listed) | ✓ | CORRECT |
| 7 | on-DCX | not listed | already OPEN | N/A |
| 9 | integer corollaries | not listed by number | = row-1 content; the branch's "Row 1 (the integer layer) falls back to open at L1" covers the integer layer wholesale | COVERED |
| 11 | evidence | not listed | evidence-only | N/A |

### 4.3 PE4-F1 — the full finding

**Statement.** Under the S7 [IL3]-failure hypothetical, the L6 chain (#4) at
rungs ≥ 2 IS affected: it falls, with row 3, to "open at the [IL3]
WELL-DEF(i)/(ii) m = 1 displays" (rung 1 is exempt — the 2-read tower has no
canonical lift). The branch's "#4 NOT affected", and the round-3 erratum's
re-affirmation "Rows 1/2/4 of THIS branch stand as written" (line 1146), are
false at row 4.

**Derivation (the note's own text, three steps).**
1. The class data at rungs ≥ 2 includes Φ_{m+1} = canonical ε_m-corrected
   lifts, m ≥ 1; S0.1 line 138 pins their certification: "(well-definedness
   on the class: Lemma WELL-DEF-(n), S4.1)". Every rung ≥ 2 tower invokes
   realize₁ (for Φ₂), and realize_m recurses down to realize₁.
2. The S4.2 proof consumes, uncited (line 553): deg Φ_{j+1} = e_jg_j·deg Φ_j.
   This is NOT free: Φ_{m+1} = Σ_{k≤g_m} C_kΦ_m^{e_mk} with C_{g_m} = 1 has
   that degree (and is monic, as the division algorithm at the next level
   requires) only given deg C_k < deg Φ_m — REALIZE-(m)'s (R1) — plus the
   existence of the C_k (WELL-DEF(i): the (I_m) invariant keeps every
   realize₀ weight ≥ 0, else π^w ∉ O[x]). Both are S4.1 clauses.
3. S4.1's m = 1 base legs consume [IL3]† WELL-DEF(i)/(ii) — the note's own
   operative bracket (513–527) and the r3-corrected row 3. So the corrected
   paragraph now records, three lines above the row-4 exemption, that this
   particular "generic proof of this note" loses its base under the
   hypothetical — and #4 consumes it.

**Why prior passes missed it:** PE r1 (line 265–266 of its report) verified
"L6-(n) … consume[s] only TRUNC + degree telescope + IH(P-L6), exactly as
claimed" — treating the telescope as free-standing arithmetic; PE3 (line 206)
re-checked the telescope's INEQUALITY (e_j−1 ≤ e_jg_j−1) and asserted "#4:
[IL] base only" without tracing the telescope's equality input to S4.1. The
S10 claim DAG abets the miss: it records S4.1 → S4.6 only — the S4.1 →
L6-(n) edge is absent (a silent consumption in the sense of the note's own
hostile charge (i)).

**Failure scenario.** A reader pricing an [IL3]-failure recovery off the
corrected display re-derives the WELL-DEF m = 1 displays for row 3's sake but
treats the L6 chain — "unconditional at EVERY rung given only [IL]" (S4.2
close), "PROVED given only the [IL] base" (S0.3 clause table), "proved given
[IL] only" (S7 row 4) — as untouched collateral, leaving every anchor value,
and hence the entire recovery plan's value layer, resting on uncertified
class objects with no flagged fallback. No live claim breaks: [IL3] is
ACCEPTED (r38 bracket), the branch is structural-completeness display only,
and the real-world grade of row 4 is unchanged (its silent extra input is an
ACCEPTED artifact). The campaign's own standard (PE2-F1 cured at r2, PE3-F1
cured at r3 — both invoked "symmetry of standards" in this same display)
grades exactly this defect shape as a gap.

**Affected display sites (one defect, five expressions):** (i) the branch
row list + parenthetical (1137–1139); (ii) the r3 erratum's "Rows 1/2/4 …
stand as written" (1146); (iii) S7 table row 4, rung ≥ 2 cells ("proved
given [IL]" — silently + S4.1's class certification); (iv) S0.3 clause-table
L6 row + S4.2 closing parenthesis ("given only the [IL] base"); (v) the S10
DAG's missing S4.1 → L6-(n) edge. (S1 item 1's "the L6 chain never consumes
W-MULT, RM, or any DCX exclusion" stays literally TRUE — S4.1 is none of the
three.)

**Cure (the PE3-F1 shape, one clause + attribution touch-ups):** amend the
branch to "…the integer layer (#1) and EXP-KIT (#2) are NOT affected (they
consume only [IL]); REALIZE (#3) AND the L6 chain (#4, rungs ≥ 2 — via the
canonical-lift certification WELL-DEF-(n)/(R1) consumed by the S4.2 degree
telescope and the S0.1 class pin) fall back to 'open at the [IL3]
WELL-DEF(i)/(ii) m = 1 displays' (elementary, independently re-derivable;
rung 1 exempt)"; bracket the same qualifier at the three "given [IL] only"
attribution sites; add the S4.1 → L6-(n) DAG edge.

## §5 Fresh content sweep (clean; findings NONE beyond §4.3)

* **Integer layer re-derived:** SHIFT top + step (Bézout conversion
  1 − ℓγ_j = e(ℓ′−ℓwΦ) exact); D-INT congruence; (★)-POS both cases —
  active-case chain recomputed: e_{j−1}S_{j−1} ≥ (g_{j−1}−1)e_{j−1}γ_j +
  γ_j + h_j/e_j > γ_j ✓; WINDOW worst case (S₁ > (e₀−1)h₀ vs defect ≥
  −(e₀−1)) ✓; slotwise cocycle telescoping ✓; descent/Π_j bookkeeping ✓.
* **EXP-KIT:** (a)/(b)/(c) re-derived; dependency census = L1 only. ✓
* **S4.1:** (I_m) descent chain γ⁽ⁱ⁾ ≥ γ_m/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1}
  ✓; (R1) degree induction ✓; READ-ADD slot-kill induction ✓.
* **S4.4 weights display:** E₁ᴵᴴ-line = B_n + (γ_n − e_{n−1}e_{n−2}γ_{n−1})
  = B_n + h_{n−1} at g_{n−2}=1 ✓ (T-notation reading throughout ✓).
* **W-MULT legs:** II-1 EPS-MULT/ε′-cancellation recomputed (C₀ =
  −c_{n−1}vε_{n−1}(B_{n−1}) = z_n^{δ}vε ✓); II-1 e_n = 1 top sub-case
  B_n − γ_{n+1} < B_n − e_{n−1}γ_n ✓; II-2 slot lines + N3-vacuity
  (k+2 off-grid at e ≥ 3) ✓; II-3 incl. the r1 PC-G4 bracket re-derived:
  line − B_n = 2γ_n − 2e_{n−1}e_{n−2}γ_{n−1} = 2h_{n−1} ✓; PE-N1 supplement
  (E₁ export weight with h_{n−1} to spare) ✓; collision legs + READ-ADD
  kills ✓. RM-1 double-sum ε′-factoring via L1 ✓; the r1 PC-G3 corrected
  bound 2e₀g₀−1 < 2e₀g₀ ✓.
* **S4.7 DCX:** outer-bound proof (Q⁰ impossible: T_m ≤ 2e−2; Q¹ needs
  CII_{m−1} ⟹ g_{m−2} = 1 + extremal track) ✓ under the PE-G1 (given IH
  package) qualifier, bracketed at all three sites ✓; emptiness legs ✓;
  no-consecutive-degree-1 consequence ✓.
* **S5 assembly:** one EXP-KIT(c) kernel per level with T = S_j; δ_j^{pl}
  cancellation inside kernels ✓; matches the S0.3 recursion exactly ✓.
* **Corollaries:** COR-3 e_n = 1 collapse recomputed (δ = 0, D_n = δ_n^{pl},
  S_{n−1} = δ_n^{pl}γ_n — verbatim (ITER-LAW-(n−1))) ✓; COR-4 ρ =
  ∏z_j^{−ℓ_{j−1}Π_{j−1}} re-derived from EXP-KIT(a) + the descent shifts ✓;
  COR-5 ✓; COR-1/2 ride S2 ✓; S6.6 fences honest ✓.
* **T-notation:** head erratum + all site brackets consistent; the (P-DS)
  display's inline "S_{r+1} := s_{r+1}(β)+s_{r+1}(β′)" is unambiguous under
  the global read-as-T rule ✓; composed S_j verified absent from S4.3–S4.7 ✓.
* **Rule-8 / incorporation convention:** head declaration + both † blocks
  pasted once; operative pastes at the four declared sites verified present
  (header, S4.3 base, S4.1 bracket, S7 r38 bracket); composition-time
  0/2-descriptions superseded-as-dated by the r38 bracket ✓.
* **S8:** all figures tie to the output (§3) ✓; md5s of script + output
  match the note's claims ✓; "instance evidence only" standing ✓.
* **Boxing:** the (RM-m) box self-contained (setting/input/claim/status/
  price) ✓; (W-MULT-DCX-m) priced at S4.7 ✓; S9 fences ✓; S10 charges ✓.

## §6 Provenance appendix (verbatim slices, current text @ 4e8f027)

* Line 138 (S0.1): "(well-definedness on the class: Lemma WELL-DEF-(n), S4.1)".
* Line 248 (S0.3 clause table): "L6-(n) ANCHOR-VAL = ε-chain, all n | PROVED
  given only the [IL] base ( … no RM, no DCX) | S4.2".
* Lines 551–554 (S4.2): "Degree telescope: deg a = Σ_{j<n} s_{j+1}·deg Φ_j ≤
  Σ_{j<n} (e_j−1)·deg Φ_j ≤ Σ_{j<n} (deg Φ_{j+1} − deg Φ_j) = deg Φ_n − d₀ <
  deg Φ_n (using deg Φ_{j+1} = e_jg_j·deg Φ_j ≥ e_j·deg Φ_j)."
* Lines 562–563 (S4.2 close): "(The L6 chain is therefore unconditional at
  EVERY rung given only [IL] …".
* Line 482 (S4.1): "m = 1 is [IL3] WELL-DEF(i)'s display"; line 511: "(At
  m = 1 this is [IL3] WELL-DEF(ii) verbatim.)".
* Lines 514–516 (S4.1 operative bracket): "the m = 1 base legs of
  REALIZE-(m)/WELL-DEF-(n) above consume [IL3] WELL-DEF(i)/(ii)".
* Lines 1137–1139 (branch A): "— the integer layer (#1), EXP-KIT (#2),
  REALIZE (#3), and the L6 chain (#4) are NOT affected (they consume only
  [IL] and this note's generic proofs)."
* Line 1146 (r3 erratum): "Rows 1/2/4 of THIS branch stand as written".
* Line 1126 (S7 table row 4): "| 4 | L6 chain (anchor = ε-chain) | ACCEPTED |
  proved given [IL] | proved given [IL] | proved given [IL] only (S4.2) |".
* Lines 1261–1262 (S10 DAG): "TRUNC → L6-(n), CASE-SPLIT, S4.5/S4.6" /
  "REALIZE-(m) → WELL-DEF-(n) → S4.6 (Ĉ-clauses); READ-ADD-(m) → S4.6" —
  no S4.1 → L6-(n) edge.
* Prior-pass provenance: PE r1 report lines 265–266 ("L6-(n) verified to
  consume only TRUNC + degree telescope + IH(P-L6), exactly as claimed");
  PE3 report line 206 (telescope inequality only) and its F1 section
  ("#4: [IL] base only" — bare assertion, no S4.1 trace).

— ITERLAWN-PE4 (Fable), 2026-08-03 wallclock (campaign 2026-08-08), on
4e8f027; re-runs from `verification/openmath/` at repo HEAD; both scripts
byte-unchanged from their cited pins.
