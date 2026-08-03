# ITERLAWN-PE7 — Fable round-7 pass on the 61dc2e0 text: CLEAN 0C/0G (+2 nits) — the machine census INDEPENDENTLY RE-RUN AND REPRODUCED EXACTLY (194/194, zero divergence); errata-r6 fidelity verified; zero mathematical findings

## VERDICT BLOCK

* **Grade: 0 critical / 0 gaps (+2 nits, §6).** With PC6 CLEAN (0C/0G @
  3a281e7, landed mid-pass), both round-7 legs are clean — the 2-clean
  model-diverse bar for the general-n note is MET on the 61dc2e0 text.
* **THE MACHINE RE-RUN (charge item 2, the pass's designated duty):
  EXACT MATCH on every axis.** My own independent reimplementation of the
  8-pattern scan (own code, written from the r6 bracket's stated pattern
  list BEFORE consulting PE6's method paragraph beyond the pattern
  definitions; committed as `verification/openmath/iterlawn_pe7_census.py`)
  over the pinned 0672082 text returns: **194 raw hits on 147 distinct
  lines — N = 194 vs PE6's 194**; per-pattern counts identical (consum 84,
  only 51, never 18, alone 15, self-contained 9, independen 8, free 6,
  not-affected 3); the hit-line set has **ZERO symmetric difference** with
  PE6's Appendix A line map (147 = 147, no line hit that Appendix A lacks,
  no Appendix-A line my scan misses); my raw-hit counts summed over
  Appendix A's class line-lists reproduce the disposition table exactly
  (R-rows 88, F-families 21, apparatus 53, quoted 8, non-genre 18,
  positive 6 — total 194); and rows 13/18's sites (L632, L1033–34) are
  confirmed pattern-free. Enumeration completeness of the pinned text is
  now a machine fact CONFIRMED BY A SECOND INDEPENDENT PROGRAM.
* **Errata-r6 fidelity: VERIFIED** (§2) — the diff is additive-only (42+0;
  both file reconstructions byte-exact); the note bracket's numbers are
  all faithful to PE6's report (each checked against my own re-run, not
  just against PE6's text); the supersession claim and the
  four-confirmation claim are accurate; rows 13/18's "content verified in
  r4/PE5" parenthetical checks (both rows are purely-V in the r4 table,
  hence inside PE5's 12 re-derived rows); the 9f9910c incorporation
  convention cited for the by-reference incorporation exists as described.
* **Execution re-runs: both exit 0, zero violations** (§4). diag
  byte-identical (md5 `7c72c4c6c0a953ebd41a56eab1e266e1` = committed);
  reimpl semantically identical, sole diff = ONE wall-clock digit (I4A
  `0.1s` → `0.2s`) — the PE4-classified benign species (PE6 saw two such
  digits; the count wobbles, the content never has).
* **Fresh content sweep: zero mathematical findings** (§5) — thirteen
  independent spot re-derivations across the integer layer, S4.1/S4.2,
  all three II-legs, DCX, and the corollaries, all confirming the
  displays; concurring with PC6's independent content pass.
* **The two nits** are wording compressions in the r6 RECORD (one in the
  ledger append, one in the note bracket), both with a correct authoritative
  record incorporated by reference and zero grade/math impact — they do not
  break CLEAN (the PE2-N1 species, graded nit then and now).

## §1 Charge, identity, pins

ITERLAWN-PE7, Fable round-7 fresh verifier on the general-n note
`lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` as amended at 61dc2e0
(errata round 6 = the machine census installed as the enumeration of
record). Binding scope rule (ledger 61dc2e0): the census question is BOUND
to the machine artifact — verify faithful incorporation + re-run the
machine census independently; fresh pattern-scope quibbles out of charge.
Duties: (1) errata-r6 fidelity; (2) the machine re-run; (3) execution
re-runs; (4) fresh content sweep; (5) this report + ledger + scoped commit.

Pins: note @61dc2e0 md5 `d21d8efd78b142bca7b4747e35b43e2a` (= HEAD text at
pass start AND at report time); pinned census base @0672082 md5
`5811db126d1ed0824e4870b20e0fd774` (= the PE5/PE6 pin); scripts
`iterlawn_pe_reimpl.py` md5 `cae45db2318b89520dd5484466ef3604`,
`iterlawn_diag.py` md5 `cd7581b7fd9df555e517b69556199ef3` (both = the
standing pins). Mid-pass event: PC6 landed at 3a281e7 (CLEAN 0C/0G; report
read AFTER my verdict was formed — §7).

## §2 Errata-r6 fidelity (VERIFIED, six legs)

1. **Additive-only.** `git diff 08a52e9..61dc2e0`: 42 insertions, 0
   deletions, two files. Note: deleting the 23 inserted lines (1168–1190
   of the r6 text) reproduces the 362d118 file **byte-exactly**; ledger:
   the r6 text = the 08a52e9 ledger + 19 appended lines, **byte-exact**
   head match. PE6's report file untouched at HEAD (0-diff vs 61dc2e0).
2. **The bracket's numbers, checked against my own re-run** (not merely
   transcribed): 8 widened patterns ✓; 194 raw hits ✓; 147 lines ✓;
   194/194 mapped, zero unadjudicated ✓; 88/21/53/8/18/6 ✓ (all six
   reproduced by my scan over Appendix A's line lists); seven families ✓;
   ≈15 textual sites ✓ (16 hit-lines, L1287–88 one two-line site — PE6's
   own "≈15" language); two judgment-added rows 13/18 ✓ (machine-confirmed
   pattern-free at L632/L1033–34).
3. **Supersession claim accurate.** The hand census is superseded by PE6
   §3 + Appendix A "incorporated by reference per the 9f9910c convention"
   — 9f9910c is the incorporation-convention adjudication commit as cited;
   the artifact incorporated (PE6's report @08a52e9) is committed,
   untouched, and now independently re-verified (§3).
4. **Four-confirmation claim accurate.** r4's sweep + PE5's 12-row
   re-derivation + PC5's re-derivations + PE6's machine pass, the last by
   program — matches PE6's verdict block ("a fourth independent sweep and
   for the first time by machine"); conservative (PC4's adversarial
   re-derivation of the V-rows would be a fifth, unlisted).
5. **Rows 13/18 parenthetical.** "(their content verified in r4/PE5)":
   both rows carry bare status V in the r4 sweep table (pinned text
   L1125/L1130), hence both sit among the 12 purely-VERIFIED rows PE5
   independently re-derived (e4a8e8a). ✓
6. **PC5-sites naming.** The bracket names PC5's two sites "the II-3
   'WEIGHT clauses only' engine sites and the S1/S8 'instance evidence
   only' family" — correct on PC5's actual citations (the II-3 instance;
   L319); the families containing them are larger (F2 also holds II-2
   L865; F1 is five sites), which the bracket separately counts correctly
   in the 21/seven-families figures. Not a finding.

## §3 THE MACHINE RE-RUN (charge item 2 — the deterministic check)

**Method.** Own scanner (`verification/openmath/iterlawn_pe7_census.py`,
md5 `60a0b67b422360e48d0417307a7cdc62`), written from the r6 bracket's +
PE6 §3's stated pattern definitions: case-insensitive `\bonly\b`,
`\balone\b`, `not\s+affected`, `self-contained`, `free` (substring),
`independen` (substring), `consum` (substring), `\bnever\b`, run
line-by-line over all 1,417 lines of `git show 0672082:` (md5 verified =
the pin). Appendix A's line map transcribed verbatim into the script as
the comparison target.

**Result: EXACT MATCH, all axes.**

| axis | PE6 (the artifact of record) | PE7 (this re-run) | match |
|---|---|---|---|
| raw hits N | 194 | **194** | ✓ |
| distinct hit-lines | 147 | **147** | ✓ |
| per-pattern (consum/only/never/alone/self-c/indep/free/not-aff) | 84/51/18/15/9/8/6/3 | same | ✓ |
| hit-lines vs Appendix A line map | 147 mapped | symmetric difference **∅** | ✓ |
| class hit-sums (R/F/A/B/C/D) | 88/21/53/8/18/6 | same, recomputed from my hits | ✓ |
| rows 13/18 sites (L632, L1033–34) | pattern-free | **0 hits, confirmed** | ✓ |

Mapping attributions spot-verified at source on a sample (L139 R1, L208
R23, L528 B-inside-row-11, L715/L932 D, L803 grammatical-alone C, L1391
A-hostile-charge): each line's content matches its Appendix-A class. Zero
divergence of any kind; the r6 bracket faithfully incorporates a machine
artifact that a second independent implementation reproduces bit-for-bit
on every reported number. **The finding the charge defines (a mismatch)
does not exist.**

## §4 Execution re-runs (charge item 3)

* **iterlawn_pe_reimpl.py:** exit 0; `== BASELINE VIOLATIONS: 0 ==`; 940
  pairs; family totals match the committed output exactly (K1_shift 3444,
  K3_star 3444, K7_law 940, K10_sharp2 940, …); mutations
  `7/7 caught+visible`; elapsed 7.0s. Fresh md5
  `ecf7cd495f25bffbf1cee2c6d8725e85` vs committed
  `cfad79439821551f9c6a572f5d627d0b`: sole diff = ONE per-instance
  wall-clock digit (I4A line, `0.1s` → `0.2s`) — the PE4-classified benign
  species; zero count/violation diffs.
* **iterlawn_diag.py:** exit 0; **byte-identical** (fresh md5
  `7c72c4c6c0a953ebd41a56eab1e266e1` = committed); `== VIOLATIONS: 0 ==`,
  `DIAG VERDICT: CLEAN`; count block independently re-summed this pass:
  18 families, total **5,311** (matches S8's ~5,300 figure), elapsed 2.5s
  (= the S8 wallclock).

## §5 Fresh content sweep (charge item 4 — the standing surface)

Independent re-derivations performed this pass, all CONFIRMING the
displays: (i) the SHIFT-(n) step algebra — (S-rec), the defect
substitution, and the Bézout identity 1 − ℓγ = e(ℓ′ − ℓwΦ), including the
j = 1 convention leg (w₀Φ₀ = 0, γ₁ = h₀); (ii) D_j-INT's congruence
s(β) ≡ ℓβ (mod e); (iii) the (★)-POS active-case chain incl. the
γ_{j+1} = e_je_{j−1}g_{j−1}γ_j + h_j expansion; (iv) WINDOW-(n)'s
S₁ > (e₀−1)h₀ leg; (v) EXP-KIT (a) exponent algebra; (vi) the REALIZE-(m)
invariant descent γ⁽ⁱ⁾ ≥ γ_m/e_{m−1} > e_{m−2}g_{m−2}γ_{m−1} and (R1);
(vii) WELL-DEF(i)'s (I_m) check; (viii) the L6-(n) degree telescope;
(ix) the CASE-SPLIT overflow equivalences under the T-reading; (x) all
three II-legs' slot-line arithmetic — II-1's C₀ ε′-cancellation
(EPS-MULT + τ = ε(γ_n)^{−1}c), II-2's R¹/Q¹ bounds (B_n + h_{n−1},
B_n + 2h_{n−1}, the e_{n−1} ≥ 3 off-grid leg), II-3's PC-G4 bracket
(line − B_n = 2h_{n−1} re-derived) and the E₁ⁿᵉʷ top-line
Γ″ + h_n + e_nh_{n−1}; (xi) the DCX outer-bound slot arithmetic (Q⁰
impossible, Q¹'s two emission modes); (xii) the S5 assembly — EXP-KIT(c)
per level with T = S_j yielding exactly D_j, internal carries cancelling;
(xiii) COR-4's ρ = ∏ z_j^{−ℓ_{j−1}Π_{j−1}} from EXP-KIT(a). Also
re-adjudicated with fresh eyes: F1 (evidence-only — S8/S4.6/S2 diagnostic
citations all labeled, no proof body consumes sealed data) and F2 (II-2
consumes only R⁰'s read, II-3 only E₀ᴵᴴ's — weight clauses only from the
E₁ᴵᴴĈ calls), concurring with PE6/PC5/PC6. The statement, architecture,
(RM-m) boxing and pricing, DCX honesty, T/S separation, both S7 branches,
the r38 conditionality arithmetic, S8 labeling, and the rule-8 apparatus
are coherent. **No mathematical finding — the seventh consecutive pass
with zero.**

## §6 Nits (recorded; no cure owed on their own; the PE2-N1 species)

* **N1 (ledger append, r6).** The clause "both executables byte-identical
  (7th consecutive byte-stable round)" misstates PE6 §4 under the natural
  outputs reading: PE6's diag WAS byte-identical, but its reimpl output
  differed in two wall-clock digits (PE6: "semantically identical, sole
  diff = two wall-clock digits"; my re-run: one digit). A true reading
  exists (the executables/scripts themselves are byte-identical to the
  standing pins, every round), but in a results-summary list the clause
  reads as an outputs claim. Authoritative record (PE6 §4, incorporated by
  reference) is correct; ledger-side only; zero impact. Suggested
  restatement at the acceptance fold: "diag byte-identical; reimpl
  content-identical modulo wall-clock digits — 7 consecutive rounds with
  zero content drift."
* **N2 (note bracket, r6).** "21 at the seven site-families F1–F7, ALL
  content-true, each re-derived" — "each re-derived" compresses PE6's
  mixed adjudication basis: F1/F2 were re-derived IN-PASS by PE6 (and
  again by PC6 and this pass); F3–F7 were adjudicated on standing
  on-record verifications (r1 E1/E6, the rule-8 audits, the PC3/PE4/PC4/
  PE5 S7 audits, the operational re-run record). Every family does carry
  an on-record derivation, so the claim is defensible read arc-wide;
  display precision only.

## §7 PC6 cross-check (read after verdict formation)

PC6 @3a281e7: CLEAN 0C/0G on the same 61dc2e0 text; its NOTE 1 records
that repo execution was unavailable in its sandbox (no bubblewrap), so
byte-level and executable checks were not re-run there. This pass supplies
exactly those legs (§2 leg 1 reconstructions, §3 machine re-run, §4
executions) — the two round-7 legs are complementary as designed, and
their content adjudications (F1/F2/F6, the full sweep) concur
independently.

## Appendix — provenance

* Commit chain: 0672082 (pinned census base) → … → 362d118 (r5) → c2992a0
  (PC5) → 08a52e9 (PE6 + Appendix A, the artifact of record) → 61dc2e0
  (r6, the text under review) → 3a281e7 (PC6, mid-pass). HEAD at pass
  start = 61dc2e0; working tree clean on all pass-relevant paths.
* md5s: pinned text `5811db126d1ed0824e4870b20e0fd774`; 61dc2e0 text
  `d21d8efd78b142bca7b4747e35b43e2a`; reimpl/diag scripts = standing pins
  (§1); fresh outputs §4; census script
  `60a0b67b422360e48d0417307a7cdc62`.
* Reproduce the machine re-run:
  `git show 0672082:lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md > /tmp/pinned.md`
  then `python3 verification/openmath/iterlawn_pe7_census.py /tmp/pinned.md`
  — prints the counts, the per-pattern table, both direction diffs vs the
  transcribed Appendix A, the class sums, the row-13/18 check, and
  `MATCH VS PE6: EXACT` (exit 0 iff every axis matches).
* Key verbatim slices re-checked at source this pass: L208 `(… S₀ =
  D₁h₀ + S₁ℓ₀′ — computed by the recursion but consumed by nothing.)` ·
  L632 `[No DCX exclusion needed for this clause — L6-(n), S4.2.]` (no
  pattern token) · L1033 `no cross-level denominator ever forms` ("ever":
  no pattern token) · L865 `E₁ᴵᴴĈ = R¹+Q¹Φ (WEIGHT clauses only)` · L891
  `(engine on E₁ᴵᴴĈ, weight clauses only)` · L319 `INSTANCE EVIDENCE
  ONLY, never proof steps`.
