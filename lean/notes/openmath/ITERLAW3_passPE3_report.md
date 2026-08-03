# ITERLAW3 pass PE3 (Fable, round 3: errata-r2 fidelity + execution + fresh full content read) — 2026-08-03 (campaign 2026-08-08)

**Pass:** ITERLAW3-PE3, the Fable leg of acceptance round 3 on
`lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md` as re-amended at a687b80
(errata round 2). Charge: (1) errata-r2 fidelity on `git diff
467b523..a687b80` incl. independent re-derivation of the corrected S4.5
display and a full n=3-token classification; (2) re-run of all three frozen
runners from /tmp copies, byte-exact bar; (3) fresh full content read of the
re-amended note over the standing charge surface (DEV-1, cases, L7
consumption, integer layer, class pin, DCX honesty, corollaries, open-lemma
displays). FRESH VERIFIER discipline: the full note was read and the verdict
below frozen BEFORE consulting any round-1/2 report beyond the arc facts;
the concurrent Codex PC3 report (5bdca01, found already landed) was not
opened before freezing (its one-line verdict was visible in `git log`
during provenance collection, after my content read and execution leg were
complete — disclosure, no findings were derived from it).

## VERDICT BLOCK

**VERDICT: CLEAN (0 critical / 0 gaps / 0 new nits).**

* **Errata-r2 fidelity: VERIFIED.** The a687b80 commit touches exactly two
  files: the note (+22/−2 = the two erratum brackets) and the ledger
  (+20-line append). Both note hunks are insertion-only: each removed line's
  full text is preserved verbatim inside the additions (hunk 1 splits
  "...read 0 either way. Hence" around the S4.5 bracket; hunk 2 splits
  "...Candidate 2 at n = 3:" around the S6.6 bracket, colon preserved after
  the bracket). No math line altered; S2–S5 proved core byte-stable outside
  the S4.5 bracket insertion. The wider range 467b523..a687b80 additionally
  contains only the intervening chartered GENERAL-n unit 5fe901e (4 files,
  100% additive: ITERLAWN_PROOF + iterlawn_diag.py + its output + its own
  ledger append) — declared in the a687b80 commit message and the arc
  facts; it does not touch this note or any sealed artifact.
* **The corrected S4.5 derivation is RIGHT** (independently re-derived, see
  Fidelity A below): w₂(E₁) = B₂ − e₁γ₂ exactly; at g₁ = 1, e₂ = 1 one has
  γ₃ = e₁γ₂ + h₂, so the slot-(S₃+1) weight B₂ − γ₃ = w₂(E₁) − h₂ < w₂(E₁)
  (h₂ ≥ 1), i.e. the slot weight sits strictly below the E₁ line and the
  R3w read convention returns 0. The old middle link "= w₂(E₁) + 0" was
  indeed false (B₂ − e₁γ₂ + h₂ = w₂(E₁) + h₂); the erratum's diagnosis,
  correction, and "conclusion standing" claim all check.
* **NO residual rung-mislabel token.** Fresh grep of `n = 3`/`n=3` over the
  whole note: 12 hits, every one classified (table below); each
  rung-indexed occurrence is either correct-as-written (rung 3 = the 4-read
  ITERLAW4 battery) or bracket-covered with the rung-2 correction displayed
  at the token. The two round-2 findings (S4.5 display link = PC2-g/PE2-F1;
  S6.6 dictionary tokens = PC2-c/PE2-F2) are both CURED.
* **Execution: ALL GREEN, byte-exact, all five artifacts.** All three
  runners re-run from /tmp copies: `iterlaw3_pe_reimpl.py` reproduces
  3,344 pairs / 55,186 checks / 0 violations / SYMBOLIC 20000/20000 /
  MUTATIONS all fired / DCX locus OK / VERDICT ALL GREEN;
  `iterlaw3_proof_diag.py` reproduces 1,424 pairs, aggregate census
  I 912 / II-1 368 / II-2 40 / II-3 88 / DCX 16, 0 violations, GREEN;
  `iterlaw3_pe2_e1witness.py` reproduces the 4 + 48 DCX witnesses at the
  exact split-classes, 52/52 instance data, GREEN. All five outputs
  (2 stdout captures + 2 results-JSONs + diag stdout) byte-identical to the
  frozen artifacts (`cmp` clean).
* **Fresh full content read: no new findings.** Every load-bearing
  computation on the standing charge surface re-derived by hand (details in
  Content C below); the round-1 brackets (S6.3 re-scope, S4.1 DEV-1 scope +
  fenced corner, rung relabels, N1/N3) all stand and are honest; DCX
  honesty, the class pin, the consumption manifest, and the open-lemma
  displays are exact.

**Acceptance consequence:** PE3 is CLEAN. The concurrent Codex PC3 leg
reported CLEAN (0C/0G) at 5bdca01 on the same a687b80 text. Both round-3
legs of the 2-clean model-diverse bar are therefore CLEAN on the current
text; the acceptance fold (counter, display upgrades per note S9, ledger
defined-term block) is the orchestrator's, not this pass's — until it is
executed, the note's own S0.4 standing language (attempt grade) governs.

## Fidelity A — the a687b80 diff, hunk by hunk

**Hunk 1 (S4.5, lines 594–604 post-image).** Bracket inserted between
"...read 0 either way." and "Hence". Independent re-derivation of the
corrected chain (from the note's own definitions, not the bracket):

* w₂(E₁): E₁ = aΦ₁^k is a single Φ₁-digit at slot k with w₁(a) = B₁, so
  w₂(E₁) = e₁B₁ + kγ₂ = e₁B₁ + (S₂−e₁)γ₂ = B₂ − e₁γ₂ (B₂ = e₁B₁ + S₂γ₂). ✓
* The slot-(S₃+1) weight at the read Γ″ (e₂ = 1 branch, on-grid):
  Γ″ − (S₃+1)γ₃ = (B₂ + S₃γ₃) − (S₃+1)γ₃ = B₂ − γ₃ (Γ″ = e₂B₂ + S₃γ₃ at
  e₂ = 1). ✓
* γ₃ = e₂·w₂Φ₂ + h₂ = e₂e₁g₁γ₂ + h₂ = e₁γ₂ + h₂ at g₁ = 1, e₂ = 1. ✓
* Hence B₂ − γ₃ = B₂ − e₁γ₂ − h₂ = w₂(E₁) − h₂ < w₂(E₁) since h₂ ≥ 1
  (S0.1 read data). The digit's line w₂(E₁) exceeds the slot weight, so the
  R3w convention (C_j = 0 unless w₂(A_{s_j}) equals the slot weight) reads
  0. ✓ Exactly the bracket's one-line derivation, and exactly the
  sentence's pre-existing final clause "w₂(E₁) = B₂ − γ₃ + h₂ > slot
  weight" (which is equivalent: B₂ − γ₃ + h₂ = B₂ − e₁γ₂ = w₂(E₁) ✓).
* The struck middle link: B₂ − e₁γ₂ + h₂ = w₂(E₁) + h₂ ≠ w₂(E₁) + 0 — the
  erratum's diagnosis is exact; the inequality B₂ − γ₃ < B₂ − e₁γ₂ + h₂ was
  true but the "= w₂(E₁) + 0" tail mislabeled it (and as PE2 noted, a
  reader deriving from that tail would get slot weight < w₂(E₁) only via a
  false identity). The bracket's consumption note is also accurate: S4.6's
  "Top level verbatim as in S4.5" (Case II-2, line 658–659) rides the
  corrected derivation with w₂(E₁) there ≥ B₂ − e₁γ₂ (the II-2 E₁ has a
  second, higher slot) — the inequality only strengthens.

**Hunk 2 (S6.6, lines 845–853 post-image).** Bracket inserted between
"...Candidate 2 at n = 3" and the display colon. It STRIKES the dictionary
tokens to (rung) n = 2 with the correct scoping argument: inside the
recursion dictionary, Candidate 2's n is a bound index of the source
(L3CONVERGENCE S2, whose convention (n+1)-read = rung n makes this 3-read
note the rung-2 instantiation), so the round-1 "counts READS" gloss cannot
re-bind it; the section title's "at n = 3, derived" is corrected by the
same bracket. The displayed equations below the bracket are indeed the
top-index-2 instantiation (S_2/D_2/S_1/D_1 with γ₃ as the top modulus) —
"no math content changes" checks.

**Ledger hunk.** The a687b80 append to `BRIDGE_ADJUDICATIONS_2026-07-30.md`
is a 20-line block ("ITERLAW3 errata round 2 APPLIED — 2026-08-03"),
accurately summarizing both remedies, the round-2 verdicts (PC2 cf013a4 1C/1G,
PE2 467b523 0C/2G, convergent), counter 0/2, round 3 next; pure append
(the prior tail, the GENERAL-n block, is untouched above it).

## Fidelity B — the n = 3 token classification table (fresh grep, whole note)

`grep -n 'n = 3\|n=3'` (12 hits; `n=3` unspaced: 0 hits; adjacent `n ≥ 3`
hits included for completeness):

| line | token in context | classification | status |
|---|---|---|---|
| 187 (S0.4 status row) | "the (ITER-LAW-n) recursion at n = 3 [errata r1: reads; = RUNG n = 2 — S6.6 rung bracket]" | recursion-index token | BRACKET-COVERED (rung-2 value displayed at the token) |
| 223 (S1 close) | same phrase + same r1 bracket | recursion-index token | BRACKET-COVERED (rung-2 value displayed) |
| 827 (S6.6 title) | "(ITER-LAW-n) at n = 3, derived" | rung-indexed (dictionary) | BRACKET-COVERED by the r2 bracket ("the section title's 'at n = 3, derived' ... corrected to (rung) n = 2") |
| 834 (inside r1 bracket) | quoted token '"at n = 3" in this section's title...' | meta-text (quotation of the glossed token) | superseded for title+display sentence by the r2 bracket, which names exactly those two |
| 838 (r1 bracket) | "The 4-read battery ... is RUNG n = 3" | rung-indexed | CORRECT as written (4-read = rung 3) |
| 841 (r1 bracket, rung ledger) | "n = 3 MEASURED GREEN (4-read battery)" | rung-indexed | CORRECT as written (rung 3 = the ITERLAW4 battery) |
| 845 (S6.6 display sentence) | "Candidate 2 at n = 3" | rung-indexed (dictionary) | BRACKET-COVERED by the immediately following r2 bracket (corrected to (rung) n = 2) |
| 850 (inside r2 bracket) | quoted token "'at n = 3, derived'" | meta-text | part of the correction itself |
| 861 (confirmed-rungs sentence) | "n = 1 accepted [IL], n = 2 this note (off DCX); the n ≥ 3 recursion..." | rung convention throughout | CORRECT as written (r1 bracket already certifies this sentence) |
| 885 (S7) | "recursion display at n ≥ 3" | rung-indexed | CORRECT (bracket at 886–888 confirms "already RUNG-indexed (= orders ≥ 4)") |
| 887 (S7 bracket) | "the 'n = 4 probe' counts READS" | reads-name | CORRECT (probe named by reads) |
| 888 (S7 bracket) | "its battery is RUNG n = 3" | rung-indexed | CORRECT (4-read battery = rung 3) |

Every rung-indexed occurrence now either says the right rung or carries a
bracket displaying "(rung) n = 2" at the token. **Non-blocking observation
(not a finding):** the r1 inline brackets at lines 187/223 retain the
one-word classification "reads" for the recursion-index tokens, which sits
in mild tension with the r2 bracket's (correct) ruling that a
recursion-indexed n cannot be re-glossed as a reads count; but both
brackets display the operative correction "= RUNG n = 2" at the token and
point to the S6.6 rung bracket, so no reader can extract a wrong rung from
any occurrence. Cure (a one-word strike inside two r1 brackets) can ride
the acceptance fold if desired; it does not affect the CLEAN verdict.

## Execution — re-run actuals (all from /tmp/pe3_run copies; byte-exact bar)

Method: the three frozen runners copied to `/tmp/pe3_run/` and executed
there (python3; the diag additionally consumes the pinned harness of record
— `grb_order2_check.py`, `strata3_probe.py`, `iterlawr_probe.py`,
`strata_probe.py` — copied read-only alongside, exactly the S0 PRINT-
CONSUMPTION pins; the reimpl and witness runners are import-self-contained
by design). Outputs then `cmp`'d against the frozen repo artifacts.

| runner | actuals (this re-run) | frozen comparison |
|---|---|---|
| `iterlaw3_pe_reimpl.py` (sealed be9a77b) | 10 towers, PAIRS 3344, CHECKS 55186, VIOLATIONS 0; SYMBOLIC 20000/20000; all 6 mutations FIRED (M1 868 / M2 768 / M3 464 / M4 720 / M5 784 / M6 1288 violations, = visibility); DCX measure 16/16/48 on the three DCX-live towers, 0 elsewhere; DCX instance data 80/80; "VERDICT: ALL GREEN" | stdout + results.json BOTH byte-exact |
| `iterlaw3_proof_diag.py` (sealed 8ba1820) | 5 shapes × {ℤ₃, F₂[[t]]}, 1,424 pairs; aggregate census DCX 16 / I 912 / II-1 368 / II-2 40 / II-3 88; TOTAL identity violations 0; "DIAG VERDICT: GREEN" | stdout byte-exact |
| `iterlaw3_pe2_e1witness.py` (sealed 467b523) | e₂=1 ℤ₅ tower: 4/4 DCX at split-class ((2,1,0),(2,1,0)); e₁=1 TW2/F₃[[t]]: 48/48 DCX at the 12 predicted split-classes; on-DCX instance data thm/wmult/prod/shape/Q¹≠0/naive-overflow 52/52 each; CX-embed 4/4; integer reductions 0 violations both blocks; "PE2 E1-WITNESS VERDICT: GREEN" | stdout + results.json BOTH byte-exact |

Exit codes 0 on all three final runs. Note for reproducers: the diag run
requires the four harness modules next to it (ModuleNotFoundError
otherwise); this is by design (it cross-checks the note against the harness
of record) and identical to the PE/PE2 procedure.

## Content C — fresh full read of the amended note (standing charge surface)

Every item below independently re-derived on this pass (not replayed from
prior reports); listed by surface.

* **Integer layer (S2), unconditional:** L2-(3a) re-derived (γ₃ = e₂w₂Φ₂ +
  h₂ absorbs the L1 carry); D₂-INT via s₂(β) ≡ ℓ₁β (mod e₁); L2-(3b) via
  β₂ = e₁β₁ + s₂γ₂ at all three arguments and 1 − ℓ₁γ₂ = e₁(ℓ₁′ − ℓ₁w₁Φ₁);
  D₁-INT likewise; WINDOW all three cases checked incl. the (iii) bound
  e₁Σ ≥ γ₂ + h₂ > e₁(e₀−1)h₀. All exact. The (i) "wait —" artifact remains
  properly bracket-struck (r1/N1).
* **EXP-KIT (S3):** (a)/(b)/(c) re-derived; the two instantiation rows
  (T = δ₃γ₃ at level 2, T = Σ at level 1) are the only kernels S5 consumes
  — no cross-level denominator anywhere, matching COR-1's claim.
* **WELL-DEF (S4.0):** the realize1 domain bound e₀u(gp) > e₀(g₀−1)h₀
  re-checked (the displayed rearrangement is exact); (Ĉ1–3) follow.
* **DEV-1 (S4.1) with the r1 erratum:** base and step re-derived; the
  corrected measure claim confirmed (junkΦ exponent j − e₀ + 1 descends iff
  e₀ ≥ 2; at e₀ = 1, i = g₀−1 gives exactly j — non-descending); the fenced
  corner {e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀} verified UNREACHED: S4.5's e₀ = 1
  inputs have J = S₁ + s(γ₂) = 0 (all s ≡ 0 at e₀ = 1) hence exponent
  m ≤ g₀−1 in base range; S4.6 forces e₀ ≥ 2 via δ₁ = 1 ∧ S₁ ≤ 2e₀−2; at
  d₀ = 1 the DIGIT-SPLIT Y-cofactor vanishes by degree. Read-transparency
  telescope re-derived (ψ₀(z₁) = 0 kills the head; exponent arithmetic
  (j−e₀g₀−s*)/e₀ + g₀ = (j−s*)/e₀ exact; final abscissas ≥ s*).
* **L6-(3) (S4.2):** the degree bound deg a < deg Φ₂ and the slot-0
  placement re-checked; the accepted [IL L6] consumed exactly through the
  S0.3 dictionary (β₂(γ) ∈ [IL]'s W ⟺ γ ∈ W₃ re-verified from u₁ = u).
* **CASE-SPLIT + L7 consumption (S4.3):** the partition re-derived from the
  displayed [IL L7] development shapes; overflow thresholds at g₁ = 1
  exact (inner I: S₂ ≥ e₁ ⟺ δ₂ = 1; inner II: S₂+1 ≥ e₁ splits II-2/II-3);
  w₂(A) = B₂ and R2v(A) = z₂^{δ₂}z₁^{δ₁}ε₁(B₁) both re-derived from the
  digit weights. Consumption manifest correctly declares BOTH the L7 forms
  and its displayed development shapes.
* **S4.5 (Case II-1):** full re-derivation — the G_m line computation, the
  Φ₀-exponent bounds (both g₀ regimes), the (J−s*)/e₀ = δ₁+ε′ double-L1
  step, the EPS-MULT ε′-cancellation to C₀ = z₂^{δ₂}z₁^{δ₁}ε₁(B₁), the
  slot-(k+1) off-grid claim at e₁ ≥ 2, and the corrected e₂ = 1 top-level
  branch (Fidelity A). All exact.
* **S4.6 (II-2/II-3) off DCX:** A₀Ĉ/A₁Ĉ generalized-monomial lines
  re-computed (β* and β* − e₀h₀); Q¹ ≠ 0 ⟹ ω ≥ e₀ ⟹ e₀ ≥ 3 re-derived;
  II-2's C₀ = c₀c₁ε₁(B₁) = z₂z₁ε₁(B₁) and II-3's C₀ = −c₀ε₁(B₁) =
  z₁^{δ₁}ε₁(B₁) both re-derived; the II-3 e₁ = 2 collision note checked
  (w₁(Q¹) ≥ B₁ + h₁ > B₁, above-line summand inside the digit); the r1 N3
  bracket (vacuous e₁ = 2 branch in II-2) stands correct.
* **DCX honesty (S0.4/S4.7/S7/S8):** the S0.4 and S4.7 DCX displays agree
  ((s₁+s₁′) + s(γ₂) ≥ 2e₀ ⟺ ω ≥ e₀); emptiness at e₀ ≤ 2 re-derived; the
  exactly-what-breaks display matches the II-2/II-3 guards (k+2 = e₁ at
  S₂ = 2e₁−2; slot 1 = e₁ at e₁ = 1); the open lemma is displayed with
  price everywhere it matters and the S8 DAG routes it only into "S5 on
  DCX". Instance evidence consistently labeled never-a-proof-step.
* **Class pin (S0.1):** per-read conditions only, no E₃ floor, coincidence
  display + the r1 coverage bracket accurate (unconditional exactly where
  DCX is empty, e₀ ≤ 2).
* **Corollaries (S6):** COR-1/COR-2 unconditional legs re-checked (the
  slotwise cocycle telescopes are symmetric as displayed); COR-3 rides the
  r1 re-scope correctly (CX/CW field-level off-DCX; integer reductions +
  CV unconditional — the e₂ = 1 reduction Σ = γ₂δ₂, D₁ = accepted exponent
  re-derived); COR-4's shift arithmetic and ρ = z₂^{−ℓ₁e₀}z₁^{−ℓ₀}
  re-derived via EXP-KIT(a); COR-5 keeps the H²-class honestly
  cited-measured; COR-6 now correctly rung-labeled (Fidelity B); COR-7
  scope exact.
* **Open-lemma displays:** (W-MULT-3-DCX) and the fenced DEV-1 corner are
  the only open items, both boxed, both with price/route displayed, neither
  consumed anywhere on the proved perimeter (grep + DAG re-checked).

**Findings: NONE.** (One non-blocking wording observation recorded at the
end of Fidelity B; explicitly not a gap: no reader-extractable error.)

## Provenance appendix (tails eyeballed)

* Note under review: `lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md` @
  a687b80 (= HEAD state; origin 8ba1820; r1 amendments f9daca0). 974 lines;
  tail = the S9 consumer list closing "— (ITER-LAW-3) proof compose unit,
  wave 19 unit 2, campaign date 2026-08-08 (wallclock 2026-08-03)."
* Diff audited: `git diff 467b523..a687b80` = 5 files; a687b80 alone = note
  (+22/−2) + ledger (+20); 5fe901e = the chartered GENERAL-n unit (4 files,
  +1713, all new/append).
* Frozen artifacts re-run (sealing commits): `iterlaw3_pe_reimpl.py` +
  output + results.json @ be9a77b — output tail eyeballed: "PAIRS 3344
  CHECKS 55186 VIOLATIONS 0 SYMBOLIC 20000/20000 MUTATIONS all fired DCX
  locus OK / VERDICT: ALL GREEN"; `iterlaw3_proof_diag.py` + output @
  8ba1820 — tail: "AGGREGATE case census: [('DCX', 16), ('I', 912),
  ('II-1', 368), ('II-2', 40), ('II-3', 88)] / TOTAL identity violations:
  0 / DIAG VERDICT: GREEN"; `iterlaw3_pe2_e1witness.py` + output +
  results.json @ 467b523 — tail: "PE2 E1-WITNESS VERDICT: GREEN".
* Round-2 reports consulted AFTER verdict formation: `ITERLAW3_passPC2_report.md`
  (cf013a4), `ITERLAW3_passPE2_report.md` (467b523) — used only to confirm
  the findings-to-cure mapping already reconstructed from the brackets.
* Concurrent leg: `ITERLAW3_passPC3_report.md` @ 5bdca01, CLEAN (0C/0G) —
  not consulted for content; verdict line seen post-freeze (disclosed).
* Ledger tail freshly re-read before this pass's append: current tail =
  the errata-round-2 block ("...it consumes [IL3] with the honest
  attempt-grade conditionality displayed.", line 7870).

— ITERLAW3-PE3, Fable, wave-20 round 3; unit files: this report + the
ledger append ONLY (scoped `git commit --only`); the note and all sealed
artifacts byte-untouched.
