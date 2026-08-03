# ITERLAW3 hostile pass PE2 — Fable round-2 leg on the AMENDED note (post-errata f9daca0): errata fidelity + execution re-runs + new E1-witness mini-check + fresh content read

**Pass:** ITERLAW3-PE2 (Fable; round 2 of the acceptance arc). **Target:**
`lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md` at f9daca0 (errata round 1
applied). **Standing of the target (displayed per discipline):** the rung-2
proof note is at ATTEMPT GRADE, acceptance counter 0/2, round 2 in flight;
acceptance requires this pass AND the concurrent Codex PC2 both CLEAN.
**Discipline:** fresh verifier, own view; quote-and-classify; nothing fixed;
findings frozen before consulting any concurrent-pass artifact (disclosure
caveat in the Decorrelation section — the PC2 one-line commit HEADLINE
became visible mid-pass; the PC2 report file was NOT opened).
**Wallclock:** 2026-08-03 (campaign 2026-08-08).

## VERDICT BLOCK

**FINDINGS: 0 critical, 2 gaps (+2 nits) — both gaps NEW (pre-existing text
both round-1 passes missed / a naming residual of the round-1 cure), both
narrow, NEITHER introduced by the errata.**
**VERDICT: NOT-CLEAN.**

* **Errata fidelity: VERIFIED.** The f9daca0 diff is bracket-additive on the
  nose: all 7 removed lines are pure reflows with their text preserved
  verbatim inside additions (2 relocate only a trailing period past the
  inserted bracket); the PROVED core S2–S5 is substantively byte-stable (its
  only changes are three added brackets — the PE-N1 artifact gloss, the S4.1
  erratum block after the DEV-1 ∎, the PE-N3 gloss — no math line altered);
  no residual unbracketed unconditional-degeneration claim (grep: the only
  "all unconditional" left is the byte-frozen S6.3 header immediately struck
  by its erratum bracket); the DEV-1 induction quantifiers are now honest
  (corrected scope of record: step at e₀ ≥ 2, base range only at e₀ = 1,
  fenced non-consumed corner {e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀} displayed as OPEN).
* **All three round-1 errata VERIFIED CURED** (each independently re-derived,
  not just matched against the round-1 reports — details below): E1 (S6.3
  off-DCX requalification + S0.1/S0.4/S9 sweep brackets), E2 (S4.1 induction
  scope + fenced corner box), E3 (rung relabel at S6.6/S1/S0.4/S7 — with one
  residual token, Finding 2). Out-of-fence sweep claims independently
  re-verified by grep (no external unconditional S6.3/COR-3 consumer).
* **Execution: ALL GREEN, byte-exact.** `iterlaw3_pe_reimpl.py` re-run
  reproduces 3,344 pairs / 55,186 checks / 0 violations, VERDICT ALL GREEN,
  stdout AND results-JSON byte-identical to the frozen pass-1 artifacts;
  `iterlaw3_proof_diag.py` re-run byte-exact (1,424 pairs, census
  I 912 / II-1 368 / II-2 40 / II-3 88 / DCX 16, 0 violations).
* **NEW mini-check (this pass, post-seal-labeled): GREEN, first run.**
  `iterlaw3_pe2_e1witness.py` — both S6.3-erratum witnesses verified exactly
  as stated (4 DCX pairs on the e₂ = 1 ℤ₅ tower / 48 on the e₁ = 1 TW2, at
  the analytically predicted split-classes), theorem display + all W-MULT
  clauses + Q¹ ≠ 0 + naive-E₀ re-overflow hold on every one of the 52 DCX
  pairs (instance data for the open (W-MULT-3-DCX), NOT proof coverage), and
  the erratum's "genuinely unconditional NOW" integer-level reductions hold
  on all 400 pairs of both blocks.

Acceptance consequence: this pass is NOT-CLEAN, so round 2 does not close
the 2-clean bar; the counter stays 0/2 and the note stays at attempt grade;
(ITER-LAW-3) remains formally conjecture-grade at the campaign level
(sealed MEASURED law + proof attempt). Both findings are erratum-priced
(bracket-grade), not structural.

### FINDING 1 [GAP — a false displayed equality inside S4.5's e₂ = 1 grid
### check; the true conclusion is independently derived IN THE SAME SENTENCE
### and machine-true; no downstream effect]

S4.5, top level, the e₂ = 1 branch (note line 592–594; PRE-EXISTING text —
present verbatim at composition 8ba1820, untouched by f9daca0, missed by
both round-1 passes):

> off-grid when e₂ ≥ 2, and on-grid-but-strictly-above-the-line when e₂ = 1
> (slot weight Γ″ − (S₃+1)γ₃ = B₂ − γ₃ < B₂ − e₁γ₂ + h₂ = w₂(E₁) + 0 — i.e.
> w₂(E₁) = B₂ − γ₃ + h₂ > slot weight): read 0 either way.

The middle link **"B₂ − e₁γ₂ + h₂ = w₂(E₁) + 0" is FALSE as written**: S4.5
itself displays w₂(E₁) = B₂ − e₁γ₂ (line 587), so B₂ − e₁γ₂ + h₂ =
w₂(E₁) + h₂ with h₂ ≥ 1 ≠ 0; and the preceding inequality B₂ − γ₃ <
B₂ − e₁γ₂ + h₂, while true, compares the slot weight against w₂(E₁) + h₂ —
too weak to give the needed "digit strictly above the line". The SENTENCE'S
FINAL CLAUSE is a correct and self-contained derivation of the needed fact:
at e₂ = 1, g₁ = 1: γ₃ = e₂w₂Φ₂ + h₂ = e₁γ₂ + h₂, hence w₂(E₁) = B₂ − e₁γ₂ =
B₂ − γ₃ + h₂ > B₂ − γ₃ = slot weight (h₂ ≥ 1) — digit above the line, read
0. So the conclusion stands on an in-sentence valid leg; the malformed
middle link should be struck/corrected by an errata bracket. Classification
GAP (not critical): the logical chain does not break — the valid derivation
is adjacent and the behavior is machine-true on every e₂ = 1 pair probed
(TW5 battery: II-1 12 / II-2 4 / II-3 8 per ring, 0 violations; the PE2
mini-check's e₂ = 1 witness tower: 144 pairs, 0 violations, incl. its 4 DCX
pairs as labeled instance data). Ripple: S4.6 II-2 consumes this branch by
reference ("Top level verbatim as in S4.5") — same one-bracket cure covers
it. Suggested fix: bracket-strike "< B₂ − e₁γ₂ + h₂ = w₂(E₁) + 0" and let
the "i.e." clause be the derivation of record.

### FINDING 2 [GAP — one residual rung-convention token that the E3 bracket
### blesses rather than cures: the cross-note citation index]

S6.6 display sentence (note line 834–835):

> the proved display is EXACTLY the uniform recursion of L3CONVERGENCE S2
> Candidate 2 at n = 3

The SOURCE pins its index rung-wise: L3CONVERGENCE S2 Candidate 2 opens
"For an (n+1)-read standard-lift tower ..." and lists "Confirmed instances:
n = 1 (the ACCEPTED order-2 theorem ...), n = 2 (this hunt, Candidate 1)".
Under the source's own convention, "Candidate 2 at n = 3" DENOTES the 4-read
recursion (with a D₃-layer) — not what the note proves. The E3 erratum
bracket declares this token counts READS, which prevents mathematical
confusion (and the equations displayed under it ARE the correct rung-n = 2
instantiation: S_2 = δγ₃, D_2, S_1, D_1 match Candidate 2 at n = 2 symbol
for symbol), but a cross-note citation should carry the SOURCE's index: the
sentence of record ought to read "Candidate 2 at (rung) n = 2". Naming-only,
zero math content — but it is exactly the residue class the E3 cure was for,
so it should not survive into an accepted note. (The S6.6 title's "at n = 3"
and the S0.4/S1/S7 tokens are note-internal names, adequately covered by
their brackets; this is the one token whose referent lives in ANOTHER note's
convention.)

### Nits (no logic touched)

* **N-a (S6.3 erratum + S9 bracket wording):** "realizes 4 DCX pairs per
  W₁×W₁-equivalent block" — "block" here means the two-window battery block
  (4 E₃×E₃-equivalent sub-blocks); per single E₃×E₃ sub-block the counts are
  1 (CX witness) and 12 (TW2). The numbers are pinned by the cited PE-report
  census and reproduce exactly (mini-check displays both granularities);
  the phrase alone could be misread as per-sub-block.
* **N-b (S6.3/S0.1 brackets):** "unconditional exactly where DCX is empty,
  i.e. e₀ ≤ 2" — the "i.e." is the class-level quantification (DCX is empty
  for ALL towers iff e₀ ≤ 2, matching S0.4's "EMPTY unless e₀ ≥ 3"); on an
  individual e₀ ≥ 3 tower DCX can also be empty (needs s(γ₂) ≥ 2 among
  other things), where the clauses are likewise unconditional. Observation
  only; the surrounding sentence already states the precise off-DCX scope.

## ERRATA FIDELITY LEG (charge 1) — verified item by item

**Diff perimeter:** `git diff be9a77b..f9daca0` touches exactly the proof
note (+96/−7) and the ledger append (+48). The 7 removed note lines,
each checked against its replacement: (1) S0.1 "…extrapolated instance
claims." → text verbatim + bracket, period after bracket; (2) S0.4 DEV-1
status row → row verbatim + in-cell bracket; (3) S0.4 COR row → row
verbatim + two in-cell brackets; (4) S1 "(ITER-LAW-n) recursion at n = 3
are then DERIVED…" → verbatim, bracket spliced, reflow; (5) S2 WINDOW
case-(i) "…= S₂ wait — at δ₃ = 0…" → artifact text PRESERVED, struck by
bracket (PE-N1), reflow; (6) S7 "…n = 4 probe unit." → verbatim + bracket,
period after bracket; (7) S9 "wording stands." → verbatim + trailing
bracket. NOTHING deleted; all sealed artifacts and the diag byte-untouched
(re-verified by re-run below).

**E1 cure (S6.3, convergent PC-F2 = PE-F1, CRITICAL):** the header clause is
struck in-bracket; the corrected claim of record (CX/CW field-level OFF-DCX;
unconditional-for-all-towers exactly at e₀ ≤ 2; in full once (W-MULT-3-DCX)
closes; integer-level reductions + CV bullet unconditional NOW) is exactly
what the finding required, and I re-derived each leg: the DCX predicate
(S0.4/S4.7) carries no e₂-condition; at e₁ = 1 the track s₂ = s₂′ = e₁−1 = 0
is automatic (locus ENLARGED — S4.7's own "slot 1 = e₁ (Case II-3 at
e₁ = 1)" display); CV: DCX needs δ₁ = 1 ∧ S₁ + s(γ₂) ≥ 2e₀ with
s(γ₂) ≤ e₀−1, forcing S₁ ≥ e₀+1 ≥ 2 while S₁|_{e₀=1} = 0; the CX/CW/CV
integer reductions re-checked machine-side on all 400 mini-check pairs (0
bad). The consumer-at-risk S9 cite now reads "proved OFF-DCX" with the
witness displayed. Out-of-fence sweep INDEPENDENTLY re-verified: repo grep
for `ITERLAW3_PROOF` finds no consumer citing its S6.3; ITERLAW4_PROBE's
F0b leg cites the sealed MEASURED (ITER-LAW-3) (its line 269 display);
L3CONVERGENCE's "S6.3" hit is the M2 method note's section; ITERLAWLIFT_
CORNER's "COR-3" (its line 132) is the ACCEPTED order-2 note's e₀ = 1
degeneration — that accepted base being, per the ledger package of record
pasted at every cite: accepted on the harness tower class, standard-lift,
strict superset of DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting,
on-the-nose restricted to E₂ > 1, with all three residuals: (ITER-LAW-LIFT)
open exactly at g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper rides the
accepted GRB retarget consumer-side; orders ≥ 3 untouched. CURED.

**E2 cure (S4.1, convergent PC-F1 = PE-F2, GAP):** the struck display and
the corrected scope match the finding; I re-derived every clause: at e₀ = 1
the junkΦ⁽ⁱ⁾ child at i = g₀−1 has Φ₀-exponent e₀i + j − e₀g₀ + 1 = j (no
descent; its line rises by h₀ per round); at e₀ ≥ 2, j − e₀ + 1 ≤ j − 1
closes the measure; S4.5's e₀ = 1 inputs have J = S₁ + s(γ₂) = 0 (all
eq-(12-int) s-values vanish at e = 1), exponent m ≤ g₀−1 < e₀g₀ = base
range; S4.6's inner Case II needs δ₁ = 1, impossible at e₀ = 1 (S₁ = 0);
at d₀ = 1 DIGIT-SPLIT's Y-cofactor vanishes (deg αβ ≤ 2d₀−2 = 0 < d₀), so
the non-descending child is absent — the fenced corner
{e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀} is exactly the unproved set, displayed as OPEN
with the repair route explicitly NOT claimed. No other DEV-1 consumer
exists in the note (S4.5 G_m, S4.6 A₀Ĉ/A₁Ĉ, and the OPEN S4.7 discussion
only). CURED.

**E3 cure (S6.6/S1/S0.4/S7, PC-F3 = PE-N2, nominal):** brackets present at
all four charged sites; the convention verified at both sources
(L3CONVERGENCE Candidate 2 "an (n+1)-read tower"; ITERLAW4_PROBE's dated
head bracket "4-READ probe = RUNG n = 3"); the rung ledger in the bracket
(n = 1 PROVED + ACCEPTED [the accepted order-2 base — package of record:
accepted on the harness tower class, standard-lift, strict superset of
DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting, on-the-nose restricted to
E₂ > 1, with all three residuals: (ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper rides the accepted GRB
retarget consumer-side; orders ≥ 3 untouched]; n = 2 PROVED-OFF-DCX at
attempt grade + MEASURED, this note, counter 0/2 round 2 in flight; n = 3
MEASURED GREEN, 13b026b) is honest; the line-843 confirmed-rungs sentence
is rung-correct as the bracket says. Full-note grep for rung/n-tokens:
every "n = 3"/"n = 4" occurrence is either bracket-covered at its site, a
unit NAME (ITERLAW4 prereg), or genuinely rung-correct — EXCEPT the one
cross-note citation token of Finding 2. CURED up to that residual.

**N1/N3 cures:** artifact preserved-and-struck with the sentence of record
displayed (N1); the e₁ = 2 vacuity bracket's own claim re-derived (Q¹ ≠ 0
in II-2 outside DCX needs k+2 ≤ e₁−1 with k ≥ 0 ⟹ e₁ ≥ 3; at e₁ = 2,
k = 0 and S₂ = 2 forces s₂ = s₂′ = 1 = e₁−1, and Q¹ ≠ 0 ⟺ ω ≥ e₀ lands the
pair in DCX) (N3). CURED.

## EXECUTION ACTUALS (charge 2)

### A. Re-runs (byte-exactness legs)

* `iterlaw3_pe_reimpl.py` (run from a /tmp copy so the frozen results-JSON
  could not be overwritten; script is self-contained, seed 20260803,
  deterministic): exit 0, **PAIRS 3344 / CHECKS 55186 / VIOLATIONS 0 /
  SYMBOLIC 20000/20000 / MUTATIONS all fired / DCX locus OK / VERDICT: ALL
  GREEN** — stdout byte-identical to the frozen
  `iterlaw3_pe_reimpl_output.txt` AND the emitted results JSON
  byte-identical to the frozen `iterlaw3_pe_reimpl_results.json` (both
  `diff` empty). Runtime 1.85 s.
* `iterlaw3_proof_diag.py`: exit 0, byte-identical to the frozen
  `iterlaw3_proof_diag_output.txt` (diff empty) — aggregate census
  I 912 / II-1 368 / II-2 40 / II-3 88 / DCX 16 over 1,424 pairs, 0
  identity violations, DIAG VERDICT GREEN. Runtime 1.73 s.

### B. NEW mini-check (this pass; post-seal-labeled, own file)

`verification/openmath/iterlaw3_pe2_e1witness.py` (+ `_output.txt`,
`_results.json`) — deterministic (fixed window shift M = 5, no RNG),
imports the reimpl as harness (its byte-exact reproduction re-established
in leg A immediately before this file was written). Analytic expectations
derived from the S0.4/S4.7 DCX predicate BEFORE running and asserted:

* **CX witness** (3,2,1)(2,1,1)(1,1,1)/ℤ₅, e₂ = 1, E₃ = 6: s(γ₂) = 2 as
  predicted (γ₂ = 13, ℓ₀ = 2); DCX classes forced to
  ((s₁,s₂,s₃),(s₁′,s₂′,s₃′)) = ((2,1,0),(2,1,0)) — measured split-classes
  exactly that; **DCX = 4 per 144-pair battery block (1 per E₃×E₃
  sub-block, all four sub-blocks)** — the erratum's "4 DCX pairs" exact.
  On the 4 DCX pairs: theorem display 4/4, W-MULT ε-form 4/4, product form
  4/4, single-read shape 4/4, Q¹ ≠ 0 4/4, naive-E₀ re-overflow 4/4 — and
  **c₃ = embed(c₂) = the accepted-law display 4/4** [the accepted order-2
  base consumed here as the comparison target — package of record:
  accepted on the harness tower class, standard-lift, strict superset of
  DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting, on-the-nose restricted
  to E₂ > 1, with all three residuals: (ITER-LAW-LIFT) open exactly at
  g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper rides the accepted GRB
  retarget consumer-side; orders ≥ 3 untouched] — all of it INSTANCE DATA
  for the open (W-MULT-3-DCX) at the degeneration corner, exactly the
  conditionality the erratum now displays, NOT proof coverage. Integer-level
  CX reductions (δ₃ = 0, β₂(γ) = γ, D₂ = δ₂, Σ = γ₂δ₂, D₁ = accepted
  exponent): 0 bad on all 144 pairs.
* **CW witness** TW2 = (4,1,1)(1,3,1)(2,1,1)/F₃[[t]], e₁ = 1, E₃ = 8,
  spec verbatim from the PE battery roster: s(γ₂) = 3 as predicted
  (γ₂ = 7, ℓ₀ = 1); DCX classes = {S₁ ≥ 5} × {s₂ = s₂′ = 0 automatic} ×
  {s₃, s₃′ free} = 12 per sub-block — measured exactly (all 12 class-pairs
  realized); **DCX = 48 per 256-pair battery block (12 per sub-block ×
  4)** — the erratum's "48" exact. On the 48 DCX pairs: theorem display
  48/48, W-MULT ε-form 48/48, product form 48/48, shape 48/48, Q¹ ≠ 0
  48/48, naive-E₀ re-overflow 48/48. Integer-level CW reductions (D₂ = 0,
  Σ = δ₃γ₃): 0 bad on all 256 pairs.

**PE2 E1-WITNESS VERDICT: GREEN — first run, exit 0, runtime 0.06 s.**

## FRESH CONTENT READ (charge 3) — what was verified sound

Full read of all 956 lines of the amended note, own view. Beyond the
round-1-verified surface (which I spot-re-derived rather than re-trusted),
hand-checked this pass: the S2 integer layer end to end (L2-(3a)/(3b),
D₂-INT/D₁-INT via s ≡ ℓβ (mod e), WINDOW cases (i)–(iii) incl. the
case-(iii) recombination e₁Σ = δ₃γ₃ + (S₂−s₂″)γ₂ and the γ₃ ≥ e₁γ₂ + h₂
bound); EXP-KIT (a)/(b)/(c) with the δ-cancellation in (c); WELL-DEF's
u(gp) > (g₀−1)h₀ display; DEV-1's base case and the e₀ ≥ 2 step incl. the
ψ₀(z₁) = 0 telescope and the final-abscissa ≥ s* argument; L6-(3)'s degree
bound and dictionary consumption; CASE-SPLIT's exhaustiveness (inner
dichotomy S₁ < e₀g₀ automatic at g₀ ≥ 2; top trichotomy = the deg-A
criterion); S4.5's ε′-cancellation C₀ = z₂^{δ₂}z₁^{δ₁}ε₁(B₁) via EPS-MULT;
S4.6's ω-bookkeeping (ω ≤ 2e₀−3, Q¹ ≠ 0 ⟹ e₀ ≥ 3) and the II-3 e₁ = 2
collision argument; S5's two-kernel division; S6.1–S6.7 derivations incl.
the COR-2 slotwise telescopes and the COR-4 monodromy ρ = z₂^{−ℓ₁e₀}z₁^{−ℓ₀};
the S7 fences; the S8 DAG (matches the actual consumption structure). The
ONLY defects found are Findings 1–2 and nits above. The honest-conditionality
surface is correct everywhere I probed: DCX openness displayed at S0.4/S4.7/
S5/S6-preamble/S7/S9; attempt-grade standing displayed in the header; the
consumed accepted order-2 base is cited with the ledger block pasted in the
note's own header (verified verbatim against
`BRIDGE_ADJUDICATIONS_2026-07-30.md` "ITER-LAW ACCEPTED — 2026-08-03") —
that base being: accepted on the harness tower class, standard-lift, strict
superset of DITER_RESTATE §S2's pinned E₂ = e₀e₁ > 1 setting, on-the-nose
restricted to E₂ > 1, with all three residuals: (ITER-LAW-LIFT) open exactly
at g₀ = 1 ∧ δ₁ = 1; the gr(w₂) semantics wrapper rides the accepted GRB
retarget consumer-side; orders ≥ 3 untouched.

## DECORRELATION DISCLOSURE

The concurrent Codex PC2 landed mid-pass (cf013a4). Its REPORT was not
opened before (or during) the freezing of my findings; however its one-line
commit HEADLINE ("S4.5 e2=1 display-line slip … + two residual rung tokens
inside the S6.6 dictionary") became visible in a routine `git log` while I
was checking the errata commit's file scope — BEFORE my Finding-1
derivation. Honest status: Finding 1's mathematical content (the false
"= w₂(E₁) + 0" link, the valid in-sentence cure, the pre-existence at
8ba1820) is my own derivation, but the ATTENTION to that line was
headline-prompted, so Finding 1 is only PARTIALLY decorrelated from PC2;
Finding 2 I had independently flagged during the rung-source check (the
L3CONVERGENCE Candidate-2 read) before any PC2 signal, but headline-level
convergence ("residual rung tokens") is likewise on record. The
errata-fidelity leg, both re-runs, the mini-check, and the S2–S6 hand
verification predate any PC2 exposure entirely.

## PROVENANCE APPENDIX (verbatim slices; artifact tails eyeballed)

* Finding 1 slice (note lines 592–594, and identically at
  8ba1820:lines 555–557): "off-grid when e₂ ≥ 2, and
  on-grid-but-strictly-above-the-line when e₂ = 1 (slot weight
  Γ″ − (S₃+1)γ₃ = B₂ − γ₃ < B₂ − e₁γ₂ + h₂ = w₂(E₁) + 0 — i.e. w₂(E₁) =
  B₂ − γ₃ + h₂ > slot weight): read 0 either way."
* w₂(E₁) display it contradicts (note line 587): "**The top level.**
  w₂(E₁) = e₁B₁ + kγ₂ = B₂ − e₁γ₂ (single digit a at slot k, w₁(a) = B₁)."
* Finding 2 slices — note lines 834–835: "the proved display is EXACTLY the
  uniform recursion of L3CONVERGENCE S2 Candidate 2 at n = 3"; source
  (L3CONVERGENCE_2026-08-08.md, Candidate 2 head): "For an (n+1)-read
  standard-lift tower with canonical ε-corrected lifts …" and "Confirmed
  instances: n = 1 (the ACCEPTED order-2 theorem, ITERLAW S5), n = 2 (this
  hunt, Candidate 1)."
* E3 alignment source (ITERLAW4_PROBE_2026-08-08.md head, lines 3–9): "[DATED
  BRACKET 2026-08-03 … RUNG …] … an (n+1)-read tower = rung n), this 4-READ
  probe confirms the (ITER-LAW-n) recursion at **RUNG n = 3**."
* S6.3 erratum witness clause (note lines 762–765): "Executed witnesses (PE
  pass): the e₂ = 1 tower (3,2,1)(2,1,1)(1,1,1)/ℤ₅ realizes 4 DCX pairs per
  W₁×W₁-equivalent block; the e₁ = 1 battery tower TW2 =
  (4,1,1)(1,3,1)(2,1,1)/F₃[[t]] realizes 48."
* Sweep-claim targets verified by grep: ITERLAW4_PROBE line 269 ("F0b
  LEVEL-3 FIDELITY: the measured (ITER-LAW-3) reproduced on the level-3
  …"); ITERLAWLIFT_CORNER line 132 ("… no Case II exists there — COR-3's
  degeneration, already theorem-backed"; its S5 context is the ACCEPTED
  order-2 note's scope).
* Re-run tails eyeballed AND diffed: `iterlaw3_pe_reimpl_output.txt` final
  lines "PAIRS 3344  CHECKS 55186  VIOLATIONS 0  SYMBOLIC 20000/20000
  MUTATIONS all fired  DCX locus OK / VERDICT: ALL GREEN" — reproduced
  byte-exact; `iterlaw3_proof_diag_output.txt` final lines "AGGREGATE case
  census: [('DCX', 16), ('I', 912), ('II-1', 368), ('II-2', 40),
  ('II-3', 88)] / TOTAL identity violations: 0 / DIAG VERDICT: GREEN" —
  reproduced byte-exact.
* Mini-check tail (`iterlaw3_pe2_e1witness_output.txt`): "PE2 E1-WITNESS
  VERDICT: GREEN" with the per-tower lines quoted in Execution B above.
* Removed-lines audit basis: `git diff be9a77b..f9daca0 -- <note>` — 7
  '−' lines, all listed in the Errata-fidelity leg with their preserved
  replacements.

**Pass files (this unit's whole write set):** `iterlaw3_pe2_e1witness.py`,
`iterlaw3_pe2_e1witness_output.txt`, `iterlaw3_pe2_e1witness_results.json`,
this report, the ledger append. The note, the diag, both frozen reimpl
artifacts, all sealed batteries, and every iterlaw4* file byte-untouched by
this pass.

— ITERLAW3-PE2, Fable verifier leg, round 2, wallclock 2026-08-03.
