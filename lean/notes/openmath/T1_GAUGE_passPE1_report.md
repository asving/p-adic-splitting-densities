# T1-GAUGE-COCYCLE passPE1 — hostile verification report
## Arc pass 1 on T1_GAUGE_COCYCLE_2026-08-10.md (RCT round-1, CODEX arm; arm-blind charge)
## Verifier: fresh-context Fable PE1 · 2026-08-10

**VERDICT: NOT CLEAN — 0 CRITICAL, 1 GAP (G-2 confirmed and sharpened), 5 MINOR.
Counter stays 0/2.**

The note's five conclusions C1–C5 each survived independent re-derivation; the
machine leg is bit-identical on isolated re-run (85 checks / 1 violation / exit 1,
the single RED being the preregistered P-J2 row); a fresh gauge-live frame at p = 7
(not in the note's plan nor in any of the seven annexes' batteries) confirmed the
corrected-key law and the read dictionary live, dual PARI routes agreeing, with a
NEW defect signature (the naive key SPLITS {(2,1),(2,1)} instead of ramifying
{(4,1)}). The one GAP is the charged G-2 surface: C3's B-law legs consume carrier
item 9 (canonical-residual multiplicativity) as DATA where the absorbed corpus
(GENTOW2-B″) derives the corresponding facts through the FGMN normal-form machinery
at i = 2 — the absorption of the B-law sites is conditional on an undischarged
consumption check. G-1 is adjudicated DISPLAY-ONLY (MINOR).

### §0. What was verified (chain of custody)

- Note at HEAD (1,384 lines): header + verbatim block + tech verdict.
- Seals resolve as git commits: brief 6cd5e119 (t1_gauge_cocycle_brief_2026-08-10.txt),
  codex run log 6e9968bd (t1_codex_run1_output.txt), instrument seal 921a8547
  (t1_gauge_checks.py), verdict b879fa0b (t1_gauge_checks_output.txt). All four
  artifacts byte-unchanged since their seal commits (git diff empty at HEAD).
- Verbatim transcription verified: note lines 65–1334 == log lines 2509–3777
  (diff clean; one trailing blank line only). The log contains the charge
  (lines 13–1234, the brief with annexes [A1]–[A7], [S1], [S2]) and the note
  streamed once (1238–2506) + echoed as the final message (2509–3777).
- Annex extraction anti-corruption check: brief [A1] slice byte-identical to
  GENHN_PROOF_2026-08-08.md L1980–2037; [A4] == GENTOW3_PROOF S7 slice; [A5] ==
  GENTOW4_PROOF S8 slice (both content-identical modulo my slice off-by-one).
  gentow4_pe1_fresh.py md5 5dc455dd7d2feb8bca79dbfb59c2d83b matches the GENTOW4
  annex's pinned md5 — the SEC-G regression genuinely ran the committed instrument.

### §1. Machine leg

- **Isolated re-run BIT-IDENTICAL.** Instrument + gentow4_pe1_fresh.py copied to
  /tmp/t1_iso, run cold: exit 1, output byte-identical to the committed
  t1_gauge_checks_output.txt including the wall line. 85 checks, 1 violation.
- **The preregistered-RED discipline is honest.** The docstring (sealed BEFORE the
  run at 921a8547) preregisters P-J2 with the note's M2 value AS WRITTEN and
  declares it expected-RED with the G-1 diagnosis; the run's only RED is exactly
  that row ([1,2,1] = y²+ωy+1 computed vs [2,2,1] = y²+ωy+ω preregistered).
  The invariance clause is scored separately (P-J2b) and is green.
- **Check-count audit:** hand count of chk() sites reproduces 85 exactly
  (SEC-A 20, SEC-B 21, SEC-C 12, SEC-D 12, SEC-E 4, SEC-F 13, SEC-G 3).
- **Tautology audit:** two rows are literal-vs-literal (F-3 below); the second
  X3 slot-poly row is constant arithmetic but expresses a real fact (naive slot
  poly degenerate at Z = −1); the remaining 82 rows compare computed objects
  against preregistered values.
- **F4-JOINT arithmetic re-derived by hand** (quadratic + μ=3 legs): W(t), ϑ, the
  three (LIFT) outputs, corrected/naive digits, both mult residuals, Θ, B-units,
  canonical coefficients (ω,ω²,1), canonical residual (y+ω)³ = w³ψ(y/w) — all
  confirmed except the P-J2 display value (G-1, see §3).

### §2. Conclusions C1–C5 re-derived (independent routes)

- **C1-general**: sound (ratio of two exact-height normalizations has value 0;
  residue defined). C1-level-2: re-derived by CRT arithmetic and confirmed on a
  fresh (e₁,h) = (5,3) sweep, u₂ ∈ [1,40] (fresh leg FV-A): i ≡ ℓ₁u₂ mod e₁,
  exponent −⌊ℓ₁u₂/e₁⌋ exact at every u₂. The general-level reduction algorithm is
  a disclosed sketch (coprimality forces divisibility at the top key; removal
  strictly drops the top level, so it terminates) — adequately fenced by Honesty
  ledger items 1–2.
- **C2**: wrap/cocycle/telescopes re-derived; the ϑ_{1,s} = η^{⌊s·i(u)/e₁⌋} law
  verified by THREE independent routes in the fresh leg (direct exponent
  reduction / τ-recursion product / closed form) at (5,3), u = 7. Corrected-lift
  → mult coefficient = c_t re-derived. The p = 7 fresh frame (FV-C) confirms the
  corrected key carries ψ₂ and the naive key does not, dual PARI routes.
- **C3**: dictionary re-derived (needs only value-zero residues — carrier-safe).
  B-law re-derived GIVEN carrier item 9; fresh leg FV-B verifies the B-law and
  the w^fψ(y/w) residual over ALL 8 homomorphism models R: monomials → F₉^×
  compatible with the carrier constraints (η-agreement), at a fresh geography
  (F₉, e₁ = 3, u = 5, f = 3, two live ϑ slots, w ranging over 8 values incl.
  w ≠ 1 of full order 8). Gauge-invariance clause: the substitution is an
  automorphism — carrier-free, sound. The item-9 consumption is the GAP (§3 G-2).
- **C4**: re-derived; support bound i(m)+e₁r ≤ D′−1 exact; x-free classification
  confirmed exhaustively at (e₁,h,f₁) = (5,3,3) (fresh; the note's own tests stop
  at f₁ = 2). NB the clearance caveat a(m)−rh ≥ 0 is honestly ledgered (item 5).
- **C5**: re-derived (two-line consequence of C2-wrap); verified at (5,3) fresh.
- **Level/frame uniformity (charged surface 2):** C2's general-level proofs use
  only the exact-height property of n̂_i (carrier item 5) — genuinely
  level-uniform. C4/C5 are explicitly level-1-scoped and every C4-mapped site is
  a level-1/level-2 lift site. C1's explicit formula is level-2-scoped and its
  only mapped site (A7 letter formula) is level 2. The single interface the
  proof does NOT carry uniformly is item 9 (= G-2). No silent geography
  assumption found beyond it.

### §3. The charged gap adjudications

- **G-1 (ψ^{(w)} slip, P-J2) — adjudicated DISPLAY-ONLY ⇒ MINOR.** The wrong
  value y²+ωy+ω appears exactly once (M2, F4-JOINT quadratic); the correct value
  y²+ωy+1 follows from the note's own C3-three-reads/DEF W-2 (re-derived:
  slot coefficients (c₁w, c₀w²) = (ω, ω³ = 1)). C3's displays and derivation are
  consistent and correct; the μ = 3 leg computes the same operation CORRECTLY
  ((y+ω)³); no tooth, no absorption row, and no other display consumes the wrong
  value. (The wrong polynomial coincides with the LD1 residual y²+ωy+ω — where
  that value is CORRECT per GENTOW2 ground truth — consistent with a copy-slip.)
  Machine-adjudicated RED under an honest preregistration. C3 does NOT consume
  the wrong object.
- **G-2 (item-9 consumption, C3 B-law) — adjudicated GAP (confirmed, sharpened).**
  Ground truth read at GENTOW2_PROOF S5.1–S5.2: B″ proves u(β_t) = ϑ(t)·w^{f₃−t}
  at i = 2 via the Φ₂-adic expansion (steps (ii)–(iv): Cor 4.7(1) additivity,
  Lemma 3.17 + Cor 4.7(2)/eq (14) killing j ≥ 1 terms, B′(3) for j = 0) — the
  multiplicativity facts C3 assumes are DERIVED there through the FGMN
  normal-form machinery, not assumed. T1's C3 consumes "R multiplicative on
  homogeneous initial forms + residue-agreement on value-zero" (carrier item 9)
  as data. The lemma is internally sound relative to its carrier, and the
  carrier-rule audit box remains TRUE (item 9 is not the B-law). But the
  ABSORPTION claim at the B-law sites is conditional on discharging item 9 by
  the FGMN instance at level-i generality — undischarged; at i = 2 the corpus's
  only route is B″'s own proof. **Blast radius (sharpened):** rows A7/2 (S5.2
  B-law), A5/2 (C3 half only — the C2 half, mult coefficient = c_t, stands),
  S1/2 (B-law orientation half). C3-dictionary, C3 gauge-invariance, and all
  C1/C2/C4/C5 rows (14 of 19) are item-9-free. Not a defect of the statement;
  a named open consumption obligation, correctly recorded but resolvable only
  by a citation pin or a level-general proof.
- **G-3 (scope honesty) — adequate as recorded.** Ledger items 1/8/9 fence the
  level-2-only explicitness and the finite-carrier status of F4-JOINT; the tech
  verdict does not overclaim (sigma values reported as formal, not PARI).

### §4. Findings (quote-and-classify; FIX NOTHING)

- **F-1 [GAP — G-2 as adjudicated above].** "The canonical residual map is
  multiplicative on homogeneous initial forms and agrees with residue evaluation
  on value-zero elements" (carrier item 9) vs the absorption rows A7/2, A5/2,
  S1/2. Failure scenario: if the FGMN instance's R at some level i ≥ 2 geography
  fails item 9 at B″'s generality (e.g. multiplicativity only on the sub-monoid
  B″ actually walks), C3-B-law/C3-FGMN-read silently overreach and the
  "absorbed" annex sites are NOT re-derived — the corpus would then hold B″ only
  by its original i = 2 proof, and T1's unification claim shrinks at those rows.
- **F-2 [MINOR — G-1 as adjudicated above].** M2 F4-JOINT quadratic: "ψ^{(w)}(y)
  = y² + ωy + ω" — false by the note's own definition (correct: y² + ωy + 1);
  machine-refuted on a preregistered row; display-only, no consumer.
- **F-3 [MINOR — two vacuous check rows].** Instrument lines 287–288: the
  "formal sigma" rows compare literals to literals ([(2,4)] == [(2,2*2)] and
  sorted([(2,2),(2,2)]) == [(2,2*1)]*2). They score green by construction and
  inflate the count to 85; the substantive content (rc irreducible / rn splits)
  is independently scored two rows above. Failure scenario: none mathematically;
  the count "85 checks" overstates the scored surface by 2.
- **F-4 [MINOR — absorption-map count discrepancy].** Tech header: "18 site rows
  over the seven annexes ... + 2 supporting-context rows". The table has 17
  annex-site rows (A1:2 A2:2 A3:2 A4:2 A5:4 A6:2 A7:3) + 2 supporting = 19 rows.
  No reading gives 18 + 2. Gate consequences: none (≥ 3 conclusions and
  GENTOW4 = 4 sites both hold); the record sentence is wrong as written.
- **F-5 [MINOR — T-4 tooth weaker than the composed plan].** The note's tooth 4
  requires "the canonical three-digit coefficient vector ceases to equal
  (ω,ω²,1)"; the instrument checks only the s = 2 B-unit (buw == 1 != W) and
  leaves `canw` as dead code (line 416). The tooth still fires on the B-unit
  signature, but the vector-level claim is unexercised. Failure scenario: an
  implementation bug affecting only the OTHER two slots' canonical coefficients
  would not be caught by T-4 as coded.
- **F-6 [MINOR — undeclared definitions-only dependence on a parallel 0/2 note].**
  The brief's [S2] block hands the composer WFRAME_NOTE_2026-08-10.md's DEF
  W-1/W-2 (w_i, ψ^{(w)}), which surface as carrier items 9–10 and C3-three-reads;
  the T1 note and tech header never name WFRAME (a parallel RCT arc at 0/2, whose
  own PE1 found a GAP in its S4 tower data — not in the [S2] definitions).
  Mitigation: every [S2] definition carries accepted-corpus span pins (GENTOW2 @
  33f86204, GENTOW5 @ b0e5c648), so the dependence is on accepted definitions
  routed through WFRAME's restatement. Still, the mutual-consumption declaration
  rule asks for the name. Failure scenario: if WFRAME's arc revises DEF W-1/W-2,
  T1's carrier drifts with no declared edge to catch it.

### §5. Absorption-map spot verification (charged surface 1 & 3)

Sites re-verified against ground truth (annex text in the repo notes, not just
the brief): A1/1–2 (GENHN erratum: corrected block = L_{(f₂−t)u₂}(c_tη^{W(t)})
= C2-level-2-key exactly; η = 1 degeneracy = C2's degeneracy clause);
A2/1–2 (HETOW: wrap cocycle + Q-additivity = C2-wrap + C5 verbatim; W(t)
telescope = C2-telescope-2); A4/2 (GENTOW3 S7.1: primary x-free clause
"i(m_t) = 0 AND c_tη^{W(t)} ∈ F_Q" = C4-x-free at d = c_tη^{W(t)}; the η = 1 ≠
f₁ = 1 distinction matches C4's addendum); A5/1–4 (GENTOW4 S8.1: S0 pin,
slot-residue-at-corrected-key = C2's mult-coefficient computation, BOX-3
ϑ = 1-blindness = C2 degeneracy clause, S4 residue-1 = η = 1 not f₁ = 1);
A6/1–2 (GENTOW6 S6.1: I_t = i_t + e₁r_max from C4's support; 6.3′ remainder
correctly NOT claimed — ledger item 6); A7/1–3 (letter formula L634 GENTOW2 =
C1-level-2; B-law orientation: T1's Θ_i(t) has the SAME fraction orientation as
GENTOW2's ϑ(t) — n̂(su)/n̂(u)^s — and ledger item 3 pins the inversion against
ϑ_{i,s}; LP/LD decode rows L780–800 match SEC-D and M2 exactly, incl. the
lattice split (1,−5,2) = 1·(−9,0,2)+5·(2,−1,0) and LD1/LD2 residuals).
**Completeness:** the normative gauge sentences swept (the erratum display, the
wrap/Q laws, the corrected-key pins, the x-free clause, the I_t repair, the
letter formula, the B-law, the LP/LD decode rows) each trace to a mapped row;
the unabsorbed remainders found (GENTOW1 budgets/floors, GENTOW4
counts/separators, GENTOW6 6.3′ (a′)–(c′) bodies, B″'s proof mechanism) are the
ledger-6 disclaimers plus the G-2 obligation. No orphan annex sentence surfaced
in this sweep beyond those disclosed remainders.

### §6. Fresh route (frames not in the note's plan nor the annex batteries)

Script: `verification/openmath/t1_gauge_pe1_fresh.py` (fresh-composed this
pass, md5 7ba79d7544946dcf1cfa6cc5b5f461f5; output
`t1_gauge_pe1_fresh_output.txt` md5 5e2c1be8b2f117b69da0701709d285a5). Three
legs, exact arithmetic, dual oracles on the p-adic leg:

- **FV-A (exponent core, (e₁,h) = (5,3), f₁ = 3, u = 7; u₂-sweep 1..40):**
  wrap/product/Q at a,b ∈ [0,60]; ϑ-law by three routes; C1-level-2 exponent
  identity at every u₂ ≤ 40; C4 support/x-free at f₁ = 3 exhaustive.
- **FV-B (F₉ carrier, e₁ = 3, h = 1, u = 5, f = 3, η = g, TWO live ϑ slots):**
  C3 dictionary + B-law + canonical residual = w³ψ(y/w) verified over ALL 8
  monomial-homomorphisms R compatible with the carrier (w takes 8 values incl.
  order-8 units); gauge-invariance by exhaustive factorization, F₉ arithmetic
  hand-rolled + PARI cross-check.
- **FV-C (p = 7 gauge-live tower, dual PARI oracles):** Φ′ = x²−21, η = 3
  (ord 6), u₂ = 3, W(0) = 1 live, ψ₂ = Z²+Z+3 irreducible. Corrected key
  (x²−21)² − 42x(x²−21) − 1715: predicted σ = {(2,2)}, v_P(Φ′) = 3. Naive key
  (x²−21)² − 42x(x²−21) − 1372: naive mult residual Z²+Z+1 has DISTINCT roots
  {2,4} mod 7 ⇒ predicted σ = {(2,1),(2,1)} — a defect signature genre no annex
  battery exhibits (their naive keys ramify to {(4,1)}).

RESULT (run after seal of this section): see §6R below.

### §6R. Fresh-route results

**GREEN — 26 checks, 0 violations, exit 0** (single run, gp + python3, exact).

- FV-A: A1–A5 green. Wrap/product/Q hold at (5,3) for a,b ∈ [0,60]; the three
  ϑ routes agree for s ≤ 30 at u = 7; the C1-level-2 exponent identity holds at
  each u₂ in [1,40]; the C4 support/height/x-free classification holds
  exhaustively at f₁ = 3 over the in-clearance digit supports, m ≤ 60.
- FV-B: B1–B8 green, 8 R-models as predicted (cube map bijective on F₉^×, one
  model per R(π) choice; w took 8 distinct values). In each model: B-law
  R(n̂(su)) = Θ(t)w^s, slot reads = c_t·w^s, canonical residual coefficientwise
  = w³ψ(y/w). ψ (letter-live coefficients g, 2+t, 1+2t) is IRREDUCIBLE over F₉
  and its factor-degree multiset [3] is invariant across the 8 w-twists — own
  exhaustive factorization, PARI factor-over-F₉ agreeing.
- FV-C: C1–C6 green, dual routes bit-agreeing and factorpadic stable at
  N = 20/30/40. Corrected key σ = {(2,2)}, nfeltval rows [[2,2,3]]
  (v_P(Φ′) = u₂ = 3 — the C1/C2 height pin at a fresh prime). Naive key
  σ = {(2,1),(2,1)} — EXACTLY the preregistered new-genre signature derived
  from C3-dictionary (naive mult residual Z²+Z+1 splits with distinct roots
  {2,4} mod 7, so the naive key SPLITS instead of ramifying — a defect mode no
  annex battery exhibits). The gauge tooth fired (C6: corrected ≠ naive sigma).

Conclusions exercised live at fresh frames: C1 (level-2 sweep + height pin),
C2 (three-route ϑ + corrected key at p = 7), C3 (dictionary + B-law over the
8-model family + the naive-split prediction), C4 (f₁ = 3), C5 ((5,3) core) —
the ≥ 2-conclusions-live bar exceeded.

### §7. As-of states read + grade line

As-of: T1 note read at HEAD (this pass's parent cf28bcef); GENTOW5-W(i) read as
PROVED at attempt grade 1/2 (ec30256c, PE1 CLEAN 884edd2c) — consumed by T1 only
as brief supporting-context [S1] with accepted-corpus pins; WFRAME read at 0/2
(note + passPE1 report with its F-1 GAP, which sits in WFRAME §S4 tower data,
NOT in the [S2] definitions T1's brief consumed); T1 itself declares no
consumption of either parallel arc (F-6 records the undeclared [S2] edge).

**Pass 1 verdict: NOT CLEAN — 0 CRITICAL, 1 GAP (F-1 = G-2 confirmed), 5 MINOR
(F-2..F-6). Counter stays attempt 0/2.** The GAP is an interface/consumption
obligation, not a refuted claim: C1–C5 survived independent re-derivation and
two machine legs (sealed 85/1-as-preregistered; fresh 26/0). Repair path for
the arc: pin a level-general FGMN citation (or a level-general proof) for
carrier item 9, or annotate rows A7/2, A5/2, S1/2 as conditional; plus the four
mechanical MINORs.
