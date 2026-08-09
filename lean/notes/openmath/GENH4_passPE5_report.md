# GENH4 passPE5 report — hostile verification of GENH4_PROOF_2026-08-08.md (THE ACCEPTANCE ATTEMPT)

**VERDICT: CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR (+1 remark).
GENH4 is ACCEPTED 2/2** (PE4 CLEAN e15308d = 1/2; this pass = 2/2, the
second consecutive clean under the program's bar — the HE7-PE3
precedent: MINORs do not block a clean, GAP-or-worse does). **The note
text FREEZES at r3 (4b0d946 = HEAD, diff 0 lines); dated appends
only.** A dated annex is owed for the two MINOR display items below
(the HE7 F-1-annex precedent); neither touches a statement, a frozen
number, or a conclusion. Both MINORs sit on surfaces prior passes
walked without owning end-to-end (PE1 re-derived S7's σ-cases, PE2
re-derived the SPLTAIL/UND boundary CONTENT and ruled it right; the
DISPLAY residue below survived both).

**Verifier:** fresh-context hostile pass PE5 (quote-and-classify; fixes
nothing; the acceptance attempt — counter at 1/2 after PE4 CLEAN).
**Target:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` at HEAD
(note body = r3, 4b0d946). **Arc:** seal 121d9ab → RED 3eb1667 → GREEN
4b5c085 → PE1 263a36f → r1 dff23f8 → PE2 2618e9b → r2 fd35416/5279a11 →
PE3 a011533/3b88321 → r3 4b0d946 → PE4 CLEAN e15308d (1/2) → **PE5 =
this**. **Charges:** (1) the E-side (GENH4-CAP(E) + the odd/even slot
ladder) — never owned end-to-end by any pass; (2) the S9.3 level-0
assembly re-walked on TWO branches PE4 did not do; (3) the
[GENIND-H(4)] discharge supply argument itself (does GENH4.C produce
the labelling W-12.D consumes, both characteristics); (4) the
conditionality display at verdict-time git state; (5) free hunt over
the full [r1]+[r2]+[r3] tag set. Machine leg (11 md5 pins verified;
isolated re-run launched; supp leg re-run GREEN 3.0 s) and a fresh
route disjoint from all six prior routes (q = 9 = 3², the first
odd-non-prime-q cells ever, E-side raw walkers) below.

## Machine-leg status at skeleton commit

* **Pins 11/11 verified at worktree = HEAD:** runner `ee8024b7…`,
  output `9e6ca9b3…`, results `cbcff562…`, supp `7d0445c5…`/
  `8ce5faa8…`/`c966d311…`, qscout22 `cb885663…`/`6c2441a1…`, w10
  `a9c34244…`, w12 `7dc040d9…`, engine `7240a916…`. Runner
  byte-identical at 4b5c085 = fd35416 = 5279a11 = 4b0d946 = e15308d =
  HEAD; seal 121d9ab = `e5e435c3…` (the one disclosed repaired line).
* **Isolated full re-run** launched detached in /tmp/pe5/run (fresh
  copy; committed artifacts never written). **Supp leg re-run: GREEN,
  3.0 s, 0 violations** (leaf-diff pending below).

## Charge 1 (E-side, first result): OWN evaluator GREEN at ALL TEN committed consE rows

Own genre-E law evaluator written from S2.3 slot strings + S6.1
closed forms + my own re-derivation of GENH4-CAP(E) (no runner code;
`/tmp/pe5/e_side_checker.py`): full history recursion, band pricing
q^{(h−1)/2}, SPLTAIL/UND split at w < N vs w ≥ N as CAP(E) forces.
**Every consE row in BOTH artifact JSONs reproduces key-for-key: 10
rows, 301 keys, 0 mismatches, mass = (q−1)q^{4N−5h−3} exact on all** —
including the 114-key (Zp,2,7,h1) cell (deep histories to t = 2), the
deep-band cells (Zp,2,7,h3) and (Zp,2,11,h5) (h > 1: the ragged band
live, (h−1)/2 odd slots per string), and the equal-char fresh rows.
Teeth on MY OWN evaluator both fired: T1 (RAM allowed at odd band
values u ≥ 2N, i.e. CAP(E) violated) → mismatches; T2 (SPLTAIL
boundary at w < 2N instead of w < N, i.e. the undercut floor ignored)
→ 62 mismatches. Details + the CAP(E) re-derivation in the final
section below.

## FINDINGS (quote-and-classify; nothing fixed)

* **MINOR 1 (the genre-F SPLTAIL cap is displayed nowhere; the natural
  reading of two displays gives the wrong cap; S7's SPLTAIL σ-proof
  inequality is displayed for E only).** GENH4-3 (S4): "plus the
  conservative exits (A₀ hidden: SPLTAIL if **w < N-cap** else UND;
  …)" — "N-cap" is defined nowhere; the only reading that is correct
  for genre E (w < N, dv-units — matching the runner's `law_E`
  `if dv1 < N` and S6.1's explicit "SPLTAIL(w), w < N") transfers to
  genre F as w < N in v₁-units, which is FALSE: the true and
  implemented cap is **2w < N** (`law_F`: `if 2*dv1 < N`; the reader:
  `if dv1 is not None and 2*dv1 < N`). S6.1's gloss "genre F
  identically with comp-weighted exponents AND comp-weighted pin
  censuses" inherits the same false cap for the SPLTAIL row. And S7's
  SPLTAIL bullet proves the σ-decision inequality for E only ("EVERY
  lift has u_lift ≥ 2N > 2w **(E**; GENH4-CAP's undercut floor)") —
  the F instance, u_lift ≥ N > 2w (CAP(F)'s stability floor N + the
  2w < N cap), is the undisplayed one-line step on which the
  F-SPLTAIL σ-label {(1,2),(1,2)} rests — a committed key class
  (SPLTAIL(3) = 384/1,536/384 at rows 15/16/19) consumed by W-12.D's
  σ-labelling clause at n = 4. **Failure scenario (fresh
  implementer):** reading "SPLTAIL(w), w < N … genre F identically"
  predicts, at the committed (Zp,2,8,k1) row, SPLTAIL(4) = 384,
  SPLTAIL(5) = 96, SPLTAIL(6) = 24, SPLTAIL(7) = 6 and UND = 514 —
  against the committed SPLTAIL(3)-only and UND = 1,024; worse, a
  fresh prover using cap w < N would σ-label hidden-A₀ states at
  N/2 ≤ w < N as {(1,2),(1,2)} although their lifts realize u = N
  reads (odd N → RAM(N) → {(2,2)}): the label is FALSE there — which
  is exactly WHY the implemented cap is 2w < N. **Why MINOR, not
  GAP:** display-level only — the runner, the reader, every committed
  number, GENH4.B's closed forms and S6.3's complement display
  ("main factor q^{Σ comp(s): s ∈ A₁, **2s ≥ N**}") all carry the
  correct cap, so the condition is recoverable in-note by the
  UND/SPLTAIL partition; my own derivation (below) confirms 2w < N is
  the unique lift-sound cap; PE2 re-derived this exact boundary
  ("SPLTAIL needs 2w < N and UND takes 2w ≥ N — right in the note and
  right in the runner") and adjudicated the content clean — the
  residue is the same defect class as PE3's MINOR 1 (an exit-rule
  display whose listed-order/natural reading conflicts with committed
  keys, recoverable in-note), which this arc classed MINOR. Annex
  owed: state the F cap 2w < N at GENH4-3 + S6.1, and add the F
  clause to S7's SPLTAIL bullet (u_lift ≥ N > 2w).

* **MINOR 2 (S7 2SIDED bullet: the norm-valuation display is false in
  genre F's declared units).** S7 declares "genre F: w, u in v₁ = v
  units", under which v(A₀(θ)) = u and Nm_R(A₀) = Π_{η:φ(η)=0} A₀(η)
  has valuation **2u** (two roots, f_R = 2 — checked at the committed
  2SIDED(3,4) of (Zp,2,7,k1): u = 7, v(Res) = 2·3 + 2·4 = 14 = 2u).
  The bullet displays "= Nm_R(A₀), of valuation u **(both genres**,
  using GENH4-2 at the key's own roots η…)" — true for E, false for F
  by a factor 2. The displayed balance equation "j·w/2 + (4−j)(u−w)/2
  = u" is the F equation divided by 2, so it is numerically correct
  in both genres and j = 2 (hence the σ conclusion) is unaffected.
  **Failure scenario:** a reader computing in F's declared units
  solves j·w + (4−j)(u−w) = u and gets j = (4w−3u)/(2w−u) = 9 at
  (w,u) = (3,7) — impossible, self-alarming rather than silently
  wrong. Display-level, no number or conclusion moves: MINOR. Annex
  owed: one parenthetical ("valuation u in E-halved units; 2u in F's
  v-units, the equation below is the halved form").

* **REMARK (not a finding): S9.2's μ_E display carries a dangling
  token.** "2SIDED 1/(q²+q+1) − extra…, REFINE 1/(q²+q+1)". My
  from-scratch aggregation (below) gives the per-node masses EXACTLY
  RAM q²/Φ₂, SPLITEQ (q−2)/(2Φ₂), INERT q/(2Φ₂), 2SIDED 1/Φ₂, REFINE
  1/Φ₂ — summing to 1 with NOTHING subtracted; any positive "extra"
  would break the partition (self-alarming). The aggregated μ_E is
  right (machine-tied AND re-derived here). Likely an editing
  remnant; the "…" marks its own elision.

## Charge 1 (E-side, completed) — GENH4-CAP(E) + the slot ladder re-derived; own evaluator GREEN at every committed E key

* **CAP(E) re-derived (my own route):** out-of-window contributions
  have dv ≥ 2N (α₀/β₀ digit at height N → dv = 2N even; α₁/β₁ at
  N → dv = 2N+h > 2N odd), so in-window dv < 2N is lift-stable; and
  a computed dv ≥ 2N is only ever an odd ragged-band slot
  (2N+1 … 2N−2+h — the even string ends at 2N−2), which the lift's
  even 2N-digit undercuts, TYING NONE (parity): unstable. Hence the
  cap is exactly dv < 2N and the band {2N ≤ dv ≤ 2N−2+h} — (h−1)/2
  odd slots per string — is never consulted: the hidden factor
  q^{(h−1)/2} on every A₀-hidden leaf. Matches the note's CAP(E)
  display clause for clause.
* **The odd/even ladder at 2h+1:** A₁ odd slots 2v(α₁)+h from
  (h+1)/2 → 2h+1, 2h+3, …, 2N−2+h; even 2v(α₀) from h+1 → 2h+2, …,
  2N−2; A₀ from (3h+1)/2 resp. 2h+1 → 4h+1/4h+2 onward — every
  integer of [floor+1, 2N−2] covered, raggedness only above: S2.3
  re-derived exactly.
* **Machine:** my own evaluator (`/tmp/pe5/e_side_checker.py`, no
  runner import, own recursion structure) reproduces **EVERY consE
  row in BOTH artifact JSONs: 10 rows, 301 keys, 0 mismatches**, each
  row's mass = (q−1)q^{4N−5h−3} exactly. The two named cells for the
  charge, both deep-band (h > 1, the ragged band live): (Zp,2,7,**h3**)
  [(h−1)/2 = 1 band slot per string; UND = 512 = q^{N+h−1}, the
  Q22-L3-correction value, reproduced from my own slot count] and
  (Zp,2,11,**h5**) [N = 2h+1 admissibility EQUALITY; empty ladder;
  RAM(21) = 32,768 + UND = 32,768, the half-drained stratum]. The
  deep-history cell (Zp,2,7,h1) [114 keys, H₂ to depth 2] passed
  key-for-key as well. GENH4-6's S₁-liveness is ASSERTED at every residual
  node my evaluator visits (`assert dmu in A1`) — 0 violations.
* **Teeth (mine):** T1 — RAM admitted at odd band values u ≥ 2N
  (CAP(E) violated) → mismatches on every deep-band row; T2 — SPLTAIL
  boundary moved to w < 2N (undercut floor ignored) → 62 mismatches.
  Both fired.
* **Runner-side:** `law_E` re-read at source — implements S6.1's six
  leaf forms verbatim (incl. `if dv1 < N` for SPLTAIL and the
  `deep0` band factor); its `integer_only`/`inert_c` knobs are
  exactly the sealed teeth GH-T-LAT/GH-T-CEN.

## Charge 2 — the level-0 assembly re-walked on branches PE4 did not own, WITH a direct HMENU3 cross-degree tie (fresh symbolic leg)

PE4 re-derived R_(2,2) and R_(1,4) from the ν₄ family table. This
pass re-executed the ENTIRE level-0 assembly (S9.3) independently
(`/tmp/pe5/assembly_check.py`, sympy over symbolic q):

* **ν₃ derived from the ACCEPTED HMENU3 note's five displayed cubic
  densities alone** (typed by hand from HM3.D; Σ = 1 verified), by
  inverting the CUBIC level-0 assembly q³R³_τ = SEP_τ +
  q(q−1)·ν₂(τ∖(1,1)) + q·ν₃(τ) with ν₂ = the ACCEPTED W-11 vector.
  (Independent corroboration in passing: my ν₃ ≡ engine β₃ term for
  term — the supp leg's identity re-hit by different code.)
* **ν₄ = the md5-pinned engine's β₄** (engine leg, disclosed — the
  one non-hand input; its independence is BOX-6's Igusa-recursion +
  BCFG reconciliation, and its ν₄ ≡ assembly tie is GH-DENS's sealed
  check which PE4 re-derived at two entries from the family table).
* **The eleven shapes/censuses of S9.3 re-typed and re-summed:
  Σ censuses = q⁴ symbolically** (C(q,4) + C(q,2)n₂ + C(n₂,2) + qn₃ +
  n₄ + qC(q−1,2) + qn₂ + C(q,2) + q(q−1) + q + n₂).
* **RESULT: all ELEVEN assembled R_τ ≡ the S9.4 displays, symbolically
  in ℚ(q)** (displays typed by hand and first pinned against the
  note's q = 2 anchors, 11/11). In particular the two branches no
  pass had walked: **R_(1,1)(1,3) = [q·n₃ + q(q−1)·ν₃({(1,3)}) +
  q·β₄({(1,1),(1,3)})]/q⁴** and **R_(1,1)(3,1) = [q(q−1)·ν₃({(3,1)})
  + q·β₄({(1,1),(3,1)})]/q⁴** — the (1,3)/(3,1) branches consume the
  HMENU3 menu DIRECTLY, so this is the first cross-degree consistency
  tie of the quartic display to the accepted cubic display.
* **μ_E re-derived from scratch** (infinite-ladder geometric
  aggregation, self-similar node, closed forms RAM = (1−r)/(1−r³)
  etc., r = 1/q): per-node masses exactly S9.2's five values, and
  μ_E = (q/(q+1), 1/(2(q+1)), 1/(2(q+1))) = ν₂'s fractions — S9.2's
  claim PROVED by my own route; μ_F follows by q → q² (same ladder
  structure, alphabet Q). S6.2's bracket re-verified (1 + (q^{f₁}−1)
  per ladder point telescopes to q^{f₁·δ}; per-advance forms
  (q−1)q^{2μ−1} / (q²−1)q^{2(μ−1)} check).
* **Teeth (both fired):** swapping ν₃({(1,3)}) ↔ ν₃({(3,1)}) breaks
  both branch ties; corrupting ν₂ breaks R_(2,1)².

## Charge 3 — the [GENIND-H(4)] supply argument ITSELF (S7 → W-12.D's σ-labelling clause), re-derived at both characteristics

The charge: not the citation (PE3 verified the W-12 firing-table row
byte-faithful) but whether GENH4.C's CONSTRUCTION produces the
labelling W-12.D consumes. W-12 (A1) [r4] requires: each core family
carries a σ_F such that EVERY disc ≠ 0 lift of EVERY member has
σ = σ_F. GENH4.C supplies exactly that shape ("at every decided stage
leaf … EVERY lift with disc ≠ 0 has the σ claimed by the leaf
dictionary"), and the dictionary is TOTAL on the decided-leaf kinds
(RAM/2SIDED/SPLITEQ/INERT/SPLTAIL, both genres; UND is excluded from
the decided menu and drains to (A2)). I re-derived all six S7 bullets:

* **E-RAM:** u odd, u ≤ 2w ⟹ u < 2w strictly (parity) ⟹ one-side
  Y-polygon, v(Y) = u/4 with u odd ⟹ 4 | e(L) ⟹ [L:base] = 4:
  {(4,1)}. **F-RAM:** v(Y) = u/2, u odd ⟹ 2 | e; F_{q²} ⊆ k_L ⟹
  2 | f; ef ≤ 4 ⟹ e = f = 2: {(2,2)}. Char-free (polygon/valuation).
* **2SIDED:** Res(F,φ) = Nm_R(A₀); j roots at the low slope: the
  balance forces j = 2 (in F units: jw + (4−j)(u−w) = 2u ⟹
  j(2w−u) = 2(2w−u) ⟹ j = 2, u ≠ 2w); Galois-invariance kills
  irreducibility; E: no root in base (v = h/2 ∉ ℤ) ⟹ 2+2, each
  factor e = 2, f = 1; F: no root in base (residue is a ψ-root ∉ F_q)
  ⟹ 2+2, each factor f = 2, e = 1. Char-free. (MINOR 2 = the units
  display only.)
* **SPLTAIL:** E: u_lift ≥ 2N > 2w below the cap ⟹ 2SIDED for every
  lift incl. A₀ = 0 (F = φ(φ+A₁), both factors one-side). F: u_lift ≥
  N > 2w below the TRUE cap 2w < N ⟹ same — and at N/2 ≤ w < N the
  label would be FALSE (u_lift = N reads), which is why the reader
  exits UND there (MINOR 1 = this inequality's display).
* **SPLITEQ:** one recentering with root s₁ kills the 2dμ-pin
  (R₂(s₁) = 0) and leaves the dμ-digit R₂′(s₁) = s₁ − s₂ ≠ 0 (char 2:
  = S₁ ≠ 0 forced by '11' separability): every lift lands u′ > 2dμ =
  2w′: 2SIDED σ. Both characteristics displayed and re-derived.
* **INERT:** Ȳ = res(Y/n₂(θ)) is a root of the TWISTED residual (the
  S3 normalizer computation — re-derived, and exercised at q = 9 in
  the fresh route below); E: [F_q(Ȳ):F_q] = 2 with e even ⟹ {(2,2)};
  F: Ȳ ∈ F_{q⁴}∖F_{q²} ⟹ [F_q(Ȳ):F_q] = 4 ⟹ {(1,4)}.

All six use only lift-stable data (CAP), so the quantifier is over
every lift: the (A1) clause is genuinely SUPPLIED at n = 4, both
characteristics. The non-composite families are supplied at the
order-1 layer + P(2)/P(3) (PE3's check, re-confirmed at pin).
**Charge 3 verdict: the supply argument is sound; the residue is the
two display MINORs.**

## Charge 4 — the conditionality display at verdict-time git state

Stack refreshed against git AT THIS VERDICT (per the note's [r3]
standing as-of disclosure, which prices exactly this):

* **GENIND:** moved since the [r3] display — r2 complete (52fb6ff),
  passPE3 NOT CLEAN 0C+2G+4m (f89b565), **r3 complete (d3ef66d)**:
  the capped-window formula (M_ℓ = N − D_ℓ, co-blocks capped at the
  extracted child's slope) corrected at GENIND-3/GENIND-6(a)/M6.
  Counter 0/2. **Load-bearing sub-check:** GENH4 consumes
  GENIND-1(ii)/GENIND-4/GENIND.B + the genre grammar — grep of the
  note: zero hits for GENIND-3/GENIND-6/M_ℓ (PE4's check, re-run at
  the new r3); GENIND-4 (the E fibration) is untouched by GENIND r3;
  the GENIND-5 mentions in S6.2/GENH4.D are naming references to the
  bracket VALUE, proved independently in S6.2. Nothing GENH4 consumes
  moved.
* **W-12:** r5 (ee17210) = last commit touching the file = the S11
  [r2] pin. Current. 0/2.
* **HEX3:** r3 (b6a1d69) = the [r3] display. Current. 0/2.
* **HMENU3:** ACCEPTED 2/2 + ANNEX A (19c0285, the HM3.C (A0)
  disc ≠ 0 quantifier — disclosed in the note's [r2] box; GENH4 cites
  HM3.D's displays and ν₃, never HM3.C's corrected sentence; my
  charge-2 leg consumed the HM3.D displays directly and they tie).
* **W-11:** ACCEPTED 2/2, no motion. **QSCOUT22:** instrument, pins
  verified. **HE7** (ACCEPTED 2/2 this wave) is NOT in GENH4's stack
  — S11 does not cite it (checked).
* **Minimum grade over the stack: 0/2, UNCHANGED** (W-12, HEX3,
  GENIND) ⟹ **P(4)'s conditionality display is unaffected**; the
  S10-BOX-1 [r3] display is accurate as-of its commit and the
  standing disclosure covers the since-motion. GENH4's own counter:
  1/2 at PE4 → **2/2 at this pass**.

## Charge 5 — free hunt over the full [r1]+[r2]+[r3] tag set

Every tagged block visited (S0 floors, S1 census box, CAP/S4
trichotomy, S6.1 gloss, S9.2 supp label, S10-BOX-1 ×3, S11 W-12
re-pin, S13 arc lines). Cross-round consistency: the r2 census clause
and the r3 mnemonic scoping compose (S1's "away from the boundary
band" + the [r2] q^{comp}−1 clause adjacent — no contradiction); the
r3 trichotomy is the corrected form of the r2 text it replaced, and
both S6.3 and GENH4.B carry the same boundary content; the arc-line
hashes (PE3 a011533/3b88321 → r3 4b0d946 → PE4 e15308d) verified
against git; the note body at HEAD is byte-identical to r3 (diff = 0
lines). GENH4.B's genre-E aggregate (q−1)^{r+1}q^{2N−h−2} re-derived
(binomial sum over H₂ ⊆ ladder of size N−1−2h); P-3's spot values
re-derived ((Zp,7,3,h1): UND per center-letter q^{N+h−1} = 343 × 6
letters = 2,058 ✓). The only residue: the S9.2 "− extra…" REMARK
above.

## FRESH ROUTE — q = 9 = 3²: the FIRST odd-non-prime-q cells of the arc (own F₉ arithmetic end-to-end)

Disjoint from all six prior routes (seal battery; PE1 tuple scans +
q = 7 full scan; PE2 symbolic + 504-ledger + q = 11/13; PE3 equal-char
walkers q = 2/5 + wild mechanism-free; PE4 non-prime q = 4/16 char 2;
r-rounds counter-key reads). `/tmp/pe5/q9_walker.py` — no runner, no
reader import: own GF(9) = F₃[ω]/(ω²+1) tables, own series ring, own
polynomial division, own reader written from GENH4-3/CAP(E)/S3's
twisted normalizer/S5's recentering, floored-node asserts armed at
every refine.

* **Validation leg (Fqt,3,5,h1):** FULL row, 1,062,882 members built
  THROUGH the GENIND-4 development map (round-trip asserts) and read
  by my walker: **25 keys, 0 mismatches vs the committed GH-FRESH
  row** — my instrument reproduces a committed row key-for-key before
  touching fresh territory.
* **Fresh leg (Fqt,9,4,h1), conditioned box** (α₀ v ≥ 3, β₁ v ≥ 3;
  A₁ slots {3,5,6,7}, A₀ slots {6,7}), letters z ∈ {1, g = ω+1
  non-square}, 9⁶ = 531,441 members per letter. The 8-key table was
  HAND-DERIVED from the note's laws BEFORE the run (preregistration in
  the runner docstring + derivation here): SPLITEQ(3) 183,708 =
  (24+4)·9⁴ [per-S₁≠0 row over F₉: '11' 3 / '2' 4 / '1sq' 1 — the F₉
  square-class census; S₁ = 0 rows split 4/4], INERT(3) 236,196,
  2SIDED(3,4) 46,656, RAM(7)@() 5,832, SPLTAIL(3) 5,832, UND@() 729,
  and — through the refine — **RAM(7)@(3,) 46,656 + UND@(3,) 5,832,
  derived via the CARRY-FORCED w′ = 4**: S5's odd-dμ carry
  C = ŝ²t² + α₁ŝt revives the conditioned-dead α₀ slot at dv 4 with
  digit 2s² ≠ 0 (char 3), so the deeper node's w′ is deterministic —
  a nontrivial consequence of the carry formula, preregistered and
  measured. **RESULT: measured ≡ preregistered, all 8 keys, BOTH
  letters (masses 531,441/531,441); every refine's floored-node
  assert passed (the twist-carry cancellation S₀ + zs² − 2zs² = 0
  pointwise at q = 9, char 3).**
* **Teeth (both fired):** T-TWIST — at z = g, the 52,488 events whose
  UNTWISTED disc vanishes (S₁² = 4S₀, truly decided under the twist)
  were recentered with the untwisted letter: the 2dμ-pin stayed ALIVE
  on **52,488/52,488** — the z̄-twist (W-9's cocycle) is load-bearing
  at non-prime odd q, exactly as S3/S5 derive. T-CEN9 — swapping the
  F₉ square-class censuses ('11' 3 ↔ '2' 4) mismatches the measured
  counts. (Runtime 38 s; log `/tmp/pe5/q9.log`.)

## MACHINE LEG (completed)

* **Pins 11/11** at worktree = HEAD = r3 = PE4 (skeleton section
  above); note body at HEAD ≡ r3 4b0d946 byte-identical.
* **Isolated full re-run** (/tmp/pe5/run, fresh copy, committed
  artifacts never written): **GREEN, exit 0, 930.2 s, 245,693 checks,
  0 violations** — GH-PIN 6 · JSONTIE 481 · FRESH 54 · PRE2 5 ·
  REFINE 192,000 · FEVEN 8 · PD 46,590 · UND 92 · BRACKET 157 ·
  DENS 115 · SIGMA 6,185; teeth LAT 19 / CEN 14 / ALPH 4 / SIG 2 /
  DENS 1 — every count identical to S13.2. **Results-JSON leaf-diff
  vs committed: `/elapsed_s` ONLY (131 leaves); output txt ex-timing
  identical.** Supp leg re-run: GREEN 3.0 s, leaf-diff = `/elapsed_s`
  only, output ex-timing identical.
* **Tautology audit:** all three of my instruments (E-side evaluator,
  assembly script, q9 walker) share no code with the runner/reader;
  the assembly script's single non-hand input is the md5-pinned
  engine's β₃/β₄ (disclosed; β₃ doubly covered by my own HMENU3
  inversion). Runner-side `law_E`/`law_F`/reader exits re-read at
  source and quoted above (MINOR 1's evidence).

## Clean charges (executed, nothing at GAP-or-worse found)

Charge 1 (E-side end-to-end — CAP(E) re-derived, 301/301 keys, teeth);
charge 2 (level-0 assembly all eleven + the first HMENU3 cross-degree
tie + μ_E from scratch); charge 3 (the σ-labelling supply argument
re-derived both characteristics — residue = the two display MINORs);
charge 4 (verdict-time stack: min grade 0/2 unchanged, no consumed
surface moved); charge 5 (tags, hashes, cross-round consistency);
machine leg (bit-identical modulo timing); fresh route (first
odd-non-prime-q cells, preregistered-exact, twist tooth 100%).

## GRADE LINE

**CLEAN: 0 CRITICAL + 0 GAP + 2 MINOR (+1 remark). The 2-clean count
completes: 1/2 → 2/2. GENH4 is ACCEPTED — the second stage-one note
through the hostile-arc bar (after HE7). P(4), the [GENIND-H(4)]
discharge, and the eleven quartic densities R_τ(q) stand as composed,
machine-corroborated, conditional exactly on the S11 arc-grade stack
(minimum grade 0/2 at verdict time: W-12, HEX3, GENIND live). The note
text is FROZEN at r3 4b0d946; dated appends only; one dated annex owed
for MINOR 1 + MINOR 2 (three display sentences, no statement or number
moves — the HE7 F-1 precedent).**

## Verifier's session artifacts (all under /tmp/pe5; repo untouched except this report)

* `/tmp/pe5/e_side_checker.py` — own genre-E law evaluator (charge 1).
* `/tmp/pe5/assembly_check.py` — the eleven-density level-0 assembly +
  HMENU3 inversion + μ_E scratch derivation + teeth (charge 2).
* `/tmp/pe5/q9_walker.py`, `/tmp/pe5/q9.log` — the q = 9 fresh route.
* `/tmp/pe5/run/`, `/tmp/pe5/rerun.log`, `/tmp/pe5/supp.log` — the
  isolated battery + supp re-runs.
