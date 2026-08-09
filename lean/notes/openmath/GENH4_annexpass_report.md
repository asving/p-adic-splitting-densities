# GENH4 ANNEX-PASS — HOSTILE VERIFIER REPORT (scoped: ANNEX PE5 + ANNEX R)

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 GAP + 4 MINOR (+ 2 remarks),
scoped to the two annexes.** The GAP sits in ANNEX R's R2 (the F4
repair): its N-even band-pinned per-stratum witness leg is FALSE, with
a MACHINE-REFUTED instance at (q,N,k) = (2,10,2) — the u = 10
refine-path lifts that R2's refine-deeper display labels
2SIDED′ → {(1,2),(1,2)} read PARI σ = {(2,2)} on 6/6, and at (2,8,2)
the "Lift 2" read R2 invokes is structurally unrealizable, making the
whole band-pinned stratum σ-CONSTANT — no within-stratum differing
pair exists there at all. Clause (c)'s KEY-LEVEL conclusion (no single
lift-sound label for the leaf key) SURVIVES — machine-confirmed by
band-zero contrast members of the same keys (6/6 {(1,2),(1,2)}) —
and (c) is unconsumed by W-12.D, so no consumer breaks: GAP, not
CRITICAL. The heavy consumed surface — ANNEX-LEMMA GENH4-7'(b), the
F-SPLTAIL σ-supply over the free band — was re-derived from scratch
and survived every attack, including two fresh cells (first k = 3
ever; first odd-q k ≥ 2). Both annex machine legs re-ran isolated
GREEN (PE5 leg bit-identical; R leg elapsed-only diff); all md5 pins
and byte-freezes verified.

Scope and provenance: target = the TWO ANNEXES of
`GENH4_PROOF_2026-08-08.md` — ANNEX PE5 (baf05ed/e945734/cceca77:
ANNEX-LEMMA GENH4-7 + A2 + A3 + `genh4annex_supp.py`) and ANNEX R
(6272cd4/b10a5a7: ANNEX-LEMMA GENH4-7' + R2 per-stratum displays + R3
L/O_L frame + R4 units + R5 law-keys + `genh4annexr_supp.py`). The
frozen accepted body's 2/2 is NOT at stake and nothing here touches
it. Fresh context, zero prior stake, quote-and-classify, fix nothing.
Body sections read for context: GENH4-3 (S4), S2.1/S2.3, S6.1/S6.3,
S7, S8; `CODEX_GENH4RAT_2026-08-09.md` read for what ANNEX R repaired.

## S1. Findings

### GAP-1 — ANNEX R, R2's N-even band-pinned leg + the refine-deeper leg: FALSE per-stratum witness claims, machine-refuted; clause (c)'s per-stratum re-establishment fails on band-pinned strata (unconsumed; key-level conclusion survives)

**Quoted (R2, N-even dμ < w bullet):** "band-pinned with m ≤ 2w:
u = N residual read at depth dμ < w (S₁-slot 0): char ≠ 2 decided
≠ {(2,2)} as above; char 2: '1sq' → one refine step. NO
residual-class comparison is needed in this sub-case — the char-2
even-N gap of the old display is bypassed by the RAM(N+1) leg."

**Quoted (the refine-deeper leg):** "LEMMA GENH4-4 maps the refine
locus ONTO the floored fresh node {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁},
whose digits are free lift digits; realize the fresh leaf
dv(A₁′) = dμ₁+1 =: w′, dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ …: a fresh
2SIDED′(w′, w′+1) for every such lift, σ = {(1,2),(1,2)} … Clause (c)
is thereby re-established at the key level in every stratum."

**Failure scenario 1 (machine-refuted, the refine-path).** Cell
(q,N,k) = (2,10,2), UND key (2w = 14 ≥ N), band-pinned stratum
m = 11 (b₁@9 ≠ 0), w = 7, dμ = 5 < w — squarely inside the quoted
bullet. The u = 10 lift (b₀@10, in budget) reads '1sq' at depth 5
and refines; the quoted display then promises a fresh
2SIDED′(6,7) → σ = {(1,2),(1,2)} "for every such lift". FALSE: the
fresh leaf dv(A₀′) = 2dμ+3 = 13 is UNREALIZABLE — the height-11 band
letter's ȳ-component d₁ ≠ 0 survives the refine (λ = ŝ²π¹⁰ + ŝπ⁵A₁
contributes the height-10 kill plus terms at heights ≥ 12 only; no
correction reaches height 11), so dv(A₀′) = 11 is FORCED, 11 odd
≤ 2w → RAM(11) → σ = {(2,2)}. The transport error: GENH4-4's
onto-the-fresh-node statement holds over the FULL refine slice
(all in-window digits free), but here the member is FIXED and only
LIFT digits vary — "whose digits are free lift digits" is false for
the A₁′ string (in-window, key-pinned: dv(A₁′) = w in equal
characteristic since s₁ = √S₀ ∈ F_q gives carry C = 0 and the 2w_re
term dies; = dμ+1 in mixed characteristic by the +2w_re revival —
forced either way, never free) and false for A₀′ below m. PARI
adjudication (fresh leg FR4): the 6 refine-path u = 10 lifts across
3 pins read σ = {(2,2)} on 6/6 — the verifier's RAM(11) derivation
CONFIRMED, the annex's 2SIDED′ display REFUTED. All 12 lifts of the
stratum read {(2,2)} (the stratum is σ-constant), both u = 10 and
u = 11 shapes.

**Failure scenario 2 (structural, N ≤ 4k).** Cell (2,8,2), band-pinned
m = 9, w = 6 (N = 8 even, dμ = 4 < w: in the bullet's scope). The
quoted "u = N residual read" DOES NOT EXIST: the height-8 letter's
two components both sit below the GENH4-1F entry budgets
(b₀@8 < v(β₀) ≥ 4k+1 = 9; b₁@6 < v(β₁) ≥ 3k+1 = 7) — a "lift" with
b₀@8 ≠ 0 leaves the entry family (its B₀ leading digit cancels:
v(B₀) = 9 ≠ 4k = 8, breaking the entry pin; smoke members built in
violation came back OUTSIDE the F dictionary entirely —
{(2,1),(2,1)}, disc 0 — disclosed in the fresh leg's docstring). So
every in-family lift has u = 9 = m → RAM(9) → σ = {(2,2)}
CONSTANT, in BOTH characteristics (12/12 machine) — neither the
char-≠2 leg nor the char-2 leg of the quoted sentence produces a
within-stratum differing pair, because no second read exists.

**Classification: GAP** (justification gap in the unconsumed
sharpness clause's re-proof). What survives: clause (c)'s conclusion
AT THE KEY LEVEL — the leaf key aggregates band strata (deep0 is
inside the key mass), and band-zero members of the SAME keys carry
u > 2w lifts with σ = {(1,2),(1,2)} (machine: 6/6 at both cells), so
"no single label is lift-sound FOR THE KEY" holds, which is exactly
what cap-uniqueness consumes; the reader's UND exit stays
conservative-sound; W-12.D consumes (b) only. What does not survive:
R2's sentence "re-established at the key level in EVERY STRATUM" read
as within-stratum witness existence, the refine-deeper leg's fresh
2SIDED′ construction (false in equal characteristic everywhere it is
invoked on a fixed member, false in both characteristics where the
band caps u′ ≤ m < 2dμ+3), and the N-even band-pinned sub-case's
claimed differing pair (no pair exists there). Owed: a dated
correction to R2 scoping the N-even band-pinned sub-case to
key-level (cross-stratum) witnesses — which is all (c) ever needed.

### MINOR-1 — GENH4-7'(a)'s realizability parenthetical (and R2's u-geography) false at N ≤ 4k hidden states

**Quoted (GENH4-7'(a)):** "u_lift = N realizable (the a₀ lift digit
at position N)". **Quoted (R2):** "u_lift sweeps {N, N+1, …} at a
band-zero state".

**Failure scenario:** at (2,8,2) hidden states (nonempty: every UND
leaf there), position N = 8 sits BELOW the entry budget
v(β₀) ≥ 4k+1 = 9 and the height-8 b₁-component below v(β₁) ≥ 7: the
height-N letter is structurally zero, u = N unrealizable; the sweep
starts at max(N, 4k+1). Harmless for the consumed clause (b) —
SPLTAIL forces N ≥ 4k+3 > 4k+1, where position N is in budget and
every committed and fresh cell confirms realizability — and for every
committed row; it bites only inside (c)'s geography, where it is
mechanism 2 of GAP-1. The floor half of (a) (u_lift ≥ N, every band
completion, every lift) is exact everywhere (re-derived, and
enumerated 24,576/0 by the annex leg's C4 + 96 + 96 fresh members).

### MINOR-2 — R2's 2w = N char-odd line-partition argument: quantifier slip at s = 0 and the 0-line case

**Quoted:** "if for EVERY square s and every d₀ the value s/4 − c·d₀
were a square, the set (squares ∪ {0}) of size (q²+1)/2 would be a
union of full affine lines in direction c, each of size q —
impossible since q ∤ (q²+1)/2."

**Failure scenario:** the faithful negation of the existence claim
quantifies only over REALIZABLE s = S₁² with S₁ ∈ F_{q²}^× — the
NONZERO squares; s = 0 is not realizable (pin letter ≠ 0), so the
displayed hypothesis is stronger than the negation, and without the
s = 0 instance the coset c·F_q through 0 is not covered: "union of
FULL affine lines" needs the extra half-step. It closes two ways: at
the actual instance c = 1 (genre F has no twist, S3) the 0-coset is
F_q ⊆ squares of F_{q²} automatically (every F_q element is a square
in F_{q²}, q odd); or count Sq∖{0} = (q²−1)/2, also ∤ q. Conclusion
(inert-continuation members EXIST at 2w = N, char odd) HOLDS; display
slip only.

### MINOR-3 — R2's N-odd dμ₁ = w branch: "separable in both characteristics" / "any nonzero digit gives a decided '11'/'2'" false at the single char-odd degenerate digit

**Quoted:** "if dμ₁ = w (N+1 = 2w) the S₁-slot is the pin letter ≠ 0,
the residual is separable in both characteristics, and any nonzero
digit gives a decided '11'/'2' ≠ {(2,2)}."

**Failure scenario:** char odd, the digit d₀ with S₀ = S₁²/4 (when
S₁²/4 lies on the S₀-line — possible) gives disc = 0: '1sq', neither
separable nor decided. In char 2 the claim is exact (disc = S₁² ≠ 0).
Existence of a decided second lift survives at every odd q ≥ 3
(≥ 2 admissible digits, ≤ 1 degenerate), so the differing pair —
which is all the branch needs — exists; the universal is the defect.
The branch's instance claim at Codex's (2,9,5) cell is char 2 and was
machine-confirmed this pass (FR5: 9/9, RAM(9) {(2,2)} vs decided
{(1,2),(1,2)}/{(1,4)}).

### MINOR-4 — GENH4-7' supersession header: "everything else unchanged" undersells its own scope

**Quoted:** "(GENH4-7 with the leaf's true floor … replaces GENH4-7's
hypothesis sentence and clause (a)'s parenthetical, everything else
unchanged)."

**Failure scenario:** 7'(a) also ADDS a new claim absent from 7(a)
(the band cap "u_lift ≤ m := the lowest nonzero band height"), and
clause (c)'s proof is wholly replaced (old two-lift witnesses
withdrawn, re-proof delegated to R2) — a reader trusting "everything
else unchanged" mis-inventories what moved. The replacement itself is
stated correctly in R1.0/R2; cosmetic display defect of the header.

### Remarks (no grade)

* **Remark 1 (R3's consumption-audit sentence).** "S7's resolvent
  chain … all run in L/O_L verbatim" is loose: S7's Y-trichotomy runs
  in the QUARTIC root field base(θ_F), not in L = Frac(R); the facts
  consumed there are covered by S7's own displayed transport
  ((F) v(θ) = k, res(θπ^{−k}) a root of ψ) plus the R6 rider (the
  GENH4-2 cite is to the proof, not the stated scope). The part of S7
  that genuinely lives in L — the norm identity Π_{η:φ(η)=0} F(η) at
  the KEY's roots — is correctly covered. No consumer breaks.
* **Remark 2 (R2's char-2 inert-existence at 2w = N).** Re-derived
  and SOUND: trace transitivity Tr_{F_{q²}/F₂}(c d₀/S₁²) =
  Tr_{F_q/F₂}(d₀·τ) with τ = Tr_{F_{q²}/F_q}(c/S₁²) (d₀ ∈ F_q pulls
  through), squaring = Frobenius bijection on F_{q²}^× so S₁² sweeps
  it, Tr_{F_{q²}/F_q} vanishes on only q of q² elements so τ ≠ 0
  members exist, and a nonzero F₂-functional on F_q attains 1. The
  honest-scope sentence (τ-degenerate members; key granularity) is
  correctly scoped.

## S2. Clean charges (each attacked, none broke)

1. **ANNEX-LEMMA GENH4-7'(b) — the consumed F-SPLTAIL supply —
   re-derived from scratch (charge 1).** The leaf-sense floors
   (v(a₀) ≥ N; v(a₁)+k ≥ N+1 with a₁-positions ≤ N−k vanishing) with
   the k−1 band digits FREE: every potentially nonzero letter of
   A₀^lift sits at v₁-height ≥ N — a₀ state digits are zero to N−1
   and lift digits sit at positions ≥ N; a₁ band digits sit at
   heights N+1 … N+k−1 ≥ N+1; a₁ lift digits at heights ≥ N+k. The
   attack "can a band digit LOWER u_lift below N via cancellation in
   A₀^lift?" fails structurally: valuation = lowest height with
   nonzero letter; there IS no letter below height N to cancel into,
   cross-height contributions of θ's deeper unit digits only move
   mass UPWARD, and within a height the F_{q²}-letter d₁ȳ + d₀
   vanishes iff both components do ({1, ȳ} F_q-independent, ψ
   irreducible — GENH4-2(F), both characteristics). So u_lift ≥ N for
   EVERY band completion and EVERY lift; 2w < N gives GENH4-3(ii)'s
   antecedent at every lift; w is lift-stable (w ≤ (N−1)/2 < N,
   letter at comp-2 height); S7's 2SIDED F-leg consumes only
   (v(A₁(θ)) = w, v(A₀(θ)) = u > 2w) → σ = {(1,2),(1,2)}.
   **The A₀ = 0 corner via F = φ(φ + A₁):** φ + A₁ keeps the S2.1
   genre-F invariants — v(a₀-comp) ≥ w > 2k keeps v(p₀+a₀) = 2k
   exact with the same residue, v(a₁-comp) ≥ w−k > k keeps the
   residue pair, so ψ is unchanged and irreducible: both quadratics
   have f = 2 roots; disc ≠ 0 (the clause's antecedent) gives
   coprimality: σ = {(1,2),(1,2)}. CLEAN — and exercised fresh at
   TWO new cells (S4: first k = 3, first odd-q k ≥ 2), 96 + 96 + the
   annex leg's 96 + 24,576 enumerated, zero violations anywhere.
2. **The (a) clause's "u_lift ≤ m at a band-nonzero member" —
   direction and consumption (charge 2).** Direction CORRECT: the
   height-m letter has d₁ ≠ 0 (the band digit), and d₁ȳ + d₀ ≠ 0 for
   every d₀ since ȳ ∉ F_q — the letter cannot be killed by the free
   a₀ digit, so v ≤ m (an upper CAP on u_lift, as consumed). R2
   consumes it in exactly this direction (band-pinned m ≤ 2w kills
   u > 2w lifts — Codex's (2,9,5) instance). Machine: FR2A/FR2B
   verified u ≤ m on every band-nonzero fresh member (valuation
   layer). CLEAN (modulo MINOR-1's separate realizability nit).
3. **R1.0's self-contradiction display of old GENH4-7.** Verified:
   "a₁-positions ≤ N−1 all vanish" gives v(a₁) ≥ N i.e.
   v(a₁)+k ≥ N+k, strictly stronger than the proof's floor N+1 —
   the two bold clauses do contradict each other exactly as ANNEX R
   quotes them; the counted leaf (law_F's deep0 = q^{k−1}) matches
   the WEAK reading. CLEAN.
4. **R1.1 supersession of 7(b) by 7'(b) (charge 5).** The supersession
   IS stated — R1.1 re-points THEOREM GENH4.C's F-SPLTAIL leg
   ("now reads ANNEX-LEMMA GENH4-7'(b) in place of GENH4-7(b)"), and
   the What-does-not-move box names "GENH4-7's hypothesis sentence
   (superseded by GENH4-7', conclusion identical)". Grep audit of
   every "GENH4-7" site in the repo: the remaining old-form citations
   (PE5 annex riders at lines 1236/1262/1335/1472) sit INSIDE the
   byte-frozen PE5 text that ANNEX R may not edit, and all cite the
   CONCLUSION of (b), which is byte-identical between 7 and 7'; sites
   outside the note (GENIND S14, PROJECT_STATE, the scaffold) are
   records, not consumers. The W-12.D chain routes through GENH4.C's
   F-SPLTAIL leg = S7's bullet = 7'(b) after R1.1 — one re-point
   covers the one consumption path. CLEAN (MINOR-4 is the header's
   own inventory sentence, not a supersession hole).
5. **R3's L/O_L frame restatement — three ridered sentences verified
   against what the proofs consume (charge 3).** (i) S2.1's E bullet
   "R is a complete DVR": restated facts e = 2, f = 1, v(θ) = h/2,
   value group ½ℤ, O_L/m_L = F_q, res(θ²π^{−h}) = z — re-derived
   (polygon single side (0,h)–(2,0), h odd; θ² = −p₁θ − p₀ with
   v(p₁θ) ≥ h + 1/2 > h = v(p₀), residue −(−z) = z); these are
   EXACTLY the inputs of GENH4-2(E)'s parity proof and S3's
   normalizer residue — no silent strengthening (nothing consumed
   R-module structure; the censuses are O[x]-coefficient counts).
   (ii) S2.1's F bullet: e = 1, f = 2, v(θ) = k, ℤ, F_{q²} = F_q(ȳ),
   res(θπ^{−k}) = ȳ — re-derived (u² + (p₁π^{−k})u + p₀π^{−2k} = 0
   reduces to ψ(ū) = 0, ψ irreducible); exactly GENH4-2(F)'s and
   S3's inputs. (iii) The gr sentence re-aimed at gr(O_L): the body
   itself says "cited as frame; everything below is proved directly"
   — zero consumption. The non-maximality witnesses check:
   R/2R ≅ F₂[ε]/(ε²) at x²+2x+4 (θ² ≡ 0 mod 2, θ ∉ 2R); genre E
   h ≥ 3 m_R non-principal (v(γ) = 1 forces v(c) = h/2−1 ∉ ℤ);
   R = O_L exactly at E h = 1. CLEAN (Remark 1 on the S7 sweep).
6. **R4's F true-unit table.** Verified against S7: opening w, u ✓
   (v₁ units); RAM v(Y) = u/2 already true-unit ✓ (that
   half-integrality IS the e-even mechanism); 2SIDED {w, u−w} ✓
   (two-side polygon slopes); INERT v(Y) = dμ with n₂ = π^{dμ} ✓
   (S3's F line). σ conclusions scale-blind ✓. CLEAN.
7. **R5's pre2 six-key partition.** Hand re-derived from the floored
   box (floors 9/7/5/3, free digits 2+4+6+8): VTX = 1·2³·2⁶·2⁸ =
   2¹⁷ (B₀ 9-digit 0, 10-digit forced 1 at q = 2; B₁ 7-digit forced),
   L1TAIL = 2^{4+6+8} = 2¹⁸ (B₀ window-zero); 655,360 + 2¹⁷ + 2¹⁸ =
   2²⁰ exact; LAW_KINDS definition matches the sealed runner line
   299. Machine-tied (C1, isolated re-run). CLEAN.
8. **ANNEX PE5 A2 (the 2u norm).** Re-derived: genre F roots η of φ
   have v(A₀(η)) = u each (GENH4-2 at v(η) = k), two roots →
   v(Nm) = 2u; the halved and unhalved balances both give
   j(2w−u) = 2(2w−u) → j = 2; the mixed form j = 9 at (3,7)
   self-alarms. Machine: C4 5/5 two-route v₂(Res) = 14 = 2u. CLEAN.
9. **ANNEX PE5 A3 (the "− extra…" closure).** Re-derived
   symbolically: (1−r)(1 + r + r²)/(1−r³) = 1 gives
   q²/Φ₂ + 1/Φ₂ + q/Φ₂ = 1; even-dμ split (q−2)/(2q) + 1/2 + 1/q = 1;
   aggregation ×Φ₂/(q²+q) reproduces ν₂'s (q/(q+1), 1/(2(q+1)),
   1/(2(q+1))). The extra is 0 by partition of unity. CLEAN.
10. **ANNEX PE5 A1's committed refutation + riders.** The three
    ridered display sentences quoted verbatim and unedited ✓; the
    wrong-cap tables re-derived by my own independent law typing
    (S4 FR3 ties the committed rows 15/16 cells key-for-key inside
    the 54-cell grid); the disclosed smoke catch (refined-history
    propagation) verified as exactly the diff cceca77 → e945734
    (mismatch tables + one decided-key guard + docstring — nothing
    else moved). CLEAN.

## S3. Machine legs (pins + isolated re-runs + instrument audit) — charge 6

**Pins, all verified at HEAD (2026-08-09).** The 5 sealed-artifact
md5s in BOTH scripts' PINS dicts match the committed files
(genh4_checks.py ee8024b7, output 9e6ca9b3, results cbcff562,
qscout22_checks.py cb885663, qscout22_results 6c2441a1). Byte-freezes:
body+PE5 md5 a584cb3e verified 3-way (baf05ed = b10a5a7 = HEAD,
first 89,530 bytes); r3 body 09af7f78 at 4b0d946. Script seals:
genh4annexr_supp.py at 6272cd4 == HEAD (d1d5288f — sealed BEFORE its
run, as claimed); genh4annex_supp.py seal cceca77 (3a3ca794) →
repaired e945734 == HEAD (bcb87498), diff verified = exactly the
disclosed C3 repair. Committed artifact md5s match the annex records
(PE5: 713a0a3b/37d0650e; R: c1ed4a7f/f26186fd).

**Isolated re-runs** (fresh /tmp sandbox, pinned artifacts + traced
transitive imports copied in; nothing sealed touched):
* PE5 leg `genh4annex_supp.py`: GREEN, exit 0, artifacts
  **BIT-IDENTICAL** to committed (713a0a3b / 37d0650e).
* R leg `genh4annexr_supp.py`: GREEN, exit 0, 0 violations; leaf
  diff vs committed = **elapsed-only** (0.4s → 0.5s in both files).

**Instrument audit (the two charged questions).**
* *Is C3's "old-gloss family = HALF" independently derivable?* YES,
  two independent legs: the annex leg's own C4 ENUMERATES all 24,576
  leaf members and counts the old-hypothesis violators digit-by-digit
  (n_oldviol = 12,288, a loop count, not the hardcoded law ratio);
  and this pass's fresh typing (S4 FR1/FR3) re-derives the leaf =
  3·2¹²·q^{k−1} independently, giving old-gloss/leaf = q^{1−k}
  (exactly HALF only at q = 2, k = 2 — at the fresh k = 3 cell the
  old-gloss family would be a QUARTER, 3·2¹⁷ of 3·2¹⁹).
* *Is the char-p Panayi leg independent of the char-0 leg?* YES:
  char 0 = PARI factorpadic + nfinit/idealprimedec (external
  library); char p = an in-script F₄[[t]] digit recursion sharing no
  code with it. Logic audited line-by-line: the char-2 derivative
  dbar[j] = f_{j+1} for j even is correct; simple residue roots
  count 1 by Hensel; multiple roots recurse on F(r + tx) with the
  correct binomial-mod-2 table; termination guarded by
  separability (fp_disc_nonzero = exact pseudo-remainder gcd over
  F₂[t], char-2 derivative c₃x² + c₁ correct). The read
  (r4, r2) = (4, 0) ⟺ {(1,2),(1,2)} is sound: 4 roots in unramified
  F₄[[t]] with none in F₂[[t]] forces two conjugate quadratic
  unramified factors given disc ≠ 0 ({(1,4)} would put roots in
  F₁₆ not F₄; any (1,1) factor would put one in F₂[[t]]; ramified
  factors contribute 0).

## S4. Fresh route — `genh4annexpass_fresh.py`, GREEN, 0 violations (final run exit 0)

Route chosen to differ from both annex legs (which ran (2,11,2) and
k = 1 rows): committed with artifacts alongside this report.
* **FR1 (first k = 3 cell EVER):** independent typing of the
  S6.1/S6.3 genre-F law at (2,15,3): no SPLTAIL at N = 13/14, first
  live at N = 15 = 4k+3 with SPLTAIL(7) = 1,572,864 = 3·2¹⁷·4,
  deep0 = 4 = q^{k−1} (TWO free band digits, heights 16/17), node
  mass 2²⁶ exact; the SEALED law_F(2,15,3) ties my typing
  key-for-key (first k = 3 exercise of the sealed runner anywhere).
* **FR2 (σ at two fresh cells, PARI):** (2,15,3) SPLTAIL(7), key
  x²+8x+64: 48 members (3 pins × 4 band values — the first
  multi-digit band — × 4 lifts incl. A₀ = 0 corner and u = N = 15):
  48/48 σ = {(1,2),(1,2)}; (3,11,2) SPLTAIL(5), key x²+9x+162
  (ψ = y²+y+2 irred over F₃): 48 members (first odd-q k ≥ 2
  exercise): 48/48. GENH4-7'(a)'s two inequalities (u ≥ N;
  u ≤ m at band-nonzero) checked on every member at the valuation
  layer. TEETH 4/4: wrong-floor mutants (b₀@13 resp. b₀@9, with and
  without a band digit) flip to RAM σ = {(2,2)}.
* **FR3 (the deep0 identity + grid):** band-slot count ≡ k−1 on the
  grid q ∈ {2,3,5} × k ∈ {1,2,3} × N ∈ 4k+1..4k+6 (54 cells); fresh
  typing == sealed law_F key-for-key on ALL 54; first-live boundary
  (SPLTAIL nonempty iff N ≥ 4k+3) exact; all 72 SPLTAIL keys carry
  the q^{k−1} factor. (Threshold note: the k−1 count holds for
  N ≥ 4k; below that the band truncates — relevant to MINOR-1.)
* **FR4 (GAP-1's machine leg):** 24/24 band-pinned lifts across
  (2,8,2) w = 6 and (2,10,2) w = 7 read σ = {(2,2)} CONSTANT; the 6
  refine-path u = 10 lifts at (2,10,2) — where R2's refine-deeper
  display predicts 2SIDED′(6,7) σ = {(1,2),(1,2)} — read {(2,2)}
  6/6; band-zero contrast members of the SAME keys 6/6
  {(1,2),(1,2)} (the key-level pair that keeps (c) alive).
* **FR5 (the Codex F4 cell, R2's N-odd leg):** (2,9,2) w = 5,
  band-pinned m = 10 = 2w: RAM(9) lift {(2,2)} vs u = 10
  separable-read lifts decided {(1,2),(1,2)}/{(1,4)} on 9/9 — R2's
  repaired N-odd witness CONFIRMED at the exact Codex instance.
* **Disclosures (this leg's own smokes, in the docstring):** (i) the
  first launch had two buggy cell-A teeth IN THIS SCRIPT (A₀ encoded
  as x¹³ instead of the coefficient pair) — fixed; FR1–FR3 were
  GREEN unchanged. (ii) the first FR4 build violated the entry
  budget (b₀@8 at (2,8,2)) — PARI returned non-F shapes, which is
  itself the structural half of GAP-1; construction corrected to
  in-budget lifts, predictions preregistered in the docstring before
  any FR4/FR5 output existed.

## S5. Grade line

**NOT CLEAN at annex scope: 0 CRITICAL + 1 GAP (GAP-1, ANNEX R R2's
N-even band-pinned per-stratum leg — machine-refuted display,
unconsumed clause) + 4 MINOR + 2 remarks. The annex stack does NOT
take its first clean mark: the annex-acceptance count stays 0/2.**
What this pass does establish: the CHALLENGE's consumed surface is
now solid — GENH4-7'(b) (the W-12.D F-SPLTAIL supply) survived a
full hostile re-derivation plus two fresh cells (first k = 3, first
odd-q k ≥ 2, 96/96 + 96/96 with teeth), the R1/R3/R4/R5 repairs and
both PE5 items verified clean, both machine legs reproduce isolated
(one bit-identical, one elapsed-only), and every pin/freeze holds.
The frozen body's ACCEPTED 2/2 is untouched. Owed for the next annex
round: a dated R2 correction — scope the N-even band-pinned
differing-pair claim to key-level (cross-stratum) witnesses, fix
GENH4-7'(a)'s realizability parenthetical to N ≥ 4k+1 (or to the
SPLTAIL-live range), and the three quantifier/display nits (MINOR
2–4). Report artifacts: `verification/openmath/genh4annexpass_fresh.py`
+ output/results (committed); isolated re-run sandbox in /tmp
(session-local).
