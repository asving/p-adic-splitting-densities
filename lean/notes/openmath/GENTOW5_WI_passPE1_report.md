# GENTOW5-W(i) passPE1 — hostile verification report

Target: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md` at HEAD (note
state = ec30256c chain; commits 07fa3676 → 4c959409 → ec30256c).
Claim under test: [GENTOW5-W(i)] u_i(β_t) = ϑ_i(t)·w_i^{f_{i+1}−t}
PROVED at levels i ≥ 3, by GENTOW2-B″'s four-step computation run at
level i with the ẑ grade-0 lift eliminated. Sources read at their
pinned commits: GENTOW5_PROOF @ b0e5c648, GENTOW2_PROOF @ 33f86204.
AS-OF state read: T1/WFRAME/WI parallel 0/2 arcs; this note consumes
neither T1 nor WFRAME (WFRAME cited as geography only — declared in
S4/S7 and confirmed by grep).

## VERDICT: CLEAN — nothing at GAP-or-worse survives verification.
Four MINOR findings below. The machine leg re-verified bit-identical;
the fresh leg produced an i = 4 letter-live contact (one level above
LW3, the first i = 4 geometry on the record) and the [GENTOW5-W(4)]
display held on the nose, 15 checks / 0 violations, dual exact
oracles bit-equal.

---

## SURFACE 1 — THE PROOF, re-derived step by step at level i

*(0) Exact grades.* Verified. Additionally re-proved (my own leg,
not in the note): deg n̂_i(m) < D_i holds by the telescoping bound
(e_1−1) + Σ_j (e_{j+1}−1)D_j ≤ D_i − 1, from the unrolled recursion's
exponent bounds i0 < e_1, b_j < e_{j+1} (DEF GENTOW5-1 @ b0e5c648
L387–398, read at source). μ_{i+1}(G) = d·κ̄_i = β_t is exact
arithmetic (β_t = u_{i+1}d/e(μ_i) = d·κ̄_i).

*(i) Peel.* Verified against the i = 2 original (B″ proof @ 33f86204
L740–778). The ẑ-drop is algebraically sound: the i = 2 equate was
ϑ·w^d = u(β_t)·1 (digit arranged to 1 via ẑ); here w^d =
u_i(β_t)·ϑ_i(t)^{−1} (digit ϑ^{−1} carried) — the same identity.
R_{i+1,κ̄}(N) = w_i is definitional (u_i-family display, β̂ = u_{i+1}
at β = κ̄). Cor 4.7(2) iteration matches the i = 2 precedent's
no-degree-hypothesis use (justified explicitly in B′'s proof text).

*(iii) The j ≥ 1 kill is level-uniform* — the charge's specific
worry checked and cleared: the dichotomy consumes gcd(h_{i+1},
e_{i+1}) = 1 (e_{i+1} is BY DEFINITION the denominator of λ_{i+1}
over Γ_i), the group structure of Γ_i, Prop 1.9(2) at deg Q_j < D_i
(level-general, S6.1 row 22 MATCH re-read), and eq (14)'s y-degree
j/e_{i+1} (row 9). The e_{i+1} = 1 branch is covered explicitly. No
i = 2-specific arithmetic found in the step.

*(iv) Digit read.* Verified: β̂_t = e(μ_i)β_t = u_{i+1}d so
n̂_i(β̂_t) = M and digit_i(Q_0) = res((N^d/M)(x0)) = ϑ_i(t)^{−1} by
the ϑ definition (inverse read of the same monomial quotient — the
S2.1 reciprocity @ b0e5c648 L938–940, on S11.2's proved list).
Evaluation legitimacy: clause (b) of GENTOW5-B at index i−1
(@ L821–833) — its exact-value + P-membership clause sits on the
S11.2 fence's NOT-conditional list ("the repo-side residue classes
and P-membership clauses ... w-blind there", read at source), so the
consumption is not circular. The exact-height→exact-value conversion
is GENTOW5-C's value clause consumed at the accepted (B-1 at level i)
adjudication of GENTOW5-B's own proof. The u_i-family factorization
is applied at one g (= Q_0: Φ_i-free, deg < D_i, exact grade) —
within the (B-2) leg's stated scope.

*Equate + corner.* w^d = u·ϑ^{−1} ⟺ the fenced display; the d = 1
corner tautologizes as disclosed.

*Circularity walk (S3 leg (c)).* Re-walked item by item: C-2/C-3/C-4
on S11.2's proved side (L1904–1908 quote verified at source);
C-5 w-blind; C-6..C-8 accepted/source-level-general. No consumed item
found behind [GENTOW5-W(i)] itself.

## SURFACE 2 — FOOTPRINT (Thm 4.8 / T(b)′(iii) out)

Verified DIRECTLY: the note's mentions of Thm 4.8/T(b)′(iii) are at
lines 24–25, 120, 228 — each a disclaimer site; S2 consumes neither.
Cross-checked transitively: GENTOW2-B′'s i = 2 proof DOES consume
Thm 4.8 at its grade-0 step (@ 33f86204, "R_{3,0}(ẑ_d) = d ... Thm
4.8"), but the i ≥ 3 (B-2) leg's derivation is credited by the fence
to (SLOT_i) + the S2.3 cocycle computation, and GENTOW5-C's proof
consumes four clauses (SLOT induction, P-membership, gcd, basis) —
Thm 4.8 is not among them (@ b0e5c648 L580–588 read at source). The
elimination claim survives; see MINOR-2 for its exact resting point.

## SURFACE 3 — BYTE-MATCH

`cat -A` comparison of note L79–80 vs fence L1912–1913 @ b0e5c648:
the equation bodies are byte-identical; differences are the fence's
`[GENTOW5-W(i)]` label, leading indentation, and the terminal `,`
vs `.` on the second line. See MINOR-1.

## SURFACE 4 — WITNESSES + LW3 HAND-DERIVATION

Committed values confirmed at their sources: (8,20,42,85) and
(16,40,84,170,341) at GENTOW5_PROOF L1185–1186/S4.3;
(32,80,168,340,682,1365) in the pe3 fresh artifacts (DLAD row). The
LW3 frame's hand arithmetic re-derived independently by this
verifier: n̂_3(43) = 3xΦ_1Φ_2 (b-chain 1,1; a=1,i0=1), n̂_3(86) =
3⁹xΦ_1 (b-chain 1,0; a=9,i0=1), M/N² = 3⁷/(xΦ_1Φ_2²) =
γ_1^{−1}γ_2^{−1}γ_3^{−1}, letters (2,2,2) from the key digits,
ϑ_3(0) = 8^{−1} = 2 in F_3^× — matching the note at each value.
Ledger row C-1 md5-8 `d4c8b885` matches `statement_ledger_baseline
.json`; row 23 (avatar) confirmed DESCRIPTIVE at GENTOW2 L1339–1342.

## MACHINE LEG

- md5 seals: instrument c8c5d129, run-2 artifact b0a8c3c4, run-1 RED
  598d6704 — each matches the note's S6/S7.
- Seal chain: 07fa3676 (instrument sealed UNRUN, predictions +
  teeth in docstring) → 4c959409 (run-1 RED KEPT + dated repair,
  run-2 prereg with [probe] provenance disclosed) → ec30256c
  (verdict). Order and contents verified via git.
- Isolated re-run (fresh copy in /tmp, this session): 60 checks /
  0 violations, exit 0, output BIT-IDENTICAL to the committed
  artifact (md5 b0a8c3c4).
- Run-1 RED artifact: 58/5 with the 5 violations exactly the rows
  the diagnosis names (P-D1 ladder print, P-D3 LAW-1/LAW-3, P-D4,
  P-D6) — gp-parse + avatar-key side; the 34 exact-integer rows
  green in run 1, matching the note's account.
- `statement_ledger.py --check`: GREEN (166 baseline; 0 changed,
  0 deleted, 0 added).
- Tautology audit: predictions are hard-coded expected values, not
  read-backs; the kit is self-contained (own Bareiss resultants, own
  nhat solver, own lattice split). Residual weaknesses → MINOR-3.

## FRESH LEG — the i = 4 LIVE contact (first anywhere)

Verifier-constructed frame FR4 (no committed source): p = 3, stages
(2,1)×4 + (1,2), u = (1,5,21,85,171) (floors 5>4, 21>20, 85>84,
171>170), keys Φ_1 = x²−6, Φ_2 = Φ_1²−18x, Φ_3 = Φ_2²−162Φ_1,
Φ_4 = Φ_3²−3⁸Φ_2 (stage-4 digit 1 ⇒ letters (2,2,2,1)), hand-solved
n̂_4(171) = 3xΦ_1Φ_2Φ_3, n̂_4(342) = 3¹⁷xΦ_1Φ_2, lattice split
(−1,−1,−1,−1) ⇒ ϑ_4(0) = (2·2·2·1)^{−1} = 2 LETTER-LIVE at i = 4;
Φ_5 = Φ_4² − n̂_4(171)Φ_4 − 2·n̂_4(342), deg 32. Preregistered in
the runner docstring before its run. Result 15/0
(`verification/openmath/gentow5_wi_pe1_fresh_i4.py` md5 02d14bdd,
output 8316f0c5): factorpadic ONE deg-32 factor, single prime
(e,f) = (16,2), nfeltval ladder (8,20,42,85,171) exact, letters
(2,2,2,1) at the prime, T0 = ϑ_4(0) = 2 measured live, Y generates
F_9, measured w_4 = tr(Y) = 1, norm(Y) = 2 = ϑ_4(0)·w_4², and
ψ_5^{(w_4)}(Y) = 0 — the [GENTOW5-W(4)] display at both slots; teeth
fired (other-unit twist nonzero; norm ≠ tr², ϑ-free law dead at
i = 4). Exact ladder v_3(Res(Φ_5,g)) = (16,40,84,170,342) by DUAL
oracles: my own subresultant-PRS integers bit-equal to gp
polresultant integers (a different algorithm from the instrument's
Bareiss — three implementations now agree on this family). Note the
last rung 342 = 2·171 ≠ 340: the frame is NOT a doubling chain at
the top, so the contact is not a disguised F-A reproduction.

---

## FINDINGS (quote-and-classify; nothing fixed)

**MINOR-1 (byte-match wording).** S1: "This is the fenced display
byte-for-byte". True of the equation bodies; the second line ends
`.` where the fence has `,`, and the label/indent differ. Failure
scenario: a later pass diffing whole lines flags a mismatch and
burns a round re-adjudicating. The parenthetical "(ASCII form)"
already hedges; a one-word "modulo label/punctuation" would close it.

**MINOR-2 (footprint resting point).** S1/S3-C-9: "the two B″-proof
inputs with NO accepted level-i analogue [are] out of the footprint
by construction." Verified for this note's own steps; but the
consumed C-2 leg's i = 2 ancestor (B′(3)) consumes Thm 4.8 in its
proof, so the elimination ultimately rests on the fence's S11.2
proved-list adjudication that the i ≥ 3 leg derives via
(SLOT_i)/cocycle instead — an accepted-record dependence the note
discloses ("at the fence's own adjudication ... adds no strength"),
not a hidden consumption. Failure scenario avoided; recorded so the
acceptance pass knows the exact resting point.

**MINOR-3 (tooth independence at LW3).** Given YGEN + LAW-I1 +
WSTAR, the rows LAW-I2, P-D4′, and P-D5 are mutually implied
(minpoly uniqueness in F_9): the intrinsic LW3 law contact reduces
to ONE substantive F_3 equation, norm(Y) = 2·tr(Y)², plus the
independent kills (P-B2 drains; P-D7′ naive-twin (e,f) = (16,1)).
Also P-A3's reciprocity row (ϑ·ϑ^{−1} = 1) cannot fail in F_3^×
(exponent-2 group). Failure scenario: a reader counts "60 checks"
as 60 independent contacts. The note's own coverage box (S7 item 4)
already discloses the K_3 = F_3 thinness; my i = 4 leg widens the
record at the same alphabet.

**MINOR-4 (probe provenance).** Run-2 rows marked [probe] were
observed once in the post-RED diagnosis probe before the run-2
seal — disclosed in the docstring and in S6, so run 2 is a
reproduction test, not a blind prediction, for those rows. Honest
as labeled; recorded for the arc.

## GRADE LINE

passPE1 verdict: **CLEAN** (0 CRITICAL, 0 GAP, 4 MINOR). The
CLEAN bar (nothing at GAP-or-worse) is met. Note grade advances
0/2 → 1/2 pending the second hostile pass. The fresh i = 4
letter-live contact (FR4, 15/0, dual oracles) is new record the
second pass can reuse as a committed battery row.
