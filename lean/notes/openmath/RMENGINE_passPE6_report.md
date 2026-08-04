# RMENGINE-PE6 — round-6 hostile content verification (THE ACCEPTANCE ATTEMPT)

**Verifier:** Fable (fresh context), PE leg of round 6. **Object:**
`lean/notes/openmath/RMENGINE_2026-08-08.md` at cfb3648 (the r5 text;
HEAD confirmed = cfb3648 at pass start). **Bar:** this pass AND the
concurrent Codex PC6 both CLEAN (zero critical, zero gaps; notes do not
block). **Charge:** (1) r5-remedy discharge, hostile (supersession
brackets accurate + SUFFICIENT across every record surface; the as-of
annotation future-proof — the stale-quote recursion dead by
construction; the gloss fixes; the two standing rules coherent);
(2) machine legs (claims census re-run vs committed output at cfb3648;
`rmengine_pe2_ext.py` re-run; the r5 fence vs the actual
`git diff d63f8bb cfb3648`); (3) full spine sweep, re-derived from
scratch (headline/T-scope; L-NORM; tree + L-EXACT; L-GRID/L-ZMULT/
L-LINE; S4.1 both branches + necessity iff; S4.2 inspection census;
DEV-(m) + L-VNZ + the four RM-GEN clauses; S6 grades; COR-A; records);
(4) fresh eyes. I verify; I fix nothing.

Findings are classified CRITICAL / GAP / NOTE, quote-and-classify.

---
## 1. Machine legs (charge 2) — ALL GREEN

**M1 — claims census.** `python3 verification/openmath/rmengine_claims_census.py`
re-run at cfb3648: exit 0, output byte-identical to the committed
`rmengine_claims_census_output.txt` (itself last committed at cfb3648):
`67 keyword lines (55 row-tagged, 12 nc-tagged); 33 table rows (2
table-only); excluded zones: 15` + `CENSUS CLOSED — zero violations.`
Zone-count arithmetic independently verified: 15 = S8 + S11 + 3
ledger-quote blocks + 5 head brackets + 5 tail records. The script
re-read (real syntactic checker: keyword regex only/never/nothing/
-free/self-contained/automatic + LEX_SKIP, tag/row cross-reference,
unreferenced-row check, exit 1 on any violation).

**M2 — pe2 referee.** `rmengine_pe2_ext.py` (md5 574f87d8… unchanged)
re-run: exit 0, output BYTE-IDENTICAL to the committed
`rmengine_pe2_ext_output.txt` — all 12 verdict lines GREEN (V-BOX/V-MU/
V-CONS/V-LINE/V-ZH/V-ID/X-IVL/X-SCOPE/X-NEC/X-BRA/V-LAW/V-P0), 67 flat
engine calls, 0 violations.

**M3 — the r5 fence.** `git diff d63f8bb cfb3648 --
lean/notes/openmath/RMENGINE_2026-08-08.md` read hunk-by-hunk (134
lines). Every hunk lies on a record surface: the round-1 head bracket
(PC5-g1 supersession at "completed"), the round-3 head bracket (pre-S0
gloss + PE5-n), the NEW round-5 head bracket, the round-2 record row
PC2-g2=PE2-1 (supersession; "the complete PE2 census absentee list" →
"the PE2 census absentee list" with the removed word preserved inside
the bracket's quote), the round-3 record row PC3-g3 (supersession;
"all SIX" preserved in-bracket), the as-of annotation after the census
quote, the round-4 record's edited-surface list + zones 11 → 13
disclosure, the NEW round-5 record, and the tail acceptance-counter
lines. ZERO S0–S10 content lines; ZERO ⟦…⟧ tags added, moved, or
removed. The fence HOLDS.

**M4 (beyond charge, decorrelation) — diagnostic re-run.**
`rmengine_diag.py` re-executed in a /tmp sandbox (repo untouched):
exit 0, output IDENTICAL to the committed `rmengine_diag_output.txt`
modulo the disclosed volatile trailing elapsed float — all seven
verdict lines (D1–D7) reproduce verbatim. The three md5s quoted in the
S9 D7 ACTUALS match the committed artifacts exactly (runner
c50c08e3…, output d9118f5a…, results JSON 1ce263df…).

**M5 (beyond charge) — historical zone figures.** The census script is
byte-identical (md5 14ce04bc…) at ab2e471, d63f8bb, cfb3648. Run
against the extracted historical note texts: ab2e471 → zones 11
CLOSED; d63f8bb → zones 13 CLOSED; cfb3648 → zones 15 CLOSED, with
67/55/12/33 (2 table-only) FROZEN across all three. The as-of
annotation's every factual assertion ("the quote above is AS OF the r3
run", "the zone count … grows while every other figure is unchanged
and the verdict stays CLOSED", "r4 run, at d63f8bb: zones 13") is
machine-verified TRUE.

**M6 (beyond charge) — paste fidelity.** All three dagger blocks
([IL]† scope quote, [IL3]†, [ILN]†) compared content-token-wise
(whitespace-normalized) against `BRIDGE_ADJUDICATIONS_2026-07-30.md`:
all three IDENTICAL.

**M7 — object integrity.** HEAD = cfb3648; the note and the
verification directory are clean in the working tree (the only
untracked file is another unit's `wmultdcx_pe2_ext.py`).

## 2. R5-remedy discharge, hostile (charge 1) — DISCHARGED

**2.1 The three supersession brackets — accurate.** (i) Round-1 head
bracket: `"completed" was this round's claim; refuted at rounds 2–3
(rows C23–C33 followed)` — accurate (C23–C28 at r2, C29–C33 at r3).
(ii) Round-2 record: `"complete … list" was this round's claim;
refuted at round 3 by PE3's L-LEX witness — rows C29–C33 followed` —
accurate; and the bracket's quote matches the actual r2-era wording (I
extracted 423b399: the r2 charter bracket read "whose complete
in-scope absentee list is exactly C23–C27, plus the repair-record
claim C28" — the S8 history paragraph's verbatim quote of it is also
exact). (iii) Round-3 record: `this cell's "all SIX" was itself
refuted at round 4 (PE4-G-1, change 7)` — accurate (verified against
the r4 diff record and the change-(7) enumeration).

**2.2 Sufficiency sweep — no fourth cell.** Full-file grep for
completeness-flavored language (complet-/exhaustiv-/all SIX/all
SEVEN/entire/exactly) with per-hit adjudication across EVERY record
surface (5 head brackets, 5 tail records, the S8 charter paragraph +
C28 row, S11): every completeness-genre assertion is either (a)
superseded in place with a dated bracket (the three PC5-g1 cells; the
r3 "SIX changes" at C28 and the round-1 record, both bracketed at r4),
(b) a quotation of a refuted claim WITH its refutation attached (the
S8 history paragraph; the r4 head bracket), or (c) not a completeness
claim (the round-2/3 head brackets' finding lists are per-round
dispositions matching their round's findings 1:1; C28's claim column
now carries an explicit "no completeness claim"). No un-superseded
refuted record cell survives.

**2.3 The as-of annotation — future-proof; the recursion is dead by
construction.** Sweep for machine-figure quotes that could speak for
HEAD: the ONLY census-figure quotes in the note are (a) the round-3
quote, now pinned AS-OF ab2e471; (b) the annotation's own "r4 run, at
d63f8bb: zones 13" — commit-pinned inline; (c) the round-4 record's
"zones 11 → 13" — round-pinned, with the commit displayed in the
adjacent annotation (see NOTE N-1). Everything else says only
"CLOSED"/"re-committed" with NO figures (in particular the round-5
bracket and record deliberately quote no figures and point to the
committed output file as the sole speaker for the current text). A
future repair round that grows the zone count can stale NOTHING: no
unpinned figure exists, and the arbiter clause ("that file, not any
quote in this note") covers all future re-runs. The S9 diagnostic
figures are pinned by md5 to committed artifacts that repair rounds do
not touch (verified M4). Recursion dead.

**2.4 The gloss fixes.** (i) The round-3 bracket now names the pre-S0
head-matter tags — verified TRUE against the body (the head
declaration block carries ⟦C15⟧/⟦C12⟧ tags; S8/S11 excluded, correctly
not named). (ii) The r4 edited-surface list now names the tail
acceptance-counter lines — verified against the actual r4 diff genre
(the tail counter paragraph was indeed rewritten at r4).

**2.5 The two standing rules — coherent.** Supersede-at-refutation
(head-bracket and record formulations agree: dated bracket in the SAME
repair) and as-of machine quotes (three formulations — head bracket,
PE5-G-1 row, the r5 rule paragraph — are consistent: quotes carry
their as-of commit; re-runs changing a figure trigger re-quoting; only
the committed output file speaks for the current text). The r5 round
itself complies with both rules (its own record quotes no figures; its
three supersessions are dated and in-place).

## 3. Spine sweep (charge 3) — re-derived from scratch, CLEAN

**Headline/T-scope.** T-scope(1) = d₀=1 ∨ e₀≥2 = (e₀≥2) ∪ (e₀=1 ∧
d₀=1) — the RM-1 scope reproduction claim is exact. T-scope₀ ⊂ T-scope
(strict at d₀=1 with a flat level) — the strengthening claim is exact.
Complement = d₀≥2 ∧ (e₀=1 ∨ ∃ flat) — the fence locus is the exact
complement (C33 verified).

**L-NORM.** Re-derived: primitive-part factorization exists (Gauss
valuation), DIGIT-SPLIT applies to b̂ĉ, restoring π^w is exact;
(a) L-child w₀ exactly w with residue b̄c̄ ≠ 0 (nonzero primitives
reduce to nonzero elements of the FIELD K₀, degree < deg ψ̄₀ — C18
verified); (b) π-child ≥ w+1; (c) Y-child ≥ w at j₀+1, and Ŷ ≡ 0 at
d₀=1 (deg b̂ĉ ≤ 2d₀−2 = 0 < d₀). All correct.

**Tree + L-EXACT.** The E1-priority inventory conserves exactness
stepwise per (ID-(i+1)); R-leaves reduced ⟹ deg R₀ < deg Φ_m
(telescope Σ(P_l−1)deg Φ_l = deg Φ_m − d₀ re-computed); L-CANON forces
the canonical division (uniqueness of division by a monic;
deg(fĈ_m) < 2 deg Φ_m gives deg Q < deg Φ_m — C2's recorded
hypotheses all consumed, none missing). The structural remark
re-derived: at an exit the priority pins j_l ≤ P_l−1 for l ≤ m−2, S is
reduced at level m−1, and w_m(S·Φ_{m−1}^{j′}) = e_{m−1}w_{m−1}(S) +
j′γ_m holds for ANY j′ ≥ 0 (w_m a valuation, w_mΦ_{m−1} = γ_m) — the
window-free (C-W_Q) route is sound (C4/C5 verified).

**L-GRID / L-ZMULT / L-LINE.** L-GRID: λ_l = the level-l truncation
line (affine recursion re-computed: λ_l = e_{l−1}λ_{l−1} + j_{l−1}γ_l);
t_l ∈ ℤ from s_l(λ_l) ≡ ℓ_{l−1}λ_l ≡ ℓ_{l−1}j_{l−1}h_{l−1} ≡ j_{l−1}
(mod e_{l−1}) — both congruence inputs are the S0.1 pins (C30/C31
verified). L-ZMULT: λ-chains add (linearity, no floors — C6); t_l^Σ =
t_l + t_l′ + δ_l with δ_l ∈ {0,1} (s-values < e); the t-leg z^{+δ}
cancels EXP-KIT(b)'s ε-leg z^{−δ} at l = 1…m−1; level m has a t-leg
and no ε-leg, so exactly z_m^{δ_m} survives — re-derived in full, the
carry-cancellation is exact. L-LINE: (i) Γ_{i+1} − P_iΓ_i =
h_{i+1}∏_{i+1<t<m}e_t > 0 (re-computed from γ_{i+2} = e_{i+1}w_{i+1}
Φ_{i+1} + h_{i+1}, w_{i+1}Φ_{i+1} = P_iγ_{i+1}); exit drop = w_mΦ_m;
(ii) Δline = 0 via the level-i on-line identity scaled by
∏_{i≤t<m}e_t (all three conversion identities re-computed exactly);
(iii) π-child ≥ +E_m, Y-child ≥ +Γ₀; i = 0 case Δline = 0 re-computed
(Γ₀ = h₀E_m/e₀). L-MONO + the depth-0 skeleton (C24): correct —
promotions/junk strictly raise the line, lines never fall, so on-line
cells at the initial-floor target never crossed either edge type.

**S4.1 both branches + necessity iff.** Branch (a) re-derived: interval
(S_i/e_i, w_{i−1}P_{i−1}) nonempty given (B_{i−1}) + e_i ≥ 2 + ρ_{i−1}
≤ P_{i−1}; base (ρ₀/e₁, P₀) nonempty. Branch (b) re-derived: at d₀=1,
ρ₀ = P₀−1; the uniform interval (S_i, w_{i−1}P_{i−1}) is nonempty iff
w_{i−1} > S_{i−1} (exact rearrangement, since ρ_{i−1} = P_{i−1}−1),
the invariant self-propagates, base (P₀−1, P₀) ≠ ∅; no e_i lower
bound consumed; (B_i) from w_ie_i ≥ w_i > S_i. Edge descents: promotion
(A), exit, correction i ≥ 1 (mass e_i(g_i−k) ≥ e_i consumed vs ≤ ρ_l
dumped — (B)), correction i = 0 (Δj₀ ≤ −e₀ + [d₀≥2]) — the combined
scope is EXACTLY the amended T-scope. Necessity: the cascade
w_{l−1}P_{l−1} > S_l ⟹ w_{l−1} > S_{l−1} re-derived (uses ρ_{l−1} =
P_{l−1}−1 for l−1 ≥ 1), bottoms at ρ₀ < P₀ ⟺ d₀ = 1 — the iff is
sound, and the machine leg (X-NEC: d₀≥2-flat infeasibility) re-ran
green. Well-foundedness: common-denominator rationals. The m = 2
consistency point re-checked: (A₁) ⟺ e₁ ≥ 2 exact; the point satisfies
(B₁) for all e₁ ≥ 1 at d₀ = 1 and iff e₁ ≥ 2 at d₀ ≥ 2, so membership
in the family ⟺ e₁ ≥ 2 in all cases — the display's operative claims
TRUE (see NOTE N-2 on the (B₁) ⟺-chain's majorization step).

**S4.2 inspection census.** Per-leg re-check: S2.1/S2.2 formulas
e ≥ 1-safe (division + valuation arithmetic; consumed mass e_i(g_i−k));
S3.1 congruences trivialize at e = 1 (s ≡ 0, δ = 0, t = j); S3.2
quanta need h ≥ 1 only; S5 carriers are class-level ([ILN]† pins
gcd(e,h) = 1 only). Confirmed: L-MU is the sole e ≥ 2 consumer (C23),
so DEV-(m)/RM-GEN ride T-TERM's amended scope. Machine shadow re-ran
(M2: 67 flat calls green).

**DEV-(m) + L-VNZ + the four RM-GEN clauses.** DEV-(m): induction on μ
re-walked; (D1) L-EXACT; (D2) leaf w = line + sums ≥ min + exit
cofactors exact-weight (the structural remark); (D3) three cases —
above-line 0; off-grid EMPTY (L-GRID); the two telescopes re-computed
IN FULL: T-tele(1) collapses via Σ_k ψ̄₀,k z₁^k = ψ̄₀(z₁) − z₁^{g₀} and
ψ̄₀(z₁) = 0 with the sign discipline of (ID-1) (re-checked: the − sign
against −z₁^{g₀} yields +); T-tele(i+1): t_{i+1} shift = k − g_i and
λ_i rise = β_k re-computed from linearity; B-READ-on-C_k^{(i)}
assembly (finite-sum interchange legitimate; realize (R3) gives τ_k);
EPS-MULT ε_i(λ_i+β_k)z_i^{ε̃_k} = ε_i(λ_i)ε_i(β_k) is EXP-KIT(b)
rearranged (re-checked); ε_i(β_k)τ_k = ψ_{i,k}; the k-sum collapses by
ψ_i(z_{i+1}) = 0. L-VNZ: induction re-derived — the slot range
t ≤ g_{m−1}−1 from j ≤ P_{m−1}−1 and 0 ≤ s_m(λ) < e_{m−1}; a
min-achieving digit is automatically on-grid (the L-GRID congruence)
with slot weight = w_{m−1}(f_j); distinct j ⟹ distinct z_m-powers (no
cross-cancellation); a nonzero K_{m−1}-polynomial of degree <
[K_m:K_{m−1}] is nonzero in K_m. Sound (C19). RM-GEN: (C-W_R) from
(D2) + development additivity; (C-W_Q) window-free via the exit
remark; (C-EPS) = L1; (C-READ): junk/above-line vanish, the surviving
(on-line x-cell)×(D-cell) L-children read via (D3) + L-ZMULT with the
UNIFORM carry ε̃ = ε′ (shared target pair — re-checked), and the
double sum factors into z_m^{ε′}·v·τ_m by B-READ on both factors. All
four clauses close on T-scope(m). The m = 1 scope agreement re-checked.

**S6 grades.** L-CAP re-computed: pool₁ ≤ 3e₀−3 ⟹ c₁ ≤ 2; pool_l ≤
3e_{l−1}−1 ⟹ c_l ≤ 2; flat levels pass the carry through (c = c_{l−1}
≤ 2). Both specializations re-computed EXACTLY: m = 1 → [IL3]†'s
S₁+s(γ₂) ≥ 2e₀ on TRACK (c₀ = 0, u₁ = γ₂); m = 2 → the v2 law
verbatim (u₁ = (γ₃ − s₂(γ₃)γ₂)/e₁ = the DCX3 note's u₀). The honesty
split (m=1 PROVED / m=2 sealed-conjecture / m≥3 first-data) intact; the
crossing-law-vs-pool-identification split (11b/11c) intact; no proof
step consumes the law (C12 verified at both use sites).

**COR-A.** The union computation re-derived: ∧_{m=2}^{n−1}[d₀=1 ∨
(e₀≥2 ∧ e_{≤m−1}≥2)] = d₀=1 ∨ (e₀≥2 ∧ e_{≤n−2}≥2) = T-class(n)
(nested branches); n = 1,2 empty call family, no T-condition —
correct; the at-acceptance rider present; e_{n−1} correctly absent
from T-class(n) (the level-(n−1) engine consumes reads 0..n−2 — C13).

**Records.** The claim DAG's arrows checked against the proofs (no
missing consumption; L-VNZ and L-LEX correctly marked consumed-by-no-
theorem-clause). The acceptance-counter narrative accurate (PC4 CLEAN
at ab2e471; rounds 5's findings record-ripple only; round 6 = the
attempt). All 12 ⟦nc⟧ sites spot-challenged (upstream-claim narration,
arithmetic narration, display/status rhetoric): all survive.

## 4. Fresh eyes (charge 4)

Nothing critical and nothing gap-grade found beyond the eight prior
passes. Additional verifications performed that no prior pass had on
record: the historical zone-figure verification at three commits (M5),
the /tmp diagnostic re-execution (M4), and the three-way paste-fidelity
token comparison (M6) — all green.

## FINDINGS

**CRITICAL: none.**

**GAPS: none.**

**NOTES (non-blocking, no cure required):**

* **N-1 (record, as-of granularity).** The round-4 record's census
  figure quote — "the census re-run CLOSED after the edit (output
  re-committed; zones 11 → 13 …)" — is round-pinned but does not carry
  its as-of commit INLINE; the commit for the 13-figure (d63f8bb) is
  displayed one paragraph up, inside the PE5-G-1 annotation. Substance
  of the standing rule met (the figure cannot be read as a HEAD
  figure; machine-verified true at M5); a strict inline reading of
  "quotes carry their as-of commit" would add "(at d63f8bb)" in the
  cell. Not a gap: no future re-run can make this quote speak falsely
  for HEAD.

* **N-2 (display arithmetic, S4.1 consistency display).** In "(B₁):
  P₀e₁(e₁+1) > 2e₁ρ₀ (ρ₀ ≤ P₀) ⟺ e₁+1 > 2", the first ⟺ is exact
  only after the parenthesized majorization ρ₀ → P₀ (i.e., at d₀ ≥ 2);
  at d₀ = 1 the un-majorized (B₁) holds for every e₁ ≥ 1 while the
  point still exits the family at e₁ = 1 through (A₁). Every operative
  claim of the display is TRUE (re-computed: the point lies in the
  (a)-branch family ⟺ e₁ ≥ 2, in all cases), and the display is
  consumed by nothing (a consistency display). Wording-level only.

## VERDICT BLOCK

Machine legs: census reproduces CLOSED byte-identical at cfb3648; pe2
referee byte-identical all-GREEN; the r5 fence HOLDS (record surfaces
only, zero tags moved); diagnostic re-executes identically; historical
figures machine-verified; pastes token-identical. R5 remedies:
DISCHARGED (brackets accurate and sufficient; the as-of recursion dead
by construction; glosses true; rules coherent). Spine: re-derived from
scratch, zero mathematical findings — the NINTH consecutive 0-critical
pass. Two non-blocking notes.

RMENGINE-PE6 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
