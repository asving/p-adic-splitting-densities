# RMENGINE pass PE7 report (Fable, round 7 — THE ACCEPTANCE ATTEMPT) — 2026-08-04

Object: `lean/notes/openmath/RMENGINE_2026-08-08.md` at a0e266c (the r6 text;
confirmed HEAD and last-touching commit). Charge: hostile content verification,
quote-and-classify (CRITICAL / GAP / NOTE), fix nothing. Bar: this pass AND the
concurrent PC7 both CLEAN.

Legs: (1) r6-remedy discharge; (2) the record layer, closing sweep; (3) machine
legs (census re-run vs committed output at a0e266c; pe2 referee re-run; r6 fence
diff); (4) full standalone spine re-derivation; (5) fresh eyes.

Findings are numbered PE7-* as they are established; the verdict block closes
the report.

---
## 1. Machine legs (charge 3) — ALL GREEN

**M1 — object integrity.** HEAD = a0e266c; the note's working-tree bytes match
`a0e266c:lean/notes/openmath/RMENGINE_2026-08-08.md` exactly (git show | diff:
identical). a0e266c is the last commit touching the note (r6).

**M2 — claims census.** `python3 verification/openmath/rmengine_claims_census.py`
re-run at a0e266c: exit 0, output BYTE-IDENTICAL to the committed
`rmengine_claims_census_output.txt` at a0e266c: `67 keyword lines (55 row-tagged,
12 nc-tagged); 33 table rows (2 table-only); excluded zones: 17` +
`CENSUS CLOSED — zero violations.` Zone arithmetic independently verified:
17 = S8 + S11 + 3 ledger blocks + 6 head brackets + 6 tail records (r6 added
exactly 2: the round-6 head bracket + the round-6 tail record; 15 → 17).
Script re-read: real syntactic checker (keyword regex + LEX_SKIP, tag/row
cross-reference both directions, exit 1 on any violation) — not vacuous.

**M3 — pe2 referee.** `rmengine_pe2_ext.py` (md5 574f87d8… unchanged) re-run:
exit 0, output BYTE-IDENTICAL to the committed `rmengine_pe2_ext_output.txt`
(diff exit 0) — all 12 XV verdict lines GREEN, 67 flat engine calls on 8 fresh
d₀ = 1 towers, 1080-shape branch-(b) sweep 0 failures, 225 d₀ ≥ 2-flat
infeasibility probes 0 feasible, v = 0 realized 0/67.

**M4 — the r6 fence.** `git diff cfb3648 a0e266c -- <note>` read hunk-by-hunk:
six hunks, ALL record surfaces — (1) the new round-6 head bracket; (2) the
round-4 record's "zones 11 → 13 as of d63f8bb" inline as-of (PE6-N-1); (3) the
PE5-G-1 disposition cell (rule site 1 + the "HEAD figure" wording replaced by
the commit-pinned form); (4) the r5 standing-rule sentence (rule site 2);
(5) the new round-6 tail record; (6) the tail acceptance-counter block. No
S0–S10 content, no tags moved. Deeper: the FULL `git diff ab2e471 a0e266c`
(r3 → r6) touches only head brackets, tail records, and ONE S8 row — the C28
rewrite documented as the r4 repair. The fence HOLDS at every advertised depth.

**M5 — historical zone figures + md5s (record-figure verification).**
Committed census output per commit: ab2e471 → zones 11; d63f8bb → 13;
cfb3648 → 15; a0e266c → 17 (all other figures frozen, verdict CLOSED at each) —
every zone figure quoted in the note is correct AND as-of-pinned. The three
md5s in the S9 D7 ACTUALS match the committed artifacts exactly (runner
c50c08e3…, output d9118f5a…, results 1ce263df…). The r2-bracket PE2 figures
(67 calls / 8 towers / 1080 / 225) match the fresh M3 re-run; the L-NORM
convention paragraph's 97/97 and L-VNZ's 0/97 match the committed
`rmengine_pe_reimpl_output.txt` (`engine_calls=97`, `v_zero_inputs=0`), and
"DIGIT-SPLIT, pi-normalized" is verbatim in the committed reimpl runner.

**M6 — row keys at HEAD.** `rmengine_pe4_ext.py` re-run: 43/44 keys match;
the single FAIL is the referee's own hardcoded round-4-era C28 key ("The
complete r1 statement-change census") — stale BY DESIGN, since the r4 repair
that this very referee's finding (PE4-G-1) mandated rewrote the key to "The
r1 statement-change census". The CURRENT C28 key matches the round-1 record
sentence exactly (verified by direct grep). Referee staleness, not a note
defect; the note claims PE4's legs green AT round 4 (on ab2e471, where the
old key matched — verified in the ab2e471 blob), never that this referee
re-runs green at HEAD. NON-FINDING, recorded for the file.

## 2. R6-remedy discharge (charge 1) — DISCHARGED

**The unification.** Grep of the full note for the second rule: every
surviving "re-quoted" hit is either (a) the unrelated, historical grep-KEY
re-quoting sense (lines 66, 1151, 1445 — actions taken at r3, accurately
described), or (b) INSIDE the r6 supersession brackets quoting the refuted
rule (lines 130, 1513, 1521, 1540). Zero live assertions of the re-quotation
rule remain. The "HEAD figure" wording PC6 quoted is gone (replaced by
"the r4-run figure displayed commit-pinned (zones 13 at d63f8bb)" — figure
verified true at d63f8bb). The note now asserts exactly one machine-quote
rule — as-of commit + committed-file-arbiter — at both former second-rule
sites and in the round-5 head bracket, and it satisfies that rule at every
machine-figure site (M5).

**Bracket accuracy.** The [r6, PC6-g1] brackets quote the superseded endings
verbatim ("…are re-quoted whenever a re-run changes any figure"; "re-runs
that change any figure are re-quoted") — checked against the actual cfb3648
blob via the M4 diff: both quotes exact. The PE6-N-1 inline as-of ("as of
d63f8bb") is the cure PE6's N-1 asked for, figure verified.

**Round-6 records vs the archived reports.** PC6 (0182e1b, archived
commit verified to exist and contain the report): FINDINGS 0 critical /
1 gap, GAPS-ONLY, the gap = the two-rules inconsistency + the HEAD-term
zone figure — the note's characterization ("the r5 records asserted TWO
machine-quote rules … while the note satisfies only the first") is accurate.
PE6 (`RMENGINE_passPE6_report.md`): FINDINGS 0 critical / 0 gaps, CLEAN,
2 notes = N-1 (as-of placement — cured at r6) and N-2 (the (B₁) ⟺-chain
majorization reading — left standing as a note, correctly, with "all
operative claims verified true" matching PE6's own words); the head
bracket's machine-leg list (census byte-identical, referee + diag re-runs,
r5 fence, historical zone figures, dagger pastes content-token identical,
spine re-derived) matches PE6 §M1–M7 item for item. One compression noted
(PE7-N-3 below).

## 3. The record layer, closing sweep (charge 2)

Systematic pass over all six head brackets, all six tail records, and both
S8 tables:

**(a) Un-superseded refuted claims: CLASS CONFIRMED DEAD.** The three
PC5-g1 supersession brackets stand at the three refuted complete-enumeration
sites (r1 bracket "completed"; r2 record "complete … absentee list"; r3
record "all SIX"); C28 carries the r4 withdrawal; the two r6 rule
supersessions are in place. A fresh sweep for completeness-genre assertions
("complete", "all …", "exactly", "only statement changes") in record
surfaces found no further un-superseded instance: the round-1 record's
seven-change enumeration explicitly disclaims completeness ("THE DIFF ITSELF
IS THE AUTHORITATIVE SURFACE"), and the standing-lesson paragraph makes it
policy. The one stale-at-HEAD status line found is the COMPOSITION header
(PE7-N-1 below) — a different class (aged at-composition gloss, never
refuted by any finding), non-blocking.

**(b) HEAD-speaking machine figures without as-of: NONE.** Every machine
figure in a record surface now carries a commit pin or a round pin whose
commit is named in the same sentence (M5 verified each figure true at its
pinned commit). The only committed-output quote (the r3 census block) is
bracketed AS-OF ab2e471 immediately below, with the file-arbiter rule
displayed. The S9 ACTUALS blocks are run-event-pinned with md5s that match
the committed artifacts (M5).

**(c) Internal contradictions: NONE FOUND.** All twelve archived pass
verdict lines re-read from the report files match every record mention
(PC 1C/4G · PE 1C/2G/3n · PC2 0C/2G · PE2 0C/1G+2n · PC3 0C/3G · PE3
0C/3G+2n · PC4 CLEAN+2n · PE4 0C/1G+1n · PC5 0C/1G+1n · PE5 0C/1G+4n ·
PC6 0C/1G · PE6 CLEAN+2n). The consecutive-0-critical count (4th/6th/8th/9th)
is arithmetically consistent across brackets. The acceptance-counter tail
("both legs CLEAN on the stable text, never in the same round; round 7 =
the attempt, bar BOTH CLEAN") is consistent with the r4/r6 brackets and
with the facts. Every commit hash cited in the records (2b29712, 363a051,
bf18bfe, 8835d20, 423b399, ab2e471, d63f8bb, cfb3648, 9466efe, 998e599,
0182e1b, 0b42885, d860a5a, a9dd275, 13b026b, 5fe901e, 9f9910c, ced7dbb,
03635d0) exists in this repo. PC2's execution-less basis (bubblewrap,
report item 7) is quoted accurately. PC-C1 = PE-F2 and PC-G4 = PE-n5
identifications consistent between the r1 bracket and the round-1 table.

## 4. Spine sweep (charge 4) — re-derived standalone, ZERO mathematical findings

Each leg re-derived from the note's displays alone (consumed upstream facts
taken at their stated grades), independently of all prior reports:

**S-1 Headline/T-scope.** T-scope(m) = d₀=1 ∨ (e₀≥2 ∧ e_i≥2, 1≤i≤m−1). At
m=1 the e_i-clause is vacuous: d₀=1 ∨ e₀≥2 ≡ e₀≥2 ∨ (e₀=1 ∧ d₀=1) — the
(RM-1) scope on the nose, and equals T-scope₀(1). Complement = d₀≥2 ∧
(e₀=1 ∨ ∃ flat) — matches the headline OFF-clause, the S4.2 fence box, C33,
and scope remark (iv), all four sites. Title gloss names both branches. ✓

**S-2 L-CANON.** Uniqueness of division by monic Φ_m; deg Q < deg Φ_m from
deg(fĈ_m) < 2 deg Φ_m. Both hypotheses recorded at C2. ✓

**S-3 L-NORM.** Primitive-part factorization exists (w₀ Gauss), w additive
(valuation); DIGIT-SPLIT applies to ALL deg < d₀ inputs (primitivity is
where nonvanishing comes from, per the corrected r2 citation); L-child
residue b̄c̄ ≠ 0 in the field K₀ (nonzero primitives of deg < d₀ = deg ψ̄₀
have nonzero reductions), so w₀(L-child) = w EXACTLY; π-child ≥ w+1; Y-child
≥ w with Ŷ = 0 at d₀=1 (deg b̂ĉ ≤ 2d₀−2 = 0 < 1). All re-derived. ✓

**S-4 Tree + L-EXACT.** Identity exactness in O[x] (consumed lift
structure); reduced-cell degree telescope deg C ≤ (d₀−1) + Σ(P_l−1)deg Φ_l
= deg Φ_m − 1 re-checked from (R1)/WELL-DEF(i); L-EXACT window-free (exit
cofactors need not be reduced); the E1-priority structural remark: at a
Φ_m-exit all j_l ≤ P_l−1 for l ≤ m−2, so the cofactor is a single
Φ_{m−1}-digit — re-derived, it carries (C-W_Q). Initial-cell inventory
(j_l ≤ 2P_l−2, +1 at l=0 on Y) re-checked. ✓

**S-5 L-GRID (full re-derivation).** line_l = e_{l−1}line_{l−1} + j_{l−1}γ_l
verified from Γ_t^{(l)} = e_{l−1}Γ_t^{(l−1)} (t<l−1), Γ_{l−1}^{(l)} = γ_l,
E_l = e_{l−1}E_{l−1}; hence λ_l = the truncation lines ∈ ℤ; s_l(λ_l) ≡
ℓ_{l−1}λ_l ≡ ℓ_{l−1}j_{l−1}h_{l−1} ≡ j_{l−1} mod e_{l−1} via γ_l ≡ h_{l−1}
and ℓh ≡ 1 (S0.1; at l=1, γ₁ = h₀ exactly). t_l ∈ ℤ at every l. The (D3)
off-grid-at-own-line case is EMPTY; first-failure convention never consulted
by any clause (C20 routing re-checked). ✓

**S-6 L-ZMULT (full).** λ-chain jointly additive (no floors); L1 gives
s-additivity mod e with carry δ_l ∈ {0,1}; t_l^Σ = t_l + t_l′ + δ_l ∈ ℤ;
EXP-KIT(b) supplies ε_l(λ+λ′) = z_l^{−δ_l}ε_lε_l′; the z_l^{+δ_l} (t-leg)
kills the z_l^{−δ_l} (ε-leg) at l = 1..m−1; the top has a t-leg and no
ε-leg, leaving exactly z_m^{ε̃}. Re-derived; the two-leg cancellation is
exact at every level. ✓

**S-7 L-LINE/L-MONO (all four bullets re-computed).** (i) Γ_{i+1} − P_iΓ_i
= h_{i+1}∏_{i+1<t<m}e_t via γ_{i+2} = e_{i+1}w_{i+1}Φ_{i+1} + h_{i+1},
w_{i+1}Φ_{i+1} = P_iγ_{i+1}; exit drop = P_{m−1}γ_m = w_mΦ_m. (ii) Δline = 0
from the d-cell's level-i on-line identity scaled by ∏_{i≤t<m}e_t — all
three conversions re-verified (E_i·∏ = E_m; Γ_l^{(i)}·∏ = Γ_l; (g_i−k)γ_{i+1}·∏
= (P_i−e_ik)Γ_i). (iii) π-child +E_m; Y-child +Γ₀; i=0 main child Δline = 0
via Γ₀ = h₀E_m/e₀. (iv) reduced weight = line (single nested digit).
L-MONO + product-additivity ⟹ the on-line skeleton at λ+γ_{m+1} is
promotion- and junk-free (C24). ✓

**S-8 S4.1 L-MU — both branches + necessity iff (full).** Edge inventory:
promotions (A), exits, corrections (B with ρ₀ = P₀−1+[d₀≥2], dumped mass
≤ ρ_l re-checked against the child inventory incl. the Y-child +1), the
i=0 corner Δj₀ ≤ −e₀+[d₀≥2] with the e₀=1∧d₀≥2 fence reproduced. Branch
(a): interval (S_i/e_i, w_{i−1}P_{i−1}) nonempty by e_i ≥ 2 + invariant
(B_{i−1}) + P_{i−1} ≥ e_{i−1}; base (ρ₀/e₁, P₀) nonempty. Branch (b):
interval (S_i, w_{i−1}P_{i−1}) nonempty ⟺ w_{i−1} > S_{i−1} (exact
rearrangement, ρ = P−1 everywhere at d₀=1), base (P₀−1, P₀); no e-bound
consumed; strictness of (A) covers flat promotions; common-denominator
well-foundedness. Necessity: flat (B_i) + (A_i) cascade w_{l−1} > S_{l−1}
bottoms at ρ₀ < P₀ ⟺ d₀=1 — the iff is exact both directions (branch (b)
= the converse witness). Consistency display re-computed (the sealed m=2
point is an (a)-branch point; exits the family at e₁=1; PE6-N-2's
majorization reading confirmed, note-grade). Machine: X-IVL/X-NEC/X-BRA
GREEN (M3). ✓

**S-9 S4.2 inspection census.** Per-leg re-walk: S2.1 valuation/division
arithmetic e≥1-safe; S2.2 masses e_i(g_i−k) ≥ e_i ≥ 1; S3.1 congruences
trivialize at e=1 (s ≡ 0, δ = 0); S3.2 quanta need h ≥ 1 only; S5 consumes
class-level facts + T-TERM. NO leg besides L-MU consumes e_i ≥ 2 (C23
re-confirmed). T-TERM scope = exactly T-scope; no silent widening found at
any consumption site (each carries the pin). ✓

**S-10 DEV-(m) (full).** Induction on μ well-founded on T-scope; (D1)
stepwise; (D2) leaves + single-digit exit cofactors (w_m = e_{m−1}w_{m−1}(S)
+ j′γ_m = line, S reduced at m−1); (D3) READ-ADD applicable (C9), the three
cases: above-line ⟹ all children above-line ⟹ 0; off-grid EMPTY (L-GRID);
the two telescopes re-derived IN FULL — T-tele(1): only j₀ moves, t₁ shifts
by k−g₀, all λ_l (l≥1) fixed, Σ_kψ̄₀,kz₁^{k−g₀} = −1 by ψ₀(z₁) = 0 (ψ₀
monic deg g₀), sign − from (ID-1); T-tele(i+1): t_{i+1} shifts k−g_i, λ_i
rises exactly β_k = (g_i−k)γ_{i+1} (linearity), upper factors k,d-uniform
(λ_l, t_l fixed for l > i+1; ε̃_k target-only), d-sum inside the k-sum
LEGAL and assembling to τ_k by B-READ + realize (R3), EPS-MULT
ε_i(λ_i+β_k)z_i^{ε̃_k} = ε_i(λ_i)ε_i(β_k), ε_i(β_k)τ_k = ψ_{i,k}, collapse
by ψ_i(z_{i+1}) = 0. The S11-charge-(i) points (d-sum interchange, β_k
exactness, sign discipline, top ε-leg) all re-derived clean. ✓

**S-11 L-VNZ (full).** Induction re-derived: grid abscissae j = s_m(λ) +
te_{m−1} with 0 ≤ t ≤ g_{m−1}−1 under deg f < deg Φ_m; a min-achieving
digit exists, satisfies the slot congruence automatically (L-GRID
congruence), its slot weight equals w_{m−1}(f_j), coefficient ≠ 0 by IH ×
units; distinct t's are distinct z_m-powers of degree < [K_m:K_{m−1}] — no
cross-slot cancellation possible. v ≠ 0 on the whole legal class; base
m=0 field case. Machine shadow 0/97 + 0/319 + 0/67 all verified committed. ✓

**S-12 RM-GEN four clauses.** (C-W_R) from (D2) + development additivity;
(C-W_Q) from the single-digit exit remark + L-MONO, window-free (C4/C5
honest); (C-EPS) = L1 restated; (C-READ): junk-split initial children
above-line, above-line x-cells give 0, surviving (on-line x)×(D) pairs
read z_m^{ε̃}·res(b̄_x)𝔷(x;λ)·res(c̄_D)𝔷(D;γ_{m+1}) with ε̃ = ε′ UNIFORM
(shared target pair), factorizing to z_m^{ε′}·v·τ_m by B-READ on both
factors + (Ĉ3). m=1 degenerate case checked (no canonical identities;
DEV-1 content re-derived, not consumed — C3 honest). Flat-level
degeneracies (s ≡ 0, ε ≡ 1, ε′ = 0 at e_{m−1}=1 in branch (b)) ride
through every display. ✓

**S-13 S6 grades.** LAW-DCX-(m+1) stated only; specializations re-computed:
m=1 → T₁ + s₁(γ₂) ≥ 2e₀ on TRACK = [IL3]†'s proved sharp form (S₁ = s₁+s₁′
per the frozen-notation disclosure); m=2 → the v2 law verbatim (u₁ =
(γ₃−s₂(γ₃)γ₂)/e₁ = the DCX3 note's u₀, disclosed). L-CAP re-derived
(pool_l ≤ 3e_{l−1}−1 ⟹ c_l ≤ 2; flat levels pass carries through).
Crossing law = child inventory (only promotions raise a higher exponent —
re-checked against S2.2); pool identification honestly HEURISTIC (11c);
liveness conjectural at every m ≥ 2; no consumption of the law as a proof
step anywhere (C12/C15 sites + S9 standing + S10 fence all checked). ✓

**S-14 COR-A.** T-class(n) = ∩_{m=2}^{n−1} T-scope(m) re-computed — the
"exact union of the per-call pins" (pins-as-constraints reading) is the
intersection of scopes, correct for n ≥ 3; n=1,2 empty call family, no
T-condition — correction verified; headline echo carries the n ≥ 3
restriction and the ⟦C32⟧ package rider; at-acceptance qualifier present
(counter has zero both-CLEAN rounds — accurate). COND-B stays a
conditional display, correctly NOT a corollary. ✓

**S-15 nc challenges (verifier affordance).** All 12 ⟦nc⟧ lines
individually challenged: each is upstream-claim narration, measurement
narration, display-internal rhetoric, or a restatement covered by a
proved in-note lemma (line 612's "d₀ ≥ 2 only" = L-NORM(c), row 1a).
All survive. The two multi-keyword single-tag lines (368, 1269) are both
fully covered by C15. ✓

## 5. Fresh eyes (charge 5)

Probed beyond the prior passes' recorded surfaces: the census script's
zone-detection logic vs the r6 bracket terminator (the round-6 bracket's
"]**" ending parses; zone count exact); the ε₀-convention seam at m=1
(B-READ's level-1 read vs 𝔷's empty ε-product — consistent under the
[ILN]† S0.2 convention consumed as definition, and machine-tied by three
independent implementations at m=2/3/4 incl. cross-ring); the D7 branch-(b)
weights in the committed output ((1,3/2,11/4), (1,3/2,5/4)) satisfy
(A_i)/(B_i) strictly by hand-check; L-CELL(ii)'s induction unwinding; the
initial Y-children's j₀ ≤ 2P₀−1 vs the E1-priority tree (window-free, no
issue). Nothing new found at gap grade or above.

## FINDINGS

**CRITICAL: none.**

**GAPS: none.**

**NOTES (non-blocking, no cure required):**

* **PE7-N-1 (record, composition header).** Line 8: "Acceptance counter 0 —
  no hostile pass has run on THIS note." The counter figure 0 remains
  operatively true at HEAD (zero rounds with both legs CLEAN — the tail's
  own accounting), but the trailing gloss is the at-composition explanation
  and is stale after twelve passes. Not an un-superseded REFUTED claim (no
  finding ever refuted it; it aged), and the six dated repair brackets
  begin three lines below, so no reader can carry the false belief past the
  same screen. A strict application of the as-of discipline would date the
  gloss.

* **PE7-N-2 (record, edited-surface list).** The round-6 record's
  edited-surface list ("the two rule-site brackets, the inline as-of, this
  record, the head round-6 bracket") omits the tail acceptance-counter
  block, which the r6 diff also rewrote (M4 hunk 6). Same genre as PE5-n's
  round-4 instance. The operative claim ("The r6 edit is record-layer
  only") is TRUE, and the note's standing policy makes enumerations
  reading aids with no completeness claim.

* **PE7-N-3 (record, fidelity vocabulary).** The round-6 head bracket and
  tail record say the PE6 machine legs were "byte-identical across the
  census, the pe2 referee, AND the S9 diag"; PE6's archived M4 states the
  diag output was identical MODULO the disclosed volatile trailing elapsed
  float (census and referee were strictly byte-identical). The compression
  follows the note's own established usage (the D7 ACTUALS' "BYTE-EXACT"
  with the same volatility disclosure inline) and the precise statement
  lives in the archived report named in the same sentence.

Informational non-finding (for the file, no note grade): the committed
round-4 referee `rmengine_pe4_ext.py` no longer passes as-is at HEAD — its
hardcoded C28 key is the pre-r4 text that its own finding retired; the
current C28 key matches the committed record sentence exactly (§1 M6).

## VERDICT BLOCK

Machine legs: census reproduces CLOSED byte-identical at a0e266c (zones 17,
arithmetic verified); pe2 referee byte-identical all-GREEN; the r6 fence
HOLDS (six hunks, all record surfaces; the r3→r6 cumulative diff also
clean); historical zone figures and all quoted md5s/figures machine-verified.
R6 remedies: DISCHARGED (rule unified, zero live second-rule assertions,
brackets quote-exact, round-6 records accurate against both archived
reports). Record layer: the un-superseded-refuted-claim class CONFIRMED
DEAD; no HEAD-speaking machine figure without as-of; no internal
contradictions across twelve re-read verdict lines and nineteen cited
commits. Spine: re-derived standalone end to end — zero mathematical
findings; the ELEVENTH consecutive 0-critical pass. Three non-blocking
notes, all record-vocabulary grade.

RMENGINE-PE7 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
