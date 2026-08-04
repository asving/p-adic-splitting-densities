# EMPTY-PE2 — hostile content verification pass 2 on EMPTY_PROOF_2026-08-08.md (commit 7ebd9c8, the E-r1 repaired text)

Verifier: fresh-context Fable (PE2 of the (EMPTY) arc). Charge: quote-and-classify
(CRITICAL / GAP / NOTE); fix nothing. Object: the (EMPTY-(m+1)) proof note at
7ebd9c8 (confirmed via `git log -1 --format=%h -- <file>`; the E-r1 repair commit,
one commit after the round-1 object 4eb1719+ab16707). Central risk per the charge:
the E-r1 repair is PE1's OWN derivation (verifier = repairer for the new S7), so
this pass's core deliverable is an INDEPENDENT from-scratch re-derivation of the
repaired S7 (R1–R7 + E-L8) from E-L1..E-L6 + the ledger definitions, plus an
independent (fresh-implementation) machine instrument decorrelated from PE1's code.

Protocol executed:
1. Re-derived the ENTIRE repaired S7 from scratch — the truncated telescope, the
   true-ledger level-0 floor, the per-edge payment bookkeeping, the R3 exact
   unroll identity, the corrected master inequality term by term with signs, the
   R4 case split, E-L8's induction, the R6 tight-corner floor drop, and the R7
   forcing — from the displayed E-L1..E-L6 + the S0/S1 consumption pins ONLY,
   before comparing against the printed steps (details below).
2. Byte-stability sweep: `git diff 4eb1719 7ebd9c8 -- <note>` read hunk by hunk;
   E-L1..E-L6 statements+proofs, the E-THM box, and the E-THM proof paragraph
   confirmed untouched (only machine brackets in S3/S5 gained E-r1 sub-brackets);
   E-L7's statement text preserved verbatim (its old inline "For (b)..." proof
   sketch moved into the new Proof block — correctly described as derivation,
   not statement).
3. Machine leg: all 9 md5 pins verified (v1/v2/pe1_ext × runner/output/results);
   v1 (`empty_derive_checks.py`, 8fed924…) confirmed untouched in git between
   4eb1719 and 7ebd9c8; the v1→v2 source diff read line by line (purely additive:
   docstring, the CTRL-PAY2 counter + witness lists, min-slack-edge recording,
   the pay_inventory_teeth() phase, provenance keys — NO v1 check logic altered);
   v2 re-run read-only in a sandbox copy (/tmp/pe2_rerun): exit 0, 18/18 families
   0 violations, EVERY semantic results field identical to the committed json
   (only `elapsed` differs).
4. NEW independent instrument `verification/openmath/empty_pe2_ext.py` (my own
   implementation, written without consulting PE1's `empty_pe1_ext.py` code):
   exhaustive grid m ∈ {2,3,4}, e ∈ {1,2,3}^{m−1}, g₀ ∈ {1,2,3}, t₁ ∈ [0,3P₀),
   t_l ∈ [0,3e_{l−1}) — 37,044 grid points, 1,365 Y-tight, exact Fractions.
   Families: PE2-EL4 (identity + bound), PE2-EL5i, PE2-EL5cap, PE2-EL5cls (the
   EXACT ⟺ classification), PE2-EL8 (level-by-level +1 ride AND ρ⁺ ≡ 0), PE2-R3
   (the exact unroll identity, both Y), PE2-HEAD (≤ 1 − w₁), PE2-R6 (single AND
   double removals on the tight corner), PE2-W1a (the withdrawn step's
   refutation witness reproduces). **Result: 0 failures, ALL GREEN.**
5. Cross-checked every statistic the note quotes from PE1's artifacts against
   the committed `empty_pe1_ext_results.json` itself (not just PE1's report):
   655 / 6-of-68 / 511 / 0-of-68 (EXT-MIDSTEP note/true forms), 290/283/437 of
   492 with 0 conclusion breaches (EXT-DISPLAY), 4,468 (EXT-TIGHT-RHO), 8,308 /
   150 / only_top_fullhouse_Y = true (EXT-PAY), 20,439 / 61,317 (grids), min
   slack 1/12 = W₀ sharp (W3G2B), CPGUARD demo record — ALL match.
6. Fresh-eyes sweep: withdrawn-form leakage greps, records accuracy
   (REPAIR RECORD vs the PE1 report; the BRIDGE_ADJUDICATIONS entry added at
   7ebd9c8), grade-cap sentences, residual boxes, fences, claims table.

---
## The independent re-derivation (the central-risk kill)

Everything below was derived by me from the displayed lemma stock before
comparison with the printed text; the printed R1–R7 + E-L8 match it exactly.

**R1.** LED₀ + j₀(C) ≥ 0 + cons₀ = P₀π₁ + ccons₀ gives P₀π₁ ≤ σ₁ + jD₀ + dmp₀
− ccons₀. Decomposing dmp₀ = Y₂ + Σ_{CE,i≥1}(a_{c,0}+y_c) + Σ_{CE,i=0}y_c and
ccons₀ = Σ_{CE,i=0}(P₀−e₀k_c), the i = 0 edges net EXACTLY −(P₀−e₀k_c−y_c) —
the printed true-ledger numerator is right and the round-1 double-count is
gone. σ₁ + jD₀ = t₁ + t·e₀ (W-D2(iv)). Removals ≥ 0 in scope: at d₀ ≥ 2, (H1)
gives e₀ ≥ 2 so P₀−e₀k_c−y_c ≥ e₀−1 ≥ 1; at d₀ = 1, y_c = 0 (L-NORM(c)) so
≥ e₀. Hence Δ₀ = 0 unconditionally valid (monotone floor), and peeling i ≥ 1
edges by ⌊(x+Σy)/P₀⌋ ≤ ⌊x/P₀⌋+Σ⌈y/P₀⌉ (y = a_{c,0}+y_c ≥ 0) then majorizing
t ≤ g₀−1 gives π₁ ≤ c⁺₁(Y₂) + Σ_{CE,i≥1}⌈(a_{c,0}+y_c)/P₀⌉ − Δ₀. MATCHES.

**R2.** Truncated telescope (from LED_l, l = 1..m−2: W_l(σ_{l+1}+jD_l+dmp_l−
ccons_l−j_l) = W_{l+1}π_{l+1}−W_lπ_l; sum = π_{m−1} − W₁π₁ — checked, incl.
m = 2 degenerate). Level-partition bookkeeping audited for double counts:
a_{c,0}, y_c, Y₂, jD₀ appear ONLY in the level-0 floor; a_{c,l≥1} ONLY in
Σ W_l·dmp_l; ccons partitioned {0} floor / {1..m−2} telescope / {m−1} E-L3 —
no term is charged twice. Per edge at 1 ≤ i ≤ m−2: [Σ_{1≤l<i}a_lW_l + ⌈⌉W₁]
≤ W_i (E-L2h's displayed intermediate) and consumption (P_i−e_ik)W_i ≥ e_iW_i
= W_i + (e_i−1)W_i (k ≤ g_i−1), net ≤ −(e_i−1)W_i; per edge at i = m−1 the
whole package ≤ 1 (E-L2h top) against the e_{m−1}-cost inside E-L3, net
−(e_{m−1}−1). MATCHES.

**R3.** ρ⁺_l := (t_l + c⁺_{l−1}(Y₂)) mod e_{l−1}; t_l = e_{l−1}c⁺_l − c⁺_{l−1}
+ ρ⁺_l; e_{l−1}w_{l−1} = w_l telescopes to the EXACT identity W₁c⁺₁(Y₂) +
Σ_{l=2}^{m−1}t_l w_{l−1} = c⁺_{m−1}(Y₂) + Σ_{l=2}^{m−1}ρ⁺_l w_{l−1} (re-derived;
also machine-exact on my grid, both Y, incl. e = 1 levels and m = 2 where both
sides degenerate to c⁺₁). With σ_{l+1}+jD_l = t_{l+1} (W-D2 at (H3)) and
W_l = w_l (l ≥ 1, (H3)), assembling R1+R2+R3 and subtracting e_{m−1}r +
j_{m−1}(C) yields EXACTLY the printed corrected master inequality — remainder
sum on the PLUS side, ≤ Σ(e_{l−1}−1)w_{l−1} = 1 − w₁ < 1 (w₁ > 0 always;
= 0 headroom at m = 2, consistent). Every subtracted term ≥ 0. MATCHES.

**R4.** If k ≥ c_{m−1}+1 and (Y₂ = 0 or off-stratum): c⁺_{m−1}(Y₂) ≤ c_{m−1}
by E-L5(i) resp. the (ii)-classification ⟹ k ≤ c_{m−1} + (1−w₁) < c_{m−1}+1,
contradiction (only k, c ∈ ℤ used — no slack assumed integral). So Y₂ = 1 ∧
Y-tight; d₀ = 1 refuted outright by L-NORM(c) absence; d₀ ≥ 2 forces ALL
e_i ≥ 2 incl. the top ((H1) d₀ ≥ 2 branch, verbatim). The off-stratum
direction of the classification I re-proved independently: off tight₀,
c⁺₁(1) ≤ c₁ (level-0 exactness) and monotonicity; tight₀ with FIRST
non-maximal level l₀: E-L8's induction runs below l₀, at l₀ the numerator is
e c_{l₀} + ρ_{l₀} + 1 with ρ_{l₀} ≤ e−2 so the +1 DIES (c⁺_{l₀}(1) = c_{l₀}),
and the chains' shared floors keep c⁺ ≤ c forever after (no rebirth); the
per-level cap c⁺_l(1) ≤ c_l + 1 rules out ever exceeding +1. NO half-tight
case escapes — the stratum characterization is exact in both directions
(machine: PE2-EL5cls, 37,044 points, 0 failures). MATCHES.

**R5 = E-L8.** Level 1: tight₀ gives c⁺₁(1) = c₁+1 exactly (both g₀ branches
re-checked: g₀ ≥ 2 numerator = P₀ exactly; g₀ = 1 numerator = (q+1)e₀).
Induction l ≥ 2: maximal remainder says t_l + c_{l−1} = e_{l−1}c_l +
(e_{l−1}−1), so t_l + c⁺_{l−1}(1) = e_{l−1}(c_l+1) EXACTLY ⟹ c⁺_l(1) = c_l+1
∧ ρ⁺_l = 0. Headroom EXACTLY 0 on the stratum — re-derived and machine-exact
(PE2-EL8, 1,365 tight points, 0 failures; also holds at e_{l−1} = 1 where the
maximal-remainder condition is vacuous and ρ⁺ ≡ 0). The "why distinct from
E-L5(ii)" paragraph is correct and load-bearing: integrality kills only the
FRACTIONAL headroom; at k = c_{m−1}+1 = c⁺_{m−1}(1) a nonzero real budget
Σρ⁺w would absorb small correction losses — the forcing genuinely needs the
= 0 collapse, not < 1. MATCHES.

**R6.** On tight₀ with Y₂ = 1 the worst-case numerator X′ = t₁+(g₀−1)e₀+1 ≡ 0
(mod P₀) (both g₀ branches); actual t ≤ g₀−1 lowers by (g₀−1−t)e₀ ≥ 0; each
CE₀ removal ≥ e₀−1 ≥ 1 (e₀ ≥ 2 here); X′ exactly divisible ⟹ ⌊(X−R)/P₀⌋ ≤
⌊(X′−1)/P₀⌋ = X′/P₀ − 1 = c⁺₁(1) − 1, i.e. Δ₀ ≥ 1 — valid, and valid ONLY
via the multiple-of-P₀ fact (the withdrawn unconditional form is false; my
PE2-W1a reproduces the refutation witness ⌊6/4⌋ = 1 > 0). Compatible with the
simultaneous i ≥ 1 peel (subadditivity applies to X−R first). Machine:
PE2-R6 single AND double removals over all admissible (t, k_c, y_c) on every
tight grid point with e₀ ≥ 2 — 0 failures. MATCHES.

**R7.** On the forced corner the master collapses to k ≤ (c_{m−1}+1) −
[nonneg terms]; k ≥ c_{m−1}+1 forces each to 0: (e_i−1)W_i > 0 kills interior
edges; (e_{m−1}−1)r ≥ r kills r (e_{m−1} ≥ 2); CE₀ ≠ ∅ would give the Δ₀ = 1
instance k ≤ c+1−W₁ < c+1, contradiction, so CE₀ = ∅. CE = ∅ ∧ r = 0 =
E-L7(b); Y₂ = 1 on Y-tight = E-L7(a). E-THM: (b) ⟹ correction-free stage-1
prefix ⟹ b_Y = π^{u₁+u₁′} (W-D1 leg) ⟹ E-L6 kills the stage-2 Φ₀Y-child ⟹
contradicts (a). MATCHES — the printed proof is my proof.

**Conclusion of the re-derivation: the repaired S7 is CORRECT as printed.**
The corrected master inequality is exactly what the valid ingredient
inequalities sum to; the signs, the < 1 headroom bound, the placement of
integrality (k, c ∈ ℤ only), the conditional Δ₀ mechanism, and the E-L8
collapse are all right; the E-L7/E-THM chain is complete on (H1)–(H3) with
g₀, d₀ free exactly as claimed.

---
## Per-charge disposition

**Charge 1 (the repaired S7).** CLEAN — see the re-derivation above. Every
term, sign, and the < 1 remainder bound re-derived; integrality enters only
as k, c_{m−1} ∈ ℤ (plus π₁ ∈ ℤ inside the R1 floor); the CE₀ deduction is
claimed unconditionally only at Δ₀ = 0 and at Δ₀ ≥ 1 exactly on the forced
corner where it is valid (both directions checked: the withdrawn
unconditional form refuted at the witness, the conditional form proved and
grid-clean incl. double removals).

**Charge 2 (E-L8).** CLEAN — induction re-derived (one line per level, exact
equality e_{l−1}(c_l+1), no floor slack); the EXACTLY-0 claim is right on the
full stratum as characterized; the characterization (tight₀ + maximal
c-chain remainders 2..m−1) is EXACT in both directions — no half-tight case
escapes (first-non-maximal-level argument + per-level +1 cap + no-rebirth
monotonicity; machine PE2-EL5cls/PE2-EL8, 0 failures on 37,044 points).
E-L8 also holds at e_{l−1} = 1 levels (condition vacuous, ρ⁺ ≡ 0), so its
statement is sound even outside the d₀ ≥ 2 corner where E-L7 invokes it.

**Charge 3 (withdrawn displays).** CLEAN with one cosmetic note (N3). The
false π₁ chain and master display sit inside the dated [WITHDRAWN] bracket
with refutation statistics quoted; grep sweep confirms the withdrawn forms
(𝟙[CE₀ ≠ ∅], #CE_{≥1}, 𝟙[Y-tight ∧ Y₂], "collected on one side") occur ONLY
inside the withdrawal bracket and the REPAIR RECORD's description of it —
no downstream consumption. The header's "every displayed intermediate
machine-checked" claim is withdrawn in place. Nothing silently deleted
(full original recoverable at 4eb1719; quoted verbatim in the committed PE1
report).

**Charge 4 (controls / machine).** CLEAN. (a) v2 re-run read-only: 18/18
families reproduce, all semantic result fields identical to committed
artifacts. (b) CTRL-PAY2 fired exactly 2×, both firings the predicted corner
(XM3B and EQ3G2A, i = m−1 = 2, k = 0, a⃗ = (3,2), y = 1, slack = 0, W₀ =
1/12); the v2 code's off-corner classification check (any non-fullhouse/
non-Y/d₀=1 firing would log an EDC-PAYINV violation) recorded none — the
localization claim is machine-enforced, not just observed. (c) v1 bytes
untouched in git; md5 = the note's pin; v2's provenance additionally pins
v1. (d) The phantom-guard disclosure is substantively accurate — I verified
the arithmetic (e₀=2, g₀=2, t₁=5: c⁺₁(1)=2 > c⁺₁(0)=1, tight₀ false, all
E-L5 clauses hold, c₁=2) and located the guard in v1 (fires iff
res[1] > res[0] ∧ ¬tight₀) — with one micro-imprecision (N2).

**Charge 5 (full sweep).** CLEAN. E-L1..E-L6 statements+proofs and the E-THM
box/proof byte-unchanged from 4eb1719 (diff hunks read exhaustively); E-L7
statement text preserved; pins present at consumption sites ((H3) at E-L5/
S5/S7/theorem box/table/F-A; (H1) at R1/R4/E-L7 row; (H2) at E-L3); the
grade-cap sentence present in header + dependency line + (SURV)(ii) bullet,
consumption range now matching S0 exactly (W-D0–W-D4 + W-D6/6c only);
residual boxes (EMPTY-gen)/(SURV)(i) untouched; the REPAIR RECORD and the
BRIDGE_ADJUDICATIONS entry added at 7ebd9c8 match the PE1 report and the
artifacts on every number I checked; (SURV)(ii) follows from E-THM + W-D0 on
the same pins at the same cap. The 0/1 CLEAN grade line and the
"model-diverse leg still owed" disclosure are accurate and prominently
placed (header, F-F, REPAIR RECORD tail).

**Charge 6 (fresh eyes).** Four NOTE-level items, no critical, no gaps:

* **N1 (NOTE — R6's closing gloss).** Quoted (S7, R6): "pushing the
  numerator strictly below the multiple: the floor drops by ≥ 1, i.e.
  π₁ ≤ c⁺₁(1) − 1." The "i.e." clause read in isolation omits the
  + Σ_{CE,i≥1}⌈(a_{c,0}+y_c)/P₀⌉ term of the R1 display it modifies — as a
  bare inequality it is false in general when CE_{≥1} ≠ ∅. The formal
  content actually consumed (Δ₀ ≥ 1, worth −W₁ in the master inequality,
  used at R7 where the ⌈⌉ units are separately absorbed by E-L2h) is
  correct and correctly derived; the gloss is exact only in the final
  forced configuration. Classification: NOTE (imprecise shorthand; no
  downstream consumption of the bare form).
* **N2 (NOTE — phantom-guard parenthetical vs the code).** The S5 E-r1
  bracket renders the guard's firing condition as "(c⁺₁(1) > c⁺₁(0) off
  tight₀)"; the v1 code (line ~365) compares the TOP chain values
  res[Y] = c⁺_{m−1}(Y), not the level-1 values. They coincide at m = 2
  (the regime of the EXT-CPGUARD demo and of the pe1_ext record); at
  m ≥ 3 the level-1 crossing is the necessary trigger but firing also
  requires the gap to ride to the top (satisfiable in scope, e.g.
  m = 3, e = (2,1), g₀ = 2, t₁ = 5 — so the guard IS phantom at every m
  and the disclosure's operative content stands). Classification: NOTE.
* **N3 (NOTE — withdrawal-bracket quoting).** The bracket's requote of the
  withdrawn master display compresses out the original's inline annotation
  column ("[E-L4/E-L5 unroll slack; = 0 iff remainders maximal]",
  "[level-0 corrections kill the floor's +1]", …) and re-wraps the lines.
  The full original text is preserved verbatim in the committed PE1 report
  (Finding 1 quote) and at 4eb1719, so history is retained in substance;
  but "quoted from the original" slightly overstates byte-fidelity. Also
  the S3 bracket closes with a doubled bracket ("…inventory pins.]
  DISCLOSED, S8.]") — nesting wart. Classification: NOTE (cosmetic).
* **N4 (NOTE — residual symbol collision inside the byte-fence).** E-L5(ii)'s
  statement (byte-unchanged by design) still labels the maximal-remainder
  congruence "ρ⁺_l-propagation", while ρ⁺_l as now DEFINED at R3 is the
  c⁺-chain remainder — which is ZERO (not maximal) exactly when that
  congruence holds on the riding +1. E-L8's display disambiguates the two
  explicitly, and no derivation step conflates them; but a reader jumping
  from E-L5(ii) to R3 meets the same symbol for dual objects. Could not be
  fixed at E-r1 without touching a byte-fenced statement. Classification:
  NOTE (flag for the eventual consolidated rewrite).

---
## Machine section

* Commit confirmed: note last touched at 7ebd9c8 (`git log -1 --format=%h`).
* md5 pins, all 9 verified on disk = the note's S0/S8/dependency-line pins:
  v1 8fed92402bcffe6e0c536f1f9d847612 / ddae4007… / 229a1b1…; v2
  61a6a0aa7a0e8d6e28151474e7005224 / 12576b80… / 8c07787f…; pe1_ext
  44d032e1f4edddb026dc210a778fc287 / 42e2f3dc… / 74076344….
* v2 sandbox re-run (/tmp/pe2_rerun): exit 0; 18 verdict families, 0
  violations; counters {terminals 22,261, edges 54,615, cells 1,009,
  dead_traced 616, TIGHT 116 (12 at d₀≥2), Y2TAKEN 61, YCNZ 1,373};
  controls {CTRL-PAY1 0, CTRL-PAY2 2, CTRL-TEL0 11,731, CTRL-FLOOR1 7,675,
  CTRL-HEAD1 560, CTRL-Y 1,373, CTRL-TIGHT 116}; sealed 412/858/126;
  pay_inventory {entries 146, fired 2}; min slack 1/12, min_slack_sharp
  true. Every results-json field except `elapsed` compares SAME.
* NEW independent instrument: `verification/openmath/empty_pe2_ext.py`
  (fresh implementation, no code shared with pe1_ext): 37,044 grid points
  (1,365 Y-tight), 9 check families, **0 failures, ALL GREEN**; the
  withdrawn-step refutation witness reproduces (line1 = 1 > 0).
* pe1_ext committed results json opened directly: every statistic the note
  quotes from it matches the artifact (see protocol item 5).

## Verdict block

The repaired S7 (R1–R7), E-L8, E-L7, and E-THM: independently re-derived
end to end from E-L1..E-L6 + the consumed pins — CORRECT AS PRINTED. E-L8's
stratum characterization exact in both directions; no half-tight escape.
Withdrawals properly bracketed with no downstream leakage. Machine legs
reproduce exactly; CTRL-PAY2 localization machine-enforced; v1 unmutated;
my own decorrelated grid instrument is all green. Grade hygiene (attempt
grade, 0/1→ now 1 clean of the required consecutive passes; WMULTDCX cap;
model-diverse Codex leg still owed and still disclosed as owed) is
accurate throughout. Four NOTE-level accuracy/cosmetic items (N1–N4), none
a justification gap: in each case the correct formal content is displayed
adjacent and is what the derivation consumes.

Chain verdicts: R1 VALID · R2 VALID · R3 VALID (exact identity) · corrected
master inequality VALID as printed · R4 VALID · E-L8 VALID (exact-0 proved +
grid) · R6 VALID (conditional form only) · R7 VALID · E-L7 statement + new
derivation VALID · E-THM VALID on (H1)–(H3), g₀/d₀ free · (SURV)(ii) rides
at the same cap.

EMPTY-PE2 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
