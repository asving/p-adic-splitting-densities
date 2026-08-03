# TR3-S3 hostile pass 6 (Fable, fresh context, model-diverse decider) — 2026-08-08 campaign

**Target:** `lean/notes/openmath/TR3S3_2026-08-08.md` at REVISION 3 +
`verification/openmath/tr3s3_check.py` + `tr3s3_check_run2_output.txt`.
**Context consumed:** TR3S1 (accepted; two-clean recorded in-note),
TR3S2 (accepted; pass-2/pass-3 CLEAN verdicts confirmed by grep of its own
reports' verdict lines only), STRATA3, GRB_ORDER2 (TR-5/RESCALE/TR-4
consumption sites). **Independence:** no TR3S3_pass*_report.md was read;
every step re-derived from the note + parents; both recorded falsifier runs
reconciled against git seals and live-reproduced; a verifier-owned
from-note implementation (fresh code, off-roster p = 5) was written and run.
**Charge:** quote-and-classify (CRITICAL vs GAP), fix nothing, FULL pass.

## VERDICT: GAPS-ONLY — 0 critical / 1 justification gap (display-level, operationally inert)

No algebraic error found anywhere in the chain. The single finding is a
residual display incompleteness of the pass-4 species inside (PIN-GEN-i)
(§2 below); it touches no proof step, no consumer service, and no falsifier
claim.

---

## 1. Step-by-step verification (every step of the charge list)

### 1.1 Lemma KER (S3) — VERIFIED

At e_i^F = 1 (all three levels: (e₁,h₁)^F = (1,h₀), (e₂,h₂)^F = (1,h₁),
(e₃,h₃)^F = (1,h₂), all e(µ_i) = 1 on the stratum): eq (12)
u·1 + s·h = β with 0 ≤ s < 1 forces (s,u) = (0,β); Bézout ℓh + ℓ′·1 = 1
with 0 ≤ ℓ < 1 forces (ℓ,ℓ′) = (0,1); the corrected Def-3.15 exponent
ℓ′s − ℓu = 0, so ǫ₁ ≡ ǫ₂ ≡ 1 (ǫ₀ ≡ 1 by convention AND formula, TR3-S1
(A1)). One line per level, exactly as claimed. Consequences re-derived:
forced progressions 0,1,2,… (s(γ) = 0, stride e = 1); t₁(i) = s₁(a_i),
t₂(i) = s₂(A_i) (the ℓu-terms die); t-integrality trivial. The (H-ℓ)
display "forces (ℓ_j, ℓ′_j) = (0,1)" (S0) is exactly this. Falsifier face:
RI now covers all three splits + all three ℓ's + both eps values (§3.3).

### 1.2 Lemma A3 (S4) — VERIFIED, including the citation discipline

* **Truncation.** A MacLane chain of µ₃ (Def 3.1) is a sequence of
  augmentations; dropping the last leaves a MacLane chain of µ₂ — prefixes
  of chains are chains, so (H-CHAIN) at depth 3 supplies (H-CHAIN) at
  depth 2 for the substate. Sound.
* **Inheritance.** The substate's read data (ν₀, ν₁; lawful monic Φ₁ with
  deg Φ₁ = g₀d₀, w₁(Φ₁) = g₀h₀, R_{λ₀}(Φ₁) ∼ ψ₀; same K₀, K₁, same F₁, F₂
  — the residue towers depend only on the truncated chain) are verbatim
  the order-3 state's own first-read data as listed in S0. Sound.
* **Stratum.** e₀ = 1 holds, so accepted TR3-S1 applies to the substate in
  full.
* **Totality.** TR3-S1 S0 quantifies over "EVERY nonzero f ∈ O[x]" with no
  degree bound (its scope note: only the finite development is used), so
  the digit A (deg A < deg Φ₂) qualifies whatever its degree — confirmed
  against the accepted TR3-S1 text.
* **j₀ = s₀ at e₁ = 1.** TR3-S1's j₀ = ⌊s₀(f)/e₁⌋ = s₀(f) at e₁ = 1; and
  s₀(A) [TR3-S1's datum: initial abscissa of the λ-component of N₂⁻(A) at
  the type-fixed slope −h₁] = s₂(A) [GMN's r = 3 inner datum: initial
  abscissa of S₂(A) = S_{λ₂}(N₂⁻(A))] — same polygon (same Φ₁-development,
  same ordinates u_m = w₁(a_m) + m·w₁(Φ₁) under the PINNED r = 2 identity
  v₂ = w₁, correctly NOT routed through (H-v3)), same type-fixed slope
  under the dictionary. Same datum; the note displays exactly this pin
  ("TR3-S1 S9.6, one level up").
* **Def-3.16-at-i=3 inner-operator identification.** Def 3.16 is
  level-generic: at i = 3 the inner operator is R_{2,γ_j}, the identical
  Def-3.16-at-i=2 symbol TR3-S1's theorem reads, over the SAME
  Φ₁-development of the digit, and at on-line slots the weight γ_j = w₂(A)
  is the digit's own weight — precisely TR3-S1's read point. At off-line
  slots TR3-S1 does NOT apply, and the note correctly routes those through
  the genuinely new Lemma Z2 instead. The m₀ = (s₂(A) − s(β))/e₁ = s₂(A)
  bookkeeping (s(β) = 0 by KER) is the displayed y^{s₂(A)} factor. All
  verified.

### 1.3 Lemma Z2 (S4) — VERIFIED (the two-level dichotomy)

β < w₂(A): every nonzero Φ₁-digit has w₁(a_m) ≥ w₂(A) − mγ₂ > β_m (min
property, strict through the hypothesis); every Φ₀-digit of a_m has
w₀(b) ≥ w₁(a_m) − m′h₀ > β_m − m′h₀ = δ; so every coefficient of b·π^{−δ}
has positive valuation and reduces to 0 — including δ < 0 (w₀ ≥ 0 > δ
gives the same conclusion; TR3-S1 (A3)'s corner verbatim). Every level-1
coefficient of every slot dies, hence every level-2 coefficient. Domain
direction confirmed: β < w₂(A) means A ∈ P_β(µ₂) — INSIDE Def 3.16's
printed domain; A = 0 reads 0 by convention. The strict-inequality chain
and both corners check. Falsifier upgrade honest: the probe HARD-CODED
off-line slots to zero; the new harness computes them (noff = 902 fired).

### 1.4 t₂-absorption — VERIFIED

Def 2.19 at r = 3 with GMN level-2 = project read-ν₁ data:
t₂(i) = (s₂(A_i) − ℓ₁u_i)/e₁ = s₂(A_i) at ℓ₁ = 0 (normalized, e₁ = 1),
e₁ = 1; integrality trivial. This exactly absorbs Lemma A3's z̄₂^{s₂(A)}
factor in the S5(ii) chain — each chain step re-derived and each
justification tag ([KER], [(SQ₂)], [A3], [t₂ = s₂ + inner R₂ = R_λ₂],
[Def 2.20]) checked. The inner-operator tie (GMN's R₂ at the type-fixed
λ₂ = the project R_λ₂ of TR3-S1's pins, evaluated per Def 2.21 from the
ACTUAL initial abscissa s₂(A)) is consistent with the GD23 rows + accepted
TR3-S1. Falsifier face RIII tests the FULL formula (with ℓ₁·u_j live in
the code), not the collapsed form.

### 1.5 σ₂ via Cor 5.6(2) at index 2 < r (S2) — VERIFIED

(i) ψ₂^F = R₂^F(Φ₂) by Cor 5.6(2) read CHAIN-INTERNALLY at index
2 < r = 3 under (H-CHAIN) at depth 3 — the same citation pattern accepted
in TR3-S1 (indices 0, 1 < r = 2), with (KP_i) correctly deferred to the
ONE extended-chain site (Φ₃, S6.2 step 1), mirroring TR3-S1's single
(KP_i) site at Φ₂. (ii) Accepted TR3-S1 at f = Φ₂ (total, side-read form).
(iii) Monicity upgrade re-derived: top Φ₁-digit 1 at abscissa g₁, on-line
(u = g₁w₁(Φ₁), e₁u + g₁h₁ = g₁γ₂ = w₂(Φ₂)); inner data R₁(1) = 1,
s₁(1) = 0, t₁ = 0 give c^G2_{g₁} = 1; lawfulness (deg R_λ₂(Φ₂) = g₁)
forces s₂(Φ₂) = 0; monic associate of monic ψ₁ = ψ₁. σ₂ = σ₁[y]/(ψ₂^F ↦
ψ₁) is then a well-defined field iso (ψ₁ irreducible is read data);
(SQ₂) is the standard quotient-evaluation square. The S6.2 Φ₃-analogue
(A_{g₂} = 1, u = g₂w₂(Φ₂), c^G3_{g₂} = 1, s₀(Φ₃) = 0, σ₂(ψ₃^F) = ψ₂)
re-derived the same way — correct one level up.

### 1.6 S5 assembly — VERIFIED

(SLOT-3) from the augmentation display (µ₃(φ₃) = µ₂(φ₃) + λ₃ =
w₂(Φ₂) + h₂ = γ₃ at E = 1). Support equivalence: under (H-v3),
e₂u_i + ih₂ = w₂(A_i) + iγ₃ ≥ γ with equality = on-line = FGMN's
w₂(A_j) = γ_j — the same equality, stride 1, no congruence. Off-line and
γ_j < 0 cases via Z2 (domain from γ = min; w₂ ≥ 0 kills negative-weight
on-line-ness); window-external abscissas consistent on both sides.
Nonvanishing: R_λ₂(A) nonzero with nonzero ends (accepted TR3-S1's
support clause at the component endpoints), deg ≤ g₁ − 1 < g₁ = deg ψ₁
via the digit degree bound (consumed exactly and only here — honestly
displayed), so evaluation at the basis-generating z̄₂ is nonzero; z̄₂ a
unit (ψ₁(0) ≠ 0). Assembly and the y^s division per Def 3.18 (j₀ = s
justified by the nonzero k = 0 term) — exact, degrees d, aligned constant
terms. Equal support both sides.

### 1.7 (H-v3) conditionality at every consumer display — VERIFIED

Every consumer-facing site carries the conditionality: summary-table rows
(TR-3′-GEN order-3; TR-3-ORD-X "(H-v3) + (KP_i) + [T]"; consumers), S6.1
heading + blockquote + GD3-FULL/OL-B clause ("in the ∼-form AND the
=-form" — lawful, the =-form is what the discrepancy-≡-1 theorem gives),
S6.2 bold conclusion + consumer clause, S6.3. The stated content of the
conditionality is accurate: (H-v3) enters ONLY through the order-3
ordinate u_i (component/on-line geometry; its t₂-appearance dies at
ℓ₁ = 0), so a false (H-v3) strips the GMN-attribution of R_λ₃ and leaves
the displayed identity true of the project-facing operator — exactly what
S6.1/S7 say. The S1 derivation sketch is internally correct (at r = 3,
e₂^{GMN} = e₁ = 1 and the H₂-intercept in the pinned r = 2 normalization
gives min_i(w₁(a_i) + iγ₂) = w₂ at e₁ = 1), and keeping it a HYPOTHESIS
because the H_{r−1} generic display was never re-extracted is the correct
application of the extraction-corruption discipline — the more
conservative choice given that the GRB leaf's TR-5 table even lists
w_i ↔ v_{i+1} as a standing GD23 row. S9.1's "no other v₃ consumer"
audit confirmed: in the displayed r = 3 pins, v₃ rides only u_i (component
+ ordinates + the dead ℓ₁u_i term).

### 1.8 (PIN-GEN-i) — pin/recipe/summaries VERIFIED; one residual site (§2)

The pin names all three operators (corrected Def 3.15 at level 2, Def
3.16 at i = 3, Def 3.18 at i = 3); the owed discharge recipe names all
three ("fresh `pdftotext -layout` … at Defs 3.15/3.16/3.18 [REV3]"); the
S7 transcription-scope bullet and S9 item 6 name all three. The pin's
scope claim (gates ATTRIBUTION, not the finite identity of the displayed
operators) is correct. The one residual: §2.

### 1.9 Fences — VERIFIED

* **e_j ≥ 2**: hard-fenced (header + S7 bullet 1) with the exact failure
  points displayed (KER dies at the first e_j ≥ 2; A3's citation needs the
  substate's e₀ = 1; the t₂-collapse needs ℓ₁ = 0); (TWIST-3) stays sealed
  and untested. Nothing in the note or harness touches such strata (roster
  all-e_j = 1 verified in code).
* **Orders ≥ 4**: fenced (S7 bullet 2) — the induction is NOT written and
  the note says so; the plausibility remark is clearly marked as such.
* **D-ITER**: untouched (header + S7 bullet; E₃ = 1 rank-1 degenerate;
  the probe's V3 δ ≡ 0 row correctly described as the degenerate control).

### 1.10 Consumer chains (S6.1–S6.3) — VERIFIED

S6.2 chain: label tie (KP_i displayed) → matched-label transport (σ₂ ring
iso preserves ψ-adic orders; key classes coincide at discrepancy ≡ 1, so
the naive both-sides-ψ₂ pairing is also lawful — consistent with TR3-S2's
(ORD-INV) discipline and Lemma KEY0 at c = 1) → Cor 5.15 leg NOT
discharged ([T] displayed). S6.3 discharges only the TR-3-ORD-X seam of
B-M2 OL-1(b) at these states with the full inherited package; other seams
(GRADED-READ, REC-SL) correctly left standing. The (2′) leg through TR-4:
the leaf's TR-4 is the generic-r factorization package (Cor 4.4(1)/4.5/
4.11, quoted generic-index prints) — same lawful generic-index consumption
pattern as the parents; the service statement carries (H-v3).

---

## 2. The finding

**GAP (display-completeness; operationally inert) — the (PIN-GEN-i) scope
sentence omits Def 3.18 from the list of displayed shapes the unit's
algebra consumes.** S1, (PIN-GEN-i), final sentence:

> "Scope of what the pin gates: the ATTRIBUTION of the displayed operators
> to the FGMN print — NOT the finite identity of this unit, whose algebra
> consumes only ǫ ≡ 1 on-stratum (Lemma KER) and the displayed Def-3.16
> shape."

The unit's finite identity includes the two-form clause (TR3-S3-form),
whose S5(iii) step explicitly consumes the displayed Def-3.18 shape
("dividing by y^{j₀} (Def 3.18; j₀ = s by (i) …)") — the very operator
REV2/REV3 added to the pin, its discharge recipe, and the S7/S9
summaries. The "consumes only … and the displayed Def-3.16 shape"
enumeration is therefore incomplete under the natural reading of "the
finite identity of this unit" (the title identity is the form). This is a
fifth site of the pass-4 species (REV3's sweep covered the recipe and the
summaries; this subordinate clause inside the pin body survived). It is
operationally inert — the discharge recipe and both summaries are
complete, and the pin's actual scope claim (attribution-only gating) is
correct — but the note's own REV3 standard ("every operator-set listing
now reads Defs 3.15/3.16/3.18 or names all three") argues for the
one-token completion "and the displayed Def-3.16/3.18 shapes". The
related S7/S9.6 recurrences of "the algebra consumes only ǫ ≡ 1" are
contextually scoped to the ǫ-reading (both sites name all three defs
immediately before) and are not separately charged.

Classification: JUSTIFICATION GAP (display), not critical — no proof step,
consumer service, or falsifier claim depends on the sentence.

---

## 3. Falsifier reconciliation (all charge items)

### 3.1 Seals and provenance — VERIFIED against git

* **b4a142b** (2026-08-03 01:40:14): note (497 lines, pre-revision) +
  `tr3s3_check.py` (502 lines, sealed header, NO addendum) — the
  preregistration, committed before any run record.
* **482150b** (01:41:48, 94 s later): adds ONLY `tr3s3_check_output.txt` +
  `tr3s3_check_results.json` + a 28-line note update — the script itself
  untouched, so the run-1 record was produced by the sealed script.
* Script diff b4a142b → HEAD: exactly 2 hunks = the REVISION 1 ADDENDUM
  header + the two-check RI leg in `R2w_at` (level-1 eq-(12) split of β_m
  at (e₀,h₀), s = 0 predicted, + l0 == 0) — precisely the declared legs,
  nothing else.

### 3.2 Run-1 record — matches S8.2 exactly

E2A 0/2,241 · E2B 0/816 · RI 0/14,797 · RII 0/1,141 · RIII 0/1,141 ·
RIV 0/1,141 · Z2 0/768 · XV 0/816 · W 0/144 · K 0/24 · O 0/816 ·
CERT 0/24 · meters m0pos 85 / j0pos 173 / noff 902 / noisy 72 / holes 64 /
wfail 0 · ord hist 0:744 1:38 2:34 · TOTAL 23,869 — every number in the
note's S8.2 block reconciles with `git show 482150b:…output.txt`.

### 3.3 Run-2 record + perimeter — VERIFIED

RI 0/21,741 and TOTAL 30,813; both deltas +6,944 (= the nonzero level-1
digit reads, one new RI sample per eps1 site) as preregistered. My own
diff of the run-1 record vs `tr3s3_check_run2_output.txt`: deviations at
EXACTLY the four timing lines, the RI count line, and the TOTAL line —
every other row, meter, and histogram value byte-identical, as the
ADDENDUM's STOP condition demands. TOTAL 30,813 = the sum of all family
counts (independently summed from the JSON). The JSON matches the run-2
table (counts, meters, ord_hist, 0 violations).

### 3.4 Live reproduction — GREEN

`python3 tr3s3_check.py` re-run in this pass: exit 0, ALL GREEN,
RI 0/21,741, TOTAL 30,813, all meters and the histogram byte-identical to
the run-2 record (23.8 s); no cypari2 WARNING, so the PARI CERT legs
fired live (24/24 towers).

### 3.5 Row O = histogram meters only — CONFIRMED in code

`check_sample` returns early on any E2B failure, and E2B's pass condition
includes `side == glist`; row O then computes `fp_ord` of two EQUAL lists,
so its violation branch is unreachable — the note's REV2 correction is
accurate (the S6.2-transport falsification lives in E2B; only O's
ord-histogram meters are live, and they fired: ord ≥ 1 present, 38+34).

### 3.6 Discipline — numerics as falsifiers only

The note claims the theorem from the finite algebra and uses the runs only
as falsifiers (header, S0, S8); the corrupted `/tmp/litunit/fgmn.txt` is
never consulted (its non-consultation is a stated pin, and the owed
re-extraction leg is displayed as OWED at (PIN-GEN-i), not attempted).

---

## 4. Verifier-owned independent implementation (external leg)

`/tmp/tr3s3_pass6_spotcheck.py` — written in this pass FROM THE NOTE's
displayed formulas alone; zero shared code with the repo harness; base
p = 5 (off the roster's {2,3}), O = F₅[t]; own nested-tuple field models,
own O[x] arithmetic, own polygon/on-line code; eps exponents computed
literally from the corrected Def 3.15 and asserted 0 (KER), t₂ asserted
= s₂ (absorption), GMN side under (H-v3). Three towers: T-I (g = (2,2,2)),
T-II (g₀ = 1 corner, K₁ = K₀, g₂ = 3), T-III (g₁ = 1 corner, ψ₁ linear,
z̄₂ ∈ K₁). Families: random, t^k, Φ₂^a·h (j₀ > 0), Φ₃^µ·Q (ord ≥ 1),
prescribed-value with holes + sub-line noise, Z2 below-weight reads incl.
negative weights, K label ties at Φ₃, A3 inner-list faces.

**Result: 1,564 checks, 0 failures, exit 0.** Both failures encountered
during development were bugs in MY fresh code (digit representation;
generator normalization), not in the note — the same shape as the pass-3
precedent, corroborating the harness. This leg also independently
exercises the two roster corners at a fresh prime and a g₂ = 3 case the
roster lacks at that corner combination.

---

## 5. Additional confirmations

* TR-5 at depth 3 is the GRB leaf's own dictionary at generic depth
  r = i+1 (S1.2) — lawful consumption, not an invention; likewise RESCALE
  (level-generic) and TR-4 (generic-r corollary package).
* TR3-S2 acceptance confirmed (its pass-2 and pass-3 reports' verdict
  lines: CLEAN, CLEAN); TR3-S1 acceptance recorded in its own note
  (passes 2+3 CLEAN, model-diverse). All consumptions are at the parents'
  accepted states; nothing from the superseded S3.2 law or the retired
  artifact ǫ is consumed.
* STRATA3 probe seal d8ef8d8 verified (script-only commit, pre-run); the
  note's S8.1 recorded-run summary matches the STRATA3 note.
* Acceptance-counter bookkeeping is consistent (0/2 after REV2/REV3
  orchestrator edits; passes 5+6 decide).

## 6. Verdict block

* CRITICAL: **0**
* JUSTIFICATION GAPS: **1** — §2 (the (PIN-GEN-i) scope sentence's
  operator list omits Def 3.18; display-level, operationally inert,
  one-token fix).

**VERDICT: GAPS-ONLY (0 critical / 1 gap).**

— pass 6 verifier (Fable, fresh context), reports only; nothing in the
note, harness, or records was modified by this pass.
