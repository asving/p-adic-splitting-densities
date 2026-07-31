# O9 Phase-B rev 4 — hostile verification PASS 4 (fresh context, 2026-07-31)

**Charge.** Verify `O9_phaseB_verifybrief_rev4.md` after the FULL-attainment
repair: (1) the restated (ADM) + (CLASS-d); (2) the re-derived r = 1
inequality, including the f₁ = 1 collapse; (3) the §5.1 image-law restatement
(the withdrawn bijection gloss); (4) the K7 claims as displayed, including
the d ≥ 2 positive-control arithmetic; (5) the standard census-layer audit.
Quote-and-classify; fix nothing.

**Method.** Full read of the rev-4 brief; independent hand re-derivation of
the (ADM) equivalence chain (via LED(iii)'s increment argument), the
(CLASS-d) proofs at r ≤ 1 and the general-order pigeonhole, the r = 1 FULL
inequality and its collapse, §5.1's injectivity/fiber-uniformity/image-law
counting, and every displayed warning-display-2 / K7 number (s-values, E′,
censuses, ratios, per-slot localization); source audit of
`o9_rev4_fulladm_check.py` against its §10 description; **re-execution** of
the K7 script with byte-diff against the committed log; full `diff` of rev 3
vs rev 4 against the header's byte-stability manifest; grep for surviving
uses of the withdrawn gloss; spot re-checks of the carried K6/K1–K4 logs and
the §6.4 source cite.

**VERDICT: SOUND — 0 critical errors, 1 justification gap.**

The FULL-attainment repair is correct and complete at every consumption
site; the mathematics verified below is exactly as displayed. The one gap is
residue of the repair itself: the withdrawn "per-slot bijection" gloss
survives verbatim at two byte-carried SUMMARY sites (§0's OL-A(iii) row and
§1's (P5) pin), where it now contradicts the rev-4 §5.1 restatement. Neither
site is consumed by any proof, so the logical chain is unbroken.

---

## 1. FINDING 1 — GAP: the withdrawn bijection gloss survives at two byte-carried summary sites

**Offending passages.**

> §0 status table, OL-A(iii) row: "OL-A(iii) line/digit structure | graded
> digit reads are per-slot F_{q^d}-bijections | = **GD-3/OL-B**, consumed
> not re-proved; order 1 PROVED (GD23 RES-1); orders ≥ 2 = (GR-B) [OPEN
> there]"

> §1, the (P5) pin: "(P5) GMN Prop 2.10: realizability of any prescribed
> residual value at any admissible weight by some P with deg P < m
> (corroboration for (GR-B)'s surjectivity clause; not load-bearing — see
> §5.1)."

**Why these offend.** Rev 4's own §5.1 establishes that the per-slot digit
read is a bijection onto F_{r+1} ≅ F_{q^d} **only at fully attained β**
(dim G_β = d), and that "no reading of (GR-B) can defeat the PROVED
LED(ii)/(iii) lattice counts" — at a partially attained slot the image is a
proper F_q-subspace, machine-witnessed by K7. So:

* The OL-A(iii) row's middle cell states the pre-repair gloss unqualified.
  Read as the content of the open input at orders ≥ 2, it is not merely
  OPEN — as stated (no attainment qualifier) it is REFUTABLE by the same
  LED(ii)/(iii) argument that grounded pass 3's critical, at any window
  slot with 0 < dim G_β < d. The row needs the attainment qualifier or a
  re-point at the line clause (which is what §5.1 now consumes).
* The (P5) parenthetical still names "(GR-B)'s surjectivity clause" — a
  clause §5.1 rev 4 explicitly withdraws from (GR-B)'s reading ("the line
  clause's true content"). §5.1's own re-scope ("cited only at fully
  attained β, and was never load-bearing") is correct; §1's pointer "see
  §5.1" defuses the pin, but the withdrawn clause's name survives.

**Classification: justification gap** (incomplete propagation of the rev-4
withdrawal into byte-carried summary text). Non-load-bearing, verified: the
grep for "bijection"/"surjectiv" over the brief finds consumption ONLY in
§5.1's withdrawal notice, the §0-pre changelog (historical quotes), and §11
(the attack list); §§6–8 are clean — §6.3's on-line bullet and §6.4 step 3
consume "§5.1 fiber uniformity + FULL attainment ((ADM) + line clause)"
exactly as the repair intends. Assume the §5.1 reading and continue: nothing
downstream changes.

---

## 2. The rev-4 repairs, each verified as displayed

### 2.1 The restated (ADM) and its equivalence chain — VERIFIED

The three displayed forms are equivalent, re-derived by hand from LED(iii):
s(β+1) − s(β) = Σ_𝐣 [max(0, ⌈(β+1−wt)/e⌉) − max(0, ⌈(β−wt)/e⌉)], and per 𝐣
the summand increments (by exactly 1) iff β − wt ≥ 0 and e | (β − wt), i.e.
iff wt(𝐣) ≤ β and wt(𝐣) ≡ β (mod e). Hence dim G_β = s(β+1) − s(β) =
#{𝐣 : wt ≡ β (mod e), wt ≤ β}, and "= d" transfers across all three forms.
The count form is a p-free lattice condition (weights by the (P3)
V-recursion), so decidability is preserved by the strengthening.

**Exactness of the consumption (attack item 1).** Nothing weaker suffices:
if dim G_{β_k} < d, §5.1's onto-ness fails (K7's countermodel), and both
§6.3's digit-vector sum and §6.4 step 3's per-digit q^{−d} charge are false
at that slot. Nothing stronger is smuggled in: §5.1's chain uses only (a)
the (GR-B) LINE clause (in(a) = ϕ_β·c(a), giving injectivity G_β ↪ F_{r+1}),
(b) LED(ii)/(iii) (proved), (c) dim G_{β_k} = d — i.e. (ADM) exactly. The
homomorphism fiber-uniformity step is unconditional (additivity of r_β on
the subgroup {w ≥ β} checked case by case as displayed; kernel = {w > β} of
size q^{mN−s(β+1)}, consistent: q^{mN−s(β)−dim} = q^{mN−s(β+1)}).
Value-attainment retains exactly its two legitimate uses (vertex emptiness;
interior forced-zero with the not-displayed variant), and the "three failure
shapes" sentence correctly separates them from the new partial-slot shape.

### 2.2 (CLASS-d) — VERIFIED (attack item 2)

* r = 0: e = 1, one class, all m = f₀ = d weights are 0. Trivial. ✓
* r = 1: wt(𝐣) = j₁·w(φ₁) (the j₀ ledger part has weight 0: w(x) =
  e₁·v₁(x) = 0 when f₀ ≥ 2; at f₀ = 1 there are no x-monomials), and
  w(φ₁) ≡ h₁ (mod e₁) by (P3). Class of c: j₁ ≡ h₁^{−1}c (mod e₁)
  (gcd(h₁,e₁) = 1), i.e. j₁ = j₁* + t·e₁ with 0 ≤ t < f₁ inside
  [0, e₁f₁) — f₁ values, each with f₀-fold j₀-multiplicity: f₀f₁ = d. ✓
* General order from (GR-B): line clause ⟹ dim G_β ≤ d for every β;
  LED(iii) at β ≥ max class-c weight (β in class c) gives dim G_β =
  #{class c}; so every class count ≤ d, and the e counts sum to m = ed,
  forcing each = d. Pigeonhole sound. ✓
* Scoping audit: the max-weight reading "(ADM) ⟺ every on-line β_k ≥ class
  max" appears only under the explicit "Every consumer of (ADM) already
  assumes (GR-B)" preamble and, in the automaticity bullet, under an
  explicit "under (CLASS-d)"; the DEFINITION of (ADM) is the unconditional
  count form. ✓ (At r = 1 the reading is unconditional via the proved
  (CLASS-d).)

### 2.3 The r = 1 FULL inequality and the f₁ = 1 collapse — VERIFIED (attack item 3)

With V₁ = 0 (the (P3) recursion's base at order 1) the class of β mod e₁
carries weights h₁·(j₁* + t·e₁), 0 ≤ t < f₁, strictly increasing in t
(h₁, e₁ ≥ 1); the count reaches d = f₀f₁ iff the class MAXIMUM
h₁·(j₁* + (f₁−1)e₁) is ≤ β. So (ADM) at r = 1 ⟺ every on-line β_k ≥
h₁·((h₁^{−1}β_k mod e₁) + (f₁−1)e₁), as displayed. At f₁ = 1 the (f₁−1)e₁
term vanishes and the formula IS rev 3's value inequality (min = max: one
weight per class), so full = value exactly when f₁ = 1 — and at f₁ ≥ 2 the
predicates genuinely differ (any class-c β with class-min ≤ β < class-max;
such β exist since the gap h₁(f₁−1)e₁ ≥ e₁ contains class members). The
f₀ > 1 case rides along: the f₀-multiplicity multiplies the count but not
which weights clear β. Spot values: warning display 2 (e₁ = 1, h₁ = 2,
f₁ = 2): FULL threshold 2·(0+1) = 2 > 1 = β₁, VALUE threshold 0 (passes,
wrongly) ✓; warning display 1 (e₁ = 3, h₁ = 2, f₁ = 1): value threshold
2·((2^{−1}·1) mod 3) = 2·2 = 4 > 1 ✓ (fails already at value; FULL = VALUE
there). K7 CH5 verifies the equivalence + (CLASS-d) + the collapse at seven
(e₁,h₁,f₁,f₀) tuples, β ≤ 40 — script logic audited (weights list carries
the f₀-multiplicity; `thr_full`/`thr_val` are the displayed formulas;
`dim_crit` is the LED(iii) count).

### 2.4 §5.1 as restated — VERIFIED (attack item 4)

* **Injectivity from the line clause:** r_β factors through G_β; if
  r_β(a) = r_β(b) on classes then in(a−b) = ϕ_β·(c(a)−c(b)) = 0 in G_β, so
  the classes coincide — the embedding G_β ↪ ϕ_β·F_{r+1} is honest, hence
  dim V_β = dim G_β = s(β+1) − s(β) by LED(iii). ✓
* **Fiber uniformity onto V_β** is the unconditional finite-abelian-group
  fact; the per-digit law q^{mN−s(β)−dim V_β} on V_β, 0 off V_β. ✓
* **Onto ⟺ FULL** is a lattice fact given injectivity, correctly labeled
  "not a (GR-B) clause". The partial-attainment law is LED(ii)-consistent
  at both ends: Σ over digits = q^{dim}·q^{mN−s−dim} = q^{mN−s(β)} ✓, and
  the z = 0 fiber = q^{mN−s−dim} = q^{mN−s(β+1)} = #{w > β} ✓.
* The withdrawn gloss is consumed nowhere in §§6–8 (grep-verified); the
  (P5) re-scope inside §5.1 is correct. The survival at §0/§1 is Finding 1.

### 2.5 §6.3 / §6.4 consumption re-pointing — VERIFIED (attack item 5)

§6.3's on-line bullet and §6.4 step 3 now condition the per-digit q^{−d}
charge on "dim G_{β_k} = d, i.e. FULL attainment = (ADM) [rev 4] + (GR-B)'s
line clause" — exactly what §5.1 delivers. FULL is needed at EVERY on-line
slot (vertices for the (q^d−1)/Lemma C-D telescope over F_{r+1}^×-valued
digits; interior slots for the uniform F_{r+1}-valued digit sum feeding
∏M), and the displayed proofs demand it at every on-line slot — no
under-demand. CEN-J's coset-top leg needs no sub-ledger FULL clause:
if k_s = ℓ the top read is the ρ-pinned right end ((FRESH)(c), value
irrelevant by Lemma C, nonvanishing by LED-top(iii)); if k_s < ℓ the top
slot is a right-tail slot charged by LED-top(i) alone (no read). The m ∤ n
top is never an interior on-line read. ✓ §6.4's r = 0 validation survives
the FULL reading verbatim: at r = 0, dim G_β = f₀ = d for every β ≥ 0
(all weights 0, e = 1), so (ADM)-FULL is automatic on M08's k₀ = 0 data
and all K5 data (attack item 8). The negative-height corner is correctly
padded. ✓

### 2.6 Warning display 2's arithmetic — VERIFIED by hand (attack item 6)

Type: m = 2, d = 2, e = 1, weights {0, 2}, V̂ = 4; s(β) = β + max(0, β−2):
s(1) = 1, s(2) = 2, s(6) = 10, s(7) = 12 ✓. dim G_β = 1 for β ∈ {0,1}, 2
for β ≥ 2 ✓. D1 = (0,6)→(1,5), N = 7: β = (6, 1), (DET) max(6,1) ≤ 6 ✓;
E′ = (14−10) + (14−1) − 2·2 = 13 ✓; rev-3 display q^{13}(q²−1)² = 73728 at
q = 2 ✓ (102036672 at q = 3 ✓). Truth = #{w = 6}·#{w = 1} =
(q^{14−10} − q^{14−12})(q^{14−1} − q^{14−2}) = (q⁴−q²)(q^{13}−q^{12}) =
q^{14}(q²−1)(q−1) = 49152 / 76527504 ✓; display/truth = (q²−1)/(q(q−1)) =
(q+1)/q ✓. Localization: slot 0 (FULL) truth q²(q²−1) = 12 at q = 2 =
its displayed factor (q^d−1)q^{mN−s−d} ✓; slot 1 (PARTIAL) truth
q^{12}(q−1) = the §5.1 image law (q^{dim}−1)q^{mN−s−dim} ≠ the onto law
(q²−1)q^{11} ✓. Membership at this datum is genuinely valuation-level:
both slots are vertices of a d(S) = 1 face, so the residual polynomial has
exact degree 1 with nonzero constant term — type {(1,1)} is forced by
digit-nonvanishing = exact w. ✓

### 2.7 K7 as displayed — VERIFIED, script and log audited (attack item 7)

* **Re-execution:** `python3 o9_rev4_fulladm_check.py` reproduces
  `logs/o9_rev4_fulladm_20260731_202140.log` **byte-identically**
  (RESULT: ALL PASS), and every §2/§10 headline number appears verbatim in
  the log (73728/49152 with the exact display·q = truth·(q+1) identity;
  102036672/76527504; 147456/306110016; CH4's 0/0, 16/16, 324/324; CH5's
  seven tuples; CH5b's thresholds 2 vs 0).
* **Script audit against the §10 description:** w is computed from the
  pinned one-step recursion min(v(c₀), v(c₁)+2) (not TRI as a black box)
  ✓; CH1 measures dim G_β from count ratios #{w ≥ β}/#{w > β} = p^{dim}
  and matches the LED(iii) criterion at every β ✓; CH2's truth is by
  v-census convolution (exact: w depends only on the valuation pair, with
  the v-census by direct enumeration) with the p = 2 naive joint pair loop
  as the second leg ✓ — the loop enumerates the full box jointly and tests
  §2's per-slot exact-w keying, which IS stratum membership at these data
  (§2.6 above), so the disclosure ("shares the one-step pinned w-recursion;
  the loops check every count and the slot-product structure, not w
  itself") is accurate ✓; CH2c's image-law leg is labeled
  arithmetic-consistency, correctly ✓.
* **The d ≥ 2 positive control (CH3) is a genuine VALUE gate of CEN-W's
  free-box display:** D2 = (0,7)→(1,6), N = 8: β = (7, 2), both dim = 2 =
  d (7, 2 ≥ 2), (DET) 7 ≤ 7 ✓; E′ = (16−12) + (16−2) − 4 = 14 ✓;
  display = q^{14}·(q²−1)·M_{(1,1)}(q²) = q^{14}(q²−1)² ✓ — and the
  brute-force truth (q⁴−q²)(q^{14}−q^{12}) equals it exactly, at both
  primes ✓. It exercises the E′ bookkeeping, the −d·L charge, the ε = 1
  free-unit factor, and ∏M at d = 2 — the first VALUE gate off the
  value = full diagonal. Coverage limits (single-face, ℓ = 1, e = 1,
  valuation-forced types, no genuine deg-≥ 2 residual condition) are
  disclosed in §10 verbatim. ✓
* CH4's K6 regression under FULL: at the two m = 3, d = 1, f₁ = 1 cells
  FULL ⟺ VALUE (the collapse), so 0 = 0 and p⁴(p−1)² must and do stand
  (E′ = (9−8) + (9−4) − 2 = 4 re-derived by hand ✓). ✓

### 2.8 The automaticity rescope — VERIFIED (attack item 8)

r = 0: dim G_β = #{wt ≤ β} = m = f₀ = d for every β ≥ 0 — FULL, not merely
value, is automatic on nonnegative on-line data; scope ("every datum
realizable as an actual polygon") and the negative-height padding corner
are right, and all M08/K5 data qualify. r ≥ 1: the two countermodels stand
(§2.3, §2.6). The general-order bullet claims only decidability + the
deep-stratum sufficient condition — sound.

### 2.9 The K4 atom-set blindness disclosure (attack item 9, carried) — ACCURATE

(q^{dim}−1) at dim = 1 is literally the atom (p−1), so K1–K4's fitted forms
cannot distinguish a partial-attainment census from a census-atom — the §10
FORM caveat states exactly this, and the form/value split correctly assigns
the fence to the VALUE gates (K5/K6/K7). No overstatement found.

---

## 3. Census-layer audit — CLEAN

* **K7:** script re-executed, log byte-identical (above); exit 0.
* **Byte-stability manifest:** full `diff` rev 3 → rev 4: every hunk falls
  inside the declared repair sites (header/§0-pre/§0 (ADM) + falsifier
  rows + headline; §2's (ADM) block incl. the two warning displays and the
  automaticity bullet; §5.1's header + surjectivity/fiber bullets; §6.3's
  header + on-line bullet; §6.4's header + step-3 parenthetical + the one
  appended validation parenthetical; §7/§9 bracketed tags; §10's header,
  form/value paragraph, K7 block, coverage paragraph; §11; the verdict).
  §§1, 3, 4, 5.2, 5.3, 5.4, 6.1, 6.2, 8 are verbatim rev 3 as claimed. ✓
* **Carried logs:** K6 (`o9_rev3_adm_20260731_194858.log`) still shows
  0 = 0, mod-e 256/26244 REFUTED, positive controls 16/324, ALL PASS ✓;
  the K1–K4 harness log (`o9_census_20260731_165908.log`) still ends
  "K4: cross-p cells=18 … violations=0 / OVERALL: GATE SURVIVES (0
  violations)" ✓; K5 log present and unchanged (pass-3 confirmations
  carried). The §6.4 source cite (`o9_order2_census_check.py` lines
  121–124, the v(a₀) ≥ M parent drop) still matches the source. ✓
* **Pass-3 characterization:** rev 4's header quotes pass 3's verdict
  (UNSOUND — 1 critical, 0 gaps), its verified list, and its repair
  direction accurately against `O9_pass3_verify.md`. ✓

---

## 4. Verdict

**SOUND — 0 critical errors, 1 justification gap (Finding 1: the withdrawn
bijection gloss surviving at the §0 OL-A(iii) row and the §1 (P5) pin, both
non-load-bearing).** The FULL-attainment (ADM) is the first form matching
what the count consumes, its consumption sites are correctly re-pointed,
the r = 1 decidable check and (CLASS-d) are proved as displayed, warning
display 2 and all of K7 are exact (log byte-reproduced from a fresh run),
and the census layer is clean. The honest headline — reduction to (GR-B) +
(FRESH) under the per-datum decidable (ADM), with the disclosed VALUE-gate
coverage limits — stands.

— Pass-4 hostile verifier (fresh context), 2026-07-31.
