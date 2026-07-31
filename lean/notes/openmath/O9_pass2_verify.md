# O9 Phase-B verify brief REV 2 — hostile verification, PASS 2 (fresh context, 2026-07-31)

**Charge.** Re-pass after the rev-2 repair of `O9_phaseB_verifybrief_rev2.md`: verify
the two repairs line by line (the E′ strict left tail; the JUNCTION-PIN rescope to
(FRESH)(c)), the new (ADM) hypothesis, the displayed (E″), then a standard audit of the
census layer. Quote-and-classify (CRITICAL ERROR vs JUSTIFICATION GAP); fix nothing.
Read only the rev-2 brief (no prior reports); cited falsifier artifacts (scripts, logs)
were checked at source, and key claims were re-derived or re-brute-forced independently
(verifier's own code, not the brief's scripts).

**Verdict (stated up front): UNSOUND — 1 critical error, 3 justification gaps.**
Both pass-1 repairs under re-verification are themselves SOUND (details below). The
critical error is in the NEW (ADM) hypothesis: its displayed definition rests on a false
equivalence between class-attainment and value-attainment of β_k, and under either
disambiguation a displayed claim of the brief is false — the pass-1 G3 bug (positive
formula on an empty stratum) reappears through the hole. The fix looks local (strengthen
(ADM) to G_{β_k} ≠ 0 with the correct criterion; rescope the order-≤1 automaticity),
but per the charge nothing is fixed here.

---

## 1. Repair 1 — the (STRICT) left-tail threshold: VERIFIED SOUND

Checked line by line against §2, §5.2 + rev-2 note, §6.3, and K5.

* **Correctness of ⌊L⌋+1.** u_k ∈ ℤ, so u_k > L_k ⟺ u_k ≥ ⌊L_k⌋+1 uniformly —
  equal to ⌈L_k⌉ at non-integral L_k, strictly larger at integral L_k. ✓
* **Within-face agreement.** At off-line slots k = k_{S−1} + je_S + t, 0 < t < e_S,
  the line value is (integer) − t·h_S/e_S with gcd(h_S, e_S) = 1, hence non-integral, so
  ⌊L⌋+1 = ⌈L⌉ there and rev 0's within-face slots are unchanged, exactly as claimed. ✓
* **(DET) still suffices.** kV̂ ∈ ℤ gives β_k = ⌊L_k − kV̂⌋ + 1 ≤ (eN−1) + 1 = eN,
  inside LED(i)'s inequality-only scope (the well-definedness argument at β = eN — adding
  π^N b shifts every coordinate weight by ≥ eN — checks out); digit reads keep β ≤ eN−1. ✓
* **The keying rationale.** At an integral left-tail value, u_k = L admits face 1
  extending to a left endpoint at k — under §2's keying a different stratum (larger
  d(1)); rev 0's ⌈L⌉ counted u_k ≥ L. Verified against the countermodel by hand and by
  independent brute force (my own code, `/tmp/o9_indep_check.py`): r = 0, q = 2, N = 4,
  free box ℓ = 3, D = (2,1)→(3,0): conditions v(a₀) ≥ 4, v(a₁) ≥ 3, v(a₂) = 1 (digit
  ≠ 0), v(a₃) = 0 (digit ≠ 0) give 1·2·4·8 = **64 = 2⁶** (E′ = 6 ✓); rev-0 thresholds
  give 2⁸ = **256** ✓. I also independently brute-forced the MONIC-LT case
  ((1,2)→(3,0), monic top): 8 per type, matching E′ = 3 and the K5 log. ✓
* **K5 (predict-from-ledger).** Script + log exist
  (`o9_rev2_ledger_predict_check.py`, `logs/o9_rev2_ledger_predict_20260731_175221.log`);
  the log matches the brief exactly: 11 (D,λ) cells over 7 data, ALL PASS, rev-0 formula
  refuted at all 8 integral-left-tail cells (256; 128 ×4; 16 ×2; 324 vs truths 64 ×5;
  8 ×2; 108), M08 c_i regression E′_monic = Σ(N−c_i) PASS. The brute-force membership is
  an independent reimplementation of §2's strict keying (strict `>` at 'lt'/'off' slots
  with the valuation capped at N — sound under (DET) since L ≤ N−1; exact valuation +
  nonzero digit at vertices; free digit at interior on-line slots; non-strict tails). ✓
* Attack item 6 (deep steeper faces): both the formula and the K5 brute force GROUP
  visible steeper deep faces at k < k₀ into the stratum (only u_k > extended-line is
  imposed) — e.g. tuples with u₀ = 4 in the countermodel (hull would start (0,4)→(2,1),
  slope −3/2) are counted by both. Consistent with the left-tail cutoff convention. ✓
* Coverage note (no finding): all 7 K5 data are SINGLE-face (2 vertices). The
  shared-vertex/multi-face VALUE accounting of E′ (one −d per shared vertex + the
  Lemma C/D telescope) is untested by K5; §10's coverage-honesty paragraph does not say
  so. Minor disclosure miss, folded into the queued order-2 predictor's scope.

## 2. Repair 2 — the JUNCTION-PIN rescope: VERIFIED SOUND (one stale label, Finding 3)

* The PROVED label is withdrawn consistently: §0 status row files the pin as
  "(FRESH)(c) … OPEN"; §5.4 clause (c) carries it as a hypothesis clause; the mechanism
  note is labeled "NOT A PROOF" and honestly names the missing step (graded-level →
  finite-level digit transport = the GD-2/VTX layer). ✓
* Attack item 7 (is the mechanism note consumed as a proof anywhere in §§6–8?): NO.
  §6.3's ε = 0 branch pins the end by MONICITY (a_ℓ = 1, read the constant 1 ≠ 0) —
  window-internal, legitimately proved, not clause (c). §6.4 step 3 cites (FRESH)(c)
  explicitly as hypothesis. §8's residue list names (FRESH). ✓
* The telescope consequence given (c) — exactly ∏M, no stray (q^d−1), via Lemma D
  pinned-end + Lemma C (value-irrelevance: only nonvanishing + fixedness enter) — is
  correctly scoped as "PROVED given the clause". ✓
* CEN-J's conditionality "(GR-B)+(FRESH)" unchanged: correct, the pin was a subset of
  (FRESH) all along; only §7/§0's OL-D row missed the propagation — **Finding 3 below**.
* ε = 0 on the 18 cross-p cells restated as shape-forced/non-discriminating in the §10
  headline ✓ (log confirms every fitted exponent vector has zero (p−1)- and
  (p^g−1)-exponents, i.e. all tested cells are monic-top).

## 3. The new (ADM) hypothesis: **CRITICAL ERROR**

### Finding 1 — CRITICAL ERROR (§2 (ADM); consumed at §6.3/§6.4; propagates to §0 and the headline)

Quote (§2, the definition):

> "Say D is *ledger-admissible* if every on-line lattice slot's β_k is attained by the
> slot ledger: β_k mod e ∈ {wt(𝐣) mod e : 𝐣 a ledger index} — equivalently G_{β_k} ≠ 0
> (LED(iii))."

The "equivalently" is FALSE. By LED(ii)/(iii), dim G_β = s(β+1) − s(β) =
#{𝐣 : wt(𝐣) ≡ β (mod e) **and wt(𝐣) ≤ β**}. The mod-e condition drops the second
conjunct. The supporting bullet contains the conflation site:

> "the w-values attained on {deg < m} \ {0} are exactly {e·v + wt(𝐣) : v ≥ 0}, i.e.
> the classes {wt(𝐣) mod e} and nothing else"

— the displayed SET is correct, but its members are {β : ∃𝐣, β ≡ wt(𝐣) (e), β ≥ wt(𝐣)},
not all of the attained classes' members: membership of a specific β needs β ≥ wt(𝐣)
for the witnessing 𝐣.

**Countermodel (machine-checked arithmetic).** r = 1 type: f₀ = f₁ = 1, e₁ = 3, h₁ = 2
(λ₁ = −2/3). Then m = 3, d = 1, e = 3; ledger = {1, φ₁, φ₁²} with weights {0, 2, 4}
(w(φ₁) = e₁V₁ + h₁ = 2, V₁ = 0, per the pinned (P3) — attack item 5 verified);
V̂ = e₁f₁·(e₁V₁ + h₁) = 6. Attained w-values on {deg < 3}\{0} are
{3v} ∪ {3v+2} ∪ {3v+4} = {0,2,3,4,5,6,7,8,…} — **1 is not attained**, although
1 mod 3 = 1 IS an attained class (4 ≡ 1). Take the order-2 stratum datum D with the
single face (0,8)→(1,7) (slope −1, e_S = 1, d(S) = 1, λ = {(1,1)}), free box, ℓ = 1,
N = 3 ((DET): max = 8 ≤ eN − 1 = 8 ✓). Then β₀ = 8 (attained), β₁ = 7 − 6 = 1
(vertex, UNATTAINED, G_1 = 0 since s(2) = s(1) = 1). The stratum is EMPTY — by TRI
alone, no (GR-B) needed: the vertex needs w(a₁) = 1. But:

* under the displayed mod-e reading, D **is** ledger-admissible (β₀ ≡ 2, β₁ ≡ 1, both
  ∈ {0, 2, 1}), and CEN-W's display gives q^{E′}(q^d−1)∏M = q⁸(q−1)·M > 0 ≠ 0
  (s(8) = 7, s(1) = 1, E′ = (9−7)+(9−1)−2 = 8). The theorem as stated is false — the
  pass-1 G3 bug shape (positive formula on an empty stratum), inside the repair meant
  to fence it;
* under the corrected reading (G_{β_k} ≠ 0), the same datum refutes the displayed claim
  "**(ADM) is AUTOMATIC at orders ≤ 1**" (§2; propagated to the §0 status row
  "automatic at orders ≤ 1 (proved, §2)" and to the honest headline "automatic at
  orders ≤ 1"): the r = 1 argument proves CLASS coverage ({j₁h₁ mod e₁} = everything ✓,
  that step is fine) but not VALUE coverage, which fails at β₁ = 1 here.

The consuming step in §6.3 —

> "the surjectivity behind it needs β_k attained, which is (ADM) + (GR-B)"

— is therefore a false inference under the displayed (ADM) (attainment is a
(GR-B)-free ledger fact, and mod-e (ADM) does not imply it); §6.4 step 3 consumes the
same hypothesis ("surjectivity = (ADM) + (GR-B)"). Classification: **CRITICAL ERROR** —
it breaks the logical chain of CEN-W and CEN-J as stated (and the automaticity claim is
a proved-labeled ∀-claim with a counterexample). Damage assessment (not a fix): the
r = 0 instance is untouched (e = 1: class = value attainment, so K5 and the M08
recovery stand); the repair is plausibly one line (define (ADM) as
∃𝐣: wt(𝐣) ≡ β_k (mod e) ∧ wt(𝐣) ≤ β_k, i.e. G_{β_k} ≠ 0, and rescope automaticity to
r = 0 + a per-datum r = 1 check), but rev 2 as written does not contain it.

## 4. The displayed (E″): VERIFIED, modulo Finding 1 and one wording gap

* Display audit: E″ = n(N−N₀) − Σ_{k∈K_D} max(0, s(β_k) − s(g_k)) − d·L′ is genuinely
  displayed with one named open ingredient (the (FRESH)(a′) floors g_k); the
  non-circularity claim is honest — g_k's existence/shape-dependence is priced to
  (FRESH)(a′), and the rev-0 "E′ minus parent's charge" gloss is demoted to a remark. ✓
* Proof steps 1–5 re-checked: step 1's fiber count (#parent at N₀)·q^{n(N−N₀)} ✓ (monic
  degree-n f mod π^N has n free coordinates); step 2's relative charge
  q^{−max(0, s(β_k)−s(g_k))} is the correct LED(ii) ratio on the (a′) product box, with
  g_k ≥ β_k slots charging nothing ✓; step 3's per-digit q^{−d} with L′ = L − [k_s ∈ K_D]
  and the ρ-pinned end charged to the parent ✓ (consistent monic-top special case);
  step 4 = imported Lemma C + pinned-end Lemma D at F_{q^d} ✓; step 5 assembles to (E″)
  exactly ✓. Attack item 3: given (a′)'s "amount to per-slot floors + pin" (a full
  product box) the fiber's digit uniformity follows from §5.1, so (b) as displayed is
  strong enough for step 3; no separate joint-distribution clause is needed beyond what
  (a′)+(b) jointly assert. Attack item 4: step 1's "(DET) over the parent's own reads"
  is exactly the level-N₀ determinacy used, carried as a standing hypothesis — fine.
  Step 3's surjectivity inherits **Finding 1**.
* **r = 0 validation re-derived**: with m = d = e ... = 1, V̂ = 0, N₀ = 1, g_k = 1,
  monic top (L′ = #lattice slots i < e): non-lattice slot charge ⌈Δ(i)⌉ − 1 = c_i − 1;
  lattice slot (Δ(i) − 1) + 1 = c_i − 1 (c_i = Δ(i)+1, the +1 = the read); E″ =
  e(N−1) − Σ(c_i − 1) = Σ(N − c_i). Arithmetic exact as displayed; K5's independent
  m08_ceils regression confirms at (0,3)→(3,0): c = [4,3,2], Σ(N−c) = 3 = E′_monic. ✓

### Finding 2 — JUSTIFICATION GAP (§4, Lemma LED-top(ii); false as written, verified non-load-bearing)

Quote:

> "(ii) [below the anchor] for β < w*, β ≤ eN − 1: the graded read on the coset is
> r_β(a) = r_β(b) — §5.1 applies verbatim on the sub-ledger (fiber-uniform onto
> F_{r+1} iff β is attained in the SUB-ledger)."

The parenthetical is false: attainment in the sub-ledger makes the read fiber-uniform
onto its IMAGE, the F_q-subspace V of dimension s′(β+1) − s′(β), which can be a proper
subspace of F_{r+1}. Counterexample: f₀ = 1, e₁ = 1, f₁ = 2, h₁ = 2 (so m = 2, d = 2,
e = 1, m′ = 1, 𝐣* = (0,1), w* = 2); β = 1 < w*: β is value-attained in the sub-ledger
{1} (wt 0), yet r_1(W′ ∩ {w ≥ 1}) = F_q·in(π) — an F_q-line in F_{q²}, dim 1 < d = 2.
Not surjective onto F_{r+1}. Classification: GAP, not critical — the lemma's own
consumption note bars exactly this clause's strong form ("the top slot's read is NOT
F_{r+1}-fiber-uniform in general"), and I verified §6.4 consumes only (i)'s counts +
(iii)'s non-vanishing; nothing downstream uses (ii)'s surjectivity. The clause must be
weakened to "fiber-uniform onto its image subspace".

(Attack item 2, resolved in the brief's favor: LED-top(iii)'s non-vanishing does hold —
the in-forms of the same-class monomials π^{(β−wt)/e}B_𝐣 are F_q-independent in G_β
because a vanishing combination would have w > β, contradicting TRI's EXACT min; the
dimension count of LED(iii) is this coordinate decomposition, so the attribution is
legitimate.)

### Finding 3 — JUSTIFICATION GAP (§7 + §0 OL-D row; stale conditionality after the C2 rescope)

Quotes:

> (§7) "given (GR-B), a one-window count from ANY representative of t has the CEN-J
> shape, and Lemma C makes the count independent of the representative's fixed residues
> (they enter only as fixed nonzero ν-arguments and junction pins)"

> (§0, OL-D row) "the order-r Remark-2.7 analogue displayed, (GR-B)-conditional"

CEN-J's shape requires (GR-B) **+ (FRESH)** (+ (ADM)): the junction pin is now the OPEN
(FRESH)(c) and the fresh reads are (FRESH)(b). Under rev 0's PROVED pin "given (GR-B)"
was arguably fine; rev 2 withdrew the label but left §7 byte-stable and repeated the
(GR-B)-only pricing in the rev-2-edited §0 table. The under-pricing is exactly the
pass-1 C2 accounting class, surviving at one site. OL-D is anyway OPEN, so no proved
claim breaks: GAP.

### Finding 4 — JUSTIFICATION GAP (minor; §2, CEN-J statement)

Quote:

> "with g_k ≤ β_k at on-line slots (else the stratum is empty and both sides are 0)"

As displayed, the right side (#parent)·q^{E″}·∏M is NOT 0 when g_k > β_k at an on-line
slot; "both sides are 0" parses only under §8's zero-padding convention ("0 on empty
fibers"), which is not imported into the theorem statement. The parenthetical should
either restrict the equation's scope or state the padding convention. Minor.

## 5. Standard audit of the census layer (§§1, 3–6, 8–9)

* §1 indexing, INDEX FLAG, pinned imports: internally consistent; d = f₀⋯f_r vs f̄_r
  correction coherent with the harness instance (f₀ = 1, d = g). ✓
* §4 A1 ✓ (monic division is O-linear; unitriangular ledger change of basis ✓).
  TRI ✓ — induction re-checked: (P2) at order r+1 splits over φ_r-digits, (P1)+Lemma
  2.2(2) rescales deg < m_r, e_r·wt_r(𝐣') = w(B_{𝐣'}) via (P1) on the monomials, and
  wt additivity is w-valuation multiplicativity; the exact-min (no cancellation) form is
  what Findings 1–2's countermodels lean on. LED (i)–(iii) ✓ (the ⌈(β−wt)/e⌉ coordinate
  count and the dim formula both re-derived). LED-top (i), (iii) ✓; (ii) = Finding 2.
* §5.1 ✓ as an explicitly (GR-B)-conditional statement (additivity fine; surjectivity
  honestly pinned to (GR-B)(2′)'s slot clause with (P5) demoted to corroboration).
  §5.2 + rev-2 note ✓ (attack item 1 discharged, see §1 of this report). §5.3 ✓
  (display-only). §5.4 see §2 of this report.
* §6.1 TYPE-MARCH ✓ — re-derived R̃(y) = τ₀R(ρy); the F₃ warning countermodel
  recomputed: (y+2)² = y² + 4y + 4 = y² + y + 1 ✓; 2y² + y + 1 ∼ y² + 2y + 2,
  discriminant −4 ≡ 2 a non-residue mod 3, irreducible ✓.
* §6.2 ✓ (Lemmas B/C/D are abstract-F_Q statements; evaluation at Q = q^d keeps one
  polynomial in q).
* §6.3 ✓ modulo Finding 1 (the strict/tail/on-line slot accounting and the ε dichotomy
  re-checked; free-box countermodel: Z_D = (q−1)² = (q^d−1)·M_{(1,1)}(q) ✓).
* §6.4 ✓ modulo Findings 1, 4 (see §4 of this report). The C1-downstream resolution is
  verified AT SOURCE: `o9_order2_census_check.py` line 122 `if vs[0] >= M: return None`
  inside `parent_data` (brief cites lines 121–124 ✓) — the level-1 keying indeed drops
  every left-tail box, so K1 never keyed a left-tail stratum and "r = 0 IS M08 Thm 2"
  correctly rescoped to k₀ = 0 data.
* §8 ✓ (assembly display only; residue list names (GR-B), (FRESH), OL-D, pack build —
  with Finding 1, (ADM)-as-corrected must be added to the §8 cell-evaluation
  discipline, which §8 already gestures at via "0 on empty fibers").
* §9 ✓ (rows match the rev-2 statuses, except OL-D — Finding 3).
* §10 falsifier record: headline numbers INDEPENDENTLY RE-SUMMED from the on-disk log
  `logs/o9_census_20260731_165908.log`: boxes 8,220,994 ✓, order-2 instances 1,128,288 ✓,
  K1 strata 100 ✓, cross-p cells 18 (one at g = 2) ✓, 0 violations ✓, 10 configurations ✓.
  The form/value split and the two disclosed weaknesses (ε = 0 shape-forced; p ∈ {2,3}
  underdetermination at the 9 degree-≥2 cells) are accurately stated. Bookkeeping nit
  (no finding): §10 says "RUN (2026-08-01, …)" while the brief is dated 2026-07-31 and
  the on-disk log is timestamped 20260731_165908; all numbers match that log.
* Attack item 8: outside-atom values (e.g. the /2 in irreducible-quadratic counts) are
  absorbed BEFORE K4 by the K3 normalization (census/∏M), so a genuine census cannot be
  mis-PASSED by atom choice; the residual small-prime accidental-fit risk is exactly the
  disclosed p ∈ {2,3} underdetermination. No finding.

## 6. Verdict

**UNSOUND.**

* CRITICAL (1): §2 (ADM) — the definition's "equivalently G_{β_k} ≠ 0" is a false
  equivalence (class- vs value-attainment); under the displayed reading CEN-W/CEN-J are
  false (explicit empty-stratum countermodel at r = 1: e₁ = 3, h₁ = 2, weights {0,2,4},
  on-line β = 1, D = (0,8)→(1,7), formula q⁸(q−1)M > 0, truth 0 by TRI); under the
  corrected reading, "(ADM) is AUTOMATIC at orders ≤ 1" (§2, §0 table, headline) is
  false at the same datum. The pass-1 G3 repair is incomplete.
* GAPS (3): LED-top(ii)'s surjectivity parenthetical (false as written,
  non-load-bearing); §7/§0 OL-D's stale (GR-B)-only conditionality (missed C2
  propagation); CEN-J's "both sides are 0" parenthetical (needs the §8 padding
  convention imported).
* Confirmed sound in this pass: the (STRICT) repair (line-by-line + two independent
  brute-force reproductions), the junction-pin rescope's honesty (labels + non-use of
  the mechanism note in §§6–8), the displayed (E″) and its r = 0 validation arithmetic,
  A1/TRI/LED/LED-top(i)(iii), §5.1–5.3, TYPE-MARCH (+ its F₃ countermodel), §6.2's
  import, §6.3/§6.4's accounting modulo (ADM), the K5 record (log-exact, membership
  semantics independently re-checked), and every §10 headline number against the
  on-disk logs.

— O9 pass-2 hostile verifier, fresh context, 2026-07-31.
