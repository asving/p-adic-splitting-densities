# O4T Phase-B brief REV 3 — hostile verification pass 3 (acceptance pass)

**Verifier:** Fable, FRESH context, standalone read of
`lean/notes/openmath/O4T_phaseB_verifybrief_rev3.md` ONLY (no prior pass reports
consulted). Date 2026-07-31. Charge: full clean-pass audit — the pinned classifier and
certificate stability; the n ≤ 3 order arithmetic at wild p = 2, 3; both (CEIL) chains;
the envelope with the Γ-unbounded hypothesis; the EIGHT named classical imports within
their stated scopes; the corrected bracket display; plus the brief's own §7 attack list
(charges 1–11). Protocol: quote-and-classify (CRITICAL ERROR vs JUSTIFICATION GAP), fix
nothing; a ∀-by-example is CRITICAL.

**Verdict (detail below): SOUND-WITH-GAPS** — zero critical errors; two justification
gaps, both minor, both localized to single sentences whose surrounding conclusions are
true and independently re-derivable. Every rev-3 repair checks out. The harness was
re-run in full (all five exhaustive configs, 2,534,851 classes): ALL PASS, and the
regenerated JSON is byte-identical to the sealed
`verification/openmath/results/O4T_transfer_results.json` except for the five
`"seconds"` timing fields (sealed file restored to HEAD afterwards).

---

## 1. Line-by-line audit results

### §1 setting, c^sem, c^K, (K), I-TAIL — VERIFIED

* Definitions of classifier/stability/soundness, `U^c_N`, `env^c` coherent.
* `c^K` and **(K)**: `2v+1 ≤ N ⟺ v ≤ ⌊(N−1)/2⌋ = ⌈N/2⌉−1` checks at both parities;
  `{v_p(disc f_a) ≥ ⌈N/2⌉}` is level-`⌈N/2⌉`-measurable (disc is a Z-polynomial in the
  coefficients) with `⌈N/2⌉ ≤ N`, so the undecided locus is exactly as displayed.
  Notably, (K) as consumed downstream (N3-BRACKET terminal clause) follows from `c^K`'s
  DEFINITION plus measurability alone — `c^K`'s soundness (M05 Lemma D) is consumed only
  by the §1 side remark `U^sem_N ⊆ U^K_N`, which nothing in §§2–3 uses. See GAP-2.

### §2 TR-0 / FLOOR / TR-Q — VERIFIED

* Lemma A: nesting direction correct (`U^c_{N'} ⊆ U^c_N` for `N ≤ N'` is the
  contrapositive of decidedness persisting); continuity from above fine.
* TR-0: sufficiency-only discipline honored.
* FLOOR: sound ⇒ every lift separable of type σ ⇒ `c^sem` decides; contrapositive gives
  the inclusion. Correct. (Well-definedness of `c^sem` as a FUNCTION leans on "separable
  lifts always exist; M05 Lemma B" — displayed in §1; see GAP-2.)
* **TR-Q with the unboundedness hypothesis (V30-critical repair): VERIFIED.**
  `Γ⁻(N) := min{v : Γ(v) > N}` is well-defined exactly because `Γ(v) → ∞` makes the set
  nonempty; `v < Γ⁻(N) ⇒ Γ(v) ≤ N` is minimality (needs no monotonicity); divergence
  `Γ⁻(N) → ∞` uses monotonicity exactly as displayed; the constant-Γ counterexample is
  excluded by the HYPOTHESIS itself, not by prose (§7 charge 7 PASS). The envelope line
  applies (I-TAIL) at `m = Γ⁻(N)` plus `μ{disc = 0} = 0`. Both consumers instantiate
  unbounded majorants: N3-ENV's `Γ(v) = v+1`; TR-OM's OL2 shape displays unboundedness.

### §3.1 the import inventory (EIGHT Facts beyond NP/SF/HEN) — VERIFIED in scope

Each Fact was checked as stated and at each declared consumption site:

* **NP** — sign convention `s = (y_left − y_right)/Δx` = root valuation is internally
  consistent (checked against g = (x−p)(x−1)); vertex no-cancellation standard.
* **SF** — needs DES (not just EXT) for the Z_p-coefficients conclusion; rev 3 supplies
  exactly that. ✓
* **HEN** — standard coprime Hensel + unramifiedness of irreducible-residue lifts. ✓
* **EXT** (unique extension, Galois invariance), **EF** (`ef = [L:Q_p]`, denominator
  divides e), **D** (`disc = ∏(α_i − α_j)²`, whence (D)), **GRD** (graded ring of the
  Gauss valuation is a Laurent domain; initial forms multiply) — all classical, stated
  correctly, consumed only where declared (EF at SIDE(i); D at both (CEIL) chains and
  measurability; GRD at RES only, and only at INTEGER slopes, inside GRD's stated scope).
* **UCT, HRG, SEP, DES** — all four one-line in-brief proofs were checked and are
  correct. (SEP: `gcd(φ, φ′) = 1` since `φ′ ≠ 0` in char 0 and `deg φ′ < deg φ`. DES:
  min poly separable + transitivity ⇒ one root ⇒ degree 1; integrality ⇒ `Z_p`.)
* **Count reconciliation (pass-2 Finding 2 repair): PASSES.** EF and GRD each bundle
  two V30 items; the other four map one-to-one; SEP/DES are new; the named inventory is
  eight Facts. Internally consistent as displayed.
* The parenthetical "(I-TAIL remains the one EXTERNAL named import, §1)" is an
  overcount-in-reverse — see GAP-2.

### §3.2 the pinned classifier — VERIFIED (policy well-defined; all reads are class reads)

* "Digits of any Z-polynomial value in `a` below level `k` are functions of the digits
  of `a` below level `k`" — true; every branch decision (residue factorization, resolved
  set, residual digits) is therefore a class read at the consumed level. ✓
* At n ≤ 3 repeated residue factors are forced linear (dm ≤ 3, m ≥ 2 ⇒ d = 1). ✓
* `d ≥ 2 ⇒ e = 1` since `e·d ≥ 4 > n` otherwise (side length ≤ n ≤ 3): the **order-≤1
  exclusion is purely combinatorial and prime-independent, hence holds at wild p = 2, 3
  and at every refined cluster** (recursion re-enters the same case split). §7 charge 4
  PASS.
* **Observation (not a finding):** condition (C1) is logically REDUNDANT: every
  hull-defining resolved point has height < k, so `H_res(i) < k` automatically at every
  scan level, and (C1) can never fail. The certificate's operative content is `x₀ ≤ 1`
  plus (C2)'s two inequalities. This redundancy is harmless (the soundness proofs use
  the true fact "unresolved ⇒ height ≥ k > H_res(i)", which is what matters), but a
  future reader should not credit (C1) with gating work it does not do.

### §3.3 CERT / RES / RES-0 / SIDE / REC — VERIFIED (one gap in (I1)'s base case, GAP-1)

* **Lemma RES** (§7 charge 5): both unique-minimality claims check out.
  `g_<` (roots of valuation > h): `v(c_j) > (deg−j)h` for j < deg, so the leading term
  is the unique w-minimal one. `g_>` (roots of valuation < h): `v(c_j) + jh > v(c_0)`
  since the j omitted roots each have valuation < h. Position bookkeeping (side occupies
  indices `[deg g_<, deg g_< + d]`, larger valuations to the LEFT) is consistent; the
  on-line-digit identification with `Ḡ` (including off-line ⇒ digit 0 ⇒ `Ḡ_j = 0`)
  closes. ✓
* **Corollary RES-0**: G monic with unit roots ⇒ `Ḡ(0) ≠ 0` (UCT) ⇒ `R(0) ≠ 0`; the
  independent vertex-digit confirmation also checks. §7 charge 3's target — the corner
  is EMPTY. ✓
* **Lemma SIDE**: (i) denominator-exactly-e + EF degree bound + `deg g_{h/e} = e` forces
  irreducibility and type (e,1) — no tameness used anywhere, wild p included. (ii) HEN on
  pairwise-coprime residual powers + HRG root bookkeeping: the m′-count on the side is
  exact; the "no other root" exhaustion is completed in REC. ✓
* **Lemma REC** (§7 charge 3): with `z₀ ≠ 0` (RES-0) the three-case split is exhaustive
  and each case gives `v(α − c′) ≤ h`; (I1) propagates with exactly m′ roots. The
  ultrametric equality cases (minimum uniquely attained) are used correctly in all three
  branches. ✓
* **Lemma CERT** (§7 charge 1): (i) under the rev-3 pinned reading (hull OF THE POINT
  SET WITH INDICES IN `[x₀, n]`) the proof closes in every completion — unresolved
  points sit at height ≥ k, strictly above the resolved hull, hence hull-irrelevant.
  (ii) the completion quantifier survives every corner probed: `v(g_0) ≥ k > y_1 + s_r`
  holds in EVERY completion including `g_0 = 0` (height +∞); `s_r` IS the true right
  slope at that moment because H_res = the true `[1,n]`-hull by (i); the slope
  comparison forces the vertex at (1, y_1) and a length-1 leftmost side; the unique
  max-valuation root is Galois-fixed (EXT) hence Q_p-rational (DES); `k > y_1 + λ_prev`
  puts it in the current cluster. ✓
* **(I1)** — statement true and correctly propagated by REC, but the step-0 base-case
  proof sentence is false as written: **GAP-1** below.

### §3.4 Theorem N3 — VERIFIED (both (CEIL) chains, every corner)

* **Stability and per-lift correctness**: all reads below the certify levels; CERT
  quantifies over completions; any lift of the level-L(f) class runs the identical walk;
  each certificate is true of the lift. ✓
* **Every-lift separability (pass-2 Finding 3 repair; §7 charge 11-ii): VERIFIED.**
  Each certified factor is a monic irreducible factor of the arbitrary completion `g`
  (HEN / EF-degree / rational root); each factor's certified root group is its FULL root
  set; groups are pairwise disjoint across all four separation mechanisms (step-0
  residues; side valuations; residual classes via HRG; recursion depths via REC's
  three-case exclusion); degrees sum to n; the no-double-certification argument (a
  factor's root set cannot lie in two disjoint groups each equal to a full root set)
  closes; product = g; SEP gives n distinct roots. ✓
* **(CEIL) case (a)** `b_1 = b_2`: all `b_j < ∞` (at most one ∞ root); (0, y(0)) is the
  leftmost vertex, resolving exactly at `k = y(0)+1`; the shortcut cannot fire earlier
  (its soundness (CERT(ii)) would force `b_1 > b_2`); the chain
  `k − 1 = y(0) = Σ b_j ≤ 2δ₁₂ + Σ_{j≥3} δ₂ⱼ ≤ 2Σ_{i<j} δ_{ij} = v` is verified
  step-by-step (each `δ ≥ 0` since roots are integral; `δ₁₂ ≥ min(b_1,b_2) = b_1`;
  `δ₂ⱼ ≥ min(b_2,b_j) = b_j`). ✓
* **(CEIL) case (b)** `b_1 > b_2` (§7 charge 2): `y(1) = Σ_{j≥2} b_j` exact (the term
  omitting β₁ is the unique v-minimal one — checked); `b_1 ∈ Z ∪ {∞}` (length-1 side
  between integer-height vertices); `b_1 > b_2 ⇒ b_1 ≥ ⌊b_2⌋+1` at both the fractional-
  `b_2` and integer-`b_2` corners; hence `y(0) = y(1) + b_1 ≥ k`, index 0 stays
  unresolved, including the `b_1 = ∞` (`g_0 = 0`) corner where `y(0) = ∞`. (C2)'s two
  inequalities hold at `k = y(1) + ⌊b_2⌋ + 1` (`⌊b_2⌋+1 > b_2 ≥ s_r`; `⌊b_2⌋ ≥ λ_prev`
  since `λ_prev ∈ Z`, `b_2 > λ_prev`). The chain
  `k − 1 = y(1) + ⌊b_2⌋ ≤ 2b_2 + Σ_{j≥3} b_j ≤ 2δ₁₂ + Σ_{j≥3} δ₂ⱼ ≤ v` with
  `δ₁₂ = b_2` EXACT (strict ultrametric) is verified. ✓
* Residual reads at levels `≤ y(x₀) < k`; termination: `λ_prev` strictly increases
  through integer slope values and any two recursed-cluster roots give
  `λ_prev < δ_{ij} ≤ v/2`. ✓  (§7 charge 6 PASS: every ≤-step direction checked.)
* Hand-checked instances confirming the arithmetic including wild p: `x² − 2` at p=2
  (certifies k=2, type (2,1), v=3); `x² + 2x + 4` at p=2 (k=3 = v+1, sharp, residual
  `z²+z+1` irreducible → (1,2)); `x² + 2x` at p=2 (shortcut with `g_0 = 0`, k=3 = v+1,
  sharp); `x³ − 3` at p=3 (k=2, (3,1), v=5); a depth-2 recursion instance at odd p
  (roots `1, 1+p, 1+p+p²`: shortcut at recursed level, k=6 ≤ v+1=9, verdict (1,1)³). All
  match the walk, the certificates, and the bound.
* **N3-ENV**: `Γ(v) = v+1` nondecreasing and unbounded; `Γ⁻(N) = N`; envelope =
  (I-TAIL) at m = N. ✓

### Corollary N3-BRACKET (the pass-2 CRITICAL repair; §7 charge 11-i) — VERIFIED

* Count chain: left = FLOOR + N3 soundness/stability ✓; middle = (CEIL) contrapositive
  on every separable lift, inseparable lifts having v = ∞ ✓; the middle event is
  level-N measurable ✓; terminal `≤` from the displayed normalization identity.
* **The normalization identity is verified**:
  `undec^K(2N−1) = μ{v ≥ ⌈(2N−1)/2⌉}·p^{n(2N−1)} = μ{v ≥ N}·p^{n(2N−1)}
  = p^{n(N−1)}·(μ{v ≥ N}·p^{nN}) = p^{n(N−1)}·#{middle}`. ✓
* **The density identity is verified**: `env^K(2N−1) = μ{v ≥ N}`. ✓
* **The displayed refutation instance recomputed and confirmed**: n=2, p=2, N=2:
  `a₁² − 4a₀ ≡ a₁² mod 4`, so `v(disc) ≥ 2 ⟺ v(a₁) ≥ 1`, `μ = 1/2`; middle count
  8/16; `undec^K(3) = 32/64`; factor `p^{n(N−1)} = 4`; `8·4 = 32`. ✓
* Downstream consumption audited: §4's rescope display and TR-OM consume only the
  count-inequality / density forms, never a count equality. ✓
* (The parenthetical "equality iff N = 1" is fine: the middle count is always positive —
  the level-N class of a ≡ 0 has `disc ≡ 0 mod p^N` for every lift since disc has zero
  constant term as a polynomial in the coefficients.)
* The in-words gloss states the floor direction correctly (semantic = floor; canonical
  at most as slow as Krasner at double level). ✓

### §4 TR-OM + rescope note — VERIFIED as scoped (conditional; nothing over-claimed)

* TR-OM consumes TR-0 (a.e. finiteness from (AGR) + null disc locus), FLOOR (soundness/
  stability quoted as Lean-law assumptions), and — for the envelope — an OL2 majorant
  with the unboundedness hypothesis displayed. Coherent as a conditional statement.
* **Scope audit (§7 charge 8): PASS.** No §2–§3 proof consumes (AGR), CU-*, GD-≥2, GMN
  termination, or BNS. §3's proofs stand on NP/SF/HEN + EXT/EF/D/GRD/UCT/HRG + SEP/DES
  (+ I-TAIL for N3-ENV via TR-Q). The count-reconciliation map is internally consistent.
* **Rescope note (§7 charge 10): PASS**, with one strengthening remark the brief could
  have made but does not need: the charged direction
  `undec_OM(N) ≤ undec_sem(N + shift)` is in fact REFUTABLE in density form without
  numerics — FLOOR + monotonicity squeeze `env_sem(N) ≤ env_OM(N) ≤ env_sem(N+s) ≤
  env_sem(N)` would force `env_sem` constant in N, contradicting drainage plus
  `env_sem(1) > 0`. The note's numerics-based density refutation (honest, and labeled as
  an observation) plus the rescope to N3-BRACKET is correct as displayed; the raw-count
  normalization discipline (pass-2 Finding 5 repair) is now right.

### §5 numerics (§7 charge 9) — RE-RUN AND REPRODUCED

* `python3 O4T_transfer_check.py --quick` PASS; full run (all five configs, 2,534,851
  classes, ~78 s) **ALL PASS**, per-config `P1/P2/P3/P4 fails = 0/0/0/0`,
  `env/mono fails = 0/0`, and `max(L − v − 1) = 0` in EVERY config (the P3 sharpness
  claim confirmed).
* The regenerated results JSON differs from the sealed
  `results/O4T_transfer_results.json` ONLY in the five `"seconds"` fields — an
  independent byte-level reproduction of all substantive content. (The sealed file was
  restored to its committed state after the comparison.)
* Docstring preregistration = brief §5's P1–P6 = the JSON's `preregistered` field. ✓
* Every headline table number in §5 was checked against the sealed JSON: n=2 p=2 OM/sem
  columns equal through N=10 (9.766e-4), K row `.5 .5 .5 .5 .25 … .0625`; n=2 p=3 and
  p=5 rows exact; n=3 p=2 sem-lower `.5 .1875 .09375 .04052734375 0`; n=3 p=3 sem-lower
  `.3333 .08642 .028196921 0`. All match (the brief's `.02820` is the rounded
  `.028196921…`). Total classes 2,534,851 ✓.
* Harness-vs-§3.2 conformance spot-checked in source: the certify loop implements
  exactly (C1) + (C2) with `s_r` = first resolved-hull slope, the `λ_prev`-strict side
  harvest, the on-line residual digit read, and the recursion `(c + z₀p^h, m′, h)`. Two
  defensive branches (`ell % e != 0` rescan; `hull[0][0] > 1` continue) are unreachable
  for true hulls and harmless.

### §6 ledger — consistent with the audit; no unlabeled claim found. ∀-by-example scan:
none. The two numerics-only observations (n=2 semantic exactness; BNS shape match) are
explicitly labeled observations/flagged-consistency, not theorems.

---

## 2. Findings (quote-and-classify)

### GAP-1 — JUSTIFICATION GAP (minor, localized): false clause in (I1)'s step-0 proof

§3.3, Invariant (I1), base case:

> *Proof of (I1) at step 0*: the roots reducing to the repeated residue `r` are exactly
> those with `v(α − r) ≥ 1 > 0`; multiplicity of `r` in `f̄` = the count.

The set identity "reducing to r ⟺ `v(α − r) ≥ 1`" is FALSE in general: reduction to r
is equivalent to `v(α − r) > 0`, and root differences take FRACTIONAL valuations in
(0, 1). Concrete refutation: `f = x² − p` (any p), `f̄ = x²`, r = 0, both roots `±√p`
reduce to 0 with `v(α − 0) = 1/2 < 1` — the displayed criterion counts 0 roots against
multiplicity m = 2. The invariant's STATED conclusion (`#{v(α − c) > λ_prev} = m` at
`λ_prev = 0`) is true via the correct criterion `v(α − r) > 0`, which is also the only
form anything downstream consumes (the case (a)/(b) arithmetic uses `b_2 > λ_prev`
only; no later step uses `b_j ≥ 1`). Classification: justification gap, not critical —
the false clause is inside a proof, nothing depends on the "≥ 1" form, and the one-line
correct derivation ("ᾱ = r ⟺ α − r ∈ 𝔪 ⟺ v(α − r) > 0") restores the chain. (Same
class as V30 finding 2's false in-proof sentence, which V30 classified as a gap.)

### GAP-2 — JUSTIFICATION GAP (minor, prose/inventory): "the one EXTERNAL named import" undercounts

§3.1, closing parenthetical:

> (I-TAIL remains the one EXTERNAL named import, §1 — V30: "as acknowledged".)

Two further external, quoted-not-proved imports live in §1 and are consumed by the
package: **M05 Lemma B** ("separable lifts always exist"), which is what makes `c^sem` a
well-defined FUNCTION (without it, an all-inseparable class would satisfy the deciding
condition vacuously for every σ) — consumed by FLOOR and hence by N3-BRACKET's left
clause; and **M05 Lemma D** (Krasner–Hensel local constancy), which underwrites `c^K`'s
soundness and the §1 remark `U^sem_N ⊆ U^K_N` — though notably NOT the (K) identity
that N3-BRACKET's terminal clause actually consumes (that follows from `c^K`'s
definition plus class-measurability alone). Both imports ARE displayed in §1 with named
pins and verification tags, so nothing is hidden; but the counting sentence, read
standalone, overstates the inventory's completeness in exactly the direction pass 2's
Finding 2 policed. Scoped strictly to §3's PROOFS the sentence is defensible (no §3.3
lemma or (CEIL) step touches Lemma B or D); as an unscoped package-level claim it is
inaccurate. Classification: justification gap (overstatement), no mathematical content
at risk.

---

## 3. §7 attack-list scorecard

| charge | result |
|---|---|
| 1 CERT(ii) completion quantifier, `g_0 = 0`, s_r trueness | PASS |
| 2 case-(b) `y(0) ≥ k`; `b_1 = ∞` and fractional-`b_2` corners | PASS |
| 3 REC `z₀ = 0` corner via RES-0; three-case split | PASS |
| 4 `e·d ≥ 4` exclusion at wild p and refined clusters | PASS (prime-independent) |
| 5 RES monomial bookkeeping, both unique-minimality claims | PASS |
| 6 (D) and every ≤-step in both (CEIL) chains | PASS |
| 7 TR-Q `Γ⁻` off-by-one + unboundedness placement + consumers | PASS |
| 8 no silent (AGR)/CU-*/GD-≥2 consumption; inventory map | PASS (with GAP-2's prose caveat) |
| 9 harness re-run, preregistration vs docstring vs sealed JSON | PASS (reproduced; timings-only diff) |
| 10 rescope-note direction + normalization discipline | PASS (an even stronger abstract refutation exists) |
| 11 rev-3 repairs: bracket identity/density; separability chain; index-range hull | PASS / PASS / PASS |

Non-finding observations for the record: (C1) is logically redundant (can never fail;
the operative gate is `x₀ ≤ 1` + (C2)); the §3.2 residual definition reuses the symbol
`y₁` for the side's left-endpoint height (notation overload with `y_1 = y(1)`,
unambiguous in context).

---

## VERDICT: SOUND-WITH-GAPS

Zero critical errors. The entire mathematical core — the pinned §3.2 policy and its
stability, CERT/RES/RES-0/SIDE/REC, both (CEIL) chains at every probed corner including
wild p = 2, 3, the `e·d ≥ 4` exclusion, TR-0/FLOOR/TR-Q with the unboundedness
hypothesis, N3-ENV, the corrected N3-BRACKET (count inequality + normalization identity
+ density identity), the every-lift separability chain, the eight-Fact import inventory
with its count reconciliation, and the §4 rescope — survives line-by-line audit, and the
preregistered numerics reproduce exactly. The two justification gaps are single-sentence
repairs: (GAP-1) replace `v(α − r) ≥ 1` by `v(α − r) > 0` in (I1)'s base-case proof;
(GAP-2) rescope or extend the "one EXTERNAL named import" sentence to name M05 Lemmas
B and D as the other two displayed external imports (with their exact, limited
consumption sites). Neither gap touches any displayed theorem statement, either (CEIL)
chain, or any downstream consumer.
