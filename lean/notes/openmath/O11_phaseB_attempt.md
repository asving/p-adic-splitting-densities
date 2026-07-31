# O11 — SERIES-TIE ASSEMBLY: the per-σ tree-series = R_σ value tie — Phase-B unit (Fable, 2026-08-02)

**Unit type: ASSEMBLY over named proved pieces** (the CU-cluster/CUC precedent:
statements + proofs-by-citation + one assembly walk; the ONE new proof-shaped
content is the re-priced Theorem O11 walk of §3, whose glue core was already
proved self-contained in M04). Charge (tree DELTA-2 §D2.6 step 8, node O-11 at
the DELTA-1 **D-9 corrected dependency set**): assemble the per-σ tie
"σ-graded tree series of T_can = block-solve value R_σ" from O-10 (D-8-guarded,
now PROVED sharper), O-5 + the D-7 triple (O5triple, 0-critical), O-8b/O-9
(transition weights; O-9 now REDUCED to zero new inputs), the mass bridge
(Dfloor VERIFIED / D-11 pending), and T-7s — with EVERY consumption displayed
and the residue named. Skeleton: the M04 attempt's interface-level equivalences
(`M04-series-tie_fable.md`, Theorems 1/2/4 + Lemmas 3.1–3.3 + Finding F1).

Falsifier ran FIRST: `verification/openmath/o11_seriestie_check.py` (§7) —
including Finding F1's test EXECUTED AT THE REAL PACK (the M04 charge's own
falsifier line): the real n = 2 solve reproduces the true triple
(p/(2(p+1)), p/(2(p+1)), 1/(p+1)) IDENTICALLY in ℚ(q).

Sources read in full: `M04-series-tie_fable.md` ·
`docs/MATH_COMPLETION_TREE_2026-08-01.md` (O-11, D-8/D-9/D-11/D-15, DELTA 2) ·
`O10_phaseB_attempt.md` · `O9_phaseB_attempt.md` (+ verifybrief §§ cited) ·
`O5triple_phaseB_verifybrief_rev3.md` §0 · `Dfloor_phaseB_verifybrief_rev2.md`
§0 · `CU_cluster_phaseB.md` (§§0, 2, 8) · `O12_phaseB_verifybrief_rev4.md`
(Thm 1/Cor D sites) · `O1thr_phaseB_verifybrief_rev3.md` (Thm 3 = D-15) ·
ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md` through WAVE 8 + commits
4d109b9/252f34c (GD23/CU-1 pass-2s). No Lean file is touched.

## 0. Verdict and the residue display (the headline)

**VERDICT: ASSEMBLED — PROVED-UNVERIFIED conditional on exactly FOUR named
open items.** Theorem O11 (§3) proves the row at the intended instantiation
with every consumption displayed (§5 table). The **tier-1 mathematical
residue** — what must close for the tie to be an unconditional theorem — is:

> **(GR-B)** — the order ≥ 2 side-residual/carry-algebra package (GD-2/GD-3's
>   one open input; GD23 §7.2; order ≤ 1 PROVED over an arbitrary complete
>   DVR). Enters through THREE faces here: the (I-τ)/K-LOC engine
>   presentation of K1, the census weights of K3 (O-9 CEN-W), and the
>   unramified-pool re-base slice (O-8b's (R1)–(R4), §3.4).
> **(FRESH)** — the joint-with-parent level-determinacy separation (O-9's
>   named clause, priced at the GD-2/CL-13 vertex-law layer = CU-1's step
>   content). Enters through K3's joint census CEN-J.
> **CU-2t** — the terminal seam (one unexecuted corollary-grade lemma,
>   CU cluster §2): verdict-carrying terminal records are FORCED by
>   (f, prefix). Enters through K1's leaf verdict labels and K4's decided
>   classes.
> **D-11 (PENDING — unit in flight, cite-as-pending per dispatch)** — the
>   instance pin: the intended pack's kernel entries ARE the Haar volumes of
>   the T-3/T-6 continuation events, its block system is 𝔅_n (or covered by
>   O-12 Theorem 3's robustness), per-box lift uniformity via O5triple Thm E
>   + D-15 (the WAVE-8 pricing). Enters through K2 (escape at the pack), K3
>   (measured weights = table evaluations), and the wiring fence of §2.4.

This matches the dispatch's expected set {D-11 pending, (GR-B), (FRESH),
CU-2t} exactly — nothing smaller was achievable: each of the four is consumed
at a displayed step below, and no fifth mathematical open is consumed.

**Tier-2 displays (NOT new mathematics; carried per the honesty discipline):**
inherited perimeters — D-12r (rides every TB-CAP window consumed here, via
CU-2t/D-15); the O5triple five flags (GMN-COH)/(R-0)/(R-1)/(R-2)/(R-3) =
GD-1/GD-7/GD-8 literature-transcription duties (owner: the GD campaign's
literature surface; NOT covered by the executed LITUNIT); LIT-1's
LITERATURE-CONDITIONAL grade (§D1.5(b)) — and the pending-pass registry (§6):
P(O-2a r5), P(O-1thr r4), P(O5t r3), the GD23/CU-1 pass-2 gap repairs (both
0-critical), the owed hostile passes on O-10/O-9/THIS unit, and the M04
core's verification-only round (tree §4 roster). (E-N) is displayed NOT
consumed (§3.1 note). Nothing in tier 2 adds an open lemma; each is either a
verification duty or an inherited perimeter already displayed at its owner.

## 1. The target statement

Lean row (normative form, `lean/LeanUrat/MovesU/BridgeKernels.lean:223–224`):

```lean
series_tie : ∀ σ : SplittingType n,
    F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))
```

Mathematics (the [3t] ↔ [3] solve seam, per-σ): for every splitting type σ
of degree n and every prime p,

> **(TIE_σ)**  Σ_{T ∈ Trees_σ(T_can)} mass(T)  =  R_σ(p)  in [0, ∞],

where the left side sums the fiber masses of the complete realizable
canonical trees of type σ (the σ-graded tree series) and R_σ = Rval(vmap σ)
is the σ-entry of the finite block solve over ℚ(q) evaluated at q = p.

**The D-9 re-owning, executed.** Per DELTA-1 D-9 (V6 findings 18/24): T-7 is
SPLIT — T-7s (the symbolic tables + obligations ledger, VERIFIED-DUAL) is an
input; the **[1v]-FULL value-correctness event is THIS unit's goal content**,
not an input (K3 was struck from O-11's input list because T-7 had routed its
open value content here). §3.4 is where [1v]-FULL is assembled. D-9k (K2-SEM,
the semantic escape input) is consumed at §3.3 with its two-scope pricing.

## 2. The skeleton consumed from M04 (statuses displayed)

All four M04 pieces are consumed at statement level; their grade is
PROVED-UNVERIFIED with a verification-only round owed (tree §4 roster: "M04
Theorems 1/2/4 core"). None is re-proved here; none is silently strengthened.

* **2.1 (M04 Theorem 1 + Corollary 1.1).** Interface-level: seriesSum σ is the
  nondecreasing limit of the level-N slice sums (only `mem_slice_iff` used);
  GIVEN the count/cylinder law (count_tie — here supplied through D-15, §3.1),
  the row is EQUIVALENT to the limiting-density identity
  (D_σ): lim_N decided_σ(N)/p^{nN} = R_σ(p), and the finiteness clause is
  free. [Falsifier T1 probes (D_σ) directly at n = 2, §7.]
* **2.2 (M04 Theorem 2).** The σ-SUMMED tie is derivable from the sibling
  rows; the row's content is exactly the per-σ refinement. Consumed only as
  orientation (the per-σ assembly below never routes through the σ-sum, and
  drainage/env_tendsto is NOT consumed by this unit — it stays root-side,
  §D1.4).
* **2.3 (M04 Lemmas 3.1–3.3 + Theorem 4).** The abstract resummation core —
  tree series = least fixed point (Kleene/Tonelli in [0,∞]); Bekić
  triangularization to per-block affine systems x = Ax + c with the
  verdict-blind common matrix A; Neumann/Cramer under A^k𝟙 → 0 with
  det(I−A) ≠ 0; the shallow-cut regrouping — PROVED self-contained in M04
  (known mathematics, label (b); Harris / Etessami–Yannakakis / Kuich / Bekić
  / Seneta corroborations listed there). Theorem 4's glue walk (K4 → K1 +
  Lemma 3.3 → induction on block size with 3.1/3.2 + K2 → K3 identification →
  `rsh_interp`) is consumed VERBATIM; §3 re-prices its four K-faces.
* **2.4 (M04 Finding F1 + the wiring fence).** The as-built DEVICE chain
  `n2Chain` is REFUTED as a discharge site (device triple (q², q+1, 0)/
  (q²+q+1) vs true (p/(2(p+1)), p/(2(p+1)), 1/(p+1))). The fence — the final
  wiring MUST bind C to the REAL pack when F carries true masses — is
  EXECUTED here in two parts: (i) this unit's statement binds C to the real
  per-n pack (the D-11 unit's subject; cited as pending); (ii) the falsifier
  V1 (§7) verifies the REAL pack's n = 2 solve is the true triple in ℚ(q) —
  the real pack passes exactly the test the device chain fails.

## 3. Theorem O11 — the assembly

**Theorem O11.** Fix n ≥ 2 and a prime p. Bind (X, F, seam) to the canonical
classifier with true-mass fibers over the pinned models, and C to the real
per-n pack (symbolic tables = T-7s; block system pinned by D-11, PENDING).
Then (TIE_σ) holds for every σ, conditional on exactly {(GR-B), (FRESH),
CU-2t, D-11} (tier-1) with the tier-2 displays of §0.

*Proof.* The M04 Theorem 4 walk, with each K-face supplied as follows.

### 3.1 K4 (mass semantics): LHS = Σ_{T type σ} μ(fiber T)

Three layers, each displayed:

* **(K4-μ) The measure side** — Haar cylinder mass p^{−nN} at every level,
  Borel loci, continuity from below, the two-sided bracket: **Dfloor Theorem
  MEAS-BRIDGE = D-1(i)–(v), VERIFIED** (V22 Codex clean + fresh-Fable pass 2,
  adjudicated at ledger commit dbccbc1; three minor gaps ride the next doc
  touch). Both decided conventions covered; clause (iv) exact in the strict
  convention.
* **(K4-CYL) Level-exact cylinder reading** of decided verdict classes with
  the per-tree fiber scaling (the `bridgeMass T = μ(fiber T)` identity =
  M04's K4 clause; the count_tie face consumed by Corollary 1.1): **D-15 =
  O-1thr Theorem 3** ("the cylinder law": the fiber of a decided ns-free tree
  T is, at every N ≥ thr(T), an EXACT finite union of level-thr(T)
  coefficient cylinders; counts scale by p^n per level) **+ D-14 (O-1thr
  Theorem 1, proved outright) + CU-1/CU-2 (per-f faithfulness) + TB-CAP
  windows** — the DELTA-2 D2.1-line-3 routing, D-15 owning ALL box-level lift
  quantification. Statuses: O-1thr Thm 3 proved modulo (M6b)(iii) + the
  (V1)/(V2) citation inputs beyond degree-1 first transitions — (V1)/(V2)
  are LITUNIT-pinned and GD23-proved at order ≤ 1 over an arbitrary DVR, so
  the order ≥ 2 residue is **(GR-B)**; CU-1 rev 3 (V29 + Fable pass 2, both
  0-critical; gap repairs owed); CU-2 = re-label over O-2a Thm 2(A)–(D)
  (P(O-2a r5); GD residue → **(GR-B)**); TB-CAP dual-accepted,
  perimeter-conditional on **D-12r** (tier-2, displayed). Terminal/verdict
  records inside the decided classes are forced by **CU-2t** (tier-1).
  NOTE ((E-N), displayed non-consumption): O-1thr Thm 3(c)'s σ-count clause
  carries the (E-N) caveat (open, scoped, owner O-1thr); the clauses consumed
  here are the cylinder-exactness/scaling clauses, and per the DELTA-2
  remainder table (E-N) is not consumed by the mandatory path — if a
  verifier finds the D-15 consumption engaging 3(c), (E-N) must be ADDED to
  tier 1; flagged as verification charge (§8, item v).
* **(K4-ns) Infinite/non-separable trees excluded**: (ns-null), T-6,
  VERIFIED-DUAL (proved four times per the tree's T-6 node); standing
  ns-free perimeter carried (tree §2.4).

With (K4-μ) + (K4-CYL) + (K4-ns): seriesSum σ = Σ_{T type σ} μ(fiber T), and
by Corollary 1.1 the row is equivalent to (D_σ). [Falsifier T1's monotone
bracket is exactly this equivalence's testable face.]

### 3.2 K1 (per-tree product + shallow cut): the grammar weight factorization

The Lemma 3.3 hypothesis — a weight-preserving bijection between complete
type-σ trees and shallow-shape + block-derivation tuples, with
μ(fiber T) = W(Ŝ)·∏ weight(D_i) — is supplied by:

* **(K1-a) Tree architecture / first-split recursion / CUT-WD**: T-6
  (§T-ASSEMBLY), VERIFIED-DUAL; its open kernels (SIB-STEP)/CUT-WD are now
  served at statement level by O-10 + the CU cluster (O-10 §5.3 consumer
  audit names exactly this unit's use).
* **(K1-b) Sibling independence + the per-site Jacobian constant**: **O-10,
  PROVED SHARPER THAN CHARGED** (wave 8): Theorem 1 (K-COUNT — constant
  nonempty fibers p^{Σ min(e_i, N−τ)} at EVERY N ≥ τ, = p^{ρ(c)} in the D-8
  guard range) + Theorem 2 (the adapted-cell (SIB) product law,
  unconditional in factor coordinates) + Corollary 1 (the constant-fiber
  surjection). THIS unit consumes the FULL D-8 guard N ≥ thr(c) + 2ρ(c):
  the fiber value p^{−ρ(c)} is the per-site Jacobian factor in the grammar
  weights (O-10 §5.3: "this is where the FULL guard is genuinely used") —
  matching D-9's "O-10 guarded" entry. Falsifier record: 68/68 with the
  Route-1 breakage at exactly ratio p.
* **(K1-c) The engine presentation (I-τ)/K-LOC** — that realized site strata
  ARE adapted presentations (A1)–(A3) in branch-factor coordinates with
  τ(c) ≤ thr(c) + ρ(c) and reads within ceiling: OPEN, owned by M07 OL-3;
  its ingredients are the GD-2/GD-3 dictionary (O-10 §4.3's own pricing),
  proved at order ≤ 1 (GD23 over an arbitrary DVR; pass-2 0-critical), so
  the residue is **(GR-B)**. K-JAC's engine half is absorbed here (O-10
  Lemma 3 makes ρ(c) automatically cell-constant once the presentation
  exists).
* **(K1-d) Multi-site composition (JC-multi)**: M07 Lemma B
  (PROVED-UNVERIFIED; verification-only roster).
* **(K1-e) Leaf verdict labels are the true (e, f) data** — so verdict(D) is
  the honest σ-grading: O-5 + D-7a/b/c via **O5triple Theorems A/B/E**
  (rev 3, V23 0-critical; P(O5t r3) owed) — Theorem A (semantic leaf/factor
  bijection over the pinned GMN floor, conditional on the five §2 flags =
  GD-1/GD-7/GD-8 duties, tier-2), Theorem B (D-7b coverage by counting — NO
  no-missing consumed), Theorem E (D-7c + ASSEMBLY: leaf multiset = factor
  invariants uniformly over all lifts). The terminal-record forcing that
  ties the engine's emitted verdict fields to these semantic labels is
  **CU-2t** (tier-1). No-phantom for the realized histories underneath:
  CU-2 (= O-2a Thm 2(D) ∘ ι; GD residue → **(GR-B)**).

Given (K1-a)–(K1-e), each complete tree's mass factors as the grammar weight
of its derivation with measured one-step conditional masses at composed
pools, and the type-σ corpus decomposes along shallow shapes — Lemma 3.3
applies.

### 3.3 K2 (spectral escape, = D-9k): A(q₀)^k·𝟙 → 0 at every consumed pool

Two scopes, priced per D-9k:

* **At 𝔅_n (the abstract solve family):** **O-12 Theorem 1 + Corollary D,
  VERIFIED at honest scope** (leaf #2; ledger commit 95a46d2): every block
  kernel substochastic with positive termination margin at every prime power
  q₀ ≥ 2 (margins ≥ 3/4, 7/8, 6/7 at the on-record organizations), hence
  ρ(A) < 1 and det(I−A) ≠ 0; plus D-6 (DENOM-ALL, O-12 Theorems 1+4 + Lemma
  RR): EVERY assembled denominator is cyclotomic-type, pole-free at every
  prime power — so Lemma 3.2(ii)'s Neumann/Cramer step and the `evalAt`
  ring-hom passage are available at every pool q₀ = p^δ in the
  multiplicative closure. Lean partial: `E0Matrix` (BP4-P1).
* **At the intended pack:** that the pack's one-step matrices ARE
  𝔅_n-organized volume matrices (so the 𝔅_n theorems apply) is **D-11
  (PENDING)**. Numerics: N6 25/25; RESUM-n3 det(I−K_e) exact at pools
  2, 3, 4; falsifier T5 (M04) remains available.

### 3.4 K3 = [1v]-FULL (value correctness — THIS unit's goal content)

The numeric grammar weights equal the pool-evaluations of the symbolic ℚ(q)
entries (K_e, b^term, J, W_Ŝ) consumed by blockSolve/Rsh, with
agreement-after-cancellation at non-all-active pools. Assembled as:

* **(K3-a) The symbolic tables themselves**: T-7s, VERIFIED-DUAL (V-n3
  178/178 exact; tables exact at off-census q = 16/25) — the D-9 split's
  surviving input. T-5's H-DOMAINS package (VERIFIED-DUAL) supplies the
  height resummations; its six H.6 fences are respected by the table
  construction (they gate THIS event, and V-n3/H-n3 are the sealed evidence
  that the built tables sit inside them).
* **(K3-b) Per-stratum censuses are the claimed q-polynomials** (the
  transition-weight counts): **O-9 CEN-W/CEN-J** — level 1 PROVED at every
  n, every prime power, every complete DVR (M08 Theorem 2, 46-strata machine
  check); order ≥ 2 REDUCED to **(GR-B)** (window form) **+ (FRESH)**
  (joint-with-parent form; O-9's own census falsifier: 1,128,288 order-2
  instances, 0 violations, ε = 0 throughout). Index correction carried: the
  census field degree is d = f₀⋯f_r (O-9's DELTA-3 flag), not the tree's
  q^{f̄_r} display.
* **(K3-c) Unramified pools (q₀ = p^δ, δ > 1)**: the re-based classifier
  obeys the same digit/alphabet laws with a_δ = δ·a₁ — **O-8b (M14),
  PROVED-UNVERIFIED conditional on (R1)–(R4)** (the O_δ re-base of the T-1
  stage laws; N8 exhaustive, 199,723 alphabets, 0 violations). Discharge
  route, displayed: the adopted arbitrary-DVR discipline (DELTA-2 §D2.6
  step 3) states the GD families over an arbitrary absolutely-unramified
  complete DVR from the start — GD23's order ≤ 1 layer is proved at that
  generality, so (R1)–(R4)'s residue at order ≥ 2 is **(GR-B)** again; the
  remaining scope-hygiene audit (each consumed table law stated at DVR
  generality at the pack) rides **D-11**'s instance pin. No fifth open item
  is introduced.
* **(K3-d) Measured weights = table evaluations AT the intended pack** (the
  semantic mass identification): **D-11 (PENDING)** — kernel entries are the
  Haar volumes of the T-3/T-6 continuation events (T-3 §D4-R mass laws,
  VERIFIED-DUAL, supply the events; O5triple Thm E + D-15 supply the per-box
  lift uniformity per the WAVE-8 pricing), rows pairwise disjoint with
  positive termination margin, block system = 𝔅_n or O-12-Thm-3-covered.

### 3.5 The glue

Exactly M04 Theorem 4's proof: K4 (§3.1) rewrites the LHS as
Σ_{T type σ} μ(fiber T); K1 (§3.2) + Lemma 3.3 regroup it as the shallow
convolution of the numeric block series B; Lemma 3.1 + Bekić + Lemma 3.2
with K2 (§3.3), by induction on block size (smaller blocks' pools are pool
powers, covered by §3.3's every-prime-power scope), give
B_{e,·}(σ′)(q₀) = (I − A(q₀))^{−1} c(σ′); K3 (§3.4) identifies this
inductively with the evaluation at q₀ of blockSolve (ring-hom `evalAt` on
the regular subring, memberships from D-6/`wsh_ok`/`rsh_interp`); assembling
over shapes gives the evaluation at p of Rsh(vmap σ); `rsh_interp` (a
carried law of the real pack — RatBurdens' interpolation face, checked at
RESUM-n3) converts it to Rval(vmap σ)(p) ∈ [0,1] (`r_bdd`), and
ENNReal.ofReal is faithful there. ∎

## 4. Displayed non-consumptions (quantifier hygiene)

* **Drainage (env_tendsto / O-4) is NOT consumed.** The per-σ assembly goes
  through Theorem 4's K1–K4 route; drainage enters only M04 Theorem 2's
  σ-sum remark and the root's squeeze (T-U), both outside this unit. (O-4's
  own residue OL1-ii ← CU-2 + CU-4 + GMN Cor 4.19 stays where DELTA 2 put
  it; O4T's n ≤ 3 unconditional transfer is unconsumed here.)
* **No-missing (CU-1) is consumed ONLY through D-15's routing** (the K4-CYL
  face) — never as a box-keyed universal statement (the V21-1/2 discipline:
  box-level lift quantification lives in D-15 alone).
* **OB1/D-16/LIT-5, K-OB-C: not consumed** (route R-QNT, per DELTA 2). CU-6/
  OB2: not consumed (the WAVE-8 audit: D-11 needs per-box lift uniformity,
  not ∼OM invariance; CU-6 evicted).
* **The row is NOT claimed as the density tie.** (TIE_σ) equates the tree
  series with the solve value; the further identity with α(n, σ; p) is the
  root's business (T-U squeeze over D-1's bracket + O-4), not this unit's.

## 5. The consumption table (every consumption displayed)

| # | consumed piece | supplies (site) | status + evidence | tier-1 residue contributed |
|---|---|---|---|---|
| 1 | M04 Thm 1 + Cor 1.1 | slice-limit form; row ⇔ (D_σ) given the cylinder law (§2.1, §3.1) | PROVED-UNVERIFIED (M04; verification-only roster) | — |
| 2 | M04 Lemmas 3.1–3.3 + Thm 4 glue | lfp/Bekić/Neumann core + the walk (§2.3, §3.5) | PROVED self-contained (M04); same roster | — |
| 3 | Dfloor Thm MEAS-BRIDGE (D-1) | Haar/cylinder measure side (K4-μ) | **VERIFIED** (V22 + Fable pass 2; ledger dbccbc1) | — |
| 4 | O-1thr Thm 3 (= D-15) + Thm 1 (= D-14) | exact cylinder law + per-tree scaling (K4-CYL) | proved mod (M6b)(iii) + (V1)/(V2) beyond order 1; rev 4 landed; P(O-1thr r4) owed | **(GR-B)** (order ≥ 2) |
| 5 | CU-1 (no-missing, per-f) | decided-class faithfulness under D-15 (K4-CYL) | rev 3; V29 + Fable pass 2 both 0-critical; gap repairs owed | (GD residue → **(GR-B)**) |
| 6 | CU-2 (no-phantom = O-2a Thm 2(D)∘ι) | realized histories are GMN data (K4-CYL, K1-e) | re-label complete; P(O-2a r5) | **(GR-B)** |
| 7 | **CU-2t** (terminal seam) | verdict-carrying terminal records forced (K4-CYL, K1-e) | **OPEN — one unexecuted corollary-grade lemma** (CU cluster §2; owner recommendation: CU-1 orbit) | **CU-2t** |
| 8 | TB-CAP (T-6) windows | (τ-hen)/(τ-irr) verdict windows (K4-CYL, K1-e via CU-2t) | VERIFIED-DUAL, perimeter-conditional | (tier-2: D-12r perimeter) |
| 9 | T-6 (ns-null) + first-split/CUT-WD architecture | infinite-tree exclusion (K4-ns); shallow cut (K1-a) | VERIFIED-DUAL; kernels served by O-10 + CU cluster | — |
| 10 | O-10 Thms 1/2 + Cor 1 (K-COUNT + SIB, **D-8-guarded**) | per-site product law + Jacobian constant p^{−ρ(c)} (K1-b) | **PROVED IN FULL** in factor coordinates (wave 8); own hostile pass owed; harness 68/68 | — |
| 11 | (I-τ)/K-LOC (= M07 OL-3) | engine cell → factor-coordinate presentation (K1-c) | OPEN, priced at GD-2/GD-3; order ≤ 1 PROVED (GD23, arbitrary DVR; pass 2 0-critical) | **(GR-B)** |
| 12 | (JC-multi) = M07 Lemma B | multi-site composition (K1-d) | PROVED-UNVERIFIED (verification-only roster) | — |
| 13 | O5triple Thms A/B/E (O-5 + D-7a/b/c) | semantic leaf labels + leaf/factor bijection (K1-e); per-box lift uniformity input to D-11 | rev 3, V23 0-critical; P(O5t r3) owed; five flags = GD-1/GD-7/GD-8 duties (tier-2) | — |
| 14 | O-12 Thm 1 + Cor D + Thm 4/Lemma RR (D-6, D-9k at 𝔅_n) | substochastic escape + pole-free denominators at every prime power (K2, §3.5 evalAt) | **VERIFIED at honest scope** (leaf #2); `O12PoleFree.lean`/`E0Matrix` partials | — |
| 15 | **D-11** (instance pin / MASS-ID) | pack = 𝔅_n-organized volume matrices; measured weights = table evaluations (K2 pack side, K3-d; wiring fence §2.4) | **PENDING — unit in flight** (WAVE-8 pricing: O5triple Thm E + D-15, no OB2) | **D-11** |
| 16 | T-7s (symbolic tables + ledger) + T-5 H-DOMAINS/H.6 | the symbolic ℚ(q) entries + height resummations (K3-a) | VERIFIED-DUAL (V-n3 178/178; H-n3 151/151; off-census q = 16/25) | — |
| 17 | O-9 CEN-W/CEN-J over M08 Thm 2 | per-stratum census q-polynomials (K3-b); index fix d = f₀⋯f_r carried | level 1 PROVED; order ≥ 2 REDUCED (wave 8); own hostile pass owed | **(GR-B) + (FRESH)** |
| 18 | O-8b (M14, EQ-2) via the arbitrary-DVR discipline | unramified-pool weight laws (K3-c) | PROVED-UNVERIFIED conditional on (R1)–(R4); order ≤ 1 discharged at GD23's DVR generality; N8 exhaustive | **(GR-B)** (≥ 2); scope-hygiene → D-11 |
| 19 | K-FACT (GMN Thms 1.15/1.19/3.1/3.7) | roster members are coprime factors (inside O-10's Thm-2 application) | LITERATURE (LIT-1, conditional grade §D1.5(b), tier-2) | — |
| 20 | rsh_interp / r_bdd / wsh_ok (pack laws) | Rsh → Rval conversion + [0,1] bounds (§3.5) | carried laws of the real pack (RatBurdens face); checked at RESUM-n3; pack construction = O-14d/D-11 territory | (rides **D-11**) |

Tier-1 union over the table: **{(GR-B), (FRESH), CU-2t, D-11}** — exactly the
§0 display; rows 4/5/6/11/17/18 all point at the SAME (GR-B) package (one
input, many faces — the D2.2 merge working as designed).

## 6. Pending-pass registry (verification duties, tier-2; CUC §0 pattern)

P(O-2a r5) · P(O-1thr r4) · P(O5t r3) · GD23 pass 2 = SOUND-WITH-GAPS,
0-critical, 9 gaps (commit 4d109b9; repairs owed) · CU-1 pass 2 =
SOUND-WITH-GAPS, 0-critical, 7 gaps (commit 252f34c; repairs owed) · hostile
passes NOT YET RUN: O-10 attempt, O-9 brief (V-pass owed), THIS unit · the
M04 core's verification-only round (tree §4 roster). Per §D1.7 none of these
is consumed by an acceptance claim: this unit's grade is PROVED-UNVERIFIED
(conditional), not VERIFIED.

## 7. Falsifier record (ran FIRST; predictions sealed in the harness docstring)

Harness: `verification/openmath/o11_seriestie_check.py` (V1/V2 need sympy —
run under `uv run --with sympy`; T1 pure stdlib). Log:
`verification/openmath/logs/o11_seriestie_run3.log`. **38/38 PASS, exit 0**
(2026-08-02, this machine):

* **V1 (Finding F1's test AT THE REAL PACK — the dispatch's named
  falsifier).** The real n = 2 solve (`om_density_engine.alpha_full(2)`, the
  same block-recursion pipeline RESUM-n3 gates at n = 3) equals the true
  triple (q/(2(q+1)), q/(2(q+1)), 1/(q+1)) IDENTICALLY in ℚ(q) (sympy
  difference ≡ 0, all three types + Σ = 1) and matches the oracle-validated
  `padic_types.monic_quad_pred` exactly at p ∈ {2, 3, 5, 7}. The real pack
  passes exactly where M04 proved the device chain fails — the K3/value leg
  is alive at the discharge site. 8/8.
* **V2 (the n = 3 anchor, symbolic).** `alpha_full(3)` equals the five-type
  oracle (`monic_cubic_pred`, transcribed line-for-line) identically in ℚ(q),
  each type also exact at p ∈ {2, 3, 5, 7}; Σ_σ = 1 in ℚ(q). This re-derives
  the RESUM-n3 65/65 anchor symbolically end-to-end. 6/6.
* **T1 (M04 test T1 — the (D_σ) limit form, which Cor 1.1 makes equivalent
  to the row given K4-CYL).** Exhaustive enumeration of (b, c) ∈ (ℤ/p^N)²,
  p ∈ {2, 3, 5}, N ≤ (10, 6, 4): per-σ decided mass is NONDECREASING and the
  two-sided bracket dmass_σ(N) ≤ ρ_σ(p) ≤ dmass_σ(N) + env(N) holds at every
  level, env decaying geometrically (7.8e-3 / 1.4e-3 / 1.6e-3 at the caps).
  24/24. Any bracket violation would have refuted (D_σ) at the real
  classifier and killed the row.
* Harness-bug honesty: two dead-code defects in V2's oracle call (q = 1
  division; Fraction-vs-symbol typing) were fixed between runs 1–3; no
  sealed prediction changed; run 3 is the run of record.

Not run (displayed): M04 T5 (the E0 spectral probe at extracted engine
blocks — subsumable into the D-11 unit's own falsifier, where the pack
matrices live); M04 T2a (n = 3 Monte-Carlo via cypari2 — not installed;
RESUM-n3's sealed PARI gate already covers the values).

## 8. Honesty ledger + suggested verification charges

PROVED here: nothing new — this unit is an assembly; its one contribution is
Theorem O11's re-priced walk (§3) + the consumption table (§5) + the executed
F1 wiring fence (§2.4/§7-V1). CONSUMED: rows 1–20 of §5, statuses as
displayed. OPEN (tier-1): (GR-B) · (FRESH) · CU-2t · D-11 (pending unit).
TIER-2: §0 + §6 lists. NOT CLAIMED: the density tie (root's business); any
unconditional per-σ value at general n; any Lean discharge (the
`series_tie` row and item-27-adjacent wiring stay untouched, PARKED).

Suggested charges to the hostile pass, beyond the standard: (i) check §5's
tier-1 union claim — hunt for a consumption NOT in the table (the
quantifier-hygiene traps: does §3.1 really avoid (E-N)? does §3.2's Lemma
3.3 bijection consume more of T-6 than CUT-WD + first-split?); (ii) verify
the D-8 guard is engaged ONLY at K1-b's fiber-value clause (O-10 §5.3's
audit) and nowhere sub-guard; (iii) confirm §3.4(K3-c)'s (R1)–(R4)-to-(GR-B)
pricing does not smuggle an unstated order-1 O_δ gap (the GD23 DVR layer's
exact scope); (iv) re-derive §3.5 from M04 Theorem 4's text and diff the
K-face bindings; (v) adjudicate the (E-N)/Thm-3(c) seam named in §3.1.

## 9. Files + owed tree lines

* This unit: `lean/notes/openmath/O11_phaseB_attempt.md`.
* Falsifier: `verification/openmath/o11_seriestie_check.py` + log
  `verification/openmath/logs/o11_seriestie_run3.log` (38/38 PASS).
* Owed DELTA-3 lines (orchestrator): O-11 status → PROVED-UNVERIFIED
  conditional on {(GR-B), (FRESH), CU-2t, D-11}, [1v]-FULL assembled at
  §3.4; the M04 F1 wiring fence recorded EXECUTED at the real pack (V1);
  CU-2t owner assignment (still owed from CUC §8).
