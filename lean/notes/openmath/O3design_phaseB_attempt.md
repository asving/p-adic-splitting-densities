# O3design — the O-3 ⊕ O-2b joint cluster: DESIGN (statement layer + gates + decomposition) — Phase-B design round (Fable, 2026-07-31)

**Unit type: DESIGN, not proof.** Target: the §D1.3 joint cluster of
`docs/MATH_COMPLETION_TREE_2026-08-01.md` (original + DELTA 1) — **O-3** (K-RUN
realization faithfulness, four clauses + K-OB-A/B/C/E) **⊕ O-2b** (K-DICT-OB1
trace/tree correspondence + K-DICT-OB2 σ-invariance), the two halves V6 findings
15/23 found mutually dependent and DELTA 1 resolved into ONE cluster proved by a
single well-founded induction on resolution level. Deliverables here: (1) the
statement layer in the O-2a carrier vocabulary (DES-1..7, rev-2 strengthened);
(2) the gate list (cheapest falsifier per claim); (3) the dependency map into the
verified/pending leaves; (4) the decomposition into prover units. This design
goes to Codex plan review BEFORE any prover dispatches (per the standing
plan-level adversarial-pass rule).

Sources consumed: the tree + DELTA 1 (§§D1.2–D1.6); `O2a_phaseB_attempt.md` +
`O2a_phaseB_attempt_rev2.md` (the carrier; rev-2's formal codomain 𝔗,
interpretation ι, intrinsic positional Cons_f clause, Lemma R, OL-2a-1/2/3/4 —
the design targets the STRONGER rev-2 positional form of OL-2a-2, clauses
(a)–(d), identity frame); `O1thr_phaseB_attempt_rev2.md` (per-site package,
policy parametrization, (M6a)/(M6b) split, laws (N2)–(N4), vhtx);
`IFK_BLUEPRINT_2026-07-31.md` REV 1 (§R1 finding dispositions, §R3 OB1/OB2, §R5
U6 canonicalizations, K-OB-A..E); `O14ap_phaseB_attempt_rev2.md` (RunRealizerExists:
prime-field collapse + last-node closure, verifier-confirmed); the V5 disposition
(`BRIDGE_ADJUDICATIONS_2026-07-30.md` §IFK RE-REVIEW); U6 results
(`verification/openmath/results/U6_krun_results.json`, SURVIVES exhaustively).

## 0. The cluster in one paragraph, and the cycle it must break

O-3 says: at every level N and box x, the realized run set of the canonical
classifier is EXACTLY the level-N truncation of the semantic OM tree of any lift
f — no phantoms, nothing missing, realized loci nonempty, acceptance exact.
O-2b says: the classifier's produced traces are determined (up to the published
Okutsu/OM-factorization equivalence) by the OM factorization — trace/tree
correspondence (OB1, THE hardest face) and σ-invariance (OB2). The V6 cycle:
no-phantom needs engine-reads → GMN-data (dictionary content); OB1 quantifies
over "the trees the classifier produces" (O-3's subject). The resolution (D1.3,
made concrete here): O-2a's rev-2 carrier already split off everything upstream;
what remains cyclic is broken by ONE well-founded induction on **resolution
level** whose package IND(N) bundles six faces (§2) — each face at level N may
consume any face at level < N, and within a level the faces are consumed in a
DISPLAYED acyclic order (§2.3). The per-order engine-seam lemmas OL-2a-1/2/3 are
NOT part of the cycle (they presuppose Cons_f chains, no realization semantics)
and dispatch as upstream units; OL-2a-4 (emission discipline) is O-3-flavored
and is proved INSIDE the cluster.

## 1. Objects (definitions the statement layer quantifies over)

Standing preconditions (tree §2.4): f monic degree n over O = ℤ_p (D-3 will
re-scope to W(F_q) later), separable; trees range over **ns-free carriers**;
everything at the pinned representative family F_rep.

* **(O1) The carrier, by citation.** 𝔈 = dressed histories 𝐇 = (ρ₀; ν₁,…,ν_k)
  with laws W1–W5; 𝔈° = all-continuing histories; the formal codomain 𝔗 (chain
  data, literal equality); Θ : 𝔈 → 𝔗 total, truncation-compatible; the GMN
  interpretation ι (level 0 proved, levels ≥ 1 gated by OL-2a-1); Cons_f ⊂ 𝔈
  with the rev-2 INTRINSIC positional clause ((c0)/(c1)/(c2) + (s_i,u_i) = the
  initial point of the read side in the order-i GMN integer frame); Lemma R
  (injectivity on 𝔈°_f). All verbatim from O2a rev-2 — the cluster adds NO new
  carrier (V5 defect (1) answered by reuse, §6).
* **(O2) Cons_f^τ — the terminal-extended consistency (NEW; discharges the
  rev-2 terminal-seam obligations (t-i)/(t-ii) assigned to O-3).** For 𝐇 with
  terminal last node ν_k: Cons_f^τ(𝐇) iff Cons_f(𝐇°) (the continuing prefix)
  AND the terminal record matches the GMN verdict datum of the prefix chain:
  (τ-irr case) μ_{k'} = 1 at the last read and the verdict pair equals
  (accE_{k'}, accF_{k'}) (= O-2a Thm 2(B) saturation data); (τ-hen case) the
  node sits on the slope-−∞/Hensel side and the verdict pair is (1, f₀) with
  the (D3)-window read [O2a rev-2 (L3+) j₀-convention]. For all-continuing 𝐇:
  Cons_f^τ := Cons_f. This is the codomain extension (t-ii); that it is
  CONSISTENT (a terminal record is forced by the prefix + f — no free choice)
  is the (t-i) obligation, a lemma of unit JC-0, from O-2a (B) + Cor 1.20/3.8.
* **(O3) The semantic tree, as a set.** T_can(f) := {𝐇 ∈ 𝔈 : Cons_f^τ(𝐇)},
  ordered by prefix. DESIGN MOVE: the semantic object is DEFINED as the
  Cons^τ-set over F_rep — intrinsically GMN-defined, no classifier in the
  definition. (D-5's semantic-invariance half, for this cluster's needs, then
  reduces to: Cons_f^τ depends on f only through GMN data over the pinned
  F_rep — true by construction — plus lift-independence below the resolution
  level, which is face F1's uniformity clause, NOT presupposed.)
* **(O4) The realized run set.** For a level-N box x ∈ (O/p^N)^n: Run_N(x) :=
  the set of τ-pruned dressed histories the canonical classifier emits on x at
  working level N. Pinned choices: (i) the classifier is the engine at the
  CANONICAL policy (the (†15) pair canPolicy/canPolicy_pin — dischargeable at
  F = ZMod p by O14ap rev-2 Theorem 1 + Corollary 4, the verifier-confirmed
  prime-field collapse; the intended instance K = ℚ_p has ambient F = 𝔽_p, so
  this supply is PROVED for the cluster's scope); (ii) τ-pruning per D4R.4/L12;
  (iii) the dressing is the OL-2a-4 emission map (anchor-unit normalization) —
  Run_N(x) ⊂ 𝔈 is itself conditional on OL-2a-4, displayed as such.
* **(O5) Resolution level.** N(𝐇) := max over the sites (H_i, ν_i) along 𝐇 of
  the O-1thr read ceiling L(H_i, ν_i) (well-formed: Lemma NAT gives L ≥ 2),
  joined with the verdict window at a terminal node (TB-CAP (τ-hen) N_V = 1;
  (τ-irr) level-N(η) window). Reconciliation with D4R.4/L12's N(η,⊤) is a
  JC-0 duty (adopt the max-of-ceilings form as THE definition; prove it ≥ the
  L12 form or re-key consumers). Induction measure: (N, k) ∈ ℕ × ℕ
  lexicographic — primary = resolution level, secondary = history length
  (needed because a level-N step extends prefixes of the same N).
* **(O6) Fresh-frame-lawful chains (the F3 index set), U6-canonicalized.** A
  formal assignment chain whose per-step reads are menu-lawful at the frame
  state (the REV-1 finding-4 indexing the U6 probe validated — the free-chain
  wording was tautological), with the TWO BINDING canonicalizations from the
  probe: (i) branch species = the WHOLE node read (all polygon sides +
  residual profiles) — keying by the branch's own side letters (e, ℓ, h) pools
  configurations with different digit-pinning counts and SPURIOUSLY falsifies
  the equal-fiber law; (ii) beyond-cap content pools into a single ('deep', k)
  marker (its internal decomposition is horizon-dependent; pooled deep
  censuses verified exact p-powers). Any prover unit that drops either
  canonicalization is pre-refuted at the U6 data.
* **(O7) The BNS relation (OB1/OB2 hypothesis).** f ∼_OM g iff f and g admit a
  COMMON OM factorization in the published sense (BNS §2/§3 vocabulary;
  transcription duty at JC-10a — journal text, the numbering-shift warning
  stands). NOTE the design keeps LIT-5 (BNS Thm 3.13, the δ+1 congruence ⇒
  ∼_OM) OUT of the cluster: it is consumed only by D-16 downstream. The
  cluster's OB1 hypothesis is ∼_OM itself.

## 2. THE STATEMENT LAYER — the package IND(N)

### 2.1 The six faces + one level-free satellite

**IND(N)**, for N ∈ ℕ: for every ns-free monic separable f of degree n over O,
with x := f mod p^N:

* **(F1_N — no-phantom, with ceiling conformance and lift uniformity).**
  Every 𝐇 ∈ Run_N(x) has N(𝐇) ≤ N, and Cons_g^τ(𝐇) holds for EVERY monic
  lift g of x. [K-RUN clause 1; M02 L2's fiber invariance is the "every lift"
  quantifier; the two-lift transfer below the ceiling is consumed from O-1thr
  Thm 1.]
* **(F2_N — no-missing).** Every 𝐇 ∈ T_can(f) with N(𝐇) ≤ N lies in
  Run_N(x). [K-RUN clause 2. THE hardest O-3 face.]
* **(F3_N — nonempty locus).** Every fresh-frame-lawful chain c (per (O6),
  whole-node-read species, deep pooling) with resolution ≤ N has a monic
  separable witness g in its level-N digit cylinder with the corresponding
  history in T_can(g). [K-RUN clause 3; the T-2 (SAE) precedent — an empty
  stratum once predicted 62,500 members — is the failure mode this clause
  exists to exclude.]
* **(F4_N — acceptance, K-RUN clause 4 / OL1-ii face-content).** The built
  certification predicate Cert accepts (x, 𝐇) iff 𝐇 ∈ Run_N(x) AND 𝐇 is
  verdict-carrying in T_can(g) for every lift g (i.e. accepted = realized ∧
  semantic, both directions).
* **(F5_N — state coherence / single-run trace transport; the intra-run half
  of OB1).** For every 𝐇 ∈ Run_N(x): the engine's frame state after 𝐇 equals
  the GMN state data of ι(Θ(𝐇)) — stage key = Lift_k(chain data), frame
  valuation u_{k+1} = v_{k+1} (OL-2a-2(a), identity frame), digit
  algebra/tower = F_{k+1} on the nose (DES-1), positional data per
  OL-2a-2(d).
* **(F6_N — trace correspondence, OB1 at level N).** For f ∼_OM g (common
  admissible OM factorization over F_rep): there is a bijection
  Run_N(x_f) ≅ Run_N(x_g) preserving dressed node data up to the
  representative-equivalence of §2.2's TT-DET, and matching maximal
  recentering-population runs one-to-one with same-degree refinement
  iterations of the published Montes flow. [K-DICT-OB1. The recentering-run
  pooling is forced by the K-3/M01 caterpillar: raw node counts differ
  between equal-factorization polynomials, only collapsed runs correspond —
  this is the same compression D-12 proved skeleton-side.]

**(OB2 — σ-invariance; level-free satellite).** If f ∼_OM g then σ(f) = σ(g).
Design route: an OM factorization assigns each irreducible factor a saturated
type; O-2a clause (i) says (e, f) per factor = (accE, accF), functions of the
type's discrete data; the Okutsu-equivalence relation preserves these
invariants (the BNS §2 statement to transcribe); σ is the multiset of (e, f).
So OB2 = O-2a(i) + one transcription + bookkeeping — NOT inductive, dispatches
early (JC-12), and is a hypothesis-consumer of nothing in IND.

### 2.2 The named auxiliary lemmas (the cluster's genuinely new mathematics)

* **(TT-DET — type-tree determinacy; GMN-side, deep-wild-hard; the core of
  OB1).** If f ∼_OM g, then T_can(f) and T_can(g) correspond as dressed trees
  up to representative equivalence: there is an explicit equivalence on 𝔈
  (generated by Okutsu-equivalent re-choices of representatives at each level,
  BNS/GMN vocabulary) and a bijection T_can(f)/≈ ≅ T_can(g)/≈ preserving
  (e_i, h_i, g_i, μ_i) data and collapsed recentering runs. This is finding
  24's exact point ("same factorization reachable through different
  representative choices and refinement histories") stated as mathematics.
  F_rep pins ONE representative per chain, so ≈ acts between the trees, not
  within one — the statement must say how F_rep-pinned trees of DIFFERENT
  polynomials align (mechanism: both align to the factorization's Okutsu
  frames; GMN §3 + BNS §2).
* **(MF-MATCH — Montes-flow matching).** Within one polynomial's run: maximal
  recentering runs of T_can(f) correspond one-to-one to same-degree refinement
  iterations of the published Montes flow (the iteration structure of BNS §4 /
  GMN §4.2's algorithmic passage). Needed so that any future BNS
  iteration/precision bound (D-16, OL2 rates) can be consumed. Citation pull
  duty BEFORE dispatch: the published flow's refinement-step specification.
* **(K-OB-C — Okutsu proximity).** Membership of f in the semantic prefix 𝐇
  (Cons_f(𝐇)) ⇒ the tracked cluster's roots lie in a disk of radius w − C_φ
  around a key root, with w the accumulated weight and C_φ the explicit
  Okutsu constant. GMN-side; candidate cite to pull first (Guàrdia–Nart Okutsu
  invariant papers / GMN §1.3–§2 value bounds). Consumed by O-7 (X1) and
  available to F2's step as the root-tracking route; the design does NOT make
  F1 depend on it (F1 goes through the engine seam — cleaner post-O-2a).
* **(K-OB-E — continuing ⇒ repeated residual).** A continuing node of
  T_can(f) has μ_i ≥ 2. GMN-side content: non-complete ⇔ ω ≥ 2 (Def 3.9) —
  near-definitional over the carrier (W3 is the carrier law; this is its
  semantic counterpart). Folded into JC-4.
* **(K-OB-A — finite-site assembly).** For a row touching finitely many sites,
  the fibers agree below the max modulus max_i L(H_i, ν_i). From O-1thr Thm 1
  applied per site + O-13/D-12 finiteness of the site roster. Corollary-grade
  (JC-13).
* **(K-OB-B — inStratum ⇒ realized).** With the DES-6 re-key (inStratum f H :=
  ∃ dressing 𝐇 of H with Cons_f(𝐇)): membership ⇒ 𝐇 ∈ T_can(f) (definitional
  now) ⇒ realized once N ≥ N(𝐇) (face F2). So K-OB-B = F2 + a resolution-level
  computation — a corollary UNIT (JC-13), not a face; the V1-critical bridge
  is priced but no longer independent.

### 2.3 The intra-step consumption order (the acyclicity display)

Within the step (N, k), faces consume: **F5** ← {F5, F1 at < (N,k)} +
OL-2a-1/2/3 (the seam at the reached order) + OL-2a-4. **F1** ← F5 at (N, k)
+ OL-2a-2(c,d)/3 (the read just made = (c1)/(c2) data) + Cons^τ (terminal
seam, JC-0) + O-1thr Thm 1 (lift transfer below the ceiling). **F2** ← F1/F5
at < (N,k) (the engine reached the right state on the strict prefix) + D-14
(the next semantic read is menu-lawful and determined below its ceiling — the
LAWFUL-SITE quantifier, NOT the realized-site form: this is exactly why D-15/
V5-defect-(2) forced D-14 upstream) + roster totality (O-1thr (M6a)/(M6b)) +
K-OB-E (semantic children exist only at μ ≥ 2, matching the continuation
rule). **F3** ← F2 at ≤ (N,k) is NOT used; instead O-14a′ (witness
construction: RunRealizerExists at F = ZMod p, PROVED) + D-14 (cylinder
pinning) + the forge method (T-2 C.1.5 digit mechanics). **F4** ← F1 + F2 at
(N, k) + O-1thr (Cert's reads well-defined per-site) + TB-CAP (τ-irr) window
[perimeter-conditional — inherited conditionality, displayed]. **F6** ← F1 +
F2 + F5 at (N, k) (both runs' traces ARE their Cons^τ sets — the classifier
quantifier is ELIMINATED, which is how the cluster answers V6 finding 23) +
TT-DET + MF-MATCH. No face at (N, k) consumes a later face: the order
F5 → F1 → F2 → {F3, F4} → F6 is acyclic. OB2 is outside the induction.

Base case (N ≤ 1 or k = 0): O-2a Theorem 1 (order ≤ 1, all clauses incl. the
j₀ corner and k' = 0 cases — PROVED rev-2) + the compiled length-≤1 forge
instances + K-12's n = 2 anchor. The U6 exhaustive length-2 survival is the
numeric floor directly above the base.

### 2.4 Inherited conditionality (displayed, not hidden)

The cluster's theorems will carry, until separately discharged: (M6b) — the
O-1thr single interface assumption (vertex read well-defined + band at depth
≥ 2); EXPECTED DISCHARGED by OL-2a-2/3 (the identity-frame crossing + residual
identification prove vertex transport at every order — one proof serving both
consumers; record the convergence, do not double-prove). TB-CAP (τ-irr)
perimeter (T-6, D4R.0-K(c) verdict pin residue, = D-12r's gate). OL-2a-1..3
until JC-1..3 land. The O14ap (S6b′) residue at deg Φ > 1 is NOT inherited at
the intended instance (prime-field collapse covers F = 𝔽_p); it re-enters only
at D-3's unramified re-scope — flagged for D-3, not here.

## 3. THE GATE LIST (cheapest falsifier per claim; run BEFORE proving)

| claim | gate | mechanism + one-shot kill | cost |
|---|---|---|---|
| F1 | **G-F1**: U6 Test A extended to length 3 | phantom scan: any realized dressed history failing Cons^τ vs PARI-computed GMN data refutes | U6 harness extension; hours |
| F2 | **G-F2**: U6 counting tie T = T̂ at length 3, all (n,p) ∈ {2,3}² | any stratum T < T̂ refutes F2 (T > T̂ refutes F1); 174/174 already exact at length 2 | same harness |
| F2 (terminal seam) | **G-F2t**: the landing-flank countermodel search (LIVE) | O14ap rev-2 Thm 3 PREDICTS empty + UNRECORDABLE (RG-2 fence); any hit reopens the terminal step | already running |
| F3 | **G-F3**: SAE-style stratum census at depth 3 | enumerate lawful chains (whole-node species, deep pooling), predict member counts, exhaustive box scan; any EMPTY predicted-nonempty stratum refutes (the 62,500 precedent) | new script, ~1 day |
| F4 | **G-F4**: acceptance regression (M06-TD style) | simulate Cert per definition on exhaustive decided ns-free boxes n ≤ 4, p ≤ 5 vs factorpadic; accepted-but-wrong OR semantic-decided-but-unaccepted-at-N(f) refutes | extend U6 harness |
| F5 | **G-F5**: state-transport probe at depth 3 | after each realized read compare engine frame (key, u, tower) vs independently computed v_r/F_r; the sealed Case-J 12-strata gate is the depth-2 precedent | extend harness |
| F6 + TT-DET | **G-F6** (RUN FIRST — hardest face, cheapest kill): cross-polynomial trace gate | pairs via (a) g = f + p^{δ+1}h sweeps, (b) representative perturbation at order 2; run both, compare pooled traces (collapsed recentering runs); ANY mismatch at ∼_OM pairs refutes OB1-as-stated and forces a weaker correspondence — learn this before proving | new script; the M15 §7 ℤ₂ family (T1-recentering exclusion) is the mandatory first family; wild corner p = 2, n = 4 mandatory |
| MF-MATCH | **G-MF**: instrument the same pairs' runs against a hand-transcribed Montes-flow iteration count | mismatch in same-degree iteration multiset refutes | rides G-F6 |
| OB2 | **G-OB2**: σ(f) vs σ(g) via PARI on the G-F6 pairs | any σ difference at a ∼_OM pair refutes (and would contradict BNS's intent — a finding, not just a repair) | free rider |
| K-OB-C | **G-OBC**: M12-T1 radius harness | realized read at weight w with NO root within w − C_φ refutes the constant | existing harness re-run |
| OL-2a-4 | **G-EMIT**: emitted-history W-law scan | any emitted history violating W1–W5/a₀ = ord(f̄)/only-last-terminal refutes; extends the U6 fidelity header | rides U6 harness |
| N(𝐇) def | **G-CEIL**: ceiling conformance scan | any realized read above max L(H_i, ν_i) on exhaustive cubic boxes kills the (O5) definition (M02 T3–T5 precedent) | o1thr harness re-run at depth 3 |

Gate discipline: G-F6 and G-F3 are the two NEW investments and run before any
prover unit of JC-7/JC-10; the rest are extensions of standing harnesses. All
species/pooling per (O6) — a gate keyed by side letters is void (U6 caveat).

## 4. DEPENDENCY MAP

**Consumes (status as of 2026-07-31 late):**

| input | status | consumed by |
|---|---|---|
| O-2a Thm 1 (order ≤ 1) + Thm 2(A)–(C) | PROVED-UNVERIFIED (V10 core confirmed; rev-2 pass pending) | base case; F1/F5 conditional core; OB2 via clause (i) |
| OL-2a-1/2/3 (rev-2 strengthened forms) | OPEN — upstream units JC-1..3 | F5, F1; expected to also discharge O-1thr's (M6b) |
| OL-2a-4 | OPEN — owned HERE (JC-4) | Run_N(x) ⊂ 𝔈; F1 |
| O-1thr Thm 1/2(a) (per-𝒫, outright) + 2(b)/3 (mod (M6b)) | PROVED-UNVERIFIED (V12 SOUND-WITH-GAPS; rev-2 on file) | F1 lift transfer; F2 roster totality; F4 moduli; K-OB-A; (O5) |
| D-14 (lawful-site read) | pass-1 substantively clean, r2 in flight | F2 step; F3 cylinder pinning |
| D-15 (CYL) | NOT consumed — supplied-to (see below) | — |
| O-14a′ RunRealizerExists | ZMod p collapse + last-node closure VERIFIER-CONFIRMED (rev-2) | F3 witnesses; (O4) policy pin; G-F2t prediction |
| O-13/D-12 skeleton finiteness | 2-pass VERIFIED / PROVED-UNVERIFIED (V8) | K-OB-A roster finiteness; F3 menu finiteness; F6 recentering-run pooling (same compression) |
| T-6 TB-CAP (τ-irr) | dual-accepted, perimeter-conditional (D-12r) | F4 window; Cons^τ (t-i) |
| T-2 C.1.5 graded presentation | deferred T-2 obligation (shared with O-1/O-8a) | F3 forge mechanics |
| LIT-1 GMN (Thm 1.15/1.19, Cor 1.20/3.8/4.19, Defs 2.x/3.9/3.10/4.x) | LITERATURE-CONDITIONAL | Cons^τ, TT-DET, K-OB-C/E, F2 |
| BNS §2/§4 (∼_OM, Okutsu equivalence, the flow) | LITERATURE-CANDIDATE; transcription duty JC-10a/12 | TT-DET, MF-MATCH, OB2 |
| LIT-5 BNS Thm 3.13 | NOT consumed (D-16 only) | — |

**Supplies (who consumes the cluster):** K-4/K-6 repairs (via D-15); K-14
MarkGraft duties (I0) = F2+F3, (I1) = F1+F2 (faithful census), (I3-rc) = F5;
O-4's OL1-ii = F4 + GMN Cor 4.19; O-5/D-7a-c (leaf verdicts consume F1/F4 +
O-2a saturation; the bijection triple stays O-5's); O-7 (X1) = K-OB-C + F1,
(X4) = F1 + K-OB-E; D-16 (consumes OB1/OB2 + F1–F5 — the design engineered F6
as run-correspondence precisely so D-16's execution transport has its carrier,
V5 defect (3)); D-11; D-15 (consumes D-14 + O-1thr (K2) + F1/F2 + (τ-irr)).

## 5. DECOMPOSITION INTO PROVER UNITS (each ~1 verify-brief)

| unit | content | consumes | gate |
|---|---|---|---|
| **JC-N** | the numerics wave: G-F6 + G-F3 (new) + U6-length-3 (G-F1/F2/F5) + G-EMIT/G-CEIL extensions | harnesses | IS the gate wave; runs FIRST |
| **JC-0** | statement layer as theorems-of-definitions: Cons^τ well-posedness (t-i consistency), T_can(f) truncation laws, N(𝐇) definition + D4R.4/L12 reconciliation, the IND package statement + acyclicity display | O-2a carrier, T-6, GMN | G-CEIL |
| **JC-1** | OL-2a-1 (lift admissibility + (16)-normalization) | GMN Thm 2.11/Prop 2.10 | F3B-style order-2 checks |
| **JC-2** | OL-2a-2 rev-2 clauses (a)–(d) (identity frame crossing + positional transport); records the (M6b) discharge | F.0 interface, GMN Def 2.5 | G-F5 |
| **JC-3** | OL-2a-3 (anchor-normalized residual = twisted residual; ONE proof shared with O-9 OL-B) | F.0–F.2, GMN Defs 2.19–2.21 | O-9's Artin–Schreier gate |
| **JC-4** | OL-2a-4 (emission discipline) + K-OB-E | engine flow, Def 3.9 | G-EMIT |
| **JC-5** | face F5 step lemma (IH-interfaced) | JC-1..4, IH | G-F5 |
| **JC-6** | face F1 step lemma | JC-2/3/4, JC-5, O-1thr Thm 1, Cons^τ | G-F1 |
| **JC-7** | face F2 step lemma (hardest O-3 unit) | IH(F1/F5), D-14, roster totality, K-OB-E | G-F2, G-F2t |
| **JC-8** | face F3 (nonempty locus, canonicalized) | O-14a′, D-14, C.1.5 | G-F3 |
| **JC-9** | face F4 (acceptance) | JC-6/7, O-1thr, TB-CAP | G-F4 |
| **JC-10a** | TT-DET (+ the ∼_OM/Okutsu-equivalence transcription) | GMN §3, BNS §2; citation pull FIRST | G-F6 |
| **JC-10b** | MF-MATCH (+ published-flow transcription) | BNS §4/GMN §4.2 | G-MF |
| **JC-10c** | face F6 assembly (OB1) | JC-6/7/5 + JC-10a/b | G-F6 |
| **JC-11** | K-OB-C (citation pull first) | GMN/Guàrdia–Nart | G-OBC |
| **JC-12** | OB2 (σ-invariance) | O-2a(i), BNS §2 transcription | G-OB2 |
| **JC-13** | K-OB-A + K-OB-B corollaries | O-1thr, O-13, F2 | rides G-F2 |
| **JC-14** | MASTER: the well-founded induction assembly (checks each step lemma's IH interface; base case wiring) | all step units | full gate suite green |

Dispatch order: JC-N → JC-0 → {JC-1, JC-2, JC-3, JC-11, JC-12 in parallel} →
JC-4 → JC-5 → JC-6 → {JC-7, JC-8} → JC-9 → JC-13 → {JC-10a, JC-10b} → JC-10c
→ JC-14. Each step-lemma unit receives the IH as an explicit displayed
hypothesis (the package at < (N, k)) — no unit re-proves another face.

## 6. Where the design answers V5's architectural defects (cited)

* **V5 defect (1) — "K-DICT lacks a coherent carrier/equality design."**
  Answered UPSTREAM by O-2a's DES-1..7 rev-2 (formal codomain 𝔗, literal
  equalities, intrinsic positional Cons_f, Lemma R); this cluster adds NO new
  carrier — OB1/OB2 are stated on 𝔈/𝔗 with the Okutsu quotient appearing ONLY
  as TT-DET's explicit equivalence ≈ (the "further quotient" DES-4 promised),
  and the classifier quantifier in OB1 is ELIMINATED via F1/F2 (traces = Cons^τ
  sets) rather than carried as a primitive.
* **V5 defect (2) — "CYL is not implied by its listed faces."** The design does
  NOT claim CYL and does not consume it. It supplies exactly the inputs V5
  found missing: D-14 is consumed as a separate upstream node (F2's lawful-site
  quantifier), O-1thr's (K2) window closure stays with D-15, and the (τ-irr)
  perimeter is inherited-conditional and displayed (§2.4). D-15 assembles
  DOWNSTREAM from D-14 + O-1thr + F1/F2 — the non-implication is honored by
  keeping it a separate node.
* **V5 defect (3) — "K-READ-δ lacks execution transport."** D-16 stays outside
  the cluster (per D1.3 step 3) and BNS Thm 3.13 is not consumed here; F6 is
  deliberately stated as RUN correspondence (not factorization correspondence)
  so that D-16 = LIT-5 + OB1/OB2 + F1–F5 composes with no new mechanism.

## 7. Open design questions for the Codex plan review (explicit asks)

1. Is the (O5) resolution-level definition (max per-site ceilings + verdict
   window) the right induction measure, or must the L12 N(η,⊤) form be primary
   (JC-0 reconciliation direction)?
2. F6's correspondence is stated up-to-≈ with recentering-run pooling. Is
   there a cheaper TRUE statement (e.g. correspondence only of collapsed
   skeletons + per-node invariants) that still serves D-16? The G-F6 gate
   should decide empirically before JC-10a dispatches.
3. Does OB2 really evade the induction (§2.1's route via O-2a(i) + Okutsu
   invariance), or does "the paper's OM-factorization relation" quantify over
   traces in a way that pulls it into F6?
4. The (M6b)-discharge convergence (§2.4): should JC-2/3 be re-scoped to state
   the O-1thr vertex-transport clause verbatim as a corollary, so ONE verifier
   pass covers both consumers?
5. Is the F2 ← D-14 consumption free of the V6-finding-14 circularity in the
   OTHER direction (D-14 is stated for lawful sites without realization — the
   design believes yes; confirm the quantifier orientation survives).

## VERDICT

**DESIGNED** — statement layer (six-face package IND(N) + OB2 + five named
auxiliary lemmas, all in the O-2a rev-2 carrier vocabulary), gate list (12
gates, 2 new investments, one-shot kill criteria named), dependency map
(consumes 12 inputs with statuses; supplies 9 downstream nodes), decomposition
(16 prover units with dispatch order and IH interfaces). No mathematics is
claimed proved by this unit. Next: Codex plan review with §7's five asks, then
JC-N (the gate wave) before any prover dispatch.

---

# REVISION 1 (2026-07-31, post-V16) — the right-sizing pass

V16 (report `V16_o3design.jsonl`) REJECTED the design: 6 blockers + 8
advisories, with ONE central diagnosis — faces stated STRONGER than any
consumer needs (the reviewer's finding 12 lists the instances; findings 1–5/7
are where the over-strength breaks well-posedness or provability). §§0–7 above
are kept byte-stable as the record of the reviewed state; where a REVISION 1
clause conflicts with them, REVISION 1 governs. The repair method: walk the
tree's consumer list per face (§R2), restate each face at the strength its
strongest actual consumer uses (§R3), re-fit every gate to its stated
quantifier or narrow its advertised kill (§R4), reorder dispatch with the
statement-layer type-check first (§R5), and replace the U6-as-base language
with the PROVED base (§R5).

## R1. Disposition table — all 14 V16 findings

| # | V16 finding (compressed) | class | disposition |
|---|---|---|---|
| 1 | T_can(f) := Cons^τ-set silently replaces the O-3 target (no adequacy with GMN's t_•(f)) | CRIT | **ACCEPTED** → new named lemma **(ADEQ)** (§R3): Θ induces a prefix-tree isomorphism T_can(f) ≅ t_•(f) over F_rep — lands-in + injectivity are PROVED (O-2a + Lemma R); the SURJECTIVITY leg (read-back construction) is the new open clause, priced into JC-0. K-RUN-as-designed implies K-RUN-as-in-tree only THROUGH ADEQ; displayed as such |
| 2 | F6 claims a raw-run bijection its ingredients cannot give (quotient ≠ raw) | CRIT | **ACCEPTED** → **F6′** (§R3): stated at the pooled/quotient level only; raw-run bijection WITHDRAWN (the caterpillar already forbade it — the rev-0 text was internally inconsistent) |
| 3 | TT-DET preserves no level filtration, so it cannot restrict to same-N run sets | CRIT | **ACCEPTED** → **TT-DET′** (§R3): restated as a FILTERED isomorphism (compatible system over N, preserving the primary level N*); the level clause is flagged as the design's single riskiest claim, gate-tested (G-F6′) before JC-10a dispatches; bounded-shift fallback recorded |
| 4 | (O5) max-of-ceilings is not a semantic truncation level (ceilings are upper bounds; F1's ≤ N unprovable from O-1thr) | CRIT | **ACCEPTED** → the D4R.4/L12 per-branch level **N\*** is PRIMARY (§R3 (O5′)); max-of-ceilings demoted to the one-directional upper bound **(CEIL-UB)** (all K-OB-A needs); F1′'s conformance clause re-warranted as ENGINE mechanics (OL-2a-4 + L12 window), not an O-1thr consequence |
| 5 | every-lift quantifier ill-typed (nonseparable lifts) and subsumes a cylinder law (unacknowledged CYL) | CRIT | **ACCEPTED** → every-lift WITHDRAWN from F1/F4 (selected-f forms, §R3); all residual lift quantifiers typed over monic SEPARABLE lifts (JC-0 duty); cylinder content routed to D-15 downstream where the ns-guard is explicit — the design still neither claims nor consumes CYL, now truthfully |
| 6 | intra-step order F5→F1→F2→F4→F6 genuinely acyclic | ADV+ | **RECORDED** — §2.3 stands byte-stable; the assumption it rests on (TT-DET/MF-MATCH invoke no run correspondence) is re-checked against TT-DET′ (still true: TT-DET′ is Cons^τ-side only) |
| 7 | F3's route misses lawful ⇒ coherent (O-14a′ realizes only coherent histories) | CRIT | **ACCEPTED** → **F3′** re-indexed to COHERENT chains (`HistoryCoherent`, O-14a′'s actual compiled scope); the lawful→coherent bridge named **(LC-COH)**, displayed OPEN and UNCONSUMED (no current consumer needs lawful-chain indexing — §R2); G-F3 kill criterion narrowed accordingly (§R4) |
| 8 | "D-14 (the next semantic read is MENU-LAWFUL)" misattributes the bridge; no named statement discharges it | ADV | **ACCEPTED** → new named lemma **(SEM-LAWFUL)** (§R3), owned by JC-7's spec: the semantic next read of a Cons_f chain is menu-lawful at the F5-identified frame state (from roster totality (M6a)/(M6b) + O-2a positional clauses + K-OB-E); D-14 supplies ONLY locality at the lawful site |
| 9 | OB2 genuinely level-free (BNS Defs 1.7/3.1–3.2 quantify over factors, not traces); Thm 3.13 cannot supply TT-DET implicitly | ADV+ | **RECORDED** — §7 ask 3 answered; JC-12 unchanged; the BNS definition numbers are pinned into JC-12/JC-10a's citation-pull duty |
| 10 | load-bearing F6 content = filtered pooled execution structure + verdicts + refinement blocks (raw runs too strong, bare skeleton+invariants too weak) | ADV | **ACCEPTED** → F6′ is pitched at exactly this middle (§R3); §7 ask 2 answered |
| 11 | (M6b) should be an explicit joint corollary of JC-2/3, not an "expected discharge" | ADV | **ACCEPTED** → JC-2's spec states the O-1thr (M6b) interface conclusion VERBATIM as a displayed corollary, with JC-3's residual-identification input recorded; one verifier pass, two consumers (§R6) |
| 12 | over-strength list: F5 literal identity; TT-DET whole-tree; F6 raw bijection; F1/F4 every-lift; F4 all-N biconditional; F3 lawful chains | ADV | **ACCEPTED per item** → F1/F3/F4/F6/TT-DET right-sized (§R3). F5 is the ONE deliberate retention: its literal strength is purchased upstream (OL-2a-2 identity-frame clauses deliver on-the-nose equalities), so weakening buys no proof reduction and would break the verbatim-consumption discipline — displayed as intentional |
| 13 | gates don't test their stated quantifiers (F1 lifts, F4 all-N, N(𝐇) direction) | ADV | **ACCEPTED** → §R4: G-F1′ narrowed to the selected-f claim; NEW G-LIFT rider tests the two-lift transfer where it now lives (O-1thr/D-14); G-F4′ sweeps ALL working levels with split kill criteria; G-CEIL′ tests the conformance DIRECTION (ceiling ≤ working level) plus CEIL-UB |
| 14 | JC-0 is the cheapest falsifier and isn't first; finite U6 survival cannot be an inductive base | ADV | **ACCEPTED** → dispatch reordered JC-0 FIRST, then JC-N with G-F6′ first among computational gates (§R5); base language REPLACED: the base is the PROVED O-2a Thm 1 + OL-5 order-1 base (V20-confirmed); U6 demoted to corroboration everywhere (§R5) |

§7's five asks are hereby absorbed: ask 1 → finding 4's repair; ask 2 →
finding 10; ask 3 → finding 9; ask 4 → finding 11; ask 5 → findings 6 + 8.

## R2. The consumer-to-face table (the right-sizing warrant)

Walking §4's supply list against the tree (`MATH_COMPLETION_TREE_2026-08-01.md`
node texts): what each consumer of the cluster ACTUALLY uses.

| consumer (tree node) | what it needs from the cluster | right-sized form that suffices |
|---|---|---|
| K-14 MarkGraft (I0) extend/graft | realized censuses extend | F2′ + F3′ — the coherent-chain form suffices: grafted extensions extend realized (hence Cons^τ) prefixes, which are coherent by construction |
| K-14 (I1) faithful census | realized counts = semantic counts per stratum | F1′ + F2′ at the box's own f — no lift quantifier |
| K-14 (I3-rc) | frame-state premise at recenterings | F5 (as stated) |
| O-4 OL1-ii (agreement seam) | run terminates below finite N(f) AND Cert accepts there | F1′ conformance clause + **F4-C** at N ≥ N(f) + GMN Cor 4.19 — completeness at the DECISION level only |
| O-5 + D-7a/b/c (leaf verdicts) | accepted leaf ⇒ true factor datum | **F4-S** (soundness, selected f) + O-2a saturation + F1′; D-7c's all-lifts clause routes through D-15's cylinder law, NOT an F1 lift quantifier |
| O-7 (X1) | realized read ⇒ root-tracking disk | F1′ + K-OB-C |
| O-7 (X4) | first-read wildness | F1′ + K-OB-E |
| D-15 (CYL, downstream assembly) | decided classes = cylinder unions | D-14 + O-1thr (K2) + F1′/F2′ + (τ-irr) — THIS node owns lift-uniformity, with the ns-guard explicit |
| D-16 (δ execution transport) | run correspondence at ∼_OM pairs | **F6′** (filtered, pooled, verdict-preserving) + OB2 + F1′–F5 — per V16 finding 10, raw-run bijection NOT needed |
| D-11 / mass-id | σ invariance | OB2 (level-free) |
| K-4/K-6 repairs | via D-15 | indirect — no direct face consumption |

**The display:** NO consumer requires (a) Cons_g^τ for every lift, (b) the F4
biconditional at every N, (c) a raw-run bijection, (d) lawful-chain-indexed
nonemptiness. Each withdrawn quantifier reappears, if at all, in the
downstream node that owns it (D-15) or as a displayed unconsumed lemma
(LC-COH).

## R3. The revised statement layer (supersedes §2.1's F1/F3/F4/F6, §2.2's TT-DET, and (O5))

Standing: f monic separable ns-free of degree n over O, x_f := f mod p^N.
EVERY residual lift quantifier in the layer ranges over monic SEPARABLE lifts
(JC-0 types every domain; V16 finding 5's ill-posedness cured at the root).

* **(O5′) The primary resolution level.** N\*(𝐇) := the D4R.4/L12 per-branch
  level N(η,⊤) of 𝐇's end state (the exact level at which the branch state is
  realized), joined at a terminal node with the TB-CAP verdict window ((τ-hen)
  N_V = 1; (τ-irr) the level-N(η) window). This is THE truncation level — the
  project's earlier per-branch resolution stays primary (V16 finding 4).
  Induction measure: (N, k) lexicographic with N = N\*.
* **(CEIL-UB) — the demoted (O5) expression; JC-0 lemma.** N\*(𝐇) ≤
  max_i L(H_i, ν_i) ∨ (verdict window): the max of the O-1thr per-site
  ceilings BOUNDS the primary level (each read is determined below its
  ceiling, so the branch state is pinned below the max). One direction only —
  exactly what K-OB-A consumes. No minimality or equality is claimed.
* **(F1′_N — no-phantom, selected-f form).** Every 𝐇 ∈ Run_N(x_f) satisfies
  Cons_f^τ(𝐇), and N\*(𝐇) ≤ N. The conformance clause is warranted by ENGINE
  mechanics (the working-level-N run reads only digits below N: OL-2a-4
  emission discipline + the L12 window bookkeeping), NOT by O-1thr ceilings —
  V16 finding 4's provability objection lands on the rev-0 warrant, and this
  is the repair. [Every-lift clause WITHDRAWN: ill-typed on nonseparable
  lifts, and jointly with F2 it was an unacknowledged cylinder law (V16
  finding 5); fiber invariance below the ceiling lives in O-1thr Thm 1/D-14
  and is consumed by D-15, not asserted here.]
* **(F2′_N — no-missing).** Every 𝐇 ∈ T_can(f) with N\*(𝐇) ≤ N lies in
  Run_N(x_f). [Unchanged except keyed to N\*.]
* **(F3′_N — nonempty locus, coherent form).** Every COHERENT chain
  (`HistoryCoherent`, the O-14a′ predicate — the realizer theorem's actual
  scope) with N\* ≤ N, bookkept under the (O6) canonicalizations, has a monic
  separable witness g in its level-N digit cylinder with the corresponding
  history in T_can(g). **(LC-COH)** — "every fresh-frame-lawful chain is
  coherent/witnessed" — is NOT claimed, displayed OPEN, and consumed by
  nothing in the tree (§R2); if a future census consumer demands lawful-chain
  indexing, LC-COH must be proved then (V16 finding 7).
* **(F4_N split — acceptance).** **(F4-S, soundness, every N):** Cert accepts
  (x_f, 𝐇) ⇒ 𝐇 ∈ Run_N(x_f) AND 𝐇 is verdict-carrying in T_can(f).
  **(F4-C, completeness at the decision level):** if 𝐇 ∈ T_can(f) is
  verdict-carrying and N ≥ N\*(𝐇), then Cert accepts (x_f, 𝐇). Displayed
  corollary: for N ≥ N\*(𝐇) the two give the biconditional — the all-N
  biconditional and its lift quantifier are WITHDRAWN (V16 findings 5/12; §R2:
  OL1-ii uses F4-C at the decision level, D-7a-c use F4-S).
* **(F5_N — unchanged, intentionally.)** Literal identity of key/valuation/
  tower/position is retained: OL-2a-2's identity-frame clauses supply it
  on-the-nose, so the strength is free, and every consumer quotes those
  clauses verbatim. The one deliberate over-strength, displayed (V16
  finding 12).
* **(F6′_N — pooled filtered trace correspondence = OB1 at level N).** For
  f ∼_OM g: writing P_N(f) := (Run_N(x_f) pooled by collapsing maximal
  recentering runs)/≈, there is an isomorphism P_N(f) ≅ P_N(g), compatible
  with truncation P_{N+1} → P_N, preserving per-node (e_i, h_i, g_i, μ_i),
  terminal verdicts AND acceptance, branch incidence/multiplicity of the
  pooled tree, and matching refinement blocks (maximal recentering runs)
  one-to-one with same-degree refinement iterations of the published Montes
  flow (MF-MATCH). Explicitly NOT claimed: any bijection of raw run sets (the
  caterpillar forbids it). This is V16 finding 10's load-bearing middle —
  strong enough for D-16's execution transport, no stronger.
* **(TT-DET′ — filtered type-tree determinacy; supersedes TT-DET).** For
  f ∼_OM g: a system of isomorphisms T_can(f)^{≤N}/≈ ≅ T_can(g)^{≤N}/≈
  (T^{≤N} := {𝐇 : N\*(𝐇) ≤ N}), compatible with N → N+1, preserving
  (e_i, h_i, g_i, μ_i), collapsed recentering runs, and terminal verdicts —
  equivalently, ONE quotient-tree isomorphism that PRESERVES N\* on pooled
  classes. The level-preservation clause is the design's single riskiest
  claim (V16 finding 3): G-F6′ tests it empirically BEFORE JC-10a dispatches.
  Recorded fallback if the gate kills on-the-nose preservation: a
  bounded-shift form (N\* preserved up to an explicit constant of the ∼_OM
  data) — D-16's rate consumer tolerates a uniform additive shift; adjudicate
  at gate results, do not paper over.
* **(ADEQ — T_can adequacy; the finding-1 repair).** Over the pinned family
  F_rep, Θ restricted to T_can(f) induces an isomorphism of prefix trees onto
  GMN's type tree t_•(f) with verdict decoration: (i) lands-in — PROVED
  (O-2a Thm 1/2 scope, seam-conditional at orders ≥ 2); (ii) SURJECTIVITY —
  OPEN, the read-back construction: a t_•(f) node's side/residual data is
  exactly the data Cons_f's intrinsic clauses demand, so build the dressed
  history level by level (conditional on OL-2a-1 admissibility); (iii)
  injectivity on all-continuing — PROVED (Lemma R) — plus terminal
  correspondence via O-2a Thm 2(B)/Cor 3.8. WITHOUT ADEQ, Run_N = T_can(f)_{≤N}
  is a theorem about the design's object, not the tree's O-3; WITH it, the
  original K-RUN target is recovered. Owner: JC-0 (leg (ii) is its hardest
  clause and may split off as JC-0b).
* **(SEM-LAWFUL — the finding-8 repair; owned by JC-7's spec).** For an
  all-continuing 𝐇 ∈ T_can(f) whose frame state is identified by F5 on the
  strict prefix: every immediate Cons_f-extension of 𝐇 corresponds to a read
  that is MENU-LAWFUL at that frame state. Warrant: roster totality
  ((M6a)/(M6b) — the menu lists ALL sides + residual profiles readable at the
  state) + O-2a positional clauses (c1)/(c2) (semantic side data IS frame
  positional data) + K-OB-E (continuing ⇒ μ ≥ 2). D-14 then supplies ONLY
  locality at that lawful site — the quantifier orientation of §2.3 is
  unchanged; the bridge now has a name and an owner.

F2's step, restated with the names: IH-F2 realizes the strict prefix; IH-F5
identifies its frame state; **SEM-LAWFUL** shows the next semantic read is on
the menu; **D-14** localizes it; roster finiteness + K-OB-E close the child
set. (This is V16 finding 8's own reconstruction, adopted verbatim.)

## R4. Gate fixes (supersedes the affected §3 rows; V16 finding 13)

| gate | fix | new advertised kill criterion |
|---|---|---|
| **G-F1′** | criterion NARROWED to the face's actual quantifier | any realized history on box x_f failing Cons_f^τ for the box's OWN f (canonical instantiation) — the every-lift kill is retired with the clause |
| **G-LIFT** (NEW rider) | tests the two-lift transfer where it now lives (O-1thr Thm 1 / D-14, consumed by D-15) | per box sample ≥ 3 monic separable lifts incl. extremal digit patterns above level N; ANY two lifts of one box with different level-N realized run sets or per-site read sets |
| **G-F4′** | all-N sweep: run Cert at EVERY working level N = 1..N(f)+2 per box | kill-S: accepted-but-semantically-wrong at ANY N (kills F4-S); kill-C: verdict-carrying semantic 𝐇 with N\*(𝐇) ≤ N unaccepted at N (kills F4-C) |
| **G-CEIL′** | direction FIXED: test conformance (ceiling ≤ working level), not just reads-below-ceiling | kill-1: a realized read on a working-level-N run with N\*(𝐇) > N (kills F1′ conformance); kill-2: a history with N\* > the max-ceilings expression (kills CEIL-UB); the old reads-above-ceiling check retained as the O-1thr regression |
| **G-F6′** | extended to the filtered claim | pooled traces compared WITH per-history N\* levels and terminal verdicts/acceptance; any ∼_OM pair mismatching pooled structure, verdicts, OR N\* levels (a level-only mismatch kills the TT-DET′ level clause → adjudicate the bounded-shift fallback) |
| **G-F3′** | kill criterion NARROWED to the coherent form | an EMPTY predicted-nonempty stratum of a COHERENT chain kills F3′; an empty lawful-but-incoherent stratum refutes nothing here — it is a recorded finding against LC-COH/census indexing |

Unchanged rows: G-F2, G-F2t, G-F5, G-MF, G-OB2, G-OBC, G-EMIT (their stated
quantifiers already match their claims).

## R5. Reordering + the base repair (supersedes §5's dispatch head and §2.3's base paragraph; V16 finding 14)

**Dispatch order revised:** **JC-0 FIRST** — the pure statement-layer unit is
the cheapest falsifier of the whole design (it would have surfaced V16
findings 1–5 pre-review): formal type-check of Cons^τ (t-i), T_can truncation
laws, ADEQ statement + legs (i)/(iii) wiring, N\* definition + CEIL-UB, every
lift domain typed monic separable, the six REVISED faces + the §2.3 acyclicity
display re-verified against them. THEN JC-N (the gate wave) with **G-F6′
first** among the computational gates (hardest conjecture, cheapest kill),
G-F3′ second; then {JC-1, JC-2, JC-3, JC-11, JC-12 in parallel} → JC-4 → JC-5
→ JC-6 → {JC-7, JC-8} → JC-9 → JC-13 → {JC-10a, JC-10b} → JC-10c → JC-14.

**Base case, restated:** the inductive base is PROVED mathematics — O-2a
Theorem 1 (order ≤ 1, all clauses incl. the j₀ corner and k′ = 0) with the
OL-5 first-read base, per V20's confirmation of O-2a rev-3 (SOUND-WITH-GAPS;
both findings justification-gap class; the verifier's own summary: "OL-5(b)/(c),
together with OL-4(d), fully establish the order-1 base without an undeclared
engine-semantics assumption") + the compiled length-≤1 forge instances + K-12's
n = 2 anchor. **U6's exhaustive depth-2 survival is CORROBORATION ONLY** — a
numeric floor above the base, never cited as a base-case proof. Every "U6
sits directly above the base" phrasing in §§2.3/2.1 is superseded by this
paragraph.

## R6. Unit-spec deltas (supersedes the affected §5 rows)

* **JC-0** (now FIRST): gains ADEQ (surjectivity leg = hardest clause, may
  split off as JC-0b), CEIL-UB, the N\* primary definition (no reconciliation
  duty remains — the L12 form IS the definition), and lift-domain typing.
* **JC-2**: states the O-1thr (M6b) interface conclusion VERBATIM as a
  displayed joint corollary (JC-3's residual identification recorded as
  input) — one verifier pass serves both consumers.
* **JC-6** (F1′): selected-f form; the conformance clause proved from
  OL-2a-4 + L12 window mechanics, not from O-1thr ceilings.
* **JC-7** (F2′): gains SEM-LAWFUL as a displayed lemma of its spec.
* **JC-8** (F3′): re-keyed to `HistoryCoherent` chains; (O6)
  canonicalizations retained for census bookkeeping; LC-COH displayed
  unconsumed.
* **JC-9** (F4): split into the F4-S and F4-C legs with their separate kill
  criteria.
* **JC-10a** (TT-DET′): filtered form; the level clause is the unit's
  declared crux; BLOCKED until G-F6′ reports.
* **JC-10c** (F6′): assembly at the pooled level; raw-bijection language
  purged.
* **JC-12, JC-13**: unchanged (V16 finding 9 confirms OB2's evasion; BNS
  Defs 1.7/3.1–3.2 pinned into the citation-pull duty; Thm 3.13 recorded as
  unable to supply TT-DET implicitly).
* Proposed TREE delta (recorded, not executed here): O-3's clause-3 wording
  ("every fresh-frame-lawful assignment chain") to be re-keyed to the
  coherent-chain form at the next tree edit, with LC-COH listed as the
  displayed residue; O-3's "of any lift f" phrase inherits the D-15 routing.

## REVISION 1 VERDICT

**REVISED** — all 14 V16 findings dispositioned (6 blockers repaired by
right-sizing + three new named lemmas ADEQ/SEM-LAWFUL/CEIL-UB + one displayed
non-claim LC-COH; 8 advisories absorbed: 3 as repairs, 2 as confirmations
recorded, 3 as reorderings/demotions). The revised layer claims, for each
face, exactly the strength of its strongest tree consumer (§R2 table); the
one deliberate over-strength (F5) is displayed with its warrant. No
mathematics is claimed proved by this revision. Next: re-review of the
revised layer (brief rev-2), then JC-0 before any gate or prover dispatch.
