# O3design REV 2 — SELF-CONTAINED plan-review brief: the O-3 ⊕ O-2b joint cluster design (post-V16 right-sizing)

**What you are reviewing.** REVISION 1 of a DESIGN (not a proof) for the
hardest remaining object of a mathematical completion campaign: the joint
cluster "realization faithfulness + trace correspondence" for a p-adic
polynomial-factorization classifier. A prior hostile review (V16) REJECTED
rev 1 with one central diagnosis — faces stated STRONGER than any consumer
needs — plus specific well-posedness breaks. This brief presents the REVISED
layer. Your charge: adversarial PLAN review — attack the revised statement
layer (well-posed? non-circular? strong enough for the named consumers, no
stronger?), the adequacy repair, the induction measure, the gate list (does
each falsifier test its stated quantifier?), and the per-finding repairs
(§6: does each repair actually answer its finding?). Quote each offending
passage; classify *critical defect* vs *gap*. Fix nothing.

## 0. Setting (all context you need)

Fix a prime p, O = ℤ_p, residue field F = F_p. For f ∈ O[x] monic separable
of degree n, the Okutsu–Montes (OM) machinery (Guàrdia–Montes–Nart, Trans.
AMS 364 (2012) — "GMN") resolves the irreducible factors of f by a tower of
Newton polygons: order-1 polygon w.r.t. a key φ₁ (a monic lift of an
irreducible factor ψ₀ of f̄), residual polynomials over growing finite fields
F₁ ⊂ F₂ ⊂ ⋯, higher-order polygons w.r.t. recursively built keys. A "type"
is the discrete datum (φ₁; λ₁, ψ₁; …; λ_r, ψ_r); the type tree t_•(f) (GMN
Def 3.10) branches over slopes and residual factors; a type with residual
multiplicity 1 certifies an irreducible factor with e = e₁⋯e_r, f = f₀⋯f_r
(GMN Cor 3.8). GMN notes its type sets depend on representative choices.

The project has a combinatorial ENGINE (a digit-reading classifier on residue
classes x ∈ (O/p^N)^n) intended to realize this semantics uniformly in p.
The accepted upstream dictionary unit ("O-2a", now at rev 3, verifier verdict
SOUND-WITH-GAPS with both findings justification-gap class) built:

* **The carrier.** 𝔈 = dressed histories 𝐇 = (ρ₀; ν₁,…,ν_k): ρ₀ = (ψ̂₀, a₀);
  nodes ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i) recording one
  polygon-side read (slope −h_i/e_i, residual degree ℓ_i, initial point
  (s_i, u_i)), dressed with the selected residual irreducible ψ̂_i of degree
  g_i and multiplicity μ_i. Well-formedness laws W1–W5. Equality is literal;
  the fields F_i are explicit iterated quotients.
* **Θ and Cons_f.** Θ maps 𝐇 to its formal type-chain datum (total,
  truncation-compatible); a pinned representative family F_rep (one canonical
  key lift per chain) makes GMN's objects single-valued. Cons_f(𝐇) is defined
  INTRINSICALLY: a₀ matches, each level's (e_i, h_i, ℓ_i) and (s_i, u_i) are
  the data of a side of the order-i polygon N_i^−(f) in the order-i GMN
  integer frame, and ord_{ψ̂_i}(R_{λ_i}(f)) = μ_i. NO realization semantics.
  O-2a proved (order ≤ 1 OUTRIGHT — Theorem 1 incl. the OL-5 first-read base,
  the j₀ corner, k′ = 0; all orders modulo four named seam lemmas
  OL-2a-1..4): Cons_f histories LAND IN the type tree, invariants match
  (accE = ∏e_i, accF = f₀∏g_i; saturation ⇔ μ = 1), certified nodes charge
  ind(f) ≥ 1 each, and Θ is injective on all-continuing Cons_f histories
  (Lemma R). NOTE: lands-in + injectivity only — NOT surjectivity onto
  t_•(f). That gap is now the explicit lemma (ADEQ), §2.
* **Adjacent verified inputs:** "O-1thr": per history-site a computable read
  ceiling L(H, ν) — a SUFFICIENT bound: whether the run reads the site
  depends only on digits below L (proved per-policy modulo ONE interface
  assumption (M6b) = depth-≥2 vertex-read transport). "D-14": same for sites
  merely menu-LAWFUL at the frame state (not presupposed realized). "O-14a′":
  at ambient residue field ZMod p, every COHERENT history (predicate
  `HistoryCoherent`) has a center realizer — proved incl. the terminal flank.
  "O-13/D-12": collapsed tree shapes form a finite p-free set; arbitrarily
  long recentering runs collapse to one node ("the caterpillar": for
  f_m = (x−a)(x−b) with v_p(a−b) = m+1, raw node counts grow unboundedly, so
  only POOLED/collapsed structures can correspond across polynomials).
  "D4R.4/L12": the project's per-branch resolution level N(η,⊤) — the exact
  level at which a branch state is realized. "TB-CAP": terminal verdict
  windows ((τ-hen) N_V = 1; (τ-irr) a level-N(η) window). "U6": an exhaustive
  numeric probe at depth ≤ 2, all (n, p) ∈ {2,3}²: realized run set =
  semantic truncation EXACTLY (174/174 strata, 0 phantoms) — CORROBORATION
  only, never a base case.

**The cluster.** O-3 (K-RUN): the realized run set at level N is EXACTLY the
level-N truncation of the semantic tree (four clauses: no-phantom,
no-missing, nonempty locus, acceptance) + auxiliaries K-OB-A/B/C/E. O-2b:
K-DICT-OB1 (trace correspondence under the published OM-factorization
equivalence) + K-DICT-OB2 (σ-invariance). Mutually dependent (no-phantom
needs engine-reads → GMN-data; OB1 quantifies over the classifier's traces);
resolved by ONE well-founded induction on resolution level, package IND(N)
bundling six faces, faces at level N consuming faces at < N and, within a
level, a displayed acyclic order (V16 confirmed acyclicity).

## 1. Definitions

* **Cons_f^τ** — terminal-extended consistency: Cons_f on the continuing
  prefix + the terminal record FORCED by the prefix ((τ-irr) μ_last = 1,
  verdict pair = (accE, accF); (τ-hen) slope-−∞ side, verdict (1, f₀)).
  Consistency of the extension ("no free choice") is a stated lemma (JC-0).
* **T_can(f) := {𝐇 ∈ 𝔈 : Cons_f^τ(𝐇)}**, prefix-ordered — intrinsically
  GMN-defined, no classifier. That T_can is the RIGHT object is not assumed:
  see (ADEQ), §2.
* **Run_N(x)** — the τ-pruned dressed histories the classifier (pinned
  canonical policy; realizer supply proved at ZMod p) emits on box x at
  working level N. Run_N(x) ⊂ 𝔈 is conditional on OL-2a-4 (displayed).
* **N\*(𝐇)** — THE resolution level (primary): the D4R.4/L12 per-branch
  level N(η,⊤) of 𝐇's end state, joined at a terminal node with the TB-CAP
  verdict window. Induction measure: (N, k) ∈ ℕ² lexicographic, N = N\*,
  k = history length. The max-of-per-site-ceilings expression is DEMOTED to
  a one-directional bound: **(CEIL-UB)** N\*(𝐇) ≤ max_i L(H_i, ν_i) ∨
  (verdict window) — a JC-0 lemma; no minimality claimed (a ceiling is only a
  sufficient bound; L valid ⇒ L+c valid).
* **Coherent chains** — `HistoryCoherent`, the O-14a′ predicate (the realizer
  theorem's exact scope). Census bookkeeping keeps the U6-validated
  canonicalizations: branch species = the WHOLE node read; beyond-cap content
  pooled as ('deep', k).
* **f ∼_OM g** — common OM factorization in the published sense
  (Bauch–Nart–Stainsby, LMS JCM 16 (2013) "BNS", Defs 1.7/3.1–3.2 — these
  quantify over factors and separation data, NOT execution traces). BNS
  Thm 3.13 (δ+1 congruence ⇒ ∼_OM) is NOT consumed here (downstream D-16
  only) and supplies no trace statement.
* **Lift typing.** EVERY lift quantifier ranges over monic SEPARABLE lifts
  (a residue box contains nonseparable monic lifts; Cons_g is defined only
  for separable g). JC-0 types every domain.

## 2. THE REVISED STATEMENT LAYER — package IND(N) + satellites

For f monic separable ns-free of degree n, x_f := f mod p^N:

* **F1′_N (no-phantom, selected-f).** Every 𝐇 ∈ Run_N(x_f) satisfies
  Cons_f^τ(𝐇), and N\*(𝐇) ≤ N. The conformance clause is warranted by ENGINE
  mechanics (a working-level-N run reads only digits below N: OL-2a-4
  emission discipline + L12 window bookkeeping) — NOT by O-1thr ceilings.
  [The former "Cons_g^τ for EVERY lift g" clause is WITHDRAWN: ill-typed on
  nonseparable lifts, and jointly with F2 it amounted to an unacknowledged
  cylinder law. Fiber invariance lives in O-1thr Thm 1/D-14, consumed by the
  downstream cylinder node D-15.]
* **F2′_N (no-missing).** Every 𝐇 ∈ T_can(f) with N\*(𝐇) ≤ N lies in
  Run_N(x_f).
* **F3′_N (nonempty locus, coherent form).** Every coherent chain with
  N\* ≤ N has a monic separable witness g in its level-N digit cylinder, with
  the corresponding history in T_can(g). "Every menu-lawful chain is
  coherent" **(LC-COH)** is NOT claimed — displayed open, consumed by no tree
  node.
* **F4_N (acceptance), split.** **(F4-S, soundness, every N):** Cert accepts
  (x_f, 𝐇) ⇒ 𝐇 ∈ Run_N(x_f) AND 𝐇 verdict-carrying in T_can(f). **(F4-C,
  completeness at the decision level):** 𝐇 ∈ T_can(f) verdict-carrying and
  N ≥ N\*(𝐇) ⇒ Cert accepts. Corollary: the biconditional exactly on
  N ≥ N\*(𝐇). No all-N biconditional, no lift quantifier.
* **F5_N (state coherence).** For 𝐇 ∈ Run_N(x_f): engine frame state after 𝐇
  = the GMN state data of its chain — key, valuation u = v_{k+1}, tower
  F_{k+1}, position, all on the nose. DELIBERATELY stronger than consumers
  need: the strength is purchased upstream (OL-2a-2 identity-frame clauses
  are on-the-nose equalities), weakening buys no proof reduction. The one
  displayed intentional over-strength.
* **F6′_N (pooled filtered trace correspondence = OB1 at level N).** For
  f ∼_OM g, write P_N(f) := (Run_N(x_f) pooled by collapsing maximal
  recentering runs)/≈ (≈ = TT-DET′'s explicit representative equivalence).
  Claim: P_N(f) ≅ P_N(g), compatibly with truncation P_{N+1} → P_N,
  preserving per-node (e_i, h_i, g_i, μ_i), terminal verdicts AND acceptance,
  branch incidence/multiplicity, and matching refinement blocks one-to-one
  with same-degree refinement iterations of the published Montes flow
  (MF-MATCH). NOT claimed: any bijection of raw run sets (the caterpillar
  forbids it). Sized to the δ-transport consumer D-16: filtered pooled
  execution structure + verdict + refinement-block correspondence.

**OB2 (satellite, level-free).** f ∼_OM g ⇒ σ(f) = σ(g). Route: per-factor
(e, f) = (accE, accF) are functions of the type's discrete data (O-2a clause
(i)); Okutsu equivalence preserves them (BNS §2 transcription); σ = the
multiset. Not inductive (V16 confirmed the published relation quantifies over
factors, not traces).

**Named auxiliary lemmas:**

* **(ADEQ — T_can adequacy; NEW, the target-identification repair).** Over
  F_rep, Θ|_{T_can(f)} induces a prefix-tree isomorphism onto GMN's t_•(f)
  with verdict decoration: (i) lands-in — PROVED (O-2a, seam-conditional at
  orders ≥ 2); (ii) surjectivity — OPEN: the read-back construction (a
  t_•(f) node's side/residual data is exactly what Cons_f's intrinsic clauses
  demand; build the dressed history level by level; conditional on OL-2a-1);
  (iii) injectivity on all-continuing — PROVED (Lemma R) + terminal
  correspondence (O-2a Thm 2(B)/Cor 3.8). WITHOUT ADEQ, "Run_N = T_can(f)_{≤N}"
  is about the design's object, not the original O-3 target; WITH it, K-RUN
  is recovered. Owner JC-0 (leg (ii) may split off).
* **(TT-DET′ — filtered type-tree determinacy; OB1's core).** f ∼_OM g ⇒ a
  system of isomorphisms T_can(f)^{≤N}/≈ ≅ T_can(g)^{≤N}/≈
  (T^{≤N} := {𝐇 : N\*(𝐇) ≤ N}), compatible with N → N+1, preserving
  (e_i, h_i, g_i, μ_i), collapsed recentering runs, terminal verdicts —
  equivalently one quotient-tree isomorphism PRESERVING N\* on pooled
  classes. The level-preservation clause is the design's declared riskiest
  claim; gate G-F6′ tests it BEFORE the prover unit dispatches. Recorded
  fallback if killed: bounded-shift preservation (N\* up to an explicit
  constant of the ∼_OM data; the D-16 rate consumer tolerates a uniform
  additive shift) — adjudicated at gate results, not assumed.
* **(SEM-LAWFUL — NEW, the F2-bridge name).** For all-continuing
  𝐇 ∈ T_can(f) with frame state identified by F5 on the strict prefix: every
  immediate Cons_f-extension corresponds to a read MENU-LAWFUL at that state.
  Warrant: roster totality ((M6a)/(M6b)) + O-2a positional clauses (c1)/(c2)
  + K-OB-E. D-14 supplies ONLY locality at the lawful site. F2's step: IH-F2
  realizes the strict prefix → IH-F5 identifies the state → SEM-LAWFUL puts
  the next semantic read on the menu → D-14 localizes it → roster finiteness
  + K-OB-E close the child set.
* **MF-MATCH**: maximal recentering runs ↔ same-degree refinement iterations
  of the published Montes flow (citation pull before dispatch).
* **K-OB-C** (Okutsu proximity: Cons_f(𝐇) ⇒ root-tracking disk of radius
  w − C_φ; citation pull first); **K-OB-E** (continuing ⇒ μ ≥ 2; GMN Def 3.9
  arithmetic); **K-OB-A/B** (finite-site assembly via CEIL-UB; stratum
  membership ⇒ realized via F2′): corollary-grade.

**Intra-step order (V16-confirmed acyclic; unchanged).** At (N, k):
F5 ← IH + OL-2a-1/2/3/4; F1′ ← F5 + OL-2a-2(c,d)/3 + Cons^τ; F2′ ← IH(F1′/F5
strict prefix) + SEM-LAWFUL + D-14 + roster totality + K-OB-E; F3′ ← O-14a′ +
D-14 (no F2 use); F4 ← F1′ + F2′ + O-1thr + the (τ-irr) window (inherited
conditionality, displayed); F6′ ← F1′ + F2′ + F5 (the classifier quantifier
in OB1 is eliminated: traces ARE Cons^τ sets, THROUGH ADEQ) + TT-DET′ +
MF-MATCH. TT-DET′/MF-MATCH invoke no run correspondence (Cons^τ-side only).

**Base case (PROVED, not numeric).** O-2a Theorem 1 (order ≤ 1, all clauses,
incl. the OL-5 first-read base — the O-2a rev-3 verifier confirmed "OL-5(b)/(c),
together with OL-4(d), fully establish the order-1 base without an undeclared
engine-semantics assumption") + compiled length-≤1 forge instances + the n = 2
anchor. U6 is corroboration ONLY.

**Displayed inherited conditionality:** (M6b) — now stated VERBATIM as a
joint corollary in unit JC-2's spec (JC-3 input recorded); the (τ-irr)
verdict-pin perimeter; OL-2a-1..3 until their units land.

## 3. GATE LIST (each gate tests its face's STATED quantifier, or its kill is narrowed)

| claim | gate | kill criterion |
|---|---|---|
| F1′ | U6 phantom scan, depth 3 | any realized history on x_f failing Cons_f^τ for the box's OWN canonical f |
| O-1thr/D-14 transfer (feeds D-15; ex-F1 lift clause) | **G-LIFT** (new): per box ≥ 3 monic separable lifts incl. extremal high digits | any two lifts of one box with different level-N realized run sets or per-site reads |
| F2′ | counting tie T = T̂ at depth 3, (n,p) ∈ {2,3}² | any stratum T < T̂ (T > T̂ kills F1′) |
| F2′ terminal | LIVE landing-flank countermodel search | any hit |
| F3′ | stratum census at depth 3 over COHERENT chains | an EMPTY predicted-nonempty COHERENT stratum kills F3′; an empty lawful-incoherent stratum is a finding against LC-COH only |
| F4-S/F4-C | acceptance regression at EVERY working level N = 1..N(f)+2, n ≤ 4, p ≤ 5 vs factorpadic | kill-S: accepted-but-wrong at ANY N; kill-C: verdict-carrying 𝐇, N\*(𝐇) ≤ N, unaccepted at N |
| F5 | state-transport probe depth 3 | any frame/tower/position mismatch |
| F6′/TT-DET′ | **G-F6′ (FIRST computational gate)**: ∼_OM pairs from (a) g = f + p^{δ+1}h sweeps, (b) order-2 representative perturbations; compare POOLED traces WITH per-history N\* levels and verdicts; mandatory: the worked ℤ₂ order-2 family, wild p = 2, n = 4 | any pooled-structure/verdict/N\*-level mismatch at a ∼_OM pair (level-only mismatch → adjudicate the bounded-shift fallback) |
| N\*/CEIL-UB | ceiling-direction scan | kill-1: realized read on a level-N run with N\*(𝐇) > N (kills F1′ conformance); kill-2: N\* > max-ceilings (kills CEIL-UB); reads-above-ceiling retained as O-1thr regression |
| MF-MATCH | iteration-multiset vs hand-transcribed flow | multiset mismatch |
| OB2 | σ(f) vs σ(g) (PARI) on the F6 pairs | any σ difference |
| K-OB-C | radius scan | read at weight w, no root within w − C_φ |
| OL-2a-4 | emitted-history W-law scan | any W1–W5 / a₀ / only-last-terminal violation |

## 4. DEPENDENCY MAP + the consumer-to-face right-sizing table

Consumes: O-2a Thm 1 + 2(A)–(C) [rev-3 verdict SOUND-WITH-GAPS, gap-class
only]; OL-2a-1/2/3 [open units]; OL-2a-4 [owned here]; O-1thr [proved
per-policy mod (M6b)]; D-14 [pass-1 clean]; O-14a′ [confirmed]; O-13/D-12;
TB-CAP (τ-irr) [perimeter-conditional]; D4R.4/L12 [the N\* source]; GMN; BNS
§2/§4 [transcription duties]. NOT consumed: D-15 (CYL), BNS Thm 3.13, LC-COH.

Right-sizing warrant — each face at its strongest consumer's strength:

| consumer | needs | face form |
|---|---|---|
| K-14 (I0) graft | censuses extend | F2′ + F3′ (grafts extend realized prefixes ⇒ coherent) |
| K-14 (I1) census | counts tie per box | F1′ + F2′ (selected f) |
| K-14 (I3-rc) | frame premise | F5 |
| O-4 OL1-ii | terminate + accept at N(f) | F1′ conformance + F4-C + GMN Cor 4.19 |
| O-5 + D-7a/b/c | accepted ⇒ true datum | F4-S + O-2a saturation; the all-lifts clause via D-15, not F1 |
| O-7 (X1)/(X4) | read ⇒ disk / wildness | F1′ + K-OB-C / K-OB-E |
| D-15 (CYL) | cylinder assembly | D-14 + O-1thr (K2) + F1′/F2′ + (τ-irr) — OWNS lift-uniformity |
| D-16 (δ) | execution transport | F6′ + OB2 + F1′–F5 (pooled filtered suffices) |
| D-11 | σ invariance | OB2 |

No consumer needs: every-lift F1, all-N F4 biconditional, raw-run F6,
lawful-chain F3.

## 5. UNIT DECOMPOSITION (dispatch order REVISED)

**JC-0 FIRST** (statement layer as theorems-of-definitions: Cons^τ (t-i),
T_can truncation laws, ADEQ statement + legs (i)/(iii), N\* + CEIL-UB, lift
typing, the six revised faces + acyclicity re-check) → **JC-N** (gate wave;
G-F6′ first, then G-F3′; the rest ride standing harnesses) → {JC-1 = OL-2a-1,
JC-2 = OL-2a-2 + the verbatim (M6b) corollary, JC-3 = OL-2a-3, JC-11 =
K-OB-C, JC-12 = OB2, parallel} → JC-4 (OL-2a-4 + K-OB-E) → JC-5 (F5) → JC-6
(F1′) → {JC-7 (F2′ + SEM-LAWFUL — hardest), JC-8 (F3′, coherent-keyed)} →
JC-9 (F4-S/F4-C) → JC-13 (K-OB-A/B) → {JC-10a (TT-DET′ — BLOCKED until G-F6′
reports), JC-10b (MF-MATCH)} → JC-10c (F6′) → JC-14 (master assembly). Every
step unit receives the IH as an explicit displayed hypothesis.

## 6. The V16 findings and their repairs (verify each repair answers its finding)

| V16 # | finding | repair in this brief |
|---|---|---|
| 1 (crit) | T_can definition replaces the O-3 target | (ADEQ): lands-in/injectivity PROVED, surjectivity an explicit OPEN leg; recovery of the original target displayed as THROUGH ADEQ |
| 2 (crit) | F6 raw-run bijection not implied by quotient ingredients | F6′ stated at pooled/quotient level only; raw bijection withdrawn |
| 3 (crit) | TT-DET preserves no level filtration | TT-DET′ filtered, N\*-preserving; clause flagged riskiest; G-F6′ tests it first; bounded-shift fallback recorded |
| 4 (crit) | ceiling-max not a semantic level; F1's ≤ N unprovable from O-1thr | N\* (L12 form) primary; CEIL-UB one-directional; F1′ conformance re-warranted as engine mechanics |
| 5 (crit) | every-lift ill-typed + hidden cylinder law | selected-f faces; separable lift typing; cylinder content routed to D-15 |
| 6 (adv+) | acyclicity confirmed | recorded; re-checked against TT-DET′ |
| 7 (crit) | lawful ⇏ coherent; realizer covers coherent only | F3′ coherent-keyed; LC-COH displayed unconsumed; G-F3 kill narrowed |
| 8 (adv) | menu-lawfulness bridge unnamed / misattributed to D-14 | (SEM-LAWFUL) named, owned by JC-7, warrant displayed |
| 9 (adv+) | OB2 level-free; Thm 3.13 no trace content | recorded; BNS Defs 1.7/3.1–3.2 pinned |
| 10 (adv) | load-bearing F6 = filtered pooled + verdicts + blocks | F6′ pitched exactly there |
| 11 (adv) | (M6b) should be an explicit JC-2/3 corollary | verbatim corollary clause in JC-2's spec, JC-3 input recorded |
| 12 (adv) | six over-strength instances | five right-sized; F5 retained with displayed warrant (upstream identity-frame makes the strength free) |
| 13 (adv) | gates don't test stated quantifiers | G-F1′ narrowed + G-LIFT added; G-F4′ all-N sweep; G-CEIL′ direction fixed; G-F6′ extended |
| 14 (adv) | JC-0 not first; U6 not a base | JC-0 first, G-F6′ first gate; base = PROVED O-2a Thm 1 + OL-5; U6 corroboration only |

## 7. Explicit review asks

1. **(ADEQ) sufficiency:** do legs (i)–(iii) + the read-back surjectivity, if
   proved, actually identify T_can(f) with the pinned t_•(f) STRONGLY enough
   that "Run_N = T_can(f)_{≤N}" is the original K-RUN theorem? What about
   terminal/verdict nodes — is leg (iii)'s terminal correspondence enough?
2. **N\* well-definedness:** the L12 per-branch level is defined for branch
   states of realized runs — is its extension to arbitrary 𝐇 ∈ T_can(f)
   (needed for F2′'s quantifier) well-posed without circularity through
   realization?
3. **TT-DET′ level clause:** is on-the-nose N\* preservation plausibly TRUE,
   or should the design adopt the bounded-shift form NOW (what exactly does
   D-16 tolerate)?
4. **F4-C's decision level:** OL1-ii needs a single finite N(f) for the whole
   run; F4-C is per-history. Does N(f) := max over the run's histories of
   N\*(𝐇) (finite by GMN Cor 4.19 + finite branching) close the seam, or is
   there a gap?
5. **SEM-LAWFUL's warrant:** does roster totality + (c1)/(c2) + K-OB-E really
   yield menu-lawfulness of the next SEMANTIC read, or is there residual
   content (e.g. the menu's frame is the engine's, the read's data is GMN's —
   who bridges that, F5 at which index)?
6. Any face still stated stronger than its §4 consumer row — name each
   instance.

END OF BRIEF.
