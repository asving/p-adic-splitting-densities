# O3design — SELF-CONTAINED plan-review brief: the O-3 ⊕ O-2b joint cluster design

**What you are reviewing.** A DESIGN (not a proof) for the hardest remaining
object of a mathematical completion campaign: the joint cluster "realization
faithfulness + trace correspondence" for a p-adic polynomial-factorization
classifier. Your charge: adversarial PLAN review — attack the statement layer
(are the claims well-posed, non-circular, strong enough for their consumers,
no stronger than provable?), the induction architecture, the gate list (does
each falsifier actually test its claim?), and the unit decomposition. Quote
each offending passage; classify *critical defect* (breaks the plan) vs *gap*
(needs a fix, plan survives). Fix nothing. Five explicit asks are at §7.

## 0. Setting (all context you need)

Fix a prime p, O = ℤ_p, residue field F = F_p. For f ∈ O[x] monic separable of
degree n, the Okutsu–Montes (OM) machinery (Guàrdia–Montes–Nart, Trans. AMS 364
(2012) — "GMN") resolves the irreducible factors of f by a tower of Newton
polygons: order-1 polygon of f w.r.t. a key φ₁ (a monic lift of an irreducible
factor ψ₀ of f̄), residual polynomials over growing finite fields
F₁ ⊂ F₂ ⊂ ⋯, higher-order polygons w.r.t. recursively built keys. A "type" is
the discrete datum (φ₁; λ₁, ψ₁; …; λ_r, ψ_r) (slopes λ_i = −h_i/e_i, residual
irreducibles ψ_i); the type tree t_•(f) (GMN Def 3.10) branches over slopes
and residual factors; a type with residual multiplicity 1 certifies an
irreducible factor with e = e₁⋯e_r, f = f₀⋯f_r (GMN Cor 3.8).

The project has a combinatorial ENGINE (a digit-reading classifier on residue
classes x ∈ (O/p^N)^n) intended to realize this semantics uniformly in p. A
previously accepted upstream unit ("O-2a") built the dictionary between engine
histories and GMN types:

* **The carrier.** 𝔈 = dressed histories 𝐇 = (ρ₀; ν₁,…,ν_k): ρ₀ = (ψ̂₀, a₀)
  with ψ̂₀ ∈ F[y] monic irreducible, a₀ = ord_{ψ̂₀}(f̄); nodes
  ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i) recording one polygon-side
  read (slope −h_i/e_i, residual degree ℓ_i, initial point (s_i, u_i)),
  dressed with the selected residual irreducible ψ̂_i ∈ F_i[z] of degree g_i
  and multiplicity μ_i. Well-formedness laws W1–W5 (row typing; the increment
  law inc = 1 ⇔ e·g ≥ 2; interior μ ≥ 2; ψ̂ monic irreducible ≠ z; only the
  last node may be terminal). Equality is literal componentwise equality; the
  fields F_i are explicit iterated quotients, not isomorphism classes.
* **Θ and Cons_f.** Θ maps 𝐇 to its formal type-chain datum (total,
  truncation-compatible); a pinned representative family F_rep (one canonical
  key lift per chain, a function of the discrete data) makes GMN's objects
  single-valued. Cons_f(𝐇) ("GMN-consistency") is defined INTRINSICALLY: a₀
  matches, each level's (e_i, h_i, ℓ_i) and (s_i, u_i) are the data of a side
  of the order-i polygon N_i^−(f) in the order-i GMN integer frame, and
  ord_{ψ̂_i}(R_{λ_i}(f)) = μ_i. NO realization semantics: Cons_f never
  mentions the classifier. O-2a proved (order ≤ 1 outright; all orders modulo
  four named seam lemmas): Cons_f histories land in the type tree, invariants
  match (accE = ∏e_i, accF = f₀∏g_i; saturation accE·accF = deg ⇔ μ = 1),
  each certified node charges the GMN index ind(f) by ≥ 1, and Θ is injective
  on all-continuing Cons_f histories (Lemma R). Its four OPEN seam lemmas:
  **OL-2a-1** (the pinned lift is a genuine GMN representative), **OL-2a-2**
  (the engine's stage-frame polygon of f = N_{i+1}(f) identically — identity
  frame, with positional transport of (s, u); clauses (a)–(d)), **OL-2a-3**
  (the engine's anchor-normalized residual = GMN's twisted residual up to a
  nonzero constant), **OL-2a-4** (the engine EMITS well-formed dressed
  histories with a₀ = ord(f̄)).
* **Adjacent verified inputs** (statuses in §4): a per-site read-locality
  package ("O-1thr": every history-site has a computable ceiling L(H, ν) such
  that whether the run reads the site depends only on digits below L; proved
  per-policy modulo ONE interface assumption (M6b) = depth-≥2 vertex-read
  transport); a lawful-site strengthening ("D-14": the same for sites merely
  menu-lawful at the frame state, not presupposed realized); a realizer-
  existence supply ("O-14a′": at ambient residue field ZMod p, every coherent
  history has a center realizer — proved, incl. the terminal-node flank); a
  skeleton-finiteness theorem ("O-13/D-12": collapsed tree shapes form a
  finite p-free set); an exhaustive numeric probe ("U6": at depth ≤ 2, all
  (n, p) ∈ {2,3}², the realized run set = the semantic truncation EXACTLY —
  174/174 strata, zero phantoms, equal fibers exact).

**The cluster to design.** O-3 (K-RUN): the realized run set at level N is
EXACTLY the level-N truncation of the semantic tree — four clauses
(no-phantom, no-missing, nonempty locus, acceptance) + auxiliary obligations
K-OB-A/B/C/E. O-2b: **K-DICT-OB1** (equal admissible OM factorizations ⇒ the
classifier's refinement traces correspond, recentering-population nodes
matched to same-degree iterations of the published Montes flow) + **K-DICT-OB2**
(the splitting type σ is invariant under the published OM-factorization/
Okutsu-equivalence relation). A prior review (V5) found these two mutually
dependent: no-phantom needs engine-reads → GMN-data; OB1 quantifies over "the
trees the classifier produces" (O-3's subject). The adjudicated resolution:
ONE well-founded induction on resolution level, package bundling both faces.

## 1. New definitions the design introduces

* **(O2) Cons_f^τ** — terminal-extended consistency: Cons_f on the continuing
  prefix, plus the terminal record forced by the prefix: (τ-irr case)
  μ_last = 1 and the verdict pair = (accE, accF); (τ-hen case) the node sits
  on the slope-−∞/Hensel side with verdict (1, f₀). Consistency ("the
  terminal record is forced, no free choice") is a stated lemma (unit JC-0).
* **(O3) T_can(f) := {𝐇 ∈ 𝔈 : Cons_f^τ(𝐇)}**, prefix-ordered. The semantic
  tree is DEFINED as the consistency set — intrinsically GMN-defined, no
  classifier in the definition.
* **(O4) Run_N(x)** — the τ-pruned dressed histories the classifier (at the
  pinned canonical policy; realizer supply from O-14a′ at ZMod p, which covers
  the intended instance F = 𝔽_p) emits on box x at working level N. That
  Run_N(x) ⊂ 𝔈 at all is OL-2a-4's content — displayed conditionality.
* **(O5) N(𝐇)** — resolution level: max over sites along 𝐇 of the O-1thr
  ceiling L(H_i, ν_i), joined with the terminal verdict window. Induction
  measure: (N, k) ∈ ℕ² lexicographic (k = history length).
* **(O6) Fresh-frame-lawful chains** — formal assignment chains whose per-step
  reads are menu-lawful at the frame state, with two BINDING canonicalizations
  validated by the U6 probe: (i) branch species = the WHOLE node read (keying
  by a branch's own side letters pools unequal digit-pinning counts and
  spuriously falsifies fiber laws); (ii) beyond-cap content pooled as a single
  ('deep', k) marker.
* **(O7) f ∼_OM g** — f and g admit a common OM factorization in the published
  sense (Bauch–Nart–Stainsby, LMS JCM 16 (2013), §2/§3; transcription duty
  flagged). The BNS congruence theorem (Thm 3.13: f ≡ g mod p^{δ+1} ⇒ ∼_OM)
  is deliberately NOT consumed by the cluster — only by the downstream
  δ-transport node D-16.

## 2. THE STATEMENT LAYER — package IND(N) (six faces) + one satellite

For every ns-free monic separable f of degree n, x := f mod p^N:

* **F1_N (no-phantom).** Every 𝐇 ∈ Run_N(x) has N(𝐇) ≤ N, and Cons_g^τ(𝐇)
  for EVERY monic lift g of x.
* **F2_N (no-missing).** Every 𝐇 ∈ T_can(f) with N(𝐇) ≤ N lies in Run_N(x).
* **F3_N (nonempty locus).** Every fresh-frame-lawful chain (per (O6)) with
  resolution ≤ N has a monic separable witness g in its level-N digit
  cylinder, with the corresponding history in T_can(g).
* **F4_N (acceptance).** The built certification predicate accepts (x, 𝐇) iff
  𝐇 ∈ Run_N(x) AND 𝐇 is verdict-carrying in T_can(g) for every lift g.
* **F5_N (state coherence — the single-run half of OB1).** For 𝐇 ∈ Run_N(x),
  the engine's frame state after 𝐇 (stage key, frame valuation, digit
  algebra/tower, position) equals the GMN state data of its chain under the
  pinned interpretation — key = the pinned lift, valuation u = v_{k+1}
  identically, tower = F_{k+1} on the nose.
* **F6_N (trace correspondence = OB1 at level N).** For f ∼_OM g: a bijection
  Run_N(x_f) ≅ Run_N(x_g) preserving dressed node data up to the explicit
  representative-equivalence ≈ of TT-DET (below), matching maximal
  recentering-population runs one-to-one with same-degree refinement
  iterations of the published Montes flow. (Raw node counts CANNOT correspond
  — the caterpillar family f_m = (x−a)(x−b), v_p(a−b) = m+1 forces unboundedly
  many recenterings — so the pooling is forced, mirroring the proved
  skeleton-compression theorem.)

**OB2 (satellite, level-free).** f ∼_OM g ⇒ σ(f) = σ(g). Route: each factor's
(e, f) = (accE, accF) are functions of the type's discrete data (O-2a clause
(i)), and Okutsu equivalence preserves them (BNS §2 transcription); σ is the
multiset of (e, f). Not inductive.

**Named auxiliary lemmas (the genuinely new mathematics):**

* **TT-DET** (deep-wild-hard; OB1's core): f ∼_OM g ⇒ T_can(f)/≈ ≅ T_can(g)/≈
  as dressed trees, where ≈ is the explicit equivalence generated by
  Okutsu-equivalent representative re-choices; preserves (e_i, h_i, g_i, μ_i)
  and collapsed recentering runs. (The pinned family F_rep pins ONE
  representative per chain, so ≈ acts BETWEEN the two trees.)
* **MF-MATCH**: within one run, maximal recentering runs ↔ same-degree
  refinement iterations of the published Montes flow (citation pull before
  dispatch). Needed so BNS iteration/precision bounds are consumable by D-16.
* **K-OB-C** (Okutsu proximity): Cons_f(𝐇) ⇒ the tracked cluster's roots lie
  in an explicit disk of radius w − C_φ. GMN-side; citation pull first.
  Consumed by the weight-charge leaf (X1); NOT load-bearing for F1.
* **K-OB-E**: continuing nodes of T_can(f) have μ ≥ 2 (GMN Def 3.9
  non-completeness arithmetic; near-definitional).
* **K-OB-A** (finite-site assembly: fibers agree below the max of finitely
  many ceilings) and **K-OB-B** (stratum membership ⇒ realized): corollaries
  of O-1thr + F2 + finiteness; priced as one unit.

**Intra-step order (acyclicity).** At (N, k): F5 ← IH + OL-2a-1/2/3/4;
F1 ← F5 + OL-2a-2(c,d)/3 + Cons^τ + O-1thr Thm 1; F2 ← IH(F1/F5 on the strict
prefix) + D-14 (the next semantic read is MENU-LAWFUL — the lawful-site
quantifier, which is exactly why D-14 was forced upstream as its own node) +
roster totality + K-OB-E; F3 ← O-14a′ + D-14 (no F2 use); F4 ← F1 + F2 +
O-1thr + the (τ-irr) window (inherited perimeter-conditionality, displayed);
F6 ← F1 + F2 + F5 (the classifier quantifier in OB1 is ELIMINATED: both
traces ARE their Cons^τ sets) + TT-DET + MF-MATCH. No face consumes a later
face. Base: O-2a Theorem 1 (order ≤ 1, proved) + compiled length-≤1 instances;
the U6 exhaustive depth-2 survival sits directly above the base.

**Displayed inherited conditionality:** (M6b) until OL-2a-2/3 discharge it
(expected — one proof, two consumers); the (τ-irr) verdict-pin perimeter;
OL-2a-1..3 until their units land. The O-14a′ residue at deg Φ > 1 does NOT
bind at the intended instance (prime-field collapse); it re-enters only at the
unramified-base re-scope (node D-3), flagged there.

## 3. GATE LIST (falsifier per claim; countermodel-first)

| claim | gate | one-shot kill criterion |
|---|---|---|
| F1 | U6 phantom scan extended to depth 3 | any realized dressed history failing Cons^τ vs independently computed GMN data |
| F2 | U6 counting tie T = T̂ at depth 3, (n,p) ∈ {2,3}² | any stratum T < T̂ (T > T̂ kills F1); 174/174 exact at depth 2 |
| F2 terminal | the LIVE landing-flank countermodel search | any hit (predicted empty + unrecordable by the proved last-node closure) |
| F3 | stratum census at depth 3: enumerate lawful chains (whole-node species, deep pooling), predict counts, exhaustive box scan | any predicted-nonempty EMPTY stratum (precedent: an earlier draft predicted 62,500 members of an empty stratum) |
| F4 | acceptance regression: simulated certification vs PARI factorpadic on exhaustive decided boxes n ≤ 4, p ≤ 5 | accepted-but-wrong or semantic-decided-but-unaccepted at N(f) |
| F5 | state-transport probe at depth 3 (engine frame vs independent v_r/F_r) | any frame/tower/position mismatch |
| F6/TT-DET | **RUN FIRST**: cross-polynomial trace gate — pairs from (a) g = f + p^{δ+1}h sweeps, (b) order-2 representative perturbations; compare pooled traces; mandatory families: the worked ℤ₂ order-2 family with the T1-recentering exclusion; wild p = 2, n = 4 | ANY pooled-trace mismatch at a ∼_OM pair (would force a weaker correspondence — must be learned before proving) |
| MF-MATCH | same pairs, iteration-multiset vs hand-transcribed Montes flow | multiset mismatch |
| OB2 | σ(f) vs σ(g) on the same pairs (PARI) | any σ difference |
| K-OB-C | radius scan on realized reads | any read at weight w with no root within w − C_φ |
| OL-2a-4 | emitted-history W-law scan (extends the U6 fidelity header) | any emitted history violating W1–W5 / a₀ / only-last-terminal |
| N(𝐇) | ceiling-conformance scan at depth 3 | any realized read above the claimed ceiling |

Two NEW investments (F6 gate, F3 census); the rest extend standing harnesses.
Any gate keyed by side letters instead of whole-node species is void (U6).

## 4. DEPENDENCY MAP (statuses at design time)

Consumes: O-2a Thm 1 + Thm 2(A)–(C) [proved-unverified; hostile-pass core
confirmed]; OL-2a-1/2/3 [open; upstream units of this wave]; OL-2a-4 [open;
owned by the cluster]; O-1thr Thms 1/2 [proved-unverified per-policy, 2(b)/3
modulo (M6b)]; D-14 [pass-1 clean, r2 in flight]; O-14a′ [prime-field collapse
+ last-node closure verifier-confirmed]; O-13/D-12 [verified / in
verification]; TB-CAP (τ-irr) [dual-accepted, perimeter-conditional]; GMN
[literature-conditional]; BNS §2/§4 [literature-candidate; transcription
duties]. NOT consumed: D-15 (CYL — supplied-to, downstream); BNS Thm 3.13
(D-16 only). Supplies: the count-tie and verdict-soundness row repairs;
MarkGraft duties (I0)/(I1)/(I3-rc); drainage's agreement seam OL1-ii (= F4);
halt/assembly's inputs; weight-charge (X1)/(X4); D-15; D-16; the mass-id node.

## 5. UNIT DECOMPOSITION (16 units, ~1 brief each; dispatch order)

JC-N (the gate wave — FIRST) → JC-0 (Cons^τ + T_can laws + N(𝐇) + package
statement) → {JC-1 = OL-2a-1, JC-2 = OL-2a-2(a–d), JC-3 = OL-2a-3 (shared
with the order-r census leaf), JC-11 = K-OB-C, JC-12 = OB2, in parallel} →
JC-4 (OL-2a-4 + K-OB-E) → JC-5 (F5 step) → JC-6 (F1 step) → {JC-7 (F2 step —
hardest), JC-8 (F3)} → JC-9 (F4) → JC-13 (K-OB-A/B) → {JC-10a (TT-DET),
JC-10b (MF-MATCH)} → JC-10c (F6 assembly) → JC-14 (master well-founded
assembly). Every step unit receives the IH as an explicit displayed
hypothesis; no unit re-proves another face.

## 6. How the design answers the three prior architectural defects (V5)

(1) "Dictionary lacks a coherent carrier/equality design" — answered by
REUSING the O-2a rev-2 carrier verbatim; the Okutsu quotient enters only as
TT-DET's explicit ≈; OB1's classifier quantifier is eliminated via F1/F2.
(2) "The cylinder law (CYL) is not implied by the listed faces" — the design
neither claims nor consumes CYL; it supplies D-14-consumption, F1/F2, and the
displayed (τ-irr) conditionality, and CYL assembles downstream as its own
node. (3) "The δ-congruence tier lacks execution transport" — F6 is stated as
RUN correspondence precisely so the downstream node D-16 = published Thm 3.13
+ OB1/OB2 + F1–F5 composes with no new mechanism; nothing δ-related is
claimed here.

## 7. Explicit review asks

1. Induction measure: is (O5)'s max-of-per-site-ceilings (+ verdict window)
   sound as the primary measure, or must the project's earlier per-branch
   resolution level be primary? What breaks if they disagree on a family?
2. F6's strength: is correspondence-up-to-≈-with-run-pooling the weakest form
   that still serves the δ-transport consumer? Is there a cheaper true
   statement (collapsed skeletons + per-node invariants only)?
3. Does OB2 genuinely evade the induction, or does the published
   OM-factorization relation quantify over traces in a way that pulls OB2
   into F6?
4. Should JC-2/3 state the O-1thr vertex-transport assumption (M6b) verbatim
   as a corollary (one verifier pass, two consumers), or is that scope creep?
5. Quantifier audit: F2 consumes D-14 (lawful-site locality). Is the
   orientation clean — D-14 stated with no realization premise, F2 using it
   only to determine menu-lawfulness of the NEXT semantic read — or does any
   hidden realized-site restriction re-enter the circle the decomposition was
   built to break?
6. Anything in §2 stated STRONGER than its consumers need (over-claiming is
   how the last two rounds' criticals arose) — name each instance.

END OF BRIEF.
