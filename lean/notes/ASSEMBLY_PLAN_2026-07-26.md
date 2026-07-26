# ASSEMBLY_PLAN_2026-07-26 — the final campaign: from accepted §C to the complete wild-uniformity theorem (REV 4)

*Plan architect: Fable, 2026-07-26. REV 2, same day: rebuilt against the pass-1
structural review (ASSEMBLY_PLAN_PASS1_2026-07-26.md — 8 critical obstructions,
7 concerns, verdict UNSOUND); the finding→repair table is the REV 2 record near the end
of this file. REV 3, same day: revised against the pass-2 review
(ASSEMBLY_PLAN_PASS2_2026-07-26.md — 7 criticals, 8 concerns, verdict UNSOUND) and
BOTH wall probes' reports (value_probe: NO-WALL exploration-class, anchor-twist caveat;
state_probe: probe-level NO-WALL, vtx-rigidity feasibility finding — gate reopened).
REV 4, same day: rebuilt against the pass-3 review (ASSEMBLY_PLAN_PASS3_2026-07-26.md —
7 criticals, 6 concerns, verdict UNSOUND) around its four demanded structural builds:
(B1) the JOINT-REFINED STATE JREF/τ built ONCE in [1v]/[2b] and consumed by
MENU/RESUM/SQUEEZE; (B2) the LOC/HIST/FAM three-object separation (§1s) with displayed
maps; (B3) the ESCAPE kernel replacing the refuted WEIGHT-CHARGE→B(n)-leak route; (B4)
the truncated aggregate-census protocol replacing the unjustified σ-aggregate (†). The
REV 4 record is the final table. Directive (Asvin, 2026-07-26): iterate on the math with
Codex until either a COMPLETE math proof of wild uniformity exists or the approach is shown
conclusively to not work. This plan is the architecture for everything between the accepted
§C (MOVES_2026-07-24.md, passes 12+13 CLEAN) and the endpoint theorem.*

## 0. The endpoint and the certified inputs

**THEOREM U (the target).** For each degree n and factorization type σ (a multiset of
(e, f) pairs with Σ e·f = n), there is ONE rational function R_σ ∈ ℚ(q) such that for
EVERY prime p — wild p ≤ n included — the density of monic degree-n f ∈ ℤ_p[x] with
type σ equals R_σ(p); and Σ_σ R_σ = 1 identically in q.

**Certified perimeter this plan consumes (nothing else is assumed):**
- **§C / Theorem C** (MOVES ledger, ACCEPTED): for every REALIZABLE lift-carrying history
  H = (ν₀,…,ν_k) and admissible terminal system Z, at every N ≥ N(H, Z):
  #{f mod p^N ∈ S(H, Z)} = p^{nN} · ∏ᵢ vol(E_fresh(νᵢ)) · vol(Z), with Ψ_H a mass-exact
  bijection onto the image locus. Each vol(E_fresh(νᵢ)) = product of per-digit factors
  (alphabet cardinality)⁻¹, a power of p determined by the history's SHAPE data (C.3).
  SCOPE NOTES consumed at REV 2: C.0's LIFT-TRANSLATION remark equates masses of
  TRANSPORTED pairs only — no fixed-downstream correspondence is claimed; and §C names
  a CANONICAL lift choice (the (S6b) offset-P-lift realizer), on which [1] D4-R builds.
- **§B2-DEF** (ACCEPTED): the per-move ledger D.11 at all tower stages (the order-r
  induction TRANS), increments at any (e, h, g, μ, a), recenterings at e_read = 1,
  lift-independence D.10, realizability (NA)/(HV).
- **§A, §B1 (surviving parts), JOINT-D1**; eleven sealed census gates (Cases E…L).
- **The decomposition note** (`MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md`, ACCEPTED):
  Lemma 3.2 (depth ⟹ ind ⟹ v_p(disc); GMN pins (P1)–(P3)), Lemma 3.3 (discriminant
  tail (3b), elementary), Cor 3.4 (Desc_d envelope (3c)), Thm 2.1 (N-stability),
  Lemma 3.1/3.4′ scaffolding, the OPEN-D4 statement (3i) + its (R1)/(R2) reduction
  shape, §4 (the conditional resummation blueprint 4.1–4.5), L3/Claim 4.3
  (per-shape counts are universal polynomials in the pool size Q).
- **L5fix** (`L5fix_complete.md`, accepted long since): termination invariants; the
  cluster-tree shape menu 𝒯_n is finite and p-independent (Serre different bound).
- **The n=2 precedent** (W5/W6/W6q, machine-checked): chain menus → geometric series
  (`msW_eighth_le` fixpoint) → two-sided squeeze (U) → `montes_uniform_n2` with fixed
  (num, den) per type. This is the pattern each note below generalizes.

## 1. The DAG of the remaining notes (REV 3 — eight notes, ACYCLIC)

Arrows = "consumes the accepted statement of". REV 3 (pass-2 obstruction 3): the rev-2
graph was CYCLIC — [1v] VALUE quantified over MENU's shape list while MENU's M2/M4b
consumed [1v]'s strata, and EXHAUST's X.2 silently consumed MENU. Repair: [2] MENU is
SPLIT into [2a] SPECIES (the raw catalogue, no strata — feeds [1v]) and [2b] STATE-GEOM
(types + cone geometry — consumes [1v]); the [2]→[5] edge is now explicit.

```
§C ─► [1] D4-R ─► [2a] SPECIES ─► [1v] VALUE ─► [2b] STATE-GEOM ─► [2r] REL
                        │                              │               │
      decomp §3 ─► [5] EXHAUST ◄───(X.2 ← M4a tails)───┤               │
                        │   (X.1a/X.1b draftable       │               │
                        │    right after [2a])         │               │
                        ▼                              ▼               ▼
                   [3] RESUM ◄─────────────────────────┴───────────────┤
                        │                                              │
                        ▼                                              │
                   [4] SQUEEZE ◄───────────────────────────────────────┘
                        │
                        ▼
                    THEOREM U  (assembly capstone paragraph inside [4])
```

Full edge list (ACYCLIC; every rev-2 edge preserved or corrected): §C → [1], [2a],
[2r] · decomp §3 → [5] · [1] → [2a] (canonical policy) · [2a] → [1v] (the local
species Theorem VAL quantifies over — §1s), [2b], [5] (X.1a's species dictionary) ·
[1v] → [2b] (the JREF cells in M2's τ — REV 4; VAL.2J in M4b), [3] (RS.2) · [2b] →
[2r] (stratification
vocabulary), [5] (X.2's envelope constants ← M4a tails — the edge pass-2 found
missing), [3] · [2r] → [3], [4] · [5] → [3], [4] · [3] → [4].

- **[1] D4-R** — *the per-shape-prefix mass law* on the CANONICAL-POLICY history
  (strata are fibers, no quotient); the pool BOUND (3i) survives verbatim. (§2)
- **[2a] SPECIES** — *the raw shape catalogue*: M1's corrected degree bounds + M5
  completeness; NO strata, NO state types — exactly the finite list [1v] needs to
  quantify over, so no cycle. (§3)
- **[1v] VALUE** — *the linked value-count structure*: VAL.1 with the CORRECTED
  three-cell example, VAL.2J on the DEFINED joint refinement JREF (REV 4 — no longer
  "or an explicit common refinement"), the (†) census epistemics restricted to
  integer-count objects (§1s classes LOC/HIST); risk R1's decision point. PROBE
  REPORTED (2026-07-26): NO-WALL, exploration-class, anchor-twist caveat adopted. (§2v)
- **[2b] STATE-GEOM** — M2 STATE = the JOINT-REFINED type τ (JREF-valued — REV 4;
  a LUMPABILITY theorem, not label closure), M4a cone geometry + M4a-X EXACT-DOMAIN
  (REV 4 kernel), M4b per-point counts + M4b-T translation/equivariance; supplies 𝒯_n
  to [3]. ACCEPTANCE BLOCKED on STATE-probe-2 (REV 4, pass-3 obstruction 7). (§3)
- **[2r] REL** — *the relative ledger*: Theorem C over unramified O = W(F_{p^δ}) +
  the four-obligation sub-cluster base change — what β_m(q^δ) MEANS. (§3r)
- **[5] EXHAUST** — *the discriminant-tail tie-in*, two-track: X.1a genuine-event
  dictionary (per-species GMN index table) + X.1b STALL (an OPEN kernel at REV 3:
  WEIGHT-CHARGE + its own STALL-probe) + X.2 PROGRESS. (§5)
- **[3] RESUM** — *the depth resummation*: block system over (cluster size e, state
  type τ); RS.PRE defines the NORMALIZED kernel K_e (substochastic GIVEN three named
  inputs — REV 4, no longer "by construction" tout court); RS.0 TYPE-CLOSURE
  (lumpability + height-shift bisimulation); solvability via the ESCAPE kernel
  (REV 4 — the WEIGHT-CHARGE→B(n) route is STRUCK); p-uniformity from [1v].
  ACCEPTANCE BLOCKED on STATE-probe-2 (§4).
- **[4] SQUEEZE** — *the two-sided finite-level bound*: decided_σ(N) ≤ R_σ(p)·p^{nN}
  and ≥ (R_σ(p) − env(N))·p^{nN}, hence ρ_σ = R_σ(p) — Theorem U; the domination
  induction over (e, τ) blocks with base-changed hypotheses from [2r]. (§6)

**Execution order:** [1] → [2a] → [1v] → [2b] → { [2r] ∥ [5] } → [3] → [4], with
X.1a/X.1b draftable right after [2a]. DRAFT CLEARANCE (REV 4, pass-3 closing): [1]
D4-R is cleared to draft FIRST — its partition argument and pool inequality do not
depend on the unresolved RESUM architecture; its draft must distinguish complete
histories from prefixes (§2) and prove all three D4R.0 obligations. Both wall probes
have ALREADY reported (exploration-class, 2026-07-26; verification/results/): the
VALUE probe (R1) NO-WALL with the anchor-twist caveat; the STATE probe (R2)
probe-level NO-WALL with the vtx-rigidity feasibility finding — its sealed gate is
REOPENED as STATE-probe-2 (§4), which must PASS before [2b] OR [3] is accepted
(REV 4, pass-3 obstruction 7: it tests M2(ii), a theorem of [2b]). The sealed gates
still run (Case-K discipline): probes are unsealed exploration, never acceptance
evidence.

**Format per note (sections 2–6 below):** key definitions · load-bearing lemmas with
proof sketches · kernels (fresh-context derivation-grade, C10B/C15-style) · the sealed
gate that must PASS before the note may be trusted (§7 protocol). GATE DESIGN RULE
(REV 2, pass-1 obstruction 8): wherever the gated claim is exact, the gate is exact —
exhaustive finite-level enumeration or exact F_q counts; sampling survives only in
labeled consistency layers. And n = 3 alone is NOT enough: a cubic's deg-2 key cannot
carry μ ≥ 2, so the value-kernel gates run at n = 5 and directly over F_q.

## 1s. The three counting objects — LOC / HIST / FAM (NEW at REV 4; pass-3 obstruction 4: "(†), M4b, and RS.2 refer to different objects under the same C_S notation")

One separation, built once, binding on every note. Three distinct objects, two maps:

- **LOC (local move species) m ∈ ℳ_n.** ONE node/move with its linked data: species,
  (e, h, g, μ, a) bounds, residual shape, the JREF stratum vocabulary (§2v). Finite
  p-independent list, extracted from [2a]'s shapes. Each m has a FIXED pool dimension
  W_loc(m). Its count C_m(q) is an integer at every prime power. **Theorem VAL and the
  (†) rule apply HERE**, per species, at degree bound W_loc(m).
- **HIST (unrolled finite histories) H.** A shape PLUS a full ℕ-parameter tuple
  (heights, depths/loop counts k). `unroll`: a JREF-chained sequence of LOC moves ↦ H.
  Its count C_H(q) = the VAL.2J-iterated product of local counts along the chain —
  polynomial of degree ≤ W(H) := Σ_moves W_loc, which GROWS with the loop parameters
  (k loop reads = k fresh pools; pass-3's point). (†) applies to each FINITE H, or to
  any FINITE explicitly-listed family with a displayed common monomial normalization,
  at ITS OWN displayed degree bound — never to a completed sum.
- **FAM (resummed families) β, K_e-entries, R_σ.** `resum`: a per-(shape, type)
  cone-lattice sum of HIST masses ↦ an element of ℚ(q) with geometric denominators
  (1 − q^{−a}). NOT integer-valued, NOT degree-bounded, NOT subject to (†). Tested
  only via the truncated-census protocol (§2v (†-AGG)) or the two-sided SQUEEZE
  brackets — never by interpolation.

**Notation rule (binding):** C_m = LOC counts; C_H (and C_{S,τ} at a fixed lattice
point) = HIST counts; β/K/R = FAM. Any statement using "C_S" must say which class it
means. (†) claims outside LOC/HIST are void. RS.2's matrix entries are FAM objects
assembled from LOC counts × M4a-X-exact geometric sums; M4b's per-point counts are
HIST-at-a-point; the raw catalogue [2a] indexes shapes, and assigns NO count.

## 2. NOTE [1] D4-R — the per-shape-prefix mass law (REV 3: canonical policy, Z = ⊤, three-obligation kernel)

**What D4 was.** Decomposition note (3i): for class-3 read-prefixes P,
μ(P) ≤ p^{−A_net(P)}, A_net(P) := A(P) − W(P), with A(P) the ledger exponent and
W(P) = Σ_r w_r·d_r the pool dimension — UNIFORMLY in p. Its reduction (R1)/(R2) ran
through joint-D1's conditional-on-ancestors clause. §C now supplies that clause in
proved form: C.1.5(1) — mass(Σ_i ∩ stratum(ν_{i+1})) = mass(Σ_i)·vol_nom(E_fresh(ν_{i+1}))
— IS the chain rule (R2) needed, and Theorem C(b) with Z = ⊤ is its closed composition.
NOTATION (REV 3, pass-2 concern 2): Z = ⊤ denotes the TAUTOLOGICAL terminal system —
no constraint, vol(⊤) = 1 — NOT the empty locus (which has volume 0); every rev-2
"Z = ∅" in this note meant and now reads ⊤.

**Key definitions (REV 2 — the transport quotient is RETIRED; pass-1 obstruction 2:
lift-translation gives equal mass for TRANSPORTED pairs, never a license to discard
all but one representative while computing the mass of a union).**
- CANONICAL-POLICY HISTORY: the classifier run with the (S6b) offset-P-lift realizer at
  every recentering (already the named canonical choice in §C C.0) is a deterministic
  TOTAL map f ↦ H_can(f) on terminating f. Hist(P̂) := { canonical-lift realizable
  histories H with shape P̂ } — a literal SET of histories, NO quotient. Lift-transport
  is demoted to a symmetry remark (MENU M3); nothing counts through it.
- SHAPE-PREFIX P̂: a history prefix with node VALUES forgotten — species, (e, h, g, μ, a),
  strides, residue degrees w_r retained; the side-digit tuples (d_j) and lifts forgotten.
- C_P̂(p) := #Hist(P̂) — a COUNT; realizability = (NA)/(HV) per node. NO uniformity or
  polynomial structure in q is claimed in this note (that is [1v]'s burden).

**Load-bearing lemmas.**
- **D4R.0 (PARTITION — promoted kernel; pass-1 concern 3).** On every state cylinder
  Σ_i of a canonical prefix, the strata of the possible next nodes ν_{i+1} PARTITION
  Σ_i: the frame-(i+1) development's polygon and side patterns are FUNCTIONS of f, so
  distinct node data have disjoint strata and every f realizes exactly one outcome (or
  terminates); consequently — WITH THE PREFIX/COMPLETE DISTINCTION DISPLAYED (REV 4,
  pass-3 concern 1) — for a COMPLETE history H, S(H, ⊤) = {f : H_can(f) = H} (a fiber);
  for a PREFIX P, S(P, ⊤) = {f : P ⪯ H_can(f)} (a prefix-fiber — the union of the
  fibers of all completions). Theorem C(b) with Z = ⊤ is applied to the PREFIX event;
  terminal exhaustiveness (obligation (b) below) is stated for completions of a prefix,
  never conflating the two. Strata are fibers of a map, and disjointness is automatic.
  *Derivation obligations (REV 3, pass-2 concern 1 —
  the three named burdens this kernel carries):* (a) TOTALITY: the (S6b) canonical
  choice is defined at EVERY eligible recentering (no node where the policy is
  partial); (b) TERMINAL EXHAUSTIVENESS: the outcome case analysis covers every f in
  the cylinder — every f produces SOME next-node stratum or a terminal verdict, none
  omitted; (c) COMMON FRAME: two histories sharing a prefix are compared in the COMMON
  frame Ψ_prefix (same prefix + same canonical lifts ⟹ IDENTICAL frame before the
  next read — to be PROVED, not assumed), where the two node-(i+1) patterns read
  different digit values of the same development — never across transported
  coordinates (Theorem C alone does NOT supply this; it is a new lemma).
- **D4R.1 (exact prefix mass).** μ(P̂) = Σ_{H ∈ Hist(P̂)} ∏ᵢ vol(E_fresh(νᵢ))
  = C_P̂(p)·p^{−A(P̂)}. *Sketch:* disjointness + exhaustion of the prefix event by
  D4R.0 (fibers of H_can); each mass is Theorem C(b) with Z = ⊤; vol(E_fresh) depends
  only on shape (C.3), so the sum factors as (count) × (common p-power).
- **D4R.2 (pool bound, p-uniform — SURVIVES verbatim).** C_P̂(p) ≤ p^{W(P̂)}: each
  read's value choices live in ≤ d_r digit functionals over a pool of size Q_r = p^{w_r};
  (NA)/(HV) only shrink the count. Hence (3i) verbatim: μ(P̂) ≤ p^{−A_net(P̂)}. [An
  INEQUALITY — untouched by the death of value-fiber uniformity.]
- **D4R.3 — RETIRED (pass-1 obstruction 1).** The rev-1 torus lemma is FALSE for
  extension-valued vertices: the torus is only Fˣ, with orbits of size ≤ q−1 on
  F_{q^g}ˣ (g > 1), and z ↦ uz transports ψ rather than acting on a fixed-ψ fiber.
  Counterexample on record (the review's): R_anch = z^a·ψ(z)^μ·(Az+B), ψ irreducible
  quadratic, A, B ∈ F_qˣ, μ ≥ 2 — vtx-fiber counts are 1 (target α+1: A = B = 1) vs 0
  (target α: needs B = 0, prohibited by the nonzero-endpoint convention). The lemma is
  STRUCK; every downstream use re-routes to NOTE [1v]. Nothing in THIS note needs it
  (D4R.1 counts, D4R.2 bounds).
- **D4R.4 (N-stability).** μ(P̂) is computed at any N ≥ max_H N(H, ⊤): Hist(P̂) is
  finite WITHOUT any quotient (pass-1 concern 4 repaired) — value assignments range
  over finite alphabets, the canonical lift is a function of node data, the fixed shape
  bounds all heights hence all constrained levels hence each N(H, ⊤), and the max over
  a finite set is finite. [Thm 2.1 re-derived from Theorem C's N(H, Z) clause.]

**Kernels (derivation-grade):** D4R.0 (the partition/fiber argument at common frames;
the totality half needs the read-outcome case analysis to be exhaustive — every f in
the cylinder produces SOME polygon side or terminal verdict).

**Sealed gate D4-n3 (aggregated prefix mass — SCOPE RECORDED).** n = 3, class-3
prefix: root read with residual shape (irreducible quadratic)·(linear) → deg-2 key
φ lifting the quadratic → one depth-1 descend at the deg-2 key (side data fixed, μ = 1).
Seal BEFORE running: C_P̂(p) by direct enumeration of realizable value assignments,
A(P̂), the predicted #{f mod p^N ∈ P̂} = C_P̂(p)·p^{3N−A} at p = 2 AND p = 3, two
levels N each, verified on EXHAUSTIVE level-N boxes (feasible through 2^24 and 3^15);
plus the net bound check; plus a PARTITION check — every box member lands in exactly
one next-node stratum, 0 double-counts and 0 orphans tolerated. RECORDED LIMITATION
(pass-1 obstruction 8): μ = 1 only — this gate exercises D4R.0/1/2 and does NOT touch
the value-count risk; the μ ≥ 2 / a > 0 danger is gated in [1v] at n = 5 and over F_q.

## 2v. NOTE [1v] VALUE — the linked value-count structure (REV 4: JREF defined, Theorem VAL split LOCAL/CHAIN, (†) scoped + (†-AGG); R1's decision point — PROBE REPORTED NO-WALL)

**Why this note exists (pass-1 obstructions 1, 3, 4).** The retired torus lemma was the
only bridge from Theorem C (per-history masses) to p-independent COEFFICIENTS (counts
of histories). The bridge is rebuilt honestly: the count of (NA)/(HV)-linked value
assignments per shape is a THEOREM about explicit finite-field families, not a torus
orbit. Point counts of general finite-field definable families need NOT be one
polynomial in q — this note must PROVE polynomiality (or explicitly structured
q-dependence) for the SPECIFIC evaluation maps the classifier produces, or demonstrate
the failure (risk R1's wall).

**Key definitions.**
- Per node ν_{i+1} of a shape: the EVALUATION MAP V, from the node's side-pattern value
  tuple (d_j) to its transported vertex value vtx(ν_{i+1}) ∈ F_{i+2}ˣ (C.0's explicit
  formula: vtx = z̄^{−μm̂}·z̄^{a}·((R_anch/ψ^μ) mod ψ)).
- The LINKED COUNT of a shape S: C_S(p) := #{ joint value assignments over all nodes :
  per-node residual shape, irreducibility, nonzero-endpoint, and factor-collision/
  distinctness conditions hold; (HV) links each adjacent child's pattern lead to
  vtx(parent); (NA) holds at non-adjacent reads }. By [1] this is D4R.1's C_P̂(p),
  extended node by node to complete histories.
- FIBER-COUNT FUNCTION of V: c_V : Fˣ → ℕ, c_V(t) := #{pattern values : V = t}. The
  pass-1 counterexample establishes c_V is NOT constant (values 0 and 1 at fixed shape).

**The statement to prove (RESTATED at REV 4 per §1s — pass-3 obstruction 4: the
rev-3 form assigned one C_S and one W(S) to a raw shape whose unrolled pool dimension
grows with its loop parameters).**
> **Theorem VAL (target form).** (a) LOCAL: for each local move species m ∈ ℳ_n
> (extracted from the [2a] raw catalogue — the acyclic dependency, §1) there is ONE
> polynomial C_m ∈ ℚ[q], deg C_m ≤ W_loc(m), whose value at the species' pool sizes
> is the linked count of that single move, for every p — equivalently every prime
> power q at the finite-field layer. (b) CHAIN: for each unrolled finite history H,
> the linked count is the JREF-conditioned iterated pairing of the constituent local
> counts (VAL.2J below), hence one polynomial C_H of degree ≤ W(H) = Σ W_loc — the
> degree bound is PER HISTORY, parameter-dependent, never per raw shape. Resummed
> FAM objects are outside this theorem (§1s). [REV 3, pass-2 obstruction 2: the
> rev-2 "OR" clause (type-aggregated ℚ(q) values) is NOT a form that closes the
> stated RESUM — cancellation visible only after summing all shapes yields no local
> matrix M_e and no induction in e; it survives only as the VAL.3 REDESIGN branch
> below.]

**Route (three derivation-grade objects — VAL.1, JREF, VAL.2J — + a REDESIGN
branch; REV 4).**
- **VAL.1 (stratified fiber calculus — worked example CORRECTED at REV 3, pass-2
  obstruction 1).** For each node species, c_V is CONSTANT on the cells of an explicit
  p-independent stratification of the target F_{q^g}ˣ. Worked instance (V(A,B) = Aα+B,
  A, B ∈ F_qˣ; coordinates t = xα + y in the basis {α, 1} of F_{q²} over F_q): THREE
  cells — FG = {x ≠ 0, y ≠ 0} with c_V = 1 (unique (A,B) = (x,y)); FL = F_qˣ·α
  (y = 0) with c_V = 0 (needs B = 0, prohibited); FS = F_qˣ (x = 0) with c_V = 0
  (needs A = 0, prohibited). [The rev-2 two-cell display was WRONG: it assigned
  c_V = 1 on all of {t ∉ F_q·α} ⊇ FS.] ANCHOR ALIGNMENT (probe-forced): at anchor
  exponent a_eff ≠ 0 the cells are applied to the TWISTED target α^{−a_eff}·t, never
  to t in the fixed frame — the value probe (results/value_probe_output.txt) measured
  fixed-frame cell counts PROVABLY char-dependent (32 non-universal series; a q mod 3
  split at a_eff = 2) while TWISTED cells are fiber-constant EXACTLY at all 24 census
  q. Cell sizes and counts universal polynomials; the L3 necklace/Gauss counts are
  the depth-0 instance.
- **JREF (the JOINT REFINEMENT — DEFINED at REV 4; pass-3 obstruction 2 + its
  disposition 1: "or an explicit common refinement" postponed the decisive issue).**
  Per local species m with residual-factor tuple (φ₁, …, φ_k) and transported-value
  tuple (t₁, …, t_k): JREF(m) := the common refinement of (a) the k per-coordinate
  ANCHOR-TWISTED VAL.1 cell partitions, and (b) the RELATIONAL strata of exactly the
  finitely many polynomial relations that m's displayed evaluation and admissibility
  maps mention — factor collision/distinctness (φ_i = φ_j), hinge-ratio cells (the
  twisted cell of t_i/t_j where a shared parent links i and j), and the norm/trace
  strata to subfields tested by (NA)/(HV) and the nonzero-endpoint convention. The
  relation list is read off the species' displayed maps — a finite SYNTACTIC object.
  THREE BURDENS, each a proof duty of this note, consumed downstream as ONE object
  (M2's τ, RS.0, SQ.2 all condition on JREF cells and on nothing finer):
  (J1) FINITENESS/p-INDEPENDENCE — JREF(m) is a finite p-independent partition;
  (J2) POLYNOMIAL COUNTS — every JREF cell's size is a universal polynomial in q
  (a kernel duty: general definable families do NOT have this; it must come from the
  specific triangular/monomial shape of the vtx formulas);
  (J3) SUFFICIENCY — the joint outgoing one-step law is constant on JREF cells.
- **VAL.2J (JOINT hinge/collision law — now stated ON JREF; REV 4).** For each node
  with its FULL tuple of linked data — every (HV) hinge value it supplies to adjacent
  children, every sibling-collision/distinctness condition among its residual
  factors — the JOINT distribution of that tuple over the parent's linked assignments
  is constant on JREF cells (= burden J3). The scalar statement (one hinge, "the
  distribution of vtx(parent)") is the one-child special case; a node feeding k
  linked children needs the k-fold joint law — scalar marginals do NOT suffice when
  children are correlated through the parent, and MULTISETS of individual cells do
  NOT suffice either (pass-3 obstruction 2: ratios, traces, norms, collisions,
  shared-parent correlations all escape the multiset). Then the linked count is the
  iterated pairing Σ_{JREF cells} (parent joint count on the cell)·∏(child fiber
  counts) — polynomial with degree per §1s. This is where the note closes or hits
  R1: the matching must hold at EVERY hinge tuple of every species, μ ≥ 2 and a > 0
  included. Probe evidence: the (fixed × twisted) joint matrix is exactly constant on
  twisted cells at every census q (exploration-class; ONE two-node family — the
  k = 1 case; no k ≥ 2 joint family has been probed). JOINT-probe (exploration-class,
  runs with this note's draft): one species with k = 2 linked children sharing a
  parent PLUS one sibling-collision condition, exact F_q joint census over the 24-q
  list — measures joint-law constancy on JREF cells vs on the product of marginal
  cells; a marginal-constant/joint-varying finding refutes any τ lacking (b)-strata.
- **VAL.3 (aggregate branch — RECLASSIFIED at REV 3: a REDESIGN, not a fallback;
  pass-2 obstruction 2).** RS.0–RS.3 need per-(shape, type) coefficients BEFORE the
  final σ-aggregate; aggregate-only cancellation yields no local M_e and no induction
  in e. So if some C_S is genuinely non-polynomial: (i) VAL.3 is a NEW ARCHITECTURE —
  aggregate-block unknowns, a new transition law, a new closure theorem and
  solvability argument, a new DAG node [3′] replacing [3], budgeted 3+ units with its
  own verification rounds (§8 R8); (ii) it is entered only on BOTH a proved per-shape
  non-polynomiality (a census refutation per (†) below) AND a proved aggregate
  cancellation; (iii) a proved NON-cancellation at some σ and wild p is the R1 wall.
  Probe status: all 15 probed LINKED totals interpolated UNIVERSAL with surplus ≥ 15
  — the trigger is unexercised; the branch stays specified, unbudgeted.

**The census epistemics (†) — what finite q-data can and cannot decide (REV 4:
scope restricted to §1s integer-count classes; the rev-3 σ-aggregate clause is
STRUCK — pass-3 obstruction 5 + disposition 2: a resummed aggregate has geometric
denominators such as 1 − q^{−a}, and no single finite "A-shift" makes it an
integer-valued count).**
> **(†) Degree bound (LOC/HIST only).** For every local species m (resp. finite
> history H, resp. finite explicitly-listed history family with a displayed common
> monomial normalization q^{A_max}), pool arithmetic gives 0 ≤ C(q) ≤ q^{W} at every
> prime power q, with W the DISPLAYED pool dimension of that object. Consequence: if
> C agrees with ANY R ∈ ℚ(q) at all prime powers, then R is a POLYNOMIAL (a rational
> function integer-valued at infinitely many integer points has vanishing
> non-polynomial part) of degree ≤ W — hence R is THE unique degree-≤W interpolant
> through any W+1 census points.
>
> **Decision rule (refute-or-support).** Census at m ≥ W+2 exact points. REFUTE: one
> exact mismatch between the census and the degree-≤W interpolant, surviving
> adjudication, CONCLUSIVELY refutes ℚ(q)-universality of that count — by (†), finite
> data DOES decide the negative. SUPPORT: all points match — universality is
> SUPPORTED at surplus m − W − 1, never proved; acceptance still requires the
> VAL.1/VAL.2J derivation, with the census as its standing falsifier.
>
> **(†-AGG) The truncated aggregate-census protocol (REV 4 — the ONLY admissible
> aggregate census).** An aggregate census quantity is ADMISSIBLE iff it is (a) a
> FINITE explicitly-listed sum of LOC/HIST counts, (b) carrying a DISPLAYED common
> monomial normalization making it an integer count, and (c) carrying a DISPLAYED
> degree bound. The canonical instance: decided_σ(N) — an integer in [0, p^{nN}],
> and by SQ.0 (§6) a finite sum Σ_{threshold(H) ≤ N} C_H(q)·q^{nN−A(H)} of degree
> ≤ nN — so (†) applies verbatim at W = nN. The COMPLETED density R_σ is NEVER
> census-refuted by interpolation: it is tested only by the two-sided SQUEEZE
> brackets (⌈(R_σ(p) − env(N))p^{nN}⌉ ≤ decided_σ(N) ≤ ⌊R_σ(p)p^{nN}⌋), which refute
> a candidate VALUE at a given p quantitatively, envelope in hand. §8 R1(3)'s wall
> language is rebuilt on this protocol.

**Sealed gates (both EXACT — no sampling anywhere in this note).**
- **VALUE-Fq (q-list WIDENED at REV 3 — the rev-2 nine-point list against degree-8
  linked series had surplus ZERO: non-discriminating by (†)).** Direct exhaustive
  enumeration of linked counts over F_q for a sealed list of n ≤ 5 two-node
  configurations INCLUDING the pass-1 counterexample family (deg ψ = 2, μ = 2,
  a_eff ∈ {0, 1, 2}, lead factor (Az+B)) and the FAM-Q quadratic-cofactor stress
  family (genuinely non-constant fibers), at the 24-point list
  q ∈ {2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,49,53,59} — prime
  powers included deliberately. Seal: per-series displayed pool dimension W (§1s
  class stated per series — LOC or finite HIST), the VAL.1/VAL.2J closed forms with
  exact values at every q, AND (REV 4) the JREF layer — the sealed JREF cell list
  with per-cell counts for each gated species, verified cell-by-cell. PASS = exact
  integer equality throughout, with surplus ≥ 3 per series per (†). STATUS: the exploration-class probe
  (verification/value_probe.py, 2026-07-26) already ran this geometry UNSEALED —
  all linked totals UNIVERSAL, twisted-cell fiber constancy exact, aggregates match
  at wild p; the gate re-runs SEALED with the closed forms committed first (Case-K
  discipline), the anchor-twist requirement now itself a sealed prediction.
- **VALUE-p (the p-adic shadow).** n = 5, p = 2 and p = 3: root read carrying residual
  ψ²·(linear) (the counterexample geometry), one linked descend. Seal: the exact
  prefix-event count C·p^{5N−A}, verified by EXHAUSTIVE enumeration mod p^N (feasible:
  2^20 at N = 4; 3^15 at N = 3). PASS = exact.
- A FAIL is adjudicated (prediction-derivation error vs theory error); if theory: run
  §8 R1's isolation experiment BEFORE any further RESUM work.

## 3. NOTES [2a] SPECIES + [2b] STATE-GEOM — the rev-2 MENU, split acyclic (REV 4: joint-refined τ, M4a-X, M4b-T equivariance; [2b] gated on STATE-probe-2)

**Split delivery (pass-2 obstruction 3):** [2a] SPECIES = the raw catalogue 𝒮_n^raw —
M1's bounds + M5's completeness, with NO strata and NO state types: this is the finite
list Theorem VAL quantifies over, so [1v] consumes [2a] and no cycle exists. [2b]
STATE-GEOM = M2 + M4a + M4b/M4b-T, drafted AFTER [1v] (it consumes the twisted cells).
𝒮_n = 𝒮_n^raw enriched by [2b]'s types. M3 stays a remark. Theorem MENU below is
delivered jointly: its finiteness/completeness clauses by [2a], its parameter-geometry
and type clauses by [2b].

**The statement to prove.**
> **Theorem MENU.** Fix n. Define the shape of a realizable canonical-policy history by
> forgetting: all side HEIGHTS h (per read), all self-loop repetition counts (depths),
> all digit values — retaining the finite tree of reads with per-node species
> (increment / recentering / root), slope denominators e, key degrees, multiplicities
> μ, residual SHAPES (degree–multiplicity partitions), residue degrees w,
> stride/anchor combinatorics, and the flank/co-factor pattern. Then 𝒮_n is FINITE and
> INDEPENDENT of p, and every realizable history is a shape + a tuple of ℕ-parameters
> (heights, depths) lying in explicit per-shape sets: products of cones INTERSECTED
> WITH CONGRUENCE LATTICES (M4a). NO claim that the lattice points exhaust
> realizability (pass-1 obstruction 3): the arithmetic layer — (NA)/(HV), factor
> degrees and irreducibility, nonzero endpoints, cofactor/residual collisions — is
> counted PER LATTICE POINT by [1v], never encoded in the cone.

**Load-bearing lemmas.**
- **M1 (per-node data bounded — bound CORRECTED, pass-1 concern 1).** Display the
  degree identity: D_{r+1} = e_r·g_r·D_r — a genuine increment multiplies the key
  degree by e_r·g_r ≥ 2; a degree-preserving recentering has e_read = g = 1 and leaves
  D fixed. Hence ∏_r e_r·g_r ≤ n and the CUMULATIVE residue degree ∏_r g_r ≤ n (the
  rev-1 "n!-bounded" is retired; the review found no unbounded-g counterexample, and
  this displayed invariant is why). Also e ≤ n, μ ≤ n, residual degree ≤ n, #sides ≤ n,
  strides/anchors ≤ side width ≤ n — every bound the one displayed degree budget.
- **M2 (STATE — the JOINT-REFINED type; REWRITTEN AGAIN at REV 4, pass-3
  obstruction 2 + disposition 4: the rev-3 multiset of individual cells does NOT
  determine the joint outgoing law — ratios, traces, norms, collisions, shared-parent
  correlations escape it). Lives in [2b].** The LOOP STATE TYPE at a node is
  τ = (the JREF CELL of the FULL residual-factor tuple — [1v]'s joint refinement,
  §2v, carrying the individual twisted cells AND all relational strata as ONE
  object; anchor a; tower phase). This is the plan's SINGLE state definition: M2,
  RS.PRE/RS.0, SQ.2 and every conditional law condition on τ and on NOTHING finer or
  coarser — a law needing more than τ is a lumpability failure (R2), never a local
  patch. DECIDED (rev 2 was internally inconsistent about position): loop POSITION
  and heights are NOT in τ; their irrelevance is RS.0(β)'s THEOREM, never a
  definition. Prove: (i) τ ranges over a FINITE p-INDEPENDENT list 𝒯_n (from JREF
  burden J1 + the M1 bounds); (ii) LUMPABILITY, not label-closure (pass-2's
  distinction) — any two CONCRETE states of one type have IDENTICAL full outgoing
  one-step laws: the JOINT law of (next node data, all hinge values, all
  collision/admissibility data), exhibited per move species, with the e_birth vs
  e_read threading re-walked once here (what "self-loop at fixed key data" is at
  order r ≥ 2). Route: Theorem C freshness (fresh digits uniform on the state
  cylinder — the mechanism the state probe verified exactly: every readable word
  cell 1024/729 on the nose) + VAL.2J constancy on JREF cells (burden J3 — the
  route now consumes the JOINT law, closing pass-3's "the state definition does not
  support the theorem it is supposed to prove"); (iii) proper refinements number
  ≤ n − 1 (L5fix Invariant 1 transported). Load-bearing TWICE: menu finiteness and
  the block-index set of RESUM's system (RS.0). ACCEPTANCE of [2b] is BLOCKED on
  STATE-probe-2 (§4) — it tests M2(ii) directly (pass-3 obstruction 7).
- **M3 (lift symmetry — DEMOTED; pass-1 obstruction 2).** The C.0 lift-translation
  remark is retained only as a consistency check on shape-determined volumes (C.3
  already supplies those). NO counting quotient runs through it; the menu counts
  canonical-policy histories ([1]).
- **M4a (parameter geometry — necessary conditions only).** Per shape: the
  ℕ-parameters of realizable histories lie in an explicit product of cones intersected
  with congruence lattices (strictly-decreasing-slope inequalities; h ≡ 0 mod
  e-denominator lattices), and vol(E_fresh)-exponents are AFFINE in these parameters
  with positive weights. *Sketch:* D.3's stride rule makes the per-digit pin count
  affine in h; the (‡) ledger arithmetic of the decomposition note §2, unconditional
  via §B2-DEF/§C. Sufficiency NOT claimed (obstruction 3).
- **M4a-X (EXACT-DOMAIN — NEW OPEN KERNEL at REV 4; pass-3 obstruction 1: M4a's
  cones are NECESSARY only, yet RS.1 summed them as exact domains — summing a
  containing cone overcounts histories).** Target theorem, either route: (Route A —
  semilinear via zero-extension) the M4b-T translation bijection is defined at EVERY
  lattice point of the M4a cone, with count 0 allowed; then the per-point count
  (zeros included) is constant on each congruence class, the zero pattern is itself
  translation-invariant, and the EXACT realizable domain = the union of the nonzero
  classes — semilinear by construction, with per-class counts C_{S,τ}. (Route B —
  admissibility classes) if the bijection degenerates at boundary strata, partition
  the cone into FINITELY MANY explicitly-listed exact admissibility classes with a
  per-class count polynomial each; RS.1 then sums per class. Until M4a-X closes, NO
  cone-lattice sum is exact: RS.1 cites M4a-X, never M4a alone. Deciding probe: the
  MENU-n3 parameter check is upgraded two-sided (clause (iii), gate below).
- **M4b (per-point counts factor through the type) + M4b-T (TRANSLATION — the new
  arithmetic theorem pass-2 concern 3 identified; EQUIVARIANCE FORM at REV 4,
  pass-3 concerns 2 + 3).** At every lattice point of M4a's cone, the number of
  realizable value assignments (0 allowed) is C_{S,τ}(q) — a function of shape and
  state type ONLY, not of the cone position. *Route:* M4b-T FIRST, as a NORMAL-FORM
  AUDIT whose TARGET CONCLUSION — proved, never premised (pass-3 concern 3) — is
  that after auditing ALL residual coefficients, factor collisions, and lift
  choices, the anchor monomial z̄^{a−μm̂} (C.0's display) is the ONLY
  position-dependent factor. PRECISE EQUIVARIANCE STATEMENT (pass-3 concern 2):
  translation by a lattice vector v induces an explicit BIJECTION of linked value
  systems composing each target with the twist by anchor^{⟨w,v⟩}; this carries the
  JREF stratification at point P to the one at P + v, a priori PERMUTING cell
  labels by some π_v — the natural result is a bijection between two differently
  twisted stratifications, NOT automatically preservation of one fixed label.
  EQUIVARIANCE CLAUSE (to prove): with types defined in the twisted frame, π_v acts
  trivially on type labels; if instead π_v is nontrivial, RS.0 and K_e are
  re-indexed by π-orbits and the cone sums run per orbit — the matrix indexing must
  absorb π_v, stated here so RESUM cannot silently assume π_v = id. THEN VAL.2J +
  M2(ii) close the count. Evidence: the value probe's a_eff ∈ {0, 1, 2}
  twisted-cell exactness is M4b-T's shadow; its fixed-frame char-splits are exactly
  what M4b-T looks like when the twist is omitted. With M4a-X, this is what makes
  per-cone geometric resummation legitimate in RESUM.
- **M5 (menu completeness).** Every monic f with terminating resolution has its
  canonical history of some shape in 𝒮_n. *Sketch:* §B2-DEF TRANS constructs stage
  r+1 data of exactly the retained vocabulary; nothing else occurs.

**Kernels:** M2 (STATE, a lumpability theorem on the JOINT-REFINED τ), M4a (the
affine-exponent + congruence-lattice bookkeeping, with the Case-J anchor-monomial
a > 0 exponents as worked instances), M4a-X (EXACT-DOMAIN — OPEN, REV 4), and M4b-T
(the translation normal-form audit + equivariance clause — REV 4).

**Sealed gate MENU-n3 (EXHAUSTIVE; pass-1 obstruction 8 repairs).** Enumerate 𝒮_3
with per-shape parameter sets and state types BEFORE any census. Then: (a) EXHAUSTIVE
enumeration of ALL monic cubics mod p^N — p = 2 at N = 8 (2^24 boxes), p = 3 at N = 5
(3^15) — every f classified to decision or marked undecided-at-N; (b) independent
ORACLE cross-check: every decided f's type vs PARI factorpadic — closes the
shared-blindness loophole at the DECISION level; RECORDED as not closing it at the
history-extraction level (that residue is M5's proof burden, not the gate's); (c) tame
control p = 7 by 10⁶ sampling, labeled consistency-only. PASS = (i) zero stray shapes;
(ii) every sealed shape with nonzero predicted level-N mass realized at its EXACT
predicted count — exhaustive sets make this deterministic; no "given the sample size"
clause survives; (iii) TWO-SIDED parameter exactness (REV 4 — M4a-X's deciding
probe): every realized parameter tuple lies in the sealed exact domain AND every
sealed-domain lattice point within the level-N budget is realized at its sealed
per-point count (sealed zeros included) — orphans and strays both zero; (iv) zero
oracle mismatches. LIMITATION RECORDED: n = 3 exercises deep species only lightly
(risk R3's n = 4 escalation clause stands).

## 3r. NOTE [2r] REL — the relative ledger (REV 3: four-obligation REL.2, decision-independent gate)

**Why.** RESUM's mixed legs and SQUEEZE's domination induction consume β_m(q^δ) — the
cluster law over the unramified degree-δ extension. The ALGEBRA is fine and was never
the problem (pass-1's own closing: q ↦ q^δ preserves ℚ(q) — recorded in §8's
non-failure list). What is MISSING is the measure statement: the accepted Theorem C is
stated for monic f over ℤ_p, and nothing certified says the sub-cluster continuation
IS the MOVES measure theory over O_δ := W(F_{p^δ}). Without that, SQ.2's induction
hypothesis at base-changed arguments sits outside the certified perimeter.

**Load-bearing statements.**
- **REL.1 (Theorem C over O).** §A/§B2-DEF/§C hold verbatim over any complete
  unramified O with residue field F_{p^δ}: monic f ∈ O[x], digit alphabets the
  D.3(e)(i) pieces over F_{p^δ}, masses in vol_O. *Route:* a derivation-grade
  RE-SCOPING PASS over the accepted texts — list every step that touches the base
  (Fact A/B division bookkeeping: expected base-free; TYP(a)'s per-digit additive
  counting: retypes from 𝔽_p-linear to additive on O-digit blocks; C.0's block
  convention: per-position residue bases over F_{p^δ}). This is a NEW THEOREM with its
  own verification passes — "by inspection" is claimed nowhere without the pass
  (risk R6's REV-2 clause).
- **REL.2 (sub-cluster base change — four NAMED obligations at REV 3; pass-2
  concern 4: this is NOT a consequence of REL.1).** At a read whose residual factor
  has residue degree δ, the conditional continuation measure of that factor's cluster
  is measure-exactly the REL.1 theory over O_δ, with pool sizes q^δ — the precise
  content of JOINT-D1's q ↦ q^w clause, now THROUGH Theorem C. The proof must supply,
  separately: (a) the COORDINATE IDENTIFICATION — which O_δ-monic-polynomial
  coordinates the conditioned ℤ_p-slice acquires; (b) the NORMALIZATION/JACOBIAN —
  the conditioned ℤ_p-mass equals the vol_{O_δ} mass (a measure comparison, not a
  bijection alone); (c) SIBLING INDEPENDENCE — conditioning on the other factors does
  not distort the cluster's law; (d) LIFT-POLICY COMPATIBILITY — [1]'s canonical
  H_can commutes with the identification. Consumers: RS.1's mixed legs; SQ.2's
  induction at β_m(p^δ).
- **REL.3 (positivity/domination transfer).** The finite-level covering and
  monotone-domination statements SQUEEZE needs, restated and proved over O — stated
  separately because SQ.2 consumes them at q = p^δ, where "positive mass < 1" must be
  a theorem about vol_O, not a formal substitution.

**Kernel:** REL.1's re-scoping pass (fresh context, accepted §C text in hand,
step-by-step base audit; the one place a silent q = p usage could hide is TYP(a)'s
per-digit 𝔽_p-linearity, retyped at §C rev 11 — walk it first).

**Sealed gate REL-n4 (INDEPENDENCE REPAIRED at REV 3 — pass-2 concern 4's
shared-normalization loophole).** p = 2, n = 4: condition on root reads whose residual
factor is an irreducible QUADRATIC (δ = 2); seal the conditional refinement law of
that cluster from the O = W(F_4) formulas (the engine's q ↦ q² layer). Verify EXACTLY
two ways: (i) a ℤ_2 side described WITHOUT MOVES strata — the conditioning event
written as explicit root-read coefficient congruences (Theorem-C-certified vocabulary
only) and the cluster's refinement read off the PARI factorpadic DECISION oracle, on
the exhaustive level-N slice (2^{4N} boxes, N ≤ 5); (ii) a direct W(F_4)-side
enumeration of the corresponding MOVES strata at matching level. PASS = exact equality
of both with the sealed law. RECORDED RESIDUE: (i) is MOVES-free at the DECISION level
only; the history-level identification stays REL.2(a)–(d)'s proof burden, not the
gate's.

## 4. NOTE [3] RESUM — the depth resummation into rational functions of q (REV 4: normalized kernel K_e with displayed conditionality, ESCAPE kernel, STATE-probe-2 blocking [2b]+[3])

**The algebraic form (REV 2 — BLOCK-triangular; pass-1 obstruction 5 + concern 5).**
Unknowns β_{e,τ} : {types of degree e} → ℚ(q), indexed by cluster size e ≤ n AND state
type τ ∈ 𝒯_n (MENU M2's finite p-independent list — rev 1's scalar-per-e form was
UNPROVED closure, asserted against risk R2; closure is now the theorem RS.0):

  (R_e)   β_{e,·} = q^{−e(e−1)/2} · M_e(q) β_{e,·} + SHALLOW_{e,·}      (e = 1, …, n)

with M_e(q) the SAME-SIZE TRANSITION MATRIX (rows/columns = state types; entries =
[1v]-counted one-move coefficients in ℚ(q)); SHALLOW_{e,·} collects deciding/branching
root reads (coefficients: MENU shapes × [1v] counts × [2r]-certified mixed legs
β_m(q^δ), m < e). Triangular in e; within e the block solve is
(I − q^{−e(e−1)/2}M_e)^{−1}, licit by RS.3. The n = 2 instance is the 1×1 case (W6's
geometric series, denominator q²+q+1; `msW_eighth_le` its p = 2 inequality shadow).
R_σ := the σ-component of the full-space assembly over root residual shapes (the L3
Gauss/necklace layer). Engine form: `verification/om_density_engine.py`, BB3_infinity
§4.1 — whose scalar FULLMONIC is hereby a CONJECTURED degenerate case (|𝒯| = 1), not
an input.

**Key definitions.** Per-shape weight w(S) ∈ ℚ(q)-monomials: by MENU M4a the
fresh-volume exponent is affine in the shape's ℕ-parameters, so the sum over one
ladder/tower direction is a geometric series over a congruence sublattice with ratio
q^{−(positive weight)}; per-(shape, type) VALUE count C_{S,τ}(q): from [1v] Theorem VAL
via [2b] M4b + M4b-T — NOT from the retired torus lemma.

- **RS.PRE (the NORMALIZED kernel — definition supplied at REV 3; pass-2
  obstruction 7: rev 2 never fixed what M_e contains).** Define K_e(q) entrywise as a
  CONDITIONAL MASS: K_e(q)_{τ,τ′} := (the [1v]-counted, M4a-height-resummed mass of
  the disjoint union of one-move continuations τ → τ′ inside one source cylinder) /
  (the source cylinder's mass) — fresh-volume costs, cone/height sums, multiplicities
  and the displayed exterior factor ALL INSIDE. Then q^{−e(e−1)/2}M_e(q) := K_e(q)
  (the display (R_e) is unchanged; the exterior factor is notation, not an extra
  cost). Because the continuations are DISJOINT sub-events of the source cylinder
  (D4R.0) and height resummation is countable additivity over disjoint cylinders,
  K_e(p) ≥ 0 and Σ_{τ′} K_e(p)_{τ,τ′} + (deciding/branching fraction) ≤ 1 hold at
  every p: substochasticity is inherited from measure, never asserted of a resummed
  matrix. CONDITIONALITY DISPLAYED (REV 4, pass-3 disposition 7: "by construction"
  was overclaimed): the inheritance is conditional on THREE named inputs — (1) M4a-X
  exact domains (else the resummed rows sum masses of non-events); (2) D4R.0
  disjointness after height grouping; (3) M2(ii) lumpability (else the quotient by τ
  is not well-defined). K_e carries all three tags until each closes. Every
  probabilistic claim in RS.3/SQ.2 is about K_e.
- **RS.0 (TYPE-CLOSURE — promoted kernel; PROOF SHAPE fixed at REV 3, pass-2
  concern 8 + obstruction 4).** Two theorems, proved not extrapolated: (α)
  LUMPABILITY = M2(ii) — any two concrete same-type states have identical full
  outgoing JOINT laws (VAL.2J + Theorem C freshness); (β) POSITION/HEIGHT
  ELIMINATION, as a finite-state BISIMULATION: exhibit the height-shift conjugacy —
  the state at height h+1 is the state at height h composed with one uniform fresh
  layer (the exact mechanism behind the probe's uniform-word rows) — so the
  conditional law is h-invariant and the retained data after k self-loops is a state
  type, not a k-indexed object. The probe's cross-height row (S1 marginal = S2 word,
  16 cells exact) is evidence for ONE comparison only — recorded as such, never cited
  as the proof. A same-type failure surviving adjudication and one 𝒯-refinement =
  risk R2's wall, probed by STATE-probe-2 below.

**Load-bearing lemmas.**
- **RS.1 (the aggregation identity — REV 4: exact domains + Tonelli).** For each
  type σ: Σ_{complete realizable canonical H of type σ} mass(H) — a positive series
  of masses of DISJOINT events (D4R.0), hence bounded by 1 and unconditionally
  convergent with all rearrangements licit (Tonelli; the rev-3 citation of the
  X.1b-tagged envelope for CONVERGENCE is dropped — the envelope is needed only for
  RATES, in X.2/SQUEEZE) — equals, after grouping by (MENU shape, state type) and
  resumming each parameter set, the σ-component of the solution of (R_e).
  *Sketch:* Theorem C gives mass(H) = ∏ vol(E_fresh); D4R.0/D4R.1 give disjoint
  exhaustion (canonical fibers — no quotient multiplicity; the pass-1 obstruction-2
  aggregation gap is repaired upstream, in [1]); group by shape (M5); per shape,
  Fubini the lattice sum over the EXACT semilinear domain (M4a-X — REV 4, pass-3
  obstruction 1: the rev-3 sketch summed the containing CONE, which overcounts;
  per-class summation with sealed zero classes replaces it); per-point counts are
  C_{S,τ}(q), constant across each class (M4b + M4b-T's equivariance clause);
  per-direction sums are geometric series over congruence sublattices (M4a); the
  self-loop directions are the M_e legs (a depth-k chain = k-fold composition of ONE
  matrix — RS.0; the geometric FIXPOINT is the block solve, not a new sum).
- **RS.2 (coefficient p-independence).** Every coefficient of (R_e) is one fixed
  element of ℚ(q). REV 2 HONESTY (pass-1 obstruction 4): this rests on [1v] Theorem
  VAL — it does NOT follow from Theorem C + Claim 4.3; the torus-lemma bridge is
  dead. (REV 3: the VAL.3 aggregate form does NOT support THIS system — if VAL.3 is
  entered, RS.2 and the whole block system are re-derived in [3′], per §2v/R8.)
  Shapes and exponents: [2a]/[2b]. Mixed legs: [2r].
  Per-shape emptiness at wild p = polynomial vanishing (W1's pool-size effect).
  p enters only at evaluation q = p.
- **RS.3 (solvability — REBUILT at REV 4; pass-3 obstruction 3: the rev-3 route
  "B(n) via the menu diameter + X.1b's STALL budget" is STRUCK — WEIGHT-CHARGE only
  bounds zero-gain nodes by s(n)·v_p(disc f), and v_p(disc f) is UNBOUNDED across a
  source cylinder, so no B depending only on n follows; individual-path termination
  also gives no uniform spectral gap).** (i) cites the SEPARATE kernel:
  > **ESCAPE (OPEN KERNEL, REV 4 — the uniform escape/spectral-radius argument).**
  > There exist B = B(n) and c = c(n) such that for every e ≤ n, every τ ∈ 𝒯_n(e),
  > and every p: the B-step still-in-block conditional mass from any concrete state
  > of type τ is ≤ 1 − p^{−c} — i.e. K_e(p)^B has all row sums ≤ 1 − p^{−c}.
  Route candidates (named, neither asserted): (E1) REACHABLE-EXIT — from every τ the
  K_e-transition graph reaches, within B ≤ |𝒯_n(e)| steps, a type with one-step exit
  mass ≥ p^{−c₀}; the per-step witness is an (NA)/(HV)-style realizability lemma: at
  each self-loop read at least one fresh-digit assignment produces a deciding or
  strictly-refining outcome, with witness count ≥ 1 from the VAL tables — a lemma to
  PROVE, not assume. (E2) DRIFT/RENEWAL fallback (the pass-3 suggestion, tolerant of
  unbounded zero-gain runs): a weighted norm V(τ, key weight) with K_e V ≤ λV,
  λ = λ(n, p) < 1, from D.10's strict weight climb + the positive per-move
  fresh-volume cost. **ESCAPE-probe (exploration-class, runs before [3] drafting):**
  in the STATE-probe-2 cylinders (n = 6, p = 2, conditioned, N = 8) and the 2^24
  cubic box, measure per-type one-step and B-step exit masses against a sealed
  candidate (B, c); a type with B-step exit mass 0 at every loop position refutes
  (E1) for that candidate and forces (E2). With RS.PRE's K_e(p) ≥ 0 and
  substochasticity, ESCAPE gives ρ(K_e(p)) < 1, Neumann convergence, and
  (I − K_e(p))^{−1} ≥ 0. (ii) Hence det(I − K_e) ≠ 0 at infinitely many evaluations,
  so ≠ 0 in ℚ(q): the symbolic block solve is licit. Solution: R_σ ∈ ℚ(q), one per
  σ. RS.3 no longer cites X.1b ANYWHERE; it is CONDITIONAL-ON-ESCAPE until the
  kernel closes.
- **RS.4 (checksum — CONDITIONAL, tag inline at REV 4, pass-3 concern 5).**
  Σ_σ R_σ = 1 identically in q (series = 1 at every p by [5]; a rational function
  equal to 1 at infinitely many q is 1). Cheapest layer invariant. STANDING TAG:
  RS.4 inherits every condition of the block solve (ESCAPE; K_e's three RS.PRE
  inputs; X.1b through [5]'s X.2 constants) — its acceptance record, like [3]'s,
  [4]'s, and the capstone's, may NOT be marked unconditional before those close
  (§7's acceptance-record rule).
- **RS.5 (engine agreement).** Solved R_σ ≡ `alpha_full(n)[σ]` symbolically, n = 2…5 —
  the decomposition note's Thm 4.5 claim, proved rather than conditional. (Since the
  engine shares the value-count formulas, this is a CONSISTENCY identity, never
  independent evidence — pass-1 obstruction 8.)

**Kernels (derivation-grade — the campaign's biggest, now four):**
1. **RS.1's regrouping**: multi-side reads (strictly-decreasing-slope cones, the gap
   substitution `_sum_by_gaps`), summation over M4a-X's EXACT classes only, the
   conditional-on-ancestors chain via C.1.5 stepwise (NO independence assumption),
   base-changed legs entering ONLY through [2r] REL.2.
2. **The depth-leg coefficient derivation**: M_e's entries with the Case-J a > 0
   anchor exponents inline — a wrong anchor exponent silently corrupts every deep
   coefficient.
3. **RS.0 TYPE-CLOSURE**: with M2/VAL.2J in hand, the height-shift bisimulation —
   the residual argument that loop position adds nothing (RS.0(β)).
4. **ESCAPE (OPEN — REV 4)**: the uniform B(n)-step spectral-gap lemma above, routes
   (E1)/(E2), with the ESCAPE-probe as its front-loaded discriminator.

**Sealed gates (two; STATE-probe runs FIRST, before this note is drafted).**
- **STATE-probe — RAN 2026-07-26 (exploration-class; results/state_probe_output.txt).
  STATUS: probe-level NO-WALL; the rev-2 gate spec was NOT satisfied and the gate is
  REOPENED (pass-2 obstruction 5).** Feasibility finding (recorded in the script
  docstring): in exhaustible monic boxes the vtx coordinate is RIGID below n = 6 —
  the specified different-vtx-stratum configuration does not exist there. The probe
  instead varied the UNTYPED retained value (the RS residual root r ∈ F_{q²}ˣ: 3
  states at p = 2, 8 at p = 3, including cross-VAL.1-line pairs) and found every
  readable-word law EXACTLY uniform and r-independent (every cell 1024/729 on the
  nose), plus one exact cross-height match. That is negative evidence for R2 at the
  probed rows ONLY — it does not establish RS.0. SPEC FIX (the pass-2 internal
  inconsistency): since the vtx-stratum is PART of τ, different-stratum states are
  different TYPES; the pass condition is restated — (i) same type (same twisted cell;
  untyped values and loop position varying) ⟹ EXACTLY equal laws; (ii) each type's
  law matches its sealed per-τ K_e row EXACTLY; cross-type differences are expected
  and carried by the block system.
- **STATE-probe-2 (NEW at REV 3 — the vtx-VARYING regime; REQUIRED to PASS before
  [2b] STATE-GEOM OR [3] RESUM may be ACCEPTED — blocking scope WIDENED at REV 4,
  pass-3 obstruction 7: it directly tests M2(ii), a theorem of [2b]; accepting
  STATE-GEOM before it passes would violate the sealed-gate protocol, and every
  downstream type-indexed count presupposes [2b]).** Configuration (the n = 6 one the feasibility finding
  names): p = 2, monic sextics, root Newton side with residual R₀ = ψ²·χ (ψ = z²+z+1;
  χ a monic quadratic coprime to ψ) — the continuing ψ-cluster's vtx = χ(α) ∈ F_4ˣ
  GENUINELY VARIES across VAL.1 twisted cells as χ ranges. Seal: the per-τ
  conditional next-move rows from RS.PRE/M2. Census: exhaustive CONDITIONED CYLINDERS
  (root stratum pinned, fresh digits free), N = 8, designed so each state's cylinder
  is ≤ 2^28 (feasible: the first probe's 2^26 box censused in 3 s; ≤ 12 s/state on
  40 workers, ≤ 12 states — minutes); states in ≥ 2 distinct twisted cells AND ≥ 2
  loop-position variants per cell (pass-2 concern 8's residue). PASS = conditions
  (i)+(ii) above, exactly. Adjudication and the single-𝒯-refinement clause as in
  STATE-probe; a second same-type failure invokes §8 R2's wall protocol.
- **RESUM-n3 (the headline gate, REV 2 form).** Solve (R_e) for n = 3 symbolically.
  Seal BEFORE any census: the FIVE rational functions R_σ, σ ∈ {(1,1)³, (1,1)+(1,2),
  (1,3), (1,1)+(2,1), (3,1)}, values at p = 2, 3 (wild), 5, 7 (tame), the checksum,
  AND the exact finite-level partial sums by depth. DISCRIMINATING layer (exact,
  pass-1 obstruction 8): decided_σ(N) by EXHAUSTIVE enumeration (p = 2: N ≤ 8, 2^24;
  p = 3: N ≤ 5, 3^15), types from the PARI `factorpadic` oracle
  (`verification/quartic_oracle.py` pattern) — EXACT integer equality per (σ, N)
  against the sealed theory totals; oracle types are extractor-independent, so this
  layer discriminates. RECLASSIFIED at REV 3 (pass-2 concern 7): the per-DEPTH-ROW
  comparison is a CONSISTENCY layer — assigning f to a depth row uses the history
  extractor under test, so it is exact but not independent. Any exact mismatch in the
  discriminating layer surviving adjudication is structural (§8 R1/R2). CONSISTENCY
  layer (labeled non-discriminating): the depth rows; 10⁶–10⁷ sampled cubics at all
  four primes within EXHAUST-tail + σ-bands; `om_density_engine.alpha_full(3)` and
  `reconcile_om_bcfg.py` cross-checks.

## 5. NOTE [5] EXHAUST — the discriminant-tail tie-in (REV 3: X.1a index table; X.1b OPEN kernel WEIGHT-CHARGE)

**What already stands (decomposition note §3, accepted):** Lemma 3.2 (still descending
at depth d ⟹ v_p(disc f) ≥ 2d — GMN theorem of the index, pins (P1)–(P3) verbatim in
`GMN_citations.md`), Lemma 3.3 (elementary tail: μ{v_p(disc) ≥ D} ≤
(n−1)·p^{−⌈(D−n·v_p(n))/(n−1)⌉}), Cor 3.4 (Desc_d envelope, geometric in d). Pointwise
depth ⟹ disc; NO per-depth identities (the SELFLOOP wall stays sidestepped).

**REV 2 REDESIGN (pass-1 obstruction 7: rev 1's X.1 claimed every MOVES node is a unit
GMN event while its own kernel paragraph admitted zero-index recenterings —
incompatible; the raw node-count premise is WITHDRAWN).** Depth splits into two tracks:
- **X.1a (genuine-event dictionary — per-species TABLE duty added at REV 3, pass-2
  concern 5).** d_gen(H) := #{nodes with GMN index gain ind_r ≥ 1}. "All increments
  count" is NOT taken from the name GMN: the kernel must produce a per-species INDEX
  TABLE — for every increment species and every recentering species, the node's own
  polygon, its candidate lattice point (s+e, u+(d−1)h), and the evaluated GMN index
  formula showing ind ≥ 1 or ind = 0 under the (P1) on-or-below convention, with
  endpoint and zero-contributing cases explicitly ruled in or out (the pass-1 EXHAUST
  failure was exactly a convention slip of this kind; (P3) accounting, GMN Thm 4.18's
  "including refinements", pinned). Then stratum(H) ⊆ Desc_{d_gen(H)} ⊆
  {v_p(disc) ≥ 2·d_gen(H)}; the §B2-DEF stage dictionary (D.12) aligns polygons.
- **X.1b (STALL — DEMOTED at REV 3 from asserted lemma to OPEN KERNEL with its own
  probe; pass-2 obstruction 6: the rev-2 premise does not imply the affine bound —
  a "local height budget" is not globally coercive and can itself be unbounded).**
  What survives: each zero-index recentering strictly increases the current key's
  weight (D.10: the new key's weight is the consumed side's value > the old key's
  weight). The affine consequence is now a TARGET, reduced to ONE named missing
  lemma:
  > **WEIGHT-CHARGE (OPEN).** Every unit of key-weight climbed by a zero-gain ladder
  > is charged, injectively up to a factor s(n), against a unit of v_p(disc f) — via
  > the L5fix-Invariant-2 different budget, which is itself bounded by v_p(disc f).
  > That is: #{zero-gain nodes of H} ≤ s(n)·v_p(disc f), with explicit s(n).
  DISPLAYED two-step reduction (so the kernel's burden is exactly WEIGHT-CHARGE):
  given WEIGHT-CHARGE and X.1a's v_p(disc) ≥ 2·d_gen,
  d_total = d_gen + d_zero ≤ v_p(disc)/2 + s(n)·v_p(disc), hence
  v_p(disc f) ≥ d_total(H)/(s(n) + 1/2) — affine with named constants, and the
  geometric-in-d_total envelope survives with rescaled constants. STATUS: OPEN until
  derived. CONSUMERS NARROWED at REV 4: X.2's env constants (hence SQ.3 and every
  envelope gate layer) remain CONDITIONAL-ON-X.1b; RS.1's convergence is discharged
  by Tonelli (§4), SQ.1's finiteness by SQ.0 (§6), and RS.3's gap by ESCAPE (§4) —
  pass-3 obstruction 3 established that WEIGHT-CHARGE canNOT yield a uniform B(n)
  (v_p(disc) is unbounded across a source cylinder), so no consumer may cite it for
  uniform leakage.
  **STALL-probe (exploration-class, runs with the kernel draft):** exhaustive p = 2
  boxes — the full cubic box 2^24 at N = 8 and the quartic RS-chain conditioned
  cylinder 2^26 at N = 10 (the state-probe geometry: RS self-loops ARE zero-gain
  recenterings) — measure the max zero-gain run and the per-f ratio
  #zero-gain / v_p(disc f); one f violating the candidate s(n) kills that constant
  before the kernel is drafted around it. If the derivation instead finds a legal
  UNBOUNDED zero-gain chain (REV 4 rewording, pass-3 concern 6: this is NOT
  automatically "a hole in the termination story" — unbounded finite chain lengths
  across inputs are compatible with a.e. termination, and even an infinite chain on
  a measure-zero input can be compatible with a density theorem): it DEFEATS the
  envelope and uniform-leak designs as built; the exact termination consequence is
  adjudicated against L5fix's precise quantifiers — stop, record, check L5fix's
  statement, run §8 R4's experiment.
- **X.2 (undecided ⊆ deep-or-tall, coercivity DISPLAYED — pass-1 concern 6).** Kernel
  PROGRESS: each move's fresh content constrains levels ≤ an explicit affine function
  of its heights, so f undecided at level N has (d_total ≥ d*(N)) OR (some height ≥
  h*(N)), with the d*/h* balance displayed — no "positive exponents ⟹ done" step
  (mixed height cones can grow nominal exponent and required precision at different
  rates; the uniform bound must be exhibited). Then env(N) ≤ c₃(n)·p^{−c₄(n)·N} with
  constants traced to X.1b (OPEN — this trace carries the CONDITIONAL-ON-X.1b tag
  until WEIGHT-CHARGE closes) + M4a tails (from [2b] — the DAG edge pass-2 found
  missing). This is what SQUEEZE and RESUM-n3 consume.
- **X.3 (termination a.e. + N-stability restated).** μ(non-terminating) = 0; every
  terminating f decided at its finite threshold; the stratum series per σ sums the
  full type density (3.2 + 3.3 + Thm 2.1, restated in MOVES vocabulary — one cite
  point for [3]/[4]).

**Kernels:** X.1a (the per-species index TABLE — the exact "what counts as an event"
subtlety that produced the (P1) convention hunt), X.1b STALL (OPEN: the WEIGHT-CHARGE
lemma + STALL-probe), and X.2 PROGRESS (the threshold-vs-exponent coercivity).

**Sealed gate EXHAUST-n3 (exhaustive where the claim is pointwise).** Seal: (i) on the
EXHAUSTIVE level-8 box at p = 2 (2^24) and level-5 at p = 3 (3^15): every f still
descending at genuine-event depth d has v_p(disc f) ≥ 2d — 0 violations tolerated;
(i′) per exercised species, the minimum observed v_p(disc) jump vs the X.1a index
table's prediction (REV 3, pass-2 concern 5 — the table is gated, not just named);
(ii) STALL census: the maximum observed zero-gain run vs the sealed budget — one
overrun kills X.1b; (iii) the (3b) constant at D = 2…8 vs exact counts; (iv) X.2's
env(N) at N = 4…8 vs measured undecided mass, both primes, exhaustive. A violation in
(i)/(ii) is adjudicated against the dictionary X.1a/X.1b, not patched.

## 6. NOTE [4] SQUEEZE — the two-sided general-n bound, and THEOREM U (REV 4: SQ.0 DECIDED-BUDGET; ESCAPE-conditional domination)

**The n = 2 pattern to generalize (W6):** (U) decided_σ(N) ≤ (value)·p^{2N} via the
fixpoint inequality `msW_eighth_le`, plus decided_σ(N) ≥ (value − env(N))·p^{2N} via the
box partition. REV 4 changes: SQ.1's finiteness cites the NEW SQ.0 DECIDED-BUDGET
lemma (the rev-2 STALL citation and rev-3's box-level disc bound are both retired);
SQ.2's induction runs over (e, τ) blocks with [2r] supplying every base-changed
hypothesis and ESCAPE supplying Neumann convergence.

- **SQ.0 (DECIDED-BUDGET — NEW LEMMA at REV 4; pass-3 obstruction 6: Lemma 3.3 is a
  MEASURE bound and implies NO pointwise discriminant bound on a level-N box —
  residue boxes contain discriminant-zero polynomials and lifts of arbitrarily high
  valuation; the rev-3 citation is STRUCK).** If f's canonical history has decision
  threshold ≤ N, then — proved from DECISION STABILITY (Thm 2.1 / X.2 PROGRESS
  mechanics), never from the tail: (a) every height ≤ h*(N) (each move constrains
  levels ≥ an affine function of its heights, and all constrained levels are ≤ N);
  (b) every key weight ≤ w*(N) (a key's weight is a consumed side value, bounded by
  the height budget); (c) #zero-gain nodes ≤ n!·w*(N) (D.10: each zero-gain
  recentering STRICTLY increases key weight; weights are quantized in (1/n!)·ℤ — a
  flagged derivation sub-claim); (d) the ledger exponent A(H) ≤ nN and every
  genuine-index node has POSITIVE ledger increment (flagged sub-claim), so
  #genuine nodes ≤ nN. Hence histories with threshold ≤ N form a FINITE family with
  an explicit bound T(n, N) — X.1b appears NOWHERE in this lemma.
- **SQ.1 (budgeted covering — finiteness re-cited at REV 4).** Every f in the
  level-N box is in exactly one of: (a) the stratum of one complete realizable
  canonical history with threshold ≤ N, or (b) Undec(N). PARTITION (not mere
  covering): D4R.0, with the prefix/complete distinction per §2. FINITENESS of the
  family in (a): SQ.0 ALONE — the rev-3 conjunction (box-level disc bound + X.1b
  stall cap) is retired, and SQ.1's CONDITIONAL-ON-X.1b tag is REMOVED. Then strong
  induction on the remaining degree budget, per the decomposition note 3.4′(a).
- **SQ.2 (the fixpoint upper bound — the (U) analogue).** For every N and σ:
  decided_σ(N) ≤ R_σ(p)·p^{nN}. *Route (REV 2):* the depth/height partial sums of
  RS.1's positive series are ≤ the full sum; the full sum = the block solve; the
  solution dominates every partial sum by MATRIX monotone iteration — RS.PRE's
  normalized K_e ≥ 0, Neumann convergence via the ESCAPE kernel at q = p (REV 4;
  CONDITIONAL-ON-ESCAPE until it closes) — inducted in cluster size
  e, with ALL base-changed legs β_m(p^δ) supplied as [2r] REL.3 statements over O_δ
  (pass-1 obstruction 6: the induction hypothesis is now a certified input, not a
  formal substitution). Needs R_σ(p) ≥ 0 and block positivity (RS.3), stated
  explicitly, not just formal solvability.
- **SQ.3 (the lower bound).** decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN}: box partition
  p^{nN} = Σ_τ decided_τ(N) + undec(N), apply SQ.2 to every τ ≠ σ, RS.4's checksum,
  and X.2's envelope.
- **SQ.4 = THEOREM U (conditional qualifier INLINE at REV 4, pass-3 concern 5).**
  ρ_σ := lim decided_σ(N)/p^{nN} exists and equals R_σ(p) for every p; R_σ ∈ ℚ(q) is
  the p-independent solution of (R_e); Σ_σ R_σ = 1. Assembled from SQ.2 + SQ.3 +
  X.2 — hence CONDITIONAL on ESCAPE and on X.1b (via X.2's env constants) and on
  K_e's three RS.PRE inputs until each closes; the capstone statement and its
  acceptance record carry these tags verbatim (§7's acceptance-record rule). State
  with the honest normalization sentence (monic-box density; projective/palindromy
  OUT OF SCOPE per the standing directive).

**Kernels:** SQ.2's block-matrix domination induction — the well-founded order is
(cluster size e; within e, the Neumann iteration index), base-changed hypotheses
entering ONLY at strictly smaller e and ONLY through REL.3; the derivation must
display the order and check that no (e, τ) leg feeds back at equal e outside M_e —
the one place a circularity could hide.

**Sealed gate SQUEEZE-n3 (feasible-exhaustive; pass-1 obstruction 8).** Seal, for all
five σ: p = 2 at N = 4, 6, 8 (2^12, 2^18, 2^24 — exhaustive) and p = 3 at N = 4, 5
(3^12, 3^15 — exhaustive; rev 1's p = 3, N = 8 = 3^24 DROPPED as infeasible, and
"stratified-exact" DROPPED as unspecified + circular — it risked testing the stratum
formulas against themselves): the exact integers ⌈(R_σ(p) − env(N))·p^{3N}⌉ ≤
decided_σ(N) ≤ ⌊R_σ(p)·p^{3N}⌋, with decided_σ(N) counted by exhaustive enumeration
under the PARI oracle (never the stratum formulas — independence requirement). Upper
bound EXACT — any single-f overshoot falsifies SQ.2. Plus the checksum row at each N.

## 7. Verification protocol (the dual standard, now in force)

Per note, in order; no step may be skipped, no note trusted early:
1. **Draft** in the MOVES ledger style (self-contained displays, explicit scope
   clauses, evidence perimeter section). Kernels get FRESH-CONTEXT derivations first
   (separate C10B/C15-style notes, `<KERNEL>_DERIVATION_<date>.md`), then transfer.
2. **Dual adversarial verification — BOTH verifiers, every pass:** (a) Codex
   (`codex exec`, fresh context, quote-and-classify: critical error vs justification
   gap, fix nothing); (b) a fresh-Fable verifier subagent under the identical charge.
   The two reports are adjudicated jointly; disagreement between verifiers is itself
   a finding to resolve, not average away.
3. **Acceptance = two consecutive CLEAN passes from BOTH verifiers on identical text**
   (the §B2-DEF/§C standard). Pass records appended verbatim to the ledger.
4. **Sealed gates BEFORE trust:** the note's gate predictions are written and committed
   (numbers, exact counts, tolerance provenance) BEFORE the census code runs — the
   Case-K discipline: a FAIL is adjudicated on record (prediction-derivation error vs
   theory error), then RE-SEALED fresh; never silently re-run. One gate (or pair) per
   new formula layer — the REV 3 roster below (§§2–6). DISCRIMINATION RULE (REV 2, pass-1
   obstruction 8): wherever the gated claim is exact, the gate is exact — exhaustive
   enumeration or exact F_q counts, with the PARI oracle as the independent
   ground truth; sampled censuses appear only as labeled consistency layers and never
   constitute acceptance evidence. GATE-EPISTEMICS (REV 3, pass-2 concern 7): gates
   REFUTE or SUPPORT, never prove — an exact census refutes CONCLUSIVELY exactly
   where a displayed degree/growth bound applies (the §2v (†) rule); elsewhere it
   refutes only the sealed formula. Every seal document carries a
   WHAT-THIS-GATE-CANNOT-SEE line (e.g. RESUM-n3's depth rows use the extractor under
   test — consistency-class; REL-n4 is oracle-independent at the decision level only;
   MENU-n3/EXHAUST-n3 exercise n = 3 species only). AGGREGATE-CENSUS clause (REV 4,
   pass-3 obstruction 5): any census of an aggregate quantity must satisfy §2v
   (†-AGG) — finite listed sum, displayed monomial normalization, displayed degree
   bound; completed densities are gated ONLY by two-sided SQUEEZE brackets. Gate
   roster at REV 4: D4-n3, VALUE-Fq (24 q-points, + the JREF joint layer) + VALUE-p
   (+ JOINT-probe), MENU-n3 (two-sided parameter exactness), REL-n4, EXHAUST-n3
   (+ STALL-probe), STATE-probe-2 (blocks [2b] AND [3]) + ESCAPE-probe + RESUM-n3,
   SQUEEZE-n3. Gate scripts live in `verification/`, predictions in
   `verification/*_SEALED_PREDICTIONS_<date>.md`.
   ACCEPTANCE-RECORD RULE (REV 4, pass-3 concern 5): every acceptance record names
   its note's open conditions INLINE — RS.4, [3], [4], and the capstone may not be
   recorded unconditional while ESCAPE, WEIGHT-CHARGE (X.1b), or any RS.PRE input
   (M4a-X, D4R.0, M2(ii)) is open; a record lacking its tags is a protocol
   violation, not an oversight.
5. **Update `docs/PROJECT_STATE.md` + the MOVES ledger** at every acceptance
   (update-then-act); axiom changes (none planned — X.1 cites the already-pinned GMN
   material) would additionally require the semantic-guardian triple test.
6. Check `codex-limits` before each heavy verification round; adversarial verification
   is the LAST Codex use to cut.

## 8. Honest risk register (REV 3 — updated per the pass-2 review + both probe reports)

**Recorded NON-failures (the review's own closing findings — keep off the worry
list):** the base-change substitution q ↦ q^δ does not threaten rationality (the
missing piece was the MEASURE statement, now note [2r]); unbounded deep residual
degrees are NOT the MENU obstruction (M1's corrected degree identity bounds cumulative
residue degree by n). Also surviving intact: D4R.2's pool bound (3i) and the entire §0
certified perimeter.

- **R1 — the linked value count is not universal in q (the theorem-killer; POTENTIAL
  STRUCTURAL WALL). PROBE REPORTED 2026-07-26: NO-WALL at the probed families.** The
  exposure is [1v] Theorem VAL (torus lemma dead, counterexample on record in §2).
  WALL RULE (REV 4 — refute-or-support per §2v (†)/(†-AGG); the rev-3 σ-aggregate
  clause was NOT justified — pass-3 obstruction 5: a completed density has geometric
  denominators and no finite A-shift restores integrality): (1) census a LOC/HIST
  count at m ≥ W+2 exact points (W = ITS displayed pool dimension, per §1s); (2) an
  exact mismatch with the degree-≤W interpolant, surviving adjudication,
  CONCLUSIVELY refutes universality of that count — the displayed growth bound plus
  integrality means finite data DOES decide the negative; at the aggregate level the
  same conclusive force attaches ONLY to (†-AGG)-admissible quantities — e.g. a
  wild-p mismatch of decided_σ(N) (integer, degree ≤ nN) against its degree-bounded
  tame interpolant is the WALL, demonstrated conclusively (the directive's
  obstruction); a COMPLETED-density discrepancy becomes a wall only via the
  two-sided SQUEEZE brackets excluding the candidate value, envelope in hand —
  quantitative, never interpolation; (3) an all-points match is SUPPORT at stated
  surplus, and acceptance still runs through the VAL.1/VAL.2J proofs. PROBE RESULT (exploration-class, 24 q-points,
  results/value_probe_output.txt): all 15 linked totals UNIVERSAL (surplus ≥ 15);
  σ-aggregates match the tame interpolant at p = 2 and p = 3 EXACTLY; twisted-cell
  fiber constancy exact everywhere; 32 fixed-frame series provably char-dependent —
  adopted as the ANCHOR-TWIST design constraint on VAL.2J/M2/M4b-T, NOT a wall. The
  SEALED VALUE-Fq/VALUE-p gates still run before [1v] is trusted (Case-K discipline).
- **R2 — the same-size recursion does not close in finitely many state types
  (POTENTIAL STRUCTURAL WALL). PROBE REPORTED 2026-07-26: probe-level NO-WALL; the
  gate is REOPENED.** Repair: RS.0 TYPE-CLOSURE (lumpability + bisimulation, §4) +
  M2 ([2b], now on the JOINT-REFINED τ). The first STATE-probe (exploration-class)
  found exact same-type law equality at the UNTYPED-VALUE-varying, vtx-RIGID n = 4
  configuration (REV 4 renaming, pass-3 concern 4: the rev-3 label "value-varying"
  invited overcitation — vtx was rigid; only an untyped retained value varied; the
  feasibility finding is on record in the script docstring) — negative evidence for
  the probed rows only; it does NOT establish RS.0 and did NOT exercise the
  vtx-stratum-varying regime rev 2 specified. WALL EXPERIMENT now = STATE-probe-2
  (§4: n = 6, p = 2, R₀ = ψ²·χ, conditioned cylinders ≤ 2^28 per state at N = 8,
  REQUIRED before [2b]'s OR [3]'s acceptance — REV 4 scope): a same-TYPE mismatch
  surviving adjudication AND one 𝒯-refinement round via [1v]'s JREF strata = the
  wall — a genuinely new resummation idea required; no fallback inside this
  architecture. (Same-SHAPE different-TYPE differences are expected and carried by
  the block system. A JREF-insufficiency finding — joint law varying within one τ —
  is the SAME wall channel: one refinement round, then wall.)
- **R3 — menu completeness failure (M5).** A realized history species outside the
  retained vocabulary. DEMONSTRATED BY: a stray shape or a PARI-oracle mismatch in the
  exhaustive MENU-n3 census. REV 2 honesty (pass-1 obstruction 8): gates cannot
  certify ABSENCE — exhaustive enumeration certifies fixed (p, N) only, and the oracle
  closes shared blindness at the decision level only; M5 is accepted on PROOF, gates
  are falsifiers. The n = 4 / depth-3 escalation clause stands (D.12 level-3 gate,
  promoted from optional, if M5's species-coverage argument resists).
- **R4 — the stall budget fails (X.1b). WIDENED at REV 3: X.1b is an OPEN kernel
  (WEIGHT-CHARGE), so this wall is LIVE until the lemma is derived or refuted.** If
  zero-index recenterings can repeat unboundedly between genuine events, the ENVELOPE
  design breaks (REV 4 precision, pass-3 concern 6: the TERMINATION consequence is
  not automatic — a.e. termination tolerates unbounded finite chains; adjudicate
  against L5fix's exact quantifiers, §5). DEMONSTRATED BY: a STALL-probe (§5) per-f
  ratio violation of every candidate s(n), an EXHAUST-n3(ii) stall-census overrun, or
  the X.1b derivation finding a legal unbounded improvement chain against the L5fix
  Invariant-2 budget. CONSUMERS NARROWED at REV 4: only X.2's env constants (hence
  SQ.3 and the envelope gate layers) carry the CONDITIONAL-ON-X.1b tag — RS.1, RS.3,
  SQ.1 discharged (§4/§6); no acceptance of [3]/[4] hides the condition.
- **R9 — ESCAPE fails (NEW at REV 4; pass-3 obstruction 3 made the spectral gap an
  UNSUPPORTED claim, not a consequence of WEIGHT-CHARGE).** If no uniform (B(n),
  c(n)) exists — some type family retains still-in-block mass → 1 — then Neumann
  inversion and SQ.2's domination both fail; RESUM's solvability is unfounded even
  with all counts polynomial. DEMONSTRATED BY: the ESCAPE-probe (§4) measuring a
  type with B-step exit mass 0 at every loop position for every candidate constant,
  or the (E1)/(E2) derivations both failing with a witness family. FALLBACK: route
  (E2)'s drift/renewal argument tolerates unbounded zero-gain runs; if BOTH routes
  fail with witnesses, that is a structural wall of the block architecture —
  recorded, not patched.
- **R5 — fixpoint domination circularity (SQ.2).** As rev 1, sharpened: the induction
  order is now explicit ((e, τ) blocks, Neumann index within e; base-changed legs only
  via REL.3), and the kernel must check no equal-e feedback outside M_e. DEMONSTRATED
  BY: no well-founded order found, or a SQUEEZE-n3 upper-bound overshoot by even one f.
  FALLBACK: the finite-window version (window-K partial systems, monotone in K — the
  W3→W6 route) at the cost of a longer note.
- **R6 — silent scope debt from accepted inputs.** §C covers recenterings at
  e_read = 1 and any-(e, h, g, μ, a) increments; tower levels ≥ 3 rest on proofs alone
  (D.12). REV 2 ADDITION: [2r] REL.1 re-scopes accepted text to a NEW BASE — a silent
  q = p usage could hide there (TYP(a)'s per-digit 𝔽_p-linearity walked first; REL.1
  gets its own verification passes, never "by inspection"). MITIGATION unchanged:
  gates' shape logs RECORD which species/levels were exercised; unexercised menu rows
  are listed as proofs-only (the D.12 convention).
- **R7 — normalization mismatch at the finish.** Theorem U is a MONIC-box density;
  the paper's headline is weight-normalized projective with palindromy — OUT OF SCOPE
  by the standing directive (2026-07-22). The capstone must state this boundary
  explicitly to avoid a false "full theorem" claim in PROJECT_STATE.
- **R8 — aggregate-cancellation mirage (REV 3: VAL.3 reclassified as a REDESIGN).**
  If VAL.3 is entered (a proved per-shape non-polynomiality per (†) AND a proved
  aggregate cancellation), RESUM's per-(shape, type) basis is DEAD, not patchable:
  new aggregate-block unknowns, a new transition law, closure theorem and solvability
  argument — a new DAG node [3′] replacing [3], budgeted 3+ units with full
  verification rounds; never a silent patch. Probe status: the trigger is unexercised
  (all probed linked totals universal); the branch stays specified, unbudgeted.

## 9. Effort map (REV 3 — for scheduling, not for skipping)

[1] D4-R: 1 unit (restatement + the PARTITION kernel with three named obligations;
DRAFT-CLEARED first, §1). [2a] SPECIES: 1 unit (M1 + M5). [1v] VALUE: 3 units (VAL.1
+ the JREF burdens J1–J3 + the widened 24-point gates + JOINT-probe). [2b] STATE-GEOM:
2.5 units (M2 joint-refined lumpability + M4a + M4a-X + M4b-T equivariance;
acceptance behind STATE-probe-2). [2r] REL: 1.5–2 units (the re-scoping pass + the
four REL.2 obligations + one gate). [5] EXHAUST: 2 units (three kernels; X.1b is
OPEN — WEIGHT-CHARGE may resist). [3] RESUM: 4–5 units (RS.PRE/RS.0/RS.1 + ESCAPE
kernels + STATE-probe-2 + ESCAPE-probe + RESUM-n3). [4] SQUEEZE: 2 units (incl.
SQ.0's flagged sub-claims). Verification multiplies each by the usual ~2× (the §C
precedent: 13 passes). Gates are cheap (CPU-only, exhaustive boxes ≤ 2^28 conditioned
/ 2^24 full / 3^15–3^18; `verification/` patterns exist); seal discipline is the
cost. REV 3 status: both wall probes have REPORTED (R1 NO-WALL exploration-class; R2
probe-level NO-WALL with the vtx-varying regime still untested) — the two decisive
experiments cost 17 s and 145 s of wall time; STATE-probe-2 and the STALL-probe are
the remaining front-loaded cheap discriminators.

---

## REV 2 RECORD (2026-07-26) — response to the pass-1 structural review

*(ASSEMBLY_PLAN_PASS1_2026-07-26.md: 8 critical obstructions, 7 concerns, verdict
UNSOUND. Every finding responded to in place above; dispositions tabulated here.
C = critical obstruction, K = concern.)*

| Finding | Verdict on rev 1 | REV 2 disposition |
|---|---|---|
| C1 torus lemma false for extension-valued vtx (z^aψ^μ(Az+B): fibers 1 vs 0) | lemma DEAD | D4R.3 RETIRED, counterexample on record (§2); role rebuilt as NEW NOTE [1v] VALUE (VAL.1 stratified fiber calculus + VAL.2 vtx-distribution + VAL.3 aggregate fallback), promoted to kernel pair with exact F_q + p-adic gates; R1 rewritten as potential wall with its decisive experiment |
| C2 lift quotient is no aggregation license | definition WRONG | Hist(P̂) REDEFINED via the canonical (S6b) policy — strata are fibers of the deterministic classifier, no quotient (§2); PARTITION promoted to kernel D4R.0; M3 demoted to a symmetry remark (§3) |
| C3 product-of-cones ignores arithmetic realizability | claim overreached | M4 SPLIT: M4a = NECESSARY cone + congruence-lattice geometry only; the arithmetic layer ((NA)/(HV), irreducibility, endpoints, collisions) routed to per-point counts C_{S,τ} from [1v] (M4b); the MENU theorem statement disclaims lattice-point exhaustiveness (§3) |
| C4 RS.2 not derivable from Thm C + Claim 4.3 | bridge missing | RS.2 now EXPLICITLY rests on [1v] Theorem VAL (or VAL.3) — stated as a dependency, not a consequence (§4) |
| C5 triangular closure unproved (assumed R2's negation) | assertion, not theorem | System REDESIGNED block-triangular over (cluster size e, state type τ); closure = RS.0 TYPE-CLOSURE, a promoted kernel gated by STATE-probe; MENU M2 promoted to supply the finite type list (§§3, 4) |
| C6 base change lacks the measure statement | hypothesis outside perimeter | NEW NOTE [2r] REL: Theorem C over unramified O (REL.1, derivation-grade re-scoping pass), sub-cluster identification (REL.2), domination transfer (REL.3); gate REL-n4; SQ.2 cites REL.3 (§§3r, 6). Recorded: the ALGEBRA of q ↦ q^δ was never the problem |
| C7 EXHAUST node-count premise false (zero-index recenterings) | X.1 self-contradictory | X.1 WITHDRAWN and split: X.1a genuine-event dictionary (v_p(disc) ≥ 2·d_gen, sound) + X.1b STALL budget kernel (affine v_p(disc) ≥ c₁d_total − c₂, honest constants); envelope rescaled; stall census added to the gate (§5) |
| C8 gates cannot discriminate R1/R2/R3 | gate suite inadequate | DISCRIMINATION RULE (§7): exact claims get exact gates. Exhaustive enumeration replaces sampling in every discriminating layer (D4-n3, MENU-n3, EXHAUST-n3, RESUM-n3, SQUEEZE-n3); VALUE gates at n = 5 and over F_q incl. prime powers (n = 3 cannot express μ ≥ 2 at a deg-2 key); STATE-probe added for R2; PARI-oracle independence required; p = 3 N = 8 exhaustive and "stratified-exact" DROPPED; sampled layers labeled consistency-only |
| K1 "w ≤ n!" sloppy; residual degrees not the failure | recorded | M1 corrected: displayed identity D_{r+1} = e_r·g_r·D_r ⟹ cumulative residue degree ≤ n; logged as NON-failure in §8's preamble (§3) |
| K2 L5fix finiteness ≠ MOVES-quotient finiteness | map missing | M2 promoted to STATE kernel: explicit per-species map from every degree-preserving move to a bounded type invariant (§3) |
| K3 disjointness not supplied by Theorem C | argued at wrong coordinates | Supplied by D4R.0 (fibers of a function), with the common-frame derivation obligation named — never across transported coordinates (§2) |
| K4 no uniform threshold over the fiber | quotient-dependent | D4R.4 restated on the canonical, unquotiented, finite Hist(P̂) (§2) |
| K5 scalar pivot too weak for a coupled system | insufficient | RS.3 redesigned: LEAK lemma ⟹ substochastic M_e with every state leaking ⟹ ρ < 1 at every q = p, Neumann inversion, det ≠ 0 in ℚ(q) (§4) |
| K6 X.2 coercivity not displayed | assumed | PROGRESS kernel added: the threshold-vs-exponent balance displayed with named d*/h* split; env(N) constants traced (§5) |
| K7 zero-cost infinite refinement silently excluded in SQ.1 | silent requirement | Named citation: SQ.1's finiteness now runs through X.1b's STALL budget (§6) |

**Survivals recorded (per the review's own closing paragraph):** base-change
substitutions and unbounded deep residual degrees are NOT the failures; D4R.2's pool
bound (3i), the §0 certified perimeter, the five-note skeleton's outer squeeze logic,
and the n = 2 precedent all stand.

**DAG change:** 5 notes → 7 ([1v] VALUE and [2r] REL added). Execution order:
[1] → { [1v] ∥ [2] ∥ [5] } → [2r] → [3] → [4], with [1v] and STATE-probe front-loaded
onto the two potential structural walls (R1, R2) so the decisive experiments report
before RESUM/SQUEEZE effort is spent. *(Superseded at REV 3 — see below.)*

---

## REV 3 RECORD (2026-07-26) — response to the pass-2 structural review + both wall probes

*(ASSEMBLY_PLAN_PASS2_2026-07-26.md: 7 critical obstructions, 8 concerns, verdict
UNSOUND. Probes: value_probe.py (R1) and state_probe.py (R2), both exploration-class,
reported 2026-07-26, results in verification/results/. C = critical, K = concern.)*

| Finding | Verdict on rev 2 | REV 3 disposition |
|---|---|---|
| C1 VAL.1's worked stratification false; joint calculus missing | example WRONG; scalar VAL.2 insufficient | VAL.1 example corrected to the three-cell FG/FL/FS partition with fibers 1/0/0; VAL.2 upgraded to VAL.2J — the JOINT hinge/collision law on products of ANCHOR-TWISTED cells (probe: twisted cells exactly fiber-constant at all 24 q; fixed-frame provably char-dependent — the twist adopted as a design constraint) (§2v) |
| C2 VAL.3 undefined as fallback; R1 wall rule logically impossible | fallback vacuous; rule impossible | VAL.3 reclassified as a REDESIGN branch ([3′], 3+ units, entered only on proved non-polynomiality + proved cancellation); R1 rule rebuilt refute-or-support on the displayed (†) degree bound: C_S ≤ q^{W(S)} + integrality ⟹ any ℚ(q) fit IS the deg-≤W(S) interpolant ⟹ one surplus-point mismatch is a CONCLUSIVE refutation; support is never proof. VALUE-Fq widened to 24 q-points — the rev-2 nine-point list had surplus ZERO against degree-8 series (§2v, §7, §8 R1/R8) |
| C3 DAG cyclic ([1v]⇄[2]); [2]→[5] edge missing | graph unsound | [2] SPLIT: [2a] SPECIES (raw catalogue — feeds [1v]) and [2b] STATE-GEOM (consumes [1v]); full acyclic edge list displayed incl. [2a]→[5] and [2b]→[5]; execution order rebuilt [1]→[2a]→[1v]→[2b]→{[2r]∥[5]}→[3]→[4] (§1, §3) |
| C4 M2's τ not shown to carry M4b/RS.0's needs; position inconsistency | label closure ≠ lumpability | M2 rewritten: τ = (residual factor configuration over twisted cells, anchor, phase); POSITION excluded by decision, its irrelevance = RS.0(β)'s theorem; M2(ii) restated as LUMPABILITY of full outgoing JOINT laws, route = Thm C freshness + VAL.2J (§3, §4) |
| C5 probe ≠ rev-2 spec; gate spec internally inconsistent | gate not satisfied | Probe recorded as probe-level evidence ONLY (vtx RIGID below n = 6 — feasibility finding); STATE gate REOPENED; spec inconsistency fixed (vtx-stratum ∈ τ ⟹ pass = same-type equality + sealed per-τ rows, cross-type differences expected); STATE-probe-2 specified — n = 6, p = 2, R₀ = ψ²·χ, conditioned cylinders ≤ 2^28/state at N = 8, ≥ 2 twisted cells × ≥ 2 loop positions — and made BLOCKING for [3]'s acceptance (§4, §8 R2) |
| C6 STALL premise does not imply the affine bound | implication missing | X.1b DEMOTED to OPEN kernel; the missing lemma NAMED — WEIGHT-CHARGE: #zero-gain ≤ s(n)·v_p(disc f) via the different budget; the two-step reduction displayed (with X.1a: v_p(disc) ≥ d_total/(s(n)+1/2)); STALL-probe added (2^24 cubic + 2^26 quartic boxes); ALL consumers tagged CONDITIONAL-ON-X.1b (§5, §6, §8 R4) |
| C7 matrix normalization undefined; one-step leak possibly false | K_e untied to masses | RS.PRE added: K_e := conditional masses of DISJOINT one-move continuations — substochastic BY CONSTRUCTION (height resummation = countable additivity); q^{−e(e−1)/2}M_e := K_e is notation; LEAK weakened to B(n)-step row-sum decay (forced-recentering states allowed to not leak in one step); RS.3/SQ.2 run on K_e (§4, §6) |
| K1 D4R.0 is the entire burden | acknowledged | Kernel charge now lists the three named obligations: totality of the canonical choice, terminal exhaustiveness, common-frame identity (§2) |
| K2 "Z = ∅" ambiguous terminal notation | dangerous | Z = ⊤ (tautological terminal system, vol 1 — not the empty locus) fixed throughout §2 |
| K3 M4b stronger than the repair table admits | new arithmetic theorem unnamed | M4b-T TRANSLATION lemma named as the burden: the anchor monomial is the only position-dependent factor; twisted cells make per-cell counts translation-invariant. Probe's a_eff ∈ {0,1,2} twisted exactness = its evidence; the fixed-frame char-splits = its negation exhibit (§3) |
| K4 REL.2 not a consequence of REL.1; REL-n4 shares normalization | burden unnamed; gate loophole | REL.2's four obligations named (coordinates, Jacobian, sibling independence, lift-policy compatibility); REL-n4 side (i) rebuilt MOVES-free at the decision level (root-read congruences + PARI oracle); residual history-level blindness recorded as REL.2's proof burden (§3r) |
| K5 X.1a's "all increments genuine" unjustified by naming GMN | convention risk | Per-species INDEX TABLE duty: evaluated GMN index formula per species under (P1), endpoint/zero-contribution cases ruled explicitly; EXHAUST-n3 gains the per-species jump check (i′) (§5) |
| K6 SQ.1 cites too little for finite truncation | single citation | Finiteness = displayed conjunction: X.2 height bound h*(N) + box-level disc bound capping d_gen + X.1b stall cap (conditional tag) (§6) |
| K7 gates overstated at the claimed layer | risk-register drift | GATE-EPISTEMICS standing clause in §7 (gates refute or support, never prove; conclusive refutation only under a displayed degree/growth bound; per-seal WHAT-THIS-GATE-CANNOT-SEE line); RESUM-n3 depth rows reclassified consistency-only; REL-n4 fixed per K4 (§4, §7) |
| K8 cross-height check narrower than RS.0 | extrapolation risk | RS.0(β) restated as the height-shift BISIMULATION theorem (proof, not extrapolation); the probe row cited as one-comparison evidence only; STATE-probe-2 includes loop-position variants (§4) |

**Probe incorporation (both exploration-class, 2026-07-26 — neither is acceptance
evidence; sealed gates still run).** VALUE probe (145 s): NO-WALL — 15/15 linked
totals UNIVERSAL on 24 exact q-points (surplus ≥ 15 per (†)); σ-aggregates match the
degree-bounded tame interpolant at p = 2, 3 EXACTLY; fiber constancy exact on
anchor-twisted cells at every q and a_eff; 32 fixed-frame series char-dependent —
adopted as the ANCHOR-TWIST constraint on VAL.2J/M2/M4b-T. STATE probe (17 s):
probe-level NO-WALL at the value-varying n = 4 rows (11 states, exact uniform words,
one exact cross-height match); vtx RIGID below n = 6, so the rev-2 spec was not
exercised — gate reopened as STATE-probe-2.

**Wall status after REV 3:** R1 — open; probe-level NO-WALL; sealed VALUE-Fq/VALUE-p
still to run; the wall rule is now logically executable (refute-or-support under (†)).
R2 — open; probe-level NO-WALL in the value-varying regime; the vtx-VARYING regime is
untested pending STATE-probe-2 (blocking for [3]). R4 — WIDENED: X.1b is an open
kernel (WEIGHT-CHARGE), so the stall wall is live until derived or probe-refuted.
No wall has been demonstrated; none has been closed.

**DAG change at REV 3:** 7 notes → 8 ([2] split into [2a] SPECIES / [2b] STATE-GEOM);
the graph is now acyclic with the [2a]→[5] and [2b]→[5] edges explicit; [3] RESUM's
acceptance is gated on STATE-probe-2; X.1b and its consumers carry an explicit
conditional tag until WEIGHT-CHARGE closes.

---

## REV 4 RECORD (2026-07-26) — response to the pass-3 structural review

*(ASSEMBLY_PLAN_PASS3_2026-07-26.md: 7 critical obstructions, 6 concerns, verdict
UNSOUND; plus 7 re-judgments of the rev-3 dispositions, of which #1, #2, #4, #5, #6,
#7 were judged incomplete/partial and are REDONE here. C = critical, K = concern,
D = pass-2-disposition re-judgment.)*

**The four demanded structural builds (the pass's closing list, all delivered):**
1. **JOINT-REFINED STATE** — JREF defined ONCE in [1v] (§2v: per-coordinate twisted
   cells + the finite relational strata read off the species' displayed maps;
   burdens J1 finiteness/p-independence, J2 polynomial counts, J3 sufficiency);
   M2's τ = (JREF cell, anchor, phase) is the plan's SINGLE state object, consumed
   as-is by MENU/RESUM/SQUEEZE — no law conditions on anything finer or coarser.
2. **LOC/HIST/FAM separation** — new §1s: local species (fixed W_loc, Theorem VAL's
   home), unrolled histories (parameter-dependent W(H) = Σ W_loc), resummed families
   (ℚ(q), never (†)-censusable); maps `unroll`/`resum` displayed; binding notation
   rule; Theorem VAL restated as (a) LOCAL + (b) CHAIN.
3. **UNIFORM ESCAPE** — RS.3's WEIGHT-CHARGE→B(n) route STRUCK (C3's refutation
   recorded verbatim); new OPEN kernel ESCAPE (uniform (B(n), c(n)) row-sum decay of
   K_e(p)^B) with routes (E1) reachable-exit and (E2) drift/renewal, plus the
   ESCAPE-probe; new risk R9.
4. **CORRECTED AGGREGATE CENSUS** — (†) restricted to LOC/HIST integer counts;
   rev-3's σ-aggregate clause STRUCK; new (†-AGG) protocol (finite listed sum +
   displayed monomial normalization + displayed degree bound; canonical instance
   decided_σ(N), degree ≤ nN); completed densities tested only by two-sided SQUEEZE
   brackets; §7 AGGREGATE-CENSUS clause; R1(3) rebuilt.

| Finding | Verdict on rev 3 | REV 4 disposition |
|---|---|---|
| C1 cones used as exact summation domains | RS.1 overcounts | NEW OPEN kernel M4a-X EXACT-DOMAIN (§3): Route A semilinear-via-zero-extension (M4b-T bijection at EVERY cone point, zero pattern translation-invariant) or Route B finite exact admissibility classes; RS.1 re-sketched to sum M4a-X classes only; MENU-n3 clause (iii) upgraded to TWO-SIDED parameter exactness (orphans and strays both zero) |
| C2 M2 omits the joint refinement (= D1/D4 redone) | state can't prove its theorem | JREF built in [1v] with burdens J1–J3; τ redefined as the JREF cell (+ anchor, phase); M2(ii)'s route now consumes VAL.2J-on-JREF (J3); JOINT-probe added (k = 2 linked children + collision, exact F_q) |
| C3 WEIGHT-CHARGE cannot yield uniform B(n) leakage (= D6 redone) | RS.3 unfounded | The route is STRUCK on record; ESCAPE kernel + ESCAPE-probe installed (§4); RS.3 and SQ.2 cite ESCAPE, CONDITIONAL-ON-ESCAPE until closed; X.1b's consumers narrowed to X.2's env constants (RS.1 discharged by Tonelli, SQ.1 by SQ.0) |
| C4 species/histories/families conflated under C_S | three objects, one notation | §1s three-object separation with displayed maps + binding notation rule; Theorem VAL restated LOCAL + CHAIN with per-history degree bounds (§2v) |
| C5 aggregate (†) unjustified (= D2 redone) | conclusive-wall overclaim | (†) scoped to LOC/HIST; (†-AGG) truncated-census protocol; R1(3) wall = (†-AGG)-admissible mismatch (e.g. decided_σ(N)) or two-sided bracket exclusion — never completed-density interpolation (§2v, §7, §8) |
| C6 SQ.1 used Lemma 3.3 as a pointwise box bound | citation invalid | Citation STRUCK; NEW lemma SQ.0 DECIDED-BUDGET from decision stability (heights ≤ h*(N); key weights ≤ w*(N); zero-gain ≤ n!·w*(N) via D.10 + quantization sub-claim; genuine ≤ nN via positive-increment sub-claim — both flagged); SQ.1 cites SQ.0 alone, its X.1b tag REMOVED (§6) |
| C7 STATE-probe-2 must gate [2b] (= D5 redone) | governance defect | Blocking scope widened: STATE-probe-2 must PASS before [2b] OR [3] is accepted — stated in §1, §3 (M2), §4 (the probe), §7 (roster), §8 R2 |
| K1 D4R.0 conflates history and prefix | definition gap | Prefix/complete distinction displayed in D4R.0: S(H,⊤) fiber for complete H, S(P,⊤) prefix-fiber; Theorem C applied to the prefix event; obligation (b) restated for completions (§2); [1]'s draft charge updated (§1) |
| K2 M4b-T "cell-preserving" imprecise | equivariance unstated | Precise statement: translation induces a bijection of stratifications a priori permuting labels by π_v; EQUIVARIANCE CLAUSE to prove π_v = id in the twisted frame, else RS.0/K_e re-index by π-orbits — RESUM may not silently assume π_v = id (§3) |
| K3 "only position-dependent factor" premised | motivation vs theorem | Reworded: it is M4b-T's TARGET CONCLUSION, proved by the normal-form audit, never premised (§3) |
| K4 R2 record misnames the probed regime | overcitation risk | Renamed UNTYPED-VALUE-varying, vtx-RIGID n = 4 configuration in §8 R2 (the rev-3 record table itself is history — correction noted here) |
| K5 conditional tags missing at checksums/capstone | acceptance drift | Inline tags added at RS.4 and SQ.4/Theorem U; §7 ACCEPTANCE-RECORD RULE: RS.4/[3]/[4]/capstone never recorded unconditional while ESCAPE, X.1b, or any RS.PRE input is open |
| K6 unbounded zero-gain chain ≠ automatic termination hole | overclaim | X.1b's clause reworded: it defeats the envelope/uniform-leak DESIGNS; the termination consequence is adjudicated against L5fix's exact quantifiers (§5); R4 wording aligned (§8) |

**Also at REV 4 (not demanded, forced by the repairs):** RS.PRE's "substochastic by
construction" made honestly conditional on its three named inputs (M4a-X, D4R.0,
M2(ii)) per pass-3 disposition 7; RS.1's convergence discharged unconditionally by
Tonelli (disjoint positive masses bounded by 1), removing one X.1b tag; [1] D4-R
recorded DRAFT-CLEARED first per the pass's readiness note.

**Open kernels after REV 4 (each with its deciding probe/gate):** D4R.0 (gate D4-n3);
JREF J1–J3 + VAL.1/VAL.2J (VALUE-Fq + JREF layer, VALUE-p, JOINT-probe); M2 lumpability
(STATE-probe-2 — blocks [2b] AND [3]); M4a-X EXACT-DOMAIN (MENU-n3 two-sided (iii));
M4b-T + equivariance (VALUE-Fq twisted layers; MENU-n3); REL.1/REL.2 (REL-n4); X.1a
(EXHAUST-n3 (i)/(i′)); X.1b WEIGHT-CHARGE — OPEN (STALL-probe, EXHAUST-n3 (ii));
ESCAPE — OPEN (ESCAPE-probe; RESUM-n3); RS.0 (STATE-probe-2 + RESUM-n3); SQ.0's two
flagged sub-claims (weight quantization; positive genuine-increment) — derivation
duties inside [4]; SQ.2's no-equal-e-feedback check (SQUEEZE-n3).

**Wall status after REV 4:** R1 open (probe-level NO-WALL; sealed gates pending; wall
rule now (†)/(†-AGG)-sound). R2 open (vtx-varying regime untested pending
STATE-probe-2, which now blocks [2b] too; JREF-insufficiency identified as the same
wall channel). R4 live (WEIGHT-CHARGE open; consumers narrowed to X.2). R9 NEW and
live (ESCAPE open; two named routes, probe specified). No wall demonstrated; none
closed.
