# ASSEMBLY_PLAN_2026-07-26 — the final campaign: from accepted §C to the complete wild-uniformity theorem (REV 3)

*Plan architect: Fable, 2026-07-26. REV 2, same day: rebuilt against the pass-1
structural review (ASSEMBLY_PLAN_PASS1_2026-07-26.md — 8 critical obstructions,
7 concerns, verdict UNSOUND); the finding→repair table is the REV 2 record near the end
of this file. REV 3, same day: revised against the pass-2 review
(ASSEMBLY_PLAN_PASS2_2026-07-26.md — 7 criticals, 8 concerns, verdict UNSOUND) and
BOTH wall probes' reports (value_probe: NO-WALL exploration-class, anchor-twist caveat;
state_probe: probe-level NO-WALL, vtx-rigidity feasibility finding — gate reopened);
the REV 3 record is the final table. Directive (Asvin, 2026-07-26): iterate on the math with
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
[2r] · decomp §3 → [5] · [1] → [2a] (canonical policy) · [2a] → [1v] (the catalogue
Theorem VAL quantifies over), [2b], [5] (X.1a's species dictionary) · [1v] → [2b]
(VAL.1 cells in M2's τ; VAL.2J in M4b), [3] (RS.2) · [2b] → [2r] (stratification
vocabulary), [5] (X.2's envelope constants ← M4a tails — the edge pass-2 found
missing), [3] · [2r] → [3], [4] · [5] → [3], [4] · [3] → [4].

- **[1] D4-R** — *the per-shape-prefix mass law* on the CANONICAL-POLICY history
  (strata are fibers, no quotient); the pool BOUND (3i) survives verbatim. (§2)
- **[2a] SPECIES** — *the raw shape catalogue*: M1's corrected degree bounds + M5
  completeness; NO strata, NO state types — exactly the finite list [1v] needs to
  quantify over, so no cycle. (§3)
- **[1v] VALUE** — *the linked value-count structure*: VAL.1 with the CORRECTED
  three-cell example, VAL.2J joint hinge law on ANCHOR-TWISTED cells, the (†) census
  epistemics; risk R1's decision point. PROBE REPORTED (2026-07-26): NO-WALL,
  exploration-class, anchor-twist caveat adopted. (§2v)
- **[2b] STATE-GEOM** — M2 STATE (a LUMPABILITY theorem, not label closure), M4a cone
  geometry, M4b per-point counts + M4b-T translation; supplies 𝒯_n to [3]. (§3)
- **[2r] REL** — *the relative ledger*: Theorem C over unramified O = W(F_{p^δ}) +
  the four-obligation sub-cluster base change — what β_m(q^δ) MEANS. (§3r)
- **[5] EXHAUST** — *the discriminant-tail tie-in*, two-track: X.1a genuine-event
  dictionary (per-species GMN index table) + X.1b STALL (an OPEN kernel at REV 3:
  WEIGHT-CHARGE + its own STALL-probe) + X.2 PROGRESS. (§5)
- **[3] RESUM** — *the depth resummation*: block system over (cluster size e, state
  type τ); RS.PRE defines the NORMALIZED kernel K_e (substochastic by construction);
  RS.0 TYPE-CLOSURE (lumpability + height-shift bisimulation); B-step LEAK
  solvability; p-uniformity from [1v]. ACCEPTANCE BLOCKED on STATE-probe-2 (§4).
- **[4] SQUEEZE** — *the two-sided finite-level bound*: decided_σ(N) ≤ R_σ(p)·p^{nN}
  and ≥ (R_σ(p) − env(N))·p^{nN}, hence ρ_σ = R_σ(p) — Theorem U; the domination
  induction over (e, τ) blocks with base-changed hypotheses from [2r]. (§6)

**Execution order:** [1] → [2a] → [1v] → [2b] → { [2r] ∥ [5] } → [3] → [4], with
X.1a/X.1b draftable right after [2a]. Both wall probes have ALREADY reported
(exploration-class, 2026-07-26; verification/results/): the VALUE probe (R1) NO-WALL
with the anchor-twist caveat; the STATE probe (R2) probe-level NO-WALL with the
vtx-rigidity feasibility finding — its sealed gate is REOPENED as STATE-probe-2 (§4),
which must PASS before [3] is accepted. The sealed gates still run (Case-K
discipline): probes are unsealed exploration, never acceptance evidence.

**Format per note (sections 2–6 below):** key definitions · load-bearing lemmas with
proof sketches · kernels (fresh-context derivation-grade, C10B/C15-style) · the sealed
gate that must PASS before the note may be trusted (§7 protocol). GATE DESIGN RULE
(REV 2, pass-1 obstruction 8): wherever the gated claim is exact, the gate is exact —
exhaustive finite-level enumeration or exact F_q counts; sampling survives only in
labeled consistency layers. And n = 3 alone is NOT enough: a cubic's deg-2 key cannot
carry μ ≥ 2, so the value-kernel gates run at n = 5 and directly over F_q.

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
  terminates); consequently S(H, ⊤) = {f : H_can(f) = H} — strata are FIBERS of a map,
  and disjointness is automatic. *Derivation obligations (REV 3, pass-2 concern 1 —
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

## 2v. NOTE [1v] VALUE — the linked value-count structure (REV 3: corrected cells, VAL.2J, the (†) rule; R1's decision point — PROBE REPORTED NO-WALL)

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

**The statement to prove.**
> **Theorem VAL (target form).** For each shape S ∈ 𝒮_n (the [2a] raw catalogue —
> the acyclic dependency, §1) there is ONE polynomial C_S ∈ ℚ[q] with C_S evaluated
> at the shape's pool sizes = the linked count, for every p — equivalently every
> prime power q at the finite-field layer. [REV 3, pass-2 obstruction 2: the rev-2
> "OR" clause (type-aggregated ℚ(q) values) is NOT a form that closes the stated
> RESUM — cancellation visible only after summing all shapes yields no local matrix
> M_e and no induction in e; it survives only as the VAL.3 REDESIGN branch below.]

**Route (two derivation-grade kernels + a REDESIGN branch).**
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
- **VAL.2J (JOINT hinge/collision law — upgraded from scalar at REV 3; pass-2
  obstruction 1's structural half).** For each node with its FULL tuple of linked
  data — every (HV) hinge value it supplies to adjacent children, every
  sibling-collision/distinctness condition among its residual factors — the JOINT
  distribution of that tuple over the parent's linked assignments is constant on
  products of ANCHOR-TWISTED VAL.1 cells (or an explicit common refinement). The
  scalar statement (one hinge, "the distribution of vtx(parent)") is the one-child
  special case; a node feeding k linked children needs the k-fold joint law — scalar
  marginals do NOT suffice when children are correlated through the parent. Then the
  linked count is the iterated pairing Σ_cells (parent joint count on the cell
  product)·∏(child fiber counts) — polynomial. This is where the note closes or hits
  R1: the matching must hold at EVERY hinge tuple of every shape, μ ≥ 2 and a > 0
  included. Probe evidence: the (fixed × twisted) joint matrix is exactly constant on
  twisted cells at every census q (exploration-class; ONE two-node family).
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

**The census epistemics (†) — what finite q-data can and cannot decide (REV 3;
pass-2 obstruction 2's impossibility repaired by a displayed degree bound).**
> **(†) Degree bound.** For every shape S, D4R.2's pool arithmetic gives
> 0 ≤ C_S(q) ≤ q^{W(S)} at every prime power q, with W(S) the displayed pool
> dimension. Consequence: if C_S agrees with ANY R ∈ ℚ(q) at all prime powers, then
> R is a POLYNOMIAL (a rational function integer-valued at infinitely many integer
> points has vanishing non-polynomial part) of degree ≤ W(S) (the growth bound at
> infinitely many points) — hence R is THE unique degree-≤W(S) interpolant through
> any W(S)+1 census points.
>
> **Decision rule (refute-or-support).** Census at m ≥ W(S)+2 exact points. REFUTE:
> one exact mismatch between the census and the degree-≤W(S) interpolant, surviving
> adjudication, CONCLUSIVELY refutes ℚ(q)-universality of C_S — by (†), finite data
> DOES decide the negative. SUPPORT: all m points match — universality is SUPPORTED
> at surplus m − W(S) − 1, never proved; acceptance still requires the VAL.1/VAL.2J
> derivation, with the census as its standing falsifier. The same rule governs
> σ-aggregates (clear the p^{−A} denominators to restore integrality; degree bound
> max_S W(S) + the A-shift) — so §8 R1(3)'s wild-p wall test is a CONCLUSIVE
> refuter, repairing rev 2's logically impossible "differs from every ℚ(q)
> interpolation" clause.

**Sealed gates (both EXACT — no sampling anywhere in this note).**
- **VALUE-Fq (q-list WIDENED at REV 3 — the rev-2 nine-point list against degree-8
  linked series had surplus ZERO: non-discriminating by (†)).** Direct exhaustive
  enumeration of linked counts over F_q for a sealed list of n ≤ 5 two-node
  configurations INCLUDING the pass-1 counterexample family (deg ψ = 2, μ = 2,
  a_eff ∈ {0, 1, 2}, lead factor (Az+B)) and the FAM-Q quadratic-cofactor stress
  family (genuinely non-constant fibers), at the 24-point list
  q ∈ {2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,49,53,59} — prime
  powers included deliberately. Seal: per-series W(S) AND the VAL.1/VAL.2J closed
  forms with exact values at every q. PASS = exact integer equality throughout, with
  surplus ≥ 3 per series per (†). STATUS: the exploration-class probe
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

## 3. NOTES [2a] SPECIES + [2b] STATE-GEOM — the rev-2 MENU, split acyclic (REV 3)

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
- **M2 (STATE — REWRITTEN at REV 3; pass-2 obstruction 4). Lives in [2b].** The LOOP
  STATE TYPE at a node is τ = (the residual factor CONFIGURATION — the multiset over
  residual factors of (degree, multiplicity, ANCHOR-TWISTED VAL.1 cell of its
  transported value), anchor a, tower phase). DECIDED (rev 2 was internally
  inconsistent about position): loop POSITION and heights are NOT in τ; their
  irrelevance is RS.0(β)'s THEOREM, never a definition. Prove: (i) τ ranges over a
  FINITE p-INDEPENDENT list 𝒯_n; (ii) LUMPABILITY, not label-closure (pass-2's
  distinction: "closure of labels is different from lumpability of transition
  counts") — any two CONCRETE states of one type have IDENTICAL full outgoing
  one-step laws: the JOINT law of (next node data, all hinge values, all
  collision/admissibility data), exhibited per move species, with the e_birth vs
  e_read threading re-walked once here (what "self-loop at fixed key data" is at
  order r ≥ 2). Route: Theorem C freshness (fresh digits uniform on the state
  cylinder — the mechanism the state probe verified exactly: every readable word
  cell 1024/729 on the nose) + VAL.2J twisted-cell constancy; (iii) proper
  refinements number ≤ n − 1 (L5fix Invariant 1 transported: each strictly refines
  the (e, f)-partition or strictly increases Σ eᵢfᵢ). Load-bearing TWICE: menu
  finiteness and the block-index set of RESUM's system (RS.0).
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
- **M4b (per-point counts factor through the type) + M4b-T (TRANSLATION — the new
  arithmetic theorem pass-2 concern 3 identified; NOT a corollary of a type map).**
  At every lattice point of M4a's set, the number of realizable value assignments is
  C_{S,τ}(q) — a function of shape and state type ONLY, not of the cone position.
  *Route:* M4b-T FIRST — a normal-form lemma comparing evaluation families at two
  lattice points: the vtx formula's only position-dependent factor is the anchor
  monomial z̄^{a−μm̂} (C.0's display), so translation by a lattice vector twists the
  target by a power of the anchor and relabels fresh digits; on ANCHOR-TWISTED cells
  the twist is cell-preserving, so per-cell counts are translation-invariant. THEN
  VAL.2J + M2(ii) close the count. Evidence: the value probe's a_eff ∈ {0, 1, 2}
  twisted-cell exactness is M4b-T's shadow; its fixed-frame char-splits are exactly
  what M4b-T looks like when the twist is omitted. This makes per-cone geometric
  resummation legitimate in RESUM; rev 1 assumed it silently, rev 2 understated it.
- **M5 (menu completeness).** Every monic f with terminating resolution has its
  canonical history of some shape in 𝒮_n. *Sketch:* §B2-DEF TRANS constructs stage
  r+1 data of exactly the retained vocabulary; nothing else occurs.

**Kernels:** M2 (STATE, now a lumpability theorem), M4a (the affine-exponent +
congruence-lattice bookkeeping, with the Case-J anchor-monomial a > 0 exponents as
worked instances), and M4b-T (the translation normal form — REV 3).

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
clause survives; (iii) all parameter tuples in the sealed sets; (iv) zero oracle
mismatches. LIMITATION RECORDED: n = 3 exercises deep species only lightly (risk R3's
n = 4 escalation clause stands).

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

## 4. NOTE [3] RESUM — the depth resummation into rational functions of q (REV 3: normalized kernel K_e, B-step LEAK, STATE-probe-2 blocking)

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
  K_e(p) ≥ 0 and Σ_{τ′} K_e(p)_{τ,τ′} + (deciding/branching fraction) ≤ 1 hold BY
  CONSTRUCTION at every p: substochasticity is inherited from measure, never asserted
  of a resummed matrix. Every probabilistic claim in RS.3/SQ.2 is about K_e.
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
- **RS.1 (the aggregation identity).** For each type σ: Σ_{complete realizable
  canonical H of type σ} mass(H) — an absolutely convergent positive series (EXHAUST's
  depth envelope + M4a's height tails) — equals, after grouping by (MENU shape, state
  type) and resumming each parameter set, the σ-component of the solution of (R_e).
  *Sketch:* Theorem C gives mass(H) = ∏ vol(E_fresh); D4R.0/D4R.1 give disjoint
  exhaustion (canonical fibers — no quotient multiplicity; the pass-1 obstruction-2
  aggregation gap is repaired upstream, in [1]); group by shape (M5); per shape,
  Fubini the cone-lattice sum (absolute convergence justifies all rearrangements —
  Thm 4.1(i), unconditional via [5]); per-point counts are C_{S,τ}(q), constant across
  the cone (M4b — the rev-1 sketch had no such step and was unsound without it);
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
- **RS.3 (solvability — matrix pivots; LEAK weakened to MULTI-STEP at REV 3, pass-2
  obstruction 7's second half: ONE-step leakage from every state may be false at
  forced-recentering types and is not needed).** (i) LEAK lemma, B-step form: there
  exist B = B(n) (bounded via the menu diameter + X.1b's STALL budget — a NAMED
  dependence, conditional until X.1b closes) and c = c(n) such that from every type
  τ the B-step still-in-block mass is ≤ 1 − q^{−c} at every q = p — i.e. K_e(p)^B
  has row sums ≤ 1 − p^{−c}. With RS.PRE's K_e(p) ≥ 0 and substochasticity this
  gives ρ(K_e(p)) < 1, Neumann convergence, and (I − K_e(p))^{−1} ≥ 0. (Scalar
  positivity of entries proves NONE of this; the normalized-kernel + B-step-leak pair
  controls the whole block.) (ii) Hence det(I − K_e) ≠ 0 at infinitely many
  evaluations, so ≠ 0 in ℚ(q): the symbolic block solve is licit. Solution:
  R_σ ∈ ℚ(q), one per σ.
- **RS.4 (checksum).** Σ_σ R_σ = 1 identically in q (series = 1 at every p by [5]; a
  rational function equal to 1 at infinitely many q is 1). Cheapest layer invariant.
- **RS.5 (engine agreement).** Solved R_σ ≡ `alpha_full(n)[σ]` symbolically, n = 2…5 —
  the decomposition note's Thm 4.5 claim, proved rather than conditional. (Since the
  engine shares the value-count formulas, this is a CONSISTENCY identity, never
  independent evidence — pass-1 obstruction 8.)

**Kernels (derivation-grade — the campaign's biggest, now three):**
1. **RS.1's regrouping**: multi-side reads (strictly-decreasing-slope cones, the gap
   substitution `_sum_by_gaps`), the conditional-on-ancestors chain via C.1.5 stepwise
   (NO independence assumption), base-changed legs entering ONLY through [2r] REL.2.
2. **The depth-leg coefficient derivation**: M_e's entries with the Case-J a > 0
   anchor exponents inline — a wrong anchor exponent silently corrupts every deep
   coefficient.
3. **RS.0 TYPE-CLOSURE**: with M2/VAL.2J in hand, the height-shift bisimulation —
   the residual argument that loop position adds nothing (RS.0(β)).

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
  [3] RESUM may be ACCEPTED).** Configuration (the n = 6 one the feasibility finding
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
  derived; every consumer (X.2's env constants, RS.1's absolute convergence, SQ.1's
  finiteness, RS.3's B(n)) carries a CONDITIONAL-ON-X.1b tag until then.
  **STALL-probe (exploration-class, runs with the kernel draft):** exhaustive p = 2
  boxes — the full cubic box 2^24 at N = 8 and the quartic RS-chain conditioned
  cylinder 2^26 at N = 10 (the state-probe geometry: RS self-loops ARE zero-gain
  recenterings) — measure the max zero-gain run and the per-f ratio
  #zero-gain / v_p(disc f); one f violating the candidate s(n) kills that constant
  before the kernel is drafted around it. If the derivation instead finds a legal
  UNBOUNDED zero-gain chain, that is a hole in the termination story itself: stop,
  record, run §8 R4's experiment.
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

## 6. NOTE [4] SQUEEZE — the two-sided general-n bound, and THEOREM U (REV 3)

**The n = 2 pattern to generalize (W6):** (U) decided_σ(N) ≤ (value)·p^{2N} via the
fixpoint inequality `msW_eighth_le`, plus decided_σ(N) ≥ (value − env(N))·p^{2N} via the
box partition. REV 2 changes: SQ.1's finiteness cites STALL; SQ.2's induction runs
over (e, τ) blocks with [2r] supplying every base-changed hypothesis.

- **SQ.1 (budgeted covering — finiteness citation COMPLETED at REV 3; pass-2
  concern 6: X.1b alone is not enough).** Every f in the level-N box is in exactly
  one of: (a) the stratum of one complete realizable canonical history with threshold
  ≤ N, or (b) Undec(N). PARTITION (not mere covering): D4R.0. FINITENESS of the
  family in (a) — a displayed CONJUNCTION of three named bounds: (1) X.2 PROGRESS:
  threshold ≤ N bounds every relevant height by h*(N); (2) a genuine-event bound:
  v_p(disc f) is bounded on the decided level-N box (Lemma 3.3's tail at box level),
  so X.1a caps d_gen; (3) X.1b's STALL budget (CONDITIONAL-ON-X.1b tag) caps
  zero-gain nodes by s(n)·v_p(disc f). Together: boundedly many nodes, each over
  finite data alphabets — a finite family. Then strong induction on the remaining
  degree budget, per the decomposition note 3.4′(a).
- **SQ.2 (the fixpoint upper bound — the (U) analogue).** For every N and σ:
  decided_σ(N) ≤ R_σ(p)·p^{nN}. *Route (REV 2):* the depth/height partial sums of
  RS.1's positive series are ≤ the full sum; the full sum = the block solve; the
  solution dominates every partial sum by MATRIX monotone iteration — RS.PRE's
  normalized K_e ≥ 0, Neumann convergence via RS.3(i)'s B-step LEAK at q = p —
  inducted in cluster size
  e, with ALL base-changed legs β_m(p^δ) supplied as [2r] REL.3 statements over O_δ
  (pass-1 obstruction 6: the induction hypothesis is now a certified input, not a
  formal substitution). Needs R_σ(p) ≥ 0 and block positivity (RS.3), stated
  explicitly, not just formal solvability.
- **SQ.3 (the lower bound).** decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN}: box partition
  p^{nN} = Σ_τ decided_τ(N) + undec(N), apply SQ.2 to every τ ≠ σ, RS.4's checksum,
  and X.2's envelope.
- **SQ.4 = THEOREM U.** ρ_σ := lim decided_σ(N)/p^{nN} exists and equals R_σ(p) for
  every p; R_σ ∈ ℚ(q) is the p-independent solution of (R_e); Σ_σ R_σ = 1. Assembled
  from SQ.2 + SQ.3 + X.2. State with the honest normalization sentence (monic-box
  density; projective/palindromy OUT OF SCOPE per the standing directive).

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
   MENU-n3/EXHAUST-n3 exercise n = 3 species only). Gate roster at REV 3: D4-n3,
   VALUE-Fq (24 q-points) + VALUE-p, MENU-n3, REL-n4, EXHAUST-n3 (+ STALL-probe),
   STATE-probe-2 + RESUM-n3, SQUEEZE-n3. Gate scripts live in `verification/`,
   predictions in `verification/*_SEALED_PREDICTIONS_<date>.md`.
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
  WALL RULE (REV 3 — refute-or-support per §2v (†); rev 2's "differs from every ℚ(q)
  interpolation" was logically impossible on finite data): (1) census the family at
  m ≥ W(S)+2 exact points; (2) an exact mismatch with the degree-≤W(S) interpolant,
  surviving adjudication, CONCLUSIVELY refutes universality of that stratum — the
  displayed growth bound C_S ≤ q^{W(S)} plus integrality means finite data DOES
  decide the negative; a wild-p mismatch on the degree-bounded tame interpolant of a
  σ-aggregate is the WALL, demonstrated conclusively (the directive's obstruction);
  (3) an all-points match is SUPPORT at stated surplus, and acceptance still runs
  through the VAL.1/VAL.2J proofs. PROBE RESULT (exploration-class, 24 q-points,
  results/value_probe_output.txt): all 15 linked totals UNIVERSAL (surplus ≥ 15);
  σ-aggregates match the tame interpolant at p = 2 and p = 3 EXACTLY; twisted-cell
  fiber constancy exact everywhere; 32 fixed-frame series provably char-dependent —
  adopted as the ANCHOR-TWIST design constraint on VAL.2J/M2/M4b-T, NOT a wall. The
  SEALED VALUE-Fq/VALUE-p gates still run before [1v] is trusted (Case-K discipline).
- **R2 — the same-size recursion does not close in finitely many state types
  (POTENTIAL STRUCTURAL WALL). PROBE REPORTED 2026-07-26: probe-level NO-WALL; the
  gate is REOPENED.** Repair: RS.0 TYPE-CLOSURE (lumpability + bisimulation, §4) +
  M2 ([2b]). The first STATE-probe (exploration-class) found exact same-type law
  equality at the value-varying n = 4 configuration (vtx RIGID below n = 6 — the
  feasibility finding on record in the script docstring) — negative evidence for the
  probed rows only; it does NOT establish RS.0 and did NOT exercise the
  vtx-stratum-varying regime rev 2 specified. WALL EXPERIMENT now = STATE-probe-2
  (§4: n = 6, p = 2, R₀ = ψ²·χ, conditioned cylinders ≤ 2^28 per state at N = 8,
  REQUIRED before [3]'s acceptance): a same-TYPE mismatch surviving adjudication AND
  one 𝒯-refinement round via [1v]'s strata = the wall — a genuinely new resummation
  idea required; no fallback inside this architecture. (Same-SHAPE different-TYPE
  differences are expected and carried by the block system.)
- **R3 — menu completeness failure (M5).** A realized history species outside the
  retained vocabulary. DEMONSTRATED BY: a stray shape or a PARI-oracle mismatch in the
  exhaustive MENU-n3 census. REV 2 honesty (pass-1 obstruction 8): gates cannot
  certify ABSENCE — exhaustive enumeration certifies fixed (p, N) only, and the oracle
  closes shared blindness at the decision level only; M5 is accepted on PROOF, gates
  are falsifiers. The n = 4 / depth-3 escalation clause stands (D.12 level-3 gate,
  promoted from optional, if M5's species-coverage argument resists).
- **R4 — the stall budget fails (X.1b). WIDENED at REV 3: X.1b is an OPEN kernel
  (WEIGHT-CHARGE), so this wall is LIVE until the lemma is derived or refuted.** If
  zero-index recenterings can repeat unboundedly between genuine events, the envelope
  AND the termination story both break. DEMONSTRATED BY: a STALL-probe (§5) per-f
  ratio violation of every candidate s(n), an EXHAUST-n3(ii) stall-census overrun, or
  the X.1b derivation finding a legal unbounded improvement chain against the L5fix
  Invariant-2 budget. Until X.1b closes, all consumers carry the CONDITIONAL-ON-X.1b
  tag (X.2, RS.1, RS.3's B(n), SQ.1) — no acceptance of [3]/[4] hides the condition.
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

[1] D4-R: 1 unit (restatement + the PARTITION kernel, now with three named
obligations). [2a] SPECIES: 1 unit (M1 + M5). [1v] VALUE: 2–3 units (two kernels +
the widened 24-point gates). [2b] STATE-GEOM: 2 units (M2 lumpability + M4a + M4b-T).
[2r] REL: 1.5–2 units (the re-scoping pass + the four REL.2 obligations + one gate).
[5] EXHAUST: 2 units (three kernels; X.1b is OPEN — WEIGHT-CHARGE may resist).
[3] RESUM: 4–5 units (RS.PRE/RS.0/RS.1 kernels + STATE-probe-2 + RESUM-n3).
[4] SQUEEZE: 2 units. Verification multiplies each by the usual ~2× (the §C
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
