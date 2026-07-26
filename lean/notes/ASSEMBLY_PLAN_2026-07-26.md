# ASSEMBLY_PLAN_2026-07-26 — the final campaign: from accepted §C to the complete wild-uniformity theorem (REV 2)

*Plan architect: Fable, 2026-07-26. REV 2, same day: rebuilt against the pass-1
structural review (ASSEMBLY_PLAN_PASS1_2026-07-26.md — 8 critical obstructions,
7 concerns, verdict UNSOUND); the finding→repair table is the REV 2 record at the end
of this file. Directive (Asvin, 2026-07-26): iterate on the math with
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

## 1. The DAG of the remaining notes (REV 2 — seven notes)

Arrows = "consumes the accepted statement of". Two notes are NEW at REV 2: [1v] VALUE
(the linked value-count kernel — the honest replacement for the retired torus lemma)
and [2r] REL (the relative ledger — the MEASURE content of every q ↦ q^δ substitution).

```
   §C (Theorem C)                     decomposition note §3 (3.2/3.3/3.4)
    │        │        │                            │
    ▼        ▼        ▼                            ▼
[1] D4-R  [2] MENU  [2r] REL                  [5] EXHAUST
    │        │  │       │                          │   (tie-in: genuine-event
    ▼        ▼  │       │                          │    depth ⟹ Desc_d + STALL)
   [1v] VALUE   │       │                          │
        │       │       │                          │
        ▼       ▼       ▼                          │
       [3] RESUM ◄──────┴───(abs. convergence)◄────┤
            │                                      │
            ▼                                      │
       [4] SQUEEZE ◄───────────────────────────────┘
            │
            ▼
        THEOREM U  (assembly capstone paragraph inside [4])
```

- **[1] D4-R** — *the per-shape-prefix mass law*, REBUILT on the CANONICAL-POLICY
  history (no transport quotient — pass-1 obstruction 2): the deterministic classifier
  with the (S6b) canonical lift emits ONE history per terminating f; strata are fibers,
  disjointness is the PARTITION kernel. The pool BOUND (3i) survives verbatim.
- **[1v] VALUE** — *the linked value-count structure* (NEW; absorbs the role of the
  retired torus lemma D4R.3): whether the per-shape count of (NA)/(HV)-linked value
  assignments is a universal polynomial in q. The campaign's R1 decision point; its
  gates run BEFORE [3] is drafted.
- **[2] MENU** — *shape-menu finiteness at general n*: goal unchanged; M1's bound
  corrected to the displayed degree identity (cumulative residue degree ≤ n, not n!);
  M2 promoted to the STATE kernel (finite p-independent state-TYPE list — also the
  block-index set [3] needs); M4 split into cone geometry (M4a) and per-point counts
  (M4b, routed to [1v]).
- **[2r] REL** — *the relative ledger* (NEW): Theorem C re-scoped to unramified
  O = W(F_{p^δ}) + the sub-cluster base-change identification — what β_m(q^δ) MEANS as
  a measure statement (pass-1 obstruction 6).
- **[5] EXHAUST** — *the discriminant-tail tie-in*, REDESIGNED two-track (pass-1
  obstruction 7): genuine-event depth via GMN, PLUS a STALL budget for zero-index
  recenterings; envelope constants affine-honest, geometric decay retained.
- **[3] RESUM** — *the depth resummation*, now a finite BLOCK-triangular linear system
  over ℚ(q) indexed by (cluster size e, state type τ): closure is the TYPE-CLOSURE
  theorem (pass-1 obstruction 5 — no longer an assumption); pivots are matrix pivots
  (I − M_e(q)), inverted via the substochastic LEAK lemma; p-uniformity derived from
  [1v], never imported.
- **[4] SQUEEZE** — *the two-sided finite-level bound*: decided_σ(N) ≤ R_σ(p)·p^{nN}
  and ≥ (R_σ(p) − env(N))·p^{nN}, hence ρ_σ exists and equals R_σ(p) — Theorem U; the
  domination induction runs over (e, τ) blocks with base-changed hypotheses supplied
  by [2r], not assumed.

**Execution order:** [1] → { [1v] ∥ [2] ∥ [5] } → [2r] → [3] → [4]. [1v] is
deliberately EARLY: if linked-count universality fails structurally (risk R1), the
campaign finds out before [3] consumes its 4–5 units. The STATE-probe gate (§4) also
runs before [3] drafting. [2r] starts once [1v]'s stratification vocabulary stabilizes.

**Format per note (sections 2–6 below):** key definitions · load-bearing lemmas with
proof sketches · kernels (fresh-context derivation-grade, C10B/C15-style) · the sealed
gate that must PASS before the note may be trusted (§7 protocol). GATE DESIGN RULE
(REV 2, pass-1 obstruction 8): wherever the gated claim is exact, the gate is exact —
exhaustive finite-level enumeration or exact F_q counts; sampling survives only in
labeled consistency layers. And n = 3 alone is NOT enough: a cubic's deg-2 key cannot
carry μ ≥ 2, so the value-kernel gates run at n = 5 and directly over F_q.

## 2. NOTE [1] D4-R — the per-shape-prefix mass law (REV 2: canonical policy, no quotient)

**What D4 was.** Decomposition note (3i): for class-3 read-prefixes P,
μ(P) ≤ p^{−A_net(P)}, A_net(P) := A(P) − W(P), with A(P) the ledger exponent and
W(P) = Σ_r w_r·d_r the pool dimension — UNIFORMLY in p. Its reduction (R1)/(R2) ran
through joint-D1's conditional-on-ancestors clause. §C now supplies that clause in
proved form: C.1.5(1) — mass(Σ_i ∩ stratum(ν_{i+1})) = mass(Σ_i)·vol_nom(E_fresh(ν_{i+1}))
— IS the chain rule (R2) needed, and Theorem C(b) with Z = ∅ is its closed composition.

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
  terminates); consequently S(H, ∅) = {f : H_can(f) = H} — strata are FIBERS of a map,
  and disjointness is automatic. *Derivation obligation:* two histories sharing a
  prefix are compared in the COMMON frame Ψ_prefix (same prefix + same canonical lifts
  ⟹ same frame), where the two node-(i+1) patterns read different digit values of the
  same development — never across transported coordinates (Theorem C alone does NOT
  supply this; it is a new lemma).
- **D4R.1 (exact prefix mass).** μ(P̂) = Σ_{H ∈ Hist(P̂)} ∏ᵢ vol(E_fresh(νᵢ))
  = C_P̂(p)·p^{−A(P̂)}. *Sketch:* disjointness + exhaustion of the prefix event by
  D4R.0 (fibers of H_can); each mass is Theorem C(b) with Z = ∅; vol(E_fresh) depends
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
- **D4R.4 (N-stability).** μ(P̂) is computed at any N ≥ max_H N(H, ∅): Hist(P̂) is
  finite WITHOUT any quotient (pass-1 concern 4 repaired) — value assignments range
  over finite alphabets, the canonical lift is a function of node data, the fixed shape
  bounds all heights hence all constrained levels hence each N(H, ∅), and the max over
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

## 2v. NOTE [1v] VALUE — the linked value-count structure (NEW at REV 2; the R1 decision point)

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
> **Theorem VAL (target form).** For each shape S ∈ 𝒮_n there is ONE polynomial
> C_S ∈ ℚ[q] with C_S evaluated at the shape's pool sizes = the linked count, for every
> p — equivalently every prime power q at the finite-field layer. — OR the explicitly
> weaker form that still closes RESUM: the TYPE-AGGREGATED sums
> Σ_{S contributing to σ} C_S(p)·p^{−A(S)} are values of fixed elements of ℚ(q)
> (per-shape non-polynomiality allowed iff it provably cancels in the aggregate).

**Route (two layers + a fallback; the first two are derivation-grade kernels).**
- **VAL.1 (stratified fiber calculus).** For each node species, c_V is CONSTANT on the
  cells of an explicit p-independent stratification of the target F_{q^g}ˣ (cells cut
  by subfield membership, support conditions, the anchor monomial — e.g. the
  counterexample's target space stratifies as {t ∉ F_q·α} with c_V = 1 versus
  {t ∈ F_qˣ·α} with c_V = 0, cell sizes polynomial in q), with cell sizes and counts
  universal polynomials. The L3 necklace/Gauss counts are the depth-0 instance.
- **VAL.2 (the vtx image/distribution — the "additional theorem" pass-1 named).** The
  distribution of vtx(parent) over the parent's own linked assignments is constant on
  the SAME stratification (or an explicit common refinement). Then the linked count is
  the pairing Σ_cells (parent count on cell)·(child fiber count on cell) — polynomial.
  This is where the note either closes or hits R1: the two stratifications must match
  at EVERY (HV) hinge of every shape, μ ≥ 2 and a > 0 included.
- **VAL.3 (fallback — aggregate cancellation).** If some C_S is genuinely
  non-polynomial (a q mod m or Frobenius-trace term), determine whether the σ-aggregate
  cancels it. A PROVED cancellation keeps RESUM alive at aggregate granularity (risk
  R8's re-derivation cost); a proved NON-cancellation at some σ and wild p is the R1
  wall — the directive's conclusive obstruction, demonstrated per §8 R1, not papered
  over.

**Sealed gates (both EXACT — no sampling anywhere in this note).**
- **VALUE-Fq.** Direct exhaustive enumeration of linked counts over F_q for a sealed
  list of n ≤ 5 two-node configurations INCLUDING the pass-1 counterexample family
  (deg ψ = 2, μ = 2, a ∈ {0, 1}, lead factor (Az+B)), at q ∈ {2, 3, 4, 5, 7, 8, 9, 11,
  13} — prime POWERS included deliberately: they probe universality in q directly.
  Seal: the VAL.1/VAL.2 formulas' exact values at every q. PASS = exact integer
  equality throughout.
- **VALUE-p (the p-adic shadow).** n = 5, p = 2 and p = 3: root read carrying residual
  ψ²·(linear) (the counterexample geometry), one linked descend. Seal: the exact
  prefix-event count C·p^{5N−A}, verified by EXHAUSTIVE enumeration mod p^N (feasible:
  2^20 at N = 4; 3^15 at N = 3). PASS = exact.
- A FAIL is adjudicated (prediction-derivation error vs theory error); if theory: run
  §8 R1's isolation experiment BEFORE any further RESUM work.

## 3. NOTE [2] MENU — shape-menu finiteness at general n (REV 2)

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
- **M2 (STATE — promoted kernel; pass-1 concern 2 + obstruction 5's demand).** Define
  the LOOP STATE at a node: (residual polynomial's shape, anchor a, tower phase, the
  STRATUM of the transported vertex value vtx under [1v]'s VAL.1 stratification — not
  the value itself). Prove: (i) states quotient to a FINITE p-INDEPENDENT list of state
  TYPES 𝒯_n; (ii) EVERY degree-preserving MOVES move maps state type to state type —
  the map pass-1 concern 2 found missing: each L5fix-bounded phase invariant exhibited
  per move species (what "self-loop at fixed key data" is at order r ≥ 2; the e_birth
  vs e_read threading re-walked once here); (iii) proper refinements number ≤ n − 1
  (L5fix Invariant 1 transported: each strictly refines the (e, f)-partition or
  strictly increases Σ eᵢfᵢ). Load-bearing TWICE: menu finiteness here, and the
  block-index set of RESUM's system (RS.0).
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
- **M4b (per-point counts factor through the type).** At every lattice point of M4a's
  set, the number of realizable value assignments is C_{S,τ}(q) — a function of the
  shape and state type ONLY, not of the cone position. *Route:* [1v] VAL.2 + M2(ii)
  (the state type is the only value-relevant datum a move can change). This makes
  per-cone geometric resummation legitimate in RESUM; rev 1 assumed it silently.
- **M5 (menu completeness).** Every monic f with terminating resolution has its
  canonical history of some shape in 𝒮_n. *Sketch:* §B2-DEF TRANS constructs stage
  r+1 data of exactly the retained vocabulary; nothing else occurs.

**Kernels:** M2 (STATE) and M4a (the affine-exponent + congruence-lattice bookkeeping,
with the Case-J anchor-monomial a > 0 exponents as worked instances).

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

## 3r. NOTE [2r] REL — the relative ledger (NEW at REV 2; pass-1 obstruction 6)

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
- **REL.2 (sub-cluster base change).** At a read whose residual factor has residue
  degree δ, the conditional continuation measure of that factor's cluster is
  measure-exactly the REL.1 theory over O_δ, with pool sizes q^δ — the precise content
  of JOINT-D1's q ↦ q^w clause, now THROUGH Theorem C. Consumers: RS.1's mixed legs;
  SQ.2's induction at β_m(p^δ).
- **REL.3 (positivity/domination transfer).** The finite-level covering and
  monotone-domination statements SQUEEZE needs, restated and proved over O — stated
  separately because SQ.2 consumes them at q = p^δ, where "positive mass < 1" must be
  a theorem about vol_O, not a formal substitution.

**Kernel:** REL.1's re-scoping pass (fresh context, accepted §C text in hand,
step-by-step base audit; the one place a silent q = p usage could hide is TYP(a)'s
per-digit 𝔽_p-linearity, retyped at §C rev 11 — walk it first).

**Sealed gate REL-n4.** p = 2, n = 4: condition on root reads whose residual factor is
an irreducible QUADRATIC (δ = 2); seal the conditional refinement law of that cluster
from the O = W(F_4) formulas (the engine's q ↦ q² layer). Verify EXACTLY two ways:
(i) the exhaustive level-N slice of the conditioned event over ℤ_2 (2^{4N} boxes,
N ≤ 5); (ii) a direct W(F_4)-side enumeration of the corresponding MOVES strata at
matching level. PASS = exact equality of both computations with the sealed law.

## 4. NOTE [3] RESUM — the depth resummation into rational functions of q (REV 2)

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
via MENU M4b — NOT from the retired torus lemma.

- **RS.0 (TYPE-CLOSURE — promoted kernel; the rev-1 assumption made a theorem).**
  Every same-size move's transition coefficient depends on the source state only
  through its TYPE τ (M2(ii) gives the type map; VAL.2 gives coefficient constancy per
  type), and loop POSITION carries no further information (the retained data after k
  self-loops is a state type, not a k-indexed object). If this fails — same shape,
  same type, provably different transition law — the system is not finite: risk R2's
  wall, probed by the STATE-probe gate below.

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
  VAL (or its VAL.3 aggregate form) — it does NOT follow from Theorem C + Claim 4.3;
  the torus-lemma bridge is dead. Shapes and exponents: MENU. Mixed legs: [2r].
  Per-shape emptiness at wild p = polynomial vanishing (W1's pool-size effect).
  p enters only at evaluation q = p.
- **RS.3 (solvability — matrix pivots; pass-1 concern 5 repair).** (i) LEAK lemma:
  from every state type, the one-move mass into deciding/branching continuations is
  ≥ q^{−c(n)} > 0 at every q = p — so M_e(p) is componentwise nonnegative and
  substochastic with every state leaking: spectral radius ρ(q^{−e(e−1)/2}M_e(p)) < 1,
  the Neumann series converges, and (I − q^{−e(e−1)/2}M_e(p)) is invertible with
  nonnegative inverse. (Scalar positivity of entries proves NONE of this by itself —
  the concern's point; the leak argument controls the whole block.) (ii) Hence
  det(I − q^{−e(e−1)/2}M_e) ≠ 0 at infinitely many evaluations, so ≠ 0 in ℚ(q): the
  symbolic block solve is licit. Solution: R_σ ∈ ℚ(q), one per σ.
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
3. **RS.0 TYPE-CLOSURE**: with M2/VAL.2 in hand, the residual argument that loop
   position adds nothing.

**Sealed gates (two; STATE-probe runs FIRST, before this note is drafted).**
- **STATE-probe (NEW — risk R2's discriminating experiment).** Smallest configuration
  with two same-shape, same-size states in DIFFERENT VAL.1 vtx-strata (expected n = 4
  or 5). Seal: the two conditional next-move distributions, exact, from the claimed
  M_e row. Census: exhaustive small-N enumeration of both conditioned events at p = 2
  (and p = 3 where feasible). PASS = both match the sealed row EXACTLY (same type ⟹
  same law). A reproducible same-TYPE mismatch after adjudication triggers ONE
  𝒯-refinement round via [1v]'s strata; a second failure invokes §8 R2's wall
  protocol.
- **RESUM-n3 (the headline gate, REV 2 form).** Solve (R_e) for n = 3 symbolically.
  Seal BEFORE any census: the FIVE rational functions R_σ, σ ∈ {(1,1)³, (1,1)+(1,2),
  (1,3), (1,1)+(2,1), (3,1)}, values at p = 2, 3 (wild), 5, 7 (tame), the checksum,
  AND the exact finite-level partial sums by depth. DISCRIMINATING layer (exact,
  pass-1 obstruction 8): decided_σ(N) by EXHAUSTIVE enumeration (p = 2: N ≤ 8, 2^24;
  p = 3: N ≤ 5, 3^15), types from the PARI `factorpadic` oracle
  (`verification/quartic_oracle.py` pattern) — EXACT integer equality per (σ, N,
  depth-row) against the sealed theory partial sums; any exact mismatch surviving
  adjudication is structural (§8 R1/R2). CONSISTENCY layer (labeled non-discriminating):
  10⁶–10⁷ sampled cubics at all four primes within EXHAUST-tail + σ-bands;
  `om_density_engine.alpha_full(3)` and `reconcile_om_bcfg.py` cross-checks.

## 5. NOTE [5] EXHAUST — the discriminant-tail tie-in (REV 2: two-track; do before RESUM)

**What already stands (decomposition note §3, accepted):** Lemma 3.2 (still descending
at depth d ⟹ v_p(disc f) ≥ 2d — GMN theorem of the index, pins (P1)–(P3) verbatim in
`GMN_citations.md`), Lemma 3.3 (elementary tail: μ{v_p(disc) ≥ D} ≤
(n−1)·p^{−⌈(D−n·v_p(n))/(n−1)⌉}), Cor 3.4 (Desc_d envelope, geometric in d). Pointwise
depth ⟹ disc; NO per-depth identities (the SELFLOOP wall stays sidestepped).

**REV 2 REDESIGN (pass-1 obstruction 7: rev 1's X.1 claimed every MOVES node is a unit
GMN event while its own kernel paragraph admitted zero-index recenterings —
incompatible; the raw node-count premise is WITHDRAWN).** Depth splits into two tracks:
- **X.1a (genuine-event dictionary).** d_gen(H) := #{nodes with GMN index gain
  ind_r ≥ 1}: all increments, plus recenterings whose polygon carries an on-side
  lattice point (the (P3) accounting; GMN Thm 4.18's "including refinements", pinned).
  Then stratum(H) ⊆ Desc_{d_gen(H)} ⊆ {v_p(disc) ≥ 2·d_gen(H)}. *Sketch:* per genuine
  node, exhibit the (s+e, u+(d−1)h) on-side point in the node's OWN polygon under the
  (P1) on-or-below convention; the §B2-DEF stage dictionary (D.12) aligns polygons.
- **X.1b (STALL budget — promoted kernel).** Zero-index recenterings between genuine
  events are BOUNDED: each recentering strictly increases the current key's weight
  (D.10: the new key's weight is the consumed side's value > the old key's weight),
  and the weight ladder within one genuine-event interval is capped by the
  L5fix-Invariant-2 different budget — yielding an explicit s(n) with (#zero-gain
  nodes between consecutive genuine events) ≤ s(n)·(local height budget). HONEST
  consequence: v_p(disc f) ≥ c₁(n)·d_total(H) − c₂(n), affine with NAMED constants —
  NOT "≥ 2d" for raw node count (rev 1's false premise). A geometric-in-d_total
  envelope survives with rescaled constants — all that [3]/[4] consume. If the
  derivation instead finds a legal UNBOUNDED zero-gain chain, that is a hole in the
  termination story itself: stop, record, run §8 R4's experiment.
- **X.2 (undecided ⊆ deep-or-tall, coercivity DISPLAYED — pass-1 concern 6).** Kernel
  PROGRESS: each move's fresh content constrains levels ≤ an explicit affine function
  of its heights, so f undecided at level N has (d_total ≥ d*(N)) OR (some height ≥
  h*(N)), with the d*/h* balance displayed — no "positive exponents ⟹ done" step
  (mixed height cones can grow nominal exponent and required precision at different
  rates; the uniform bound must be exhibited). Then env(N) ≤ c₃(n)·p^{−c₄(n)·N} with
  constants traced to X.1b + M4a tails. This is what SQUEEZE and RESUM-n3 consume.
- **X.3 (termination a.e. + N-stability restated).** μ(non-terminating) = 0; every
  terminating f decided at its finite threshold; the stratum series per σ sums the
  full type density (3.2 + 3.3 + Thm 2.1, restated in MOVES vocabulary — one cite
  point for [3]/[4]).

**Kernels:** X.1b STALL (per-species index accounting AND the weight-ladder cap — the
exact "what counts as an event" subtlety that produced the (P1) convention hunt) and
X.2 PROGRESS (the threshold-vs-exponent coercivity).

**Sealed gate EXHAUST-n3 (exhaustive where the claim is pointwise).** Seal: (i) on the
EXHAUSTIVE level-8 box at p = 2 (2^24) and level-5 at p = 3 (3^15): every f still
descending at genuine-event depth d has v_p(disc f) ≥ 2d — 0 violations tolerated;
(ii) STALL census: the maximum observed zero-gain run vs the sealed budget — one
overrun kills X.1b; (iii) the (3b) constant at D = 2…8 vs exact counts; (iv) X.2's
env(N) at N = 4…8 vs measured undecided mass, both primes, exhaustive. A violation in
(i)/(ii) is adjudicated against the dictionary X.1a/X.1b, not patched.

## 6. NOTE [4] SQUEEZE — the two-sided general-n bound, and THEOREM U (REV 2)

**The n = 2 pattern to generalize (W6):** (U) decided_σ(N) ≤ (value)·p^{2N} via the
fixpoint inequality `msW_eighth_le`, plus decided_σ(N) ≥ (value − env(N))·p^{2N} via the
box partition. REV 2 changes: SQ.1's finiteness cites STALL; SQ.2's induction runs
over (e, τ) blocks with [2r] supplying every base-changed hypothesis.

- **SQ.1 (budgeted covering).** Every f in the level-N box is in exactly one of:
  (a) the stratum of one complete realizable canonical history with threshold ≤ N, or
  (b) Undec(N). PARTITION (not mere covering): D4R.0. FINITENESS of the family in (a):
  a threshold-≤N history has boundedly many nodes — X.1b's STALL budget excludes
  unboundedly many zero-new-condition moves (pass-1 concern 7: this was a silent
  requirement; it is now a NAMED citation, without which the passage from the finite
  decided set to a finite truncation of the series fails). Then strong induction on
  the remaining degree budget, per the decomposition note 3.4′(a).
- **SQ.2 (the fixpoint upper bound — the (U) analogue).** For every N and σ:
  decided_σ(N) ≤ R_σ(p)·p^{nN}. *Route (REV 2):* the depth/height partial sums of
  RS.1's positive series are ≤ the full sum; the full sum = the block solve; the
  solution dominates every partial sum by MATRIX monotone iteration — nonnegative
  blocks, Neumann convergence via RS.3(i)'s LEAK at q = p — inducted in cluster size
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
   new formula layer: D4-n3, VALUE-Fq + VALUE-p, MENU-n3, REL-n4, EXHAUST-n3,
   STATE-probe + RESUM-n3, SQUEEZE-n3 (§§2–6). DISCRIMINATION RULE (REV 2, pass-1
   obstruction 8): wherever the gated claim is exact, the gate is exact — exhaustive
   enumeration or exact F_q counts, with the PARI oracle as the independent
   ground truth; sampled censuses appear only as labeled consistency layers and never
   constitute acceptance evidence. Gate scripts live in `verification/`, predictions
   in `verification/*_SEALED_PREDICTIONS_<date>.md`.
5. **Update `docs/PROJECT_STATE.md` + the MOVES ledger** at every acceptance
   (update-then-act); axiom changes (none planned — X.1 cites the already-pinned GMN
   material) would additionally require the semantic-guardian triple test.
6. Check `codex-limits` before each heavy verification round; adversarial verification
   is the LAST Codex use to cut.

## 8. Honest risk register (REV 2 — updated per the pass-1 structural review)

**Recorded NON-failures (the review's own closing findings — keep off the worry
list):** the base-change substitution q ↦ q^δ does not threaten rationality (the
missing piece was the MEASURE statement, now note [2r]); unbounded deep residual
degrees are NOT the MENU obstruction (M1's corrected degree identity bounds cumulative
residue degree by n). Also surviving intact: D4R.2's pool bound (3i) and the entire §0
certified perimeter.

- **R1 — the linked value count is not universal in q (the theorem-killer; POTENTIAL
  STRUCTURAL WALL).** Pass-1 obstruction 1 KILLED the torus lemma (counterexample on
  record in §2: R_anch = z^a ψ^μ (Az+B), vtx-fibers 1 vs 0); the exposure is now
  precisely [1v] Theorem VAL. WALL EXPERIMENT (decisive, cheap, runs EARLY): (1)
  VALUE-Fq exact enumeration of the counterexample family's linked counts at
  q ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13}; (2) if non-polynomial: compute the σ-AGGREGATED
  counts exactly at the same q — a PROVED cancellation sends the campaign down VAL.3
  (see R8); (3) if a type-aggregate at wild p provably differs from every ℚ(q)
  interpolation of the tame/prime-power values (exact arithmetic, both wild primes,
  adjudicated on record), the approach — and possibly the theorem's monic form — fails:
  record as the directive's conclusive obstruction. NOTHING downstream of [1v] is
  drafted before this experiment reports.
- **R2 — the same-size recursion does not close in finitely many state types
  (POTENTIAL STRUCTURAL WALL).** Pass-1 obstruction 5: rev 1 asserted triangularity —
  effectively R2's negation — without proof; retained state (vtx stratum, anchor,
  phase, position) could index same-e unknowns, potentially infinitely many. Repair:
  RS.0 TYPE-CLOSURE + MENU M2. WALL EXPERIMENT: STATE-probe (§4) — two same-TYPE
  states with provably different one-move laws, surviving adjudication AND one
  𝒯-refinement round via [1v]'s strata, = the wall: a genuinely new resummation idea
  required; no fallback inside this architecture. (Two same-SHAPE different-type
  states differing is expected and handled by the block system.)
- **R3 — menu completeness failure (M5).** A realized history species outside the
  retained vocabulary. DEMONSTRATED BY: a stray shape or a PARI-oracle mismatch in the
  exhaustive MENU-n3 census. REV 2 honesty (pass-1 obstruction 8): gates cannot
  certify ABSENCE — exhaustive enumeration certifies fixed (p, N) only, and the oracle
  closes shared blindness at the decision level only; M5 is accepted on PROOF, gates
  are falsifiers. The n = 4 / depth-3 escalation clause stands (D.12 level-3 gate,
  promoted from optional, if M5's species-coverage argument resists).
- **R4 — the stall budget fails (X.1b).** If zero-index recenterings can repeat
  unboundedly between genuine events, the envelope AND the termination story both
  break. DEMONSTRATED BY: an EXHAUST-n3(ii) stall-census overrun, or the X.1b
  derivation finding a legal unbounded improvement chain against the L5fix
  Invariant-2 budget.
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
- **R8 — aggregate-cancellation mirage (NEW).** If VAL.3's fallback is invoked
  (per-shape counts non-polynomial, aggregates provably cancel), RESUM's per-shape
  ledger stops being the natural basis: RS.1's regrouping must be RE-DERIVED at
  aggregate granularity with its own verification round — budget one extra unit; never
  patch silently.

## 9. Effort map (REV 2 — for scheduling, not for skipping)

[1] D4-R: 1 unit (restatement + the PARTITION kernel). [1v] VALUE: 2–3 units (two
kernels + the campaign's cheapest decisive gates — run early). [2] MENU: 2–3 units
(M2 STATE is now a kernel alongside M4a). [2r] REL: 1–2 units (the re-scoping pass +
one gate). [5] EXHAUST: 1.5 units (two kernels now). [3] RESUM: 4–5 units (three
kernels + two gates). [4] SQUEEZE: 2 units. Verification multiplies each by the usual
~2× (the §C precedent: 13 passes). Gates are cheap (CPU-only, exhaustive boxes ≤ 2^24
/ 3^15; `verification/` patterns exist); seal discipline is the cost. The REV-2
additions are FRONT-LOADED by design: [1v] and STATE-probe sit on the two potential
walls (R1, R2) and report before the expensive middle is drafted.

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
before RESUM/SQUEEZE effort is spent.
