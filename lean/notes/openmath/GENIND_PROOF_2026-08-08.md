# GENIND — THE GENERAL TWO-SPECIES INDUCTION (the (hMenu-n)+(hExhaust-n) package for ALL n at once): every refinement history decomposes into α-nodes (self-similar, bracket (Q−1)Q^{(m(m−1)/2+1)μ−1}) and β-nodes (products of strictly-lower-degree systems indexed by the realized partition), the induction scaffold PROVED conditional on the per-stage classification, the simple-stage layer delivered by W-12.A + the transports, the composite-stage criterion DERIVED EXACTLY (a stage with ≥ 4 keys: n ≥ 4, NOT primality — n = 5 is composite-bearing), and the composite-stage law displayed as the frontier with the quartic (2,2) bracket attempted from the weld corpus

**Unit:** GENIND (the general-induction composer; Asvin's 2026-08-08
directive on reading HMENU3: "we now have the shape of a general
inductive argument! Exhilarating, lets keep going!" — ledger 66057f4).
**Attempt grade 0/2** (composed; no hostile arc). **Instrument:**
sealed two-commit battery `verification/openmath/genind_checks.py` —
the two-species classification machine-checked at n = 4 AND n = 5 on
targeted rosters (full-sweep rows where the state space permits;
CONSTRUCTED targeted loci where it does not, e.g. the first n = 5
α-node at N = 6 and the first n = 4 depth-2 α at N = 9), with the
depth-0 species partition both directions, the α-transport pointwise,
the β-fracture pointwise (scale-then-Hensel + child re-read), the
drainage first-step recursion, the composite-stage criterion with two
flagship genre laws per degree, an n = 3 negative control tied to the
committed hex3 artifacts, a PARI σ-oracle leg, and ≥ 3 teeth at
preregistered exact fire counts. Verdict §S11, appended at commit 2
FROM the committed artifacts. **Division of labor (disclosed):** the
parallel scout QSCOUT22 (@ 240a56c, skeleton) owns the INSIDE of the
quartic (2,2) composite stage (genres E/F, the four-slot model, the
level-2 empirical table); this unit owns the induction, the
opening-level laws, and the criterion — the two units' machine legs
are disjoint by design.

**What GENIND is (one breath).** THEOREM W-12.D (PROVED, an
unconditional reduction) turns {(A0) lift well-posedness + (A1) exact
disjoint q-uniform core menu + (A2) drainage} at degree n into ONE
R_τ ∈ ℚ(q) per splitting type at every prime power, both
characteristics, wild included. At n = 2 it fires on W-11; at n = 3 on
HEX3 + HMENU3. The n = 3 proof had a SHAPE — LEMMA HM3-1's two-species
chain classification (α self-similar + β re-entry into lower degree),
the α-bracket telescoping, the β raw-key dictionary — and this unit
composes that shape AS the induction on n it visibly is: the package
(hMenu-k)+(hExhaust-k) for all k < n, in history-resolved form, is
exactly what a degree-n history consumes at every β-fracture, and the
only genuinely new ingredient at each n is the PER-STAGE
CLASSIFICATION of refine events — which is complete order-1 knowledge
(PROVED, from W-12.A's depth-0 completeness) except at COMPOSITE
stages, which exist precisely when some stage carries ≥ 4 keys (first
instance: the quartic (2,2)). So the distance from the n = 3 theorem
to the FULL uniformity theorem is exactly ONE displayed hypothesis
family — the composite-stage law [GENIND-H] — plus hostile arcs.

---

## S0. RECONCILIATION (what the suppliers proved; what this unit adds)

* **W-12.D** (@ r2 HEAD 99f1813): the reduction. Its per-degree
  hypothesis package {(A0), (A1), (A2)} is what (hMenu-n)+(hExhaust-n)
  abbreviate throughout.
* **W-12.A** (same pin): the order-1 decided-shape count law AT EVERY
  DEGREE — the leaves of the induction, already unconditional.
* **W12-L0 / HM3.A** (pins below): the HISTORY-RESOLVED menus at
  n = 2, 3 — the form the induction's β-consumption needs (aggregate
  menus do not suffice: β-children enter at their own refine loci,
  HM3's β3).
* **HEX3 H-1..H-4 + HM3-1..HM3-4**: the n = 3 instances of every
  scaffold lemma below; each general lemma names its instance.
* **The carry corpus** (J-D0, GRTJC W-6..W-9, WELDMASTER, DULEMMA,
  [W12-H]): consumed ONLY at the composite-stage frontier (S7), where
  it is the counting engine — J-D0 (shape-only counts), W-9
  (dim_K 𝒜(T) = E: the stage slot lattice), JC-LOAD/W-8
  (no-cancellation), (H-e) (order-≥2 σ-decision).
* **QSCOUT22** (@ 240a56c): the (2,2) empirical instrument; S7's
  predictions are keyed to its table, not re-measured here.

This note edits no supplier note. Proposed annex texts: §S9.

## S1. STATEMENT

Conventions as W-12 §S1 (O a complete DVR, residue field F_q, either
characteristic; window N ≥ 2; the recursive OM-convention conservative
read: v(current a₀) ≥ N ⟹ UNDECIDED exit, no tail certification).
A CLUSTER SYSTEM (m, d, N): fix a monic irreducible P̄ of degree d
over F_q and the read's monic lift Φ; states = monic degree-md f over
O/π^N with f̄ = P̄^m, coordinatized by the Φ-adic development
f = Φ^m + Σ_{j<m} a_j Φ^j, a_j ∈ (O/π^N)[x]_{<d} with ā_j = 0
(W-12 S2.2's bijection); q^{dm(N−1)} states; Q := q^d. The full-space
degree-n problem reduces to cluster systems by the level-0 Hensel
product (W12-S2.1). Write c(m) := m(m−1)/2.

> **THEOREM GENIND.A (candidate: the general two-species recursion).**
> For every prime power q, both characteristics, every cluster system
> (m, d, N) with m ≥ 2:
>
> **(I) [the event grammar]** Every state is EXACTLY ONE of:
>   * **DRAIN**: v(a₀) ≥ N (conservative exit); locus q^{d(m−1)(N−1)}.
>   * **DEC**: all residuals separable — an order-1 decided shape;
>     locus = THEOREM W-12.A's law; σ by Ore.
>   * **α(k)**, 1 ≤ k, mk ≤ N−1: one side (0, mk)–(m, 0), integer
>     slope k, residual (y−z)^m, z ∈ F_Q^×; locus
>     (Q−1)·Q^{m(N−1) − k·m(m+1)/2}.
>   * **β**: at least one repeated residual factor, every repeated
>     factor linear with e = 1, and not α: the cluster FRACTURES into
>     child clusters (μ_l, d) at their sides' slopes — the partition
>     datum {μ_l} ∪ {decided piece degrees}, a nontrivial partition of
>     m — plus decided pieces.
>   * **CS** (composite opening): some repeated residual factor
>     (ψ, μ) with μ ≥ 2 and e·deg ψ ≥ 2 — the read exits the order-1
>     calculus into a degree-(e·d·deg ψ) key stage ([W12-H]).
>
> **(II) [α-transport + THE GENERAL BRACKET]** α(k) recenters
> bijectively onto the node D_k ≅ (ghost fiber Q^{k·c(m)}) × (the SAME
> (m, d) system at window N − mk), key-sheared; the α-prefix histories
> aggregate with the bracket
>
>     b_{m,d}(μ) = (Q−1) · Q^{(c(m)+1)·μ − 1}   (μ ≥ 1; b(0) = 1),
>
> exponent coefficient c(m)+1 = m(m−1)/2 + 1 (= 2, 4, 7, 11 at
> m = 2, 3, 4, 5): the n-dependence of HM3-4's (q−1)q^{4μ−1}.
>
> **(III) [β-transport]** each β-genre fibers, route-explicitly, over
> the PRODUCT of its child systems (μ_l, d) at explicitly shifted
> windows and entry loci, with q-power fibers and letter censuses —
> children evolve independently (fracture permanence) and consume the
> lower-degree history-resolved menus.
>
> **(IV) [THE COMPOSITE-STAGE CRITERION]** a CS event at a stage with
> m keys requires a side of abscissa length e·μ·deg ψ ≥ 4, hence
> m ≥ 4; conversely m ≥ 4 realizes CS with positive locus at every q.
> Therefore: composite stages occur at degree n IFF n ≥ 4 (realized
> already at d = 1); n = 2, 3 are composite-free (the PE2-verified
> fact, now a theorem); n = 5 is NOT composite-free despite being
> prime — the criterion is "some stage carries ≥ 4 keys", NOT a
> factorization property of n. First instances at n = 4: the e-first
> genre QRT-G2(h; (1²)) (locus (q−1)q^{4N−5h−3} per center) and the
> f-first genre FULL(k)-(2²) (locus (Q(Q−1)/2)·q^{4N−10k−4},
> Q = q here); at n = 5 the embedded genres of S5.3.
>
> **GRADE: (I), (II), (IV) PROVED below (S2–S5) at order 1, both
> characteristics; (III) proved as the displayed schema with the
> n = 3 routes as consumed instances and the n = 4, 5 instances
> machine-checked pointwise — the general per-route ledger is
> compressed exactly as HEX3-BOX-2 priced its own. Machine-sealed on
> the S10 roster.**

> **THEOREM GENIND.B (the induction; conditional structure displayed
> the montes_unconditional way).** Fix n ≥ 2. Define the package
> P(k) := {history-resolved exact menu (HM3.A-form) + finite
> (A1)-admissible aggregate menu + (A0) + exact-complement (A2)} for
> the degree-k problem. ASSUME:
>   (IH) P(k) for all 2 ≤ k < n;
>   [GENIND-H(n)] for every composite-stage genre realizable at
>   degree ≤ n: (CS-1) the stage transport (the stage system is
>   count-fibred over an explicit lower-complexity system), (CS-2) the
>   stage bracket (the stage's own refine aggregation), (CS-3) the
>   order-≥2 σ-decision theorem ((H-e), = (A0) at the stage's leaves).
> THEN P(n) holds. CONSEQUENTLY, by strong induction from the proved
> bases P(2) (W-11/W12-L0) and P(3) (HEX3+HMENU3): given [GENIND-H(n)]
> for all n, the packages (hMenu-n)+(hExhaust-n) hold for ALL n, and
> THEOREM W-12.D fires at every degree — THE FULL UNIFORMITY THEOREM:
> one R_τ(q) ∈ ℚ(q) per splitting type at every degree, every prime
> power, both characteristics, wild primes included, Σ_τ R_τ = 1.
> At n ≤ 3, [GENIND-H] is EMPTY (S5): the theorem is unconditional
> there and reproduces the proved instances. At n = 4, 5 the entire
> conditional surface is the (2,2)-type stages of S5.3/S7.
>
> **GRADE: the reduction (IH)+[GENIND-H] ⟹ P(n) PROVED at the S6
> level of detail (scaffold); [GENIND-H] OPEN (the frontier), with
> the (2,2) instance attacked in S7.**

## S2. LEMMA GENIND-1 (the species classification; HM3-1 generalized)

[body in S2 below — statement, proof, and the fracture-permanence
lemma]

## S3. LEMMA GENIND-2 (α-transport + the general bracket; HEX3 H-2 +
HM3-2 + HM3-4 generalized)

[body]

## S4. LEMMA GENIND-3 (β-transport: the fracture fibration schema;
HEX3 H-3 + HM3-3 generalized) and LEMMA GENIND-0 ((A1) product
stability)

[body]

## S5. THE COMPOSITE-STAGE CRITERION (THEOREM GENIND.A(IV)) and the
simple-stage layer

[body; S5.3 = the n = 4, 5 genre tables with flagship closed forms]

## S6. PROOF OF THEOREM GENIND.B (the scaffold assembled)

[body]

## S7. THE COMPOSITE-STAGE LAW [GENIND-H] DISPLAYED + THE (2,2)
BRACKET ATTEMPT (the crown target)

[body; the fibration lemma proved, the transport candidate, the exact
obstruction boxed, predictions keyed to QSCOUT22]

## S8. HONEST BOXES

[body]

## S9. CONSUMERS + PROPOSED ANNEXES

[body]

## S10. THE SEALED BATTERY (two-commit; verdict from artifacts)

[roster, families, preregistered predictions, teeth]

## S11. VERDICT (commit 2 — from the committed artifacts)

PENDING.
