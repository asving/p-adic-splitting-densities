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

> **LEMMA GENIND-1.** In the cluster system (m, d, N), m ≥ 2:
> (i) [partition] every state is exactly one of DRAIN / DEC / α(k) /
> β / CS as in GENIND.A(I), and the α-locus law is
> (Q−1)·Q^{m(N−1) − k·m(m+1)/2};
> (ii) [α preserves the cluster] the α(k)-recentering is a bijection
> of the z-slice onto the node D_k := {v(a_j) ≥ (m−j)k + 1 ∀j};
> (iii) [fracture permanence] after a β-event the separation
> valuations of the child clusters are CONSTANT along the rest of the
> chain: every later recentering is strictly deeper than every
> separation depth, so children never re-merge, each child's
> continuing read is a function of that child's own state alone, and
> the top-level chain grammar is α* [optional fracture, then the
> children's independent grammars] — two species and nothing else.

*Proof.* (i) The read is deterministic: the drain rule fires first
(v(a₀) ≥ N); otherwise the exact polygon is computed (exactness of the
hull with window-hidden points: every hull line lies weakly below the
chord from (0, v(a₀)) to (m, 0), hence strictly below height N, so a
point with v(a_j) ≥ N is strictly above every candidate line — the
w12 reader's mechanics, HEX3 S2 verbatim at general m); per side the
residual over F_Q factors uniquely; the residual trichotomy per factor
(separable / repeated linear on e = 1 / repeated with e·deg ψ ≥ 2) is
exhaustive by definition, and W-12 S1's [r1 F3]-corrected taxonomy
says exactly: separable factors are Ore-decided pieces, repeated
linear factors on e = 1 sides recenter (order 1), everything else
repeated opens a composite key of degree e·d·deg ψ > d. α is the case
"one side, integer slope, residual (y−z)^m" — the unique case in
which the fracture partition is the trivial partition (m). The
α-locus count is the S2.2 slot count: m pinned digits (the
coefficients of (y−z)^m at the m lattice points j = 0..m−1, one
letter z ∈ F_Q^×: the pins are universal polynomial identities in z,
degenerating but never merging in small characteristic — J-D0's
blindness, HEX3 S2's (α) bullet at general m), all deeper digits
free: Q^{Σ_j (N−1−(m−j)k)} = Q^{m(N−1) − k·m(m+1)/2}. (ii) is HEX3
H-2(iii)'s computation at general m: recentering by ẑπ^k cancels all
m pinned digits (the binomial identities Σ_i C(·)z^i from
(y−z)^m expanded at y = z + ·, valid in every characteristic), is
injective (a shift), and #slice = (Q−1)·Q^{m(N−1)−k·m(m+1)/2}/(Q−1) =
#D_k — a bijection. (iii) is HM3-1(iii)'s valuation argument at
general m: at the fracture, the polygon of the recentered/scaled
frame splits the roots into groups by valuation (one group per side,
one subgroup per residual root); for a child C entering at depth k_C,
every non-C root differs from the C-cluster at valuation exactly its
separation depth s ≤ k_C, while all subsequent recenterings within C
have v(s′) > k_C ≥ s — so the separation digits are never touched:
the hull of the full frame remains [child hull, sheared] ∪ [the
other sides], with residual coefficients equal to the child's up to
the unit Π(−ρ̄_i) of the split-off factors' values (LEMMA W12-L1(b)'s
computation, product form: letters move by a unit, hulls/lattice
points/separability types do not). Hence the continuing read of C is
the (μ_C, d) system's read of C's own state, and no later event can
involve two children at once. ∎

The n = 3 instances: (i) = HEX3 H-1; (ii) = HEX3 H-2(iii); (iii) =
HM3-1(iii). At n = 2, (iii) is vacuous (no nontrivial fracture) —
which is why W-11 never needed it.

## S3. LEMMA GENIND-2 (α-transport + the general bracket; HEX3 H-2 + HM3-2 + HM3-4 generalized)

> **LEMMA GENIND-2.** (a) [window coherence + shear] With
> σ_k(a_j) := a_j/π^{(m−j)k} mod π^{N−mk} coordinatewise: the chain of
> X ∈ D_k and the chain of σ_k(X) (a window-(N−mk) state of the same
> (m, d) system) correspond step for step, heights shearing by
> (j, v) ↦ (j, v − (m−j)k); every consulted digit of X sits strictly
> below the ghost zone {≥ N − jk} at abscissa j; each scaled state has
> exactly Q^{k·c(m)} ghost-fiber preimages (Σ_{j<m} jk = k·m(m−1)/2
> ghost slots), all key-constant. Hence the α(k)-slice's
> history-resolved menu = (Q−1)·Q^{k·c(m)} × the window-(N−mk) menu,
> key-sheared.
> (b) [the bracket] Σ over all finite sequences (k₁, …, k_r), k_i ≥ 1,
> Σk_i = μ, of Π_i (Q−1)Q^{c(m)·k_i} = (Q−1)·Q^{(c(m)+1)μ−1} =:
> b_{m,d}(μ).

*Proof.* (a) The three parts are HEX3 H-2(i)(ii)(iii) with the n = 3
exponents replaced by their general forms, plus HM3-2's upgrade of the
correspondence from drain-verdict resolution to KEY resolution. Ghost
zones: along any chain from D_k every recentering has v(s) ≥ k+1; the
consulted heights at abscissa j are ≤ the hull height ≤ (m−j)(N−1)/m
(convexity from (0, ≤ N−1) to (m, 0)), and (m−j)(N−1)/m < N − jk for
all 0 ≤ j < m and mk ≤ N−1 (cross-multiply: m(N−jk) − (m−j)(N−1) =
j(N−1−mk) + m ≥ m > 0; at j = 0 it reads N−1 < N; the HEX3 [r1 F1]
corrected pairing, generalized — the ghost
zone at abscissa j is {≥ N − jk}, deepest at the constant coefficient
j = 0 which has NO ghosts). Updates: the recentering substitution
x ↦ x + s (v(s) ≥ k+1) determines each a_j′ mod π^{N−jk} from the
a_{j′≥j} mod their own windows (ring homomorphism per quotient; the
binomial update matrix is triangular with unit diagonal), so ghost
digits never contaminate consulted windows — in both ring types
(carries move upward only). Shear/scaling: f(π^k(y + s̃)) =
π^{mk}·f̃(y + s̃) makes recentering commute with σ_k; hulls, lattice
points, side subdivisions and residual positions are preserved by the
affine-in-j map; v(a₀) ≥ N ⟺ v(ã₀) ≥ N−mk. Fibers: coordinate j
carries jk ghost digit-slots of size Q each. The count of ghost slots
and the bijection (ii) of GENIND-1 give the displayed menu transport.
(b) Generating function, exactly HM3-4's: one step contributes
A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k = (Q−1)Q^c x/(1−Q^c x) (c := c(m));
chains contribute A₁/(1−A₁) = (Q−1)Q^c x/(1 − Q^{c+1}x), whose
x^μ-coefficient is (Q−1)Q^{(c+1)μ−1}. ∎

**Instances (the exponent's n-dependence displayed).** c(m)+1 = 2 at
m = 2 (W-11/HEX3-S4's R-recursion telescoping coefficient
(q−1)q^{2l−1}), 4 at m = 3 (HM3-4's (q−1)q^{4μ−1} — verified on 41
rows at the HMENU3 seal), 7 at m = 4, 11 at m = 5 (machine: GT-AGGDEEP
at n = 4, 5, this battery). At d ≥ 2 the same formulas hold in
Q = q^d (roster limit: the battery exercises d = 1 plus one (m, d) =
(2, 2) targeted row; GENIND-BOX-3).

## S4. LEMMA GENIND-3 (β-transport: the fracture fibration schema; HEX3 H-3 + HM3-3 generalized) and LEMMA GENIND-0 ((A1) product stability)

### S4.1 LEMMA GENIND-3

> **LEMMA GENIND-3.** Fix a β-genre at the (m, d, N) system: a polygon
> P with sides S₁, …, S_r, per-side residual factorization types with
> repeated factors all linear on e = 1 sides — child data
> (μ_l, k_l)_l (child sizes and entry depths, k_l = the slope of the
> child's side; children on one side share its slope) — and decided
> pieces (the separable factors). Then the genre's locus fibers over
>
>     Π_l [ the (μ_l, d) cluster system at window M_l ],
>
> M_l = N − (Σ_j μ_j k_j + Σ_pieces deg·slope-mass of the frame at
> S_l's scale) — the explicit affine window of the scale-then-Hensel
> extraction at the child's frame — with fiber = (letter census of the
> genre: vertex units, child letters z_l, decided-piece residual
> letters) × Q^{(affine exponent in the genre parameters)}: the free
> digits of the decided pieces and the ghost digits of the scalings.
> Children entering at their own refine locus carry the entry datum j
> into the lower system's history key (the β3 mechanism). Drain
> composition: the frame drains iff some child drains; decidedness:
> the frame is decided iff every child is (and then σ = ⊎_l σ_l ⊎
> {decided pieces' Ore types}).

*Proof (schema; instance-proved, machine-checked pointwise).* Three
steps, each the general form of an n = 3 route: (1) RECENTER +
SCALE: for the side S_l of slope k_l (integer, e = 1), recenter at
the child's residual root (ẑ_l π^{k_l}) and scale x = π^{k_l}y: by
GENIND-2(a)'s mechanics the frame becomes a window-(N − m·k_l)
level-0 frame whose reduction is ȳ^{μ_l}·(separable factors with the
other letters as roots — the other children sit at valuation 0 of
this frame if on the same side, at their own slopes otherwise).
(2) HENSEL SPLIT: LEMMA W12-S2.1 at the scaled frame splits the state
into the product of its branch states — the child (μ_l, d) blocks and
the decided pieces — bijectively with multiplicative count transport;
this is where the level-0 product structure re-enters BELOW level 0,
exactly as W12-L1(a) did for n = 3's DBL. (3) READ EQUIVALENCE: by
GENIND-1(iii) the continuing read of each child block equals the
child system's own read with letters unit-scaled (W12-L1(b)'s
computation, product form) — so histories, leaves, drains and σ
transport verbatim, and the frame's raw key is the dictionary image
of the children's (hist, leaf) tuples (HM3.A's dictionary, one entry
per genre). The fiber count per genre is the S2.2 slot count of the
genre's pinned/priced/free digits, an affine-exponent q-power times
the letter census — the same bookkeeping that produced HEX3 H-3's
three routes; the general per-route ledger is compressed into this
schema plus: the three n = 3 routes PROVED and sealed (HEX3/HMENU3,
consumed at pin), and the n = 4, 5 depth-0 genres checked POINTWISE
by this battery (GT-BETA: Hensel product reconstruction + child
re-read + drain/σ composition, member by member). ∎

**Honesty note (the GENIND-3 grade).** What is proved outright at
general (m, d): steps (1)–(3) as stated — each is a supplier lemma's
argument with m, d as parameters, none uses n = 3 specifics. What is
NOT written here: the closed-form fiber exponent of every genre at
every degree (there are finitely many genres per degree; each is a
mechanical S2.2 evaluation, as S5.3 does for the n = 4, 5 flagship
genres). A hostile pass should attack the ledger compression exactly
as HEX3-BOX-2 invited: (a) onto-ness of the route maps at multi-child
genres, (b) the M_l window bookkeeping when children sit on different
sides, (c) the unit-scaling of letters when several pieces split at
once. The pointwise machine leg is designed so that an error in ANY
of (a)–(c) at n ≤ 5 surfaces as an integer mismatch.

### S4.2 LEMMA GENIND-0 ((A1) product stability)

> **LEMMA GENIND-0.** Finite products, finite disjoint unions, and
> affine re-parameterizations (unimodular integer changes of
> coordinates with shifts, e.g. (w₁, w₂) ↦ (w₁, δ = w₂−w₁−1)) of
> (A1)-admissible family data are (A1)-admissible: parameter sets
> stay finite unions of shifted products of arithmetic progressions;
> exponents ℓ = Σ ℓ_l stay affine with strictly positive integer
> coefficients after coordinate normalization; c_F = Π c_{F_l};
> visibility ν = max_l ν_l is handled by splitting the parameter set
> along the (finitely many) affine dominance regions, each rewritten
> as a shifted product by the δ-coordinate trick.

*Proof.* Products and unions: coordinatewise. Positivity: each ℓ_l is
affine with positive coefficients in its own variables; the
concatenated variable set keeps them. Dominance regions: for two
affine forms ν₁, ν₂ with integer coefficients, {ν₁ ≥ ν₂} ∩ (shifted
product) is a finite union of shifted products: induct on dimension,
solving ν₁ − ν₂ = δ ≥ 0 by the substitution used at W-12 S3.4's
2SIDED instance ((w₁, w₂) = (w₁, w₁+1+δ)); finitely many regions for
finitely many pairs. ν = the region's dominating form, affine. ∎

(Consumed by S6 wherever a β-family multiplies lower menus; the n = 2
instance is W-12 S3.4's own 2SIDED handling, the n = 3 instances are
HM3.B's B-families.)

## S5. THE COMPOSITE-STAGE CRITERION (THEOREM GENIND.A(IV)) and the simple-stage layer

### S5.1 The criterion, proved

*Necessity.* A CS event is a repeated residual factor (ψ, μ) with
μ ≥ 2 and e·deg ψ ≥ 2 on a side of the stage polygon. The side's
abscissa length is e·g with g ≥ μ·deg ψ, so length ≥ e·μ·deg ψ ≥
2·2·1 = 4 (case e ≥ 2, ψ linear) or ≥ 1·2·2 = 4 (case e = 1,
deg ψ ≥ 2) — in every case ≥ 4. The polygon of a stage with m keys
spans abscissas [0, m]: m ≥ 4. A stage with m keys of degree D inside
a degree-n read has mD ≤ n, so n ≥ 4D ≥ 4. Refinements only shrink or
preserve multiplicities (α preserves m; β-children have μ_l < m;
composite children have m′ = μ ≤ m/(e·deg ψ) ≤ m/2), so ALL stages of
a degree-≤3 read have m ≤ 3: n = 2, 3 are composite-free — the
ledger's PE2-verified observation, now a theorem, and the reason the
n ≤ 3 program never consulted [W12-H].

*Sufficiency (realization at every n ≥ 4, every q, both
characteristics).* At d = 1, m = 4: the QRT-G2(h; (1²)) stratum
exists with positive locus (q−1)q^{4N−5h−3} > 0 (W-12 S2.5, PROVED);
at n > 4 pad with n−4 distinct simple roots at level 0 (Hensel
product, W12-S2.1) or realize the embedded genres of S5.3 inside the
full cluster. ∎

**The criterion in one line: composite stages exist at degree n ⟺
n ≥ 4 (⟺ some stage can carry ≥ 4 keys).** The charge's candidate
criterion "n has a nontrivial factorization d·e with e ≥ 2" is
REFUTED: n = 5 is prime yet composite-bearing — the key degree of a
composite stage divides no invariant of n; it consumes 4 of the n
abscissa units and leaves the rest to split off. (Machine: GT-CRIT —
n = 3 rows show ZERO CS events; n = 4, 5 rows show CS events exactly
at the S5.3 genre grammar, with two flagship laws per degree checked
both directions.)

### S5.2 The simple-stage layer (what is unconditional at every n)

Call a history SIMPLE if no CS event occurs along it. The simple
slice of the degree-n problem is generated by exactly the S2–S4
machinery over the W-12.A leaves — every ingredient PROVED:
* the leaves: THEOREM W-12.A (all degrees, order 1) [pin];
* the α-aggregation: LEMMA GENIND-2 (bracket b_{m,d});
* the β-fibrations: LEMMA GENIND-3 over the LOWER-degree simple
  slices (strong induction; at n ≤ 3 the simple slice is everything
  and the induction grounds in W-11/HEX3/HMENU3);
* (A1)-form: LEMMA GENIND-0 + the affine exponent bookkeeping
  (window variables enter the exponents with the strictly positive
  integer coefficients displayed in GENIND-2/3);
* (A0) on simple leaves: Ore at the terminal frame + window coherence
  transporting the certificate (W-12 S2.3 + GENIND-2(a), exactly
  HM3.C's S5.2 argument at general n);
* drainage of the simple slice: the first-step recursion
  u_{m,d}(N) = Q^{(m−1)(N−1)} + Σ_k (Q−1)Q^{k·c(m)}·u_{m,d}(N−mk) +
  Σ_{β-genres} (route prefactor)·[children: at least one drains,
  inclusion–exclusion over the child systems' u's and totals] — every
  term supplied by GENIND-2/3 + IH, telescoping by GENIND-2(b)
  exactly as HEX3 S5.2 (the α-part's telescoped coefficient is
  b_{m,d}); vanishing: u/Q^{m(N−1)} → 0 by induction (head Q^{−(N−1)};
  α-terms geometric; β-terms lose at least one child's full mass by
  the IH bound — each contributes O(poly(N)·Q^{−(N−c)}) relative
  mass).

So: **THEOREM GENIND.C (the simple-stage layer).** For every n, the
simple slice carries a finite (A1)-admissible menu with exact counts,
(A0), and an exactly-recursed conservative drain, unconditionally on
[GENIND-H] (conditional only on the S0 supplier pins). For n ≤ 3 the
simple slice is the whole problem and GENIND.C reproduces the proved
packages P(2), P(3). For n ≥ 4 the complement of the simple slice —
the CS strata — has EXACTLY KNOWN entry mass (the opening loci are
order-1 shapes priced by W-12.A: e.g. Σ_h (q−1)q^{4N−5h−3} at the
quartic e-first genre) but positive density: it can NOT be absorbed
into (A2) by bounds, which is precisely why [GENIND-H] is
load-bearing and not a technicality. GRADE: proved modulo the
GENIND-3 ledger honesty note; machine-checked at n = 4, 5 as S10.

### S5.3 The n = 4 and n = 5 depth-0 CS genre tables (flagship laws)

Per center, window N, d = 1; z-letters ∈ F_q^×; ψ = irreducible
quadratics over F_q (#ψ = q(q−1)/2). Derivations: direct S2.2 slot
counts (this session; the two n = 4 laws are W-12 S2.5's and its
(2²) sibling).

**n = 4 (the whole polygon is the side):**
* **CS4-E(h)** [e-first: e = 2, ψ linear, μ = 2; = QRT-G2(h;(1²))]:
  slope h/2, h odd, residual (y−z)²: (q−1)·q^{4N−5h−3}. [pin: proved
  at the w12 seal; QSCOUT22's GENRE E entry.]
* **CS4-F(k)** [f-first: e = 1, residual ψ², deg ψ = 2]: integer
  slope k, heights (4k, 3k, 2k, k), L = 4:
  (q(q−1)/2)·q^{4N−10k−4}. [QSCOUT22's GENRE F entry.]

**n = 5 (the side has length 4; the fifth root splits off — the
criterion's "consumes 4, leaves the rest" made flesh):**
* **CS5-V1E2(h)**: vertex at 1, side (1, 2h)–(5, 0), h odd, e = 2,
  residual (y−z)² on lattice {1, 3, 5}; v(b₀) strictly above the
  extended side (≥ (5h+1)/2) and NOT window-zero (else DRAIN fires
  first): (q−1)·q^{4-coordinate exponent}·(q^{N−(5h+1)/2} − 1) with
  4-coordinate exponent = (N−1−2h) + (N−(3h+1)/2) + (N−1−h) +
  (N−(h+1)/2) = 4N − 2 − 3h − (4h+2)/2 = 4N − 5h − 3, i.e.
  **(q−1)·q^{4N−5h−3}·(q^{N−(5h+1)/2} − 1)** — the CS4-E law times
  the b₀ headroom factor (the split root's fiber).
* **CS5-V4E2(v₄, h)**: vertex at 4, left side (0, v₄+2h)–(4, v₄),
  h odd, e = 2, residual (y−z)² (pins at abscissae 0, 2), right side
  (4, v₄)–(5, 0) a split simple root (letter at the vertex):
  **(q−1)²·q^{5N−5v₄−5h−4}**, v₄ ≥ 1, VERTEX CONDITION h ≥ 2v₄+1
  (hull convexity at (4, v₄): the left drop (v₀−v₄)/4 must exceed the
  right drop v₄ — caught by the battery's smoke: at h < 2v₄+1 the
  same digits read as a single e = 5 decided side), visibility
  v₀ = v₄+2h ≤ N−1: first visible at N = 8 — beyond this roster's
  windows, so machine-checked as PREDICTED-ABSENT (its law is
  derivation-only here).
* Non-flagship (classified, laws not preregistered): CS5-V1E1-(2²)
  (side (1, 4k)–(5, 0), integer slope, residual ψ², first visible
  N = 7 — the b₀ headroom 5k+1 ≤ N−1), CS5-V4E1-(2²), CS5-FULL-(2²1)
  (full side, residual ψ²·(y−w), N ≥ 6) — all beyond this roster's
  windows, enumerated in the criterion grammar (GT-CRIT accepts
  exactly the grammar, so an unlisted CS genre on any row is a
  violation, and a listed-but-early genre appearing below its
  visibility floor is one too).

**Deeper CS openings** (behind α/β prefixes) inherit these tables at
sheared windows through GENIND-2/3 — self-similarly, no new genre
(machine: the full-history classifier tallies CS events at all
depths; every one must parse in the grammar).

## S6. PROOF OF THEOREM GENIND.B (the scaffold assembled)

Fix n; assume (IH) [P(k), history-resolved, for k < n] and
[GENIND-H(n)].

*Step 1 (level 0).* By W12-S2.1 the degree-n problem is the disjoint
union over level-0 configurations of products of cluster systems
(m_i, d_i) and simple branches. Configurations with every m_i·d_i < n
are products of strictly-lower-degree data: (IH) supplies each
factor's package; LEMMA GENIND-0 multiplies the menus, W-12.A's
level-0 censuses supply C₀(q); drains compose by "some factor
drains". The only configurations not covered by (IH) are the full
clusters m·d = n, m ≥ 2 (and the trivial separable ones, decided at
level 0).

*Step 2 (the full cluster: menu).* In the (m, d, N) system, LEMMA
GENIND-1 partitions every state; the recursion on histories
terminates because α strictly reduces the window (GENIND-2), β
strictly reduces every child's degree (GENIND-1(iii) + GENIND-3, then
(IH) at the children — history-resolved, so children entering at
their own refine loci are consumable, the β3 mechanism), and CS
events exit into [GENIND-H]'s stages, whose (CS-1)+(CS-2) supply the
stage's own resolved menu and (CS-3) its σ/(A0). Aggregating: the
α-prefixes by GENIND-2(b)'s bracket (a finite relabeling per family,
HM3-BOX-5's pedantry inherited); the β-genres by GENIND-0 products of
the children's finite (A1) menus; the CS stages by [GENIND-H]. Every
family's data is a single q-polynomial expression by construction
(slot counts + censuses; J-D0's frame) — q- and characteristic-
uniform. Disjointness: the deterministic read keys partition
(GENIND-1(i)). This is (hMenu-n) = (A1) + the history-resolved form
of P(n).

*Step 3 (A0).* Order-1 leaves: Ore at the terminal frame + window
coherence (S5.2 bullet). CS leaves: (CS-3) = (H-e). Products: σ and
certificates compose branchwise (W12-S2.1, GENIND-3). 

*Step 4 (A2).* r(N) = conservative drains + window-boundary (tail)
families + CS-internal residues. The simple part: GENIND.C's
recursion telescopes and vanishes; the boundary families route
through (A2) exactly as W-12 S3.4 [r2] displays at n = 2, 3 (their
masses are the transported SPLIT-TAIL-type aggregates, N-dependent
counts, vanishing after normalization); the CS-internal part:
(CS-1)+(CS-2) resolve each stage into its own decided menu + drain,
with the stage drains vanishing by the same telescoping run inside
the stage ([GENIND-H]'s content). Summing: r(N)/q^{nN} → 0, with the
same exact-complement sharpening HM3.C S5.3 achieved at n = 3
wherever the stage laws are exact.

*Step 5 (fire W-12.D).* P(n)'s (A0)+(A1)+(A2) are W-12.D's
hypotheses at degree n: THEOREM W-12.D (PROVED, @ pin) yields one
R_τ(q) ∈ ℚ(q) per splitting type of degree n, = the Haar density,
same expression at every prime power and characteristic, Σ_τ R_τ = 1.
Strong induction over n completes THEOREM GENIND.B. ∎

**Where the conditionality lives, exactly.** (IH) grounds at the
PROVED P(2), P(3). Steps 1–2's order-1 content is S2–S5 (this note,
proved). The ONLY consumption of [GENIND-H(n)] is: Step 2's CS-stage
menus, Step 3's CS-leaf σ, Step 4's CS-internal drainage. At n ≤ 3
these consumptions are vacuous (S5.1) — GENIND.B degenerates to the
proved n ≤ 3 chain, which is the reduction's non-vacuity check.

## S7. THE COMPOSITE-STAGE LAW [GENIND-H] DISPLAYED + THE (2,2) BRACKET ATTEMPT (the crown target)

### S7.1 What a composite stage needs, precisely

A CS opening hands the read a stage (m′, D′, E, K): key polynomial
Φ′ of degree D′ = e·d·deg ψ, stage multiplicity m′ = μ, value-group
index E = e (the new denominator), stage residue field K
(|K| = q^{d·deg ψ}). [GENIND-H] at this stage is:
* **(CS-1) the stage transport** — the order-≥2 analogue of the
  per-center transport: the opening locus fibers as (letter census) ×
  q^{affine} × [the stage state space], with the stage states = the
  Φ′-adic development (A_{m′−1}, …, A₀), deg A_j < D′, carrying ONE
  K-digit slot per (abscissa, v′-height) in the stage's value
  normalization — and the stage read (polygon, residuals over K,
  refine events) is count-isomorphic to a degree-m′ cluster-system
  read over K at an explicit stage window.
* **(CS-2) the stage bracket** — the stage's own α-aggregation:
  b_{m′,K}(μ″) = (|K|−1)·|K|^{(c(m′)+1)μ″−1} in stage units, i.e.
  GENIND-2(b) run inside the stage.
* **(CS-3) the σ-decision** — the order-≥2 GMN leaf theorem
  ([W12-H](H-e)): separable stage residuals ⟹ σ-decided with (e·E,
  f·[K-ext]) read off, for ALL disc ≠ 0 lifts — (A0) at the stage.

**Where the carry corpus delivers (the displayed mechanism).** The
stage slot claim in (CS-1) — one K-digit per (abscissa, v′-height) —
is exactly COROLLARY W-9 + FINDING JC-F1's **dim_K 𝒜(T) = E**
(GRTJC @ pin): the transported carry algebra at the stage is the
twisted group algebra K^c[ℤ/E], E graded K-lines per integer height —
E slots per old v-unit, one per v′-unit. The stage residual reads are
the GRADED reads with no cancellation across the ℤ/E-degrees —
JC-LOAD/W-8's warrant (wild composite stages included). And the
letters the stage read consumes are ζ-twisted by the carry cocycle
(W-9(iii)) — units, which COUNTS NEVER SEE: LEMMA J-D0 lifts the
count laws over the twist. So the corpus supplies the stage's
SLOT GEOMETRY and LETTER-BLINDNESS outright; what it does not supply
by itself is the step-for-step READ CORRESPONDENCE (the stage
analogue of W12-L1(b)'s case check) — that is the exact residue of
(CS-1), and (CS-3) is its own theorem ((H-e), open).

### S7.2 LEMMA GENIND-4 (the (2,2) stage fibration — PROVED)

The first instance, the quartic e-first genre CS4-E(h) (= QSCOUT22
GENRE E): m′ = 2, D′ = 2, E = 2, K = F_q, Φ′ = x² − s, s = ẑπ^h.

> **LEMMA GENIND-4.** On the CS4-E(h, z) opening locus (per center,
> (q−1)q^{4N−5h−3} members), the Φ′-adic development f = Φ′² +
> A₁Φ′ + A₀ (A₁ = α₁x + α₀, A₀ = β₁x + β₀) is a TRIANGULAR digit
> bijection from the opening coordinates (b₃, b₂, b₁, b₀):
>
>     b₃ = α₁,  b₂ = α₀ − 2s,  b₁ = β₁ − sα₁,  b₀ = β₀ − sα₀ + s²,
>
> with stage-initial budgets v(α₁) ≥ (h+1)/2, v(α₀) ≥ h+1,
> v(β₁) ≥ (3h+1)/2, v(β₀) ≥ 2h+1 — total free exponent 4N−5h−3, the
> opening locus EXACTLY (no overcount, no undercount). In doubled
> units dv := 2v (the stage normalization v′, E = 2), each coordinate
> A_j carries ONE q-digit slot per integer dv-height (h odd forces
> the parities apart: even dv-slots from the constant coefficient,
> odd from the x-coefficient — the ℤ/2 carry grading of W-9 made
> literal), and the stage-initial node is
>
>     { dv(A₀) ≥ 2S+1, dv(A₁) ≥ S+1 }  with  S := 2h
>
> — the W-11 refine node C(2S+1, S+1) ON THE NOSE, in stage units.

*Proof.* The development identities are the direct expansion of
(x²−s)² + (α₁x+α₀)(x²−s) + (β₁x+β₀); triangularity (each b_j = its
A-coordinate + terms in later coordinates) makes the map a bijection
of digit spaces. Budgets: the opening pins v(b₃) ≥ (h+1)/2,
digit_h(b₂) = −2z, v(b₁) ≥ (3h+1)/2, digit_{2h}(b₀) = z² (W-12 S2.5)
translate coordinatewise: α₁ = b₃; α₀ = b₂ + 2s has its h-digit
cancelled (−2z + 2z), so v ≥ h+1; β₁ = b₁ + sα₁ has v ≥
min((3h+1)/2, h + (h+1)/2) = (3h+1)/2; β₀ = b₀ + sα₀ − s² has its
2h-digit cancelled (z² + 0 − z²), so v ≥ 2h+1. Free-digit total:
(N − (h+1)/2) + (N−1−h) + (N − (3h+1)/2) + (N−1−2h) = 4N − 5h − 3 ✓
— matching the opening law exactly, which is the no-over/undercount
check. dv-arithmetic: dv(a·x + b) = min(2v(a) + h, 2v(b)) (the root
has v = h/2); 2v(b) is even, 2v(a)+h odd — distinct parities, no
ties, one slot per integer dv. Node: dv(A₁) ≥ min(2·(h+1)/2 + h,
2(h+1)) = 2h+1 = S+... = 2h+1; dv(A₀) ≥ min(2·(3h+1)/2 + h,
2(2h+1)) = 4h+1. With S = 2h: (2S+1, S+1) = (4h+1, 2h+1). ∎

(QSCOUT22's LEMMA Q22-B states the same budgets from the scout side;
the two derivations were made independently — the numbers agree,
disclosed as a cross-check, not two units citing one computation.)

### S7.3 The (2,2) bracket: candidate theorem, and what resists

> **CANDIDATE THEOREM GENIND-5 (the (2,2) stage law; NOT proved —
> boxed at the displayed obstruction).** The CS4-E(h) stage read is
> count-isomorphic to the W-11 n = 2 system over F_q in dv-units at
> the stage node C(4h+1, 2h+1): its history-resolved menu = W12-L0's
> laws with (N, depth) read in dv-units and the PARITY-RAGGED window
> (even slots end at dv = 2N−2, odd at 2N+h−2; uniform statements
> hold below dv = 2N−2, the ragged band routes through (A2) as a
> boundary family); in particular THE COMPOSITE-STAGE BRACKET IS THE
> m = 2 BRACKET IN STAGE UNITS:
>
>     b_stage(μ) = (q−1)·q^{2μ−1}   (dv-depth aggregation),
>
> the (CS-2) instance — same exponent coefficient c(2)+1 = 2 as the
> order-1 quadratic cluster, because W-9's dim = E already flattened
> the stage lattice to one slot per unit height. Stage leaves map to
> σ by: stage-RAM (odd dv-side) ↦ {(4,1)} (e doubles again);
> stage-2SIDED/SPLITEQ ↦ {(2,1),(2,1)}; stage-INERTDEEP ↦ {(2,2)};
> stage-refine ↦ recurse with b_stage. [Wild p = 2 included: the
> pins degenerate (−2z ≡ 0), the slot counts do not — J-D0.]

**What is PROVED toward it:** GENIND-4 (the fibration + node + slot
grading — the stage's (A1)-side geometry), so the first stage-polygon
classification is well-posed. And the stage-refine RECENTERING
Φ′ ↦ Φ′ + w (deg w ≤ 1) is computed here to be triangular-WITH-CARRY:
expanding f = (Φ′+w)² + A₁″(Φ′+w) + A₀″ and reducing mod Φ′ gives
A₁″ = A₁ − 2w + c, A₀″ = A₀ − wA₁ + w² − c·(…) with c = the Φ′-carry
of the degree-2 overflow of wA₁ (the x² ≡ s (mod Φ′) wrap — LITERALLY
the cocycle multiplication of W-9: odd·odd dv-slots landing on even
slots twisted by s). The parities (h odd) keep the carry's landing
slots disjoint from the pinned slots — JC-LOAD's no-cancellation
holds here BY PARITY, elementarily — so the one-step update is again
a digit bijection killing the refined pin: the SINGLE-STEP refine
isomorphism is within reach of exactly the S7.2 computation.

**The EXACT OBSTRUCTION (boxed, not hand-waved):**
* **(OB-a) chain-level window coherence in dv-units.** The one-step
  bijection must be iterated: ghost zones of the stage (which
  dv-digits of A₁, A₀ a depth-κ stage chain may consult) need the
  H-2(i) argument re-run on the RAGGED window (even/odd slots end at
  different dv-heights). Until that ledger is written, deep stage
  histories might consult a ragged-band digit and break uniformity
  at the last ⌊h/2⌋-ish window slots. Expected resolution: the
  consulted-height bound (m−j)(window)/m of GENIND-2 lands below
  BOTH parities' ends; the n = 3 analogue was exactly HEX3's [r1 F1]
  corner.
* **(OB-b) the stage residual = the block residual up to units, at
  EVERY step.** One step is the parity argument above; the general
  step needs the graded-read identification (W-8/JC-LOAD consumed as
  warrant — accepted 2/2, but its consumption here as a POINTWISE
  digit statement on (α₁, α₀, β₁, β₀) coordinates is a new
  transcription that must be written and machine-checked, not
  cited).
* **(OB-c) σ/(A0) at stage leaves = (H-e)** — open exactly as
  [W12-H] prices it; the COUNT claims of GENIND-5 do not consume it,
  the (A0) claims do.
* **(OB-d) genre F** (residue-field-first, K = F_{q²}) — untouched
  here; QSCOUT22's territory; the analogue of GENIND-5 there has
  K-letters and the F_{q²} censuses.
**Falsifiable predictions handed to QSCOUT22's table** (keyed to its
GENRE E; per opening (h, z), per center, window N, dv-window
M₂ := 2N−2): the stage's undecided (conservative) count =
q^{#A₁-slots} at A₀ ≡ 0: q^{(N−(h+1)/2)+(N−1−h)} = q^{2N−(3h+3)/2};
the first-step stage-RAM(u₂) law (q−1)q^{...} with exponents read
from W12-L0 at (M₂, node S = 2h) — if the scout's measured table
matches these at its smoke rows, GENIND-5's transport is corroborated
before its proof; a mismatch localizes to (OB-a)/(OB-b) and refutes
the candidate as stated.

### S7.4 The general composite-stage law (the [GENIND-H] work order)

The (2,2) pattern generalizes as the work order: at a stage
(m′, D′, E, K), (CS-1) = a GENIND-4-style triangular development
fibration (the entry pins cancel coordinatewise; expected budgets =
the entry law's exponent, the E parities/residues mod E separating
slots — W-9's ℤ/E grading) + the stage read's identification with
the (m′, 1) cluster system over K in v′-units; (CS-2) = GENIND-2(b)
inside the stage: b_{m′,K}(μ) = (|K|−1)|K|^{(c(m′)+1)μ−1}; (CS-3) =
(H-e). Each is per-genre finite work at each degree; the corpus
supplies grading + blindness + no-cancellation; the residue is the
transcription (OB-a)/(OB-b) per genre plus (H-e) once. NOTHING in
the scaffold consumes a stage law before its genre is realized
(criterion, S5.1), so the program is finitely enumerable
degree-by-degree while the SCAFFOLD stays uniform in n.

## S8. HONEST BOXES

* **GENIND-BOX-1 ([GENIND-H] itself).** The composite-stage laws are
  OPEN at every genre; GENIND-5 is a CANDIDATE with its obstruction
  displayed (OB-a..d). No count law at order ≥ 2 is claimed proved.
  THEOREM GENIND.B is a REDUCTION; its unconditional content at
  n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion
  + the opening-mass laws.
* **GENIND-BOX-2 (GENIND-3's ledger compression).** The β-transport
  is proved as a schema with per-route ledgers compressed (S4.1's
  honesty note); hostile targets named there. The n = 4, 5 pointwise
  machine families are the compensating instrument.
* **GENIND-BOX-3 (d ≥ 2 and prime-power coverage).** The battery
  exercises d = 1 clusters at prime q only; general d ≥ 2 (and the
  Q = q^d letter spaces) rests on the proofs' Q-uniformity (the
  arguments never use d = 1) — machine-uncorroborated here beyond the
  w12-sealed order-1 instances; prime-power q rows are carried by the
  supplier batteries (HEX3/HMENU3 up to q = 27).
* **GENIND-BOX-4 (drainage bound at n ≥ 4).** GENIND.C's vanishing
  argument for the simple slice is an induction whose β-term
  bookkeeping is displayed, not expanded per genre; its n ≤ 3
  instances are the proved HEX3.B/W-11(iii). The battery checks the
  EXACT first-step recursion at n = 4, 5, which is stronger at those
  degrees than the bound it feeds.
* **GENIND-BOX-5 (grades).** 0/2, composed this session, no hostile
  arc; every supplier consumed at the pins of S10's PIN family; the
  full-degree corollary inherits the MINIMUM grade over
  {W-11, W-12, HEX3, HMENU3 arcs, this note, and — at n ≥ 4 —
  [GENIND-H] which is OPEN}: i.e. the uniformity theorem at n ≥ 4 is
  a CONDITIONAL STRUCTURE, displayed, not a result.
* **GENIND-BOX-6 (conventions).** The conservative drain convention
  as at HEX3/HMENU3 (v(a₀) ≥ N exits; no tail certification); the
  reader-reimplementation seams (W10-BOX-3 lineage) inherited; the
  n = 3 control ties to the committed hex3 JSON mitigate; oracle
  mixed-characteristic only.

## S9. CONSUMERS + PROPOSED ANNEXES

### S9.1 Proposed annex to W12-BOX-1 / the [W12-H] box (text offered; W12_PROOF not edited)

> **[BOX-1 ANNEX, 2026-08-08, GENIND]** The orders-≥2 program now has
> its INDUCTION: THEOREM GENIND.B reduces (hMenu-n)+(hExhaust-n) for
> ALL n to the per-genre composite-stage package {(CS-1) transport,
> (CS-2) stage bracket, (CS-3) = (H-e)} — with the two-species
> scaffold (α-bracket (Q−1)Q^{(m(m−1)/2+1)μ−1}, β partition-product
> transport), the simple-stage layer, and the criterion "composite
> stages ⟺ some stage carries ≥ 4 keys ⟺ n ≥ 4" PROVED
> (GENIND_PROOF_2026-08-08.md; sealed battery at n = 4, 5, both
> characteristics). The (2,2) stage's fibration + node + ℤ/2 slot
> grading are PROVED (LEMMA GENIND-4); the stage law is CANDIDATE
> GENIND-5, boxed at (OB-a)/(OB-b)/(H-e).

### S9.2 Downstream

1. **QSCOUT22** — S7.3's falsifiable predictions are keyed to its
   GENRE-E table; a confirmed table upgrades GENIND-5 from candidate
   to corroborated-candidate (proof still owed at the boxes).
2. **The [GENIND-H] closure program** — per-genre units: (2,2)-E
   first (GENIND-5's obstruction list is the work order), then
   (2,2)-F (K = F_{q²}), then the n = 5 embedded genres (S5.3's
   grammar), each consuming W-9/J-D0/JC-LOAD as S7.1 displays.
3. **W-13/W-14 naming** — the per-degree instances of GENIND.B at
   n = 4, 5 fire as soon as their [GENIND-H] genres close; no other
   degree-specific work remains (the scaffold is degree-uniform).
4. **Phase-B Lean** — GENIND.B's scaffold is a finite recursion over
   (A1) data: the natural Lean target once the hostile arcs mature
   (math-first: Lean waits).
5. **Public exposition** — at the next milestone fold: the map's
   general-n panel can now show the honest structure (proved
   scaffold + boxed stage laws), per the standing directive.

### S9.3 Conditionality stack (consumed suppliers, as-of pins)

* **THEOREM W-12.D + W-12.A + S2.4/S2.5 + W12-L0/L1** @ w12 seal
  f669cb0 / verdict c16c717 / r1 ba0d1a4 / r2 99f1813 (arc 0/2, PE2
  adjudicated + r2, PE3 owed) — the reduction, the order-1 leaves at
  every degree, the [r1 F3] refine taxonomy, the (1²) frontier law.
* **THEOREM W-11(n = 2)** @ seal 7020ceb / r2 31506b3 / PE3 CLEAN
  839b735 (counter 1/2 — the first clean pass) — through W12-L0 and
  R(M).
* **HEX3 (H-1..H-4, HEX3.A/B/C)** @ seal e3f3459 / verdict 671a126 /
  r1 2580f12 — the n = 3 transport instances, u₃(M), the committed
  species tables (GT-N3TIE's target).
* **HMENU3 (HM3-1..4, HM3.A/B/C/D)** @ seal 64d3ff9 / verdict 625fa49
  (0/2, PE1 = 0C+1G+1m @ f4f7b03, r1 owed) — the two-phase chain
  template, the raw-key dictionary, the n = 3 bracket instance.
* **LEMMA J-D0** @ 1642275/9387eb1 — the count-gauge-blindness frame
  (S7's letter-blindness; the char-tally legs corroborate again).
* **GRTJC W-6..W-9 (ACCEPTED 2/2 @ 83f47f4; JC-F1/JC-F2 [r1/r2])** —
  consumed ONLY in S7's display: dim_K 𝒜(T) = E, the carry cocycle,
  JC-LOAD's no-cancellation. No count law of S2–S6 consumes them.
* **WELDMASTER / DULEMMA / [W12-H]** @ their accepted pins — named in
  S7.1's (CS-1..3) pricing only.
* **QSCOUT22** @ 240a56c (skeleton) — the (2,2) empirical instrument;
  S7.3's predictions target its table; nothing consumed from it.
* **Classical:** Hensel (coprime + monic-factor lifting), Ore/GMN
  order-1, lower-hull geometry, generating functions.

**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
{W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas};
GENIND.A(III) adds the S4.1 ledger-compression honesty; THEOREM
GENIND.B adds [GENIND-H] as its displayed hypothesis; the FULL
uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
weld face inside any count law; grade = composition 0/2.**

## S10. THE SEALED BATTERY (two-commit; verdict from artifacts)

**Runner:** `verification/openmath/genind_checks.py`. Exact integer
arithmetic; deterministic; cypari2 only in GT-ORACLE. Self-contained
reader (fresh same-session code — GENIND-BOX-6's seam), consuming the
suppliers ONLY as md5 pins + the committed hex3 JSON tie. The reader
implements the general recursive conservative read: drain rule first,
exact hull, per-side residuals, α by in-frame recentering, β children
by c = k scaling (D = weighted min) + monic Hensel extraction at
window W − D, CS-EXIT at composite openings.

**Families** (evidence class): GT-PIN [NONE] (5 pins: w11/w12/hex3/
hmenu3 runners + hex3 results JSON); GT-PART [SAME] (partition + the
Zp/Fqt tally equality at every shared (m, q, N)); GT-DEPTH0 [SAME,
both directions]; GT-BDRAIN [SAME] (the n = 4 FULL-side β drain laws
in closed form — the β-transport consuming the PROVED n ≤ 3 drains
R(M)/u₃(M)); GT-ALPHA [SAME, pointwise + fibers + onto]; GT-BETA
[SAME, pointwise Hensel reconstruction]; GT-RECUR [SAME] (α-drain
self-similarity against fully-enumerated reduced windows);
GT-BRACKETID [SYM] (LEMMA GENIND-2(b) at m ∈ {2,3,4,5}, μ ∈ {1,2,3},
q ∈ {2,3}); GT-CRIT [SAME]; GT-N3TIE [NONE]; GT-CONS [SAME]
(constructed loci); GT-ORACLE [IND].

**ROSTER (full sweeps, per-center, states = q^{m(N−1)}, both ring
kinds):** n = 3 control: (2,5), (3,4). n = 4: (2,4), (2,5), (2,6),
(3,3), (3,4), (5,3). n = 5: (2,4), (2,5), (3,3). Total 22 sweep rows
= 6,422,014 per-center states [2·23,779 + 2·2,046,835 + 2·1,140,393].
CONSTRUCTED: n=4 α(2) @ (Zp,2,9)
[4,096]; n=5 α(1) @ (Zp,2,6), (Fqt,2,6) [1,024 each], (Zp,3,6)
[118,098]; n=4 BFULL(1) types 22/31/2Q @ (Zp,3,6) [59,049 + 118,098 +
354,294]. ORACLE (Zp): (2,4) n=4, (3,3) n=4, (2,4) n=5 — every DEC
member.

**PRE-SEAL SMOKE + PROBES DISCLOSED** (the runner docstring carries
the same record): smoke run 1 RED with exactly one violation — the
predictor listed V4E2(1,1) at (Zp,2,4,n5), refuted by the trace: the
hull convexity at the (4, v₄) vertex forces h ≥ 2v₄+1, a MATH-side
correction folded into S5.3 (V4E2 first visible at N = 8:
predicted-absent here); smoke run 2 GREEN (736 checks / 0). Three
targeted probes of paths smoke misses: GT-N3TIE clean; GT-ORACLE on
(Zp,2,4,n4) clean (3,264 scored, 0 bad — the full run repeats this
row, disclosed); cost probe (Fqt,2,6,n4) 13.6 s / 0 violations
(verdicts 939,520 DEC / 42,496 DRAIN / 66,560 CS). No full battery
run before the seal.

**PREREGISTERED PREDICTIONS (commit 1; spot values computed from the
sealed predictor pre-run):**
* P-1 [NONE] GT-PIN 0/5.
* P-2 [SAME] GT-PART 0 violations; Zp/Fqt depth-0 tallies IDENTICAL
  at all 11 shared (m, q, N).
* P-3 [SAME] GT-DEPTH0 0 violations both directions. Never-measured
  spots (per center): (·,2,6,n4): ALPHA(1) = 1,024, E4(1) = 65,536,
  F4(1) = 1,024, B2Q(1) = 1,024, DRAIN₀ = 32,768 (the cost probe's
  66,560 CS = E4+F4 exactly); (·,3,4,n4): E4(1) = 13,122, DRAIN₀ =
  19,683, ALPHA/F4/BFULL ABSENT (4k ≤ 3 impossible); (·,5,3,n4):
  E4(1) = 2,500, DRAIN₀ = 15,625; (·,2,5,n5): V1E2(1) = 12,288,
  DRAIN₀ = 65,536, V4E2 ABSENT (vertex condition); (·,3,3,n5): NO CS
  key at all (V1E2 headroom = 0), DRAIN₀ = 6,561.
* P-4 [SAME] GT-BDRAIN 0 violations — spot: (·,2,6,n4) B2Q(1) drained
  = 512 of 1,024 (M = 2: R(2) = 2 of q^{2(M−1)} = 4 block states).
* P-5 [SAME] GT-ALPHA 0 violations — every fiber exactly
  q^{k·m(m−1)/2}, scaled states onto.
* P-6 [SAME] GT-BETA 0 reconstruction failures; GT-RECUR 0 (α-drain
  = (q−1)q^{k·c(m)}·u_m(N−mk) exactly, per realized k).
* P-7 [SYM] GT-BRACKETID 24/24 identities.
* P-8 [SAME] GT-CRIT: ZERO CS events on all four n = 3 rows; every
  n = 4/5 CS event obeys μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame; no
  genre outside the S5.3 grammar.
* P-9 [NONE/IND] GT-N3TIE: both legs exact (HEX3 S5.1 closed forms
  AND the committed JSON species tables, key by key); GT-ORACLE
  0 bad on all three rows.
* P-10 teeth at EXACTLY: GT-T-ALPHA = 12 (8 sweep rows with α keys +
  4 constructed legs), GT-T-CS = 12 (every n = 4 row), GT-T-CRIT = 4
  (the n = 5 rows with CS visible: (2,4),(2,5) × 2 kinds; (3,3)
  correctly excluded), GT-T-BRACKET = 24.
* P-11 falsifiers: a GT-DEPTH0/GT-CONS α or CS mismatch with the
  n = 3 control clean refutes the S2/S5 laws at n ≥ 4 (diagnose the
  slot counts first); a GT-BDRAIN violation with GT-BETA clean
  refutes the β drain composition (LEMMA GENIND-3's consumption of
  R/u₃ — check HEX3's laws before this note's); a GT-ALPHA pointwise
  divergence refutes LEMMA GENIND-2(a) at that (m, k); a GT-CRIT
  event outside the grammar refutes S5.1/S5.3's completeness — the
  criterion itself dies only if a CS event has e·μ·γ < 4; an
  ORACLE mismatch hits the σ dictionary (Ore composition, S4.1
  step 3); a tooth off its count voids the battery, not the
  theorems.

**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
appends §S11 from `genind_checks_output.txt` /
`genind_checks_results.json`.**

## S11. VERDICT (commit 2 — from the committed artifacts)

PENDING.
