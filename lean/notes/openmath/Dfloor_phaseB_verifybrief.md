# Dfloor — the assembly floor: D-1 (MEAS-BRIDGE) + D-2 (SUM-ONE) + D-4 (BASE-CASES) — Phase-B self-contained verification brief

(Fable, 2026-07-31. Companion record: `Dfloor_phaseB_attempt.md`. Falsifier —
run FIRST, before this text was finalized: `verification/openmath/
dfloor_checks.py`, ALL PASS, 0 failures; results in
`verification/openmath/results/dfloor_results.json`. Node statements from
`docs/MATH_COMPLETION_TREE_2026-08-01.md` §D1.2.)

## 0. Charge and summary of claims

The three nodes are the tree's "assembly floor": standard measure theory and
local-field algebra that the root's counting form silently assumed (V6
findings 1, 2, 4) and that is here WRITTEN OUT as complete quantified
propositions. Deliverables:

* **Theorem MEAS-BRIDGE** = D-1 clauses (i)–(v), proved for BOTH decided
  conventions in circulation (the root (U-GEN)'s strict convention and M05's
  lax Def-4.1 convention), with clause (iv) EXACT (not just up-to-null) in
  the strict convention.
* **Corollaries BRACKET / SEM-DRAIN / SEM-DRAIN-RATE** — the two-sided
  level-N bracket and qualitative + quantitative semantic drainage: the
  measure content of (U-GEN)(i)+(ii) on the SEMANTIC side, unconditional at
  every prime including wild.
* **Theorems TYPE / PART / FIN, SUM-ONE, ID, TRANSFER** = D-2 clauses
  (i)–(iv); (iii)–(iv) in honest hypothesis-explicit transfer form, with
  unconditional instances at n = 1 and n = 2.
* **Theorems BASE-0 / BASE-1, Lemmas ADD / LIN, conventions (C0)–(C2)** =
  D-4 in full; the uniformity root at n = 1 proved outright.

Everything is semantic-side assembly. NOTHING here concerns the OM
classifier's own decided counts (leaves O-1/O-2/O-3/O-5 and O-4's OL1-ii) or
the α = R_σ(p) tie at general n (T-U + its kernel ledger). §8 is the honesty
ledger. Per the rigor rules each result carries a grade: (a) known, (b) new
proof / new assembly of known substance, (c) claimed new. Everything below is
(a)/(b) in substance; the contribution is the complete assembled statement
with quantifiers, which the tree lacked as a NODE.

## 1. Setting

Fix a prime p and an integer n ≥ 0. Identify the monic polynomial
f_a = Xⁿ + a_{n−1}X^{n−1} + … + a₀ with its coefficient vector
a = (a₀, …, a_{n−1}) ∈ G := ℤ_pⁿ. Here ℤ_p is the ring of p-adic integers,
v = v_p the valuation with v(p) = 1 and v(0) = ∞, extended uniquely to every
finite extension of ℚ_p and to a fixed algebraic closure ℚ̄_p (ℚ-valued
there); |x|_p = p^{−v(x)}.

### 1.1 Cylinders and topology

For N ≥ 0 and x ∈ (ℤ/p^N)ⁿ set

    (1)  C_N(x) := { a ∈ G : a ≡ x (mod p^N) coordinatewise }

— the level-N (residue) class. C_N(x) is a coset of the subgroup
H_N := (p^N ℤ_p)ⁿ; the p^{nN} level-N classes partition G; at N = 0 there is
exactly one class, C₀ = G. A monic degree-n polynomial g is a *lift* of x iff
its coefficient vector lies in C_N(x). Under the max-metric
d(a, b) = max_i |a_i − b_i|_p, C_N(x) is the ball of radius p^{−N} about any
of its points.

**Lemma H0 (topology).** [(a)] The cylinders (1) are clopen and compact, and
form a countable base of the topology of the compact metrizable group G.
Hence σ(cylinders) = Borel(G), and every open subset of G is a countable
union of cylinders.

*Proof.* Balls of positive radius in an ultrametric space are clopen. G is
compact (finite product of the compact ℤ_p; ℤ_p compact as the inverse limit
of the finite rings ℤ/p^N, or by sequential compactness via digit
diagonalization), so the closed C_N(x) are compact. Countability: p^{nN}
classes per level, countably many levels. Base: for a ∈ U open, the ball
C_N(a mod p^N) ⊆ U for N large. Consequently every open set is a union of
cylinders, and since there are countably many cylinders in total the union
can be taken countable. σ-algebras: cylinders are open, so σ(cyl) ⊆ Borel;
opens are countable unions of cylinders, so Borel ⊆ σ(cyl). ∎

### 1.2 Haar measure and the cylinder mass law (the D-1(ii) layer)

**Proposition H1 (existence, uniqueness, mass law).** [(a); written out in
full because V6 finding 1's charge is exactly that this layer was assumed,
never stated] There is exactly one translation-invariant Borel probability
measure μ on G, and it satisfies

    (2)  μ(C_N(x)) = p^{−nN}   for every N ≥ 0 and every x.

Moreover: every finite union of cylinders has μ-mass = (number of level-N
classes it contains)·p^{−nN} at any common level N; singletons are μ-null;
and μ = μ₁^{⊗n}, the n-fold product of the coordinate measure μ₁ on ℤ_p.

*Proof.* EXISTENCE + (2). Let 𝒜 := the collection of finite unions of
cylinders. 𝒜 is an algebra of sets: two cylinders are nested or disjoint
(ultrametric balls); the complement of a level-N class is the union of the
other p^{nN} − 1 classes; G = C₀ ∈ 𝒜. Every A ∈ 𝒜 is a finite disjoint union
of level-N classes for all sufficiently large N (each level-M class splits
into exactly p^{n(N−M)} level-N classes: coordinatewise, each residue mod p^M
has exactly p^{N−M} lifts mod p^N). Define

    μ₀(A) := #{ level-N classes contained in A } · p^{−nN}.

Well-defined: refining N → N + 1 multiplies the count by exactly pⁿ and the
weight by p^{−n}. Finite additivity: count classes at a common level.
σ-additivity on 𝒜: if A = ⨆_{k≥1} A_k with A, A_k ∈ 𝒜, then A is compact
(clopen in compact G) and each A_k is open, so finitely many A_k cover A;
disjointness forces all remaining A_k to be empty, reducing the identity to
finite additivity. By the Carathéodory extension theorem for a σ-additive
premeasure on an algebra (standard; e.g. Folland, *Real Analysis*, Thm 1.14),
μ₀ extends to a Borel measure μ (σ(𝒜) = Borel by H0) with μ(G) = 1 and (2)
by construction.

TRANSLATION INVARIANCE. For g ∈ G: C_N(x) + g = C_N(x + ḡ) (ḡ := g mod p^N),
so translation permutes the level-N classes; hence A ↦ μ(A + g) also extends
μ₀. Two finite measures agreeing on the π-system 𝒜 (closed under
intersection, contains G) agree on σ(𝒜) (the π–λ / Dynkin theorem), so
μ(A + g) = μ(A) for all Borel A.

UNIQUENESS + MASS LAW FOR ANY HAAR ν. Let ν be any translation-invariant
Borel probability on G. The p^{nN} level-N classes are pairwise translates of
one another and partition G, so each has ν-mass exactly p^{−nN}. Thus ν = μ₀
on 𝒜, and by π–λ again ν = μ on Borel(G).

SINGLETONS. {a} ⊆ C_N(a mod p^N) gives μ{a} ≤ p^{−nN} → 0.

PRODUCT FORM. μ₁^{⊗n} is a Borel probability measure (for finite products of
second-countable metric spaces the product σ-algebra equals the Borel
σ-algebra — standard), and it is translation-invariant: a translation of G is
the product of coordinate translations; the image measure agrees with μ₁^{⊗n}
on measurable rectangles, hence everywhere (uniqueness of the product
measure, finite case). By the uniqueness just proved, μ₁^{⊗n} = μ. ∎

**Lemma H2 (continuity of measures).** [(a)] For Borel A₁ ⊆ A₂ ⊆ …:
μ(⋃_N A_N) = lim_N μ(A_N). For Borel B₁ ⊇ B₂ ⊇ …: μ(⋂_N B_N) = lim_N μ(B_N).

*Proof.* Disjointify: ⋃ A_N = A₁ ⊔ ⨆_k (A_{k+1} ∖ A_k); countable additivity
gives μ(⋃ A_N) = μ(A₁) + Σ_k (μ(A_{k+1}) − μ(A_k)) = lim μ(A_N). The
decreasing case follows on complements in the probability space. ∎

### 1.3 Splitting types

    (3)  Σ_• := all multisets σ of pairs (e, f) ∈ ℤ_{≥1} × ℤ_{≥1};
         deg σ := Σ_{(e,f) ∈ σ} e·f  (with multiplicity);
         Σ_n := { σ ∈ Σ_• : deg σ = n }.   (σ = ∅ allowed; deg ∅ = 0.)

For a finite field extension K/ℚ_p: e(K) := [v(K^×) : v(ℚ_p^×)] (ramification
index) and f(K) := [k_K : 𝔽_p] (residue degree) — invariants of the
isomorphism class of the extension, both finite (LIT-2 basics; the only fact
CONSUMED about them is import I-2 below).

**Lemma FIN.** [(b)] Σ_n is finite (crudely, |Σ_n| ≤ (n² + 1)ⁿ for n ≥ 1).

*Proof.* In a degree-n type each pair has e·f ≤ n, so (e, f) ∈ {1..n}²; each
pair contributes ≥ 1 to the degree, so there are ≤ n pairs. A multiset of at
most n elements drawn from a set of at most n² elements is the image of a
function {1..n} → (pairs ∪ {blank}) forgetting order. ∎

## 2. Imports — established results consumed (exact statements)

The theorems below consume EXACTLY the following. Appendix A independently
re-proves the null clause of I-3, so the qualitative results are
self-contained given I-1 and I-2 alone; I-4/I-5 feed only instance remarks.

* **I-1 (Lemma D — local constancy of the splitting type at modulus 2v+1).**
  Let f ∈ ℤ_p[x] be monic of degree n ≥ 1, separable, v := v(disc f) ∈ ℤ_{≥0}.
  Let g ∈ ℤ_p[x] be monic of degree n with g ≡ f (mod p^{2v+1})
  coefficient-wise. Then g is separable, v(disc g) = v, and σ(g) = σ(f).
  [Provenance: `lean/notes/openmath/M05-exhaust_fable.md` §4.0, proof via
  Newton–Hensel + Krasner, wild-valid (nothing uses p ∤ n). Verified status:
  the Codex pass V2 (`V2_m05_verify.jsonl`) upheld M05's items 5–8 = Lemmas
  A–D and the semantic Theorem E exactly; the tree's O-4 node records this as
  the "VERIFIED core". Consumed by MEAS-BRIDGE(iv) and SEM-DRAIN-RATE.]
* **I-2 (e·f = deg, per irreducible factor).** For monic irreducible
  g ∈ ℚ_p[X], the field K_g := ℚ_p[X]/(g) satisfies
  e(K_g)·f(K_g) = [K_g : ℚ_p] = deg g.
  [Provenance: tree row K-11, PROVED over LIT-2 (M16 + Group E; Lean
  footprint `AX_integralClosure_dvr` + core; V3 guardian audit PASSED).
  Classically: Serre, *Local Fields* II §3 (complete discretely valued
  fields are defectless). Consumed by TYPE.]
* **I-3 (discriminant tail bound + null locus).** For n ≥ 2, every prime p,
  every m ≥ 0, with w := n·v_p(n):
  μ{a : v(disc f_a) ≥ m} ≤ (n−1)·p^{−max(0, ⌈(m−w)/(n−1)⌉)} (the event read
  with v(0) = ∞); in particular μ{a : disc f_a = 0} = 0.
  [Provenance: M05 §§2–3 (Lemmas B + C); V2 items 6–7 upheld exactly these.
  The NULL clause is ALSO re-proved self-containedly in Appendix A below, and
  is the content of T-6's (ns-null) (VERIFIED-DUAL) — three agreeing
  carriers. The tail is consumed ONLY by SEM-DRAIN-RATE.]
* **I-4 (REG-p finiteness).** The set of primes at which the pinned rational
  data of the assembled solve degenerate is FINITE. [Tree row K-13, PROVED +
  Lean (M17; `MovesU/RegPFinite.lean`). Consumed only by the instance remarks
  after TRANSFER.]
* **I-5 (instance data — used ONLY in instance corollaries and the
  falsifier, never in the theorems).** (a) n = 2: α(2, σ; p) = R_σ(p) at
  EVERY prime, with R_ram = 1/(q+1), R_split = R_inert = q/(2(q+1))
  [VERIFIED-LEAN: `OM/UniformCapstone.montes_uniform_n2` + the W6q census
  ledger `verification/census_n2_uniform.py`]. (b) n = 3: the five sealed
  R_σ of `verification/CASE_RESUMN3_SEALED_PREDICTIONS.md` §S2.

Classical background used with displayed statements but without import
ceremony: unique factorization in ℚ_p[X] (Euclidean domain), the resultant
product formula (LIT-8c; Bourbaki *Algèbre* IV §6 / Lang *Algebra* — exact
numbering owed to the standing LIT-8 per-use-site transcription duty),
Tychonoff / Carathéodory / π–λ / Tonelli (any graduate text; Folland Thms
1.14, 2.37), Euclid's infinitude of primes, and — in the FALSIFIER ONLY —
the classical square-class classification of quadratic extensions of ℚ_p.

## 3. D-2 clause (i): the type function, with the partition corollary

### 3.1 Separability

For monic f ∈ ℚ_p[X] of degree n ≥ 1 with roots α₁, …, α_n ∈ ℚ̄_p listed with
multiplicity, define disc f := ∏_{i<j} (α_i − α_j)²; for n ∈ {0, 1} this is
the empty product 1. Call f *separable* iff its roots are pairwise distinct
(n ≤ 1: always).

**Lemma SEP.** [(a)] (i) disc f = (−1)^{n(n−1)/2} Res(f, f′) with Res the
Sylvester resultant; in particular disc f_a is a polynomial in a with ℤ
coefficients, and a ↦ disc f_a : G → ℤ_p is continuous. (ii) f separable ⟺
disc f ≠ 0 ⟺ gcd(f, f′) = 1. (iii) For n ≥ 1 the polynomial a ↦ disc f_a is
not identically zero.

*Proof.* (i) The resultant product formula Res(f, g) = lc(f)^{deg g}
∏_{f(α)=0} g(α) [LIT-8c] with monic f and g = f′ gives Res(f, f′) =
∏_i f′(α_i) = ∏_i ∏_{j≠i} (α_i − α_j) = (−1)^{n(n−1)/2} ∏_{i<j}(α_i − α_j)²
(pair the factors (i, j) and (j, i)). Sylvester's matrix has as entries the
coefficients of f and f′ (integers times coefficients of f), so
Res(f, f′) ∈ ℤ[a₀, …, a_{n−1}] evaluated at a; polynomial maps are
continuous. (ii) Distinct roots ⟺ ∏_{i<j}(α_i − α_j)² ≠ 0. If α is a
repeated root, f = (X − α)²h, then f′(α) = 0, so the minimal polynomial of α
divides gcd(f, f′) ≠ 1. Conversely if gcd(f, f′) is nonconstant it has a root
α with f(α) = f′(α) = 0; writing f = (X − α)h, from f′ = h + (X − α)h′ we get
h(α) = 0, so (X − α)² | f and α is repeated. (iii) Evaluate at
f = ∏_{i=1}^n (X − pⁱ): the roots pⁱ are pairwise distinct elements of ℤ_p,
so disc ≠ 0 at this coefficient vector. ∎

### 3.2 The type function

**Theorem TYPE (= D-2 clause (i)).** [(a) in substance; (b) as assembled]
Every monic separable f ∈ ℚ_p[X] of degree n ≥ 0 has EXACTLY ONE splitting
type: writing f = ∏_{i=1}^k g_i with g_i monic irreducible (n = 0: k = 0),
the g_i are pairwise distinct, and the multiset

    (4)  σ(f) := {{ (e(K_{g_i}), f(K_{g_i})) : i = 1, …, k }}

is independent of the chosen factorization and lies in Σ_n. (Each pair is
well-defined because e, f are invariants of the isomorphism class of the
field K_{g_i} = ℚ_p[X]/(g_i).)

*Proof.* ℚ_p[X] is Euclidean, hence a UFD; its units are the nonzero
constants, so every associate class of irreducibles contains exactly one
MONIC member, and comparing leading coefficients in f = c·∏ (monic
irreducibles) forces c = 1. Uniqueness of factorization up to order therefore
makes the multiset {{g₁, …, g_k}} — hence (4) — well-defined. Pairwise
distinctness: if g_i = g_j for i ≠ j then g_i² | f, so any root of g_i (which
exists, deg g_i ≥ 1) is a repeated root of f, contradicting separability.
Degree count: Σ_i e(K_{g_i})·f(K_{g_i}) = Σ_i deg g_i [I-2] = deg f = n, so
σ(f) ∈ Σ_n by (3). "Exactly one": σ is thereby a single-valued FUNCTION on
the monic separable locus. ∎

**Corollary PART.** [(b)] The separable locus S := {a ∈ G : disc f_a ≠ 0} is
open in G, and S = ⨆_{σ ∈ Σ_n} L_σ (disjoint union), where

    L_σ := { a ∈ S : σ(f_a) = σ }.

*Proof.* S is the preimage of the open ℚ_p ∖ {0} under the continuous
a ↦ disc f_a (SEP(i)–(ii)). Each a ∈ S has exactly one type (TYPE), so the
L_σ, σ ∈ Σ_n, partition S (types of degree-n polynomials lie in Σ_n). ∎

## 4. D-1: THE MEASURE BRIDGE

### 4.1 The two decided conventions

For N ≥ 0 and x ∈ (ℤ/p^N)ⁿ (lifts of x as in §1.1):

    (5) [STRICT — the root (U-GEN)'s literal convention]
        x is σ-decided iff EVERY lift of x is separable with type σ.
        decided_σ(N) := #{σ-decided x};  D_σ(N) := ⋃{C_N(x) : x σ-decided}.

    (6) [LAX — M05 Definition 4.1's convention]
        x is σ-decided° iff every SEPARABLE lift of x has type σ.
        decided°_σ(N), D°_σ(N) analogous.

A class σ-decided per (5) is σ-decided° per (6): its separable lifts are
among all lifts. So decided_σ(N) ≤ decided°_σ(N) and D_σ(N) ⊆ D°_σ(N).

**Lemma EX (separable lifts exist).** [(b)] Every class C_N(x) contains a
separable lift. Hence a class is σ-decided° for AT MOST one σ, and likewise
(5) assigns at most one σ.

*Proof.* μ({disc = 0}) = 0 (Appendix A; = I-3's null clause) while
μ(C_N(x)) = p^{−nN} > 0 (Prop H1), so C_N(x) ⊄ {disc = 0}. Uniqueness of the
assigned type: any separable lift has exactly one type (TYPE), and a lift
witnesses both verdicts. ∎

**Theorem MEAS-BRIDGE (= D-1, clauses (i)–(v)).** [(b)] For every prime p,
every n ≥ 1, and every σ ∈ Σ_n — stated for the strict convention (5), with
the lax deltas in brackets:

(i) L_σ is OPEN in G, hence Borel; consequently the root's density
    α(n, σ; p) := μ(L_σ) is well-defined.
(ii) Every level-N residue class is a compact-open cylinder of Haar mass
    exactly p^{−nN} [Prop H1 (2)], and μ(D_σ(N)) = decided_σ(N)·p^{−nN}.
(iii) D_σ(N) ⊆ D_σ(N+1) for every N ≥ 0. [Likewise D°_σ(N) ⊆ D°_σ(N+1).]
(iv) ⋃_N D_σ(N) = L_σ EXACTLY. [Lax: L_σ ⊆ ⋃_N D°_σ(N) ⊆ L_σ ∪ {disc = 0} —
    equality up to the μ-null set {disc = 0}.]
(v) lim_{N→∞} decided_σ(N)/p^{nN} = α(n, σ; p). [The lax counts have the
    same limit.]

*Proof.*

(iii) Let C_{N+1}(y) ⊆ C_N(x) with x σ-decided. Every lift of y is a lift of
x, hence separable with type σ; so y is σ-decided. Since D_σ(N) is the union
of the level-(N+1) classes it contains, D_σ(N) ⊆ D_σ(N+1). [Lax: the
separable lifts of y are among the separable lifts of x, and y HAS separable
lifts (EX), so y is σ-decided°.]

(iv) (⊆) If a ∈ D_σ(N) then f_a is itself a lift of a's class, hence
separable with σ(f_a) = σ: a ∈ L_σ. (⊇) Let a ∈ L_σ and v := v(disc f_a) <
∞; put N := 2v + 1. Every lift g of a's level-N class satisfies g ≡ f_a
(mod p^{2v+1}) coefficient-wise, so by I-1: g is separable and σ(g) =
σ(f_a) = σ. Hence a's class is σ-decided and a ∈ D_σ(2v+1). So the union is
EXACTLY L_σ. [Lax (⊇): strict-decided ⟹ lax-decided. (⊆): for
a ∈ D°_σ(N), either f_a is separable — then f_a is a separable lift of its
own class, so σ(f_a) = σ and a ∈ L_σ — or disc f_a = 0.]

(i) By (iv), L_σ = ⋃_N D_σ(N) is a countable union of finite unions of
cylinders, hence open (H0). (Equivalently: C_{2v+1}(a mod p^{2v+1}) ⊆ L_σ is
an open neighborhood of each a ∈ L_σ.) Open ⟹ Borel; μ(L_σ) is defined.

(ii) The first half is Prop H1 (2). D_σ(N) is a finite union of the
decided_σ(N) σ-decided level-N classes, which are pairwise disjoint (distinct
cosets of H_N), so finite additivity gives the mass identity. [Same for D°.]

(v) By (iii) the D_σ(N) increase in N; by (ii) their masses are
decided_σ(N)·p^{−nN}; by continuity from below (H2) and (iv):

    lim_N decided_σ(N)·p^{−nN} = μ(⋃_N D_σ(N)) = μ(L_σ) = α(n, σ; p).

[Lax: L_σ ⊆ ⋃_N D°_σ(N) ⊆ L_σ ∪ {disc = 0} with μ({disc = 0}) = 0 squeezes
μ(⋃_N D°_σ(N)) = α as well, and H2 applies verbatim.] ∎

### 4.2 The bracket and semantic drainage (the (U-GEN)(i)–(ii) measure content)

At each level N (strict convention) define the undecided locus

    U_N := G ∖ ⨆_{σ ∈ Σ_n} D_σ(N),
    undec(N) := μ(U_N) = 1 − Σ_σ decided_σ(N)·p^{−nN}

(the D_σ(N), σ ∈ Σ_n, are pairwise disjoint by Lemma EX, so the mass formula
follows from (ii) and finite additivity over the finite Σ_n (FIN)).

**Corollary BRACKET** [(b); = the semantic side of (U-GEN)(i)]. For every p,
n ≥ 1, σ ∈ Σ_n, N ≥ 0:

    decided_σ(N)·p^{−nN}  ≤  α(n, σ; p)  ≤  decided_σ(N)·p^{−nN} + undec(N).

*Proof.* Lower: D_σ(N) ⊆ L_σ (step (iv)(⊆)) and monotonicity of μ. Upper:
L_σ ⊆ D_σ(N) ∪ U_N — for a ∈ L_σ, a's class is either σ′-decided for some σ′
(then f_a, being a lift, has type σ′, so σ′ = σ and a ∈ D_σ(N)) or undecided
(a ∈ U_N). Subadditivity finishes. ∎

**Corollary SEM-DRAIN.** [(b)] U_N ⊇ U_{N+1} for all N, ⋂_N U_N = {disc = 0},
and undec(N) ↓ 0 as N → ∞ — at every prime including wild.

*Proof.* Decreasing: the U_N are complements of the sets ⨆_σ D_σ(N), which
increase in N by (iii) (disjointness at each level: EX). The intersection:
a ∉ ⋂_N U_N ⟺ a ∈ D_σ(N) for some N and σ ⟺ a ∈ ⋃_σ L_σ = S (by (iv) and
PART). So ⋂_N U_N = G ∖ S = {disc f_a = 0}, and continuity from above (H2)
plus the null clause (Appendix A / I-3) give undec(N) ↓ μ({disc = 0}) = 0. ∎

**Corollary SEM-DRAIN-RATE.** [(b): a one-line strengthening of M05's
verified Theorem E from the lax to the strict convention] For n ≥ 2 and
w := n·v_p(n):

    undec(N) ≤ (n−1) · p^{−max(0, ⌈(⌈N/2⌉ − w)/(n−1)⌉)}.

*Proof.* Suppose a ∈ U_N and f_a is separable with 2·v(disc f_a) + 1 ≤ N.
Every lift g of a's level-N class satisfies g ≡ f_a (mod p^N), hence
(mod p^{2v+1}) since N ≥ 2v+1; by I-1 every lift is separable of type
σ(f_a), i.e. a's class is σ(f_a)-decided — contradicting a ∈ U_N. So every
a ∈ U_N has disc f_a = 0 or 2v(disc f_a) + 1 > N; for integers v the latter
is v ≥ ⌈N/2⌉ (N even: v > (N−1)/2 ⟺ v ≥ N/2; N odd: ⟺ v ≥ (N+1)/2). Hence
U_N ⊆ {a : v(disc f_a) ≥ ⌈N/2⌉} (v(0) = ∞), and I-3's tail bound applies. ∎

### 4.3 Scope note — what MEAS-BRIDGE does and does not say

The counts decided_σ(N) of (5) are the SEMANTIC counts of the root's (U-GEN)
— its literal definition ("residue classes all of whose monic lifts have
splitting type σ"). The theorem therefore supplies (U-GEN)'s measure
content: the two-sided bracket (BRACKET), drainage (SEM-DRAIN, with rate
SEM-DRAIN-RATE), and the identification of the level-count limit with the
Haar density α (clause (v)) — unconditionally, at every prime including
wild, with clause (v) needing no drainage hypothesis at all. What it does
NOT touch: that the OM classifier/engine COMPUTES these counts (leaves
O-1/O-2/O-3/O-5; O-4's OL1-ii seam), and that the solve's R_σ equals α
(T-U + the §2.3 kernel ledger). The Lean `decided`/`hExhaustP` fields are
classifier-side objects; tying them to (5)/(6) is K-12's recorded
faithfulness-audit duty (tree §D1.5(g)), not part of this node. Provenance
note: MEAS-BRIDGE(ii) + BRACKET are the decided-side complement of M05's
Lemma A (which handled the UNDECIDED cylinder unions of an abstract stable
classifier); the two agree where they overlap.

## 5. D-2: SUM-ONE

**Theorem SUM-ONE.** [(b)] For every prime p and every n ≥ 1:
(i) [= TYPE] every monic separable degree-n f over ℚ_p has exactly one
    splitting type, and it lies in Σ_n;
(ii) μ({a : disc f_a = 0}) = 0 [Appendix A / I-3 / T-6 (ns-null)];
(iii) Σ_{σ ∈ Σ_n} α(n, σ; p) = 1.

*Proof of (iii).* By PART, G = {disc = 0} ⊔ ⨆_{σ ∈ Σ_n} L_σ, with Σ_n finite
(FIN) and each L_σ Borel (MEAS-BRIDGE(i)); {disc = 0} is closed, hence
Borel. Finite additivity:
1 = μ(G) = μ({disc = 0}) + Σ_σ μ(L_σ) = 0 + Σ_σ α(n, σ; p). ∎

**Lemma ID (rational identity principle).** [(a)] Let R ∈ ℚ(t) and let
Z ⊆ ℤ be infinite, with R defined (denominator nonzero) and R(z) = 0 at
every z ∈ Z. Then R = 0 in ℚ(t).

*Proof.* Write R = A/B with A, B ∈ ℚ[t], B ≠ 0. For z ∈ Z: B(z) ≠ 0 and
A(z)/B(z) = 0, so A(z) = 0. Thus the polynomial A vanishes on the infinite
set Z of the field ℚ; a nonzero polynomial has at most deg A roots; so
A = 0 and R = 0. ∎

**Theorem TRANSFER (= D-2 clauses (iii)–(iv), hypothesis-explicit).** [(b)]
Let n ≥ 1, let {R_σ}_{σ ∈ Σ_n} ⊆ ℚ(t), and let P be an INFINITE set of
primes such that for every p ∈ P and every σ ∈ Σ_n: R_σ is defined at t = p
and α(n, σ; p) = R_σ(p). Then Σ_{σ ∈ Σ_n} R_σ = 1 in ℚ(t).

*Proof.* Q := (Σ_σ R_σ) − 1 ∈ ℚ(t): a finite sum by FIN. For p ∈ P: Q is
defined at p and Q(p) = Σ_σ α(n, σ; p) − 1 = 0 by SUM-ONE(iii). P is an
infinite set of integers, so Q = 0 by ID. ∎

**Instances (grades explicit).**
* n = 1: P = ALL primes with R_{(1,1)} = 1, by Theorem BASE-1 below;
  Σ_σ R_σ = 1 holds unconditionally (trivially).
* n = 2: P = ALL primes by I-5(a) (VERIFIED-LEAN), so Σ_σ R_σ = 1 in ℚ(t)
  at n = 2 UNCONDITIONALLY. Direct check of the known table:
  1/(q+1) + q/(2(q+1)) + q/(2(q+1)) = (1 + q)/(q + 1) = 1.
* General n (the root's intended use): once T-U + its kernel ledger supply
  α(n, σ; p) = R_σ(p) at every (REG-p) prime, take P := the (REG-p) primes —
  infinite because the complement is finite (I-4) and there are infinitely
  many primes (Euclid). Definedness at p ∈ P is part of (REG-p) (pinned
  denominators; the all-denominator strengthening is node D-6/O-12). This
  instance is CONDITIONAL exactly on the T-U ledger; the transfer theorem
  itself is unconditional.
* Lemma ID is deliberately stated over arbitrary infinite Z ⊆ ℤ: the
  unramified-base clause (node D-3) will want it at prime powers q = p^δ;
  nothing changes.

## 6. D-4: BASE CASES

### 6.1 Degree 1

**Theorem BASE-1 (= D-4's first clause; the uniformity root at n = 1).**
[(b)] For every prime p:
(a) Σ₁ = { {(1,1)} } — there is exactly one degree-1 splitting type;
(b) every monic linear f = X + a₀ (a₀ ∈ ℤ_p) is separable with
    σ(f) = {(1,1)};
(c) L_{(1,1)} = G = ℤ_p and α(1, {(1,1)}; p) = 1;
(d) for every N ≥ 0 EVERY level-N class is {(1,1)}-decided in the strict
    sense (5): decided_{(1,1)}(N) = p^N, undec(N) = 0; in particular the
    single level-0 class is decided AT N = 0;
(e) with R_{(1,1)} := 1 ∈ ℚ(t): α(1, σ; p) = R_σ(p) at every prime, the
    bracket is exact at every level, drainage is trivial, Σ_σ R_σ = 1, and
    the producing solve is the 1×1 system (1)·C = (1) with C = 1 — pivot 1,
    p-independent, pole-free. (U-GEN) and (U-DENS) hold at n = 1
    UNCONDITIONALLY.

*Proof.* (a) A degree-1 type is a multiset of pairs each contributing
e·f ≥ 1 with total 1: exactly one pair, e·f = 1, forcing e = f = 1 (positive
integers); ∅ has degree 0 ≠ 1. (b) f = X + a₀ has the single root −a₀
(pairwise-distinct vacuously; disc = 1 by the n = 1 empty-product
convention, consistent with SEP). It is irreducible (degree 1), and
K_f = ℚ_p[X]/(X + a₀) ≅ ℚ_p by evaluation X ↦ −a₀. The trivial extension has
e = 1 (equal value groups) and f = 1 (equal residue fields), so
σ(f) = {(1,1)} by (4) — I-2 is not even needed. (c) By (b) every a ∈ G lies
in L_{(1,1)}; μ(G) = 1. (d) Every lift of every class is separable of type
{(1,1)} by (b), which is exactly (5), at every N ≥ 0 — including the single
class C₀ = G at N = 0 (p^{n·0} = 1 classes, mass p⁰ = 1). (e) Immediate from
(c) + (d): decided/p^N = 1 = α = R(p); bracket 1 ≤ 1 ≤ 1 + 0; the sum over
the singleton Σ₁ is 1; at n = 1 there is one type and one state, so the
finite solve of (U-GEN)(iii) degenerates to (1)·C = (1), whose unique
solution C = 1 is R_{(1,1)}; its only pivot is the constant 1 ≠ 0 at every
prime power. ∎

*Remark (base change).* The proof of (a)–(d) uses nothing about ℚ_p beyond
completeness of a discretely valued field with finite residue field: over
any such base (e.g. K_δ = W(𝔽_{p^δ})[1/p], Haar on O^n via the verbatim
Prop-H1 construction with q = residue size), every monic linear polynomial
has type {(1,1)} and density 1 = R_{(1,1)}(q). So the n = 1 instance of the
root's unramified-base clause holds too; this feeds node D-3 but is recorded
here because it is free.

### 6.2 Degree 0 and the convolution unit

**Theorem BASE-0.** [(b)] (a) Σ₀ = {∅}; the unique monic degree-0 polynomial
is the constant 1; its factorization into monic irreducibles is the empty
product; σ(1) = ∅; disc 1 = 1 (empty products); 1 is separable.
(b) The space of monic degree-0 polynomials is the one-point space
G = ℤ_p⁰ = {()}; its unique probability measure is the Dirac mass (trivially
the Haar measure); for every N ≥ 0 the single level-N class is ∅-decided —
already at N = 0; α(0, ∅; p) = 1 =: R_∅(p) with R_∅ := 1.

*Proof.* (a) deg σ = 0 forces σ to have no parts (each part contributes
≥ 1): σ = ∅, and ∅ ∈ Σ₀. A monic degree-0 polynomial is the constant 1. The
UF argument of TYPE runs verbatim with k = 0: in 1 = c·∏(monic irreducibles)
every irreducible factor has degree ≥ 1, so the product is empty and c = 1.
Then (4) gives σ(1) = ∅, a multiset over the empty index set. Roots: none,
pairwise distinct vacuously; disc = empty product = 1 ≠ 0. (b) One point,
one class per level, every lift equal to 1 and separable of type ∅; all
clauses read 1 = 1. ∎

**Lemma ADD (type additivity — the semantic ground of the branch
convolution).** [(b)] Let g, h ∈ ℚ_p[X] be monic, separable, and coprime.
Then gh is separable and σ(gh) = σ(g) ⊎ σ(h) (multiset union). By induction,
for every FINITE pairwise-coprime family (g_j)_{j∈J} of monic separable
polynomials, ∏_{j∈J} g_j is separable with

    σ( ∏_{j∈J} g_j ) = ⨄_{j∈J} σ(g_j),

INCLUDING J = ∅ with the conventions ∏_∅ := 1 and ⨄_∅ := ∅ (Theorem BASE-0).

*Proof.* Concatenating monic-irreducible factorizations of g and h gives one
of gh; by uniqueness (TYPE) the factor multiset of gh is the multiset union
of those of g and h. All multiplicities in gh are 1: within g's (resp. h's)
block the factors are distinct (g, h separable, TYPE), and a factor common
to both blocks would divide gcd(g, h) = 1. Separability of gh: over ℚ̄_p,
each monic irreducible q ∈ ℚ_p[X] is separable (char 0: q′ ≠ 0 with
deg q′ < deg q and q irreducible give gcd(q, q′) = 1; SEP(ii)), and two
DISTINCT monic irreducibles share no root (a common root α would have both
as its minimal polynomial over ℚ_p). So the roots of gh — the union of the
roots of its distinct irreducible factors, each factor with distinct roots —
are pairwise distinct. Finally σ(gh) = σ(g) ⊎ σ(h) by (4) applied to the
concatenated factor multiset. Finite J: induction on |J|; J = ∅ is
BASE-0(a): σ(1) = ∅. ∎

**Conventions (C0)–(C2) — the recursion floor interface** (definitions plus
consistency proofs; this is the record V6 finding 4 demanded):

* **(C0) The graded type monoid.** (Σ_•, ⊎, ∅) is a commutative monoid
  graded by deg: multiset union — addition of multiplicity functions — is
  associative and commutative with unit ∅ (the zero function), and
  deg(σ₁ ⊎ σ₂) = deg σ₁ + deg σ₂ since deg is linear in the multiplicity
  function (deg σ = Σ_{(e,f)} e·f·mult_σ(e,f)). It is cancellative:
  σ ⊎ σ₂ = σ ⊎ σ₂′ ⟹ σ₂ = σ₂′ (subtract multiplicities).
* **(C1) The branch convolution and its unit.** For c₁, c₂ : Σ_• → A
  (A a commutative ring, e.g. ℚ(q)):

      (c₁ ⊛ c₂)(σ) := Σ_{σ₁ ⊎ σ₂ = σ} c₁(σ₁)·c₂(σ₂),

  a FINITE sum: a finite multiset σ has finitely many sub-multisets σ₁, and
  σ₂ = σ ∖ σ₁ is then determined (cancellativity). ⊛ is commutative and
  associative with unit δ_∅ (value 1 at ∅, else 0): the unit law is
  (c ⊛ δ_∅)(σ) = Σ_{σ₁⊎σ₂=σ} c(σ₁)·δ_∅(σ₂) = c(σ) (only σ₂ = ∅, σ₁ = σ
  survives); associativity: both bracketings of c₁ ⊛ c₂ ⊛ c₃ equal
  Σ_{σ₁⊎σ₂⊎σ₃=σ} c₁(σ₁)c₂(σ₂)c₃(σ₃), the ordered triple decompositions
  being in bijection under re-association. **The convolution over an EMPTY
  child family is DEFINED as the unit: ⊛_{j∈∅} c_j := δ_∅.** This is the
  tree's "empty child set ⇒ convolution unit" convention; its semantic
  consistency is Lemma ADD's J = ∅ case (a branch node with no children
  carries the polynomial 1, of type ∅, with the empty product of weights 1).
* **(C2) Terminal-leaf conventions.** (τ-lin): a leaf whose block is a
  single monic LINEAR factor contributes the atom δ_{(1,1)} — semantically
  PROVED here (Lemma LIN). (τ-irr, saturated): a leaf certified with
  accumulated invariants (E, F) with E·F = its block degree d contributes
  δ_{(E,F)} — at d = 1 this forces (E, F) = (1,1) and reduces to (τ-lin),
  PROVED; at d > 1 the convention's semantic correctness is exactly O-5's
  (τ-irr) clause (LIT-4 through the dictionary O-2): FIXED HERE AS A
  CONVENTION, NOT PROVED. (τ-hen): a Hensel leaf at a simple residue factor
  of degree d̄ contributes δ_{(1, d̄)} — O-5's (τ-hen) clause via LIT-3, NOT
  re-proved here; its d̄ = 1 instance is again LIN.

**Lemma LIN.** [(b)] A monic linear factor g = X − c (c ∈ ℚ_p) of a monic
separable polynomial contributes the pair (1, 1) to (4).

*Proof.* K_g = ℚ_p[X]/(X − c) ≅ ℚ_p (evaluation at c); the trivial extension
has e = f = 1, as in BASE-1(b). ∎

**Consumers (the floor's role).** T-6's first-split recursion bottoms out at
leaves and empty child sets: (C1) + (C2) are the well-defined values it
needs there, with Lemma ADD as the semantic warrant for convolving coprime
children at all. T-8's block solve needs the degree-0/1 rows: BASE-0 and
BASE-1(e) supply the unit row and the n = 1 instance. D-1's level-0
bookkeeping (one class of mass p⁰ = 1) is BASE-0/1(d). Any formal artifact
whose leaf or empty-child conventions differ from (C0)–(C2) is unfaithful to
the semantics proved here; checking that is a cheap audit duty at each
consumption site (§8).

## 7. The falsifier suite (run FIRST; ALL PASS, 0 failures)

`verification/openmath/dfloor_checks.py` — pure Python 3, EXACT integer and
rational arithmetic throughout; results JSON at
`verification/openmath/results/dfloor_results.json`. Ground truth: ONLY the
classical square-class classification of quadratics over ℚ_p [(a); e.g.
Serre, *A Course in Arithmetic* — for D ≠ 0, writing D = p^v·u: split iff D
is a square (p odd: v even and u a QR mod p; p = 2: v even and u ≡ 1 mod 8);
inert iff v even and u a non-residue (p = 2: u ≡ 5 mod 8); ramified
otherwise], independent of every project artifact.

**Prop N2 (exact n = 2 decided criterion — proved, for the falsifier's
sake).** For the class of (b₀, c₀) mod p^N (N ≥ 1) with D₀ := b₀² − 4c₀, the
set of discriminants of its lifts is EXACTLY
  * p odd: D₀ + p^N ℤ_p;
  * p = 2: ⋃_β ( D₀ + 2^{N+1}b₀β + 2^{2N}β² + 2^{N+2}ℤ₂ ), β ∈ ℤ₂, and the
    coset depends on β only through β mod 2.

*Proof.* Lifts are b = b₀ + p^N β, c = c₀ + p^N γ with β, γ ∈ ℤ_p, and
D = D₀ + 2b₀p^Nβ + p^{2N}β² − 4p^Nγ. For p odd, 4 is a unit, so at each
fixed β the γ-orbit −4p^Nγ is all of p^Nℤ_p, which already absorbs the
β-terms (both lie in p^Nℤ_p); conversely every lift's D lies in D₀ + p^Nℤ_p.
For p = 2 the γ-orbit is exactly 2^{N+2}ℤ₂, giving the displayed union; mod
2^{N+2} the β-terms depend only on β mod 2 (2^{N+1}b₀β through b₀β mod 2;
2^{2N}β² vanishes mod 2^{N+2} for N ≥ 2, and for N = 1 equals 4β² mod 8,
determined by β mod 2). ∎

The verdict set of a class is then computed exactly by valuation/unit-class
bookkeeping on ≤ 2 (p odd: 1) cosets: a coset E + p^Mℤ_p with v(E) < M has
constant valuation v := v(E) and unit part ranging over u₀ + p^{M−v}ℤ_p; a
coset containing 0 realizes nonseparable lifts and units of every class.
The script marks a class decided iff its verdict set is a singleton ≠ ns.

Tests (assertions; ANY failure = a falsifier fires):
* **T-A** (p ∈ {2,3,5}, N ≤ 7/4/3, exhaustive over all p^{2N} classes):
  partition Σ_σ counts + undec = p^{2N}; per-class NESTING — all p² children
  of every decided class decided with the same σ (= clause (iii)); BRACKET
  against I-5(a)'s R_σ(p) (= Cor BRACKET); the SEM-DRAIN-RATE envelope at
  n = 2 (undec(N) ≤ p^{−max(0, ⌈N/2⌉−w)}, w = 2v_p(2)); monotone undec
  (= SEM-DRAIN). ALL PASS.
* **T-B** (witness certification): every undecided class exhibits two
  explicit integer lifts with distinct verdicts, or an exact nonseparable
  lift — the criterion's "undecided" marks are certified against ground
  truth, not trusted from Prop N2 (≤ 400 witnesses per level). ALL PASS.
* **T-C** (Krasner cross-check = I-1's n = 2 instance): every class whose
  center lift has 2v(disc) + 1 ≤ N is decided, with the center's verdict —
  checked for every class at every level. ALL PASS.
* **T-D** (independent closed form, p ∈ {3,5}): decided_σ(N) =
  p^N · #{d mod p^N : v_p(d) < N, verdict σ} (the (b,c) ↦ D fiber count),
  and the exact geometric series Σ_{v even} (p−1)/(2p^{v+1}) = p/(2(p+1)) —
  an end-to-end analytic instance of clause (v). ALL PASS.
* **T-E** (Lemma D perturbation test): 3000 random f per p ∈ {2,3,5}, 8
  random perturbations each at modulus 2v+1: verdict invariant, 0 violations
  (consistent with the VERIFIED import I-1). Sharpness probe at modulus 2v:
  0 violations found by random sampling at n = 2 (reported, not asserted —
  the proved constant is 2v+1; no claim about 2v is made either way).
* **T-F** (SUM-ONE point checks): Σ_σ R_σ = 1 EXACTLY at q = 2..200 for the
  n = 2 table and for the sealed n = 3 five-type table [I-5(b)]. 199 points
  exceed every relevant numerator degree, so by Lemma ID's argument these
  two instances of Σ_σ R_σ = 1 hold in ℚ(t). ALL PASS.
* Observed structure (recorded, not asserted): the strict undecided count at
  n = 2 is EXACTLY p^N at every tested (p, N) — undec(N) = p^{−N}: at p odd
  this is provable from Prop N2 (undecided ⟺ p^N | D₀, and D ranges
  uniformly: p^N choices out of p^{2N} per fiber), and it matches p = 2 as
  well.

## 8. Honesty ledger

* **PROVED HERE OUTRIGHT** (given only the listed imports): H0/H1/H2;
  SEP/TYPE/PART/FIN; EX; MEAS-BRIDGE(i)–(v) in both conventions; BRACKET;
  SEM-DRAIN; SEM-DRAIN-RATE (consumes I-1 + I-3's tail); SUM-ONE; ID;
  TRANSFER; BASE-0/BASE-1; ADD; LIN; (C0)/(C1) with consistency proofs;
  Prop N2 (falsifier support). Claimed grade: PROVED-UNVERIFIED until
  fresh-context adversarial passes accept this brief.
* **IMPORTED (established elsewhere; exact statements in §2):** I-1
  (V2-upheld), I-2 (K-11 over LIT-2, V3-audited), I-3 (V2-upheld; the null
  clause ALSO re-proved self-containedly in Appendix A, so the qualitative
  results do not depend on the import), I-4 (K-13; instance remarks only),
  I-5 (instance corollaries and falsifier only).
* **CONVENTIONS FIXED, NOT PROVED:** (C2)'s (τ-irr) at block degree > 1 and
  (τ-hen) at residue degree > 1 — these are O-5's clauses; D-4 pins the
  conventions and proves exactly their degree-≤1 instances.
* **NOT CLAIMED:** anything about the OM classifier's decided counts or
  their agreement with (5)/(6) (O-1/O-2/O-3/O-5; O-4's OL1-ii); the
  α = R_σ(p) tie at general n (T-U + kernel ledger); classifier rates (OL2);
  the unramified-base package beyond the free n = 1 remark (D-3); the Lean
  `decided`-field faithfulness (K-12's audit duty).
* **Convention seam to audit at consumption:** strict (5) vs lax (6). Both
  are bridged here with explicit deltas (decided ≤ decided°, same density
  limit); (U-GEN)'s literal definition is (5). Any consumer must say which
  one it counts.

## Appendix A. The nonseparable locus is null (self-contained)

**Lemma NULL.** [(a)] Let m ≥ 1 and let P ∈ ℚ_p[y₁, …, y_m] be a nonzero
polynomial. Then μ_m{ y ∈ ℤ_p^m : P(y) = 0 } = 0, where μ_m is the Haar
probability on ℤ_p^m. Consequently μ({a ∈ G : disc f_a = 0}) = 0 for every
n ≥ 1 (by SEP(iii) the discriminant is a nonzero polynomial in a; for n = 1
the locus is empty).

*Proof.* Induction on m. Z := {P = 0} ∩ ℤ_p^m is closed (P continuous),
hence Borel. m = 1: P has at most deg P roots in the field ℚ_p ⊇ ℤ_p, and
finite sets are μ₁-null (singletons are null by Prop H1). Step m > 1: write
P = Σ_{k=0}^d P_k(y₁, …, y_{m−1})·y_m^k and fix k₀ with P_{k₀} ≠ 0. Put
A := { y′ ∈ ℤ_p^{m−1} : P_{k₀}(y′) = 0 }: μ_{m−1}(A) = 0 by the induction
hypothesis applied to P_{k₀}. For y′ ∉ A the one-variable polynomial
P(y′, ·) is nonzero (its coefficient k₀ is nonzero), so the fiber
Z_{y′} = { y_m : P(y′, y_m) = 0 } is finite, hence μ₁-null. By Prop H1,
μ_m = μ_{m−1} ⊗ μ₁ (product measures associate), and by Tonelli for finite
product measures (Folland Thm 2.37; y′ ↦ μ₁(Z_{y′}) is measurable):

    μ_m(Z) = ∫ μ₁(Z_{y′}) dμ_{m−1}(y′) ≤ ∫_A 1 dμ_{m−1} + ∫_{Aᶜ} 0 dμ_{m−1} = 0. ∎

(Three agreeing carriers of the corollary: this appendix; I-3's null clause
[M05 Lemmas B+C, V2-upheld]; T-6's (ns-null) [VERIFIED-DUAL]. The brief's
§§4–6 may cite any one; the appendix keeps the package self-contained.)

## 9. Suggested checks for the verification pass

(i) Prop H1: audit the algebra/π-system bookkeeping (the compactness
reduction of σ-additivity, and that BOTH uses of π–λ are legitimate — finite
measures, π-system containing G). (ii) MEAS-BRIDGE(iv): confirm the strict
convention gives EXACT equality and that the lax bracket
L_σ ⊆ ⋃D° ⊆ L_σ ∪ {disc=0} is airtight, including Lemma EX's role in (iii)
and in the disjointness used by BRACKET/SEM-DRAIN. (iii) SEM-DRAIN-RATE:
check the ⌈N/2⌉ integer arithmetic and that the strict-vs-lax upgrade
really is the displayed one-liner. (iv) TYPE: confirm nothing beyond I-2 is
consumed about e/f, and that the monic-normalization uniqueness argument is
complete. (v) TRANSFER: confirm the conditional structure (nothing
unconditional is claimed at general n) and the definedness bookkeeping.
(vi) BASE: check the empty-product conventions are used consistently
(disc 1 = 1, ⨄_∅ = ∅, ⊛_∅ = δ_∅) and that (C2)'s unproved clauses are
fenced exactly as O-5 content. (vii) Falsifier: re-derive Prop N2
independently; confirm T-B really certifies the undecided marks against the
classical rule only.

