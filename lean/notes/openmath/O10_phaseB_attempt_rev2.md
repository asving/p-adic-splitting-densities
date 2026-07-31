# O10_phaseB_attempt REV 2 — O-10: sibling independence at adapted cells (the D-8-guarded form) + the K-COUNT lemma

Date: 2026-08-01 (rev 1); 2026-08-02 (this rev). Prover: Fable (fresh context). Charge (tree §3 item 11 +
DELTA 1 node D-8 + DELTA 2 path step 7): state O-10 in the adapted-cell form
CARRYING the N-guard, and prove K-COUNT — "the multiplication map on factor
tuples mod p^N is, for N ≥ thr(c) + ~2ρ(c), a constant-fiber surjection
(Sylvester determinant + Smith normal form + Newton absorption)" — or the
sharpest partial. Sources: `docs/MATH_COMPLETION_TREE_2026-08-01.md` (O-10
node, D-8, DELTA 2 §D2.2 remainder table), `lean/notes/openmath/
M07-sibjc_fable.md` (the reduction K-FACT/K-LOC/K-JAC/K-COUNT, OL-1..OL-4,
the three adversarial routes), `lean/notes/openmath/M07-sibjc_brief.md` (the
typed `SibJcRows` being fenced), `lean/LeanUrat/MovesU/SibJcRouteA.lean`
(the compiled route-(a) counting gate, 5¹³ ≠ 5¹²). No Lean file is touched;
the item-27 statement repair stays PARKED (§6).

(This is REVISION 2, repairing the pass-2 hostile audit (`O10_pass2_verify.md`;
Fable, fresh context, model-diverse, standalone read of rev 1: verdict
**SOUND-WITH-GAPS — zero critical errors**. The mathematical core — Lemma 1,
Lemma 2 ("the new mechanism is airtight and correctly load-bearing"), the
T-bijection absorption Steps 1–5, Corollary 1, Theorem 2's proof at each
instantiable level, the §4.3 guard arithmetic (a)–(c) — was verified
item-by-item, the falsifier suite reproduced 68/0, and Lemma 2 confirmed by an
independent throwaway check at the B10 wild pair. Both findings are
display/narration-level; the verifier found EVERY displayed theorem true as
stated. The core is carried BYTE-STABLE; the repairs below touch only the
narration sites the verifier quoted. Pass 1 (`O10_pass1_verify.md`) had
recorded clean; this pass was the model-diverse second read.)

## §0-pre Rev-2 changelog (pass-2 findings → dispositions → repair sites)

| pass-2 finding | class | disposition | repair site |
|---|---|---|---|
| 1: the advertised D-8 value-vs-law SEPARATION collapses under the document's own definitions — keying is defined only at depths K ≥ τ (§1) and (A3) demands K_j ≤ N − e_max, so an adapted presentation EXISTS iff N ≥ τ + e_max, i.e. M ≥ e_max — precisely Theorem 1(ii)'s s(M) = ρ condition. Hence Theorem 2's "every N ≥ τ" is VACUOUS on τ ≤ N < τ + e_max (whenever ρ ≥ 1); in EVERY nonvacuous instance the fiber constant is already p^ρ; the §5.2 regime "law with value p^{s(M)} ≠ p^ρ, still cancelling" is EMPTY; §4.3(d)'s "the buffer is what makes the fiber VALUE p^{ρ(c)}" is a misattribution. All displayed theorems remain TRUE as stated (the sub-guard fiber counts of Theorem 1(i) genuinely non-vacuous) | gap | REPAIRED — the separation is DEFINITIONAL, so the separation language is DROPPED at all four quoted sites; N ≥ τ + e_max (Theorem 1(ii)'s range) is stated as THE existence range of adapted presentations = the product law's effective range; the law's and the value-p^ρ's thresholds stated as COINCIDING at N = τ + e_max; the 2ρ(c) buffer re-billed as read headroom (+ the §4.3(a) arithmetic), not law and not value; the verifier's B10 anchor displayed | §0 (OL-4 sentence); §4.2 Remark (1); §4.3(d); §5.2 |
| 2: the box-count transport (§1) is consumed at §4.3(b) but rests on an undisplayed external document (M07 brief §2.1) — a standalone reader cannot check clause (b)'s box-count phrasing from this document alone | gap (minor) | REPAIRED — the transport gets its standalone DISPLAY (the digit-array chart (BOX), a stated bijection) AND an explicit external-cite row scoping exactly what is owed to M07 §2.1 and its single consumption site | §1 (BOX); §8 cite row |
| §V3 minor notes: the E_j-keying category slip (§4.1); S_j's literal domain; Corollary 1's silent N ≥ τ + e_max instantiability presupposition; §7's T2 "exactly" gloss | notes | RECORDED — the Corollary-1 instantiability point is covered by the Finding-1 repair (the existence range is now stated globally); the other three acknowledged here with wording left byte-stable (the verifier: intended meaning unambiguous / harmless / no overclaim consumed) | this table |
| core: Lemmas 1–3, Proposition 1, Theorem 1 (i)–(iv) + proof, Corollary 1, Theorem 2 statement + proof, §4.3(a)–(c), §5.1 fences, §5.3 audit, §7 numerics, §8 perimeter | UPHELD | byte-stable | — |

## §0 Verdict and scope declaration

**VERDICT: K-COUNT is PROVED IN FULL** (Theorem 1 below, self-contained,
in factor coordinates over ℤ_p) — and in a form SHARPER than charged: the
fibers of the level-N multiplication map over a ρ-separated polydisc are
constant at EVERY level N ≥ τ (not only in the guard range), of size
p^{Σᵢ min(eᵢ, N−τ)} for the Smith profile (eᵢ) of the Sylvester block map,
which equals p^ρ exactly in the guard range N ≥ τ + e_max (e_max ≤ ρ). The
adapted-cell O-10 statement (Theorem 2) carrying the D-8 guard is proved
UNCONDITIONALLY in factor coordinates; its application to the engine's
realized site strata is conditional on the two displayed open interfaces
(K-LOC = M07 OL-3, and the K-LOC pricing clause (I-τ) of §4.3), exactly as
the tree prices them. K-FACT is consumed as the recorded citation
(GMN Thms 1.15/1.19/3.1/3.7, `docs/GMN_citations.md`); K-JAC in its
polydisc form is Lemma 3 below (one line); its engine-side half is absorbed
into K-LOC. The M07 small-N open flank OL-4 is RESOLVED within the adapted
regime: there is NO small-N anomaly — fibers are constant at every N ≥ τ —
and (rev 2, pass-2 Finding 1) no sub-guard LAW regime either: adapted
presentations EXIST exactly for N ≥ τ + e_max, Theorem 1(ii)'s range, THE
existence range, where the fiber value is already p^ρ; the 2ρ buffer buys
read headroom, not the law and not the value (§5.2). Numerics: `verification/o10_kcount_harness.py`, 68 PASS / 0 FAIL
(§7); predictions sealed in the harness docstring before the first run
(one post-hoc refinement honestly recorded in §7.3).

Status labels per the workspace discipline: Lemma 1 = (a) known (classical
Sylvester-block determinant identity); Proposition 1 = (a) known (coprime
factorization rigidity / Hensel uniqueness); Theorem 1 = (c) claimed new AS
STATED (exact fiber counts at every finite level, with in-polydisc profile
constancy; the literature's quantitative Hensel gives lifting existence/
uniqueness at precision 2ρ+1, not fiber cardinalities — flagged for lookup,
§8); Theorem 2 = (c) new (but elementary given Theorem 1).

## §1 Setup: the ρ-separated polydisc and the level-N multiplication map

Fix a prime p and m ≥ 1 monic polynomials f₁, …, f_m ∈ ℤ_p[x], deg f_j =
d_j ≥ 1, n := Σ_j d_j, pairwise coprime in ℚ_p[x]. Set

    ρ_{ij} := v_p(Res(f_i, f_j)) < ∞  (i < j),    ρ := Σ_{i<j} ρ_{ij}.

Fix a **pinning depth** τ with

    (SEP)    τ ≥ ρ + 1.

For N ≥ τ define the level-N per-factor strata and the multiplication map

    A_j(N) := {g ∈ (ℤ/p^N)[x] : g monic, deg g = d_j, g ≡ f_j mod p^τ},
    μ_N : Π_j A_j(N) → {F ∈ (ℤ/p^N)[x] monic, deg n},
    μ_N(g₁, …, g_m) := Π_j g_j mod p^N.

("g ≡ f_j mod p^τ" is coefficientwise; #A_j(N) = p^{(N−τ)d_j}.) Write
M := N − τ. A subset C ⊆ A_j(N) is **keyed at depth K** (τ ≤ K ≤ N) if
membership depends only on g mod p^K.

**Box-count transport (rev 2 — pass-2 Finding 2: the chart displayed
standalone; the external half made an explicit cite).** At the pinned chart
a level-N monic class F = x^n + Σ_{i<n} c_i x^i mod p^N corresponds to its
coefficient digit array:

    (BOX)   F  ↦  (dig_k(c_i))_{0 ≤ i < n, 0 ≤ k < N},
            where c_i = Σ_k dig_k(c_i)·p^k, dig_k ∈ {0, …, p−1},

a BIJECTION between level-N monic classes of degree n and n×N digit arrays
(base-p digits of any coefficient representative; well-defined on classes).
Hence every cardinality in this document transports verbatim to counts of
digit-array ("box point") patterns. EXTERNAL CITE: that the engine's box
coordinates ARE this pinned chart — the identification of the tree's box
points with these coefficient digit arrays — is owed to M07 brief §2.1 and
is consumed ONLY at §4.3(b)'s phrasing "box counts = coefficient-class
counts"; nothing in Lemmas 1–3, Proposition 1, Theorem 1, Corollary 1, or
Theorem 2 depends on it.

**The Sylvester block map.** For a tuple h = (h_j) of monic ℤ_p-polynomials
of degrees d_j, let

    Φ_h : ⊕_j ℤ_p[x]_{<d_j} → ℤ_p[x]_{<n},   Φ_h(a₁, …, a_m) := Σ_j a_j · Π_{i≠j} h_i .

Both sides are free ℤ_p-modules of rank n (monomial bases); Φ_h is the
derivative of the multiplication map at h. For an injective ℤ_p-linear map
of rank-n free modules write e₁(h) ≤ … ≤ e_n(h) for the elementary-divisor
exponents (Smith normal form over the PID ℤ_p) and d_k(h) := e₁ + … + e_k =
v_p(gcd of all k×k minors) (the standard determinantal-divisor identity).

## §2 The three lemmas

**Lemma 1 (Sylvester block determinant; classical).** For h as above with
pairwise coprime components (over ℚ_p),

    det Φ_h = ± Π_{i<j} Res(h_i, h_j).

*Proof.* Induction on m. m = 1: Φ_h = id, empty product. m = 2: the matrix
of (a₁, a₂) ↦ a₁h₂ + a₂h₁ in the monomial bases is (a row/column
arrangement of) the Sylvester matrix of (h₂, h₁), and det = ±Res(h₁, h₂) is
the classical definition of the resultant via the Sylvester matrix (the
sign is the arrangement permutation; it plays no role below since only
v_p(det) is used). Step m → m+1: write g := h₁⋯h_m (degree n_m := Σ_{j≤m}
d_j) and Ψ(a₁, …, a_m) := Σ_{j≤m} a_j Π_{i≤m, i≠j} h_i (the m-factor block
map). Then for all (a₁, …, a_{m+1}):

    Φ_{(h₁,…,h_{m+1})}(a) = Ψ(a₁,…,a_m)·h_{m+1} + a_{m+1}·g
                          = Φ₂^{(g, h_{m+1})}(Ψ(a₁,…,a_m), a_{m+1}),

i.e. Φ_{m+1} = Φ₂^{(g,h_{m+1})} ∘ (Ψ ⊕ id). Taking determinants and using
multiplicativity of the resultant in its first argument for monic
polynomials (Res(AB, C) = Res(A, C)·Res(B, C)):

    det Φ_{m+1} = ±Res(g, h_{m+1}) · det Ψ = ± Π_{i≤m} Res(h_i, h_{m+1}) · Π_{i<j≤m} Res(h_i, h_j). ∎

In particular v_p(det Φ_h) = Σ_{i<j} v_p(Res(h_i, h_j)), and the cokernel
of Φ_h has ℤ_p-length Σ_{i<j} v_p(Res(h_i, h_j)) (Smith form of an
injective map: length coker = v_p(det)).

**Lemma 2 (in-polydisc constancy of the Smith profile).** Let h = (h_j) be
monic ℤ_p-polynomials with h_j ≡ f_j mod p^τ (coefficientwise), τ ≥ ρ + 1.
Then for every k, d_k(Φ_h) = d_k(Φ_f); in particular the profiles agree,
(e_i(h)) = (e_i(f)) =: (e_i), Σ_i e_i = ρ, and e_max := e_n ≤ ρ.

*Proof.* The entries of the matrix of Φ_h are coefficients of the products
Π_{i≠j} h_i, which are ℤ-polynomial expressions in the coefficients of the
h_i; since h_i ≡ f_i mod p^τ, every entry of Φ_h is ≡ the corresponding
entry of Φ_f mod p^τ, hence every k×k minor satisfies minor(h) ≡ minor(f)
mod p^τ. By Lemma 1 applied at f: d_n(f) = v_p(det Φ_f) = ρ, so for every
k, d_k(f) ≤ d_n(f) = ρ < τ (the d_k are partial sums of the nonneg. sorted
e_i(f)). A minor attaining d_k(f) has valuation < τ, so its valuation is
preserved exactly: d_k(h) ≤ d_k(f). Conversely if d_k(h) < d_k(f) ≤ ρ < τ,
a minor attaining d_k(h) has valuation < τ, preserved exactly in the other
direction, giving d_k(f) ≤ d_k(h) — contradiction. So d_k(h) = d_k(f); the
e_i are the consecutive differences; Σe_i = d_n = ρ; e_max ≤ Σe_i = ρ. ∎

**Lemma 3 (K-JAC, polydisc form).** For h as in Lemma 2:
v_p(Res(h_i, h_j)) = ρ_{ij} for all i < j (and hence Σ = ρ, constant).

*Proof.* Res of two monic polynomials of fixed degrees is a ℤ-polynomial in
their coefficients, so Res(h_i, h_j) ≡ Res(f_i, f_j) mod p^τ, and
v_p(Res(f_i, f_j)) = ρ_{ij} ≤ ρ < τ pins the valuation. ∎

**Proposition 1 (ℤ_p-rigidity; known).** μ is injective on ℤ_p-points of
the polydisc: if g_j ≡ f_j ≡ g'_j mod p^τ (monic, degrees d_j) and
Π g_j = Π g'_j in ℤ_p[x], then g_j = g'_j for all j.

*Proof.* Let q be a monic irreducible factor of F := Πg_j in ℤ_p[x]
(a UFD). If q ∣ g_i and q ∣ g'_j with i ≠ j then Res(g_i, g'_j) = 0; but
g_i ≡ f_i, g'_j ≡ f_j mod p^τ gives Res(g_i, g'_j) ≡ Res(f_i, f_j) mod
p^τ, of valuation ρ_{ij} < τ, hence ≠ 0 — contradiction. The same argument
with g, g on one side shows no q divides two distinct g_i, g_{i'}. So for
each q there is a single index i with q ∣ g_i, the same index carrying q
on the g' side, and the full multiplicity of q in F sits in g_i and in
g'_i. Hence g_i and g'_i have identical irreducible factorizations and are
monic: equal. ∎

## §3 Theorem 1 (K-COUNT): exact fibers of μ_N at every level

**Theorem 1.** Assume (SEP): τ ≥ ρ + 1. Let N ≥ τ, M := N − τ, and let
(e_i) be the Smith profile of Φ_f (Lemma 2), s(M) := Σ_{i=1}^n min(e_i, M).
Then:

  (i)  **(constant fibers, every level)** every nonempty fiber of μ_N has
       cardinality exactly p^{s(M)};
  (ii) **(the guard range)** if M ≥ e_max — in particular whenever
       N ≥ τ + ρ — then s(M) = ρ: every nonempty fiber has size exactly
       p^ρ, and the image of μ_N has size p^{(N−τ)n − ρ};
  (iii)**(fiber blindness)** any two members of one fiber agree
       coefficientwise mod p^{N − e_max};
  (iv) **(monotone consistency)** the image of μ_N has size
       p^{Mn − s(M)}; both sides of (i) degenerate consistently as N ↓ τ
       (at N = τ the polydisc is a point and the fiber is trivial).

*Proof.* Fix a nonempty fiber: a class F̄ ∈ (ℤ/p^N)[x] and a member
(ḡ_j) ∈ Π_j A_j(N) with Π ḡ_j ≡ F̄ mod p^N. Choose monic ℤ_p-lifts h_j of
ḡ_j (lift each non-leading coefficient arbitrarily); then h_j ≡ f_j mod
p^τ, so h = (h_j) lies in the ℤ_p-polydisc and Lemmas 1–3 apply at h.

**Step 1 (parametrization).** A general element of Π_j A_j(N) in the fiber
is ḡ'_j = ḡ_j + ā_j with ā_j ∈ (p^τ ℤ/p^N ℤ)[x]_{<d_j} (difference of two
monic degree-d_j polynomials agreeing with f_j mod p^τ), subject to
Π_j (h_j + a_j) ≡ Π_j h_j mod p^N for one (equivalently any) lift a_j ∈
p^τ ℤ_p[x]_{<d_j} of ā_j — the condition depends only on a mod p^N.
Writing a_j = p^τ b_j and expanding,

    Π_j (h_j + a_j) − Π_j h_j = Φ_h(a) + Q(a),
    Q(a) := Σ_{S ⊆ [m], |S| ≥ 2} Π_{j∈S} a_j · Π_{i∉S} h_i,

so Q(p^τ b) = p^{2τ} Q̃(b) with Q̃(b) := Σ_{|S|≥2} p^{τ(|S|−2)} Π_{j∈S} b_j
· Π_{i∉S} h_i, a polynomial map with ℤ_p coefficients. The fiber condition
becomes p^τ Φ_h(b) + p^{2τ} Q̃(b) ≡ 0 mod p^N, i.e.

    (⋆)   Φ_h(b) + p^τ Q̃(b) ≡ 0 mod p^M,

and the fiber is in bijection with the solution set of (⋆) in b̄ ∈
(ℤ/p^M)-coefficient vectors (n coordinates: b_j has d_j coefficients).

**Step 2 (Smith change of variables).** Write Φ_h = U D V with U, V ∈
GL_n(ℤ_p) and D = diag(p^{e₁}, …, p^{e_n}) — by Lemma 2 the exponents are
the SAME (e_i) as at the base point f, for every fiber. Substituting
c := V b (a bijection of (ℤ/p^M)^n) and multiplying (⋆) by U^{−1}:

    (⋆⋆)  p^{e_i} c_i + p^τ S_i(c) ≡ 0 mod p^M   (i = 1, …, n),

where S := U^{−1} ∘ Q̃ ∘ V^{−1} is again a polynomial map with ℤ_p
coefficients.

**Step 3 (Newton absorption: the T-bijection).** Since τ ≥ ρ + 1 > e_i for
every i (Lemma 2: e_i ≤ ρ), define

    T : (ℤ/p^M)^n → (ℤ/p^M)^n,   T(c)_i := c_i + p^{τ−e_i} S_i(c).

T is well-defined (τ − e_i ≥ 1, S_i has ℤ_p coefficients). T is injective,
hence bijective on the finite set: if T(c) = T(c'), put δ := c − c' and
w := min_i v_p(δ_i) (valuations in ℤ/p^M: v_p(δ_i) := min(v_p of a
representative, M)). Every polynomial P with ℤ_p coefficients satisfies
P(c) − P(c') = Σ_i (c_i − c'_i)·G_i(c, c') with G_i ∈ ℤ_p-coefficients
(finite-difference factorization), so v_p(S_i(c) − S_i(c')) ≥ w. From
δ_i = −p^{τ−e_i}(S_i(c) − S_i(c')) we get v_p(δ_i) ≥ min(M, 1 + w) for all
i, so w ≥ min(M, 1 + w), forcing w ≥ M, i.e. δ ≡ 0.

**Step 4 (the count).** For each i with e_i ≤ M, (⋆⋆) is equivalent to
T(c)_i ≡ 0 mod p^{M−e_i} (multiply/divide by the unit-free factor p^{e_i});
for e_i > M (only possible sub-guard), (⋆⋆) is vacuous — matching
min(e_i, M) = M. So the solution set of (⋆⋆) is T^{−1}(G) for the subgroup

    G := Π_i p^{max(M−e_i, 0)} (ℤ/p^M),   #G = Π_i p^{min(e_i, M)} = p^{s(M)},

and since T is a bijection the fiber has exactly p^{s(M)} elements — the
same value for every nonempty fiber, since (e_i) is fiber-independent
(Lemma 2). This proves (i); (ii) is s(M) = Σ e_i = ρ when M ≥ e_max
(and e_max ≤ ρ gives the sufficiency of N ≥ τ + ρ); the image sizes in
(ii)/(iv) are #domain/#fiber = p^{Mn}/p^{s(M)}.

**Step 5 (blindness).** Let c, c' be two solutions, δ := c − c', w :=
min_i v_p(δ_i). Then T(c), T(c') ∈ G, so v_p(T(c)_i − T(c')_i) ≥ M − e_i ≥
M − e_max, while v_p(p^{τ−e_i}(S_i(c) − S_i(c'))) ≥ 1 + w. Hence
w ≥ min(M − e_max, 1 + w), which forces w ≥ M − e_max. Back through the
unimodular V (which preserves min-valuation bounds) and a = p^τ b: the
coefficient vectors of two fiber members differ by valuation ≥
τ + (M − e_max) = N − e_max. ∎

**Corollary 1 (the OL-1 surjection form).** Assume (SEP), N ≥ τ, and fix
per-factor read depths K_j with τ ≤ K_j ≤ N − e_max. Let C_j ⊆ A_j(N) be
keyed at depth K_j and nonempty, and Σ := μ_N(Π_j C_j). Then the extraction
map ε : Σ → Π_j (C_j mod p^{K_j}), ε(F̄)_j := (g_j mod p^{K_j}) for any
member (g_j) of the fiber over F̄, is (a) well-defined, (b) surjective, and
(c) has constant fibers: #ε^{−1}(class tuple) = p^{−s(M)} Π_j p^{(N−K_j)d_j}.

*Proof.* (a) By Theorem 1(iii) fiber members agree mod p^{N−e_max}, and
K_j ≤ N − e_max. (b) Given a class tuple, pick representatives g_j ∈ C_j
and take F̄ := μ_N(g). (c) μ_N^{−1}(Σ) = Π_j C_j: "⊇" is the definition;
"⊆" — if μ_N(t) = μ_N(t') with t' ∈ ΠC_j then t, t' share a fiber, agree
mod p^{N−e_max}, and C_j is keyed at depth ≤ N − e_max, so t ∈ ΠC_j.
Therefore #ε^{−1}(cls) = p^{−s(M)} · #{t ∈ ΠC_j : t_j ≡ cls_j mod p^{K_j}}
= p^{−s(M)} Π_j p^{(N−K_j)d_j} (each C_j-member class of depth K_j contains
exactly p^{(N−K_j)d_j} elements of A_j(N), independently of the class). ∎

In the guard range (M ≥ e_max) the constant is p^{−ρ} Π_j p^{(N−K_j)d_j} —
this is exactly M07's OL-1 ("surjection … with all fibers of equal size"),
now with the fiber value displayed and the read-depth proviso made
explicit. Depth-0 consistency: ρ = 0 forces e_i ≡ 0, τ = 1, s ≡ 0 — μ_N is
a bijection at every N ≥ 1, recovering M07 Lemma A / Corollary A′.

## §4 Theorem 2: sibling independence at adapted cells (the D-8-guarded O-10)

### 4.1 Adapted data (the definition the M07 fences dictate)

Fix the §1 data and N ≥ τ. An **adapted cell presentation** is a tuple
(τ, (C_j), (K_j)) with

    (A1) product form:  C_j ⊆ A_j(N) nonempty, the cell is Σ := μ_N(Π_j C_j);
    (A2) separation:    τ ≥ ρ + 1  (= (SEP));
    (A3) read depth:    each C_j keyed at depth K_j ≤ N − e_max.

An **adapted event system** for the presentation is a family S₁, …, S_m of
subsets of the ambient level-N monics such that for each j either
S_j ⊇ Σ ("no prescription", the row's `Set.univ` option) or

    S_j = {F̄ : ε(F̄)_j-read ∈ E_j}  for some E_j keyed at depth K_j

(a per-factor condition on the j-th extracted factor, read no deeper than
K_j ≤ N − e_max; well-defined on all of μ_N(ΠA_j) by Theorem 1(iii)).

### 4.2 The theorem

**Theorem 2 (SIB at adapted cells; unconditional in factor coordinates).**
For every adapted cell presentation and adapted event system, at every
level N ≥ τ:

    #(Σ ∩ ⋂_j S_j) · (#Σ)^{m−1}  =  Π_j #(Σ ∩ S_j).

*Proof.* Let φ := p^{s(M)} be the constant fiber size (Theorem 1(i)). As in
Corollary 1(c), μ_N^{−1}(Σ) = Π_j C_j, and for each j,
μ_N^{−1}(Σ ∩ S_j) = Π_i C_i ∩ pr_j^{−1}(Ẽ_j) where Ẽ_j := {g ∈ A_j(N) :
g-read ∈ E_j} (for the univ option take Ẽ_j := A_j(N)); this uses exactly
(A3): both C_j and E_j are keyed at depth ≤ N − e_max, so all four sets are
unions of entire fibers, and preimage counts are φ times image counts.
Hence

    #Σ = φ^{−1} Π_i #C_i,
    #(Σ ∩ S_j) = φ^{−1} #(C_j ∩ Ẽ_j) Π_{i≠j} #C_i,
    #(Σ ∩ ⋂_j S_j) = φ^{−1} Π_j #(C_j ∩ Ẽ_j),

and both sides of the claimed identity equal
φ^{−m} · Π_j #(C_j ∩ Ẽ_j) · (Π_i #C_i)^{m−1}. ∎

Remarks. (1) The constant φ cancels REGARDLESS of its value — this is the
gate's recorded mechanism ("constancy on Σ_c, not unit value") made exact.
(Rev 2, pass-2 Finding 1 — the range stated honestly: the hypotheses
(A1)–(A3) are INSTANTIABLE iff N ≥ τ + e_max, because keying is defined
only at depths K ≥ τ (§1) while (A3) demands K_j ≤ N − e_max; on
τ ≤ N < τ + e_max the theorem is vacuously true, no adapted presentation
existing. So THE existence range of adapted presentations — and hence the
product law's effective range — is Theorem 1(ii)'s range N ≥ τ + e_max,
exactly where s(M) = ρ: in every nonvacuous instance of this theorem the
cancelling constant is already φ = p^ρ. Rev 1's gloss here, "the product
law holds at EVERY N ≥ τ … with no lower N-guard beyond read depth",
advertised a sub-guard law regime with φ ≠ p^ρ; that regime is EMPTY —
the separation was definitional, not mathematical.) (2) Empty
degeneracies are consistent: if
some C_j ∩ Ẽ_j = ∅ both sides vanish. (3) m = 2 is the pair form; m ≥ 3
needs nothing new.

### 4.3 The D-8 guarded statement in tree language

**O-10 (adapted, D-8-guarded).** Let Σ_c be a realized site stratum of the
canonical tree at level N with branch roster of size m ≥ 2 and branch
factors f₁, …, f_m (K-FACT: the roster members isolate pairwise coprime
ℤ_p-factors of dec(x) — GMN Thms 1.15/1.19 order 1, 3.1/3.7 order r, per
the recorded citation perimeter), ρ(c) := Σ_{i<j} v_p(Res(f_i, f_j)),
thr(c) the cell's threshold. Assume the K-LOC interface (OPEN, = M07 OL-3
+ the pricing clause):

    (I-τ) the cell datum of Σ_c is an adapted presentation (A1)–(A3) in the
    branch-factor coordinates, with pinning depth τ(c) ≤ thr(c) + ρ(c),
    τ(c) ≥ ρ(c) + 1, and all cell/event reads keyed at depth
    K ≤ thr(c) + ρ(c); prescribed-subtree events of distinct roster
    members translate to per-factor systems (E_j) at the same depths.

Then for every N ≥ thr(c) + 2ρ(c):

  (a) N ≥ τ(c) + ρ(c) ≥ τ(c) + e_max and N − e_max ≥ N − ρ(c) ≥
      thr(c) + ρ(c) ≥ K, so (A1)–(A3) hold at level N with headroom;
  (b) prescribed-subtree events of distinct siblings are independent in
      exact count form: #(Σ_c ∩ ⋂_j S_j)·(#Σ_c)^{m−1} = Π_j #(Σ_c ∩ S_j)
      (Theorem 2; box counts = coefficient-class counts, §1);
  (c) the level-N factor extraction is a constant-fiber surjection onto
      the product of the per-branch strata with fiber value
      p^{−ρ(c)} Π_j p^{(N−K_j)d_j} (Corollary 1 in the guard range) — the
      K-COUNT clause of the tree's O-10 node, with the fiber constant now
      explicit;
  (d) (rev 2 — pass-2 Finding 1 repair; rev 1's clause here misattributed
      the buffer) the product law (b) carries no threshold beyond
      instantiability: it holds at EVERY N at which an adapted presentation
      exists, i.e. every N ≥ τ(c) + e_max — Theorem 1(ii)'s existence
      range, where the fiber value is ALREADY p^{ρ(c)}. The law's threshold
      and the fiber-value-p^{ρ(c)} threshold COINCIDE there (the separation
      rev 1 advertised is definitionally empty); what the full D-8 guard
      N ≥ thr(c) + 2ρ(c) buys beyond that shared threshold is the (a)
      arithmetic — ρ(c) digits of read headroom — not the law and not the
      value.

Conditionality display (per the tree's honesty discipline): (b)–(d) are
theorems given (I-τ); (I-τ) itself is the K-LOC residue — the
recentering/lift bookkeeping that presents the engine's cell datum in
factor coordinates — owned by M07 OL-3 (the GD-2/GD-3 dictionary area is
where its ingredients live; it is NOT discharged here). K-JAC's engine
half (that the site's separation data pins ρ(c) as cell data) is absorbed
into (I-τ) via Lemma 3: once the factor presentation exists with pinning
τ(c) ≥ ρ(c) + 1, the resultant valuations are AUTOMATICALLY constant on
the cell. OL-2 (CellAssign inhabitation, Lean-side) is untouched.

## §5 The fences, the small-N residue, and the consumer audit

### 5.1 What (A1)–(A3) exclude — the M07 adversarial routes, one per clause

* **Route 1 (correlation cells; the compiled `SibJcRouteA` gate, 5¹³ ≠
  5¹²).** The refinement Σ* ∩ {v₁ = v₂} conditions on a JOINT function of
  two branches' digits; it is not of the product form μ_N(ΠC_j) — (A1)
  excludes it. Harness T4 reproduces the breakage in factor coordinates:
  refining an adapted cell by a diagonal digit condition breaks the
  product law by exactly a factor p (B4: ratio 2 at p = 2; B10: ratio 3
  at p = 3), while the SAME events on the unrefined cell satisfy it (T3).
* **Route 2 (empty side split / foreign fd) and the unrealized-cell &
  coarsened-read defects (Route 3).** These attack the site-keyed
  asymmetric forms (`JCmultiAt`'s entrance event on the right; ν₀ free;
  rosters of unrealized cells free). Theorem 2's form has no entrance
  event and quantifies only over the presentation's OWN events (E_j keyed
  at the presentation's depths); a mixture of two factor presentations
  with different (C_j) data is not itself of the form μ_N(ΠC_j) — (A1)
  again. The ledgered (JC-multi) is M07 Lemma B and is not re-derived.
* **Too-deep reads.** An "event" reading factor digits above depth
  N − e_max is in general NOT a function of the product (harness T5:
  straddling fibers 4/4, 32/32, 5/5 at B3/B5/B8) — such a prescription
  cannot even be stated as a subset of the cell, which is the sharpest
  form of the fence: (A3) is not a convenience but a well-definedness
  condition.

### 5.2 D-8r (the small-N residue) — resolved within the adapted regime

M07 OL-4 asked whether the rows need N-guards because of small-N boundary
behavior. Answer, from Theorem 1(i) + Theorem 2 (rev 2 — restated per
pass-2 Finding 1; rev 1 narrated a value-vs-law SEPARATION here that is
definitionally empty): within the adapted regime there is NO small-N
anomaly to guard against — the FIBERS are constant at every N ≥ τ (value
p^{s(N−τ)}, confirmed exactly by harness T1 sub-guard rows, e.g. sizes
1/4/8/16 along N = 5..8 at B5; that sub-guard clause of Theorem 1(i) is
real and non-vacuous). But there is no sub-guard LAW regime to pair those
fibers with: keying is defined only at depths K ≥ τ (§1) and (A3) demands
K ≤ N − e_max, so an adapted presentation exists iff N ≥ τ + e_max —
exactly Theorem 1(ii)'s s(M) = ρ range. That is THE existence range of
the product law, and at every level in it the fiber value is already p^ρ:
the law's effective threshold and the fiber-value-p^ρ threshold COINCIDE
at N = τ + e_max. (Pass-2 anchor, harness B10 — p = 3, ρ = 3, e_max = 2,
τ = 4: fibers of size p^{s(M)} ≠ p^ρ occur only at N = 4, 5, levels where
N − e_max < τ, so no cell/event read is legal and no product-law instance
exists; the first law-legal level N = 6 already has fiber p³ = p^ρ — the
harness itself labels N = 6 "(GUARD)".) What the full D-8 guard
N ≥ thr + 2ρ buys beyond the shared threshold is ρ(c) digits of read
headroom (and §4.3(a)'s arithmetic), not the law and not the value. D-8r
narrows to: consumers must not read within e_max of the working level —
a re-derivation of the read-ceiling discipline (O-1's modulus), not a new
phenomenon.

### 5.3 Consumer audit (the D-8 rider), at statement level

* **T-6 (SIB-STEP).** The stacked one-step joint law consumes (SIB) at a
  site whose events are the engine's own next reads — depth ≤ thr(c) +
  ρ(c) under (I-τ), i.e. within the guarded form's read ceiling; served by
  Theorem 2 + (I-τ). No sub-guard N is consumed.
* **O-11 (K1 per-tree product formula).** Consumes (SIB)/(JC-multi) along
  halted runs at their realized sites; all reads are engine reads, same
  ceiling; the p^{−ρ(c)} fiber value feeds the per-site Jacobian factor —
  this is where the FULL guard N ≥ thr + 2ρ is genuinely used (clause
  (c)), matching D-9's corrected dependency list (O-10 guarded).
* **M04 K1 / TREE-EXP.** Same shape as O-11's use.
The audit closes definitively when K-LOC lands (I-τ) — until then it is a
statement-level audit: no known consumer demands sub-guard N or
deeper-than-ceiling reads. (Recorded as the D-8 rider's status.)

## §6 The boundary to PARKED item 27 (the Lean statement repair)

The mathematics above dictates the repair shape but none of it is executed
here (items 22–29 are PARKED per the tree's priority note; no Lean file is
touched). What the finished mathematics will dictate for `SibJcRows`:

* the ∀-CA quantifier must be restricted by an adaptedness field (M07 R1)
  or the rows re-keyed to `SiteLedger` sites (M07 R3, which also makes
  `jc_multi` a theorem via Lemma B) — the (A1)-analogue;
* the rows gain the D-8 N-guard AND a read-depth clause: cell/event data
  keyed strictly below N − ρ(c) — the (A3)-analogue, which is new relative
  to M07's R1–R3 list (T5's straddling shows it is a well-definedness
  field, not a strengthening);
* the fiber-value clause (K-COUNT (c)) enters only in the guard range —
  sub-guard rows, if ever wanted, must use p^{s(M)}.

The compiled fence `MovesU/SibJcRouteA.lean` (sib_diag_break, 5¹³ ≠ 5¹²)
stands unchanged as the countermodel-side evidence; Theorem 2 + T3/T4 is
the positive-side evidence that the repaired statement is true and sharp.

## §7 Numerics record (the falsifier ran FIRST)

Harness: `verification/o10_kcount_harness.py` (pure Python, exact
integers, no dependencies). Battery: 10 factor systems over p ∈ {2, 3, 5}
— depth-0 pairs, ρ = 1..4 pairs and an m = 3 triple, same-reduction wild
pairs (x²+2)(x²+2x+2) at p = 2 and (x²+3)(x²+3x+3) at p = 3, the F1-shape
quadratic pair at p = 5, a mixed-degree pair; full N-sweeps τ ≤ N ≤ τ+ρ,
exhaustive enumeration (domains up to 3¹² = 531,441 tuples).

**Result: 68 PASS, 0 FAIL, 8 INFO** (2026-08-01, this session):

* T0 (10/10): v_p(det Φ) = ρ at every battery member (Lemma 1's identity).
* T1 (24/24): every nonempty fiber size = p^{Σ min(e_i, M)} exactly, at
  every swept level including all sub-guard levels; = p^ρ at the guard.
* T2 (23/23): fiber blindness exactly mod p^{N − e_max}.
* T3 (5/5): the adapted product law, exact at the guard point, including
  the m = 3 triple and both wild same-reduction pairs.
* T4 (2/2 + 3 INFO): the Route-1 mirror (diagonal correlation refinement)
  breaks the law by ratio EXACTLY p at both multi-coefficient pairs
  (B4: lhs=128 rhs=64, ratio 2 = p; B10: lhs=2187 rhs=729, ratio 3 = p).
  INFO: at m = 2 LINEAR pairs the correlation cell degenerates — see §7.3.
* T5 (4 INFO): deep reads (level N − e_max) straddle fibers at B3/B5/B8
  (4/4, 32/32, 5/5 fibers non-well-defined) — the (A3) fence witnessed.

### 7.3 Honesty notes on sealing

Predictions T0–T3 and T5 were sealed in the harness docstring before the
first run and passed unchanged. T4's expectation was REFINED after the
first run: at m = 2 pairs of LINEAR factors the product pins the
coefficient sum exactly, so the two depth-τ digits are deterministically
coupled and the diagonal cell makes the two events coincide (law holds
trivially — ratio 1 observed at B3/B5/B8). The refined prediction
("breakage by exactly p at multi-coefficient pairs") was then sealed for
the NEW case B10 before its first T4 run and passed (ratio 3 = p). The
degeneration is derived, not just observed: for g₁ = x + c₁, g₂ = x + c₂,
F determines c₁ + c₂ exactly, so dig_τ(c₁) + dig_τ(c₂) is F-measurable.

Not run (displayed): the at-instance F1 check (M07 tests 4–5: PARI
factorpadic over the 5⁸-member Σ*) — cypari2 is not installed in this
environment; the check belongs to the K-LOC/(I-τ) landing, since it tests
the ENGINE presentation, not Theorem 1/2 (which the synthetic battery
covers directly in factor coordinates).

## §8 Honesty ledger

PROVED here, self-contained: Lemmas 1–3, Proposition 1, Theorem 1 (+
Corollary 1), Theorem 2. OPEN, displayed, owned elsewhere: (I-τ)/K-LOC =
M07 OL-3 (the engine-cell → factor-coordinate presentation with the
thr(c)+ρ(c) pricing — the single hypothesis separating Theorem 2 from the
engine-level O-10); OL-2 (CellAssign inhabitation); the item-27 Lean
statement repair (PARKED). CONSUMED citations: K-FACT = GMN Thms
1.15/1.19/3.1/3.7 (recorded perimeter, `docs/GMN_citations.md`); Smith
normal form over a PID and the determinantal-divisor identity (standard);
Res(AB,C) = Res(A,C)Res(B,C) and the Sylvester-matrix definition
(standard); BOX = the identification of the tree's box points with the §1
(BOX) coefficient digit arrays at the pinned chart (M07 brief §2.1 — the
chart itself now DISPLAYED at §1; consumption confined to §4.3(b); rev 2,
pass-2 Finding 2). Literature flags for the LITUNIT session: (i) quantitative
Hensel factorization (lifting at precision 2ρ+1) — e.g. von zur
Gathen–Gerhard, *Modern Computer Algebra*, Hensel chapters — for whether
the finite-level FIBER-COUNT form (Theorem 1(i), all N ≥ τ) appears
anywhere (I believe the profile-constancy observation and the exact
sub-guard count are new as stated; the guard-range statement may well be
folklore); (ii) M07's flagged Nart-school resultant/different OM formulas
(they would eventually discharge parts of (I-τ), not of Theorem 1).
Perimeter statement: everything here is about monic factor tuples over
ℤ_p in factor coordinates; NOTHING here claims the engine's realized site
strata satisfy (A1)–(A3) — that claim is exactly (I-τ), open.

VERDICT: O-10's quantitative kernel K-COUNT — PROVED (sharper than
charged: constant fibers at every N ≥ τ, value p^{Σ min(e_i, N−τ)},
= p^{ρ} in the D-8 guard range); the adapted-cell (SIB) product law —
PROVED unconditionally in factor coordinates (Theorem 2), engine
application conditional on the displayed (I-τ)/K-LOC interface; D-8r
resolved to a read-ceiling discipline; item-27 repair shape recorded,
repair NOT executed. Falsifier suite 68/68 with the Route-1 breakage
reproduced at exactly ratio p.
