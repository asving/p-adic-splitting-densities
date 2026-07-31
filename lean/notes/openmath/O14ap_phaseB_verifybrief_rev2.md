# Verification brief O14ap, REV 2 — realizer existence at recentering nodes of coherent stage towers

You are a hostile verifier. Quote each offending passage and classify it as *critical
error* (breaks the logical chain) or *justification gap* (assume and continue). Fix
nothing. This brief is self-contained: every object is defined below; no external
documents are needed. The claims are pure mathematics about explicitly axiomatized
structures; where a claim is instead asserted about "the intended model", that status is
flagged inline and you should verify the flag's honesty, not the model theory.

*Rev note: a prior hostile pass on rev 1 CONFIRMED §§2–4 (prime-field collapse; the
terminal-realizer theorem with its threshold and transport lemmas; the corollary) and
§5.1–5.3 (the F₉ countermodel arithmetic and its conditionality flag; the recorded-lift
and fence-lift mechanisms), and found two defects, both in §5.4: (1) CRITICAL — the
replacement law's recursion prescribed lower-stage realizers in the wPrev_{r−1}-scale
but tested slot weights as if that were the σ_{r−1}.w-scale; by (STR) these differ by
the factor σ_{r−1}.e, so the equal-weight design failed except at σ_{r−1}.e = 1;
(2) JUSTIFICATION GAP — sharpness of the progression length was asserted for every g
but proved only at a g = 2 instance. Rev 2 rebuilds §5.4: the stretch factor is
threaded explicitly ((THR)), the law is scoped to the class where the scales coincide
(hypothesis (U)) with a new proposition showing the complement is a definitional void
of the clause triple (Proposition 5.4.3), and sharpness is proved at every g by a basis
argument (Proposition 5.4.2). §§1–4 and §5.1–5.3 below are byte-identical to rev 1.
Verify from scratch; do not assume the prior pass.*

## 1. Definitions

Fix a prime p and a finite field F (the "ambient" field). ℤ_p denotes the p-adic
integers; all polynomials below are in one variable X over ℤ_p unless stated. K[z^{±1}]
denotes Laurent polynomials over a field K; we write C(c) for the constant c and T(k)
for the monomial z^k, so a general element is a finite sum Σ c_k·T(k).

**Definition 1 (stage).** A *stage* σ over (p, F) is a tuple consisting of:
* natural numbers e, h ≥ 1 with gcd(e, h) = 1; integers s, t with es + ht = 1 and the
  pinning (P2): e = 1 ⟹ t = 0 (note e = 1, t = 0 forces s = 1);
* a monic key Φ ∈ ℤ_p[X] with deg Φ ≥ 1; write C_Φ := {B ∈ ℤ_p[X] : deg B < deg Φ};
* maps w, wPrev : ℤ_p[X] → ℤ; a subfield K ≤ F; a map R : ℤ_p[X] → K[z^{±1}];
subject to the axioms (all quantifiers over nonzero arguments where division by zero
would otherwise occur):
* (S1) w(fg) = w(f) + w(g) for f, g ≠ 0; min(w f, w g) ≤ w(f + g) for f, g, f+g ≠ 0.
* (wΦ) w(Φ) = h.
* (STR) w(B) = e·wPrev(B) for every nonzero B ∈ C_Φ.
* (R×) R(fg) = R(f)·R(g) for f, g ≠ 0; (R0) R(f) ≠ 0 for f ≠ 0;
  (R<) if f, g, f+g ≠ 0 and w(f) < w(g) then R(f + g) = R(f).
* (RΦ) R(Φ) = T(s) (coefficient 1).
* (S6b) for every integer ν with wPrev(Φ) < ν and every a ∈ K ∖ {0} there exists B ≠ 0
  with B ∈ C_Φ, wPrev(B) = ν, and R(B) = C(a)·T(−t·ν).
No other stage axioms are used in §§2–4. (The ambient structure has more axioms; the
proofs below cite only these, so extra axioms can only help.)

Elementary consequences of (S1), used freely: w(1) = 0 (from w(1·1) = 2w(1));
w(−1) = 0 (from w((−1)(−1)) = 2w(−1) = w(1)); hence w(−f) = w(f).

**Definition 2 (node).** A *node* ν is a tuple: a species ∈ {root, increment,
recentering}; a stage ν.σ (its *frame*); naturals ν.e, ν.h ≥ 1 coprime; naturals
ν.g, ν.μ ≥ 1; a monic irreducible ψ ∈ (ν.σ.K)[z] with deg ψ = ν.g; an element z̄ ∈ Fˣ
(a UNIT of F) with ψ(z̄) = 0 (coefficients of ψ read in F through K ≤ F); a natural
Dwidth = deg(ν.σ.Φ); a *line* L = (intercept, slope) ∈ ℚ², evaluated L(b) :=
intercept − slope·b; elements center ∈ ν.σ.K and lift ∈ ℤ_p[X]; subject to:
* (spec-rec) species = recentering ⟹ ν.e = 1 and ν.g = 1;
* (spec-cen) species = recentering ⟹ ψ = z − center and z̄ = center in F.
Since z̄ is a unit of F, (spec-cen) forces **center ≠ 0** at every recentering node.
Other node fields exist but are not consumed below.

**Definition 3 (history, coherence).** A *history* H is a nonempty finite list of nodes
ν_0, …, ν_{L−1} such that species(ν_j) = root ⟺ j = 0. Write σ_i := ν_i.σ,
D_i := ν_i.Dwidth, slope_i := the slope of ν_i's line, and STR_i := ∏_{j<i} ν_j.e (empty
product = 1). H is *coherent* if:
* (C1) deg(σ_0.Φ) = 1;
* (C2) for every i < L: slope_i · (ν_i.e · STR_i · D_i) = ν_i.h, as rationals.
  [Consequence: slope_i > 0, since ν_i.h ≥ 1 and the multiplier is a positive natural.]
* for every i with i + 1 < L:
  * (C4-rec) if ν_i is a recentering, the *recentering record* holds:
    (r1) σ_i.e = 1; (r2) σ_{i+1}.e = 1; (r3) ν_i.center ≠ 0; (r4) ν_i.lift ∈ C_{σ_i.Φ}
    and lift ≠ 0; (r5) σ_i.w(lift) = σ_i.w(σ_i.Φ); (r6) σ_i.R(lift) =
    C(ν_i.center)·T(0); (r7) σ_{i+1}.Φ = σ_i.Φ − lift; (r8) σ_{i+1}.w = σ_i.w and
    σ_{i+1}.wPrev = σ_i.wPrev as functions; (r9) σ_{i+1}.K = σ_i.K; (r10) for every
    B ∈ C_{σ_i.Φ}: ε(σ_{i+1}.R(B)) = ε(σ_i.R(B)), where ε : K[z^{±1}] → F(X) is the
    embedding z ↦ X with coefficients through K ≤ F ≤ F(X). [F(X) = rational functions.]
  * (C4-non) if ν_i is NOT a recentering: **ν_i.e = 1** (a recording fence of the
    current definition — see §5), and there are data:
    (n1) a map wV : ℤ_p[X] → ℤ which is the (ν_i.e, ν_i.h)-*slot-minimum* over σ_i.w at
    the key σ_i.Φ: for every nonzero f with development f = Σ_{j<N} B_j·Φ^j
    (deg B_j < deg Φ, Φ := σ_i.Φ), wV(f) = min over nonzero slots of
    (ν_i.e·σ_i.w(B_j) + j·ν_i.h), the minimum attained at an occupied slot;
    (n2) the *standard-lift display*: σ_{i+1}.Φ = Φ^{eg} + Σ_{k<g, ψ_k≠0} t_k·Φ^{ek},
    where (e, h, g, ψ) := (ν_i.e, ν_i.h, ν_i.g, ν_i.ψ), each present t_k ∈ C_Φ is
    nonzero with σ_i.w(t_k) = h·(g − k);
    (n3) σ_{i+1}.e = ν_{i+1}.e; (n4) σ_{i+1}.h = ν_{i+1}.h;
    (n5) σ_{i+1}.wPrev = wV as functions.
  * (C6) D_{i+1} = ν_i.e · ν_i.g · D_i;
  * (C7) slope_i < slope_{i+1}.
(The ambient definition has further clauses; only the above are consumed.)

**Definition 4 (realizer clauses).** For a node ν and t ∈ ℤ_p[X]:
* (CR1) t ≠ 0;
* (CR2) there is j₀ ∈ ℕ, congruent mod ν.e to a specified integer computed from ν's
  data, such that every exponent in the X-support of t is of the form j₀ + k·ν.e with
  k < ν.g. *At a recentering, (spec-rec) gives (e, g) = (1, 1), so (CR2) says exactly:
  t is an X-monomial (singleton support); the congruence mod 1 is vacuous.*
* (CR3) if ν is a recentering: t ∈ C_{ν.σ.Φ}, ν.σ.w(t) = ν.σ.w(ν.σ.Φ), and
  ν.σ.R(t) = C(ν.center)·T(0).

**Definition 5 (the residual law).** RRE(p, F): for every coherent history H over
(p, F) and every index i such that ν_i is a recentering, there exists t with
(CR1) ∧ (CR2) ∧ (CR3) at ν_i.

**Claim structure.** §2: at F = 𝔽_p, (CR2) is implied by (CR1)∧(CR3) (prime-field
collapse). §3: the main theorem — (CR1)∧(CR3) realizers exist at TERMINAL recentering
nodes (i = L−1), from Definitions 1–3 alone. (At interior recentering nodes, (r4)–(r6)
of the node's own record already exhibit the recorded lift as a realizer — immediate.)
§4: hence RRE(p, 𝔽_p) holds. §5: at general F, (CR2) is refutable at an explicitly
described intended-model instance, and the corrected support law is stated and proved.

## 2. Theorem 1 (prime-field collapse)

**Theorem 1.** Let F = 𝔽_p. For every coherent H: (i) every node has ν.g = 1;
(ii) deg(σ_i.Φ) = 1 for every i; (iii) at every recentering node, any t satisfying
(CR1) ∧ (CR3) satisfies (CR2).

*Proof.* (i) Every subfield of 𝔽_p equals 𝔽_p (it contains 1 and is additively closed,
hence contains the prime subfield, which is all of 𝔽_p). So each node's ψ is an
irreducible polynomial over K = 𝔽_p possessing a root z̄ in F = 𝔽_p = K. Then (z − z̄)
divides ψ; since ψ is irreducible and z − z̄ is not a unit, ψ = (z − z̄)·(unit), so
deg ψ = 1, i.e. ν.g = 1.
(ii) Induction. D_0 = deg(σ_0.Φ) = 1 by (C1) and Dwidth's definition. For i+1 < L:
D_{i+1} = ν_i.e·ν_i.g·D_i by (C6); ν_i.g = 1 by (i); ν_i.e = 1 either by (spec-rec)
(recentering) or by the fence in (C4-non) (any other species). So D_{i+1} = D_i, and
deg(σ_{i+1}.Φ) = D_{i+1} = 1.
(iii) By (CR3), deg t < deg(ν.σ.Φ) = 1, so t is a nonzero constant with X-support {0};
take j₀ = 0 (every residue mod 1 vanishes; 0 = 0 + 0·1, 0 < g = 1). ∎

## 3. Theorem 3 (terminal realizers from coherence alone)

Standing hypotheses for §3: H coherent of length L, ν_T a recentering at T = L − 1.
Since ν_0 is the root (and roots are not recenterings), T ≥ 1. Let b be least such that
ν_b, …, ν_T are all recenterings; then 1 ≤ b ≤ T and ν_{b−1} is not a recentering.

**Lemma 3.1 (anchor threshold).** σ_b.e = 1, σ_b.t = 0, σ_b.h = ν_b.h, and
σ_b.wPrev(σ_b.Φ) = e·h·g < ν_b.h, where (e, h, g) := (ν_{b−1}.e, ν_{b−1}.h, ν_{b−1}.g).

*Proof.* The index i = b − 1 satisfies i + 1 = b ≤ T < L, and ν_{b−1} is not a
recentering, so (C4-non) applies.
(a) σ_b.e = ν_b.e (n3) = 1 (spec-rec); (P2) then gives σ_b.t = 0; σ_b.h = ν_b.h (n4).
(b) Write Φ := σ_{b−1}.Φ. The display (n2) exhibits σ_b.Φ as a Φ-development: slot eg
carries the constant 1, slot ek carries t_k for each present k < g, all other slots 0;
all these coefficients have degree < deg Φ (deg Φ ≥ 1), and σ_b.Φ ≠ 0 (its degree is
eg·deg Φ, dominated by the monic top slot; each t_k·Φ^{ek} has degree
< deg Φ + ek·deg Φ ≤ eg·deg Φ). Evaluate the slot-minimum (n1) on it:
slot eg weighs e·σ_{b−1}.w(1) + eg·h = e·0 + egh = ehg (w(1) = 0 by (S1));
slot ek (present) weighs e·(h(g−k)) + ek·h = ehg (using (n2)'s weight law).
Every occupied slot weighs exactly ehg and slot eg is occupied, so wV(σ_b.Φ) = ehg,
and (n5) gives σ_b.wPrev(σ_b.Φ) = ehg.
(c) By (C2) at i = b−1 and i = b (both < L), and (C6), STR_b = STR_{b−1}·e and
D_b = e·g·D_{b−1}, and ν_b.e = 1:
    ν_{b−1}.h = slope_{b−1}·(e·STR_{b−1}·D_{b−1}),
    ν_b.h     = slope_b·(STR_{b−1}·e)·(e·g·D_{b−1}).
By (C7), slope_b > slope_{b−1} > 0, and the multiplier e²·g·STR_{b−1}·D_{b−1} is a
positive integer (e, g ≥ 1; STR ≥ 1 as a product of naturals ≥ 1; D_{b−1} ≥ 1 since it
is the degree of a stage key, ≥ 1 by Definition 1). Hence
    ν_b.h = slope_b·(e·STR_{b−1}·D_{b−1})·(e·g)
          > slope_{b−1}·(e·STR_{b−1}·D_{b−1})·(e·g) = ν_{b−1}.h·e·g = e·h·g. ∎

**Lemma 3.2 (transport along the run).** For b ≤ r ≤ T:
(i) σ_r.e = 1 (hence σ_r.t = 0, σ_r.s = 1);
(ii) σ_r.w = σ_b.w and σ_r.wPrev = σ_b.wPrev as functions; σ_r.K = σ_b.K;
(iii) deg(σ_r.Φ) = deg(σ_b.Φ) and σ_r.w(σ_r.Φ) = σ_b.w(σ_b.Φ) =: H (= σ_b.h by (wΦ));
(iv) σ_r.R(B) = σ_b.R(B) for every B ∈ C_{σ_b.Φ}.

*Proof.* Induction on r, trivial at r = b. Step r → r+1 (so r ≤ T−1 and r+1 ≤ T < L,
hence r + 1 < L and the record (C4-rec) at index r applies — ν_r is a recentering).
(i) (r2), then (P2) and es + ht = 1.
(ii) (r8), (r9), induction.
(iii) Write Φ := σ_r.Φ, t₀ := ν_r.lift, c := ν_r.center. By (r7), σ_{r+1}.Φ = Φ − t₀;
deg(Φ − t₀) = deg Φ since deg t₀ < deg Φ (r4) and Φ is monic; so also
C_{σ_{r+1}.Φ} = C_{σ_r.Φ} as sets. *No-jump:* σ_r.w(Φ − t₀) = H. Indeed
σ_r.w(t₀) = σ_r.w(Φ) = H by (r5) and induction (iii); w(−t₀) = w(t₀); Φ, −t₀, Φ − t₀
are all nonzero (Φ − t₀ is monic of degree ≥ 1); (S1) gives w(Φ − t₀) ≥ min(H, H) = H.
If w(Φ − t₀) > H, apply (R<) to Φ = t₀ + (Φ − t₀): R(Φ) = R(t₀). But (RΦ) with (i)
gives R(Φ) = T(1), while (r6) gives R(t₀) = C(c)·T(0) with c ≠ 0 (r3); comparing the
z⁰-coefficients of T(1) and C(c)·T(0) gives 0 = c, a contradiction. So
σ_{r+1}.w(σ_{r+1}.Φ) = σ_r.w(Φ − t₀) = H, using (r8).
(iv) For B ∈ C_{σ_b.Φ} = C_{σ_r.Φ}: (r10) gives ε(σ_{r+1}.R(B)) = ε(σ_r.R(B)). The
embedding ε is injective: if Σ_{k=−N}^{M} c_k X^k = 0 in F(X), multiplying by X^N gives
a polynomial identity over the field F, so every c_k = 0 in F, hence in K (K ↪ F is
injective; by (ii) the two stages share K, so both sides live in the same K[z^{±1}]).
Hence σ_{r+1}.R(B) = σ_r.R(B); induction closes. ∎

**Theorem 3.** There exists t with (CR1) ∧ (CR3) at ν_T.

*Proof.* c := ν_T.center is nonzero (Definition 2, after (spec-cen)); by Lemma 3.2(ii)
it lies in σ_T.K = σ_b.K, a field, so c is a unit there. Apply (S6b) at σ_b with
ν := σ_b.h = H: the hypothesis wPrev(Φ) < ν is Lemma 3.1. This yields B ≠ 0,
B ∈ C_{σ_b.Φ}, σ_b.wPrev(B) = H, σ_b.R(B) = C(c)·T(−σ_b.t·H) = C(c)·T(0) (σ_b.t = 0).
By (STR) at σ_b (whose e = 1): σ_b.w(B) = σ_b.wPrev(B) = H. Now Lemma 3.2 transports:
B ∈ C_{σ_T.Φ}; σ_T.w(B) = σ_b.w(B) = H = σ_T.w(σ_T.Φ); σ_T.R(B) = σ_b.R(B) = C(c)·T(0).
So t := B works (if b = T, no transport is needed). ∎

**Corollary 3.4 (interior case, for completeness).** If i + 1 < L and ν_i is a
recentering, then t := ν_i.lift satisfies (CR1) ∧ (CR3) at ν_i, directly by
(r4), (r5), (r6) of the record at index i. ∎

## 4. Corollary 4

**Corollary 4.** RRE(p, 𝔽_p) holds for every prime p (with coherence as in
Definition 3, including the recording fence in (C4-non)).

*Proof.* At any recentering node ν_i of a coherent H: (CR1) ∧ (CR3) hold for the
recorded lift (Corollary 3.4) if i is interior, and for Theorem 3's realizer if
i = L−1. (CR2) then holds by Theorem 1(iii). ∎

*Scope note (verify its honesty):* Theorem 1(ii) — hence Corollary 4 — consumes the
(C4-non) fence "ν_i.e = 1". If the ambient definition is ever changed to record interior
non-recentering reads with e ≥ 2, Theorem 1(ii) fails and §5.3's mechanism (ii) applies;
Corollary 4 is claimed ONLY for the fenced definition stated here.

## 5. General ambient F: refutation of (CR2) and the corrected support law

### 5.1 The intended model (status flag)

§§2–4 are theorems about Definitions 1–4 alone. §5 concerns the INTENDED instances of
those definitions: the order-1 MacLane/Okutsu–Montes stages over ℚ_p. For the
refutation we exhibit one such instance; its compliance with Definition 1's axioms is
asserted as standard valuation theory (flagged, not hidden), with the two load-bearing
finite-field computations independently machine-checked. Verify: (a) the internal
consistency of the exhibited data with Definitions 1–3; (b) the correctness of the
obstruction argument GIVEN the exhibited residual map; (c) that the flag honestly
scopes what is asserted versus proved.

### 5.2 The countermodel (p = 3, F ⊇ 𝔽₉)

Data. Base stage σ₀: pair (1, 1), key Φ₀ = X, w₀(Σ a_j X^j) = min_j (v₃(a_j) + j)
(v₃ = 3-adic valuation), K₀ = 𝔽₃, R₀ = the associated graded residual: for a
single-minimizing-slot polynomial, R₀ picks the minimizing slot's leading 3-adic digit
at z-position = (slot index) (its pair has t = 0, e = 1); this is a stage (standard:
w₀ is the Gauss-type valuation of the (1,1)-side; the axioms of Definition 1 are the
usual graded-algebra facts).
Root node ν₀: species root, pair (1, 1), ψ₀ = z² + 1 ∈ 𝔽₃[z] (irreducible), g₀ = 2,
z̄₀ = i ∈ 𝔽₉ˣ (i² = −1), D₀ = 1, slope₀ = 1.
Child key (the (n2) display with t_0 = 9, t_1 = 0): σ₁.Φ = X² + 9 — over ℚ₃ this is
irreducible with unramified splitting field ℚ₃(i) (machine-checked via p-adic
factorization; e = 1, f = 2), so the instance is semantically genuine.
Child stage σ₁: pair (1, 3), K₁ = 𝔽₉ = 𝔽₃(i) ≤ F, wPrev₁ = w₀,
w₁ = the (1,3)-slot-minimum over w₀ on (X²+9)-developments, and the order-1 residual
R₁, whose value on a coefficient B = aX + b ∈ C_{σ₁.Φ} with both X-slots at the
w₀-minimum is R₁(B) = C((b̄ + ā·i)·i^m)·T(0), where ā, b̄ ∈ 𝔽₃ are the leading 3-adic
digits of a, b and i^m is a fixed unit offset depending only on the weight (single-slot
coefficients get the corresponding single term). [This is the standard order-1 residual
apparatus; (S6b) holds at σ₁ because the two-slot digits {b̄ + ā·i} already realize all
of 𝔽₉ ∖ {0} — machine-checked.]
Terminal node ν₁: species recentering, pair (1, 3) (slope₁ = 3/2 > slope₀ = 1,
satisfying (C2) with STR₁ = 1, D₁ = 2, and (C7)), center c̃ := (1+i)·i^{m₃} where m₃ is
σ₁'s offset at weight 3, ψ₁ = z − c̃, z̄₁ = c̃, recorded lift = a two-slot realizer of c̃
at weight 3 (exists: ā = b̄ = 1 with v₃(a) = 2, v₃(b) = 3). H := [ν₀, ν₁] with the
remaining recorded fields chosen to satisfy the (C4-non) clauses at i = 0 (the wV,
display, and stage-tie data are exactly the σV/σ₁ data above).

**Claim.** No t with singleton X-support satisfies (CR1) ∧ (CR3) at ν₁; hence
RRE(3, F) is FALSE for every finite F ⊇ 𝔽₉ at the intended instances, and (CR2) — which
at recenterings demands singleton support — is unfaithful whenever deg(frame key) > 1.

*Proof.* Candidates are t = u·X^j with u ∈ ℤ₃ ∖ {0} and j ∈ {0, 1} (from (CR3),
deg t < 2). By (R×), R₁(t) = R₁(u)·R₁(X)^j. R₁(u) is a monomial with scalar
ū·i^{m(w)} ∈ 𝔽₃ˣ·⟨i⟩ (a constant's digit is its leading prime-field digit times a power
of the offset unit). R₁(X): X = Φ₀ is the old key; its residual under σ₁ is a monomial
with scalar i^{m'} (the base residual of the key has coefficient 1, by (RΦ) at σ₀; the
stage transition multiplies digit scalars by powers of i). So the scalar of R₁(t) lies
in the subgroup G := 𝔽₃ˣ·⟨i⟩ = {1, 2, i, 2i} of order 4. But (CR3) requires that scalar
to be c̃ = (1+i)·i^{m₃}, an element of multiplicative order 8 (machine-checked:
ord(1+i) = 8 in 𝔽₉ˣ, and G contains no order-8 element), which is not in G.
Contradiction. Meanwhile (CR1) ∧ (CR3) is satisfiable by the recorded two-slot lift, so
the failure isolates (CR2). ∎

Machine-checked facts (independent script, exit-0): ord_{𝔽₉ˣ}(1+i) = 8; |𝔽₃ˣ·⟨i⟩| = 4;
(1+i)·i^m ∉ 𝔽₃ˣ·⟨i⟩ for all m; {b̄ + ā·i : ā, b̄ ∈ 𝔽₃} ∖ {0} = 𝔽₉ˣ; X²+9 irreducible
over ℚ₃ with a single degree-2 factor.

### 5.3 Two further refutation mechanisms (recorded for completeness)

(i) *The recorded-lift form.* The statement "the RECORDED lift satisfies the support
law" is unprovable even where the ∃-form holds: if t is a lawful recorded lift
((r4)–(r6)) and s ∈ C_Φ ∖ {0} has w(s) > w(t), then t + s is an equally lawful record —
(r5) via the strict triangle w(t+s) = w(t) (from (S1): w(t+s) ≥ min = w(t); if
w(t+s) > w(t), then w(t) = w((t+s) − s) ≥ min(w(t+s), w(s)) > w(t), contradiction), and
(r6) via (R<) — with X-support anywhere. Only the existential form can be true.

(ii) *The fence-lift flag.* If (C4-non)'s fence "ν_i.e = 1" is removed (interior reads
of stride e ≥ 2 recorded), then even at F = 𝔽_p the singleton clause is refutable at
intended instances: over a unit-shifted root key Φ₀ = X − a₀ (a₀ ≢ 0 mod p), X is a
w-unit (value 0), so X-monomials u·X^j have stage weights in STR·ℤ (STR = accumulated
stretch = 2 after one e = 2 read), while a subsequent recentering can lawfully require
the odd key weight 3 ((C2)/(C7) permit slope 3/4 after slope 1/2); the two-slot lattice
min(2v(c), 2v(d)+1) attains 3 but the monomial lattice {2v} does not (machine-checked).
So a corrected support clause must land BEFORE any such definitional change.

### 5.4 The corrected (faithful) support law, with proof — REV 2 (rebuilt)

*Rev note for this section: rev 1 defined the lower targets W_k as wPrev_{r−1}-scale
weights but asserted the summand weight e·W_k + (j₀+ek)h — the slot minimum (n1)
actually consumes e·σ_{r−1}.w(t_k) + (j₀+ek)h, and by (STR) at σ_{r−1} these differ by
the factor σ_{r−1}.e (the prior pass's critical finding). Rev 2 threads that factor.*

Setting: the intended tower. Stage σ_r has key Φ_r produced from the previous key
Φ_{r−1} by a read of data (e, h, g) := (e_{r−1}, h_{r−1}, g_{r−1}) — node r−1's pair
and descend degree — and descend polynomial ψ := ψ_{r−1} with root z̄ generating
K_r = K_{r−1}(z̄) = K_{r−1}[z]/(ψ), a degree-g extension. Coefficients t ∈ C_{Φ_r} are
developed in the PREVIOUS key: t = Σ_j B_j·Φ_{r−1}^j, slots j < e·g,
deg B_j < deg Φ_{r−1}. "Parent scale" means the wPrev_r-scale; by (n5)/(n1) at the read
r−1:

    (n1-r)   wPrev_r(t) = min over occupied slots j of ( e·σ_{r−1}.w(B_j) + j·h ),
             the minimum attained at an occupied slot.

One standard fact of the intended apparatus is consumed, flagged as in rev 1:
(F1) the slot positions of the progression j₀, j₀+e, …, j₀+e(g−1) in the previous
stage's residual variable are consecutive: position(j₀ + ek) = m + k for a fixed offset
m = m(W). [Rev 1's second consumed fact (F2) is now PROVED — Lemma 5.4.0 below — and
its flag is retired.]

**Definition (stretch).** e★ := σ_{r−1}.e, the parent frame's own ramification entry.
On coherent histories e★ ∈ {1, e}: if frame r−1 was created by a recentering
transition, (r2) gives e★ = 1; if by a non-recentering transition, (n3) ties the frame
pair to its own node's read pair, and that node's read is the read (e, h) creating
stage r, so e★ = e; for the intended base/root frame, σ_0 has pair (1, 1) (part of the
§5.1 intended-instance setting), so e★ = 1 there. Under the (C4-non) fence every
RECORDED frame has e★ = 1; e★ = e ≥ 2 lives behind the fence.

**Lemma 5.4.0 (general steepening).** In a coherent history, for every i with
i + 1 < L: ν_{i+1}.h > ν_{i+1}.e · ν_i.e · ν_i.h · ν_i.g. Consequently, when ν_i is a
non-recentering — so Lemma 3.1(b)'s slot computation applies verbatim at index i and
gives wPrev_{i+1}(Φ_{i+1}) = ν_i.e·ν_i.h·ν_i.g — the threshold one stage down clears:
wPrev_{i+1}(σ_{i+1}.Φ) < ν_{i+1}.h / ν_{i+1}.e.

*Proof.* Write (e_i, h_i, g_i) := (ν_i.e, ν_i.h, ν_i.g). By (C2) at i and i+1,
STR_{i+1} = STR_i·e_i (definition of STR), and (C6):
    h_{i+1} = slope_{i+1}·(e_{i+1}·STR_{i+1}·D_{i+1})
            = slope_{i+1}·e_{i+1}·(STR_i·e_i)·(e_i·g_i·D_i)
            > slope_i·e_{i+1}·e_i²·g_i·STR_i·D_i               [(C7); the multiplier
                                                                is a positive integer]
            = e_{i+1}·e_i·g_i·(slope_i·(e_i·STR_i·D_i)) = e_{i+1}·e_i·g_i·h_i.  ∎
(Lemma 3.1's part (c) is the e_{i+1} = 1 case.)

**(THR) The threaded slot law.** For every occupied slot j of t ∈ C_{Φ_r}, (STR) at
σ_{r−1} gives σ_{r−1}.w(B_j) = e★·wPrev_{r−1}(B_j), hence

    (THR)   wPrev_r(t) = min over occupied slots j of ( e·e★·wPrev_{r−1}(B_j) + j·h ).

So a lower-stage realizer supplied at wPrev_{r−1}-scale target W_k enters the level-r
slot minimum at weight e·e★·W_k + j·h. (Rev 1 wrote e·W_k + j·h, correct only at
e★ = 1.)

**Forced class and progression, threaded.** Write E := e·e★. gcd(e, h) = 1 and
e★ ∈ {1, e} give gcd(E, h) = 1, so every W ∈ ℤ has a unique j₀(W) ∈ [0, E) with
h·j₀ ≡ W (mod E); set P(W) := { j₀(W) + E·k : k ∈ ℕ } ∩ [0, eg) and
W_k := (W − (j₀ + Ek)·h)/E ∈ ℤ. At e★ = 1: E = e, j₀ < e, and P(W) =
{ j₀ + ek : 0 ≤ k < g } has exactly g elements.

> **(S6b′-SUPP-2).** Let σ_r be a stage of a coherent intended tower satisfying
> **(U)**: every frame strictly below r is unstretched — σ_m.e = 1 for all m < r.
> Then for every parent-scale weight W > wPrev_r(Φ_r) = e·h·g (the threshold computed
> as in Lemma 3.1(b), whose slot computation applies verbatim at index r−1) and every
> c̃ ∈ K_rˣ there is a realizer t ≠ 0, t ∈ C_{Φ_r}, with wPrev_r(t) = W and digit
> scalar c̃ at the forced position, whose Φ_{r−1}-slot support is contained in
> P(W) = { j₀(W) + e·k : 0 ≤ k < g }, and whose occupied slot coefficients are,
> recursively, (S6b′-SUPP-2)-realizers one stage down at the wPrev_{r−1}-SCALE targets
> W_k := (W − (j₀+ek)·h)/e — every level's target prescribed in THAT level's
> wPrev/regrade scale, with (THR) the conversion consumed at each ascent — down to the
> base, where realizers are p^m·û (û a unit lift, support {0} for a linear base key).

**Remark 5.4.R (recentering steps create no level).** If frame r−1 is post-recentering,
(r8)–(r10) transport w, wPrev and coefficient residuals unchanged (as in Lemma 3.2),
and the threshold transports too: developing Φ′ = Φ − lift in the previous key, every
occupied slot of Φ's display weighs exactly e′h′g′ (the Lemma 3.1(b) computation for
the creating read (e′, h′, g′)) while every occupied slot of the lift weighs
≥ wPrev(lift) = σ.h > e′h′g′ ((r5), (STR) at σ.e = 1, Lemma 5.4.0); on shared slots
the (S1) strict ultrametric keeps the display slot's weight (if w(x) < w(y) and
w(x − y) > w(x) then w(x) = w((x−y) + y) ≥ min(w(x−y), w(y)) > w(x), contradiction);
slots occupied by the lift alone weigh > e′h′g′; and the top display slot (index e′g′,
coefficient 1) is untouched since deg lift < deg Φ confines it to slots < e′g′. So
wPrev(Φ′) = e′h′g′ = wPrev(Φ). "The creating read" of a post-recentering frame means
the last non-recentering read below it. The CLEARING inequality also survives the run:
along recenterings, (spec-rec) gives e_i = g_i = 1, so STR and D are constant
(definition of STR; (C6)); with b′ the run's first index and r−1 the reading node,
(C2) gives h_{r−1} = slope_{r−1}·(e_{r−1}·STR·D) and h_{b′} = slope_{b′}·(1·STR·D),
and chained (C7) gives slope_{r−1} > slope_{b′}, hence h_{r−1} > e_{r−1}·h_{b′};
Lemma 5.4.0 at the creating read (index b′−1, with e_{b′} = 1) gives h_{b′} > e′h′g′;
composing, h_{r−1} > e_{r−1}·e′h′g′, i.e. the transported threshold still satisfies
wPrev(Φ′) = e′h′g′ < h_{r−1}/e_{r−1}.

**Theorem 5.4.1.** (S6b′-SUPP-2) holds as stated.

*Proof.* Strong induction on r ≥ 1. Fix W > ehg, c̃ ∈ K_rˣ. By (U), e★ = 1, E = e.
(1) *Class arithmetic.* On the progression the W_k are integers (choice of j₀); by
(THR) with e★ = 1 every occupied slot j weighs e·wPrev_{r−1}(B_j) + j·h ≡ j·h (mod e),
so weight-W contributions need j ≡ j₀(W) (mod e).
(2) *Design.* By (F1) the progression slots sit at consecutive residual positions
m(W), …, m(W)+g−1. Since z̄^{m(W)} is a unit and 1, z̄, …, z̄^{g−1} is a K_{r−1}-basis of
K_r, there is a UNIQUE P ∈ K_{r−1}[z], deg P < g, with z̄^{m(W)}·P(z̄) = c̃, and P ≠ 0.
Set t := Σ_{k<g, P_k≠0} t_k·Φ_{r−1}^{j₀+ek}, with t_k the shaped realizer of scalar
P_k ∈ K_{r−1}ˣ at the wPrev_{r−1}-scale target W_k — supplied by the induction
hypothesis at r ≥ 2, and at r = 1 by the base realizer p^{W_k}·û_k (û_k a unit lift of
P_k; base coefficients are constants, support {0}).
(3) *The recursive call is licensed.* W_k ≥ (W − (eg−1)h)/e > (ehg − (eg−1)h)/e = h/e;
at r ≥ 2, Lemma 5.4.0 one stage down gives wPrev_{r−1}(Φ_{r−1}) = e′h′g′ < h/e (same
threshold at a post-recentering frame by Remark 5.4.R), so W_k clears the lower
threshold; (U) restricted below r−1 is (U) for the lower call. At r = 1, W_k ≥ 1 > 0
suffices (no base threshold).
(4) *Weight — the repaired seam.* Each summand's slot weight is
e·e★·W_k + (j₀+ek)·h = e·1·W_k + (j₀+ek)·h = W: by (STR) at σ_{r−1} with e★ = 1, the
lower realizer's σ_{r−1}.w-weight EQUALS its wPrev_{r−1}-target W_k, which is what
(n1-r) consumes. All occupied slots weigh exactly W, at least one is occupied (P ≠ 0),
so the attained minimum gives wPrev_r(t) = W; t ≠ 0 since its (unique, Φ_{r−1} monic)
development has a nonzero slot.
(5) *Digit.* By (F1) the slot digits assemble as Σ_k P_k·z^{m(W)+k} = z^{m(W)}·P(z);
ψ-reduction/evaluation at z̄ gives the scalar z̄^{m(W)}·P(z̄) = c̃ at the forced
position; at a recentering consumer (stage pair e = 1, Bézout t = 0) the position is 0,
so R_r(t) = C(c̃)·T(0), matching (CR3).
(6) *Support.* The support clause is the literal index set; the recursion clause is the
construction in (2). ∎

**Proposition 5.4.2 (sharpness at every g).** In the setting of Theorem 5.4.1, fix
W > ehg and define Θ : { P ∈ K_{r−1}[z] : deg P < g } → K_r by Θ(P) := z̄^{m(W)}·P(z̄).
(a) Θ is a K_{r−1}-linear bijection.
(b) For every nonempty S ⊆ {0, …, g−1}: c̃_S := Θ(Σ_{k∈S} z^k) ∈ K_rˣ, and every
(S6b′-SUPP-2)-shaped realizer of (W, c̃_S) — progression-supported, equal slot weights,
nonzero digit scalars at occupied slots, digits assembling per (F1) — has slot support
EXACTLY { j₀(W) + ek : k ∈ S }.
(c) In particular all g progression slots are simultaneously necessary (S full), and
single-slot realizers reach only ∪_{k<g} K_{r−1}ˣ·z̄^{m(W)+k}, which for g ≥ 2 misses
every c̃_S with |S| ≥ 2: the progression length g is sharp for every g, and no
single-monomial strengthening exists at any g ≥ 2.

*Proof.* (a) Θ is K_{r−1}-linear and carries the basis 1, z, …, z^{g−1} to
z̄^m, …, z̄^{m+g−1} — the unit z̄^m times the power basis of K_r = K_{r−1}[z]/(ψ),
deg ψ = g — hence a basis; a linear map carrying a basis to a basis between spaces of
equal finite dimension is a bijection. (b) c̃_S ≠ 0 by injectivity (the argument
Σ_{k∈S} z^k ≠ 0); K_r is a field, so c̃_S is a unit. A shaped realizer assembles digit
Θ(P_t) with (P_t)_k = its slot-k scalar (nonzero when occupied, 0 otherwise), so
support(P_t) = its occupied k-set; Θ(P_t) = c̃_S = Θ(P_S) forces P_t = P_S by (a).
(c) is (b) at S = {0, …, g−1}, plus: each single-slot image is Θ(K_{r−1}ˣ·z^k) =
K_{r−1}ˣ·z̄^{m+k}, and c̃_S with |S| ≥ 2 lies outside each by uniqueness of P. ∎

*Scope of 5.4.2 (verify the honesty):* sharpness WITHIN the shaped class — the same
class rev 1's tightness claim addressed; it consumes (F1) and nothing else. An
arbitrary-realizer strengthening would need the additional graded fact that any
realizer's digit reads off its minimal-weight slot stratum by the (F1) assembly; that
fact is consumed by NOTHING here and is recorded as open, not claimed. The §5.2 F₉
countermodel is the instance g = 2, S = {0, 1} (c̃_S = (1+i)·i^m outside the union
𝔽₃ˣ·⟨i⟩ of the two basis lines); the general mechanism is machine-checked exhaustively
at g = 3 over 𝔽₂₇ for every unit offset m.

**Proposition 5.4.3 (the complement of (U) is a definitional void).** Let σ be a stage
at a STRETCHED frame of a coherent history: σ.e = e ≥ 2 (by (n3) this is a frame
created by a non-recentering transition whose own node reads at stride e ≥ 2 — behind
the (C4-non) fence; the frame pair equals its read pair, so write (e, h) := (σ.e, σ.h)
for both). For any attempted non-recentering read at σ with descend polynomial ψ of
degree g: if ψ_k ≠ 0 for some k with e ∤ (g − k) — in particular whenever e ∤ g, since
ψ_0 ≠ 0 for every irreducible ψ ≠ z — then NO (n2) display exists: there is no
t_k ∈ C_{σ.Φ}, t_k ≠ 0, with σ.w(t_k) = h·(g − k).

*Proof.* By (STR) at σ, every nonzero t_k ∈ C_{σ.Φ} has σ.w(t_k) = e·σ.wPrev(t_k) ∈
e·ℤ (wPrev is ℤ-valued by Definition 1). The display demands σ.w(t_k) = h·(g−k), and
gcd(e, h) = 1 gives e ∣ h·(g−k) ⟺ e ∣ (g−k). ∎

*(Non-vacuity: under Definition 3's fence, an interior read at a stretched frame is
already unrecordable for the independent reason that (C4-non) demands ν_i.e = 1 while
(n3) ties ν_i.e = σ.e ≥ 2. The proposition quantifies over the display equation
itself, not over coherent extensions, so it additionally rules the UNFENCED variant —
the fence-lift scenario, which is the live question — void by arithmetic.)*

*Consequence (verify the scoping logic, not the design):* towers cannot extend past a
stretched frame under Definitions 1–3, so hypothesis (U) in Theorem 5.4.1 — which is
exactly the condition the rev-1 pass identified — is the ENTIRE statable domain of the
current definitions, and adopting it loses no expressible case. Numerical instance
(flagged, intended-model): at the stretched frame with pair (2, 5) and key
X² + 2X + 4 over the p = 2 base, any onward read with g = 1 demands
σ.w(t_0) = 5 ∉ 2ℤ; the same frame's (n1) scale evaluates p ↦ 4 and the key ↦ 5
(slope 5/4) while its w has p ↦ 2, key ↦ 5 (slope 5/2) — not a rescaling of any
single valuation, so the e ≥ 2 regrade semantics is itself un-adjudicated territory
(a design note, claimed nowhere).

## 6. What acceptance of this brief certifies

1. Theorem 1, Lemmas 3.1–3.2, Theorem 3, Corollary 4: theorems of Definitions 1–4
   (check every step against the listed clauses; nothing outside them is permitted).
   [Confirmed by the rev-1 pass; byte-identical here.]
2. §5.2: a valid refutation of (CR2)-as-stated GIVEN the flagged intended-model
   instance; the flag's honesty (assertion vs proof) is part of the check.
3. §5.4 (rev 2): Lemma 5.4.0 and Proposition 5.4.3 from the Definition-1/3 clauses
   outright; (THR) from (n1)+(STR); Theorem 5.4.1 given the flagged (F1), per level;
   Proposition 5.4.2 given (F1); the honesty of the (U)-scope declaration (that it is
   displayed as a hypothesis, and that the void argument justifies calling it the
   entire statable domain).
4. The scope notes: Corollary 4's dependence on the (C4-non) fence; §5.3(ii)'s
   conditional refutation; §5.4's open items (the arbitrary-realizer sharpness
   strengthening; the e ≥ 2 interior design, claimed nowhere).
