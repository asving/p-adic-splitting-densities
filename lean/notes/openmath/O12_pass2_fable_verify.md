# O12 rev 4 — pass 2 verification report (second verifier, fresh context, model-diverse)

**Verifier**: Claude (Fable 5), hostile-verifier charge, fresh context. **Input**: ONLY
`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` (read in full; no other file
consulted — the brief is standalone as required). **Charge**: quote-and-classify
(CRITICAL ERROR vs JUSTIFICATION GAP), fix nothing; press on the torus telescope, the
allocation datum, the Haar-null partition, the determinant identities, the bottom-up
solve, and every quantifier (prime / characteristic / depth / composition / allocation);
treat any ∀-by-example as CRITICAL; verify the concrete-table identification conjuncts
are LABELED interface items, not silently consumed.

## VERDICT: SOUND-WITH-GAPS

The main logical chain — the lemma stack L1–L7 + Fact F, Theorem 1 (kernels,
determinants, solves), Corollary D (the (r1) channel with margins 3/4, 7/8, 6/7),
Theorem 2 (the (r2) master-denominator induction), Theorem 3 (the claim), Theorem 4
(the substochastic backup) — verifies CLEAN at the abstractly defined family 𝔅_n, for
every prime, every characteristic (char 2 included), every depth δ ≥ 1, every booking,
every composition datum, and every allocation datum. No critical error found. The
three rev-4 repairs (allocation datum α_e; L6e exact exhaustion off Z_e; the OL-O12-2
rescoping) are each complete as stated. Two JUSTIFICATION GAPS survive, both outside
the core chain: one in the wording of the in-claim concrete-table conjunct (b), one an
inert degenerate-case citation in L1/L4(ii). Details below, then the line-by-line log.

---

## Findings

### G1 — JUSTIFICATION GAP: §1 conjunct (b) overstates what §7 demonstrates for the two non-kernel quoted degree-3 entries

Quote (§1, scope declaration):

> "(b) at n = 3, the kernels, determinants, and each entry QUOTED in §7 match the
> (O3) forms and satisfy (i)+(ii)."

Quote (§7, degree-3 bullet):

> "block-2 kernel (q−1)/(q³−1), det (q³−q)/(q³−1); block-3 kernel (q−1)/(q⁶−1), det
> (q⁶−q)/(q⁶−1) — exactly the (O3) kernel and determinant forms at e = 2, 3 … one
> quoted junction mass, ((q−1)(q−2)+(q−1))/(q⁶−1) + (q−1)²/((q³−1)(q⁶−1)); one quoted
> final density, R = … Each quoted entry is an element of ℛ and satisfies L5's
> criterion."

Classification: **JUSTIFICATION GAP** (in an in-claim conjunct, not in the main
theorem chain). For the kernels and determinants the (O3)-form match is displayed and
I verified it (E₂ = 3, E₃ = 6 give exactly the §2.4/Theorem-1(2) forms). For the
quoted junction mass and the final density R, §7 demonstrates only ℛ-membership and
the L5 criterion (both of which I verified: (q−1)(q−2)+(q−1) = (q−1)²; the
R-denominator identity (q+1)(q⁴+q³+q²+q+1) = q⁵+2q⁴+2q³+2q²+2q+1 and its divisibility
into (q²−1)(q⁵−1) check exactly). No grammar derivation is displayed identifying these
two entries as (O3) row/assembly outputs of §2.3, so the conjunct-(b) verb "match the
(O3) forms", read distributively over the full subject list ("the kernels,
determinants, and each entry QUOTED"), is asserted beyond what is proved. The (i)+(ii)
half of conjunct (b) IS fully demonstrated for all four quoted items. Downstream
impact: none — nothing in Theorems 1–3 consumes conjunct (b). Repair is a one-line
rescope (either restrict "match the (O3) forms" to the kernels and determinants, or
display the grammar derivation of the junction mass and R).

### G2 — JUSTIFICATION GAP (inert): the slope–valuation correspondence is cited without the finite-valuation proviso where a_e = 0 is possible

Quote (L1, last sentence of statement + its proof):

> "Moreover if not all v(r_j) ≥ 1 but all are > 0, the Newton polygon of g has minimal
> slope in (0, 1). … The multiset of root valuations equals the multiset of slopes of
> the Newton polygon of g (lower convex hull of {(j, v(a_j))}, a_0 = 1; standard)."

Quote (L4(ii) proof):

> "By Lemma L1, the polygon of g has minimal slope s ∈ (0, 1)…"

Classification: **JUSTIFICATION GAP**, inert. The cited standard correspondence, as
stated, presumes all root valuations finite; a g ∈ C_e \ R_e with a_e = 0 has the root
0 with v = ∞, and the hull then spans only [i₀, e] for some i₀ > 0, so "the multiset
of root valuations equals the multiset of slopes" needs the zero-root convention
(slopes = valuations of the NONZERO roots; the minimal slope is still the minimal
finite root valuation, which lies in (0,1) since g ∉ R_e forces some finite v < 1).
L4(ii)'s conclusions survive at a_e = 0 (integer vertex heights from attained finite
points, b | L per face, the degree bounds d ≤ L_s/2 and d ≤ e − 2 use only total
length ≤ e), so no downstream statement is endangered — and in fact the table consumes
L4(ii) only on the L6e polygon cells, all of which have a_e ≠ 0 (L6e(i): every cell
requires the finite vertex equality at column 0), and Z_e "is booked nowhere". Where
the correspondence is load-bearing with full precision — L6e(i) — the document itself
inserts the guard ("Since a_e ≠ 0, no root of g is 0, all e root valuations are
finite, and (L1, last sentence)…"), which is exactly right. Repair: one clause in L1
or L4(ii) noting the a_e = 0 convention.

### No other findings. In particular:

- **No ∀-by-example anywhere.** Every numeric scan (§7 hand-checks, §8 rev-1..4
  batteries) is expressly labeled corroboration ("NOT part of the proof"), and no
  theorem cites §8. The ∀-allocation and ∀-composition quantifiers are discharged
  structurally in Theorem 2(iv) (0/1 coefficients; α_e(σ) ∈ ℚ[q] is all that is
  consumed), not by the α-battery of §8 rev 4(b).
- **The interface items are LABELED and not silently consumed.** The general-n
  identification (§1: "an interface assumption declared outside this proof, NOT
  proved here and NOT part of the claim") and the complete-degree-3-table
  identification (OL-O12-2, declared in §1 and re-declared in §7) never appear in the
  proofs of Theorems 1–3 or the lemmas; the §2.2 hand-off faithfulness is likewise
  expressly excluded ("Only the arithmetic bounds m_i < e, μ < e (Lemma L4) and the
  masses are consumed") and indeed only L4 and the masses are cited downstream.

---

## Line-by-line verification log (what was checked and how)

### §1 (frame, claim, scope)

- Solve-table definition, lowest-terms convention, (REG-p): well-posed. The (r2)
  parenthetical (the project's active-value conjunct reduces to definedness "BY
  DEFINITION" at 𝔅_n) is a stipulation about the abstract instance, explicitly
  displayed — acceptable; for the CONCRETE tables it would be part of the (labeled)
  interface identification, not this claim.
- Margins recomputed: O1: 1 − q₀^{1−E} ≥ 1 − 2^{−2} = 3/4 (E ≥ 3 at e ≥ 2); O2/O2′:
  1 − q₀^{−E} ≥ 7/8; O3: 1 − (q₀−1)/(q₀^E−1) ≥ 1 − 1/(q₀²+q₀+1) ≥ 6/7. All exact.
  e = 1 (Φ₁ = 1) trivially exceeds all margins.
- Scope declaration: conjunct (a) verified below at §7; conjunct (b) — see G1.

### §2.1–2.2 (semantic model, stratification)

- vol(C_e) = q₀^{−e}, vol(R_e) = q₀^{−E} (E = Σi): exact from L1(i)/(ii) and per-
  coordinate Haar. P(R_e|C_e) = q₀^{−(E−e)}; κ₀ = q₀^{−E}, κ₁ = (q₀−1)q₀^{−E}: exact.
- Mass bookkeeping closes: κ₀ + κ₁ + Σ_{π≠{(1,e)}} q^{−(E−e)}N_π/q^e = q^{−(E−e)}
  = P(R_e|C_e), since Σ_π N_π = q^e (all monics). Verified.
- The partition is stated "complete up to the Haar-null set Z_e" with the L6e pointer
  — the rev-3 defect (3) is repaired at the point of use, not just in the lemma.

### §2.3 (row families, grammar)

- Fact F forms: N_ρ, P_ρ definitions coherent (falling factorial on distinct
  irreducibles per degree, multiset symmetry divisor; D = 1 supply q ↦ q − 1).
- (i): (q−1)/(q^E−1) = Σ_{w≥0}(q−1)q^{−E}·q^{−Ew} — (g4) with A = (q−1)q^{−E}, c = E:
  exact.
- (iii): the bracket is exactly Σ_ε Σ_{w∈ℕ^{k−1}} (1−q^{−1})^k q^{−N_min(ε)−Σc_jw_j}
  closed via geometric series — matches L6a's volume, L6b's affine N, L6′'s closure.
  The shape factor multiplies OUT of the depth sum because L6d's (JC) is conditioned
  on {polygon = P} for ANY admissible P of the face-kind — the constancy is exactly
  what L6d proves. q^e is the C_e-conditional normalization; cells ⊆ C_e by L6a's
  ⌈h_i⌉ ≥ 1. All verified.
- (iv): row_σ(F) has only 0/1 coefficients; hand-off targets μ < e (L4), base changes
  D ≤ e; the m = 1 atoms absorbed into comp_F as data. The (O2) allocation adjustment
  t_σ + α_e(σ)q^{−E} adds total mass Σ_σ α_e(σ)·q^{−E} = (q−1)q^{−E} = κ₁: exact. The
  allocation datum is genuine displayed table data (a ℚ[q]-valued map on the finite
  verdict set, fixed per member) — rev-3 defect (1) repaired.
- Finiteness of each member's E(e): patterns of degree e, face-kinds (Σ L_j = e),
  shape vectors (z-free patterns of degree d_j ≤ e), verdicts of degree ≤ n, blocks,
  Δ′ — all finite; one composition datum and one allocation datum per member. Correct.
- Grammar (g1)–(g7): each bracketed generation in (i)–(vii) checked against the
  displayed form; all correct.

### §2.4 (bookings, solves, the e = 2 divergence)

- K^{O1} = κ₀+κ₁ = q^{1−E}; K^{O3} = κ₁/(1−κ₀) = (q−1)/(q^E−1) (resummation
  Σ_{L≥1}κ₀^{L−1}κ₁ and exit scaling Σ_{L≥0}κ₀^L = q^E/(q^E−1)): exact.
- All four balance solves recomputed; O3's multiply-through by 1−κ₀ ≠ 0 legitimate in
  ℚ(q); all three re-entrant bookings solve to s/(1−q^{1−E}); O2 to t/(1−q^{−E}).
- The e = 2 worked example recomputed in full: s = (1−1/q, 1/q−q^{−2}) from the §2.2
  strata (the pattern masses over F_q sum to q^{−1}−q^{−2}); re-entrant solve
  (q/(q+1), 1/(q+1)); O2's t = (1−1/q, 1/q−q^{−3}) via α₂ = (0, q−1) with the identity
  1/q−q^{−3} = (q^{−1}−q^{−2}) + (q−1)q^{−3}; O2 solve (q²/(q²+q+1), (q+1)/(q²+q+1)).
  All four rational-function computations exact. The divergence is correctly scoped
  OUT of the claim (value correctness excluded, §1).

### §3 lemmas

- **L1**: both directions of (i)/(ii) verified, including the ultrametric
  equality-case argument at e_k (the product of the k minimal-valuation roots is the
  unique strict-minimum term; every other k-subset carries ≥ one root of valuation
  > μ). Integrality step (v(a_i) ∈ ℤ_{≥0} forces > 0 ⟹ ≥ 1) correct. Last sentence:
  see G2 (inert gap).
- **L2**: coordinate-wise π^i-division is measure-preserving (π^iO, Haar) → (O, Haar);
  b_i = a_i/π^i is the correct coefficient (a_iπ^{e−i}/π^e). Correct.
- **L3**: reduction of Haar is uniform on F_{q₀}^e; recentering is a unit-Jacobian
  triangular coefficient map (a_i ↦ a_i + poly(a_{<i}, c̃)), hence Haar-preserving,
  and maps {h̄ = (y−c)^e} onto {reduction = y^e} = C_e (L1(i) form). A global
  measure-preserving bijection carrying the event onto C_e pushes conditional law to
  conditional law. Correct.
- **L4**: (i) m = e forces D = 1 = the excluded pattern; (ii) minimal slope a/b with
  b ≥ 2 forces b | L_s so d_s = L_s/b ≤ L_s/2 ≤ e/2 < e; other faces L ≤ e − L_s ≤
  e − 2 so d ≤ e − 2 < e; μ ≤ μD ≤ d. All verified (modulo the inert G2 proviso).
- **L5**: rational-root theorem on q^c − 1 (monic, constant −1); divisor root sets;
  positivity at real x ≥ 2. Correct.
- **L6a**: the (α)+(β) ⟺ (hull = P) equivalence verified in both directions (convex-
  minorant maximality for ⟸; the raise-near-vertex argument for ⟹). Per-column
  translation to v ≥ ⌈h_i⌉ / vertex equality (integer heights) correct; volume
  (1−q₀^{−1})^k·q₀^{−N(P)} with N = Σ_{i=0}^{e−1}⌈h_i⌉ correct (k vertex columns
  x_1..x_k; the anchor (e,0) is automatic); ⌈h_i⌉ ≥ 1 from positive slopes so cell ⊆
  C_e. Correct.
- **L6b**: (i) recomputed the three column classes under the elementary move (right of
  face: 0; distance t ∈ {1..L_j}: +t; left: +L_j); integer gains + ⌈h+z⌉ = ⌈h⌉+z give
  ΔN = x_jL_j + L_j(L_j+1)/2 = c′_j ≥ 1, state-independent. (ii) the enumeration is a
  bijection onto admissible tuples (r_j determines the class, w_j the offset;
  coprimality preserved along the class; strict slope ordering preserved under
  increments); the period-shift identity a_j^min(s+1) = a_j^min(s) + b_j verified; the
  cascade (w_j increment raises s_{j′} by exactly 1 for all j′ ≤ j) composes the
  state-independent elementary moves additively: ΔN = c_j = Σ_{j′≤j}c′_{j′}, so N is
  jointly affine in w. k w-independent (x_j fixed). k = 1 finite. Verified, including
  a worked example (e = 3, κ = ((1,1),(2,2)): N = 4 + w₁).
- **L6c**: per-coordinate conditioning; F^× at vertex columns, F at interior integer-
  height columns (t ≡ 0 mod b_j by the coprimality argument, verified); face j has
  exactly d_j − 1 interior integer-height columns and the ranges of consecutive faces
  intersect exactly in the shared vertex column. Correct.
- **Fact F**: (i) squarefreeness of z^{q^D} − z (derivative −1 in char p), the
  divisor-product identity, degree count + Möbius inversion; (ii) distinct-
  irreducible choice with multiset assignment, symmetry divisor ∏c_{D,m}!; (iii) z the
  unique monic irreducible with zero constant term. All standard and correctly
  executed; every count one fixed element of ℚ[q], characteristic-uniform. Correct.
- **L6d (the torus telescope — pressed hardest)**:
  - Orientation: R_j leading coeff = V_j (left vertex), constant = V_{j+1} (right),
    V_{k+1} = 1 (the anchor column e carries residue 1 at height h_e = 0). Verified.
  - (T1): both composites of the bijection reduce to the identity — recomputed
    symbolically (backward∘forward uses R(0) = c to recover lead(R); forward∘backward
    uses S monic to identify lead((c/S(0))S) = c/S(0)). z-freeness of the pattern vs
    S(0) ≠ 0 correctly handled via Fact F(iii) (the pattern does NOT determine
    coprimality to z; the count P_ρ is of the coprime subset — the bijection lands
    exactly there). Correct.
  - Step 2: the factorization #Joint = Σ_{V⃗}∏_j n_j is legitimate because interior
    coordinate sets are disjoint across faces (L6c) and pattern(R_j) depends only on
    face j's coefficients. The elimination order is valid: after summing V_1, …,
    V_{j−1}, the variable V_j occurs only in the j-th factor; each torus sum is
    exactly (T1) (the pairs (V_j, interior_j) enumerate ALL R of degree exactly d_j
    with the given constant term, leading coefficient ranging over F^×); the anchored
    last step is (T1) at c = 1. Verified, including the d_j = 1 (n ∈ {0,1},
    Σ = q−1 = P_{{(1,1)}}) and k = 1 edge cases.
  - Step 3: configuration count (q₀−1)^k·q₀^{Σ(d_j−1)}, equally likely by L6c;
    (q₀−1)q₀^{d_j−1} = q₀^{d_j} − q₀^{d_j−1}. Consistency (Σ_ρ P_ρ = q^d − q^{d−1})
    and the marginal/independence claim (same telescope with all-but-one face summed)
    verified. The remark's char-split example (1 + χ(c/λ) ∈ {0,2} at q odd; ≡ 1 at q
    even via derivative b ≠ 0 ⟹ squarefree, b = 0 ⟹ Frobenius square) recomputed —
    the pointwise counts genuinely vary; only the torus-summed counts are universal,
    which is exactly what the proof uses. **Correct in every characteristic.**
- **L6′**: the depth-cone closure matches §2.3(iii) exactly (checked above); the
  inspection claim "only other unbounded index is the O3 run length L" is verifiable
  against §2.3's displayed families ((i),(ii),(iv)–(vii) are finite lists; (iii) is
  the cone) — holds; ratio κ₀ = q^{−E}, E ≥ 3, (g4)-shaped. Correct.
- **L6e (the Haar-null partition — pressed hard)**: (i) for a_e ≠ 0 the hull of the
  finite diagram points is a real convex PL function on ALL of [0,e] (leftmost finite
  point = column 0, and it and the anchor are hull vertices — the hull value at the
  extreme abscissa equals its unique point height); vertices attained ⟹ integer
  heights; a_e ≠ 0 ⟹ finite root valuations ⟹ L1's correspondence applies WITH the
  guard the document states; positive slopes (a_j ≥ 1), b_k ≥ 2 from min slope ∈
  (0,1) in lowest terms, b_j | L_j from integer face drops with gcd(a_j,b_j) = 1;
  (κ,s) ↦ P injective; the g satisfies its own cell's (α) (v = ∞ qualifies) and (β)
  (attained, finite); L6a gives cell ⟹ polygon = P, hence disjointness and unique
  membership. For a_e = 0: column x₁ = 0 is a vertex column of EVERY admissible P and
  demands finite equality — no cell contains it. (ii) {a_e = 0} null; Z₂ = ∅ (v(a₂) =
  ∞ ≥ 2 ∧ v(a₁) ≥ 1 ⟹ R₂ by the L1(ii) form). (iii) the no-consumption inspection is
  borne out by my own pass: the polygon strata enter only via m(κ,ρ⃗) and L4(ii); the
  Σ = 1 identity appears only in §8 (declared non-proof). **The rev-3 defect (3) is
  fully repaired; the exact statement is proved.**
- **L7**: D_f | s in the PID via coprimality; closure under q ↦ q^δ on generators; the
  three Φ's and both solve denominators exhibited as ratios of 𝒮-elements, hence
  units. Correct.

### §4 (Theorem 1, Corollary D)

- (1): the partition-to-kernel step is sound given L1–L4, L6a/L6e; singleton state ⟹
  1×1 kernel per booking. The graded-solve parenthetical (K = κ·Id, det = (1−κ)^{#types},
  same zero set; margins claimed only for the singleton presentation) is an honest,
  correctly-scoped remark.
- (2): all reduced forms recomputed, including the O3 gcd chain
  gcd(q^E−q, q^E−1) = q − 1 via gcd(q^a−1, q^b−1) = q^{gcd(a,b)}−1 and
  gcd(q, q^E−1) = 1, and N^{O3} = q(q^{E−1}−1)/(q−1) = q(1+⋯+q^{E−2}). Exact.
- (3): all four solves rechecked (see §2.4 above); O2's rows x-free BY DEFINITION of
  the booking (labeled as such); both denominators units of ℛ.
- Corollary D: nonvanishing of the reduced numerators/denominators at q₀ ≥ 2 via L5
  (all divisors of u·q^b·∏(q^{c_i}−1)); the three margin chains recomputed;
  (q₀−1)/(q₀^E−1) ≤ 1/(q₀²+q₀+1) at E ≥ 3 exact. Correct.

### §5 (Theorem 2 — the bottom-up solve, pressed hard)

- Grammar absorption into ℛ: each of (g1)–(g6) checked ((q^d−q^{d−1})^{−1} =
  q^{1−d}(q−1)^{−1}; (g4) with c ≥ 1; (g5) = L7(ii)). Correct.
- The induction is genuinely well-founded: every β-leg in (iv)/(vi) has e′ < e
  (L4's μ < e, m < e), and (vii) is NOT a division of a row containing β_e — for
  O1/O2′/O3 the solved form comes from Theorem 1(3)'s balance-equation solution
  (the non-returning row contains only closed masses and lower-block legs, per the
  (g7) definition), for O2 the rows are x-free by the booking's definition. Both u's
  are ℛ-units. (Note: for O3, dividing the SCALED row t_σ by Φ^{O3} and dividing the
  unscaled s by 1 − q^{1−E} agree — s·(q^E/(q^E−1))·(q^E−1)/(q^E−q) = s/(1−q^{1−E});
  both readings keep β_e ∈ ℛ, so the (vii) wording is consistent.) No circularity.
- Step (iv) consumes NOTHING about the composition datum beyond 0/1 coefficients and
  nothing about α_e beyond α_e(σ) ∈ ℚ[q] — the ∀-datum quantifiers are structural,
  not exemplified. **This is the correct discharge of the rev-3 defect (1).**

### §6 (Theorems 3, 4)

- Theorem 3: immediate from D + T2; the composite-depth remark (p^{δm} is a prime
  power ≥ 2) correct.
- Theorem 4: strict diagonal dominance of I − tM with margin ε on [0,1], Levy–
  Desplanques, continuity from det = 1 at t = 0. Correct; the ε values match the
  Corollary D kernel bounds (kernel value = row sum for the 1×1 case). Correctly
  labeled as a backup, consumed nowhere.

### §7 (concrete tables)

- Degree 2 (in-claim conjunct (a)): the FULL displayed table verified as the (O2)
  member at α₂ = (0, q−1): kernel q^{−3}, Φ₂ = (q³−1)/q³, the α-identity
  1/q − q^{−3} = (q^{−1}−q^{−2}) + (q−1)q^{−3}, mass-1 total, and both componentwise
  no-feedback divisions recomputed exactly ((1−1/q)/(1−q^{−3}) = q²/(q²+q+1);
  (1/q−q^{−3})/(1−q^{−3}) = (q+1)/(q²+q+1)). Denominators divide q³(q²+q+1) |
  q³(q³−1). Conjunct (a) HOLDS as stated.
- Degree 3 (in-claim conjunct (b)): kernels and determinants match the (O3) forms at
  E = 3, 6 — verified, including the hand-checks ((q−1)/(q³−1) = κ₁/(1−κ₀) at E = 3;
  dets 6/7, 62/63 at q₀ = 2 and 12/13, 363/364 at q₀ = 3, all recomputed). The
  junction mass and final density verified ∈ ℛ with L5-clean denominators
  ((q+1)(q⁴+q³+q²+q+1) = q⁵+2q⁴+2q³+2q²+2q+1 | (q²−1)(q⁵−1) — recomputed). The
  "match the (O3) forms" clause for these two entries: see finding G1.
- The complete-degree-3 identification is declared OL-O12-2, outside the claim, in
  both §1 and §7 — labeled, and consumed nowhere. Verified.

### §8 (corroboration)

Correctly declared "NOT part of the proof"; no theorem or lemma cites it. (Incidental:
the rev-4(a) exceptional-count formula reproduces 0, 0, 512, 486, 448 at the five
(e,p,M) triples — I recomputed all — so the corroboration is at least internally
consistent, though nothing rests on it.)

### Quantifier audit (charge item 11)

- **Prime / characteristic**: L5 and L7 argue via rational roots ⊆ {0,±1} at integers
  ≥ 2 — uniform in p; Fact F and L6d are proved over EVERY finite field, and the one
  genuine characteristic split (the pointwise double-root counts at q even vs odd,
  L6d remark) is precisely what the torus sum removes. No tame/wild or large-p
  restriction anywhere in the chain.
- **Depth**: the theorem is proved for every integer δ ≥ 1 (q₀ = p^δ ≥ 2), a superset
  of any finite Δ/Δ′; (vi)'s Δ′ contents are indeed irrelevant.
- **Block/degree**: induction on e with generic n; all n-dependence ((q−1)/(q^{n+1}−1),
  verdicts of degree ≤ n, E_n bounds) enters through finite displayed lists.
- **Booking**: all four handled separately at (g7)/Theorem 1(3)/Corollary D.
- **Composition datum**: only 0/1 coefficients consumed — ∀ discharged structurally.
- **Allocation datum**: only α_e(σ) ∈ ℚ[q] consumed (the Σ = q−1 constraint is not
  even needed for ℛ-membership) — ∀ discharged structurally over the infinite family.
- **No ∀-by-example** anywhere in the proof chain.

---

## Summary for the record

- CRITICAL ERRORS: **none**.
- JUSTIFICATION GAPS: **2** — G1 (§1 conjunct (b)'s "match the (O3) forms" exceeds
  §7's demonstration for the quoted junction mass and final density; the (i)+(ii)
  half is fully verified) and G2 (L1/L4(ii) cite the slope–valuation correspondence
  without the a_e = 0 proviso; inert, since consumption is confined to the L6e cells
  and the document guards the one load-bearing use).
- The three rev-4 repairs (allocation datum, L6e exact exhaustion, OL-O12-2
  rescoping) are each verified complete.
- The interface conjuncts are labeled and not silently consumed; value correctness is
  correctly excluded; the pole-free theorem at the abstractly defined family 𝔅_n —
  Theorems 1–3 with Corollary D's margins — stands.
