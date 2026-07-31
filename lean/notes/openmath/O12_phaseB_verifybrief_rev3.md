# O12 — verification brief REV 3 (self-contained; for a fresh-context hostile verifier)

You are auditing a mathematical proof. Quote each offending passage and classify
it: CRITICAL ERROR (breaks the logical chain) vs JUSTIFICATION GAP (assume the
conclusion and keep verifying downstream). Do not fix anything. Everything
needed is in this document; no external material is required.

(This is revision 3. A first audit confirmed the determinant algebra, the
subring lemmas, and the numerical identities; the rev-2 repairs — the
L6a/L6b cell-and-exponent lemmas and the O2/O2′/O3 solve algebra — were then
audited and confirmed. The remaining defects, all repaired here: (1) the
entry lists E(e) were still schematic — membership of their members in the
denominator grammar was asserted, not exhibited; §2.3 now displays E(e) as
seven explicit row families, each with its grammar generation in brackets.
(2) The joint residual-shape counts were asserted to be standard point-count
polynomials; since adjacent polygon faces SHARE their vertex coefficients,
this needed proof. The new Lemma L6d (with Fact F) proves every joint
residual-shape probability equals a displayed product of universal
point-count ratios, uniformly in the residue characteristic, by a
fibered-product argument over the shared vertex torus. (3) One displayed
solved vector in §7 was in reversed order relative to its row order;
corrected, with the componentwise pairing now displayed.)

## 1. The claim

**Frame.** Let ℚ(q) be the field of rational functions over ℚ. For f ∈ ℚ(q)
write f = N_f/D_f in lowest terms (N_f, D_f ∈ ℚ[q] coprime, D_f ≠ 0 monic);
say *f is defined at x ∈ ℚ* iff D_f(x) ≠ 0, with value N_f(x)/D_f(x).

A *solve table of degree n* is the data: for each block index e ∈ {1, …, n}, a
finite state set S_e, a kernel matrix K_e ∈ M_{S_e}(ℚ(q)), and a finite entry
list E(e) ⊂ ℚ(q); plus a finite depth set Δ ⊂ ℤ_{≥1} with 1 ∈ Δ. Write
Φ_e := det(1 − K_e) ∈ ℚ(q). For a prime p, the table's *regularity predicate*
(REG-p) is:

    ∀ δ ∈ Δ, ∀ e ∈ {1, …, n}, with q₀ := p^δ:
    (r1) Φ_e is defined at q₀ and Φ_e(q₀) ≠ 0;
    (r2) every g ∈ E(e) is defined at q₀.

(The project's predicate carries a further conjunct in (r2), agreement of the
evaluation with a designated "active value" map; at the instance below that map
is BY DEFINITION literal evaluation on the defined locus, so the conjunct
follows from definedness. You may treat (r2) as displayed.)

**The instance.** Section 2 defines, for every n ≥ 2, a stratification (the
β cluster-law block system) and FOUR solve tables over it — the *bookings*
(O1), (O2), (O2′), (O3) — differing in which strata are booked as within-block
loop, as re-entrant exit, as plain exit. Each block has a single continuation
state; each kernel is an explicit 1×1 matrix; each E(e) is an explicit finite
list of displayed rational functions (§2.3), parametrized by one further
piece of finite table data (the composition datum of §2.3(iv), which selects
WHICH of the displayed sums occur; the claim is proved for every choice).
Write 𝔅_n for this family of tables. The project's concrete
tables are: the machine-checked degree-2 table = (O2) at n = 2; the sealed
degree-3 tables = (O3); the general-n engine = (O1). (O2′) is the re-entrant
variant of (O2), included so that both readings of "recenterings booked as
exits" are covered.

**CLAIM (the theorem to verify).** For every n ≥ 2, every booking, every
composition datum (§2.3(iv)), and EVERY prime p, the table satisfies (REG-p). Stronger, and what is actually proved:
for every integer δ ≥ 1 (not just δ ∈ Δ) and every prime power q₀ = p^δ ≥ 2,

    (i)  D_{Φ_e}(q₀) ≠ 0 and N_{Φ_e}(q₀) ≠ 0 for every e — with the margins
         Φ_e(q₀) ≥ 3/4 [O1], ≥ 7/8 [O2 and O2′], ≥ 6/7 [O3];
    (ii) D_g(q₀) ≠ 0 for every g ∈ E(e), every e.

**Scope declaration (verify the claim as stated, not the label).** "Intended
instance" refers to the objects defined in §2. Whether the project's eventual
formalized general-n tables coincide with 𝔅_n is an interface assumption
declared outside this proof, NOT proved here and NOT part of the claim.
VALUE correctness is also not part of the claim: the claim is about zeros and
poles of the tables' entries, not about whether any booking's solved values
are the true splitting densities (indeed §2.4 displays that the (O2) booking's
values differ from the (O1)/(O2′)/(O3) solve — a known, recorded fact about
the machine-checked degree-2 table; both value systems have the pole-free
structure claimed). What IS part of the claim: at n = 2 and n = 3 the
project's concrete tables (kernels, determinants, entry denominators quoted
in §7 so you can check) are instances of the (O2) resp. (O3) bookings and
satisfy (i)+(ii).

## 2. The instance 𝔅_n, defined

### 2.1 Semantic model (used to derive the kernel and the stratum masses)

For a prime power q₀ = p^m, let K₀ be the unramified extension of ℚ_p of
degree m (residue field F_{q₀}), O its ring of integers, π := p a uniformizer,
v the valuation with v(p) = 1, extended uniquely to a fixed algebraic closure
K̄₀ (where it takes values in ℚ). Identify monic degree-e polynomials
g = x^e + a_1x^{e−1} + ⋯ + a_e over O with tuples (a_1, …, a_e) ∈ O^e carrying
the Haar probability measure (each a_i independent uniform on O; the measure
of {v(a) ≥ t} is q₀^{-t} for t ∈ ℤ_{≥0}, of {v(a) = t} is (1 − q₀^{-1})q₀^{-t}).
The *splitting type* of g is the multiset {(e_i, f_i)} of ramification indices
and residue degrees of the irreducible factors of g over K₀; it depends only
on the K₀-algebra K₀[x]/(g) when g is separable (multiplicities are handled by
the classifier's bookkeeping and play no role in this proof).

### 2.2 The block state and the one-step stratification

Block e ∈ {1, …, n} has one continuation state, the *aligned size-e cluster*:
Haar conditioned on

    C_e := {g : all e roots of g in K̄₀ have v > 0} = {v(a_i) ≥ 1, i = 1..e},

(the set equality is Lemma L1(i); volume q₀^{-e}). Block 1 terminates
immediately: K_1 := (0), Φ_1 = 1.

Define R_e := {g : all e roots have v ≥ 1} = {v(a_i) ≥ i, i = 1..e}
(Lemma L1(ii); volume q₀^{-E} where E = E_e := e(e+1)/2 = 1 + 2 + ⋯ + e).
Note R_e ⊆ C_e. One classifier step from the state stratifies C_e:

(S-loop) *Descend and re-cluster at a rational center.* On R_e, the rescale
h(y) := g(πy)/π^e is again monic of degree e over O; conditioned on R_e, h is
Haar-uniform (Lemma L2) with the same splitting type. Sub-stratify by the
reduction h̄ ∈ F_{q₀}[y]: on {h̄ = (y − c)^e} (c ∈ F_{q₀}; volume q₀^{-e} each),
the recentered h(c̃ + y) (c̃ a lift of c) is Haar conditioned on C_e — the
state law again (Lemma L3). Masses, conditional on C_e:

    center c = 0:      κ₀ := q₀^{-(E−e)} · q₀^{-e} = q₀^{-E}
    centers c ≠ 0:     κ₁ := (q₀ − 1) · q₀^{-E}

(P(R_e | C_e) = q₀^{-E}/q₀^{-e} = q₀^{-(E−e)}.)

(S-exit) *Everything else leaves the block.* The COMPLETE one-step partition
of the state law is:

    C_e = R_e ⊔ (C_e \ R_e)                                 [L1 dichotomy]
    R_e:  partitioned by the reduction h̄ of the rescale — all q₀^e monic
          degree-e polynomials over F_{q₀}, grouped by factorization pattern:
       (i)   h̄ = y^e (the pattern {(1,e)} at center 0): the in-place loop, κ₀;
       (ii)  h̄ = (y−c)^e, c ≠ 0: the recentering strata, total κ₁;
       (iii) every other pattern π = {(D_i, m_i)} (D_i = degree of an
             irreducible factor, m_i its multiplicity, Σ D_i m_i = e,
             π ≠ {(1,e)}): mass q₀^{−(E−e)} · N_π(q₀)/q₀^e, where N_π = the
             number of monics with pattern π; each part with m_i ≥ 2 is
             booked as a hand-off to block m_i at base change q ↦ q^{D_i}
             (and m_i < e by Lemma L4(i)); parts with m_i = 1 terminate
             (simple Hensel factors).
    C_e \ R_e (Newton polygon with minimal slope in (0,1) — Lemma L1):
          partitioned by the polygon P and residual shape (§3, L6a/L6c/L6d);
          each residual factor of multiplicity μ ≥ 2 and degree D is booked
          as a hand-off to block μ at base change q ↦ q^D (μ < e by Lemma
          L4(ii)); multiplicity-1 factors terminate.

The BOOKINGS of the block-index targets displayed in (iii) and in the
C_e \ R_e line are part of the table's DEFINITION (they say which lower
block's β-leg multiplies which mass); their semantic faithfulness (that the
handed-off sub-cluster's law is the target block's state law — the standard
Montes/Okutsu residual descent) is a value-correctness matter, expressly
outside the claim, and is consumed nowhere below. Only the arithmetic bounds
m_i < e, μ < e (Lemma L4) and the masses are consumed.

### 2.3 The table rows: the explicit entry table E(e), and the grammar

Throughout, E := e(e+1)/2. Two count polynomials recur (both proved, with
their universality over residue characteristics, in Fact F of §3). Let a
*pattern* be a finite multiset ρ of atoms (D, m) ∈ ℤ_{≥1}², its *total
degree* Σ D·m; write c_{D,m} := the number of atoms equal to (D, m) in ρ,
r_D := Σ_m c_{D,m}, and (M)_r := M(M−1)⋯(M−r+1). With
M_D(q) := D^{−1} Σ_{δ|D} μ(δ) q^{D/δ} (μ = the Möbius function):

    N_ρ(q) := ∏_D ( (M_D(q))_{r_D} / ∏_m c_{D,m}! )
    P_ρ(q) := the same product with the D = 1 supply M_1(q) = q replaced
              by q − 1.

(Fact F: over F_q, N_ρ counts the monic polynomials of degree = total
degree with factorization pattern ρ; P_ρ counts those coprime to z, i.e.
with nonzero constant term — call such ρ *z-free*. Both are polynomials in
q with ℚ-coefficients, the same for every residue characteristic.)

**The row families of block e** (e ≥ 2; block 1 has K_1 = (0), Φ_1 = 1,
E(1) := {1}). Each family is displayed with its 𝒢 generation in brackets —
these bracketed exhibitions are what Theorem 2's induction consumes.

(i) *the kernel entry*, per booking (§2.4): q^{−E} or q^{1−E}
    [(g1)·(g2) via (g6)], or (q−1)/(q^E−1) = Σ_{w≥0} q^{−Ew}·(q−1)q^{−E}
    [(g4) with A = (q−1)q^{−E} and c = E].

(ii) *divisor-pattern masses*, one per pattern π of total degree e,
    π ≠ {(1, e)}:

        m(π) := q^{−(E−e)} · N_π(q) · q^{−e}

    [(g1) for N_π (Fact F); (g2) twice; (g6)].

(iii) *polygon-family masses*, one per face-kind κ = (L_j, b_j)_{j=1..k}
    (§3) and residual-shape vector ρ⃗ = (ρ_1, …, ρ_k), each ρ_j a z-free
    pattern of total degree d_j := L_j/b_j:

        m(κ, ρ⃗) := q^e · [ Σ_{ε ∈ Enum(κ)} (1 − q^{−1})^k q^{−N_min(ε)}
                            ∏_{j=1}^{k−1} q^{c_j}/(q^{c_j}−1) ]
                        · ∏_{j=1}^{k} P_{ρ_j}(q) · (q^{d_j} − q^{d_j−1})^{−1}

    where Enum(κ) is the finite enumeration of L6b(ii), N_min(ε) ∈ ℤ_{≥1}
    is the exponent N at the nested minima of the enumeration point ε, and
    c_j ∈ ℤ_{≥1} are L6b's exponents. The final product is the joint
    residual-shape probability, ONE fixed element of ℚ(q) valid for every
    polygon of the family and every residue characteristic — that is Lemma
    L6d; being constant across the family, it multiplies the closed cell
    sum. [q^e: (g1); the bracket: finitely many (g3) volumes times (g4)
    closures with c_j ≥ 1, combined by (g6); the shape factor: (g1)·(g2)
    per face by L6d, combined by (g6).]

(iv) *verdict rows*. Finite table data, fixed per booking: each family F
    from (ii)/(iii) carries its *hand-off list* H(F) = ((μ_1, D_1), …,
    (μ_r, D_r)), read off F's pattern data — the atoms (D, m) with m ≥ 2
    (of π for (ii); of the ρ_j for (iii)), booked to block μ = m at base
    change q ↦ q^D (§2.2; μ < e by Lemma L4) — and a *composition datum*:
    a map comp_F assigning to each tuple (σ_1, …, σ_r) of verdicts of the
    hand-off blocks a verdict of block e (verdicts = splitting types of
    degree ≤ n, a FINITE set; the m = 1 atoms terminate and are absorbed
    into comp_F as fixed data). The verdict row of F at verdict σ is

        row_σ(F) := m(F) · Σ_{(σ_1,…,σ_r) : comp_F(σ_1,…,σ_r) = σ}
                             ∏_{i=1}^{r} β_{μ_i}(σ_i)(q^{D_i}),

    a finite sum of products with coefficients 0 or 1 — no other scalars
    enter. r = 0 gives the terminal rows (row_σ(F) = m(F) when comp_F() =
    σ, else the row is absent); r = 1 the split rows; r ≥ 2 the junction
    rows. Per verdict, the aggregated row t_σ := Σ_F row_σ(F) — again a
    0/1-coefficient finite sum. Booking adjustments (§2.4): under (O2) the
    designated terminal rows additionally carry the summand
    κ₁ = (q−1)q^{−E} [(g1)·(g2), then (g6)]; under (O3) every exit row is
    multiplied by the scaling q^E/(q^E−1) of family (v) [(g6)]. Both
    adjusted rows are included in E(e). [(g5) on the lower-block β's, then
    (g6). Theorem 2 is proved for EVERY choice of composition data — the
    project's specific choice, a value-correctness matter outside the
    claim, is thereby covered.]

(v) *entrance and shape weights*: the finite concrete list

        { q^{−b} : 0 ≤ b ≤ E_n } ∪ { (q^d − q^{d−1})^{−1} : 1 ≤ d ≤ n }
        ∪ { (q−1)/(q^{n+1}−1) } ∪ { q^{E_m}/(q^{E_m}−1) : 2 ≤ m ≤ n }

    (the last are the (O3) exit-row scalings Σ_{L≥0} κ₀^L). [(g2); the
    last: (g4) with A = 1, c = E_m.]

(vi) *β-legs*: β_{e′}(σ′)(q^δ) for e′ < e, verdicts σ′ of degree ≤ n, and
    δ in any fixed finite Δ′ ⊂ ℤ_{≥1} containing Δ and the base changes of
    (iv) (all D ≤ e); plus the σ′-aggregates Σ_{σ′} β_{e′}(σ′)(q^δ).
    [(g5) on already-solved entries; (g6). Theorem 2 in fact proves
    membership for every δ ≥ 1, so Δ′'s contents are irrelevant.]

(vii) *block e's own solved entries* β_e(σ) := u^{−1}·t_σ, u the booking's
    solve denominator (§2.4, Theorem 1(3)). [(g7).]

E(e) := the union of (i)–(vii): a finite set of displayed rational
functions. Finiteness: patterns π of degree e, face-kinds, shape vectors,
verdicts of degree ≤ n, blocks, Δ′, and the composition data are all finite
sets. 𝔅_n is the resulting FAMILY of tables — one member per booking (§2.4)
and per composition datum in (iv) — and the claim of §1 is proved for every
member.

The grammar 𝒢 below is the PROOF DEVICE (not the definition of E(e)): the
bracketed annotations of (i)–(vii) exhibit every member of E(e) as built by
finitely many applications of

  (g1) polynomials in ℚ[q] (point counts, pattern counts N_π, residual-shape
       counts, e.g. D^{-1}Σ_{δ|D} μ(δ)q^{D/δ});
  (g2) the normalizations q^{-b} (b ≥ 0), (q^d − q^{d−1})^{-1} (d ≥ 1), and
       (q − 1)/(q^{n+1} − 1) (the projective assembly weight);
  (g3) fixed-depth cell volumes (1 − q^{-1})^V · q^{-N} (V, N ∈ ℤ_{≥0});
  (g4) geometric depth closures: sums Σ_{w ≥ 0} A·q^{-c·w} = A·q^c/(q^c − 1)
       with c ∈ ℤ_{≥1} and A already generated (Lemma L6 proves ALL the
       depth sums occurring in 𝔅_n's stratum families have this form, with
       c ≥ 1 and A depth-free);
  (g5) base change q ↦ q^δ, δ ∈ ℤ_{≥1};
  (g6) finite sums and products of generated elements;
  (g7) the block solve, bottom-up in e: β_e := the unique ℚ(q)-solution of
       block e's balance equation

           x = (within-block return mass)·x + (non-returning row),

       where the non-returning row is generated by (g1)–(g6) from the closed
       masses and from β_{e′}, e′ < e, composed with (g5). Per booking
       (§2.4) the return mass is κ₀ + κ₁ (O1, O2′, O3 — for O3 in the
       equivalent resummed form) or κ₀ alone (O2); in every case the solved
       form is β_e = u^{−1}·(row), with u ∈ {1 − q^{1−E}, 1 − q^{−E}} a UNIT
       of the subring ℛ of Lemma L7 (Theorem 1(3) displays the four cases).

### 2.4 The four bookings

With κ₀ = q^{-E}, κ₁ = (q−1)q^{-E} ∈ ℚ(q) (now symbolic):

    (O1)  K_e = (κ₀ + κ₁) = (q^{1−E})     [loop = all e-fold rational
                                           centers; one step]
    (O2)  K_e = (κ₀)      = (q^{-E})      [loop = center 0 only; the κ₁ mass
                                           is booked INTO the terminal/exit
                                           rows as a plain ℚ(q) summand; NO
                                           row re-enters block e]
    (O2′) K_e = (κ₀)      = (q^{-E})      [loop = center 0; the κ₁ strata
                                           booked as exit legs that RE-FEED
                                           block e's own entrance]
    (O3)  K_e = (κ₁/(1−κ₀)) = ((q−1)/(q^E − 1))
                                          [in-place branch resummed into the
                                           recentering loop: Σ_{L≥1} κ₀^{L−1}κ₁;
                                           exit rows scaled by
                                           Σ_{L≥0} κ₀^L = 1/(1−κ₀)]

Balance equations and solves (s := the non-returning exit row):

    (O1)  x = (κ₀+κ₁)x + s            ⟹  x = s/(1 − q^{1−E})
    (O2′) x = κ₀x + (κ₁x + s)         ⟹  x = s/(1 − q^{1−E})   [same]
    (O3)  (1 − κ₁/(1−κ₀))x = s/(1−κ₀) ⟹  x = s/(1 − q^{1−E})   [same;
                                           multiply through by 1−κ₀ ≠ 0]
    (O2)  x = κ₀x + t, t := s + (κ₁ distributed into designated exit rows)
                                      ⟹  x = t/(1 − q^{−E})

(O2) has no feedback: its solve is a genuine division by 1 − κ₀. Its solved
VALUES differ from the common (O1)/(O2′)/(O3) solve. At e = 2 (E = 3) the
§2.2 strata give the true exit row s = (1 − 1/q, 1/q − q^{−2}) (first entry:
the no-descent stratum, terminal; second: descend-then-split-or-inert), so
the re-entrant solve is s/(1 − q^{−2}) = (q/(q+1), 1/(q+1)); the (O2)
booking instead carries t = (1 − 1/q, 1/q − q^{−3}) (the κ₁ = q^{−2} − q^{−3}
mass folded into the second row) and solves to t/(1 − q^{−3}) =
(q²/(q²+q+1), (q+1)/(q²+q+1)). The divergence arises because folding the κ₁
mass into a terminal row departs from the semantics of Lemma L3 (the
recentered cluster re-enters the state law); it is a recorded property of
the machine-checked degree-2 table and is OUTSIDE the claim (§1 scope);
both value systems have all denominators in ℛ, which is what is claimed.

## 3. Lemmas (complete proofs)

**Lemma L1** (valuations of coefficients vs roots). Let g = x^e + a_1x^{e−1}
+ ⋯ + a_e over O with roots r_1, …, r_e ∈ K̄₀ (with multiplicity). Then:
(i) all v(r_j) > 0 ⟺ v(a_i) ≥ 1 for all i; (ii) all v(r_j) ≥ 1 ⟺
v(a_i) ≥ i for all i. Moreover if not all v(r_j) ≥ 1 but all are > 0, the
Newton polygon of g has minimal slope in (0, 1).

*Proof.* (⇒) a_i = ±e_i(r_1, …, r_e), a sum of products of i distinct roots;
ultrametrically v(a_i) ≥ i·μ where μ := min_j v(r_j). If μ > 0 then
v(a_i) > 0, and v(a_i) ∈ ℤ_{≥0} (a_i ∈ O) forces v(a_i) ≥ 1; if μ ≥ 1 then
v(a_i) ≥ i.
(⇐) Let k := #{j : v(r_j) = μ}. In e_k(r), the product of the k roots of
minimal valuation has valuation kμ; every other product of k roots contains at
least one root of valuation > μ and at most k − 1 of valuation μ, hence has
valuation > kμ. By the ultrametric equality case (a sum with a unique
strict-minimum term has the minimum valuation), v(a_k) = kμ. If v(a_i) ≥ 1 ∀i:
kμ ≥ 1 > 0 so μ > 0, i.e. all roots have v > 0. If v(a_i) ≥ i ∀i: kμ ≥ k so
μ ≥ 1.
(Last sentence) The multiset of root valuations equals the multiset of slopes
of the Newton polygon of g (lower convex hull of {(j, v(a_j))}_{j=0..e},
a_0 = 1; standard). All roots v > 0 and some root v < 1 means the minimal
slope μ ∈ (0, 1). ∎

**Lemma L2** (rescale self-similarity). Conditioned on R_e = {a_i ∈ π^iO ∀i},
the coefficients b_i := a_i/π^i of h(y) := g(πy)/π^e are independent Haar-
uniform on O, and g, h have equal splitting types.

*Proof.* Division by π^i is a measure-preserving isomorphism (π^iO, Haar) →
(O, Haar), applied independently per coordinate; h(y) = y^e + Σ b_i y^{e−i}
with b_i = a_i/π^i. K₀[x]/(g) ≅ K₀[y]/(h) via x = πy, so identical splitting
data; root multisets correspond via r ↦ r/π. ∎

**Lemma L3** (re-cluster). For Haar-uniform monic h of degree e: the reduction
h̄ is uniform on the q₀^e monic degree-e polynomials over F_{q₀}; for each
c ∈ F_{q₀}, the event {h̄ = (y − c)^e} has volume q₀^{-e}, and conditioned on
it, h(c̃ + y) is Haar conditioned on C_e (the block state law), with splitting
type equal to that of h.

*Proof.* Coefficient-wise reduction of Haar is uniform on F_{q₀}^e, so h̄ is
uniform; each singleton reduction event has volume q₀^{-e}. Recentering
h ↦ h(c̃ + ·) is a Haar-measure-preserving bijection of the monic degree-e
space (it is a polynomial triangular change of coordinates on O^e with unit
Jacobian — the coefficient map is a_i ↦ a_i + (polynomial in a_{<i}, c̃) —
translation-invariance of Haar), and it maps {h̄ = (y−c)^e} onto
{reduction = y^e} = C_e (Lemma L1(i) form). Splitting types are invariant
under x ↦ x + c̃. ∎

**Lemma L4** (all exits leave the block). (i) If h̄ (deg e, monic) is not an
e-fold rational point, then every primary component of h̄ is P^m with P
irreducible of some degree D ≥ 1 and D·m ≤ e, (D, m) ≠ (1, e); each such
component has m < e. (ii) If g ∈ C_e \ R_e, every residual factor of
multiplicity μ ≥ 2 arising from its polygon has μ < e.

*Proof.* (i) Σ_P deg(P)·m_P = e; a component with m = e forces D = 1 — the
excluded e-fold rational point. So every component has m < e.
(ii) By Lemma L1, the polygon of g has minimal slope s ∈ (0, 1); s = a/b in
lowest terms with b ≥ 2. The face of slope s has horizontal length divisible
by b, say L_s = b·d_s, so its residual polynomial has degree d_s ≤ L_s/2 ≤ e/2
< e. Every other face has length L ≤ e − L_s ≤ e − 2, with residual degree
d ≤ L ≤ e − 2 < e. A multiplicity-μ, degree-D irreducible factor of a face's
residual polynomial of degree d has μ ≤ μD ≤ d < e. (The table BOOKS such a
factor as a hand-off to block μ at base change q ↦ q^D — a definition, §2.2;
only the bound μ < e is consumed by the theorems.) ∎

**Lemma L5** (rational roots of cyclotomic-type polynomials). For c ≥ 1 the
rational roots of q^c − 1 lie in {1, −1}. Any polynomial dividing some
u·q^b·∏_i(q^{c_i} − 1) (u ∈ ℚ^×, b ≥ 0, c_i ≥ 1) has rational roots only in
{0, 1, −1}; in particular it does not vanish at any rational x with |x| ≥ 2,
and for real x ≥ 2 each factor is strictly positive (x^b > 0,
x^c − 1 ≥ 2^c − 1 ≥ 1).

*Proof.* q^c − 1 is monic over ℤ with constant term −1; by the rational root
theorem any rational root is an integer dividing 1. The root set of a divisor
is contained in the root set of the product, which is {0} ∪ {±1}. A prime
power p^δ (δ ≥ 1) is an integer ≥ 2. ∎

**Lemma L6** (polygon strata: cell identification, volume, depth closure).
Setting: write the *Newton diagram* of g as the point set
{(i, v(a_{e−i})) : i = 0, …, e−1} ∪ {(e, 0)} (column i carries the
coefficient a_{e−i}; the anchor (e, 0) is the monic leading 1), and the
*Newton polygon* as its lower convex hull, read as a function
H : [0, e] → ℝ_{≥0} (the largest convex function below the diagram). A
*face-kind sequence* is κ = (L_j, b_j)_{j=1..k}: L_j ≥ 1, Σ_j L_j = e,
b_j | L_j (write d_j := L_j/b_j), b_k ≥ 2; set x_1 := 0, x_{j+1} := x_j + L_j
(so x_{k+1} = e). An *admissible slope tuple* is s_1 > ⋯ > s_k with
s_j = a_j/b_j in lowest terms (a_j ≥ 1, gcd(a_j, b_j) = 1) and s_k ∈ (0, 1).
The polygon P = P(κ; s) is the convex piecewise-linear function with
P(e) = 0 and slope −s_j on [x_j, x_{j+1}]; heights h_i := P(i) (strictly
decreasing, h_e = 0); vertex columns x_1, …, x_k, whose heights
h_{x_j} = Σ_{j′ ≥ j} a_{j′}d_{j′} are INTEGERS (each face drops
L_{j′}s_{j′} = a_{j′}d_{j′} ∈ ℤ).

**L6a (cell identification and volume — the semantic link).** For every
admissible P,

    { g : Newton polygon of g = P }
      = { g : v(a_{e−i}) ≥ ⌈h_i⌉ for EVERY column i ∈ {0,…,e−1},
              with equality v(a_{e−x_j}) = h_{x_j} at the k vertex columns },

of Haar volume exactly

    (1 − q₀^{−1})^k · q₀^{−N(P)},   N(P) := Σ_{i=0}^{e−1} ⌈h_i⌉,

with every ⌈h_i⌉ ≥ 1 (so the event lies in C_e).

*Proof.* "Hull = P" holds iff (α) every diagram point lies on or above P and
(β) every vertex of P is a diagram point. [If (α), P is a convex minorant of
the diagram, so P ≤ H (H is the largest one); if also (β), then at each
vertex column H ≤ (diagram point) = P, and on each face H ≤ the chord of its
endpoint values (convexity) = P; so H = P. Conversely if H = P: (α) is the
definition of a lower hull, and each vertex of H must be attained by a
diagram point — otherwise H could be raised near that vertex and remain a
convex minorant, contradicting maximality.] Now (α) at column i reads
v(a_{e−i}) ≥ h_i ⟺ v(a_{e−i}) ≥ ⌈h_i⌉ (v is an integer or ∞); (β) at vertex
column x_j reads v = h_{x_j} (an integer); the anchor gives v(1) = 0 = h_e
automatically. The coordinates are independent Haar with P(v ≥ t) = q₀^{−t},
P(v = t) = (1 − q₀^{−1})q₀^{−t} (t ∈ ℤ_{≥0}); the event is one such condition
per column — the displayed product. All slopes > 0 and h_e = 0 give h_i > 0
for i < e, hence ⌈h_i⌉ ≥ 1 and the cell ⊆ C_e (L1(i) form). ∎

**L6b (affine exponents with positive integer coefficients).** Fix κ.
(i) The elementary move a_j ↦ a_j + b_j (slope of face j alone grows by 1)
changes N by exactly c′_j = x_j·L_j + L_j(L_j+1)/2 ∈ ℤ_{≥1}.
(ii) The admissible slope tuples decompose as a FINITE enumeration (the
rightmost numerator a_k ∈ {1,…,b_k−1} coprime to b_k; the residues
r_j = a_j mod b_j, gcd(r_j, b_j) = 1, for j < k) times free gap variables
w_1, …, w_{k−1} ∈ ℕ, along which N is affine with constant coefficients

    c_j = Σ_{j′ ≤ j} c′_{j′} ∈ ℤ_{≥1},

and the vertex count k is w-independent. A face-kind with k = 1 has NO
unbounded parameter (the family is finite).

*Proof.* (i) Anchor P at the right (h_e = 0 fixed). Under the move: columns
strictly right of face j are unchanged; the column at distance
t ∈ {1, …, L_j} from face j's right endpoint x_{j+1} gains exactly t (the
slope over the face grew by 1, the right endpoint is fixed); every column
strictly left of face j gains the face's full extra drop b_j·d_j = L_j. All
gains are integers z, and ⌈h + z⌉ = ⌈h⌉ + z, so ΔN = x_j·L_j + Σ_{t=1}^{L_j} t
= c′_j ≥ 1 (L_j ≥ 1). The vertex columns are the x_j, fixed by the L's.
(ii) Enumerate a_k finitely (s_k ∈ (0,1)). For j < k, given s_{j+1}, the
admissible a_j run over {a_j^min(s_{j+1}) + b_j·w_j : w_j ∈ ℕ}, where
a_j^min(s_{j+1}) is the least element of the class r_j + b_jℤ with
a_j/b_j > s_{j+1}. Two facts compose: a unit step of w_j is the elementary
move on face j (ΔN = c′_j, by (i)); and when s_{j+1} grows by 1, the minimum
shifts by one full period — a_j^min(s_{j+1} + 1) = a_j^min(s_{j+1}) + b_j
(a/b_j > s + 1 ⟺ (a − b_j)/b_j > s, a bijection of the residue class). So in
the iterated right-to-left sum, with each a_{j′} evaluated at its nested
minimum, a unit increment of w_j performs the elementary move on face j and,
through the shifted minima, on every face j′ < j: ΔN = Σ_{j′≤j} c′_{j′}
= c_j ≥ 1. For k = 1 only the finite a_k remains. ∎

**L6c (the multiplier is depth-free).** Conditioned on {polygon = P}, the
residues u_i := (a_{e−i}/π^{h_i} mod π) at the integer-height columns of
each face (those at distances t ≡ 0 mod b_j from face j's right endpoint —
a classification depending only on b_j, since t·a_j/b_j ∈ ℤ ⟺ b_j | t by
coprimality) are independent, uniform on F_{q₀}^× at vertex columns (where
v = h_i exactly) and uniform on F_{q₀} at interior integer-height columns
(where v ≥ h_i = ⌈h_i⌉); the anchor contributes the constant 1. Hence the
joint law of the face residual polynomials (degree d_j, coefficients the u's
of face j, nonzero ends) depends only on κ — not on the slopes. (That every
JOINT residual-shape probability under this law is one fixed count ratio of
the forms (g1)/(g2) is Lemma L6d below — it needs an argument, because
adjacent faces SHARE their vertex coefficients.)

*Proof.* L6a's event is a per-coordinate product, so conditioning acts per
coordinate; {v = t} makes the residue of a/π^t uniform on F^×, {v ≥ t}
uniform on F; independence is Haar's. The column classification and counts
depend only on (L_j, b_j). ∎

**Fact F (universal pattern counts).** Over every finite field F_q, with
the notation of §2.3 (patterns ρ, atom counts c_{D,m}, r_D, falling
factorials (M)_r, M_D(q) = D^{−1}Σ_{δ|D} μ(δ)q^{D/δ}):
(i) the number of monic irreducibles of degree D in F_q[z] is M_D(q);
(ii) the number of monic polynomials of degree = (total degree of ρ) with
factorization pattern ρ is N_ρ(q) = ∏_D ( (M_D(q))_{r_D} / ∏_m c_{D,m}! );
(iii) the number of those coprime to z (nonzero constant term) is P_ρ(q) —
the same product with the D = 1 supply M_1(q) = q replaced by q − 1.
All are polynomials in q with ℚ-coefficients, independent of the
characteristic.

*Proof.* (i) In F_q[z], z^{q^D} − z is squarefree (its formal derivative is
−1, so it is coprime to its derivative) and equals the product of ALL monic
irreducibles of degree dividing D — the standard finite-field facts: its
roots are exactly the elements of F_{q^D} inside a fixed algebraic closure;
the minimal polynomial of such a root has degree δ | D (its root generates
a subfield F_{q^δ} ⊆ F_{q^D}); conversely every monic irreducible of degree
δ | D has all its roots in F_{q^δ} ⊆ F_{q^D}, hence divides z^{q^D} − z, and
distinct monic irreducibles are coprime. Comparing degrees:
q^D = Σ_{δ|D} δ·I_δ where I_δ := #{monic irreducibles of degree δ}; Möbius
inversion of δ ↦ δI_δ gives D·I_D = Σ_{δ|D} μ(δ) q^{D/δ}, i.e. I_D = M_D(q).
(ii) By unique factorization in F_q[z], a monic polynomial with pattern ρ is
exactly: for each degree D, a choice of r_D DISTINCT monic irreducibles of
degree D together with an assignment of the multiplicity multiset
{m with multiplicity c_{D,m}} to them. Ordered choices: (M_D(q))_{r_D};
assignments that differ only by permuting irreducibles given equal
multiplicities coincide: divide by ∏_m c_{D,m}!. (iii) The only monic
irreducible with zero constant term is z itself (if P(0) = 0 then z | P, so
P = z by irreducibility): remove it from the degree-1 supply, q ↦ q − 1.
Every displayed expression is a fixed element of ℚ[q]. ∎

**L6d (joint count-rationality at the shared vertices).** Fix a face-kind
κ = (L_j, b_j)_{j=1..k}, d_j := L_j/b_j, and orient face j's residual
polynomial as

    R_j(z) := Σ_{m=0}^{d_j} u_{x_{j+1} − m·b_j} · z^m,

so its leading coefficient is the LEFT vertex residue V_j := u_{x_j}, its
constant term the RIGHT vertex residue V_{j+1} := u_{x_{j+1}}, and its
interior coefficients the d_j − 1 interior integer-height residues of face
j; V_{k+1} = 1 (the anchor). Adjacent faces SHARE the vertex residue
V_{j+1}. Let ρ⃗ = (ρ_1, …, ρ_k) assign each face a z-free pattern of total
degree d_j (z-free is automatic: both ends of R_j are nonzero). Then,
conditioned on {polygon = P} for ANY admissible P of face-kind κ, and over
EVERY residue field F_{q₀} (any characteristic),

    Prob( pattern(R_j) = ρ_j for all j simultaneously )
      = ∏_{j=1}^{k} P_{ρ_j}(q₀) · (q₀^{d_j} − q₀^{d_j−1})^{−1}     — (JC) —

— one fixed element of ℚ(q) of the displayed standard kind (the (g1) counts
P_{ρ_j} of Fact F times the (g2) normalizations), the same for every
admissible P of the face-kind, every depth parameter, and every residue
characteristic. In particular the face shape events are mutually
INDEPENDENT — the joint law is the product of its marginals — although the
polynomials R_j themselves are coupled through the shared vertices.

*Proof.* By L6c the residue coordinates are independent: V_1, …, V_k
uniform on F^× (F := F_{q₀}), the interior residues uniform on F, the
anchor constant 1; and faces share ONLY vertex residues (the integer-height
columns of face j lie in [x_j, x_{j+1}], and consecutive column ranges
intersect exactly in the vertex {x_{j+1}}).

Step 1 (the torus identity). For every d ≥ 1, every z-free pattern ρ of
total degree d, and EVERY c ∈ F^×:

    #{ R ∈ F[z] : deg R = d, R(0) = c, pattern(R) = ρ } = P_ρ(q₀), — (T1) —

independent of c. Proof: bijection with {S monic : deg S = d, S(0) ≠ 0,
pattern(S) = ρ}, whose size is P_ρ(q₀) by Fact F(iii). Forward:
R ↦ S := lead(R)^{−1}·R — monic, S(0) = c/lead(R) ≠ 0, and patterns are
unchanged by unit scalar multiples (unique factorization). Backward:
S ↦ (c/S(0))·S — constant term c, leading coefficient c/S(0) ∈ F^×, same
pattern. The composites are the identity both ways: backward∘forward sends
R to (c/(c/lead(R)))·lead(R)^{−1}R = R (using R(0) = c); forward∘backward
sends S to division of (c/S(0))·S by its leading coefficient c/S(0),
returning S.

Step 2 (fibered telescoping over the shared vertex torus). Write
n_j(ρ_j; λ, c) := #{ interior-coefficient tuples ∈ F^{d_j−1} : the R_j with
leading coefficient λ and constant term c has pattern ρ_j }. Conditional on
the vertex values (V_1, …, V_k), the faces' interior residues are
independent, so the joint COUNT of residue configurations realizing ρ⃗ is

    #Joint = Σ_{(V_1,…,V_k) ∈ (F^×)^k} ∏_{j=1}^{k} n_j(ρ_j; V_j, V_{j+1}).

V_1 occurs only in the j = 1 factor, and for FIXED V_2, summing the leading
coefficient over the torus is exactly (T1):

    Σ_{V_1 ∈ F^×} n_1(ρ_1; V_1, V_2)
      = #{ R : deg R = d_1, R(0) = V_2, pattern ρ_1 } = P_{ρ_1}(q₀),

independent of V_2. The factor P_{ρ_1}(q₀) pulls out of the sum, leaving
the same expression for faces 2, …, k; iterating left to right (after step
j − 1, the variable V_j occurs only in the j-th factor), the final step is
Σ_{V_k ∈ F^×} n_k(ρ_k; V_k, 1) = P_{ρ_k}(q₀) — (T1) at the anchor value
c = 1. Hence

    #Joint = ∏_{j=1}^{k} P_{ρ_j}(q₀).

Step 3 (probability). The residue configuration space has
(q₀−1)^k · q₀^{Σ_j (d_j−1)} equally likely points (L6c); dividing gives
(JC), since (q₀−1)·q₀^{d_j−1} = q₀^{d_j} − q₀^{d_j−1}.

Consistency and independence: Σ_{ρ z-free, degree d} P_ρ(q₀) = q₀^d −
q₀^{d−1} (all monics of degree d with nonzero constant term), so the (JC)
values sum to 1 over all shape vectors; and the same telescoping with all
faces except j summed over their shapes gives the marginal
Prob(pattern(R_j) = ρ_j) = P_{ρ_j}(q₀)·(q₀^{d_j} − q₀^{d_j−1})^{−1}, whence
(JC) = the product of the marginals. Fact F makes every factor one fixed
polynomial in q, so (JC) is a single element of ℚ(q) uniform over residue
characteristics. ∎

*Remark (why the torus sum is needed — the falsifier's hook).* The
POINTWISE conditional counts genuinely vary with the shared vertices: at
d = 2, ρ = {(1,2)} (a double root) and q₀ odd, n(ρ; λ, c) = 1 + χ(c/λ) ∈
{0, 2} (χ the quadratic character — R = λz² + bz + c has a double root iff
b² = 4λc), which is not a polynomial in q₀ per fixed (λ, c) and behaves
differently at q₀ even (there n ≡ 1: squaring is a bijection). Only the
torus-SUMMED counts are universal — exactly what (T1) supplies. §8(d)
verifies both halves numerically.

**L6′ (the (g4) closure).** The closed mass of every polygon stratum family
(face-kind κ + residual-shape vector ρ⃗, summed over its depth cone) is the
displayed m(κ, ρ⃗) of §2.3(iii): a finite sum — over L6b(ii)'s finite
enumeration — of terms A·∏_{j≤k−1} q^{c_j}/(q^{c_j}−1) with all c_j ∈ ℤ_{≥1}
and A of the forms (g1)–(g3), w-independent (cell part from L6a at the
nested minima; residual-shape factor = the (JC) product of L6d, constant
across the family; the conditional normalization q^{+e} is (g1)). These are
exactly the (g4) shapes. The only
OTHER unbounded index in any 𝔅_n stratum family is the (O3) in-place run
length L, with Σ_{L≥1} κ₀^{L−1}κ₁ = (q−1)/(q^E−1) and exit scaling
Σ_{L≥0} κ₀^L = q^E/(q^E−1) — ratio q^{−E}, E ≥ 3: also (g4)-shaped. ∎

**Lemma L7** (the subring ℛ). Let 𝒮 ⊂ ℚ[q] be the multiplicative set generated
by q and {q^c − 1 : c ≥ 1}, and ℛ := ℚ[q][𝒮^{-1}] ⊂ ℚ(q). Then: (i) every
f ∈ ℛ has reduced denominator D_f dividing an element of 𝒮, hence (L5) f has
no pole at any rational x with |x| ≥ 2; (ii) ℛ is closed under q ↦ q^δ, δ ≥ 1;
(iii) q, q^c − 1 and their products are units of ℛ; each of

    Φ^{(O1)} = (q^{E−1}−1)/q^{E−1},  Φ^{(O2)} = Φ^{(O2′)} = (q^E−1)/q^E,
    Φ^{(O3)} = (q^E−q)/(q^E−1)

is a unit of ℛ (numerators and denominators are, up to units, products of
q-powers and (q^c−1)-factors: q^E − q = q(q^{E−1} − 1)), and so are
1 − q^{1−E} = (q^{E−1}−1)/q^{E−1} and 1 − q^{−E} = (q^E−1)/q^E — the two
solve denominators of (g7).

*Proof.* (i) f = P/s, s ∈ 𝒮; N_f·s = P·D_f with gcd(N_f, D_f) = 1 in the PID
ℚ[q] gives D_f | s; L5 applies. (ii) generators map to generators
(q ↦ q^δ, q^c − 1 ↦ q^{cδ} − 1). (iii) immediate. ∎

## 4. Theorem 1 (kernel structure and determinants)

**Theorem 1.** At 𝔅_n, for e ∈ {2, …, n} (block 1 has K_1 = 0, Φ_1 = 1):
(1) the within-block RETURN of the semantic stratification is exactly the
(S-loop) strata, of one-step mass κ₀ + κ₁ = q^{1−E}; every other stratum of
the §2.2 partition is booked to a block m < e (through base changes q ↦ q^δ,
1 ≤ δ ≤ e) or terminates;
(2) the kernels and determinants of the four bookings are as displayed in
§2.4 / L7(iii), with reduced numerators

    N^{(O1)} = q^{E−1} − 1,   N^{(O2)} = N^{(O2′)} = q^E − 1,
    N^{(O3)} = q·(1 + q + ⋯ + q^{E−2})   [ = q(q^{E−1}−1)/(q−1) ]

(for (O3): gcd(q^E − q, q^E − 1) = q^{gcd(E−1, E)} − 1 = q − 1, using
gcd(q^a − 1, q^b − 1) = q^{gcd(a,b)} − 1 in ℚ[q] and gcd(q, q^E − 1) = 1);
(3) the three re-entrant bookings O1, O2′, O3 have the SAME solve: their
balance equations are all algebraically (1 − κ₀ − κ₁)x = s, and
1 − κ₀ − κ₁ = 1 − q^{1−E} ≠ 0 in ℚ(q). The terminal booking O2 has a
DIFFERENT solve, x = (1 − κ₀)^{−1}·t (no feedback; t its designated exit
rows) — the e = 2 value divergence is displayed in §2.4 — and BOTH solved
forms are divisions by units of ℛ.

*Proof.* (1) The one-step decomposition of the state law is the complete
partition displayed in §2.2: C_e = R_e ⊔ (C_e \ R_e); on R_e, Lemma L2
(uniform rescale, type preserved), then Lemma L3 (the e-fold rational-point
reductions re-enter the state law with mass q₀^{-e} per center — the
self-loop; conditional masses κ₀, κ₁ as computed in §2.2) and Lemma L4(i)
(every other pattern's booked targets have m < e); on C_e \ R_e, Lemma L6a
(the polygon cells partition it — their disjoint union over admissible P
exhausts, since every g ∈ C_e \ R_e has SOME polygon with min slope in (0,1)
by L1) and Lemma L4(ii) (booked targets μ < e). Since the state set is a
singleton, K_e is the 1×1 matrix of the booked loop mass, per booking. (If
one grades the solve by splitting type — a vector unknown — the loop
coefficient is the SAME scalar in every type coordinate, because the
self-loop re-enters the state law with types passed through unchanged
(L2/L3 preserve types): K_e = κ·Id, whose determinant (1 − κ)^{#types} has
the same ZERO SET as 1 − κ. The nonvanishing clause (i) of §1 is therefore
presentation-independent; the displayed MARGINS are claims about the
singleton-state presentation, which is the one 𝔅_n carries.)
(2) Arithmetic + the displayed gcd's.
(3) O1: x = (κ₀+κ₁)x + s. O2′: x = κ₀x + κ₁x + s — same equation. O3:
(1 − κ₁/(1−κ₀))x = s/(1−κ₀); multiplying by 1 − κ₀ (≠ 0 in ℚ(q)) gives
(1 − κ₀ − κ₁)x = s. In each case the unique solution is x = s/(1 − q^{1−E}).
O2: x = κ₀x + t with t free of x (its booking routes NO row back into block
e), so x = t/(1 − κ₀). Both 1 − q^{1−E} and 1 − κ₀ are units of ℛ (L7(iii)). ∎

**Corollary D (det channel).** For every booking, every e ∈ {1, …, n},
and every prime power q₀ ≥ 2: D_{Φ_e}(q₀) ≠ 0, N_{Φ_e}(q₀) ≠ 0, and

    Φ^{(O1)}(q₀) = 1 − q₀^{1−E} ≥ 1 − q₀^{-2} ≥ 3/4,
    Φ^{(O2)}(q₀) = Φ^{(O2′)}(q₀) = 1 − q₀^{-E} ≥ 1 − q₀^{-3} ≥ 7/8,
    Φ^{(O3)}(q₀) = 1 − (q₀−1)/(q₀^E−1) ≥ 1 − 1/(q₀²+q₀+1) ≥ 6/7,

using E = e(e+1)/2 ≥ 3 for e ≥ 2 and q₀ ≥ 2 (and Φ_1 = 1). *Proof.* The
numerators/denominators are cyclotomic-type (Theorem 1(2)); Lemma L5 gives
nonvanishing; the margins are monotone arithmetic ((q₀−1)/(q₀^E−1) ≤
(q₀−1)/(q₀³−1) = 1/(q₀²+q₀+1) ≤ 1/7). ∎

## 5. Theorem 2 (master denominator theorem — the (r2) channel)

**Theorem 2.** Every member of every E(e) of 𝔅_n (§2.3), in every booking
and for every composition datum, including every solved β_e and every β-leg
at every depth δ ≥ 1, lies in ℛ. Hence (L7(i)) no entry has a pole at any
rational x with |x| ≥ 2; in particular every entry is defined at every
prime power q₀ ≥ 2.

*Proof.* First, ℛ absorbs every grammar step: (g1) ℚ[q] ⊂ ℛ. (g2)
q^{-b} ∈ ℛ; (q^d − q^{d−1})^{-1} = q^{1−d}(q−1)^{-1} ∈ ℛ;
(q−1)/(q^{n+1}−1) ∈ ℛ. (g3) (1 − q^{-1})^V q^{-N} ∈ ℛ. (g4) A·q^c/(q^c−1)
∈ ℛ for c ∈ ℤ_{≥1}, A ∈ ℛ. (g5) L7(ii). (g6) ℛ is a ring. Now bottom-up
induction on e, walking the displayed row families of §2.3 with their
bracketed generations. Base: E(1) = {1} ⊂ ℛ. Block e, given β_{e′}(σ′) ∈ ℛ
for all e′ < e:
(i) kernels — q^{−E}, q^{1−E} ∈ ℛ; (q−1)/(q^E−1) ∈ ℛ by its displayed (g4)
form.
(ii) m(π) = q^{−(E−e)}·N_π(q)·q^{−e} — N_π ∈ ℚ[q] is one fixed polynomial
(Fact F(ii)); the q-powers are (g2): in ℛ.
(iii) m(κ, ρ⃗) — the bracketed cell sum is a FINITE sum (L6b(ii)) of (g3)
volumes times (g4) closures with exponents c_j ≥ 1 (L6b, via L6′); the
shape factor is (JC) = ∏_j P_{ρ_j}(q)·(q^{d_j} − q^{d_j−1})^{−1} (L6d),
each factor (g1) or (g2): in ℛ by (g6).
(iv) row_σ(F) and t_σ — finite sums of products, with coefficients 0 or 1,
of m(F) ∈ ℛ (items (ii)/(iii)) with β_{μ_i}(σ_i)(q^{D_i}) ∈ ℛ (induction
hypothesis + (g5), μ_i < e by L4): in ℛ because ℛ is a ring — for EVERY
composition datum, since any 0/1-coefficient combination of ℛ elements
lies in ℛ regardless of which summands the datum selects.
(v) the weights — (g2) atoms, and q^{E_m}/(q^{E_m}−1) ∈ ℛ ((g4) with A = 1;
also a unit, L7(iii)).
(vi) β-legs — induction hypothesis + (g5) + finite σ′-sums (g6).
(vii) β_e(σ) = u^{−1}·t_σ with u = 1 − q^{1−E} (bookings O1, O2′, O3, via
Theorem 1(3)'s explicit solution of the balance equation — NOT a division
of a row containing β_e) or u = 1 − q^{−E} (booking O2, whose rows contain
no β_e by definition). Both u are units of ℛ (L7(iii)) and t_σ ∈ ℛ by (iv),
so β_e(σ) ∈ ℛ. The kernel is 1×1, so no adjugate denominators arise beyond
u. This exhausts the E(e) list of §2.3. ∎

## 6. Theorem 3 (the claim) and Theorem 4 (robust backup)

**Theorem 3.** For every n ≥ 2, every booking of 𝔅_n, every prime p,
every integer δ ≥ 1, every block e: both (r1) and (r2) hold at q₀ = p^δ. Hence
(REG-p) holds at every prime; the failing set is EMPTY. Moreover the same
clauses hold at every composite depth (p^{δ·m} is again a prime power ≥ 2), so
no descent-depth evaluation can fail either.

*Proof.* q₀ = p^δ is an integer ≥ 2. (r1): Corollary D. (r2): Theorem 2. ∎

**Theorem 4** (substochastic principle; organization-robust backup — used only
if a table variant with finer state sets replaces the scalar kernel). Let
M ∈ M_k(ℝ) have nonnegative entries and every row sum ≤ 1 − ε, ε > 0. Then
det(I − M) > 0. *Proof.* For t ∈ [0,1], I − tM is strictly diagonally
dominant with positive diagonal ((1 − tM_{ii}) − Σ_{j≠i} tM_{ij} ≥
1 − t(1−ε) ≥ ε), so by Levy–Desplanques det(I − tM) ≠ 0; t ↦ det(I − tM) is
continuous and equals 1 at t = 0, hence is positive at t = 1. ∎
At 𝔅_n the hypothesis holds at every prime power with ε = 3/4, 7/8, 6/7 per
booking (Corollary D margins; the row "sum" is the scalar kernel value).

## 7. The concrete n = 2, 3 tables (data to check the instance claims against)

* Degree-2 formal instance (the project's machine-checked n = 2 table):
  Δ = {1}; block 1: K = (0), Φ₁ = 1; block 2: one state, kernel (q^{-3}),
  Φ₂ = (q³−1)/q³; terminal masses 1 − 1/q and 1/q − q^{-3}; solved vector,
  in the SAME row order, (q²/(q²+q+1), (q+1)/(q²+q+1)); every entry
  denominator a power of q or q²+q+1 (a divisor of q³−1). This is (O2) at
  e = 2, E = 3: kernel q^{-E} = q^{-3}; the terminal masses are grammar
  elements (1 − q^{-1}, q^{-1} − q^{-3}) summing with the kernel to 1 — the
  κ₁ mass sits inside 1/q − q^{-3} = (q^{-1} − q^{-2}) + κ₁ — and the solve
  is EXACTLY the componentwise no-feedback division:
  (1 − 1/q)/(1 − q^{-3}) = q²/(q²+q+1) and
  (1/q − q^{-3})/(1 − q^{-3}) = (q+1)/(q²+q+1). No row re-enters block 2.
* Degree-3 sealed tables (the project's dual-accepted n = 3 solve): block-2
  kernel (q−1)/(q³−1), det (q³−q)/(q³−1); block-3 kernel (q−1)/(q⁶−1), det
  (q⁶−q)/(q⁶−1); junction masses e.g. ((q−1)(q−2)+(q−1))/(q⁶−1) +
  (q−1)²/((q³−1)(q⁶−1)); stratum masses with denominators q³−1, q⁶−1 and
  their products; final densities with denominators dividing (q²−1)(q⁵−1)
  products, e.g. R = (q⁴+q²+q)/(q⁵+2q⁴+2q³+2q²+2q+1) with denominator
  (q+1)(q⁴+q³+q²+q+1) | (q²−1)(q⁵−1). This is (O3) at e = 2, 3
  (E₂ = 3, E₃ = 6). All are elements of ℛ; all satisfy L5's criterion.

Checks you can do by hand: (q−1)/(q³−1) = κ₁/(1−κ₀) at E = 3
((q−1)q^{-3}/(1−q^{-3})); (q−1)/(q⁶−1) likewise at E = 6; the rational roots
of q³−1, q³−q, q⁶−q, q^{E−1}−1 are all in {0, ±1}; the dets at q₀ = 2 are
6/7 = 1 − 1/7 and 62/63, at q₀ = 3: 12/13, 363/364 — all nonzero.

## 8. Corroborating computation (NOT part of the proof; exact arithmetic)

An exact symbolic scan (sympy) verified, with zero exceptions: the diagonal-
scalar kernel structure — the raw generating-machinery self-coefficient is
exactly q^{1−e} at the (1,e)-cell for e = 2..6, and multiplied by the descent
rescale prefactor q^{−e(e−1)/2} (note e(e−1)/2 = E − e) this is the loop mass
q^{1−E} of Theorem 1(1) exactly; rational roots of all displayed det
numerators ⊆ {0, ±1} plus positivity at all 18120 prime powers ≤ 2·10⁵; for
e ≤ 5, every assembled solve component's reduced denominator has rational
roots ⊆ {0, ±1}, the symbolic mass law Σ_t β_e[t] = 1 holds exactly, and at
18 prime powers all values are defined, lie in [0,1], and sum to 1 exactly;
for n ≤ 5 the fully assembled densities have ℛ-shaped denominators and sum
to 1 symbolically. An independent prior scan (95 primes, the concrete
n = 2, 3 tables of §7, both faithful and superset pools) found zero (REG-p)
clause failures, minimum determinant margin 6/7 — equal to Corollary D's (O3)
bound at q₀ = 2.

New in rev 2 (exact, exhaustive; zero findings): (a) L6a's cell law was
enumerated over (ℤ/p^M)^e for (e,p,M) ∈ {(2,2,7), (2,3,5), (3,2,6), (3,3,4),
(4,2,5)}: every Newton-hull fiber with in-range heights matches
(1−1/p)^V p^{−N} · p^{eM} EXACTLY, and the aggregates match vol(C_e) = q^{−e},
vol(R_e) = q^{−E}, vol(C_e\R_e) = q^{−e} − q^{−E} (the L1 dichotomy); e = 2
has exactly one polygon stratum (the k = 1 finiteness). (b) L6b's move law
was checked over all 139 face-kind sequences with e ≤ 7 (2536 cone moves):
ΔN = c_j exactly, always ≥ 1, vertex count constant. (c) The (g7) algebra:
for E ∈ {3, 6, 10, 15} the O1/O2′/O3 balance equations all solve to
s/(1 − q^{1−E}) with denominator roots ⊆ {±1}; the §7 degree-2 table solves
by the no-feedback division exactly; the e = 2 value divergence of §2.4 is
real and both solved pairs are ℛ-shaped.

New in rev 3 (exact, exhaustive; zero findings; script
`verification/openmath/O12_rev3_checks.py`): (a) Fact F's pattern counts
P_ρ, N_π match brute-force factorization censuses over F_p for p ∈
{2, 3, 5, 7, 11, 13}, degrees ≤ 4, totals included. (b) The torus identity
(T1) holds at EVERY fixed constant term c ∈ F^× (p ≤ 7, d ≤ 3; honest
enumeration over all leading coefficients, no scaling shortcut). (c) L6d's
joint law (JC): over anchored shared-vertex chains with face-degree
sequences (2,2), (2,1), (1,2), (2,3), (3,2), (2,2,2) and p up to 13, EVERY
joint shape count equals ∏_j P_{ρ_j}(p) exactly (support and totals
included), and the empirical face-shape events are exactly independent.
(d) The REFUTES-hook of the L6d remark: the pointwise conditional
double-root counts take exactly the values {0, 2} as the shared vertex pair
varies (p ∈ {3, 5, 7}) and are constantly 1 at p = 2 — the coupling is
real, and only the torus-summed counts are universal. A single mismatch in
(a)–(c) would have refuted L6d or Fact F.

## 9. Verification checklist (where to press hardest)

1. L1's ultrametric equality case (the unique-minimum argument at e_k).
2. L2/L3: the measure-preservation claims (coordinate-wise division by π^i;
   recentering as unit-Jacobian triangular map).
3. L4(ii): the size bound μ < e — check the two face cases (rightmost
   fractional: d ≤ e/2; others: d ≤ e − 2) and that b ≥ 2 on the rightmost
   face is forced by minimal slope ∈ (0,1).
4. L6a: the hull-equals-cell equivalence ((α)+(β) both directions) and that
   the product volume uses ⌈h_i⌉ over ALL e coefficient columns, equality
   exactly at the k vertex columns.
5. L6b: the elementary-move shift (integer gains; anchoring at the right
   endpoint; ⌈h + z⌉ = ⌈h⌉ + z only for z ∈ ℤ) and the nested-minimum
   period shift a_j^min(s+1) = a_j^min(s) + b_j that composes the moves;
   c_j ≥ 1 in all cases; the k = 1 family is finite.
6. Theorem 1(2): the gcd computations for the (O3) reduced fraction.
7. Theorem 1(3) + Theorem 2 (g7): that NO booking divides a row containing
   the current block's unknown — O1/O2′/O3 are solved as balance equations
   with solution s/(1 − q^{1−E}), O2's rows are x-free by its definition —
   and that both solve denominators are units of ℛ.
8. §2.3: that E(e) is genuinely finite (patterns, face-kinds, residual
   shapes, verdicts, Δ′, composition data all finite), that each of the
   seven row families (i)–(vii) is a displayed rational function (not a
   schema), and that each bracketed 𝒢-generation is correct; in (iv), that
   the only scalars entering row_σ(F) and t_σ are 0/1 coefficients.
9. Fact F and L6d: the Möbius count (i) and the multiset count (ii)/(iii);
   the (T1) bijection (both composites the identity; patterns invariant
   under unit scalars); the telescoping — that V_1 occurs only in the
   first factor, that after each step the next vertex variable occurs only
   in the next factor, and that the anchored last step is (T1) at c = 1;
   the division by the configuration-space size; and that consecutive
   faces share EXACTLY the one vertex column (so the n_j factorization of
   the joint count is legitimate).
10. The scope declaration (§1): the claim is about the §2 tables; value
    correctness (including the §2.4 divergence of O2 from the re-entrant
    solve) is excluded; the n = 2, 3 concrete-table claims are checked
    against the data quoted in §7.
11. Quantifiers: the claim is ∀ prime p, ∀ δ ≥ 1, ∀ e, ∀ booking, ∀
    composition datum — verify no step restricts to "all-active" pools,
    large p, or tame p (none should: L5's root argument, L7's pole
    argument, and Fact F/L6d's counts are uniform in the prime power).

