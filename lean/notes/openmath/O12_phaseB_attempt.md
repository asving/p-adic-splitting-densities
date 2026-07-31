# O12 — (REG-p) emptiness at the intended instance — Phase-B attempt (Fable, 2026-07-31)

Leaf (docs/MATH_COMPLETION_TREE_2026-08-01.md, O-12): the formalized M17 layer
(`MovesU/RegPFinite.lean`, `regP_failing_eq`) proves, for every pinned instance,

    {p prime : (REG-p) fails}  =  {p : ∃ δ ∈ Δ, p^δ ∈ B},          — (K-13) —

B = the real zero/pole locus (rational zeros AND poles of every Φ_e = det(1−K_e),
plus poles of every entry-list member). The leaf: at the INTENDED instance, B
contains no prime power ≥ 2, so the failing set is EMPTY and theoremU's one
per-prime hypothesis holds at EVERY prime, wild pools and descent depths included.

RESULT IN ONE LINE: proved at the intended instance for every n — every
det-numerator and every entry denominator produced by the intended solve is a
divisor of q^b·∏(q^c − 1) ("cyclotomic type"), whose rational roots lie in
{0, 1, −1}; a prime power p^m is ≥ 2; done. The mechanism is a master
denominator theorem: the entire solve lives in the subring
ℛ = ℚ[q, q^{-1}, {(q^c−1)^{-1}}_{c≥1}] of ℚ(q), in which every block
determinant is a UNIT. The three kernel organizations on record (the Lean n=2
instance, the sealed RESUM-n3 tables, the general-n engine) are derived from one
stratification and all satisfy the criterion; the substochastic-escape principle
(the tree's expected mechanism) is proved as the organization-robust backup.

Labels: (a) known, (b) new proof of known, (c) claimed new. "Corpus theorem" =
sorry-free Lean theorem in this repo. Numerics: §10 (executed this session).

## 0. What is on record, and what emptiness requires

Fix n ≥ 2. The (REG-p) predicate (Lean `MovesU/Defs.lean:209`; unfolded in
`M17-regp-density_brief.md`) demands, at every pool value q₀ = p^δ (δ ∈ Δ, the
finite consumed-depth set) and every block e ∈ [1, n]:

    (r1) Φ_e := det(1 − K_e) ∈ ℚ(q) is defined at q₀ and Φ_e(q₀) ≠ 0;
    (r2) every member g of the entry list E(e) (K entries, terminal rows, split
         rows, J cells, entrances ι, shape weights W, and the β-legs
         q ↦ Σ_σ′ blockSolve_{e′,τ′}(σ′)(q^δ) at every δ ∈ Δ) is defined at q₀
         and evaluates to the designated active value act(g, q₀).

On record (all cited, not re-proved here):

* **K-13 (M17 Theorems A/B/C + Corollary U; Lean `RegPFinite.lean`, 14 thms
  Lean-core).** The failing set equals {p : ∃ δ ∈ Δ, p^δ ∈ B} EXACTLY
  (`regP_failing_eq`), is finite (`regP_failing_finite`, `regP_cofinite`),
  where B = realZeroPoleSet = ⋃_e (Z(Φ_e) ∪ P(Φ_e) ∪ ⋃_{g ∈ E(e)} P(g)),
  Z/P = rational zeros of the reduced numerator / roots of the reduced
  denominator. The act-agreement half of (r2) is free given definedness
  (M17 Lemma 0: `act_pin` + evaluation on the defined locus).
* **Schema-level emptiness is REFUTED** (compiled countermodel
  `BridgeB15a_r2Neg.lean`: an admissible n=2 pack failing exactly at p = 2).
  So O-12 is genuinely a property of the intended instance.
* **n = 2 is closed** (M17 §8): the real Lean instance has Δ = {1}, Φ₁ = 1,
  Φ₂ = (q³−1)/q³ (`n2_det`), all entry denominators powers of q; B contains no
  prime power; failing set EMPTY at every prime (also `n2_pools_all`; N6 scan
  25/25 gates, 95 primes, zero failures).

So the leaf reduces to: **at the intended instance, for every e and every
prime power q₀ ≥ 2, (i) N_{Φ_e}(q₀) ≠ 0 and D_{Φ_e}(q₀) ≠ 0, and (ii) no entry
denominator vanishes at q₀.** Two channels: dets and denominators. One key
closure observation used throughout: *a positive integer power of a prime power
is again a prime power*, so descent depths (the composite set M̂ of M17 §6)
introduce no new kind of evaluation point — proving (i)+(ii) at ALL prime
powers ≥ 2 at once collapses M17 Theorem C's sandwich (its left and right sets
both become empty).

## 1. The intended instance 𝔅_n, defined

The intended instance is the β cluster-law block system — the mathematical
content of `verification/om_density_engine.py` (the general-n symbolic engine,
gate-validated: reproduces the anchored monic laws at e ≤ 3 exactly; Σ_σ ρ = 1
symbolically for n ≤ 5; exact agreement with the PARI factorpadic oracle at
n = 4, 5, primes 2, 3, 5, 7) and of the sealed RESUM-n3 tables at n = 3. We
define it mathematically; all theorems below are about this definition.

**Semantics.** For a prime power q₀ = p^m let K₀ be the unramified extension of
ℚ_p with residue field F_{q₀}, O its integers, π = p, v the valuation with
v(p) = 1 extended to a fixed algebraic closure. Monic degree-e polynomials over
O are identified with O^e (coefficient tuples) carrying Haar probability
measure. The *splitting type* of monic g is the multiset {(e_i, f_i)} of
ramification/residue data of the irreducible factors of g over K₀.

**States.** Block e ∈ [1, n] has ONE continuation state: the *aligned size-e
cluster*, whose law is Haar conditioned on

    C_e := {g monic, deg e : all e roots of g lie in the open unit disc
            {v > 0}}  =  {v(a_i) ≥ 1 for i = 1..e}     (Lemma S1),

of volume q₀^{-e} (after the recentering normalization: an arbitrary cluster
"all roots in c + m" is carried to C_e by the measure-preserving recentering
x ↦ c + x). Block 1 has no continuation (a single root is decided: K_1 = 0,
Φ_1 = 1).

**One classifier step from C_e** (the stratification proved in §3):

* *Descent* (R_e := {v(a_i) ≥ i ∀i} = {all roots in {v ≥ 1}}): conditional
  volume q₀^{-(E−e)}, E := E_e := e(e+1)/2. Conditioned on R_e, the rescale
  h(y) := g(πy)/π^e is Haar-uniform monic of degree e with the same splitting
  type (Lemma S2). Reading h's residue divisor:
  - *re-cluster at a rational center c ∈ F_{q₀}* (h̄ = (y−c)^e): volume q₀^{-e}
    per c; conditioned on it, the recentered h(c+·) has EXACTLY the state law
    β_e again (Lemma S3) — the self-loop;
  - any other divisor: parts (δ, m) with δ·m ≤ e and (δ, m) ≠ (1, e): hand-offs
    to blocks m < e at base change q ↦ q^δ (Lemma S4(i)), or leaves (m = 1).
* *No descent* (C_e \ R_e; Newton polygon min slope in (0,1)): the polygon/
  residual-factor decomposition hands off to blocks μ < e at base changes
  q ↦ q^D and to terminal verdicts (Lemma S4(ii)); the per-stratum masses are
  Igusa cell volumes (1 − q₀^{-1})^V q₀^{-N} with depth parameters summed
  geometrically (§5).

**The q-symbolic table.** Every displayed mass above is one fixed expression in
q (the same formula for every q₀), built by the grammar: ℚ[q]-coefficient
combinations; the normalizations q^{-e}, (q^d − q^{d−1})^{-1}, and (for the
root/projective assembly) |Pⁿ(F_q)|^{-1} = (q−1)/(q^{n+1}−1); Igusa volumes
(1−q^{-1})^V q^{-N}; geometric closures Σ_{w≥0} q^{-cw} (c ∈ ℤ_{≥1}, Lemma S5);
base changes q ↦ q^δ (δ ∈ ℤ_{≥1}); and the block solve
β_e = (1 − K_e)^{-1}(exit rows), triangularly in e. The value of each such
element of ℚ(q) at every prime power q₀ ≥ 2 is the corresponding convergent
volume sum (all geometric ratios are q₀^{-c} < 1).

**Kernel organizations on record.** With κ₀ := q^{-E} (one-step in-place
descent: descend and re-cluster at c = 0) and κ₁ := (q−1)·q^{-E} (descend and
re-cluster at a nonzero c), the corpus's three organizations of block e are:

    (O1) engine one-step:    K_e = (κ₀ + κ₁) = (q^{1−E})
    (O2) Lean n=2 gate/real: K_e = (κ₀)      = (q^{-E})        [n=2: q^{-3}]
    (O3) RESUM (sealed n=3): K_e = (κ₁/(1−κ₀)) = ((q−1)/(q^E − 1))

(O3) absorbs the in-place branch geometrically into the exit rows (each exit
mass divided by 1 − κ₀); Theorem 1 proves all three are regroupings of one
stratification with the SAME solve. The sealed instances match exactly:
n=2 real Φ₂ = (q³−1)/q³ = (O2) at E = 3; RESUM-n3 κ̂₂ = (q−1)/(q³−1),
κ̂₃ = (q−1)/(q⁶−1), dets (q³−q)/(q³−1), (q⁶−q)/(q⁶−1) = (O3) at E₂ = 3, E₃ = 6.

**Scope declaration (honesty).** 𝔅_n as defined IS the campaign's intended
general-n instance (the object the engine computes and the sealed tables
instantiate). The separate obligation that the EVENTUAL Lean general-n
`UCarriers` pack is pinned to 𝔅_n is the population/dictionary work of leaves
O-2 / T-7 / O-14d, NOT part of O-12; §8's robustness theorem covers departures
in organization (finer state sets) given only the mass law.

## 2. Two standard measure lemmas

**Lemma S1** *(a — standard; elementary proof for self-containment)*. Let
g = x^e + a_1x^{e−1} + ⋯ + a_e over O with roots r_1, …, r_e (multiplicity).
For t ∈ {0} ∪ ℤ_{≥1}... stated for the two uses: (i) all v(r_j) > 0 ⟺
v(a_i) ≥ 1 ∀i; (ii) all v(r_j) ≥ 1 ⟺ v(a_i) ≥ i ∀i.

*Proof.* (⇒, both) a_i = ±e_i(r), each monomial a product of i roots:
ultrametrically v(a_i) ≥ i·min_j v(r_j); for (i) this gives v(a_i) > 0, and
v(a_i) ∈ ℤ forces ≥ 1; for (ii) it gives ≥ i. (⇐, both) Let μ := min_j v(r_j)
and k := #{j : v(r_j) = μ}. Among the products in e_k(r), the product of the k
minimal-valuation roots has valuation exactly kμ and EVERY other product is
strictly larger (it contains a root of valuation > μ in exchange); by the
ultrametric equality case, v(a_k) = kμ. If (i)'s RHS holds: kμ = v(a_k) ≥ 1 > 0
so μ > 0. If (ii)'s RHS holds: kμ = v(a_k) ≥ k so μ ≥ 1. ∎

**Lemma S2 (self-similarity)** *(a — standard)*. Conditioned on R_e (i.e.
a_i ∈ π^iO ∀i), the coefficients b_i := a_i/π^i of h(y) := g(πy)/π^e are Haar-
uniform on O^e; g and h generate isomorphic étale algebras (x = πy), hence have
equal splitting types. *Proof.* Haar on π^iO pushes to Haar on O under division
by π^i, independently per coordinate; the algebra map is x ↦ πy. ∎

**Lemma S3 (re-cluster step)** *(a — standard)*. For Haar-uniform monic h of
degree e: the reduction h̄ is uniform among the q₀^e monics over F_{q₀}; the
events {h̄ = (y−c)^e}, c ∈ F_{q₀}, are disjoint of volume q₀^{-e} each; and
conditioned on one of them, h(c̃+y) (c̃ any lift of c) is Haar conditioned on
C_e — the state law again, with the same splitting type. *Proof.* Reduction of
Haar is uniform; recentering h ↦ h(c̃+·) is a measure-preserving bijection of
monics carrying {h̄ = (y−c)^e} onto {reduction = y^e} = C_e (Lemma S1(i) form);
types are translation-invariant. ∎

**Lemma S4 (all other strata leave the block)** *(c — the structural lemma of
this note; elementary given S1–S3)*.
(i) In the descent stratum, condition on a residue divisor of h other than
e·[rational point]: every part (δ, m) (a degree-δ closed point carrying
multiplicity m, Σ δ·m = e) has m < e. (ii) In C_e \ R_e, every residual
hand-off is to a cluster of size μ < e (over F_{q₀^D}, some D ≥ 1).

*Proof.* (i) A part with m = e forces δ·e ≤ e, δ = 1 — the excluded rational
e-fold point. (ii) The Newton polygon of g ∈ C_e \ R_e has min slope s ∈ (0,1),
so its rightmost face has slope a/b, gcd(a,b) = 1, b ≥ 2, and integer length
L_right = b·d_right (d_right = its residual degree); hence d_right ≤ L_right/2
≤ e/2 < e. Any other face has length L ≤ e − L_right ≤ e − 2, and its residual
degree d ≤ L. A residual hand-off is an irreducible factor (degree D,
multiplicity μ ≥ 2) of the face's residual polynomial of degree d, resolved by
a size-μ cluster over F_{q₀^D}; μ·D ≤ d gives μ ≤ d ≤ max(e/2, e−2) < e. ∎

(The fact that a multiplicity-μ residual factor of a face is resolved by a
size-μ cluster over the residual extension is the Montes/Okutsu residual
descent — (a), standard theory of types; the corpus's L3/M6 notes carry the
project's version. For the determinant claim only the SIZE bound μ < e is
consumed, which is (ii)'s arithmetic.)

## 3. Theorem 1: the kernel trichotomy and the block determinants

**Theorem 1** *(c)*. At 𝔅_n, for every block e ∈ [2, n], with E = e(e+1)/2:

(1) The within-block continuation of block e consists EXACTLY of the self-loop
strata "descend, re-cluster at a rational center": one step re-enters the state
law with mass κ₀ + κ₁ where κ₀ = q^{-E} (center 0) and κ₁ = (q−1)q^{-E}
(nonzero center); every other stratum hands off to a block m < e (at a base
change q ↦ q^δ, 1 ≤ δ ≤ e) or terminates. In particular K_e is 1×1 (per state;
κ_e·Id on the type-graded presentation — same zero sets).

(2) The three organizations' kernels are as displayed in §1, with

    Φ_e^{(O1)} = 1 − q^{1−E} = (q^{E−1} − 1)/q^{E−1}
    Φ_e^{(O2)} = 1 − q^{-E}  = (q^E − 1)/q^E
    Φ_e^{(O3)} = 1 − (q−1)/(q^E−1) = (q^E − q)/(q^E − 1)

all fractions displayed in lowest terms except Φ^{(O3)}, whose reduced form is
q·(q^{E−1}−1) / ((q−1)·(1 + q + ⋯ + q^{E−2}))⁻¹-free form — precisely:
gcd(q^E − q, q^E − 1) = q^{gcd(E−1,E)} − 1 = q − 1, so
N_{Φ^{(O3)}} = q(q^{E−1}−1)/(q−1) = q·(1 + q + ⋯ + q^{E−2}),
D_{Φ^{(O3)}} = (q^E−1)/(q−1) = 1 + q + ⋯ + q^{E−1}.

(3) The three solves coincide: β_e = (1 − κ₀ − κ₁)^{-1}·s_e in each.

*Proof.* (1) The one-step strata of the state law are: R_e-descent followed by
the divisor read of the uniform rescale (Lemmas S2, S3), or the C_e \ R_e
polygon strata. P(R_e | C_e) = q^{-E}/q^{-e} = q^{-(E−e)} (S1(ii) gives
vol(R_e) = ∏ q^{-i} = q^{-E}; S1(i) gives vol(C_e) = q^{-e}). Given descent,
the divisor "e-fold rational point c" has mass q^{-e} per c (S3), re-entering
the state law exactly; total self-loop mass q^{-(E−e)}·q^{-e} = q^{-E} per
center, i.e. κ₀ for c = 0 and κ₁ summing the q−1 nonzero centers. Every other
descent divisor and every no-descent stratum leaves the block by Lemma S4.
Base-change depths: a part (δ, m) reads block m through q ↦ q^δ with δ ≤ e; a
residual hand-off reads block μ through q ↦ q^D with D ≤ d ≤ e.

(2) (O1) sums the q centers into the kernel: κ₀ + κ₁ = q·q^{-E} = q^{1−E}.
(O2) takes only the in-place branch as kernel (the nonzero recenterings ride
the exit rows): κ₀ = q^{-E}; at e = 2, E = 3 this is the Lean instance's
kcol = q^{-3} and Φ₂ = (q³−1)/q³ = `n2_det`. (O3) resums the in-place branch
and keeps the nonzero recentering as the loop: Σ_{L≥1} κ₀^{L−1}κ₁ =
κ₁/(1 − κ₀) = (q−1)q^{-E}/(1 − q^{-E}) = (q−1)/(q^E − 1); the sealed n = 3
kernels are exactly this at E₂ = 3, E₃ = 6. The determinant displays are
arithmetic; the gcd computation: gcd(q^a − 1, q^b − 1) = q^{gcd(a,b)} − 1 in
ℚ[q] and gcd(q, q^E − 1) = 1.

(3) Writing s_e for the total exit row (O1/O2 conventions differing only in
which strata are called exits), the three fixpoints are x = (κ₀+κ₁)x + s,
x = κ₀x + (s + κ₁x-collected-as-exit)… stated cleanly: (O2) lists the κ₁
strata among exits that re-enter the block's own entrance, which the global
triangular solve re-feeds — algebraically x = κ₀x + κ₁x + s in all cases; and
(O3): x = (κ₁/(1−κ₀))x + s/(1−κ₀) ⟺ (1−κ₀−κ₁)x = s. Same unique solution
(1 − κ₀ − κ₁ ≠ 0 in ℚ(q) since κ₀ + κ₁ = q^{1−E} ≠ 1). ∎

**Remark (n = 2 sanity).** At e = 2: Φ^{(O2)} = (q³−1)/q³ (the corpus's
`n2_det`, machine-checked); Φ^{(O3)} = (q³−q)/(q³−1) (the sealed RESUM block-2
det, re-verified in `resum_n3_seal.py`); Φ^{(O1)} = (q²−1)/q² (the engine's
e = 2 fixpoint; §10 test A). Three different determinants — one solve, and all
three numerators are cyclotomic-type.

## 4. Lemma RR: cyclotomic-type numerators have no roots at prime powers

**Lemma RR** *(a — rational root theorem)*. For any c ≥ 1, the rational roots
of q^c − 1 lie in {1, −1}; the rational roots of q·(q^c − 1) and of
1 + q + ⋯ + q^{c} lie in {0, 1, −1}. Consequently a polynomial of the form
u·q^b·∏_i (q^{c_i} − 1) (u ∈ ℚ^×, b ≥ 0, c_i ≥ 1), or any divisor of one, has
no rational root x with |x| ≥ 2. Moreover for real x ≥ 2: x^c − 1 ≥ 2^c − 1 > 0
and x^b > 0 — positivity, not just nonvanishing.

*Proof.* q^c − 1 is monic with integer coefficients and constant term −1: any
rational root is an integer dividing 1 (rational root theorem). 1 + ⋯ + q^c
divides q^{c+1} − 1. Divisors of a polynomial with rational root set
⊆ {0, ±1} have rational root sets ⊆ {0, ±1}. A prime power p^m has p^m ≥ 2. ∎

**Corollary D (the det channel, all n)** *(c)*. At 𝔅_n, in each organization,
for every e ∈ [1, n] and every prime power q₀ ≥ 2:
D_{Φ_e}(q₀) ≠ 0 and N_{Φ_e}(q₀) ≠ 0 — indeed Φ_e(q₀) ∈ (0, 1] with the
explicit margins Φ_e(q₀) ≥ 1 − q₀^{-2} ≥ 3/4 for (O1), ≥ 1 − q₀^{-3} ≥ 7/8 for
(O2), ≥ 1 − (q₀−1)/(q₀³−1) ≥ 6/7 for (O3) (e ≥ 2; E ≥ 3; Φ_1 = 1). Clause
(r1) of (REG-p) therefore holds at every prime power argument — direct pool
values AND all composite/descent depths (p^{δm} is again a prime power ≥ 2).

*Proof.* Theorem 1(2) + Lemma RR; the numerators and denominators displayed are
all of cyclotomic type. Margins: κ₀+κ₁ = q₀^{1−E} ≤ q₀^{-2} ≤ 1/4;
κ₀ = q₀^{-E} ≤ 1/8; κ₁/(1−κ₀) = (q₀−1)/(q₀^E−1) ≤ (q₀−1)/(q₀³−1) =
1/(q₀²+q₀+1) ≤ 1/7. ∎

(The N6 scan's recorded minimal escape margin 6/7 at q₀ = 2 is exactly the
(O3) bound met with equality — an external pin on the margin computation.)

## 5. Theorem 4: the master denominator theorem (the (r2) channel, all n)

Let ℛ := ℚ[q, q^{-1}, {(q^c − 1)^{-1}}_{c ≥ 1}] ⊂ ℚ(q) — the localization of
ℚ[q] at the multiplicative set 𝒮 generated by q and {q^c − 1 : c ≥ 1}.

**Lemma R0** *(a — routine)*. (i) ℛ is a subring; every f ∈ ℛ has reduced
denominator dividing an element of 𝒮 (a PID gcd argument: N_f·s = P·D_f with
gcd(N_f, D_f) = 1 gives D_f | s), hence (Lemma RR) has NO pole at any rational
x with |x| ≥ 2. (ii) ℛ is closed under q ↦ q^δ for every δ ∈ ℤ_{≥1}
(generators map to generators: q^c − 1 ↦ q^{cδ} − 1). (iii) The elements q^b
and q^c − 1 are units of ℛ; consequently all three block determinants of
Theorem 1(2) are UNITS of ℛ (each is a ratio of products of q-powers and
(q^c − 1)-factors: q^{E−1}−1 over q^{E−1}; q^E−1 over q^E; q(q^{E−1}−1) over
q^E−1).

**Lemma S5 (integer-affine depth exponents)** *(c — the geometric-closure
bookkeeping, proved here)*. Fix a face-kind sequence (L_j, b_j, d_j)_{j=1..k}
(faces left→right, L_j = b_j·d_j column lengths, Σ L_j = e, slopes a_j/b_j
strictly decreasing, depth parameters a_j ranging over a residue class + b_jℕ
in the strict-order cone). Write the stratum's Igusa exponent
N = Σ_{i=0}^{e−1} ⌈h_i⌉ where h_i is the polygon height over column i (h_i is
an integer at the polygon's vertex columns). Then along each cone generator
(the gap variables w_j ∈ ℕ of the standard decoupling a_j = r_j + b_j·u_j,
u_j = Σ_{j′ ≥ j} (shift_{j′} + w_{j′})), N is affine with a POSITIVE INTEGER
coefficient c_j ≥ 1, and the vertex count V is w-independent.

*Proof.* It suffices that the elementary move a_j → a_j + b_j (slope of face j
increases by 1, all else fixed) shifts N by a positive integer. Under that
move: for columns i on face j (x_j ≤ i < x_{j+1}), the height gains
(x_{j+1} − i) ∈ ℤ_{≥1} (the face's right endpoint is a fixed polygon vertex;
the slope over the face grows by 1); for columns strictly left of face j, the
height gains the full extra drop b_j·d_j = L_j ∈ ℤ_{≥1}; columns right of face
j are unchanged. ⌈h + z⌉ = ⌈h⌉ + z for z ∈ ℤ, so N gains
c′_j := x_j·L_j + L_j(L_j+1)/2 ∈ ℤ_{≥1}. A unit increment of the gap variable
w_j performs this elementary move on every face j′ ≤ j, so N gains
c_j = Σ_{j′≤j} c′_{j′} ≥ 1. Vertex columns are determined by the L's alone. ∎

**Theorem 4 (master denominator theorem)** *(c)*. Every rational function the
𝔅_n solve produces — every K_e entry, terminal row, split row, J cell,
entrance ι, shape weight W, every blockSolve β_{e,τ}(σ′), every β-leg
q ↦ Σ_{σ′} β_{e′,τ′}(σ′)(q^δ) at every δ ≥ 1, and the assembled R_σ — lies in
ℛ. Consequently (Lemma R0(i)) NO entry of the intended instance has a pole at
any rational x with |x| ≥ 2 — in particular at any prime power q₀ = p^m ≥ 2.

*Proof.* Induction over the assembly grammar of §1, using Lemma R0 throughout:

1. *Polynomial data* ∈ ℚ[q] ⊂ ℛ: configuration/divisor-pattern counts, the
   irreducible-point counts D^{-1}Σ_{δ|D} μ(δ)q^{D/δ}, residual-shape counts.
2. *Normalizations*: q^{-e} ∈ ℛ; the residual-pool normalization
   (q^d − q^{d−1})^{-1} = q^{1−d}·(q − 1)^{-1} ∈ ℛ; the projective assembly's
   |Pⁿ(F_q)|^{-1} = (q − 1)/(q^{n+1} − 1) ∈ ℛ.
3. *Fixed-depth Igusa volumes* (1 − q^{-1})^V·q^{-N} ∈ ℛ.
4. *Geometric depth closures*: by Lemma S5 each unbounded depth variable
   contributes Σ_{w≥0} A·q^{-c·w} = A·q^c/(q^c − 1) with c ∈ ℤ_{≥1} and A
   already in ℛ (the finite residue enumeration is a finite ℛ-sum) — in ℛ.
   The (O3) in-place resummation Σ_{L≥1} q^{-EL} = 1/(q^E − 1) is the same
   shape.
5. *Base change* q ↦ q^δ: Lemma R0(ii). (This covers both the divisor-pattern
   legs, δ ≤ e ≤ n, and the residual-descent legs, and their compositions at
   arbitrary composite depths.)
6. *The block solve*, bottom-up in e: β_e = Φ_e^{-1}·(exit rows), and Φ_e is a
   unit of ℛ (Lemma R0(iii)), exit rows ∈ ℛ by 1–5 and the inductive
   hypothesis on smaller blocks (the β-legs feeding block e's split rows are
   β_{e′}, e′ < e, composed with q ↦ q^δ — in ℛ by induction and 5). σ′-sums
   are finite. Adjugate/Cramer introduces no denominator beyond Φ_e (here K_e
   is scalar, so this is just division by 1 − κ). ∎

Numeric pin (§10, test C/D): for e ≤ 5 every reduced denominator of every
assembled β_e[t], and for n ≤ 5 every reduced denominator of every R_σ, has
rational roots only in {0, ±1} — exactly ℛ-shaped, zero exceptions.

## 6. Theorem 5: O-12 — the (REG-p) failing set is EMPTY at 𝔅_n

**Theorem 5** *(c — the leaf)*. At the intended instance 𝔅_n (any n ≥ 2, any
of the three on-record kernel organizations), for EVERY prime p, every depth
δ ∈ Δ (indeed every integer δ ≥ 1), and every block e ∈ [1, n], both (REG-p)
clauses hold at q₀ = p^δ:

(r1) Φ_e is defined at q₀ (D_{Φ_e} of cyclotomic type; Lemma RR) and
     Φ_e(q₀) ≠ 0 — with margin Φ_e(q₀) ≥ 3/4, 7/8, 6/7 per organization
     (Corollary D);
(r2) every entry g ∈ E(e) is defined at q₀ (Theorem 4: g ∈ ℛ, poles only in
     {0, ±1}); the active-value agreement is then free, since at a pinned
     record act is literal evaluation on the defined locus (M17 Lemma 0's
     `act_pin` argument, unchanged).

Hence RegP holds at every prime, i.e. by the formalized characterization
(`regP_failing_eq`) the failing set is EMPTY:

    {p prime : (REG-p) fails at 𝔅_n} = ∅,

and theoremU's per-prime hypothesis is available at EVERY prime — wild pools
included — upgrading K-13's "cofinite" to "all p". Moreover, since a positive
integer power of a prime power is a prime power, the same clauses hold at every
COMPOSITE depth m ∈ M̂ (M17 §6's descent-depth closure): M17 Theorem C's
sandwich collapses, left set = right set = ∅ — there is no undecided middle at
the intended instance. ∎

**Why this does not contradict the schema-level refutation.** The compiled
countermodel (`BridgeB15a_r2Neg.lean`) has Φ₁ = (q−4)²(q²−2)/q⁴ — its
numerator is NOT of cyclotomic type (rational root 4 = 2²), and indeed its
entries are not in ℛ. ℛ-membership is exactly the property that separates the
intended instance from admissible adversarial packs; it is not implied by the
carried chain laws (the countermodel satisfies them all), which is why O-12 is
an instance-level theorem, per the tree's framing.

## 7. Theorem 2/3: the organization-robust criterion (substochastic escape)

The tree's expected mechanism, proved as a standalone principle in case a
future Lean general-n pack organizes the blocks with finer state sets (e.g.
carry-algebra states at deep wild towers) where Theorem 1's scalar computation
does not literally apply.

**Theorem 2 (substochastic determinant positivity)** *(a — standard;
Levy–Desplanques + homotopy)*. Let M ∈ M_k(ℝ) have nonnegative entries and all
row sums ≤ 1 − ε for some ε > 0. Then det(I − M) > 0.

*Proof.* For t ∈ [0, 1], I − tM is strictly diagonally dominant:
(1 − tM_{ii}) − Σ_{j≠i} tM_{ij} ≥ 1 − t(1 − ε) ≥ ε > 0, and 1 − tM_{ii} > 0.
By Levy–Desplanques, det(I − tM) ≠ 0 on [0, 1]; it is continuous in t and
equals 1 at t = 0, hence positive at t = 1. ∎

**Theorem 3 (the criterion)** *(c — packaging)*. Let a block-e table (any
organization, any finite state set S_e) have the property that at a prime
power q₀ ≥ 2 the evaluated kernel K_e(q₀) is entrywise the Haar volume of a
continuation event, the events in one row pairwise disjoint, and each state
carries a termination/hand-off event of volume ≥ ε > 0 disjoint from the
row's continuation events. Then det(1 − K_e)(q₀) ≥ … > 0; in particular, if
additionally every K_e entry is defined at q₀ and evaluation commutes with det
there (the subring OKat argument already in the corpus,
`bridge_r1_on_activeLocus` pattern), clause (r1) holds at q₀. *Proof.* Row
sums ≤ 1 − ε; Theorem 2. ∎

At 𝔅_n the hypothesis holds with explicit uniform margins (Corollary D:
ε = 3/4, 7/8, 6/7 at every q₀ ≥ 2 and every e). What Theorem 3 asks of a
future pack is exactly the mass law (T-3/T-6): kernel mass + exit mass = 1
with exit mass bounded below — a per-table certificate, not new mathematics.
Open lemma for that contingency, stated honestly:

**OL-O12-1 (contingent, only if a future pack departs from 𝔅_n's
organizations).** The pack's kernel entries at every pool value are volumes of
disjoint continuation events with per-state termination margin ε(q₀) > 0.
(At 𝔅_n this is Theorem 1 + Corollary D; nothing further is owed.)

## 8. What this closes and what it does not (the honesty ledger)

CLOSED (this note): the O-12 leaf as charged — "a clean sufficient criterion
(all det-numerator roots …, hence no prime power ≥ 2) proved for all n":
* the criterion: every det-numerator and every entry denominator of the
  intended solve is of cyclotomic type (divides q^b·∏(q^c − 1)); rational
  roots ⊆ {0, ±1}; no prime power ≥ 2 is ever hit (Lemma RR);
* proved for ALL n at 𝔅_n (Theorems 1 + 4), in all three on-record kernel
  organizations simultaneously;
* the n = 2 real Lean instance: already closed by M17 §8 (cited, not re-proved
  — Φ₂ = (q³−1)/q³ = the (O2) det at E = 3; `n2_det`, `n2_pools_all`);
* the sealed n = 3 tables: their kernels/dets are the (O3) instance at
  E₂ = 3, E₃ = 6 (exact match to CASE_RESUMN3 S1/S3, re-verified);
* wild pools and descent depths: no special casing — every evaluation point
  is a prime power ≥ 2, and the theorems hold at ALL of them (the M̂ sandwich
  collapse, §6).

NOT part of this leaf (owned elsewhere, stated so the verifier can see the
seam): the identification of the EVENTUAL general-n Lean `UCarriers` pack with
𝔅_n (population/dictionary: O-2, T-7, O-14d); the correctness of 𝔅_n's masses
as true densities (value-correctness: T-7/O-11 — note the determinant and
denominator theorems here consume only the STRUCTURE of the table, never the
correctness of its values); and the contingent OL-O12-1 above if the pack's
organization changes. No claim in this note depends on unproved corpus rows.

## 9. Relation to prior art

(a) The substochasticity/spectral-escape mechanism was conjectured at M17 §8
(OL-1) and in the tree's O-12 reduction; this note converts it to a theorem
and strengthens it to the explicit cyclotomic-type computation (which gives
positivity margins uniform in q₀ and e — stronger than nonvanishing).
(b) The ℛ-subring viewpoint refines M17's Lemma C.2 (localization control) at
the intended instance: where C.2 left a sandwich between direct-depth and
composite-depth failure sets, ℛ-membership plus prime-power closure collapses
it. (c) The three-organization reconciliation (Theorem 1(2,3)) explains, from
one stratification, the three determinants on record — (q³−1)/q³ (Lean n=2),
(q³−q)/(q³−1) and (q⁶−q)/(q⁶−1) (sealed n=3), (q²−1)/q² (engine e=2) — which
had previously been recorded as three unrelated numbers.

## 10. Numerics executed (the falsifier, run FIRST per the charge)

Script: `verification/openmath/O12_regp_empty_scan.py` (exact sympy/Fraction
arithmetic; results `O12_regp_results.json`). Executed 2026-07-31, ALL PASS,
zero findings:

* **A (kernel structure, e = 2..6).** The engine's FULLMONIC(e) linear
  structure: ∂FULLMONIC(e)[t]/∂β_e[t] ≡ q^{1−e} exactly, all cross-derivatives
  ≡ 0, for every cluster type t — Theorem 1(1)'s diagonal-scalar claim, and
  with the rescale prefactor q^{-e(e−1)/2}: κ_e = q^{-(E−1)} exactly.
  REFUTES-hook: any deviating coefficient would have killed Theorem 1.
* **B (det numerators).** Rational roots of q^{E−1}−1 (e = 2..8), q³−1 (Lean
  n=2 gate AND real block-2), q³−q, q⁶−q (sealed n=3): all ⊆ {0, ±1}; direct
  positivity N(Q) > 0 at ALL 18120 prime powers 2 ≤ Q ≤ 200000.
* **C (assembled solve, e = 2..5).** Every β_e[t] reduced denominator has
  rational roots ⊆ {0, ±1} (ℛ-shape, Theorem 4); symbolic mass law
  Σ_t β_e[t] = 1 exact; at 18 prime powers Q ∈ [2, 128]: every value defined,
  in [0, 1], sums exactly 1; κ_e(Q), κ̂_e(Q) ∈ (0, 1).
* **D (full pipeline, n = 2..5).** Every R_σ = ρ(n, σ; q) reduced denominator:
  rational roots ⊆ {0, ±1}; Σ_σ ρ = 1 symbolically; prime-power values in
  [0, 1] summing to 1.
* Prior art consumed: N6-regp scan (95 primes, faithful + superset pools,
  n = 2, 3 real tables, 0 failures, E0 margin 6/7 = Corollary D's (O3) bound
  at q₀ = 2); RESUM-n3 seal re-verification (`resum_n3_seal.py`, dets and
  mass checksums exact at pools 2, 3, 4).

## VERDICT

VERDICT: PROVED (at the intended instance 𝔅_n, defined in §1 as the β
cluster-law block system, for every n and all three on-record kernel
organizations: every block determinant numerator/denominator and every
assembled entry denominator is of cyclotomic type — the solve lives in
ℛ = ℚ[q, 1/q, 1/(q^c−1)] where the determinants are units — so no prime power
p^m ≥ 2 is ever a zero or pole; both (REG-p) clauses hold at every prime,
every pool value, every descent depth; the failing set is EMPTY and theoremU's
per-prime hypothesis holds at every prime. The organization-robust
substochastic criterion (Theorems 2/3) is proved as backup with uniform
margins ≥ 3/4, 7/8, 6/7. Honest seams: the pin of future general-n Lean packs
to 𝔅_n is O-2/T-7/O-14d territory; the contingent OL-O12-1 fires only if such
a pack departs from the on-record organizations.)
