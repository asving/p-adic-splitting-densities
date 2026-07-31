# O12 — (REG-p) emptiness at 𝔅_n — Phase-B attempt REV 2 (Fable, 2026-07-31)

Repair of the V7 hostile verification (`V7_o12_verify.jsonl`, verdict UNSOUND)
of the rev-1 attempt (`O12_phaseB_attempt.md`) / brief (`O12_phaseB_verifybrief.md`).
V7 CONFIRMED: the entire determinant algebra (Theorem 1(2) identities, the O3
gcd reduction, the n = 2/3 concrete-table matches, the q₀ = 2, 3 values), the
subring argument L7/L5 line by line, the margins, and the numerics. V7 found
three critical errors and five justification gaps. This rev repairs ALL of
them; the two charged by the orchestrator — (1) L6 never proves the semantic
depth sums have c ≥ 1; (2) the (g7) solve step is invalid at organization O2
because its exit row contains the CURRENT β_e — are §1 and §2 below.

The repaired self-contained brief is `O12_phaseB_verifybrief_rev2.md`
(rev-1 verified parts byte-stable where possible). New falsifier:
`verification/openmath/O12_rev2_checks.py` (§5; ALL PASS, zero findings).

## 0. V7 findings → dispositions (no silent drops)

| V7 finding | class | disposition |
|---|---|---|
| C1: E(e) "all entries so generated" is not a finite set; 𝔅_n underdefined | CRITICAL | **FIXED §3**: E(e) redefined as an explicit FINITE list of closed stratum-family masses; the grammar 𝒢 demoted to proof device |
| C2: O2's exit row contains κ₁·(current β_e); (g7) division by 1−κ₀ invalid | CRITICAL | **FIXED §2**: O2 disentangled into the as-built no-feedback booking (division by the unit 1−κ₀ IS its solve) and the re-entrant reading O2′ (fixed point solved explicitly: β = s/(1−κ₀−κ₁), denominator a unit of ℛ) |
| C3: L6's exponent summed over an arbitrary column set I; coefficient can be 0; semantic link unproved | CRITICAL | **FIXED §1**: L6 restated with N = Σ over ALL e coefficient columns; NEW L6a proves this N is the exact exponent of the polygon cell (semantic link); L6b proves c_j ≥ 1 along every cone generator; L6c proves the residual factor is depth-free |
| G1: L4 cites Montes/Okutsu residual descent in a self-contained doc | GAP | **FIXED §4.1**: the block-index booking is made DEFINITIONAL (part of 𝔅_n's table data); L4's arithmetic bound μ < e is the only consumed content; the citation is flagged (a)-standard and consumed nowhere |
| G2: "exactly the (S-loop) strata" outruns the supplied stratum list | GAP | **FIXED §3**: the one-step partition of C_e is displayed as a COMPLETE finite list of stratum families; "exactly" now refers to that displayed partition |
| G3: the vector-state aside claims the margins transfer to (1−κ)^r | GAP | **FIXED §4.2**: aside now claims zero-set equality only; margins restricted to the scalar presentation (which is the one 𝔅_n carries) |
| G4: §8's corroboration coefficient q^{1−e} contradicts Theorem 1's q^{1−E} | GAP | **FIXED §4.3**: the omitted descent prefactor q^{−(E−e)}·q^{−(e−1)}… restored precisely: raw FULLMONIC coefficient q^{1−e} × rescale prefactor q^{−e(e−1)/2} = q^{1−E} exactly |
| G5: the O3 resummation display omitted κ₁ | GAP | **FIXED §4.4**: display corrected to Σ_{L≥1} κ₀^{L−1}κ₁ = (q−1)/(q^E−1); exits scaled by 1/(1−κ₀) = q^E/(q^E−1) ∈ ℛ^× |

Everything V7 confirmed is carried unchanged (§6).

## 1. Repair A (V7-C3): the polygon-stratum lemma, done right

Setting (as in rev 1 §2.2, unchanged): block e, the no-descent locus
C_e \ R_e, whose Newton data has minimal slope in (0,1) (Lemma L1). Write
g = x^e + a_1x^{e−1} + ⋯ + a_e; the *Newton diagram* is the point set
{(i, v(a_{e−i})) : i = 0, …, e−1} ∪ {(e, 0)} (column i carries a_{e−i}; the
anchor (e, 0) is the monic leading 1), and the *Newton polygon* is its lower
convex hull, read as a function H: [0, e] → ℝ_{≥0} (the largest convex
function below the diagram).

**Definition (face-kind sequence and its polygons).** A face-kind sequence is
κ = (L_j, b_j)_{j=1..k}: L_j ≥ 1, Σ_j L_j = e, b_j | L_j (write d_j := L_j/b_j),
and b_k ≥ 2. Set x_1 := 0, x_{j+1} := x_j + L_j (so x_{k+1} = e). An
*admissible slope tuple* is s_1 > s_2 > ⋯ > s_k with s_j = a_j/b_j in lowest
terms (a_j ∈ ℤ_{≥1}, gcd(a_j, b_j) = 1) and s_k ∈ (0, 1). The polygon
P = P(κ; s) is the convex piecewise-linear function with P(e) = 0 and slope
−s_j on [x_j, x_{j+1}] (heights h_i := P(i), strictly decreasing, h_e = 0).
Vertex columns: x_1, …, x_k (the columns where the maximal linear pieces
meet, plus the left endpoint x_1 = 0); the vertex heights
h_{x_j} = Σ_{j′ ≥ j} a_{j′}d_{j′} are INTEGERS (each face drops
L_{j′}·s_{j′} = a_{j′}d_{j′} ∈ ℤ).

**Lemma L6a (cell identification and volume — the semantic link)** *(c)*.
For every admissible P as above,

    { g : Newton polygon of g = P }
      = { g : v(a_{e−i}) ≥ ⌈h_i⌉ for EVERY column i ∈ {0,…,e−1},
              with equality v(a_{e−x_j}) = h_{x_j} at the k vertex columns },

and this event has Haar volume exactly

    (1 − q₀^{−1})^k · q₀^{−N(P)},   N(P) := Σ_{i=0}^{e−1} ⌈h_i⌉  — (†) —

with all ⌈h_i⌉ ≥ 1 (so the event lies in C_e).

*Proof.* "Hull = P" holds iff (α) every diagram point lies on or above P and
(β) every vertex of P is a diagram point. [If (α), then P is a convex
minorant of the diagram, so P ≤ H; if also (β), then at each vertex column
H ≤ (diagram point) = P, and on each face H is ≤ the chord of its endpoint
values (convexity), i.e. H ≤ P on all of [0, e]; so H = P. Conversely if
H = P: (α) is the definition of a lower hull; and each vertex of H must be
attained by a diagram point — otherwise H could be raised near that vertex,
contradicting maximality among convex minorants.] Now (α) at column i reads
v(a_{e−i}) ≥ h_i, and since v is a nonnegative integer (or ∞) this is
v(a_{e−i}) ≥ ⌈h_i⌉; (β) at vertex column x_j reads v = h_{x_j} (an integer).
At the anchor (e, 0): v(1) = 0 = h_e automatically — no constraint. The
coordinates a_i are independent Haar, with P(v(a) ≥ t) = q₀^{−t} and
P(v(a) = t) = (1 − q₀^{−1})q₀^{−t} for t ∈ ℤ_{≥0}; the event is a product of
one such condition per column, giving (†). Since all slopes are > 0 and
h_e = 0, every h_i > 0 for i < e, so ⌈h_i⌉ ≥ 1 and the cell lies in
{v(a_i) ≥ 1 ∀i} = C_e (Lemma L1(i)). ∎

**Lemma L6b (affine exponents with positive integer coefficients)** *(c)*.
Fix κ. (i) The elementary move a_j ↦ a_j + b_j (slope of face j alone grows
by 1) changes N by exactly

    c′_j = x_j·L_j + L_j(L_j+1)/2 ∈ ℤ_{≥1}.

(ii) The admissible slope tuples decompose as: a FINITE enumeration (the
rightmost numerator a_k ∈ {1,…,b_k−1} coprime to b_k, and the residues
r_j = a_j mod b_j, gcd(r_j, b_j) = 1, for j < k) times free gap variables
w_1, …, w_{k−1} ∈ ℕ, where — summing the cone right to left, each a_j running
over its residue class above the minimum admissible value given s_{j+1} — a
unit increment of w_j shifts N by exactly

    c_j = Σ_{j′ ≤ j} c′_{j′} ∈ ℤ_{≥1},

and the vertex count k is w-independent. In particular a face-kind with
k = 1 has NO unbounded parameter (the whole family is finite).

*Proof.* (i) Anchor P at the right (h_e = 0 fixed). Under the move, columns
strictly right of face j are unchanged; the column at distance
t ∈ {1, …, L_j} from face j's right endpoint x_{j+1} gains exactly t (the
slope over that face grew by 1; the right endpoint is fixed); every column
strictly left of face j gains the face's full extra drop b_j·d_j = L_j. All
gains are integers z, and ⌈h + z⌉ = ⌈h⌉ + z, so
ΔN = x_j·L_j + Σ_{t=1}^{L_j} t = c′_j, which is ≥ 1 since L_j ≥ 1. Vertex
columns are the x_j — determined by the L's alone.
(ii) Enumerate a_k finitely (s_k ∈ (0,1) bounds it). For j < k, given
s_{j+1}, the admissible a_j run over {a_j^min(s_{j+1}) + b_j·w_j : w_j ∈ ℕ}
where a_j^min(s_{j+1}) is the least element of the residue class r_j + b_jℤ
with a_j/b_j > s_{j+1}. Two facts compose: a unit step of w_j is the
elementary move on face j (ΔN = c′_j by (i)); and when s_{j+1} grows by 1
(an elementary move on face j+1), the minimum shifts by exactly one period,
a_j^min(s_{j+1} + 1) = a_j^min(s_{j+1}) + b_j (because a/b_j > s+1 ⟺
(a − b_j)/b_j > s, a bijection of the residue class). So in the iterated
right-to-left sum, evaluating each a_{j′} at its nested minimum, a unit
increment of w_j performs the elementary move on face j AND on every face
j′ < j (through the shifted minima) — total shift Σ_{j′≤j} c′_{j′} = c_j ≥ 1.
For k = 1: only a_k remains, and it is finitely enumerated. ∎

**Lemma L6c (the multiplier is depth-free)** *(c)*. Conditioned on
{polygon = P}, the residual data of the stratum — the residues
u_i := (a_{e−i}/π^{h_i} mod π) at the integer-height columns i of each face
(those at distances t ≡ 0 mod b_j from face j's right endpoint; this
classification depends only on b_j since gcd(a_j, b_j) = 1) — are
independent, uniform on F_{q₀}^× at the vertex columns (where v = h_i
exactly) and uniform on F_{q₀} at interior integer-height columns (where
v ≥ h_i = ⌈h_i⌉); the anchor contributes the constant 1. Hence the joint law
of the face residual polynomials R_j (degree d_j, coefficients the u's of
face j, nonzero ends) depends only on the face-kind κ — NOT on the slopes.
Every residual-shape probability is therefore ONE fixed element of ℚ(q) —
a count ratio of the forms (g1)/(g2) — constant along the depth cone.

*Proof.* Haar coordinates are independent; conditioning is per-coordinate
(L6a's product form); a coordinate conditioned on {v = t} has residue of
a/π^t uniform on F^×, one conditioned on {v ≥ t} uniform on F. Whether a
column of face j has integer height is t·a_j/b_j ∈ ℤ ⟺ b_j | t (coprimality)
— slope-free. Counts of columns and their vertex/interior classification
depend only on (L_j, b_j). ∎

**Corollary L6′ (the (g4) closure, repaired).** The closed mass of every
polygon stratum family (a face-kind κ plus a residual shape, summed over
its depth cone) is a finite sum — over the finite enumeration of L6b(ii) —
of terms

    A · ∏_{j=1}^{k−1} q^{−c_j·w_j}  summed to  A · ∏_j q^{c_j}/(q^{c_j} − 1),

with every c_j ∈ ℤ_{≥1} (L6b) and A ∈ ℛ of forms (g1)–(g3) and w-independent
(L6a gives A's cell part (1 − q^{−1})^k q^{−N(min)}; L6c gives the
residual-shape factor; the conditional normalization q^{+e} is polynomial).
These are exactly the (g4) grammar shapes; no other unbounded parameter
exists in 𝔅_n's stratum families (the divisor patterns and residual shapes
are finite; the only other unbounded index on record is the O3 in-place run
length L, with ratio κ₀ = q^{−E}, E ≥ 3 — also (g4)-shaped). ∎

Falsifiers (§5): CHECK 1 verifies (†) exhaustively (hull-computed fibers vs
the formula, exact, five (e, p) blocks incl. the L1 dichotomy aggregates);
CHECK 2 verifies ΔN = c_j ≥ 1 and V = k over 2536 cone moves, e ≤ 7.

## 2. Repair B (V7-C2): the O2 bookings and the repaired solve step (g7)

The V7 objection, verbatim in substance: rev 1 defined O2's kernel as (κ₀)
with "recenterings booked as exits", yet Lemma L3 makes a nonzero-center
recentering re-enter the SAME size-e state law, so the O2 "exit row"
contains κ₁·β_e — the current unknown — and dividing by Φ^{(O2)} = 1 − κ₀
does not solve the block. CORRECT as charged: rev 1 conflated two distinct
bookings under one name. They are now separated; both are proved.

**(O2) — the as-built terminal booking (the machine-checked n = 2 table).**
As table DATA: kernel K_e = (κ₀); the recentering mass κ₁ is booked INTO the
terminal/exit rows as a plain ℚ(q) summand (at n = 2: into the second
terminal row — kernel q^{−3}, terminal rows 1 − 1/q and 1/q − q^{−3}, which
sum with the kernel to 1); NO exit row re-enters block e. The solve is the
genuine no-feedback division

    β_e = (1 − κ₀)^{−1} · (exit rows),   1 − κ₀ = (q^E − 1)/q^E ∈ ℛ^×,

so (g7) applies verbatim. Cross-check against the recorded n = 2 table:
(1 − 1/q)/(1 − q^{−3}) = q²/(q²+q+1) and (1/q − q^{−3})/(1 − q^{−3}) =
(q+1)/(q²+q+1) — exactly the recorded solve pair (§5 CHECK 3b, exact).
*Honesty:* this booking is value-UNFAITHFUL to the semantics (L3 says the
recentered cluster re-enters the state law; folding κ₁ into a terminal row
changes the solved VALUES — the corpus's standing Finding F1, "the as-built
n = 2 device chain has the wrong value triple", says precisely this). Value
correctness is NOT part of O-12 (it is T-7/O-11/D-11 territory); (REG-p)
consumes only zero/pole structure, which is what is proved.

**(O2′) — the re-entrant reading (what rev 1's wording accidentally
defined).** Kernel booked as (κ₀); the κ₁ strata booked as exit legs that
re-feed block e's own entrance. The block's balance equation is then the
fixed point

    x = κ₀·x + (κ₁·x + s_e),   s_e = the true exit row (blocks < e and
                                     terminals only),

which is NOT a division by 1 − κ₀. Repair (the orchestrator's option (a)):
solve it. In ℚ(q) the equation is (1 − κ₀ − κ₁)x = s_e with
1 − κ₀ − κ₁ = 1 − q^{1−E} = (q^{E−1} − 1)/q^{E−1} ≠ 0, so the UNIQUE solution
is

    β_e = (1 − q^{1−E})^{−1} · s_e,   1 − q^{1−E} ∈ ℛ^×  — (‡) —

and β_e ∈ ℛ whenever s_e ∈ ℛ. The booked determinant is still
Φ^{(O2′)} = 1 − κ₀ (same as O2, nonvanishing with margin 7/8 by Corollary D);
the ENTRY list of O2′ contains κ₀, the leg weight κ₁ = (q−1)q^{−E} ∈ ℛ, the
s_e members, and the SOLVED β-legs (‡) — all in ℛ.

**Repaired (g7).** β_e := the unique ℚ(q)-solution of block e's balance
equation x = (within-block return mass)·x + (non-returning row). Per booking
the return mass is κ₀ + κ₁ (O1: all in kernel; O2′: κ₀ kernel + κ₁ re-entrant
leg; O3: resummed κ̂ = κ₁/(1−κ₀) with row scaled by (1−κ₀)^{−1} — equation
(1−κ̂)x = s_e/(1−κ₀), equivalent) or κ₀ alone (O2: no return beyond the
kernel, by its booking). In every case the solved form is

    β_e = u^{−1} · (row ∈ ℛ),   u ∈ {1 − q^{1−E}, 1 − q^{−E}} ⊂ ℛ^×,

so the bottom-up induction of Theorem 2 (master denominator theorem) closes:
rows are (g1)–(g6) combinations of the closed stratum masses (§1) and of
lower-block β-legs β_{e′}(q^δ), e′ < e (in ℛ by induction + base change).

**Theorem 1(3), restated honestly.** The three re-entrant bookings O1, O2′,
O3 have the SAME solve — all three balance equations are algebraically
(1 − κ₀ − κ₁)x = s_e (for O3, after multiplying by the unit 1 − κ₀). The
terminal booking O2 has a DIFFERENT solve (different rows, no feedback); at
e = 2 the divergence is explicit: re-entrant solve (q/(q+1), 1/(q+1)) vs
as-built (q²/(q²+q+1), (q+1)/(q²+q+1)) — F1's wrong value triple, both pairs
ℛ-shaped, both mass-1 (§5 CHECK 3c, exact). Rev 1's claim that all
organizations share one solve is hereby CORRECTED: the shared-solve claim
holds for {O1, O2′, O3}; O2 shares only the stratification and the zero/pole
structure — which is all O-12 consumes.

## 3. Repair C (V7-C1): E(e) as an explicit finite list

𝔅_n's block-e table rows are the CLOSED masses of the following stratum
families — a finite list, displayed as the complete one-step partition of
the state law (this display also discharges V7-G2's "exactly"):

    C_e = R_e ⊔ (C_e \ R_e)                                [L1 dichotomy]
    R_e:  substratified by the reduction h̄ of the uniform rescale
          (Lemmas L2, L3) — the complete finite partition of monic
          degree-e h̄ over F_q by factorization pattern:
       (i)   h̄ = (y−c)^e, c = 0:            the in-place loop, mass κ₀;
       (ii)  h̄ = (y−c)^e, c ≠ 0:            the recentering strata, κ₁
                                             (booked per organization, §2);
       (iii) every other pattern π = {(D_i, m_i)}, ΣD_im_i = e, π ≠ {(1,e)}:
             mass q^{−(E−e)}·N_π(q)/q^e (N_π = the monic count with
             pattern π, a ℚ-polynomial in q); parts with m_i ≥ 2 are booked
             as hand-offs to block m_i at base change q ↦ q^{D_i} (m_i < e
             by Lemma L4(i)); parts with m_i = 1 are terminal (Hensel).
    C_e \ R_e: substratified by face-kind κ and residual shape (finitely
          many, §1), each with ONE closed mass (Corollary L6′); residual
          factors of multiplicity μ ≥ 2 and degree D are booked as hand-offs
          to block μ at q ↦ q^D (μ < e by Lemma L4(ii)); μ = 1 terminal.

**E(e) := the finite list**: the kernel entry (per booking); the closed
family masses above; the terminal, split and junction rows (finite
ℚ(q)-combinations of family masses with products of lower-block β-legs);
the entrance/shape weights (the (g2) normalizations); the β-legs
q ↦ Σ_{σ′} β_{e′,τ′}(σ′)(q^δ) for e′ < e and δ ∈ Δ; and block e's own
solved β_e(σ). Finiteness: patterns π, face-kinds, residual
shapes, verdicts σ of degree ≤ n, blocks, and Δ are all finite sets. The
grammar 𝒢 of rev 1 is retained purely as the PROOF DEVICE: Theorem 2's
induction shows each listed member is built from (g1)–(g6) + solved (g7)
steps, hence lies in ℛ. "𝔅_n" now denotes this fully specified finite table
(per booking of §2); no quantification over "everything generated" remains.

## 4. The justification-gap fixes (V7-G1..G5)

1. **L4 / residual descent (G1).** The booking "a multiplicity-μ, degree-D
   residual factor hands off to block μ at base change q ↦ q^D" is part of
   𝔅_n's DEFINITION (table data), not an imported theorem. Lemma L4's
   arithmetic (μ ≤ d ≤ max(e/2, e−2) < e; divisor parts m < e) is the only
   content consumed by Theorems 1–3. That this booking is semantically the
   Montes/Okutsu residual descent is (a)-standard and is consumed NOWHERE in
   this leaf (it belongs to the value-correctness nodes T-7/O-11/D-11).
2. **Vector-state aside (G3).** If the solve is graded by splitting type,
   K_e = κ·Id and det = (1−κ)^{#types}: the aside now claims only that this
   has the SAME ZERO SET as 1 − κ (so (r1)'s nonvanishing is presentation-
   independent); the displayed margins 3/4, 7/8, 6/7 are claims about the
   singleton-state presentation, which is the one 𝔅_n carries.
3. **§8 corroboration (G4).** The exact scan verified the raw FULLMONIC
   self-coefficient q^{1−e} at the (1,e)-cell; multiplying by the descent
   rescale prefactor q^{−e(e−1)/2} — and e(e−1)/2 = E − e — gives the loop
   mass q^{1−e}·q^{−(E−e)} = q^{1−E} of Theorem 1(1) EXACTLY, e = 2..6. The
   rev-1 attempt carried the prefactor sentence; the rev-1 brief dropped
   it — restored.
4. **O3 resummation display (G5).** The in-place resummation is
   Σ_{L≥1} κ₀^{L−1}κ₁ = κ₁/(1−κ₀) = (q−1)/(q^E−1) (the KERNEL), and the exit
   rows are scaled by Σ_{L≥0} κ₀^L = 1/(1−κ₀) = q^E/(q^E−1) ∈ ℛ^× — both
   (g4)/unit shapes; rev 1's display Σ_{L≥1} q^{−EL} = 1/(q^E−1) described
   only the scaling factor's geometric core and mislabeled it. Corrected.

## 5. Numerics executed (falsifier-first; this session)

Script `verification/openmath/O12_rev2_checks.py`; log
`logs/O12_rev2_checks.log`; results `O12_rev2_results.json`. ALL PASS, zero
findings:

* **CHECK 1 (L6a, the semantic link).** Exhaustive over (ℤ/p^M)^e for
  (e,p,M) ∈ {(2,2,7), (2,3,5), (3,2,6), (3,3,4), (4,2,5)}: every Newton-hull
  fiber with decidable heights matches (1−1/p)^V p^{−N}·p^{eM} EXACTLY
  (19+11+29+13+32 hulls); aggregates match vol(C_e) = q^{−e},
  vol(R_e) = q^{−E}, vol(C_e\R_e) = q^{−e} − q^{−E} exactly (the L1
  dichotomy). e = 2 has exactly ONE polygon bucket — the k = 1 finiteness.
  REFUTES-hook: any fiber deviation kills L6a.
* **CHECK 2 (L6b).** 2536 cone moves over all 139 face-kind sequences with
  e ≤ 7: ΔN = Σ_{j′≤j}(x_{j′}L_{j′} + L_{j′}(L_{j′}+1)/2) exactly, always
  ≥ 1, vertex count constant.
* **CHECK 3 (repaired g7).** (a) E ∈ {3,6,10,15}: the O1/O2′/O3 balance
  equations all solve to s/(1−q^{1−E}), extra denominator q^{E−1}−1 with
  rational roots ⊆ {±1}. (b) as-built n = 2: (terminals)/(1−q^{−3}) equals
  the recorded solve pair exactly; mass law; q²+q+1 | q³−1. (c) the value
  divergence is real: (q/(q+1), 1/(q+1)) ≠ (q²/(q²+q+1), (q+1)/(q²+q+1));
  both ℛ-shaped (q+1 | q²−1).

Rev-1 numerics (18120 prime powers, engine structure e ≤ 6, full pipeline
n ≤ 5) stand unchanged and were confirmed by V7.

## 6. Byte-stable perimeter (what V7 confirmed; carried verbatim into rev 2)

Lemmas L1, L2, L3, L5, L7 and their proofs; Theorem 1(1) (the stratification
and masses κ₀, κ₁) and 1(2) (all determinant identities incl. the O3 gcd
reduction); Corollary D with margins 3/4, 7/8, 6/7 (7/8 now also covers
O2′); Theorem 2's (g1)–(g6) steps; Theorem 3's quantifier structure
(every p, every δ ≥ 1, prime-power closure of composite depths); Theorem 4
(Levy–Desplanques/substochastic backup); the §7 concrete-table data. The
scope declaration is unchanged, with one clarification made explicit: value
correctness of any booking is outside the claim (F1 already on record).

## VERDICT

VERDICT: REPAIRED (both charged gaps closed with proofs — L6 rebuilt as
L6a/L6b/L6c + Corollary L6′ with the full-column exponent, the cell
identification, c_j ≥ 1 along every cone generator, and the depth-free
multiplier; the O2 circularity dissolved by splitting the as-built
no-feedback booking (solve = division by the unit 1 − κ₀, matching the
recorded n = 2 table exactly) from the re-entrant reading O2′ (fixed point
solved explicitly: β_e = (1 − q^{1−E})^{−1}s_e, denominator a unit of ℛ) —
plus V7's third critical (E(e) now an explicit finite list) and all five
justification gaps. The O-12 theorem stands at the rev-1 honest scope: at
𝔅_n, every booking on record, every block determinant and every entry
denominator is cyclotomic-type, the (REG-p) failing set is EMPTY at every
prime, every pool value, every descent depth. Seams unchanged: instance pin
= D-11/O-2/T-7/O-14d; value correctness excluded (F1); contingent OL-O12-1
fires only for future non-𝔅_n organizations. New falsifiers: 3 checks, all
exact, zero findings.)
