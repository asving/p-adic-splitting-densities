# M08-cl6-general — attempt (Fable, 2026-07-31)

Target: `BridgeKernels.cl6` at general n — `Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)`
for the intended polygon-geometry pack at every degree n. See the companion brief
(`M08-cl6-general_brief.md`) for the full unfolding; notation from there:
per row (e, τ, o) a presentation (A, B, G) = (countT, countS, geom), law (1) =
A ℕ-valued at pools, law (2) = B equals the cell-fiber census at active pools.

**Result shape (summary).** (i) The row is NOT a theorem over the abstract pack —
this is already compiled in the corpus (countermodel + scaling freedom), so the
mathematical content lives entirely at the intended instance. (ii) I prove an
exact reduction: the row at ANY pack is equivalent to the two value laws (1)+(2)
(Lemma 1). (iii) I prove, rigorously and self-contained, the counting theorem
that IS laws (1)+(2) at the order-1 (level-1 Newton polygon) states of the
intended pack, for every n, every prime power q₀ = p^δ (wild p included), and
every complete DVR with the given residue field — Theorem 2 below, with an
explicit census polynomial. Machine-checked on 62 (stratum, p) rows across
e ∈ {2,3}, N ∈ {3,4}, p ∈ {2,3,5,7} (zero mismatches; script committed alongside).
(iv) The order ≥ 2 (deep OM tower) extension is reduced to four explicitly
stated open lemmas (OL-A–OL-D) in Guàrdia–Montes–Nart vocabulary. (v) The row is
not literature-axiom-eligible as stated; component literature identified.
Verdict: PARTIAL.

---

## 1. The exact abstract residue of the obligation

**Lemma 1 (reduction; label: (b) — new proof of a corpus-adjacent fact; the ⇐
direction is verbatim the corpus theorem).** For ANY pack (T, M, RB) of the
project's types:

    Nonempty (PolyGeomLaws T M RB)  ⟺  (H_T) ∧ (H_S), where
    (H_T): ∀ e τ o, ∀ q₀ ∈ Pools:  A_{e,τ,o}(q₀) ∈ ℤ_{≥0};
    (H_S): ∀ e τ o, ∀ q₀ ∈ Pools with Act(q₀,e,τ):
           B_{e,τ,o}(q₀) = Σ_{c ∈ cells(o)} #Inst(c, q₀, ℓ(c)).

*Proof.* (⇐) This is `MovesV.polygeom_count_laws` (V7_pgLaws.lean:91): its Lean
proof consumes ONLY the hypotheses hTCount = (H_T) and hSCount = (H_S) (the
V-side premises in its signature are not used by the proof term); it takes
tCount e τ o q₀ := (A(q₀)).num.toNat, discharges `tcount_val` from (H_T),
`scount_val` := (H_S), and the two degree legs from RB's own fields
(`degT_le` + `tg_degT`, `degS_le` + `tg_degS`). (⇒) Given hPGL, (H_T) holds
with witness k := hPGL.tCount e τ o q₀ by `tcount_val`, and (H_S) is
`scount_val`. ∎

**Recorded non-theorems (corpus facts, cited for scope).** (a) At arbitrary-pack
generality neither (H_T) nor (H_S) is derivable from RatBurdens: the rescaling
countS ↦ 2·countS, geom ↦ geom/2 preserves val, all degree data and every
RatBurdens law, and breaks (H_S) whenever some census is nonzero (ADJ-4,
V7_pgLaws docstring). (b) At the as-built n = 2 pack the package is EMPTY
(`n2_polyGeomLaws_isEmpty`): a padding presentation carries countS = 1 against
an empty cell fiber. Consequence: cl6 is a law about how the pack is BUILT.
Everything below therefore attacks the intended instance: the pack builder must
choose A := the honest T-count polynomial and B := the honest census polynomial,
and the mathematics owed is that such polynomials EXIST (one polynomial each,
correct at every pool, degrees within the W-pins). Note also a rigidity fact
used below: since Pools is infinite, if a state is active at infinitely many
pools then B is the UNIQUE polynomial satisfying (H_S) there; the builder has no
freedom (and on finitely-active or inactive rows the honest choice is forced
only by discipline, not by (H_S) — the n = 2 padding failure is exactly this
corner).

---

## 2. The level-1 counting theorem (proved)

This section proves laws (1)+(2) in their standalone form (brief §5(II)) for the
order-1 states of the intended pack: states whose cells are level-N Newton
polygon + residual factorization strata. It is stated for the "ramified block"
f̄ = x^e; Remark 2.8 lifts it to a general block (residual key polynomial of
degree f₀ > 1), which replaces q by q^{f₀} in the residual counts and keeps
polynomiality in q.

### 2.1 Setting and the stratum census

Let O be ANY complete discrete valuation ring with finite residue field F_q,
uniformizer π, valuation v, v(π) = 1 (mixed or equal characteristic — this
generality is exactly the pools' p-uniformity, wild p included). Consider monic
f(x) = x^e + a_{e−1}x^{e−1} + ⋯ + a_0, a_i ∈ O, with v(a_i) ≥ 1 for all i (the
x^e-block condition).

A **level-1 stratum datum** is D = (Δ, (λ_S)_S):

* Δ: a lower-convex polygon from (0, y₀) to (e, 0), y₀ ≥ 1, with vertices in
  ℤ², slopes strictly increasing left to right and all < 0. Write Δ(i) for its
  value at abscissa i; a **lattice slot** is an i with (i, Δ(i)) ∈ ℤ² on Δ
  (equivalently i = i_S + j·e_S along the side S of slope −h_S/e_S,
  gcd(h_S, e_S) = 1, of horizontal length ℓ_S·e_S starting at i_S).
* For each side S: λ_S, a factorization type of degree-ℓ_S polynomials over F_q
  with nonzero constant term — a multiset of (degree, multiplicity) pairs with
  Σ d·m = ℓ_S. (Types are invariant under scalar multiplication; that suffices
  below, and any per-side scaling-invariant class works verbatim.)

The **residual polynomial** of side S is
R_S(y) := Σ_{j=0}^{ℓ_S} z_{i_S + j e_S} y^j ∈ F_q[y], where for a lattice slot i,
z_i := (a_i π^{−Δ(i)} mod π) ∈ F_q (and z_e := 1 from monicity). The stratum
conditions are: NP(f) = Δ — i.e. v(a_i) ≥ Δ(i) for all i with equality exactly
at the vertices — and type(R_S) = λ_S for every S. Note the conditions force
z_i ≠ 0 at vertices, so each R_S has nonzero constant term and nonzero leading
coefficient automatically.

Fix a level N > max_i Δ(i). The conditions are then determined by the residues
a_i mod π^N, and the **census** is

    C_{D,N}(q; O) := #{ (a_0, …, a_{e−1}) ∈ (O/π^N)^e : NP(f) = Δ,
                        type(R_S(f)) = λ_S for all sides S }.

**Theorem 2 (level-1 census law).** With c_i := Δ(i) + 1 if i is a lattice slot
of Δ (vertices included) and c_i := ⌈Δ(i)⌉ otherwise (0 ≤ i ≤ e−1):

    C_{D,N}(q; O) = q^{E(D,N)} · ∏_S M_{λ_S}(q),      E(D,N) := Σ_{i=0}^{e−1} (N − c_i),

where M_λ ∈ ℚ[X] is the polynomial of Lemma B below with
M_λ(q) = #{monic R ∈ F_q[y] : deg R = ℓ, R(0) ≠ 0, type(R) = λ} for every prime
power q. In particular: C_{D,N}(q; O) is the value at q of ONE polynomial
P_{D,N} ∈ ℚ[X] independent of O, of p, of δ (q = p^δ), and of the choice of
uniformizer; it is a count, hence ℕ-valued at every prime power; and
deg P_{D,N} = E(D,N) + Σ_S deg M_{λ_S} ≤ E(D,N) + Σ_S ℓ_S.

This is exactly law (2) for order-1 cells (each cell of the intended pack is
such a stratum or a finite disjoint union of them; censuses add), and law (1)
for the rows whose T-count is a one-window census from a representative
(Remark 2.7). The proof occupies 2.2–2.6.

### 2.2 Lemma A (slot counts)

For b < N and any z ∈ F_q, writing digit_b(a) := (a π^{−b} mod π) for a with
v(a) ≥ b:

    #{a ∈ O/π^N : v(a) ≥ b} = q^{N−b},
    #{a ∈ O/π^N : v(a) ≥ b, digit_b(a) = z} = q^{N−b−1}.

*Proof.* π^b·(O/π^{N−b}) ⊆ O/π^N is the first set, and O/π^{N−b} has q^{N−b}
elements (its π-adic filtration has N−b graded pieces, each an F_q-line). The
second set is a coset-fiber of the surjection O/π^{N−b} → O/π ≅ F_q (for z = 0
it is {v ≥ b+1}, same count). No further structure of O is used. ∎

Consequently the census factors through the per-coordinate data
(v(a_i) constraints; the residue digit z_i at lattice slots):

    C_{D,N}(q; O) = q^{E(D,N)} · Z_D(q),
    Z_D(q) := #{ (z_i)_{i lattice slot, i<e} : z_i ∈ F_q^× at vertices,
                 z_i ∈ F_q at interior lattice slots, z_e := 1,
                 type(R_S) = λ_S for all S }.

(Per coordinate: non-lattice i contributes q^{N−⌈Δ(i)⌉} free choices; a lattice
slot i contributes q^{N−Δ(i)−1} choices above its pinned digit z_i, by Lemma A.
The identity NP(f) = Δ ⟺ [v(a_i) ≥ Δ(i) ∀i, equality at vertices] is the
standard lower-hull characterization; "equality at vertex" = "z_i ≠ 0".)

### 2.3 Lemma B (the type-count polynomial M_λ)

Let I_d(X) := (1/d) Σ_{k∣d} μ(k) X^{d/k} ∈ ℚ[X] (Gauss; I_d(q) = the number of
monic irreducibles of degree d over F_q — Lidl–Niederreiter, *Finite Fields*,
Thm 3.25). For a type λ, group its entries by degree: for each d let the
multiplicities be the multiset {m_{d,1}, …, m_{d,r_d}} and let a_{d,m} be the
number of j with m_{d,j} = m. Define

    M_λ(X) := ∏_d  binom(I_d(X) − [d=1], r_d) · ( r_d! / ∏_m a_{d,m}! ).

Then M_λ ∈ ℚ[X]; M_λ(q) is, at every prime power q, the number of monic
degree-ℓ polynomials over F_q with nonzero constant term and type λ; and
deg M_λ = Σ_d d·r_d ≤ ℓ.

*Proof.* Such a polynomial is uniquely a product ∏ P_{d,j}^{m_{d,j}} of DISTINCT
monic irreducibles P_{d,j} ≠ y of degree d. Choosing, for each d, an
r_d-subset of the I_d(q) − [d=1] admissible irreducibles and one of the
(r_d!/∏ a_{d,m}!) assignments of the multiplicity multiset to it enumerates each
polynomial exactly once. binom(P(X), r) := P(P−1)⋯(P−r+1)/r! ∈ ℚ[X] for
P ∈ ℚ[X], of degree r·deg P; deg I_d = d. ∎

### 2.4 Lemma C (end-pinned counts are ratio class functions)

Fix ℓ ≥ 1 and a type λ. For u, w ∈ F_q^× let

    N_λ(w, u) := #{ (z_1, …, z_{ℓ−1}) ∈ F_q^{ℓ−1} :
                    R(y) = w + z_1 y + ⋯ + z_{ℓ−1} y^{ℓ−1} + u y^ℓ has type λ }.

Then (i) N_λ(w, u) = ν_λ(w/u) for a function ν_λ : F_q^× → ℕ, and
(ii) Σ_{t ∈ F_q^×} ν_λ(t) = M_λ(q).

*Proof.* (i) For β ∈ F_q^×, R ↦ βR is a type-preserving bijection carrying ends
(w, u) to (βw, βu); take β = u⁻¹. (ii) Summing over all ends:
Σ_{(w,u) ∈ (F_q^×)²} N_λ(w, u) = #{R : deg ℓ, R(0) ≠ 0, leading ≠ 0, type λ}
= (q−1)·M_λ(q) (bijection R ↔ (leading unit, monic normalization)). The left
side is Σ_u Σ_w ν_λ(w/u) = (q−1) Σ_t ν_λ(t). ∎

### 2.5 Warning examples (ν_λ is NOT constant — the audit is real)

Nothing stronger than Lemma C is true, and this is the precise level-1 shadow of
the note's EXPONENT-MAP AUDIT. Two verified examples over F_q, q odd, χ the
quadratic character:

* λ = {irreducible quadratic} (ℓ = 2): ν_λ(t) = #{z : y² + zy + t irreducible}
  = (q − χ(t))/2. (Machine-checked at q = 3, 5, 7, 11, 13: ν takes exactly the
  two values (q∓1)/2 and sums to I_2(q).)
* λ = {(y−r)², r ≠ 0} (double nonzero root): ν_λ(t) = #{r ∈ F_q^× : r² = t}
  = 1 + χ(t) ∈ {0, 2}.

So the count of a sub-stratum with PINNED end values (e.g. "residual polynomial
irreducible with constant term −1") is (q − χ(−1))/2 — genuinely dependent on
q mod 4, NOT a polynomial in q. Any table build that refines cells by pinned
residual END VALUES (rather than scaling-invariant classes) destroys CL-6; and
conversely, the aggregation that rescues polynomiality is exactly the next
lemma. This is the failure shape numeric falsification should target (tests T3,
T5 below).

### 2.6 Lemma D (vertex-chain telescope) and proof of Theorem 2

Label the vertices of Δ left to right v_0, …, v_k (v_k = (e, 0), z_{v_k} = 1;
sides S = 1..k, side S having left vertex v_{S−1} and right vertex v_S, so its
residual constant term is z_{v_{S−1}} and its leading coefficient z_{v_S}). Then

    Z_D(q) = Σ_{z_{v_0},…,z_{v_{k−1}} ∈ F_q^×}  ∏_{S=1}^{k} ν_{λ_S}( z_{v_{S−1}} / z_{v_S} )
           = ∏_{S=1}^{k} Σ_{t ∈ F_q^×} ν_{λ_S}(t)  =  ∏_S M_{λ_S}(q).

*Proof.* First equality: group the interior slots of each side and apply Lemma C
per side (conditions across sides interact only through the shared vertex
values, which are the arguments of the ν's). Second: substitute
t_S := z_{v_{S−1}}/z_{v_S}; since z_{v_k} = 1 is pinned, the map
(z_{v_0}, …, z_{v_{k−1}}) ↦ (t_1, …, t_k) is a bijection (F_q^×)^k → (F_q^×)^k
(invert backwards from z_{v_k}: z_{v_{S−1}} = t_S·z_{v_S}), and the summand
splits as ∏_S ν_{λ_S}(t_S). Third: Lemma C(ii). ∎

Theorem 2 follows: C = q^E · Z_D (2.2) = q^E ∏ M_{λ_S}(q) (Lemma D); the
degree, ℕ-valuedness, and O/p/δ-independence claims are read off Lemmas A–B. ∎

The telescope is load-bearing: by 2.5 the per-side factors with shared pinned
ends are non-polynomial individually; only the chain-aggregated census is
polynomial — and it is polynomial with the exact factorized value ∏ M_λ, i.e.
the non-polynomial character contributions cancel completely, not just
asymptotically. (Machine-checked directly: the joint two-side census with both
residual types nontrivial equals M_{λ₁}(q)·M_{λ₂}(q) exactly for all 9 type
pairs at q = 3, 5, 7, 11 — test T2 below.)

### 2.7 Remark (T-side rows at order 1)

A one-window T-count at an order-1 state is the number of digit assignments in a
fresh window (finitely many new coordinate-slots, each a valuation-inequality or
pinned-digit condition, plus scaling-invariant residual conditions on the new
window's side data from a FIXED representative x of the source state) realizing
outcome o. Such a count has exactly the 2.2-shape: q^{(free slots)} × (residue
conditions with the source's residues entering as FIXED nonzero constants in the
ratio arguments). Lemma C makes the resulting count independent of those fixed
constants: the pinned source residues enter ν-arguments as a fixed multiplier,
and the window's own free vertex variables telescope as in Lemma D. Hence the
one-window count from ANY representative is the same polynomial value — this
simultaneously gives law (1) (counts are ℕ-valued) AND the
representative-independence of the count ((iv)-REP's count shadow) at order 1.
I state this as a remark, not a theorem, because "window" at full generality is
fixed by the table build (OL-D below); for any CONCRETE window of the above
shape the proof is verbatim 2.2–2.6.

### 2.8 Remark (general blocks, f₀ > 1)

For a block keyed by a residue-irreducible φ̄ of degree f₀ (block degree e·f₀),
the φ-adic expansion f = Σ a_j(x) φ^j (deg a_j < f₀) replaces each coordinate
a_i ∈ O by a digit vector in O^{f₀}, the graded pieces of the slot filtration
become F_{q^{f₀}}-lines, and residual polynomials live in F_{q^{f₀}}[y]. Lemmas
A–D apply verbatim over F_{q^{f₀}}: the census is q^{f₀·E'} · ∏ M_{λ_S}(q^{f₀}),
again ONE polynomial in q (composition of polynomials). ℕ-valuedness and
uniformity persist. The count of the block-selection layer itself (how many f̄
have a given multiset of (φ̄-degree, multiplicity)) is a factorization-type
count over F_q — Lemma B again.

---

## 3. The order-r tower: reduction to four explicit open lemmas

The intended pack's deep states are order-r Okutsu–Montes types (r ≥ 2, the
wild tower). GMN = Guàrdia–Montes–Nart, *Newton polygons of higher order in
algebraic number theory*, Trans. AMS 364 (2012); theorem labels below are from
the repo's pinned citation file `docs/GMN_citations.md` (arXiv:0807.2620v2
numbering). Write f̄_r := f_0·f_1⋯f_{r−1} for the accumulated residual degree of
a type t of order r (its residual field F_{q^{f̄_r}} is finite — GMN fact (I) of
the pinned file).

**OL-A (order-r slot parametrization / level determinacy). OPEN.** For a type t
of order r with representative φ (GMN Thm 2.11) and a level-(r+1) stratum datum
(order-(r+1) polygon Δ_{r+1} with types λ per side): the stratum's defining
conditions on f are determined by finitely many φ-adic digit slots, each slot
carrying a valuation-inequality-or-pinned-digit condition in the v_t-filtration
whose graded pieces are F_{q^{f̄_r}}-lines, at explicit levels; and the stratum
is a finite disjoint union of cells of the pack matching cellLvl/cellInst.
[The mathematics is GMN §2 (Def 2.19/2.20/2.21: truncation, residual
coefficient, residual polynomial of order r); the open content is the exact
slot/level ledger against the pack's carriers — the project's CL-13/LVL-DET
territory, not classical literature.]

**OL-B (residual coefficients are twisted residues — the exponent-map audit).
OPEN.** In the evaluation chain of every table entry, each order-r residual
coefficient is (fixed unit twist) · (leading residue of its slot digit), i.e.
per-slot a BIJECTION of F_{q^{f̄_r}}; no map z ↦ z^a with a ≥ 2 survives
un-cancelled. [GMN's residual coefficient (Def 2.20) has this shape in GMN's
normalization — the twist is a monomial in previous-level residual data, a unit
constant once the type is fixed. The audit obligation is that the TABLE's chain
(norms/traces/ratios introduced by the build) preserves this; the note carries
it as a displayed per-table burden, and 2.5 shows exactly what goes wrong
otherwise.]

**OL-C (order-r census). OPEN, reduces to OL-A + OL-B.** Given OL-A/OL-B, the
order-(r+1) stratum census over O/π^N is q^{E'} · ∏_S M_{λ_S}(q^{f̄_r}) with E'
the free-slot count from OL-A's ledger — ONE polynomial in q, ℕ-valued at every
prime power, O/p/δ-independent. [Proof shape: verbatim 2.2–2.6 over F_{q^{f̄_r}};
Lemma C/D need no change — they are statements about an abstract chain of sides
over a finite field. The shared-vertex chains at order r are the same
combinatorics.]

**OL-D (per-row T-counts at the built table). OPEN, reduces to OL-A–OL-C.** For
each (e, τ, o) of the built general-n table, the one-window transition count
from a fixed representative is the value of one polynomial of degree
≤ W_loc(e, τ, o), ℕ-valued at every pool; and rows/cells empty at q₀ evaluate
to 0 there (law (1)'s unguarded corner). [Per 2.7 this holds for every window
of the level-1 shape; OL-D is its officialization once the table build fixes
the windows. The representative-independence of the VALUE beyond the count is
(iv)-REP — a separate carried row, not owed here.]

**Assembly.** OL-A–OL-D ⟹ (H_T) ∧ (H_S) at the intended general-n pack (choose
countT/countS := the displayed census polynomials; degrees within W by
construction of W as the slot-ledger widths) ⟹ cl6 by Lemma 1. Padding rows
(e ∉ [1, n], duplicate outcomes) must be built with countT := 1 or 0 and
countS := the honest fiber census (0 on empty fibers) — the generalization of
the concurrent n = 2 repair; this is construction discipline, not mathematics.

---

## 4. Literature status

* **Theorem 2**: label (a)/(b) mixed — the STATEMENT is known in essence: counts
  of this shape underlie the local computations of Bhargava–Cremona–Fisher–
  Gajović, *The density of polynomials of degree n over ℤp having exactly r
  roots in ℚp* (arXiv:2101.09590; Proc. LMS, 2022 — exact theorem/lemma number
  for the stratum-count step FLAGGED FOR LOOKUP; the repo's
  `verification/reconcile_om_bcfg.py` already cross-checks against their
  P(n,r;q)), and level-1 special cases go back to Ore-condition counts. I know
  of NO published statement of the joint-sides census with per-side
  factorization types and the chain normalization (Lemmas C+D); the
  self-contained proof above is new as a write-up ((b), possibly (c) for the
  precise joint statement). The n-degree generality costs nothing — n enters
  only through the roster of strata.
* **GMN** (pinned, `docs/GMN_citations.md`): the order-r vocabulary of §3
  (Thm 2.11; Defs 2.19–2.21; §3 Thms 3.1/3.7). GMN proves no counting statement
  of CL-6's form; it supplies the objects counted.
* **Why exact polynomiality needs a hand proof** (context, label (a)):
  Chatzidakis–van den Dries–Macintyre, *Definable sets over finite fields*,
  J. reine angew. Math. 427 (1992): general definable counts are only
  #X(F_q) = μq^d + O(q^{d−1/2}) within finitely many classes — exactness fails
  in general (2.5 is a live instance). Pas, *Uniform p-adic cell decomposition
  and local zeta functions*, J. reine angew. Math. 399 (1989): uniform-in-p
  rationality for definable p-adic families, large p — neither ℕ-valued
  per-stratum polynomials nor all-p coverage. So no off-the-shelf theorem
  discharges CL-6.
* **Axiom eligibility**: NOT literature-axiom-eligible. The Lean row is
  `Nonempty (PolyGeomLaws C.T C.MS C.RB)` over the project-internal carrier pack;
  at general n the pack is unbuilt, and no published statement matches even the
  intended instance (see the CDM/Pas gap above). If the orchestrator ever wants
  a citation-shaped cut, it should be at OL-B (GMN Def 2.20's twist shape) —
  but OL-B is an audit of the project's own tables, which no external source
  can certify.

## 5. Honest gap list

1. OL-A–OL-D open (everything at OM order ≥ 2, plus the official window/W
   ledger at order 1). These are the table-build deliverable the note itself
   fences ("per-entry closed forms are the table-build deliverable,
   gate-sealed at V.6").
2. Construction compatibility: Theorem 2 produces the count polynomials; the
   pack builder must additionally verify rowVal = A·B·G with G in the
   geometric denominator class X^b·∏(1−X^a). The geometric factors arise from
   the height resummation (XHD-s geometric series Σ_h q^{−(affine in h)}),
   which is a SEPARATE carried row (XHD/HMC), not owed by cl6; but the
   factored FORM is owed by the builder and is not proved here.
3. The activity guard asymmetry: (H_S) is only forced on the active locus;
   rows active at only finitely many pools leave countS under-determined —
   discipline (honest census interpolant) must be imposed at build time, as
   the n = 2 padding failure demonstrates.
4. Lemma 1's ⇐ direction relies on the corpus theorem `polygeom_count_laws`
   compiling at HEAD (verified 2026-07-31); its extra V-side binders are
   inert in the proof term but keep its signature theorem-under-burdens.

VERDICT: PARTIAL — cl6 is equivalent (Lemma 1, proved) to the two value laws
(H_T)+(H_S) at the pack; both are PROVED here for the intended order-1
(level-1 Newton-polygon) strata at every n, every prime power q₀ = p^δ and
every complete DVR (Theorem 2, machine-checked on 46 strata with zero
mismatches); the order ≥ 2 tower and the official table windows remain open as
the explicitly stated OL-A–OL-D; the row is not provable over abstract
carriers (compiled corpus countermodel) and is not literature-axiom-eligible.

## NUMERIC-TESTS

Executed (script: `lean/notes/openmath/M08-cl6-general_check.py`, pure Python,
no dependencies; re-run with `python3 M08-cl6-general_check.py`, ~2 min):

* T1 — census formula, brute force: enumerate ALL (a_0..a_{e−1}) ∈ (ℤ/p^N)^e,
  classify by (Newton polygon, per-side residual factorization type), compare
  each stratum's exact count with q^{E(D,N)}·∏ M_{λ_S}(q).
  RAN: e = 2, N ∈ {3,4}, p ∈ {2,3,5,7}; e = 3, N = 3, p ∈ {2,3,5}; e = 3,
  N = 4, p ∈ {2,3} — 62 (stratum, p) rows including two-vertex chains, cubic
  residual types, and wild p = 2 on ramified sides. RESULT: 0 mismatches.
  Confirms Theorem 2; any single mismatch refutes it.
* T2 — telescope isolation: joint residue-level census of a two-side chain
  with shared vertex, both residual types nontrivial (deg 2 each), rightmost
  vertex pinned to 1, over F_q. Prediction M_{λ₁}(q)·M_{λ₂}(q).
  RAN: q ∈ {3,5,7,11}, all 9 type pairs. RESULT: exact match everywhere.
* T3 — audit necessity (anti-test): per-fiber counts with pinned ends,
  ν_λ(t) for λ = {irreducible quadratic}. RAN: q ∈ {3,5,7,11,13}. RESULT:
  ν takes two distinct values {(q−1)/2, (q+1)/2} at every odd q (non-constant,
  = (q−χ(t))/2), while Σ_t ν(t) = I_2(q) exactly. Confirms 2.5.

Proposed (for the numerics fleet):

* T4 — prime-power pools (δ > 1): repeat T1 with O/π^N replaced by
  GR(p^N, δ) (Galois rings, mixed char) AND F_{p^δ}[t]/(t^N) (equal char),
  q₀ = p^δ ∈ {4, 8, 9, 25}. Residual factorization over F_{q₀} via cypari2
  (`ffgen`/`factorff`) or the `galois` package (neither in the default env —
  `pip install cypari2` per `verification/README.md`). CONFIRMS: counts equal
  the SAME polynomial values P_{D,N}(q₀) as computed from the T1 formula;
  REFUTES: any dependence on (p, δ) beyond q₀ = p^δ, or mixed-vs-equal-char
  disagreement. (Note: by Lemma A the equal-char run is near-tautological;
  the Galois-ring run is the real test.)
* T5 — congruence-class probe (the refutation shape): for strata whose sides
  have e_S ∈ {2, 3} or repeated residual factors, compare exact censuses at
  primes in different classes mod 3, 4, 8 (e.g. q ∈ {5, 7, 11, 13, 17, 19})
  at fixed (D, N). CONFIRMS CL-6: one polynomial fits all classes; REFUTES:
  any q mod a dependence — this is where a wrong table (pinned end values,
  un-audited exponent maps) would first show.
* T6 — order-2 probe (targets OL-C): n = 4 block, p odd, level-1 datum
  Δ = single side (0, 2)→(4, 0) (slope −1/2, ℓ = 2) with residual type
  {(1, 2)} (double nonzero root) — the multiplicity-2 factor forces an
  order-2 refinement. Enumerate a ∈ (ℤ/p^N)^4 for p = 3, N = 5 (3^20 ≈ 3.5G —
  restrict to the stratum by construction instead: enumerate its FREE digits
  only, ~q^{E} tuples) or sample 10^7 lifts; compute the order-2 polygon and
  order-2 residual type by one hand-rolled OM step (φ = the Hensel lift of
  the double root's quadratic); tabulate the refined census at p ∈ {3, 5, 7};
  fit one polynomial of degree ≤ the OL-A slot ledger and cross-check
  ℕ-valuedness. CONFIRMS: single-polynomial fit across p; REFUTES OL-C: any
  congruence dependence. (Cross-validate stratum decidability with cypari2
  `factorpadic` on lifted representatives, as in
  `verification/quartic_oracle.py`.)
* T7 — pack-level regression once the general-n pack lands in Lean: for the
  built countT/countS at each row, verify (H_T) and (H_S) numerically at
  q₀ ∈ {2,3,4,5,7,8,9,11} before attempting the Lean instance proof — the
  n = 2 padding failure (countS = 1 vs census 0) is the class of bug this
  catches at zero cost.

