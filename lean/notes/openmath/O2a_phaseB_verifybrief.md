# O2a — verification brief (self-contained; for a fresh-context hostile verifier)

You are verifying a mathematics note. Quote each offending passage and classify
it as *critical error* (breaks the logical chain) or *justification gap* (assume
and continue); fix nothing. The note claims THREE deliverables, each to be
verified separately:

1. **A carrier design**: two discrete carriers and a map Θ between them (a
   "dictionary" between an abstract factorization-engine's read records and the
   types of Guàrdia–Montes–Nart's higher-order Newton polygon theory), with
   declared equalities — verify internal coherence and that no clause smuggles
   choices or undefined objects.
2. **Theorem 1** (order ≤ 1): the dictionary's four clauses PROVED for
   histories of length ≤ 1, with complete proofs from the cited literature.
3. **Theorem 2** (all orders): well-posedness, invariant matching, order
   placement, and the index charge PROVED conditional on a consistency
   predicate and on three EXACTLY-STATED open lemmas (OL-1/OL-2/OL-3 below) —
   verify that the conditional proofs are complete and that the open lemmas are
   genuinely the only unproved inputs (no hidden gaps).

The note does NOT claim: any correspondence of computation traces/trees, any
invariance under Okutsu equivalence of representatives, any statement about
which histories a concrete algorithm actually produces (beyond the definitional
first-level identification inside Theorem 1), or any measure-theoretic
statement. If a passage appears to need such a claim, that is a finding.

## 1. Literature background (single source; transcriptions to verify)

Source: J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in
algebraic number theory*, Trans. Amer. Math. Soc. 364 (2012), no. 1, 361–416;
numbering below from arXiv:0807.2620v2 (the note carries the standing caveat
that printed-TAMS numbering must be confirmed before external use). Throughout:
K is a finite extension of ℚ_p, O its integer ring, v the valuation with
v(K*) = ℤ, F = F_q the residue field, π a uniformizer. For a polynomial
b ∈ O[x], v(b) := min over coefficients of v.

**(L1) Types (GMN §1–2.1).** A type of order 0 is a monic irreducible
ψ₀ ∈ F[y]. A type of order r ≥ 1 is a tuple
t = (φ₁(x); λ₁, φ₂(x); ⋯; λ_{r−1}, φ_r(x); λ_r, ψ_r(y)) where φ₁ is a monic
lift of ψ₀; λ_i = −h_i/e_i with e_i, h_i coprime positive integers; the residue
tower is F₀ = F, F_{i+1} = F_i[y]/(ψ_i) with f_i := deg ψ_i, so
[F_{i+1} : F] = f₀f₁⋯f_i; ψ_i ∈ F_i[y] is monic irreducible, ψ_i ≠ y for
i ≥ 1; each φ_{i+1} is a *representative* of the order-i truncation (below).
Degrees: m₁ := deg φ₁ = f₀ and m_{i+1} := m_i·e_i·f_i.

**(L2) Order-r valuation (Def 2.5, Prop 2.6).** v_r(P) := e_{r−1}·H_{r−1}
(S_{r−1}(P)) defines a discrete valuation on K(x)* extending v with index
e₁⋯e_{r−1}; v_r(a) = e_{r−1}·v_{r−1}(a) for a ∈ K. v₁ = v on coefficients
(order 1: the Gauss valuation v(b) on development coefficients).

**(L3) Order-r polygon and residual (Defs 2.3, 2.19–2.21).** For P of type t
(order r−1) with representative φ_r, the polygon N_r(P) is the lower Newton
polygon of the φ_r-adic development P = Σ b_j φ_r^j under v_r (points
(j, v_r(b_j φ_r^j))); N_r^− is its principal (negative-slope) part. A side S of
slope −h_r/e_r (lowest terms) has degree d = d(S), length E = e_r·d, height
H = h_r·d. The residual polynomial R_{λ_r}(P) ∈ F_r[y] has degree d, is defined
up to a nonzero constant of F_r ("∼"), and is never divisible by y.
ω_{i+1}(P) := ord_{ψ_i}(R_i(P)). The largest-degree factor of P of type t,
written f_t, satisfies deg f_t = m_r·ω_r(P) (Def 2.3). At order 1 the residual
coefficients are, explicitly: for the integer points (s + je, u_s − jh) of a
side S with initial point (s, u_s), c_j := the class of b_{s+je}/π^{u_s−jh} in
F₁ = F[y]/(ψ₀) when the point lies ON the polygon, and 0 when it lies strictly
above; R_λ(f)(y) = Σ_j c_j y^j. (No twist factors occur at order 1; the
z-power normalizations of Def 2.20 enter at orders ≥ 2 only.)

**(L4) Representatives (Thm 2.11, Def 2.12).** A representative of a type t of
order r−1 is a monic φ_r ∈ O[x] of type t with R_{r−1}(φ_r) ∼ ψ_{r−1}. Theorem
2.11 effectively constructs one satisfying eq. (16): deg φ_r = m_r,
ω_r(φ_r) = 1, v_r(φ_r) = e_{r−1}f_{r−1}·v_r(φ_{r−1}); and (Prop 2.7, as used in
the proof of Prop 2.15) v_r(φ_{r−1}) = h_{r−1} + e_{r−1}·v_{r−1}(φ_{r−1}).

**(L5) The universally-fixed-family Convention (GMN §4.1).** For the index
theory, GMN fix once and for all: a monic lift φ₁ of EVERY monic irreducible
ψ₀ ∈ F[y]; recursively, one representative φ_{i+1} of every type built from
previously chosen polynomials; all types use only chosen polynomials. Quote:
"Once these choices are made, the set t_r(P) is uniquely determined by r and
P(x)."

**(L6) Order-1 dissection theorems (Thm 1.15, Thm 1.19, Cor 1.20).** For f
monic with ω := ord_{ψ₀}(f̄) ≥ 1 and φ = φ₁: the factor f_φ of f with
reduction ψ₀^ω splits along the sides of N_φ^−(f) (Thm 1.15: per side S_i a
monic factor F_i with N_φ(F_i) = S_i one-sided and R_{λ_i}(F_i) ∼ R_{λ_i}(f);
consequently F̄_i = ψ₀^{E_i} and deg F_i = m₁·E_i); each side factor splits
along the distinct irreducible factors of its residual (Thm 1.19: R_λ(f) ∼
∏ ψ_i^{a_i} gives F_S = ∏ G_i with R_λ(G_i) ∼ ψ_i^{a_i}, so G_i has one-sided
polygon of slope λ, residual degree a_i·deg ψ_i, length e·a_i·deg ψ_i, and
deg G_i = m₁·e·a_i·deg ψ_i). Cor 1.20: for a root θ of G_i, L = K(θ): f(L/K)
is divisible by f₀·deg ψ_i, the number of irreducible factors of G_i is ≤ a_i,
and if a_i = 1 then G_i is IRREDUCIBLE with e(L/K) = e, f(L/K) = f₀·deg ψ_i.

**(L7) Order-r dissections and completeness (Thm 3.1/3.7, Def 3.9/3.10, Cor
3.8).** Order-r analogues of (L6). A type t of order r is f-complete iff
ω_{r+1}(f) = 1 w.r.t. t; then f_t is irreducible. Def 3.10: the type tree
t_r(f) consists of the order-r types sprouted from NON-complete t ∈ t_{r−1}(f)
by choosing a finite slope λ_r of N_r^−(f) and a monic irreducible
ψ_r | R_{λ_r}(f). Cor 3.8: a multiplicity-1 choice (a_i = 1) certifies an
irreducible factor with e = e₁⋯e_r and f = f₀f₁⋯f_r.

**(L8) Index vocabulary (Defs 4.11/4.12/4.15, Remarks 4.13/4.14).**
ind(f) := Σ_i ind(F_i) + Σ_{i<j} v(Res(F_i, F_j)) over the monic irreducible
factorization of f in O[x], where q^{ind(F)} = (O_L : O[θ]). For a side S of
negative finite slope: ind(S) := ½(EH − E − H + d); for a principal polygon,
ind(N) := Σ ind(S_i) + Σ_{i<j} E_i H_j, plus E_∞·H_fin if there is a slope-−∞
side; Remark 4.14: ind(N) counts the lattice points strictly inside a region
(below/on the finite part of N, strictly above its last-point horizontal,
strictly beyond its initial vertical), so ind(N) ≥ 0 and every summand of Def
4.12 is ≥ 0, whence ind(N) ≥ ind(S) for each side. Def 4.15: for a type t of
order r−1 (over the fixed family), ind_t(P) := f₀f₁⋯f_{r−1}·ind(N_r^−(P)), and
ind_r(P) := Σ_{t ∈ t_{r−1}(P)} ind_t(P); GMN warn that ind_t depends on the
choice of representative (the note's design pins the choice, see DES-3).

**(L9) Theorem of the index (Thm 4.18(1)).** For f monic separable and r ≥ 1:
ind(f) ≥ ind₁(f) + ⋯ + ind_r(f). Consequence used, "(†)": for every finite set
R of orders, Σ_{r∈R} ind_r(f) ≤ ind(f) (each ind_r ≥ 0 by (L8)).

## 2. The two carriers, the map Θ, and the consistency predicate

Fix a degree bound n and the residue field F_q.

**(C1) The domain 𝔈 (dressed histories).** An element is
𝐇 = (ρ₀; ν₁, …, ν_k), k ≥ 0, where ρ₀ = (ψ̂₀, a₀) with ψ̂₀ ∈ F_q[y] monic
irreducible (write f₀ := deg ψ̂₀) and a₀ ≥ 1; and each node is
ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i) with e_i, h_i coprime ≥ 1,
ℓ_i ≥ 1, sel_i ∈ {⊥} ∪ {(g_i, μ_i) : g_i ≥ 1, μ_i ≥ 1, μ_i g_i ≤ ℓ_i},
inc_i ∈ {0, 1}, DRESSED (when sel_i ≠ ⊥) with a monic irreducible
ψ̂_i ∈ F_i[z] of degree g_i, ψ̂_i ≠ z, over the CONSTRUCTED tower
F₁ := F_q[y]/(ψ̂₀), F_{i+1} := F_i[z]/(ψ̂_i). Well-formedness laws:
* W1 (row laws): if sel_i ≠ ⊥ and ℓ_i = 1 and e_i ≥ 2 then inc_i = 1; if
  sel_i ≠ ⊥ and ℓ_i = 1 and e_i = 1 then inc_i = 0.
* W2 (increment law): if sel_i ≠ ⊥ then inc_i = 1 ⇔ e_i·g_i ≥ 2.
* W3 (interior non-completeness): μ_i ≥ 2 for all i < k; and a₀ ≥ 2 if k ≥ 1.
* W4: the dressing as displayed (monic irreducible, degree g_i, ≠ z).
* W5: sel_i ≠ ⊥ for all i < k (only the last node may be terminal).
Rows: T1 (ℓ ≥ 2), T2 (ℓ = 1, e ≥ 2, h ≥ 2), T3 (ℓ = 1, e ≥ 2, h = 1),
T4 (ℓ = 1, e = 1), all with sel ≠ ⊥; T5 = terminal. A continuing node is
CERTIFIED iff it is T1 with inc = 1, or T2; dCert(𝐇) := #certified nodes.
**Equality on 𝔈** := literal componentwise equality (all constituents live in
explicitly constructed countable sets; the F_i are explicit iterated quotients,
not isomorphism classes). Prefixes of well-formed histories ending at a
continuing node are well-formed.

**(C2) The codomain 𝔗 (type chains over a pinned family).** Fix, once and for
all, a function Lift: Lift₀(ψ̂₀) := the coefficientwise canonical lift of ψ̂₀
to O[y] (each residue class to its distinguished representative); for i ≥ 1,
Lift_i(c) := a fixed explicit construction assigning to each length-i chain
datum c (defined next) a monic polynomial of degree m_{i+1} — the note pins
this to the project engine's "standard lift" construction; for this brief it is
an ARBITRARY BUT FIXED function of c, and everything proved here uses only its
functionality plus, at levels ≥ 1, the open lemma OL-1. 𝔗 consists of the GMN
type chains t^{(0)} ≺ t^{(1)} ≺ ⋯ ≺ t^{(r)} in which every representative is
the Lift of its own chain datum: φ_{j+1} := Lift_j(ψ̂₀; (λ_1, ψ̂_1), …,
(λ_j, ψ̂_j)). Thus an element of 𝔗 IS its discrete datum
(ψ̂₀; (λ_i, ψ̂_i)_{i≤r}). **Equality on 𝔗** := equality of these discrete data.
The family F_rep := image of Lift has, by construction, the exact shape of
(L5)'s Convention (one lift per ψ₀, one representative per chain, universally
fixed because Lift is a function). NO quotient by equivalence of
representatives is taken.

**(C3) The dictionary Θ.** For 𝐇 with continuing nodes ν₁, …, ν_{k'}:
Θ(𝐇) := the chain with ψ₀ := ψ̂₀ and, for 1 ≤ i ≤ k', λ_i := −h_i/e_i,
ψ_i := ψ̂_i (representatives via Lift as in (C2)). The PLACEMENT of node ν_i is
the GMN order i (identity on indices). Note the design point: every continuing
node — including "recentering" nodes with e_i·g_i = 1 — extends the chain by
one order; GMN's strict tuples accommodate order steps with e_i = f_i = 1, so
injectivity of the placement is by construction, and only the CHARGE (§4)
distinguishes certified nodes.

**(C4) The consistency predicate.** For f ∈ O[x] monic with disc f ≠ 0 and
𝐇 ∈ 𝔈: Cons_f(𝐇) iff
(c0) ord_{ψ̂₀}(f̄) = a₀;
(c1) for each 1 ≤ i ≤ k' (inductively, granting that t^{(i−1)} is a valid type
  over F_rep — Theorem 2(A) establishes this): N_i^−(f), computed w.r.t.
  t^{(i−1)} and φ_i = Lift_{i−1}(⋯), has a side S_i of slope −h_i/e_i with
  d(S_i) = ℓ_i; and (positional clause) (s_i, u_i) equal the initial point of
  S_i read in the declared frame — at i = 1 the frame is (L2)-(L3) itself; at
  i ≥ 2 the frame tie is exactly open lemma OL-2; the positional clause is
  consumed ONLY by the injectivity statement;
(c2) ord_{ψ̂_i}(R_{λ_i}(f)) = μ_i.
All clauses are GMN-defined data of f over the pinned family — no algorithm,
no run, no realization semantics.

## 3. Theorem 1 (order ≤ 1) — statement and complete proof

**Theorem 1.** Let f ∈ O[x] be monic of degree ≤ n with disc f ≠ 0, and let
𝐇 = (ρ₀) or (ρ₀; ν₁) be well-formed with Cons_f(𝐇). Then:
(D0) Θ is total and truncation-compatible on 𝔈, and 𝐇 is recoverable from
  (f, Θ(𝐇)) — i.e. Θ is injective on {Cons_f = true, length ≤ 1};
(D1) [invariant matching] Θ(𝐇) is a genuine type of order ≤ 1 over F_rep with
  f₁ = g₁, [F₂ : F_q] = f₀f₁, m₂ = e₁·(f₀g₁) = accE·accF where accE := e₁,
  accF := f₀g₁; v₂(φ₁) = h₁; and the SATURATION law: the tracked cluster
  factor G (defined in the proof) has deg G = m₂·μ₁, so accE·accF = deg G ⇔
  μ₁ = 1, and when μ₁ = 1, G is irreducible with (e, f) = (accE, accF);
(D2) [placement] the identity placement lands in the type tree: t^{(0)} ∈
  t₀(f), non-complete when ν₁ exists, and Θ(𝐇) ∈ t₁(f) when ν₁ is continuing;
(D3) [order-1 crossing] the first-read data format defined by the displayed
  development/hull/residual formulas below IS (L3)'s order-1 data — so a
  first read performed by those formulas satisfies (c1)/(c2) automatically;
(D4) [admissibility, level 0] F_rep's level-0 layer is admissible: Lift₀(ψ̂₀)
  is a monic lift of ψ̂₀, one per ψ̂₀ — exactly (L5)'s first layer;
and the charge: dCert(𝐇) ≤ ind₁(f) ≤ ind(f).

*Proof.* Write ψ₀ = ψ̂₀, φ₁ = Lift₀(ψ₀), a = a₀.

(D4): Lift₀(ψ₀) is monic (lift of a monic polynomial coefficientwise, top
coefficient 1) and reduces to ψ₀; (L5)'s first layer demands exactly a monic
lift of every ψ₀, chosen once — Lift₀ is a function, so the choice is
universal. No other property of an order-0 representative is required by (L1).

(D3): The order-1 objects of (L2)/(L3) are: the φ₁-adic development
f = Σ_j b_j φ₁^j (deg b_j < f₀, unique by monic division), the polygon = lower
hull of {(j, v(b_j))} (v₁ = v, and v₁(b_jφ₁^j) = v(b_j) + j·0 since
v(φ₁) = 0), the principal part on abscissas [0, ω] with ω = ord_{ψ₀}(f̄) = a
(the ψ₀-adic development of f̄ is the reduction of the φ₁-adic development of
f, and ψ₀^a ∥ f̄ forces v(b_j) ≥ 1 for j < a and v(b_a) = 0), the side data
(e, h, ℓ) with E = eℓ, H = hℓ, d = ℓ, and the residual coefficients c_j as
displayed in (L3) (unit-part classes in F₁; no twist at order 1). A "first
read" that computes exactly these objects and selects a monic irreducible
factor ψ̂₁ of R_{λ₁}(f) with its multiplicity μ₁ therefore produces literally
the (c0)/(c1)/(c2) data. (This clause is definitional-by-inspection; the
verifier should confirm that each displayed formula matches (L2)/(L3) and that
the ∼-ambiguity of R does not affect factor selection: a global nonzero scalar
changes neither the irreducible factors nor their multiplicities.)

(D1): By W4 and Cons_f, ψ̂₁ ∈ F₁[z] is monic irreducible ≠ z (under Cons_f
this is automatic: R_λ(f) is never divisible by y, (L3)); λ₁ = −h₁/e₁ with
e₁, h₁ coprime positive (W-laws); so Θ(𝐇) = (φ₁; λ₁, ψ̂₁) is a type of order 1
over F_rep per (L1), with f₁ = deg ψ̂₁ = g₁, F₂ = F₁[z]/(ψ̂₁),
[F₂ : F_q] = f₀f₁, m₂ = m₁e₁f₁ = f₀e₁g₁. v₂(φ₁) = h₁ + e₁·v₁(φ₁) = h₁ (L4
with v₁(φ₁) = v(φ₁) = 0, φ₁ monic). Saturation: by (L6), the side S = S₁
carries the monic factor F_S, and the choice ψ̂₁ with R_{λ₁}(f) ∼ ∏ ψ_i^{a_i}
carves out G := G_{ψ̂₁} with one-sided polygon of slope λ₁, residual
∼ ψ̂₁^{μ₁}, and deg G = m₁·e₁·μ₁·f₁ = m₂·μ₁. Hence deg G = accE·accF = m₂ iff
μ₁ = 1; and if μ₁ = 1, Cor 1.20 gives G irreducible with e(L/K) = e₁ = accE
and f(L/K) = f₀f₁ = accF. [The verifier should check the degree bookkeeping
deg G = m₁·e·a·f against (L6)'s transcription.]

(D2): t^{(0)} = ψ₀ ∈ t₀(f) means ω₁(f) = ord_{ψ₀}(f̄) ≥ 1: that is (c0) with
a₀ ≥ 1. If ν₁ exists, W3 gives a₀ ≥ 2, i.e. ω₁(f) ≥ 2: t^{(0)} is
non-complete, so Def 3.10 sprouts order-1 types from it; (c1) says λ₁ is a
finite slope of N₁^−(f) and (c2) says ψ̂₁ | R_{λ₁}(f) with multiplicity
μ₁ ≥ 1 — Def 3.10 membership verbatim: Θ(𝐇) ∈ t₁(f).

(Charge): Suppose ν₁ is certified: T1 with e₁g₁ ≥ 2, or T2 (W1/W2). Its side S
is T1 (ℓ ≥ 2) or T2 (ℓ = 1, e, h ≥ 2). Claim ind(S) ≥ 1: by Remark 4.14,
2·ind(S) = EH − E − H + d counts (twice) the lattice points of the displayed
region; exhibit one point. T1: the on-side integer point (s + e, u_s − h)
(abscissa > s; ordinate exceeds the last-point ordinate u_s − hℓ by
h(ℓ−1) > 0 since ℓ ≥ 2; on the side ⇒ in the region). T2: the point
(s + 1, u_s − h + 1) = (s+1, u_end + 1) lies in the region iff
h·1 + e·1 ≤ eh ⇔ (e−1)(h−1) ≥ 1, true at e, h ≥ 2. [Algebra cross-check:
2·ind(S) = ℓ(ehℓ + 1 − e − h); at T1 with e = h = 1 this is ℓ(ℓ−1) ≥ 2.]
Then: ind(N₁^−(f)) ≥ ind(S) ≥ 1 ((L8): all summands ≥ 0);
ind_{t^{(0)}}(f) = f₀·ind(N₁^−(f)) ≥ 1 (Def 4.15, r = 1, twist f₀ ≥ 1);
ind₁(f) = Σ_{t ∈ t₀(f)} ind_t(f) ≥ ind_{t^{(0)}}(f) (t^{(0)} ∈ t₀(f) by (D2),
all terms ≥ 0); and ind₁(f) ≤ ind(f) (L9, r = 1). dCert ≤ 1 closes the bound;
dCert = 0 is trivial.

(D0): Totality/truncation are structural. Injectivity: from Θ(𝐇) read off
(ψ̂₀, e₁, h₁, ψ̂₁), hence g₁; Cons_f then pins a₀ = ord_{ψ̂₀}(f̄); the polygon
N₁^−(f) has at most one side per slope, so (c1) pins (s₁, u₁, ℓ₁); (c2) pins
μ₁; W2 pins inc₁. ∎

## 4. The three open lemmas (exact statements; NOT proved anywhere in the note)

These quantify over the fixed lift function Lift_i of (C2) at levels i ≥ 1 and
over the abstract "stage flow" whose level-1 instance was pinned in (D3). The
stage flow at level i + 1 ≥ 2 is specified by: a stage key Φ̂_{i+1} =
Lift_i(c); a stage valuation u_{i+1} on O[x] with value lattice
(1/(e₁⋯e_i))ℤ; a stage window polygon = lower hull of
(j, u_{i+1}(B_j) + j·w_{i+1}(Φ̂_{i+1})) over the Φ̂_{i+1}-adic development
f = Σ_j B_j Φ̂_{i+1}^j, written in integer slot coordinates (denominators
cleared); a stage residual computed from digit data and normalized by a
distinguished "anchor" unit into an F_{i+1}-polynomial. (A verifier without
access to the underlying engine text should treat these as an interface: the
lemmas state exactly the properties consumed by Theorem 2.)

**OL-1 (lift admissibility + normalization). OPEN.** For every well-formed
chain datum c of order i ≥ 1, with t = its type over F_rep: (a) Lift_i(c) is
monic in O[x] of degree m_{i+1} = m_i e_i f_i; (b) Lift_i(c) is of type t with
R_i(Lift_i(c)) ∼ ψ̂_i — i.e., a Def-2.12 representative of t; (c)
v_{i+1}(Lift_i(c)) = e_i f_i·v_{i+1}(Lift_{i−1}(c′)) (c′ the parent datum),
equivalently V_{i+1} = e_i f_i(e_i V_i + h_i) with V_i := v_i(Lift_{i−1}(c′)).
[GMN Thm 2.11 proves EXISTENCE of a representative with (a)–(c); the open
content is that the pinned Lift_i satisfies the same.]

**OL-2 (frame crossing, orders ≥ 2). OPEN.** For f monic separable and c a
Cons_f-consistent chain of order i ≥ 1 (well-defined given OL-1): the stage
window polygon of f at level i + 1 equals N_{i+1}^−(f) (as computed by
(L2)/(L3) over F_rep) up to the recorded translation, side-for-side, with
equal lowest-terms (e, h), equal degree ℓ, and equal T1–T4 classification.
Load-bearing sub-claim: u_{i+1} = v_{i+1}/(e₁⋯e_i) on development
coefficients, so the two frames differ by exactly the scaling that the integer
slot coordinates clear.

**OL-3 (residual identification, orders ≥ 2). OPEN.** Same setting: the
anchor-normalized stage residual of f at the read side equals R_{λ_{i+1}}(f)
(Def 2.21 over F_rep) up to a nonzero constant of F_{i+1} — hence equal
irreducible factor multisets with equal multiplicities — the towers F_{i+1}
being identical on both sides by construction (C1)/(C2).

## 5. Theorem 2 (all orders) — statement and complete conditional proof

**Theorem 2.** Let f ∈ O[x] be monic of degree ≤ n, disc f ≠ 0, 𝐇 ∈ 𝔈 with
continuing nodes ν₁ … ν_{k'}. Then:

(A) [unconditional at order ≤ 1; given OL-1 for well-definedness at orders ≥ 2]
If Cons_f(𝐇), then t^{(i)} ∈ t_i(f) for 0 ≤ i ≤ k', with t^{(i)} non-complete
for i < k'; the identity placement is injective; and 𝐇 is recoverable from
(f, Θ(𝐇)) given the frame tie of (c1)'s positional clause (unconditional at
order ≤ 1; via OL-2 at orders ≥ 2).

(B) [Cons_f + OL-1] Invariant matching at all levels: e_i, h_i, f_i = g_i as
constructed; [F_{i+1} : F_q] = f₀⋯f_i; deg Φ̂_{i+1} = m_{i+1} =
accE_i·accF_i where accE_i := e₁⋯e_i, accF_i := f₀g₁⋯g_i; the V-recursion
V_{i+1} = e_i f_i(e_i V_i + h_i). Saturation at the last read: the cluster
factor f_{t^{(k')}} has degree m_{k'+1}·μ_{k'}, so accE·accF = deg f_{t^{(k')}}
⇔ μ_{k'} = 1; and if μ_{k'} = 1 then f_{t^{(k')}} is irreducible with
(e, f) = (accE_{k'}, accF_{k'}).

(C) [Cons_f + OL-1] The charge: every certified node ν_i has
ind_{t^{(i−1)}}(f) ≥ 1; distinct certified nodes charge distinct orders; and
dCert(𝐇) ≤ Σ_{r=1}^{k'} ind_r(f) ≤ ind(f).

(D) [OL-1 + OL-2 + OL-3] Every history emitted by the stage flow on f (first
read per (D3); level-(i+1) reads per §4's interface) is, after dressing by the
anchor normalization, a Cons_f history — so (B)/(C) apply to such histories.

*Proof.* (A) Induction on i. Base: (c0) gives ω₁(f) = a₀ ≥ 1, so
t^{(0)} ∈ t₀(f); if k' ≥ 1, W3 forces a₀ ≥ 2 = non-completeness. Step: given
t^{(i−1)} ∈ t_{i−1}(f) non-complete, (c1) provides the finite slope λ_i of
N_i^−(f) and (c2) the monic irreducible ψ̂_i | R_{λ_i}(f); Def 3.10 membership
verbatim: t^{(i)} ∈ t_i(f). Interior non-completeness: ω_{i+1}(f) = μ_i ≥ 2
for i < k' (W3). Injectivity: levelwise as in Theorem 1 (D0): the chain datum
pins (e_i, h_i, ψ̂_i, g_i); a polygon has at most one side per slope, so f
pins (ℓ_i, s_i, u_i) through (c1) (positional clause in the declared frame);
(c2) pins μ_i; W2 pins inc_i; (c0) pins a₀. Placement: identity on indices of
a finite list — injective.

(B) The levelwise identifications are Θ's construction plus W4. Tower and
m-recursion: (L1) arithmetic, with deg Φ̂_{i+1} = m_{i+1} from OL-1(a).
V-recursion: OL-1(c) + (L4)'s Prop-2.7 identity. Saturation: t^{(k')} ∈
t_{k'}(f) by (A); ω_{k'+1}(f) = ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) = μ_{k'} by (c2);
Def 2.3 gives deg f_{t^{(k')}} = m_{k'+1}·ω_{k'+1}(f) = (accE·accF)·μ_{k'}
(using m_{k'+1} = accE_{k'}·accF_{k'} from the m-recursion and m₁ = f₀).
Hence the biconditional. At μ_{k'} = 1: Def 3.9 completeness + Cor 3.8 give
irreducibility and (e, f) = (e₁⋯e_{k'}, f₀⋯f_{k'}) = (accE, accF).

(C) A certified ν_i is T1 with e_ig_i ≥ 2 or T2 (W1/W2). By (c1), N_i^−(f)
has the side S_i with the engine data (e_i, h_i, ℓ_i); S_i is then a T1 or T2
side, and ind(S_i) ≥ 1 by the two lattice witnesses in Theorem 1's charge
step — pure Def-4.12 arithmetic, order-agnostic. Then ind(N_i^−(f)) ≥
ind(S_i) ≥ 1 by (L8) nonnegativity; ind_{t^{(i−1)}}(f) =
f₀⋯f_{i−1}·ind(N_i^−(f)) ≥ 1 (Def 4.15 at r = i; the twist is a product of
positive integers); ind_i(f) ≥ ind_{t^{(i−1)}}(f) since t^{(i−1)} ∈ t_{i−1}(f)
by (A) and Def 4.15's sum has nonnegative terms. Distinct certified nodes
occupy distinct orders (placement is the identity), so
dCert(𝐇) = #{certified i} ≤ Σ_{certified i} ind_i(f) ≤ Σ_{r=1}^{k'} ind_r(f)
≤ ind(f), the last inequality being (L9) at r = k'.

(D) Induction along the history. Level 1: (D3) is unconditional. Level
i + 1 ≥ 2: OL-2 says the read side data (e, h, ℓ) are the (c1) data of
N_{i+1}^−(f); OL-3 says the selected factor and multiplicity are the (c2)
data; OL-1 keeps the level-(i+2) GMN objects defined over F_rep. ∎

**Scope remarks the verifier should enforce.** (1) Nothing above claims that
the stage flow's emitted histories are exactly the GMN tree of f, nor that
every GMN type of f is realized — those are trace/realization statements,
explicitly out of scope. (2) The consumption of (L9) is the ONLY appeal to the
theorem of the index, and it is used exactly in the finite-sum form (†).
(3) The W2/W3 laws are laws OF THE CARRIER; whether a concrete engine's
records satisfy them is out of scope here. (4) The ∼-ambiguity of residuals
never matters: only factor multisets and multiplicities are consumed.

## 6. Corroborating computation (exact arithmetic; NOT part of the proofs)

Executed falsifiers (PARI/GP; all exact; a failure of any would have refuted
the labeled claim):

* **F1 (Theorem 1's (D1)/(D3)).** 3600 monic f ∈ ℤ[x] read at p ∈ {2, 3, 5},
  n ∈ {2..6} (half plain random, half with a forced repeated residue factor
  ψ₀^a·rest + p·noise; seed fixed). For each repeated residue factor: canonical
  lift, φ-adic development, lower hull, per-side (e, h, ℓ), residual over
  F_{p^{f₀}} by the (L3) unit-part formula, factorization. For the 3432 f whose
  every residual factor had multiplicity 1 ("order-1 decided"): the predicted
  (e, f)-multiset — (1, f₀) per simple residue factor (Hensel), (e, f₀·deg ψ)
  per multiplicity-1 residual factor (Cor 1.20) — was compared against ground
  truth from prime decomposition in the number fields of the ℚ-irreducible
  factors (orders maximal at p). Result: 0 mismatches, 0 degree-checksum
  failures.
* **F2 ((L9) at r = 1, first execution in this project).** For all 3600
  samples: ind₁(f) = Σ_{ψ₀ repeated} f₀·ind(N₁^−) (Def 4.12 with cross terms)
  versus ind_p(f) computed by the étale-algebra formula ind_p(f) =
  Σ_i (v_p(disc g_i) − v_p(disc K_i))/2 + Σ_{i<j} v_p(Res(g_i, g_j)) over the
  ℚ-irreducible factors. Result: 0 violations of ind₁ ≤ ind_p.
* **F3 (order-2 instances of Theorem 2(B)).** Family A: f = (x²−p)² −
  p^{2k+1}x, p ∈ {2,3,5}, k ∈ {1,2,3}: predicted chain (e₁, f₁) = (2, 1) →
  (e₂, f₂) = (2, 1), saturated; predicted (e, f) = (4, 1): confirmed 9/9.
  Family B (wild, residue-extended): p = 2, φ₁ = x² + x + 1,
  f = (φ₁² − 2x)² − 2^{2k+1}φ₁, k ∈ {1,2,3}: hand-derived chain — order-1 side
  (0,2)–(4,0), (e,h,ℓ) = (2,1,2), residual z² + (w̄+1) = (z + w̄)² over F₄
  (w̄² = w̄+1), selection (g, μ) = (1, 2); representative φ₂ = φ₁² − 2x (own
  polygon (0,1)–(2,0), residual z + w̄, deg 4 = m₂, v₂(φ₂) = 2 = e₁f₁v₂(φ₁));
  order-2 points (0, 4k+3), (2, 4), side (e₂,h₂,ℓ₂) = (2, 4k−1, 1), saturated.
  Predicted (e, f) = (accE, accF) = (4, 2): confirmed 3/3. Sharper: measured
  ind_2(f) = 6, 10, 14 = 4k + 2 = f₀·ind(N₁^−) + f₀f₁·ind(N₂^−) =
  2·2 + 2·(2k−1) EXACTLY — pinning Def 4.15's twist factor numerically (without
  the twist the prediction would be 2k + 1) and, via Thm 4.18(2), consistent
  with termination at order 2. Also dCert = 2 ≤ ind throughout.
* **F4 (the ind(S) table).** All 1548 configurations (coprime e, h ≤ 8,
  ℓ ≤ 6, offset grid): brute lattice count = ½(EH − E − H + d), and
  count ≥ 1 exactly on T1/T2 shapes: 0 violations.

## 7. Verification checklist (where to press hardest)

1. **Transcriptions (L1)–(L9)** against the paper (arXiv:0807.2620v2): esp.
   eq. (16) + the Prop 2.7 identity; Def 4.15's twist product f₀⋯f_{r−1} and
   its INDEXING at r = i in Theorem 2(C); Def 3.10's sprouting-from-non-complete;
   the order-1 residual coefficient formula (no twist at order 1); Remark
   4.14's region and its consequences (every Def-4.12 summand ≥ 0).
2. **The degree bookkeeping** deg G = m₁·e·a·f in Theorem 1 (D1) — does (L6)
   as transcribed genuinely yield it, including F̄_i = ψ₀^{E_i}?
3. **The two lattice witnesses** in the charge step (T1: on-side point;
   T2: (s+1, u_end+1)) — check region membership conventions against (L8).
4. **W3 vs Def 3.10**: the note maps interior nodes to sprouting steps; verify
   no clause needs sprouting FROM a complete type (the μ = 1 ⇒ last-node
   discipline), including the T4 corner (ℓ = 1, e = 1 forces μ = g = 1: check
   such a node can only be last, by W3).
5. **Placement design**: the identity placement presupposes that EVERY
   continuing node opens a GMN order — verify (L1) tuples admit consecutive
   orders with e_i = f_i = 1 (same-degree steps) and that nothing in §1 forbids
   them (GMN "optimality" of types is NOT assumed in this paper's §1–4).
6. **Independence of clauses from the open lemmas**: confirm each use of OL-1
   (well-definedness of order-≥2 objects over F_rep; deg; V-recursion), OL-2
   ((c1) at orders ≥ 2 + positional/injectivity tie), OL-3 ((c2) at orders
   ≥ 2) is flagged, and that no OTHER unproved step hides in Theorem 2.
7. **The (†) consumption**: only (L9), only in finite-sum form.
8. **Carrier coherence**: DES-equalities are literal on constructed objects;
   no isomorphism-class or choice-dependent object appears in either carrier;
   the codomain's identification "element = discrete datum" is forced by
   Lift's functionality.

Charge: quote-and-classify only; critical error vs justification gap; check
steps downstream of a gap by assuming the gap's conclusion. The three OL's are
DECLARED open — they are not findings; an UNDECLARED dependence is.
