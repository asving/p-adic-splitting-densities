# O2a — verification brief REV 2 (self-contained; for a fresh-context hostile verifier)

You are verifying a mathematics note. Quote each offending passage and classify
it as *critical error* (breaks the logical chain) or *justification gap* (assume
and continue); fix nothing. This is REV 2, repairing the V10 hostile
verification of rev 1 (verdict UNSOUND; 9 critical errors, 3 justification
gaps). Everything V10 confirmed is carried byte-stable; every V10 finding is
repaired at a flagged location (changelog below). The FOUR open lemmas
OL-1..OL-4 of §4 are DECLARED — they are not findings; an UNDECLARED
dependence is.

The note claims THREE deliverables, each to be verified separately:

1. **A carrier design**: two discrete carriers and a map Θ between them (a
   "dictionary" between an abstract factorization-engine's read records and the
   types of Guàrdia–Montes–Nart's higher-order Newton polygon theory), with
   declared equalities — verify internal coherence and that no clause smuggles
   choices or undefined objects.
2. **Theorem 1** (order ≤ 1): the dictionary's clauses PROVED for histories of
   length ≤ 1, with complete proofs from the cited literature, on the WHOLE
   quantified domain (including the zero-continuing-node cases).
3. **Theorem 2** (all orders): well-posedness, invariant matching, order
   placement, and the index charge PROVED conditional on a consistency
   predicate and on four EXACTLY-STATED open lemmas (OL-1..OL-4 below) —
   verify that the conditional proofs are complete and that the open lemmas
   are genuinely the only unproved inputs (no hidden gaps).

The note does NOT claim: any correspondence of computation traces/trees, any
invariance under Okutsu equivalence of representatives, any statement about
which histories a concrete algorithm actually produces beyond what OL-2/OL-3/
OL-4 explicitly assert, injectivity of Θ on histories with a terminal last
node (explicitly a NON-claim, displayed in Lemma R), or any measure-theoretic
statement. If a passage appears to need such a claim, that is a finding.

## 0. Rev-2 changelog (V10 findings → repair sites)

| V10 finding | class | repair site |
|---|---|---|
| C1: no domains for s_i, u_i; 𝔈-equality undefined | critical | §2 (C1): domains ℤ_{≥0} declared; semantics pinned by (C4)'s positional clause |
| C2: Lift image not "(L5)-shaped by construction"; Θ's codomain membership needs OL-1 | critical | §2 (C2): codomain now FORMAL data 𝔗; GMN interpretation ι separated, conditional on (D4)/OL-1 |
| C3: terminal node in 𝔈-equality but discarded by Θ; contradicts recovery | critical | §2 Lemma R: injectivity RESTRICTED to all-continuing histories; terminal non-recovery displayed as a non-claim; terminal seam requirements displayed |
| C4: Theorem 1 ill-formed at 𝐇 = (ρ₀) / terminal ν₁ | critical | §3: Theorem 1 restated as a three-case split |
| C5: (D0) injectivity false for terminal ν₁ | critical | §2 Lemma R + §3 (D0°)/(D0) |
| C6: "(D0) Θ total on 𝔈" asserts codomain membership needing OL-1 | critical | §2 (C2)/(C3): totality now formal, unconditional |
| G1: principal part "[0, ω]" wrong when an initial coefficient vanishes | gap | §1 (L3+) + §3 (D3): the j₀ convention; NEW falsifier F5 (§6) covers exactly this corner |
| G2: OL-2's coordinate-clearing/translation undefined; positional tie unstated | gap | §4: interface displayed; OL-2 strengthened to exact frame claims (a)–(d), NO translation |
| C7: injectivity consumes more than OL-2 states; terminal breaks it at every order | critical | §2 (C4): positional clause now INTRINSIC at all orders; Lemma R uses no OL-2; OL-2(d) states the positional transport the emission seam needs |
| G3: OL-3's digit data/anchor undefined; not attackable | gap | §4: the F.0–F.2 stage-residual interface displayed before OL-3's claim |
| C8: Theorem 2(D)'s undeclared emission-discipline dependence (hidden by scope remark 3) | critical | §4 OL-4 DECLARED; rev-1 scope remark (3) DELETED; (D) consumes OL-2+OL-3+OL-4 |
| C9: k' = 0 in Theorem 2 (μ_{k'}, "last read" undefined) | critical | §5: saturation guarded by k' ≥ 1; k' = 0 degenerations displayed per clause |

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
(order 1: the Gauss valuation v(b) on development coefficients). On O[x]∖{0}
the values are nonnegative integers.

**(L3) Order-r polygon and residual (Defs 2.3, 2.19–2.21).** For P of type t
(order r−1) with representative φ_r, the polygon N_r(P) is the lower Newton
polygon of the φ_r-adic development P = Σ b_j φ_r^j under v_r (points
(j, v_r(b_j φ_r^j)) for b_j ≠ 0); N_r^− is its principal (negative-slope)
part. A side S of slope −h_r/e_r (lowest terms) has degree d = d(S), length
E = e_r·d, height H = h_r·d. The residual polynomial R_{λ_r}(P) ∈ F_r[y] has
degree d, is defined up to a nonzero constant of F_r ("∼"), and is never
divisible by y. ω_{i+1}(P) := ord_{ψ_i}(R_i(P)). The largest-degree factor of
P of type t, written f_t, satisfies deg f_t = m_r·ω_r(P) (Def 2.3). At order 1
the residual coefficients are, explicitly: for the integer points
(s + je, u_s − jh) of a side S with initial point (s, u_s), c_j := the class
of b_{s+je}/π^{u_s−jh} in F₁ = F[y]/(ψ₀) when the point lies ON the polygon,
and 0 when it lies strictly above; R_λ(f)(y) = Σ_j c_j y^j. (No twist factors
occur at order 1; the z-power normalizations of Def 2.20 enter at orders ≥ 2
only.)
**(L3+) [NEW in rev 2 — the slope-−∞ convention; V10-G1.]** If
ord_{φ_r}(P) = j₀ > 0 (φ_r divides P exactly j₀ times in O[x]), the points of
abscissa j < j₀ are absent and N_r^−(P) additionally carries a side of slope
−∞ of length E_∞ = j₀; the FINITE-slope part then starts at abscissa j₀.
Def 3.10's sprouting and every side/residual clause below quantify over
FINITE slopes only; the −∞ side enters only ind(N), through the E_∞·H_fin
term of (L8), with H_fin := the total height of the finite part.

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
choice of representative (the note's design pins the choice, see (C2)). Both
summands of Def 4.11 are ≥ 0 (a lattice index exponent; a resultant valuation
of integral polynomials), so ind(f) ≥ 0.

**(L9) Theorem of the index (Thm 4.18(1)).** For f monic separable and r ≥ 1:
ind(f) ≥ ind₁(f) + ⋯ + ind_r(f). Consequence used, "(†)": for every finite set
R of orders, Σ_{r∈R} ind_r(f) ≤ ind(f) (each ind_r ≥ 0 by (L8)).

## 2. The two carriers, the map Θ, the consistency predicate, and Lemma R

Fix a degree bound n and the residue field F_q.

**(C1) The domain 𝔈 (dressed histories).** An element is
𝐇 = (ρ₀; ν₁, …, ν_k), k ≥ 0, where ρ₀ = (ψ̂₀, a₀) with ψ̂₀ ∈ F_q[y] monic
irreducible (write f₀ := deg ψ̂₀) and a₀ ≥ 1; and each node is
ν_i = (e_i, h_i, ℓ_i, s_i, u_i, sel_i, inc_i) with e_i, h_i coprime ≥ 1,
ℓ_i ≥ 1, **s_i ∈ ℤ_{≥0}, u_i ∈ ℤ_{≥0}** [REV 2: domains declared — V10-C1],
sel_i ∈ {⊥} ∪ {(g_i, μ_i) : g_i ≥ 1, μ_i ≥ 1, μ_i g_i ≤ ℓ_i},
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
**Equality on 𝔈** := literal componentwise equality (all constituents now
live in explicitly declared countable sets; the F_i are explicit iterated
quotients, not isomorphism classes). Prefixes of well-formed histories ending
at a continuing node are well-formed. The intended READING of (s_i, u_i) is
imposed by (C4)'s positional clause, not by the raw carrier: the initial
point of the level-i read side in the order-i GMN integer frame
(nonnegativity is consistent with (L2): v_i ≥ 0 on O[x]∖{0}). Write
𝐇° := (ρ₀; ν₁, …, ν_{k'}) for the CONTINUING PART (k' = k, or k−1 when ν_k is
terminal).

**(C2) The codomain 𝔗 (formal chain data) and the interpretation ι.** [REV 2
— V10-C2/C6.] 𝔗 := the set of formal chain data
𝔠 = (ψ̂₀; (λ_i, ψ̂_i)_{1 ≤ i ≤ r}), r ≥ 0, with ψ̂₀ ∈ F_q[y] monic
irreducible; λ_i = −h_i/e_i, e_i, h_i coprime positive; ψ̂_i ∈ F_i[z] monic
irreducible ≠ z (any degree ≥ 1) over the constructed tower
F₁ = F_q[y]/(ψ̂₀), F_{i+1} = F_i[z]/(ψ̂_i). **Equality on 𝔗** := literal
equality of these data. Membership in 𝔗 is purely combinatorial — NO
admissibility input. Separately, fix once and for all a function Lift:
Lift₀(ψ̂₀) := the coefficientwise canonical lift of ψ̂₀ to O[y]; for i ≥ 1,
Lift_i(𝔠_{≤i}) := an ARBITRARY BUT FIXED function of the length-i datum,
valued in monic polynomials of O[x] (the note pins it to the project engine's
"standard lift"). The INTERPRETATION ι assigns to 𝔠 the GMN chain
t^{(0)} ≺ ⋯ ≺ t^{(r)} with φ_{j+1} := Lift_j(𝔠_{≤j}); ι(𝔠) is a genuine chain
of GMN types-with-representatives PROVIDED each Lift_j output is a Def-2.12
representative of its type: at level 0 this is Theorem 1 (D4) (PROVED); at
levels j ≥ 1 it is exactly OL-1 (OPEN). Every GMN-valued object below
(N_i^−(f), R_{λ_i}(f), t_i(f), ind_t) is read THROUGH ι and asserted only
where ι is granted — unconditionally at order ≤ 1, given OL-1 at orders ≥ 2.
F_rep := the image of Lift. F_rep has the FUNCTIONAL SHAPE of (L5)'s
Convention by construction (one lift per ψ̂₀, one output per chain datum,
universally fixed because Lift is a function); what (L5) additionally
requires — that the chosen polynomials are REPRESENTATIVES — is precisely
(D4) + OL-1, and is claimed only there. Under (D4) + OL-1 the Convention is
instantiated and t_r(P), ind_t(P), ind_r(P) are single-valued over F_rep.
NO quotient by equivalence of representatives is taken.

**(C3) The dictionary Θ.** Θ(𝐇) := (ψ̂₀; (−h_i/e_i, ψ̂_i)_{1 ≤ i ≤ k'}) ∈ 𝔗 —
a pure re-indexing of the discrete data of the continuing part 𝐇°. Θ is total
and truncation-compatible on ALL of 𝔈, unconditionally [REV 2: honest now
because 𝔗 is formal — V10-C6]. Θ(𝐇) = Θ(𝐇°): a terminal last node is
DISCARDED; the resulting non-injectivity is quantified exactly in Lemma R.
The PLACEMENT of node ν_i is the GMN order i (identity on indices). Design
note (unchanged): every continuing node — including "recentering" nodes with
e_i·g_i = 1 — extends the chain by one order; GMN's tuples admit consecutive
orders with e_i = f_i = 1, so injectivity of the placement is by
construction, and only the CHARGE (§5(C)) distinguishes certified nodes.

**(C4) The consistency predicate.** For f ∈ O[x] monic with disc f ≠ 0 and
𝐇 ∈ 𝔈 with continuing nodes ν₁, …, ν_{k'}: Cons_f(𝐇) iff
(c0) ord_{ψ̂₀}(f̄) = a₀;
(c1) for each 1 ≤ i ≤ k' (inductively, reading GMN objects through ι — level
  1 unconditional, levels ≥ 2 given OL-1): N_i^−(f), computed w.r.t.
  t^{(i−1)} = ι(Θ(𝐇)_{≤i−1}) and φ_i = Lift_{i−1}(⋯), has a side S_i of
  finite slope −h_i/e_i with d(S_i) = ℓ_i; AND (positional clause)
  (s_i, u_i) = the initial point of S_i in the order-i INTEGER FRAME — the
  plane of the point set {(j, v_i(b_j φ_i^j))} of the development
  f = Σ_j b_j φ_i^j. [REV 2 — V10-C7: the positional clause is now INTRINSIC
  at every order (rev 1 deferred its i ≥ 2 frame to OL-2); no engine frame
  occurs in this definition.]
(c2) ord_{ψ̂_i}(R_{λ_i}(f)) = μ_i.
All clauses are GMN-defined data of f over the pinned family — no algorithm,
no run, no realization semantics. Cons_f places NO constraint on the fields
of a terminal last node (recorded honestly; consumed by Lemma R's non-claim).

**Lemma R (recovery; the exact injectivity statement).** Let f be monic with
disc f ≠ 0. On 𝔈°_f := {𝐇 ∈ 𝔈 : Cons_f(𝐇), every node continuing}, 𝐇 is a
function of (f, Θ(𝐇)) — i.e. Θ is injective on 𝔈°_f (at orders ≥ 2 granting
OL-1 for the well-definedness of the objects read). For 𝐇 with a terminal
last node, exactly the continuing part 𝐇° is so recoverable; 𝐇 itself is NOT
recoverable, and this is a displayed NON-claim, not an omission.

*Proof.* Displayed recovery map: given (f, 𝔠), 𝔠 = Θ(𝐇), set ψ̂₀ := the
level-0 datum of 𝔠; a₀ := ord_{ψ̂₀}(f̄) ((c0)); for i = 1, …, k' (:= length
of 𝔠): (e_i, h_i) := the lowest-terms data of λ_i (from 𝔠); S_i := the
UNIQUE side of N_i^−(f) of slope λ_i (a polygon has at most one side of a
given slope; the side exists by (c1)); ℓ_i := d(S_i); (s_i, u_i) := the
initial point of S_i in the order-i integer frame ((c1)'s positional clause —
intrinsic, no engine frame); ψ̂_i := the level-i datum of 𝔠; g_i := deg ψ̂_i;
μ_i := ord_{ψ̂_i}(R_{λ_i}(f)) ((c2)); inc_i := 1 iff e_i·g_i ≥ 2 (W2). Every
field of every node of 𝐇 ∈ 𝔈°_f is reproduced. Non-recovery of a terminal
node: if ν = (e, h, ℓ, s, u, ⊥, inc) is terminal and (𝐇°; ν) is well-formed
and Cons_f, then so is (𝐇°; ν′) for ANY other well-formed terminal
ν′ — e.g. ν = (1,1,1,0,0,⊥,0) vs ν′ = (1,2,1,0,0,⊥,0) — since W1/W2/W4
constrain only sel ≠ ⊥ nodes, W3/W5 see only the position, and Cons_f
constrains no terminal field; both have image Θ(𝐇°). ∎

What FULL recovery would need (the terminal seam, deferred, NOT claimed):
(t-i) a terminal consistency clause tying (e, h, ℓ, s, u) of the terminal
node to the level-(k'+1) GMN read of f (same shape as (c1)); and (t-ii) an
extension of Θ's codomain remembering the terminal read (e.g. a final entry
(λ_{k'+1}, ⊥)). Both are design extensions owned by the O-3 realization seam
(the SEMANTICS of the engine's terminal record is engine-side). Consumer
audit: every quantity this note exports — Θ(𝐇), dCert(𝐇), the per-order
charges, the saturation leaf data — is a function of 𝐇° alone (certified
nodes are continuing by definition; §5 (B)/(C) quantify over i ≤ k'), so the
restriction to 𝔈°_f costs no clause of this note.

<!-- REV2-STAGE-2 -->
