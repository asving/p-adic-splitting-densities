# O2a — verification brief REV 5 (self-contained; for a fresh-context hostile verifier)

You are verifying a mathematics note. Quote each offending passage and classify
it as *critical error* (breaks the logical chain) or *justification gap* (assume
and continue); fix nothing. This is REV 5, repairing the V25 hostile
verification of rev 4 (Codex, fresh context: SOUND-WITH-GAPS, 0 critical,
1 gap — OL-3's declared strength exceeds Theorem 2(D)'s consumption, a
minimality defect; V25 explicitly confirmed OL-6's run/read binding at base
and step, Lemma B, the OL-5 minimal-core cut, and six-lemma joint
sufficiency); rev 4 had repaired the round-5 pair of
model-diverse hostile verifications of rev 3 (P2, fresh-context Fable:
UNSOUND, 1 critical + 3 gaps; V20, Codex: SOUND-WITH-GAPS, 2 gaps, one
coinciding with P2's third); rev 3 had repaired the V14 verification of rev 2
(UNSOUND; 1 critical, 1 gap); rev 2 had repaired the V10 verification of
rev 1 (UNSOUND; 9 critical, 3 gaps). Everything V10/V14/V20/P2/V25 confirmed is
carried byte-stable; every finding is repaired at a flagged location
(changelogs below). The SIX open lemmas OL-1..OL-6 of §4 are DECLARED — they
are not findings; an UNDECLARED dependence is.

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
   predicate and on six EXACTLY-STATED open lemmas (OL-1..OL-6 below) —
   verify that the conditional proofs are complete, that the open lemmas
   are genuinely the only unproved inputs (no hidden gaps), and that each
   theorem's hypothesis list names NO MORE than it consumes (minimality —
   V14-2's charge).

The note does NOT claim: any correspondence of computation traces/trees, any
invariance under Okutsu equivalence of representatives, any statement about
which histories a concrete algorithm actually produces beyond what OL-2/OL-3/
OL-4/OL-5/OL-6 explicitly assert, injectivity of Θ on histories with a terminal last
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

## 0′. Rev-3 changelog (V14 findings → repair sites)

V14 confirmed the whole rev-2 re-architecture (intrinsic positional recovery;
all-continuing injectivity restriction; the k' = 0 corners; OL-4's exactness
for what it states; Theorems 1 and 2(A)–(C) given the transcriptions and
OL-1) and raised exactly two findings, both at the Theorem 2(D) engine seam:

| V14 finding | class | repair site |
|---|---|---|
| 1: Theorem 2(D)'s level-1 step cites (D3), but (D3) is a CONDITIONAL ("a first read that computes exactly these objects … produces the (c0)/(c1)/(c2) data"); no OL asserts the engine's first read DOES compute the displayed formulas — OL-2/OL-3 start at orders ≥ 2, OL-4 supplies only (c0). Undeclared emission dependence at i = 1; (D) cannot establish Cons_f for emitted histories with k' ≥ 1 | critical | §4: **OL-5 DECLARED** (first-read semantics, order 1); §5: (D)'s hypothesis list and proof base re-founded on OL-5 + (D3) |
| 2: OL-2(a)–(b) (valuation tie on ALL admissible coefficients; whole-polygon identity) are materially stronger than 2(D)'s consumption — (c)–(d) suffice; advertised minimality fails | gap | §4: OL-2 consumption split — **OL-2-min** [(c′)+(d′)] displayed intrinsically and made (D)'s ONLY OL-2 hypothesis; (a)–(b) re-advertised to their actual consumer (the O-3 design's unit JC-2, which targets the full (a)–(d)) and retained as OL-2-min's intended proof route |

## 0″. Rev-4 changelog (round-5 findings → repair sites)

Round 5 verified rev 3 twice, model-diverse: V20 (Codex, fresh context;
SOUND-WITH-GAPS, 2 gaps) and P2 (Claude, fresh context, first report not
consulted; UNSOUND, 1 critical + 3 gaps). P2 confirmed the carrier design,
Theorem 1 (modulo its P2-2), Lemma R, Theorem 2(A)–(C) as conditional proofs,
both lattice witnesses (independently recomputed), and the OL exactness audit
— EXCEPT the run/read seam below. V20's gap 1 = P2-3 (same charge).

| finding | class | repair site |
|---|---|---|
| P2-1: nothing binds the run's (i+1)-th emitted record to "the engine's stage read at level i+1 on f over c" WITH c = the emitted prefix's chain — OL-2-min/OL-3 are hypotheticals parameterized by (f, c), OL-4 gives no run-to-stage decomposition, OL-5 internalized the glue at level 1 ONLY, and [F.0]'s c is unbound. (D)'s induction unlicensed at every level ≥ 2; the V14-1 class one level up | critical | §4: **OL-6 DECLARED** — run decomposition + chain binding at EVERY level, with the binding c = Θ(𝐇_{≤i}) (the emitted prefix's chain) displayed; the stage interface now displays c as the stage's own parameter; §5: (D)'s base and step both re-founded on OL-6. ONE general law, not per-level patches (round-5 churn discipline) |
| P2-2: Theorem 1's unconditional (L9)-at-r = 1 cites presuppose the (L5) Convention, which the note instantiates only under (D4) + OL-1; the level-0-only bridge is missing | gap | §3: **Lemma B** (the order-1 family bridge) displayed WITH proof (level-0-only dependence; Thm-2.11 family extension; transport); all three cite sites re-pointed; checklist item 7 rescoped |
| P2-3 (= V20 gap 1): OL-5's clause (a) asserts engine-internal mechanism (development + hull computation) that (D) does not consume — (b)+(c) suffice; the V14-2 minimality defect reintroduced at level 1 | gap | §4: OL-5 restated as its minimal core (b′)+(c′), stage-wise, with (b′)'s frame anchored intrinsically; rev 3's (a) re-advertised to the O-3 seam as the intended proof route via the PROVED (D3) |
| P2-4: OL-1 as literally quantified (independently per i) is not well-posed — "its type over F_rep" at order i presupposes OL-1(b) at orders < i | gap | §4: OL-1's cumulative (joint strong-induction) reading displayed in-statement |
| V20 gap 2: (L6)'s Thm-1.15 transcription "N_φ(F_i) = S_i" overstates — the paper gives equality up to translation | gap | §1 (L6): "up to translation" restored; every downstream use (slope, length, degree, residual) is translation-invariant |

## 0‴. Rev-5 changelog (V25 finding → repair site)

V25 (Codex, fresh context) on rev 4: SOUND-WITH-GAPS, no critical errors.
Confirmed: OL-6's base and step bindings ("This covers every continuing record
… There is no remaining circularity: Θ constructs the formal chain first,
while OL-1 subsequently permits its GMN interpretation"), Theorem 2(D)'s use
of OL-6 at both sites, Lemma B ("no finding"; "the acknowledged use of choice
is legitimate"; no circularity in citing (D4)), the OL-5 minimal-core cut
("No use of the removed development/hull-computation clause remains"), and
six-lemma joint sufficiency ("no undeclared run semantics, representative
admissibility, frame transport, residual-selection, or family-choice
dependence"). One finding:

| finding | class | repair site |
|---|---|---|
| V25: OL-3 asserts the FULL normalized-residual identity (R^nrm = c·R_{λ_{i+1}}(f); equal factor multisets with equal multiplicities; nonzero constant terms) while Theorem 2(D) consumes only the selected factor's multiplicity ("OL-3 gives (c2)") — "the conditional proof is valid, but its advertised minimal hypothesis list is not minimal"; the same asymmetry as V14-2 (OL-2) and P2-3 (OL-5), now at the residual clause | gap | §4: OL-3 consumption split — **OL-3-min [(c2)-core]** displayed and made Theorem 2(D)'s ONLY OL-3 hypothesis (the exact sibling of the OL-2-min and OL-5 (b′)+(c′) cuts); full OL-3 retained on record, re-advertised to its actual consumers (the O-3 seam's conformance-unit family; shared with the O-9 leaf's twisted-residue lemma) and kept as OL-3-min's intended proof route; OL-3 ⇒ OL-3-min displayed; §5 (D) hypothesis list + proof re-pointed; checklist items 6/11/13 updated |

Cross-package seam note (for SYNTH4): as of `O5triple_phaseB_verifybrief_rev3.md`,
this note's §1 (L2) transcription (Def 2.5 + Prop 2.6) is consumed ACROSS
packages — O5triple's pin (L5b′) cites it as the normalization carrier for its
Lemma STEEP (repairing V23 finding 1 there) instead of duplicating the
transcription. (L2) is thereby load-bearing for TWO packages; any future
finding against (L2) must fan out to O5triple. ((L2) is byte-stable at this
rev; it has stood unchallenged through V10/V14/V20/P2/V25.)

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
monic factor F_i with N_φ(F_i) one-sided of slope λ_i, EQUAL TO S_i UP TO
TRANSLATION [REV 4 — V20 gap 2: the paper's statement; slope, length E_i,
height, degree, and residual are translation-invariant, which is all that is
consumed below], and R_{λ_i}(F_i) ∼ R_{λ_i}(f);
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

## 3. Theorem 1 (order ≤ 1) — statement and complete proof

**Theorem 1.** Let f ∈ O[x] be monic of degree ≤ n with disc f ≠ 0, and let
𝐇 be well-formed of length ≤ 1 with Cons_f(𝐇); k' ∈ {0, 1} its number of
continuing nodes. [REV 2 — V10-C4: the rev-1 statement quantified symbols
(e₁, h₁, g₁, μ₁, ψ̂₁, G) undefined at k' = 0; the domain is now exhausted by
three explicit cases.]

**Case (i)** 𝐇 = (ρ₀) (k = k' = 0) and **Case (ii)** 𝐇 = (ρ₀; ν₁) with ν₁
terminal (k = 1, k' = 0; then a₀ ≥ 2 by W3 and Θ(𝐇) = Θ((ρ₀))). Claims:
(D0°) Θ is total and truncation-compatible on 𝔈 (unconditional; formal
  codomain); 𝐇° = (ρ₀) is recoverable from (f, Θ(𝐇)) (Lemma R at length 0);
  in case (ii), 𝐇 itself is NOT recoverable (Lemma R's non-claim) — no
  injectivity beyond 𝔈°_f is asserted.
(D2°) t^{(0)} ∈ t₀(f); non-complete whenever a₀ ≥ 2 (in particular in case
  (ii)).
(D4) as below (level-0 admissibility).
(Ch°) dCert(𝐇) = 0 ≤ ind₁(f) ≤ ind(f).

**Case (iii)** 𝐇 = (ρ₀; ν₁) with ν₁ continuing (k = k' = 1). Claims:
(D0) Θ total and truncation-compatible (as above); 𝐇 recoverable from
  (f, Θ(𝐇)) — Θ injective on {Cons_f, length ≤ 1, all nodes continuing}
  (Lemma R at length 1);
(D1) [invariant matching] the interpreted Θ(𝐇) is a genuine type of order 1
  over F_rep with f₁ = g₁, [F₂ : F_q] = f₀f₁, m₂ = e₁·(f₀g₁) = accE·accF
  where accE := e₁, accF := f₀g₁; v₂(φ₁) = h₁; and the SATURATION law: the
  tracked cluster factor G (defined in the proof) has deg G = m₂·μ₁, so
  accE·accF = deg G ⇔ μ₁ = 1, and when μ₁ = 1, G is irreducible with
  (e, f) = (accE, accF);
(D2) [placement] t^{(0)} ∈ t₀(f), non-complete, and Θ(𝐇) ∈ t₁(f);
(D3) [order-1 crossing] the first-read data format defined by the displayed
  development/hull/positional/residual formulas below IS (L2)/(L3)'s order-1
  data — so a first read performed by those formulas satisfies (c0)/(c1)
  (INCLUDING the positional clause)/(c2) automatically;
(D4) [admissibility, level 0] F_rep's level-0 layer is admissible: Lift₀(ψ̂₀)
  is a monic lift of ψ̂₀, one per ψ̂₀ — exactly (L5)'s first layer;
and the charge: dCert(𝐇) ≤ ind₁(f) ≤ ind(f).

**Lemma B (the order-1 family bridge). PROVED.** [NEW in rev 4 — P2-2: (L9)
is stated over a fully instantiated (L5) family; the note instantiates the
Convention only under (D4) + OL-1 ((C2)), yet Theorem 1 is unconditional, so
its r = 1 cites of (L9) need the following level-0-only bridge.] For f monic
with disc f ≠ 0: ind₁(f), computed over F_rep, satisfies ind₁(f) ≤ ind(f) —
unconditionally (no OL-1).

*Proof.* t₀(f) is choice-free (its members are the monic irreducible factors
ψ₀ of f̄, Def 3.10 at r = 0), and for t = ψ₀ ∈ t₀(f), Def 4.15 at r = 1 reads
ind_t(f) = f₀·ind(N₁^−(f)) with N₁ computed w.r.t. φ₁ = Lift₀(ψ₀): so
ind₁(f) depends on the family through its LEVEL-0 LAYER alone, which is
admissible by (D4). Extend that layer to a full (L5) family 𝔉: Thm 2.11
constructs a representative of every type over previously chosen polynomials,
so recursion over orders (with choice) yields a universally fixed family
extending Lift₀'s layer. (L9) over 𝔉 at r = 1 gives ind₁^𝔉(f) ≤ ind(f)
(ind(f) itself, Def 4.11, is family-free); and ind₁^𝔉(f) = ind₁(f), both
sides reading only the shared level-0 layer. ∎

*Proof (of Theorem 1).* Write ψ₀ = ψ̂₀, φ₁ = Lift₀(ψ₀), a = a₀.

(D4): Lift₀(ψ₀) is monic (lift of a monic polynomial coefficientwise, top
coefficient 1) and reduces to ψ₀; (L5)'s first layer demands exactly a monic
lift of every ψ₀, chosen once — Lift₀ is a function, so the choice is
universal. No other property of an order-0 representative is required by (L1).

(Cases (i)/(ii)): (D0°) is Lemma R at length 0 plus its displayed non-claim.
(D2°): t^{(0)} = ψ₀ ∈ t₀(f) means ω₁(f) = ord_{ψ₀}(f̄) ≥ 1, which is (c0)
with a₀ ≥ 1; non-completeness at a₀ ≥ 2 is Def 3.9. (Ch°): certified nodes
are continuing by definition, so dCert = 0; ind₁(f) ≥ 0 by (L8) nonnegativity
(a sum of ind_t ≥ 0); ind₁(f) ≤ ind(f) is Lemma B ((L9) at r = 1 through the
family bridge — P2-2). ∎ (cases (i)/(ii))

(Case (iii), (D3)): The order-1 objects of (L2)/(L3) are: the φ₁-adic
development f = Σ_j b_j φ₁^j (deg b_j < f₀, unique by monic division), the
polygon = lower hull of {(j, v(b_j)) : b_j ≠ 0} (v₁ = v, and
v₁(b_jφ₁^j) = v(b_j) + j·0 since v(φ₁) = 0), whose FINITE-slope principal
part runs on abscissas [j₀, a], where j₀ := ord_{φ₁}(f) and
ω = ord_{ψ₀}(f̄) = a (the ψ₀-adic development of f̄ is the reduction of the
φ₁-adic development of f, and ψ₀^a ∥ f̄ forces v(b_j) ≥ 1 for j < a — with
v(0) = ∞ — and v(b_a) = 0). [REV 2, V10-G1 — the j₀ corner, previously
glossed as "[0, ω]":] for separable f, j₀ ≤ 1 (if φ₁² | f then every root of
φ₁ is a multiple root of f, contradicting disc f ≠ 0). If j₀ = 1, (L3+)'s
side of slope −∞ has length E_∞ = 1 and carries the exact factor φ₁, which
is irreducible with (e, f) = (1, f₀) (monic with irreducible reduction —
the multiplicity-1/Hensel case of (L6)); if j₀ = a (forcing a = j₀ = 1) the
finite part is the single point (a, 0), N₁^−(f) has no finite side, and no
continuing node is Cons_f-consistent with this track (cases (i)/(ii) still
apply to it). All (c1)/(c2) clauses and Def 3.10 quantify over FINITE slopes,
so they are untouched by the −∞ side; the charge below is untouched because
ind(N) gains only the NONNEGATIVE term E_∞·H_fin ((L8)), preserving
ind(N) ≥ ind(S) and every inequality used; (L6)'s side dissection and the
tracked factor G live on the finite side S. [Falsifier F5 (§6) executes
exactly this corner: 871 forced j₀ = 1 samples, zero findings.] Continuing:
the side data (e, h, ℓ) with E = eℓ, H = hℓ, d = ℓ; the side's INITIAL POINT
(s₁, u₁) read off the hull in this same integer frame — the (c1) positional
datum [REV 2: the positional clause is part of the first-read format]; and
the residual coefficients c_j as displayed in (L3) (unit-part classes in F₁;
no twist at order 1). A "first read" that computes exactly these objects and
selects a monic irreducible factor ψ̂₁ of R_{λ₁}(f) with its multiplicity μ₁
therefore produces literally the (c0)/(c1)/(c2) data. (This clause is
definitional-by-inspection; the verifier should confirm that each displayed
formula matches (L2)/(L3) and that the ∼-ambiguity of R does not affect
factor selection: a global nonzero scalar changes neither the irreducible
factors nor their multiplicities.)

(D1): By W4 and Cons_f, ψ̂₁ ∈ F₁[z] is monic irreducible ≠ z (under Cons_f
this is automatic: R_λ(f) is never divisible by y, (L3)); λ₁ = −h₁/e₁ with
e₁, h₁ coprime positive (W-laws); so the interpreted Θ(𝐇) = (φ₁; λ₁, ψ̂₁) is
a type of order 1 over F_rep per (L1), with f₁ = deg ψ̂₁ = g₁,
F₂ = F₁[z]/(ψ̂₁), [F₂ : F_q] = f₀f₁, m₂ = m₁e₁f₁ = f₀e₁g₁.
v₂(φ₁) = h₁ + e₁·v₁(φ₁) = h₁ (L4 with v₁(φ₁) = v(φ₁) = 0, φ₁ monic).
Saturation: by (L6), the side S = S₁ carries the monic factor F_S, and the
choice ψ̂₁ with R_{λ₁}(f) ∼ ∏ ψ_i^{a_i} carves out G := G_{ψ̂₁} with
one-sided polygon of slope λ₁, residual ∼ ψ̂₁^{μ₁}, and
deg G = m₁·e₁·μ₁·f₁ = m₂·μ₁. Hence deg G = accE·accF = m₂ iff μ₁ = 1; and if
μ₁ = 1, Cor 1.20 gives G irreducible with e(L/K) = e₁ = accE and
f(L/K) = f₀f₁ = accF. [The verifier should check the degree bookkeeping
deg G = m₁·e·a·f against (L6)'s transcription.]

(D2): t^{(0)} = ψ₀ ∈ t₀(f) means ω₁(f) = ord_{ψ₀}(f̄) ≥ 1: that is (c0) with
a₀ ≥ 1. Since ν₁ exists, W3 gives a₀ ≥ 2, i.e. ω₁(f) ≥ 2: t^{(0)} is
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
all terms ≥ 0); and ind₁(f) ≤ ind(f) (Lemma B). dCert ≤ 1 closes the bound;
dCert = 0 is trivial.

(D0): Totality/truncation are structural on the formal codomain (C3);
recovery/injectivity is Lemma R at length ≤ 1 (its recovery map instantiated
at k' = 1 reads off, in order: ψ̂₀, a₀, (e₁, h₁), the unique slope-λ₁ side,
(ℓ₁, s₁, u₁), ψ̂₁, g₁, μ₁, inc₁). ∎

## 4. The six open lemmas (exact statements; NOT proved anywhere in the note)

OL-2/OL-3/OL-4/OL-5/OL-6 are statements about the project engine's stage flow — an
external, cited artifact (MOVES §B2-DEF, stage data F.0–F.2; Lean `MovesX`):
OL-2-min/OL-3-min/OL-5 assert that its emitted READ records satisfy the intrinsic
clauses of (C4); OL-4 that its emitted histories are well-formed with (c0);
OL-6 that a complete run DECOMPOSES into reads whose chain parameters are its
own emitted prefixes' chains [REV 4 — P2-1]. OL-1 is a statement about the
pinned function Lift of (C2). Their statements
are exact relative to the following displayed interface — plus the run-level
vocabulary (complete run, emitted history/record, the level-1 BASE read),
which names the engine's control flow and is consumed ONLY by the run-wise
OL-4/OL-6 and OL-5's premise — which together are ALL of the
engine text they consume [REV 2 — V10-G2/G3: the interface is now displayed;
rev 1's fractional-lattice ("(1/(e₁⋯e_i))ℤ, slot coordinates cleared, up to
the recorded translation") presentation is DELETED].

**The stage interface (from F.0–F.2).** A stage at level i + 1 ≥ 2 is
PARAMETERIZED by the monic input f and a chain datum c of order i — so the c
below is the stage's own parameter, bound inside the display [REV 4 — P2-1:
rev 3 left [F.0]'s c free]; which c a stage occurring INSIDE a complete run
carries is not part of the interface: it is exactly OL-6's binding clause.
The stage carries:
* [F.0] a ℤ-valued SIDE VALUATION u_{i+1} on O[x]∖{0} (multiplicative,
  ultrametric); the monic KEY Φ̂_{i+1} = Lift_i(c) with coefficient space
  C = {B : deg B < deg Φ̂_{i+1}}; the DIGIT ALGEBRA
  𝒟 = ⊕_{ρ ∈ ℤ/e_b} F·u_ρ, u_ρu_σ = ζ^{⌊(ρ+σ)/e_b⌋}u_{ρ+σ mod e_b}
  (≅ F[u]/(u^{e_b} − ζ); F the stage residue field, e_b ≥ 1 the birth index,
  ζ ∈ F^× a distinguished unit; at e_b = 1, 𝒟 = F); the digit map
  dig : C∖{0} → nonzero homogeneous elements of 𝒟; and the axioms (S-Ore)
  (u and dig multiplicative through Φ̂-remainders) and (S-K1)
  (u(f) = min_j (u(B_j) + j·u(Φ̂_{i+1})) over the development
  f = Σ_j B_j Φ̂_{i+1}^j).
* The STAGE WINDOW POLYGON of f := the lower hull of
  {(j, u_{i+1}(B_j) + j·u_{i+1}(Φ̂_{i+1})) : B_j ≠ 0}.
* [F.1] At a read side of denominator e (the read index): the STAGE RESIDUAL
  R^st(f)(z) := Σ_{u-minimizing j on the side} dig(B_j)·z^{(j−j₀)/e} ∈ 𝒟[z],
  support-anchored at j₀ := the least minimizing slot.
* [F.2] The ANCHOR NORMALIZATION: division by the anchor unit u_{ρ₀} (the
  𝒟-grade of the anchor coefficient) converts R^st to R^nrm ∈ F[z]; the stage
  residue field F is identified with the constructed F_{i+1} of (C1) — the
  same iterated quotient tower on both sides.
* The EMITTED node record at the read is (e, h, ℓ, s, u, sel, inc): (e, h)
  the coprime slope pair and ℓ the degree of the read side, (s, u) its
  initial point — all in the window-polygon frame — and sel = (g, μ) the
  degree/multiplicity of the selected monic irreducible factor of R^nrm
  (or sel = ⊥ at termination).

**OL-1 (lift admissibility + normalization). OPEN.** For every well-formed
chain datum c of order i ≥ 1, with t = its type over F_rep: (a) Lift_i(c) is
monic in O[x] of degree m_{i+1} = m_i e_i f_i; (b) Lift_i(c) is of type t with
R_i(Lift_i(c)) ∼ ψ̂_i — i.e., a Def-2.12 representative of t; (c)
v_{i+1}(Lift_i(c)) = e_i f_i·v_{i+1}(Lift_{i−1}(c′)) (c′ the parent datum),
equivalently V_{i+1} = e_i f_i(e_i V_i + h_i) with V_i := v_i(Lift_{i−1}(c′)).
[GMN Thm 2.11 proves EXISTENCE of a representative with (a)–(c); the open
content is that the pinned Lift_i satisfies the same.] [REV 4 — P2-4: OL-1 is
ONE JOINT statement, read by strong induction on the order — "its type over
F_rep" is defined at order i only once clause (b) holds at every order < i
(each lower Lift output a Def-2.12 representative of its truncation), so the
quantifier is CUMULATIVE: the instance at order i is asserted together with,
and presupposes, all lower instances. As independently-quantified per-i
statements it would not be well-posed.] Consumed by: ι's
well-definedness at orders ≥ 2 (hence by every order-≥2 clause of §5), and
by nothing at order ≤ 1.

**OL-2 (frame crossing + positional transport, orders ≥ 2). OPEN.** [REV 2 —
strengthened per V10-G2/C7.] For f monic separable and c a Cons_f-consistent
chain of order i ≥ 1 (well-defined given OL-1), with E_i := e₁⋯e_i:
(a) [valuation tie] u_{i+1} = v_{i+1} as functions on
  {B ∈ O[x] : B ≠ 0, deg B < m_{i+1}} — the stage side valuation IS GMN's
  order-(i+1) valuation (L2) in its own ℤ-normalization — and
  u_{i+1}(Φ̂_{i+1}) = v_{i+1}(Φ̂_{i+1}). [Attackable consequence: on
  constants, u_{i+1}(π) = E_i — the index-E_i extension of (L2); an
  implementation failing this on constants refutes (a) outright.]
(b) [frame identity — NO translation, NO scaling] hence the stage window
  polygon of f EQUALS N_{i+1}(f) as subsets of ℝ², vertex for vertex and side
  for side. Any window offset or recentering shift applied internally by the
  engine is inverted before the record is emitted; the correctness of that
  inversion is PART OF THIS CLAIM — it is exactly where the corpus's compiled
  stretch counterexample lives (HK52: a naive engine-internal vertex
  transport fails by a factor-e′ stretch at e′ ≥ 2), which is why (b) is
  stated as an exact identity of the EMITTED record, not of internal state.
(c) [side dictionary] consequently the emitted (e, h, ℓ) at the read side
  equal the lowest-terms slope pair (e_{i+1}, h_{i+1}) and degree d(S) of the
  corresponding side S of N_{i+1}^−(f) — the (c1) side data.
(d) [positional transport] the emitted (s, u) equal the initial point of S in
  the order-(i+1) integer frame — exactly the pair pinned by (c1)'s
  positional clause. Displayed corollary: (s, u) is then determined by
  (f, t^{(i)}, λ_{i+1}) alone (the unique slope-λ_{i+1} side's initial
  point), which is the recoverability Lemma R consumes — Lemma R itself
  needs NO part of OL-2, since (c1)'s positional clause is intrinsic.

**Consumption split [REV 3 — V14-2].** As stated, (a)–(b) are STRONGER than
Theorem 2(D) needs: 2(D) consumes only the emitted side record, not the
valuation tie on every admissible coefficient or the whole-polygon identity.
Theorem 2(D)'s ONLY OL-2 hypothesis is the following minimal core, stated
intrinsically (no stage window polygon, no "corresponding side"):

**OL-2-min [(c′)+(d′)]. OPEN.** Same setting (f monic separable, c a
Cons_f-consistent chain of order i ≥ 1, well-defined given OL-1); suppose the
engine's stage read at level i + 1 on f over c emits the record
(e, h, ℓ, s, u, …). Then N_{i+1}^−(f) has a side S of finite slope −h/e with
d(S) = ℓ, and (s, u) = the initial point of S in the order-(i+1) INTEGER
FRAME — verbatim (c1) at level i + 1.

(a)+(b) ⇒ OL-2-min: under (b) the stage window polygon IS N_{i+1}(f); the
read side has finite negative slope −h/e (h, e ≥ 1), hence is a side of
N_{i+1}^−(f); a polygon has at most one side of a given slope, so (c)/(d)
read off exactly (c′)/(d′). Consumed by: Theorem 2(D) consumes **OL-2-min
ONLY**. Clauses (a)–(b) — and the full package (a)–(d) — are consumed by NO
theorem of this note: their consumer is the O-3 design seam (its unit JC-2
targets the full rev-2 clauses (a)–(d), including the identity-frame
valuation tie), and they are the intended PROOF ROUTE for OL-2-min; the HK52
stretch trap lives in (b), which is why the full form stays on record here
with its attackable constant-test.

**OL-3 (residual identification, orders ≥ 2 — full form). OPEN.** [REV 2 —
restated over
the displayed interface per V10-G3.] Same setting: the anchor-normalized
stage residual satisfies R^nrm = c·R_{λ_{i+1}}(f) for some c ∈ F_{i+1}^×,
where R_{λ_{i+1}}(f) is GMN's Def-2.21 residual over F_rep (itself defined
only up to F^×, so this is the maximal meaningful sharpness); both sides have
nonzero constant term (support anchoring on the engine side; "never divisible
by y" on the GMN side, (L3)). Hence equal monic-irreducible factor multisets
with equal multiplicities.
The open content: the z-power twists of GMN's Def 2.20 coefficients are
absorbed EXACTLY by the single anchor-unit division of F.2. Consumed by:
NO theorem of this note [REV 5 — V25: rev 4 advertised "Theorem 2(D) ONLY",
but (D) consumes only the minimal core below]; the full form's consumers are
the O-3 design seam (the same conformance-unit family as OL-2(a)–(d) and
rev 3's OL-5(a)) and the O-9 leaf's twisted-residue lemma [shared: one proof
should serve both], and it is the intended PROOF ROUTE for OL-3-min.

**Consumption split [REV 5 — V25; the V14-2/P2-3 asymmetry at the residual
clause].** As stated, the full residual identity is STRONGER than Theorem
2(D) needs: (D) consumes only the selected factor's multiplicity — (c2).
Theorem 2(D)'s ONLY OL-3 hypothesis is:

**OL-3-min [(c2)-core]. OPEN.** Same setting (f monic separable, c a
Cons_f-consistent chain of order i ≥ 1, well-defined given OL-1); suppose the
engine's stage read at level i + 1 on f over c emits a continuing record
(e, h, ℓ, s, u, (g, μ), inc) with dressing ψ̂ — write λ := −h/e. Then
ord_{ψ̂}(R_λ(f)) = μ, where R_λ(f) is GMN's Def-2.21 residual over F_rep at
the slope-λ side of N_{i+1}^−(f) — verbatim (c2) at level i + 1. [Definedness
protocol, as in Cons_f's own inductive reading: (c2) is read after (c1); in
Theorem 2(D), OL-2-min fires first and supplies the slope-λ side, so R_λ(f)
is the residual of an existing side. OL-3-min asserts nothing about R^nrm,
the factor multiset away from ψ̂, or constant terms.]

OL-3 ⇒ OL-3-min: by the displayed record semantics (the emitted node record:
sel = (g, μ) the degree/multiplicity of the selected monic irreducible factor
of R^nrm), ψ̂ is a monic irreducible factor of R^nrm with
ord_{ψ̂}(R^nrm) = μ; under R^nrm = c·R_λ(f) with
c ∈ F_{i+1}^×, a nonzero scalar changes neither the irreducible factors nor
their multiplicities (scope remark (4)), so
ord_{ψ̂}(R_λ(f)) = μ. Consumed by: Theorem 2(D) consumes
**OL-3-min ONLY**.

**OL-4 (emission discipline). OPEN.** [NEW in rev 2 — this dependence was
hidden by rev 1's scope remark (3), now deleted; V10-C8.] For every monic
f ∈ O[x] with disc f ≠ 0 and every complete run of the engine's stage flow on
f: the emitted dressed history 𝐇 = (ρ₀; ν₁, …, ν_k) is a WELL-FORMED element
of 𝔈, namely (a) every record field lies in (C1)'s declared domains; (b)
W1–W5 hold — in particular sel_i ≠ ⊥ for all i < k (only the final record may
be terminal), interior selections have μ_i ≥ 2, a₀ ≥ 2 whenever k ≥ 1, and
inc_i = 1 ⇔ e_i·g_i ≥ 2; (c) the dressing lands in the constructed tower with
ψ̂_i monic irreducible ≠ z of degree g_i (the F.2 normalization); (d) the
level-0 record satisfies a₀ = ord_{ψ̂₀}(f̄). Consumed by: Theorem 2(D) ONLY.
Intended proof route (NOT part of this note): the engine's control flow — the
(τ-irr) rule halts a branch at multiplicity 1, so continuation implies
μ ≥ 2; the increment bookkeeping sets inc; a run emits at most one terminal
record, last.

**OL-5 (first-read conformance, order 1 — minimal core). OPEN.** [Declared
in rev 3 — V14-1: rev
2's Theorem 2(D) obtained (c1)/(c2) at i = 1 by citing (D3), but (D3) is a
CONDITIONAL — "a first read that computes exactly these objects … produces
literally the (c0)/(c1)/(c2) data" — and nothing among OL-1–OL-4 asserted
that the engine's first read does compute them: OL-2/OL-3 quantify over the
level-(i+1) ≥ 2 stage interface only, and OL-4 supplies well-formedness plus
(c0). This was another undeclared emission-semantics dependence, distinct
from OL-4's W-law discipline. REV 4 — P2-1/P2-3: rev 3 phrased OL-5 RUN-wise,
internalizing the run↔read glue at level 1 only; that glue is now the
all-levels OL-6 below, and OL-5 is restated STAGE-wise (parameterized by
(f, ρ₀), the exact sibling of OL-2-min/OL-3) and cut to the clauses (D)
consumes — P2-3 (= V20 gap 1) charged rev 3's clause (a), the engine-internal
development/hull computation, as over-strength: the same asymmetry as
V14-2's OL-2 split.] For f ∈ O[x] monic with disc f ≠ 0: suppose the
engine's BASE READ (level 1) on f over the track ρ₀ = (ψ̂₀, a₀), with key
φ₁ := Lift₀(ψ̂₀), emits the continuing record
ν₁ = (e₁, h₁, ℓ₁, s₁, u₁, (g₁, μ₁), inc₁) with dressing ψ̂₁. Then:
(b′) [side + position] N₁^−(f) (w.r.t. φ₁) has a side S₁ of finite slope
  λ₁ := −h₁/e₁ ((e₁, h₁) the lowest-terms pair) with d(S₁) = ℓ₁, and
  (s₁, u₁) = the initial point of S₁ in the order-1 INTEGER FRAME — the
  plane of the point set {(j, v(b_j))} of the development f = Σ_j b_j φ₁^j
  [intrinsic anchoring, no engine frame — P2-3] — verbatim (c1) at i = 1;
(c′) [residual + selection] ψ̂₁ is a monic irreducible factor of the (L3)
  residual R_{λ₁}(f) with ord_{ψ̂₁}(R_{λ₁}(f)) = μ₁ and deg ψ̂₁ = g₁ —
  verbatim (c2) at i = 1.
Rev 3's clause (a) (the read COMPUTES the φ₁-adic development and its lower
hull, with the (L3+) j₀ convention) is consumed by NO theorem of this note;
it is re-advertised to the O-3 realization seam (sibling of OL-2(a)–(b), the
same conformance unit family) and remains the intended PROOF ROUTE: by (D3)
— PROVED: the displayed formulas ARE (L2)/(L3)'s order-1 objects — a read
performed by those formulas satisfies (b′)+(c′) automatically. Consumed by:
Theorem 2(D) ONLY (its induction base, at the read OL-6(a) binds). OL-5 is
the level-1 sibling of OL-2-min/OL-3: those cover the F.0–F.2 stage
interface at levels ≥ 2; the first read is the engine's BASE code path, so
its conformance is a separate statement. Histories whose first node is
terminal need no level-1 clause (Cons_f constrains no terminal field), and
k = 0 histories need only (c0) = OL-4(d). Intended proof route (NOT part of
this note): the base read of MOVES §B2-DEF is the plain Newton-polygon read
— trivial digit algebra (e_b = 1, 𝒟 = F₁), no twist, no offset — so OL-5
should be the degenerate instance of the OL-2/OL-3 conformance family.

**OL-6 (run decomposition + chain binding, every level). OPEN.** [NEW in
rev 4 — P2-1: OL-2-min/OL-3 (and now OL-5) are hypotheticals about reads
PARAMETERIZED by (f, c) resp. (f, ρ₀); nothing in rev 3 asserted that a
complete run DECOMPOSES into such reads with the chain parameter of each
read equal to the formal chain of the previously emitted records — [F.0]'s c
was unbound — so Theorem 2(D)'s induction was unlicensed at every level ≥ 2:
the V14-1 defect class one level up. Per the round-5 churn discipline this
is repaired by ONE general law, not per-level patches.] For every monic
f ∈ O[x] with disc f ≠ 0 and every complete run of the engine's stage flow
on f with emitted dressed history 𝐇 = (ρ₀; ν₁, …, ν_k) (well-formed by
OL-4; its proper prefixes 𝐇_{≤i} := (ρ₀; ν₁, …, ν_i) are then well-formed
with all nodes continuing, by W5 and (C1)'s prefix closure): for every
1 ≤ j ≤ k with ν_j CONTINUING, the j-th emitted record (with its dressing)
IS the record emitted by the engine's level-j read on f over the chain of
its emitted prefix — the binding displayed:
(a) at j = 1: ν₁ is emitted by the BASE read of OL-5 on f over the track
  ρ₀, with key φ₁ = Lift₀(ψ̂₀) — the run's level-0 dressing;
(b) at j = i + 1 ≥ 2: ν_{i+1} is emitted by the stage read at level i + 1
  on f over c := Θ(𝐇_{≤i}) — the formal chain datum of the run's emitted
  prefix, the run's current center (Θ is total and formal, (C3), so c is
  defined with NO consistency or OL-1 input) — with the stage's [F.0] key
  Φ̂_{i+1} = Lift_i(c).
In words: a complete run decomposes into successive reads, and the chain
parameter of each read is exactly the formal chain of what the run emitted
before it. Consumed by: Theorem 2(D) ONLY (base and step — it supplies the
premise on which OL-5/OL-2-min/OL-3-min fire). Terminal records need no binding
clause: Cons_f constrains no terminal field (Lemma R's non-claim). Intended
proof route (NOT part of this note): the engine's control flow BIRTHS each
next stage from the just-emitted record (MOVES §B2-DEF's stage-birth step),
so the binding should hold by construction of the flow; it is declared here
because this note consumes the engine only through its emitted records.

## 5. Theorem 2 (all orders) — statement and complete conditional proof

**Theorem 2.** Let f ∈ O[x] be monic of degree ≤ n, disc f ≠ 0, 𝐇 ∈ 𝔈 with
continuing nodes ν₁ … ν_{k'}, k' ≥ 0. Then:

(A) [Cons_f; at orders ≥ 2, OL-1 grants well-definedness of the GMN objects
read] t^{(i)} ∈ t_i(f) for 0 ≤ i ≤ k', with t^{(i)} non-complete for i < k';
the identity placement is injective; Θ is injective on 𝔈°_f with the
displayed recovery map (Lemma R); for 𝐇 with a terminal last node, exactly
𝐇° is recoverable. [At k' = 0 this reads: t^{(0)} ∈ t₀(f), and (ψ̂₀, a₀) is
recovered.]

(B) [Cons_f + OL-1] Invariant matching, all clauses quantified over
1 ≤ i ≤ k' (VACUOUS at k' = 0): e_i, h_i, f_i = g_i as constructed;
[F_{i+1} : F_q] = f₀⋯f_i; deg Φ̂_{i+1} = m_{i+1} = accE_i·accF_i where
accE_i := e₁⋯e_i, accF_i := f₀g₁⋯g_i; the V-recursion
V_{i+1} = e_i f_i(e_i V_i + h_i). SATURATION — asserted for k' ≥ 1 ONLY
[REV 2 — V10-C9: at k' = 0 there is no "last read" and μ_{k'} is undefined]:
at the last continuing node, the cluster factor f_{t^{(k')}} has degree
m_{k'+1}·μ_{k'}, so accE·accF = deg f_{t^{(k')}} ⇔ μ_{k'} = 1; and if
μ_{k'} = 1 then f_{t^{(k')}} is irreducible with
(e, f) = (accE_{k'}, accF_{k'}).

(C) [Cons_f + OL-1] The charge: every certified node ν_i has
ind_{t^{(i−1)}}(f) ≥ 1; distinct certified nodes charge distinct orders; and
dCert(𝐇) ≤ Σ_{r=1}^{k'} ind_r(f) ≤ ind(f). [At k' = 0 this degenerates to
dCert(𝐇) = 0 ≤ ind(f): certified nodes are continuing, and ind(f) ≥ 0 by
(L8).]

(D) [OL-1 + OL-2-min + OL-3-min + OL-4 + OL-5 + OL-6; REV 5 — OL-3 cut to
its minimal core (V25); REV 4 — the run/read
binding is now the declared OL-6 at every level, and OL-5 is cut to its
minimal core (P2-1/P2-3); REV 3 — the level-1 lemma (V14-1) and only the
minimal OL-2 core (V14-2)]
Every history emitted by the engine's stage flow on f is a well-formed
element of 𝔈 (OL-4) satisfying Cons_f — so (A)/(B)/(C) apply to it.

*Proof.* (A) Induction on i. Base: (c0) gives ω₁(f) = a₀ ≥ 1, so
t^{(0)} ∈ t₀(f); if k' ≥ 1, W3 forces a₀ ≥ 2 = non-completeness. Step: given
t^{(i−1)} ∈ t_{i−1}(f) non-complete, (c1) provides the finite slope λ_i of
N_i^−(f) and (c2) the monic irreducible ψ̂_i | R_{λ_i}(f); Def 3.10 membership
verbatim: t^{(i)} ∈ t_i(f). Interior non-completeness: ω_{i+1}(f) = μ_i ≥ 2
for i < k' (W3). Injectivity: Lemma R (its recovery map is stated for
arbitrary k'; at orders ≥ 2 the objects it reads are well-defined by OL-1),
together with its displayed terminal non-claim. Placement: identity on
indices of a finite list — injective.

(B) The levelwise identifications are Θ's construction plus W4. Tower and
m-recursion: (L1) arithmetic, with deg Φ̂_{i+1} = m_{i+1} from OL-1(a).
V-recursion: OL-1(c) + (L4)'s Prop-2.7 identity. Saturation (under its
k' ≥ 1 guard): t^{(k')} ∈ t_{k'}(f) by (A);
ω_{k'+1}(f) = ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) = μ_{k'} by (c2); Def 2.3 gives
deg f_{t^{(k')}} = m_{k'+1}·ω_{k'+1}(f) = (accE·accF)·μ_{k'} (using
m_{k'+1} = accE_{k'}·accF_{k'} from the m-recursion and m₁ = f₀). Hence the
biconditional. At μ_{k'} = 1: Def 3.9 completeness + Cor 3.8 give
irreducibility and (e, f) = (e₁⋯e_{k'}, f₀⋯f_{k'}) = (accE, accF).

(C) If k' = 0 there is no certified node (certified ⇒ continuing), so
dCert(𝐇) = 0, and ind(f) ≥ 0 by (L8)'s Def-4.11 nonnegativity — the bound
holds trivially; no appeal to (L9) is made [REV 2 — V10-C9]. Let now k' ≥ 1.
A certified ν_i is T1 with e_ig_i ≥ 2 or T2 (W1/W2). By (c1), N_i^−(f)
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

(D) [REV 4 — the run↔read binding at EVERY level is now the declared OL-6
(P2-1); rev 3 internalized it at level 1 only (its run-wise OL-5), leaving
the chain parameter of a level-≥2 stage occurring inside a run unbound.
REV 3 — level-1 base on OL-5 (V14-1), step re-pointed at OL-2-min (V14-2).
REV 2 — rewritten; V10-C8.] Fix a complete run of the stage flow on f and
let 𝐇 be its emitted dressed history. OL-4 gives 𝐇 ∈ 𝔈 (domains, W1–W5,
tower dressing, only-last-terminal) and (c0) (its clause (d)). Cons_f by
induction along the continuing nodes. Level 1: OL-6(a) binds ν₁ to the base
read on f over ρ₀ with key φ₁ = Lift₀(ψ̂₀); OL-5 applied to THAT read gives
(b′) = (c1) (side data AND initial point — the positional clause) and
(c′) = (c2) at i = 1. Level i + 1 ≥ 2: the induction hypothesis makes
c := Θ(𝐇_{≤i}) a Cons_f-consistent chain of order i; OL-6(b) binds ν_{i+1}
to the stage read at level i + 1 on f over THIS c (key Φ̂_{i+1} = Lift_i(c))
— exactly the premise OL-2-min and OL-3-min quantify over; OL-2-min then gives
(c1) in full ((c′) the side data, (d′) the positional clause), OL-3-min gives
(c2); OL-1 keeps the level-(i+2) GMN objects defined over F_rep. No clause
of OL-2 beyond OL-2-min, no clause of OL-3 beyond OL-3-min [REV 5 — V25], and
no clause of rev 3's OL-5 beyond (b′)+(c′), is
consumed. Hence Cons_f(𝐇), and (A)/(B)/(C) apply. The terminal record, if
any, is placed by OL-4's discipline but constrained by nothing — consistent
with Lemma R's restriction. ∎

**Scope remarks the verifier should enforce.** (1) Nothing above claims that
the stage flow's emitted histories are exactly the GMN tree of f, nor that
every GMN type of f is realized — those are trace/realization statements,
explicitly out of scope. (2) The consumption of (L9) is the ONLY appeal to
the theorem of the index, and it is used exactly in the finite-sum form (†) —
at r = 1 always through Lemma B's family bridge (P2-2).
(3′) [REPLACES rev 1's remark (3), which asserted the engine's W-law
conformance was "out of scope" while Theorem 2(D) consumed it — V10-C8; that
conformance is now the declared OL-4.] Consumer audit: every exported
quantity (Θ(𝐇), dCert, charges, saturation data) is a function of the
continuing part 𝐇°, so Lemma R's restriction to 𝔈°_f costs no clause; any
FUTURE consumer needing full-𝐇 injectivity must first supply the terminal
seam (t-i)/(t-ii) of §2. (4) The ∼-ambiguity of residuals never matters:
only factor multisets and multiplicities are consumed.

## 6. Corroborating computation (exact arithmetic; NOT part of the proofs)

Executed falsifiers (PARI/GP; all exact; a failure of any would have refuted
the labeled claim). F1–F4 are rev 1's, carried unchanged; F5 is new in rev 2.

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
  failures. [Caveat, rev 2: F1's code SKIPPED polynomials with a vanishing
  initial digit (b₀ = 0) — exactly the V10-G1 corner. F5 covers it.]
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
  order-2 points (0, 4k+3), (2, 4) — computed in the v₂ INTEGER frame, the
  same frame OL-2(a)/(d) pins (v₂(2) = e₁ = 2, v₂(φ₁) = h₁ + e₁v₁(φ₁) = 1),
  with initial point (s₂, u₂) = (0, 4k+3) — side (e₂,h₂,ℓ₂) = (2, 4k−1, 1),
  saturated. Predicted (e, f) = (accE, accF) = (4, 2): confirmed 3/3. Sharper:
  measured ind_2(f) = 6, 10, 14 = 4k + 2 = f₀·ind(N₁^−) + f₀f₁·ind(N₂^−) =
  2·2 + 2·(2k−1) EXACTLY — pinning Def 4.15's twist factor numerically (without
  the twist the prediction would be 2k + 1) and, via Thm 4.18(2), consistent
  with termination at order 2. Also dCert = 2 ≤ ind throughout.
* **F4 (the ind(S) table).** All 1548 configurations (coprime e, h ≤ 8,
  ℓ ≤ 6, offset grid): brute lattice count = ½(EH − E − H + d), and
  count ≥ 1 exactly on T1/T2 shapes: 0 violations.
* **F5 [NEW in rev 2] (the V10-G1 corner: exact φ₁-divisibility / slope-−∞
  side).** 871 samples f = φ₁·g at p ∈ {2, 3, 5}, n ∈ {3..7} (seed 20260801),
  constructed with ord_{φ₁}(f) = 1 and ord_{ψ₀}(f̄) = a ≥ 2 — exactly the
  case F1 skipped. Per sample: finite principal part read on [j₀, a]; the −∞
  side booked as the Hensel leaf (1, f₀) (the exact factor φ₁) plus the
  ind(N) term E_∞·H_fin per (L8). Checks: (i) predicted (e,f) multiset vs
  idealprimedec ground truth on the 827 order-1-decided samples — 0
  mismatches; (ii) degree checksum — 0 failures; (iii) ind₁ ≤ ind_p WITH the
  E_∞·H_fin term included (the sharper direction: the term only increases
  ind₁) — 0 violations; (iv) #certified finite sides ≤ ind₁ — 0 violations.
  Plus the displayed hand corner p = 3, f = x² + 3x (j₀ = 1, a = 2,
  ind₁ = ind_p = 1, leaves (1,1)+(1,1)): pass. Script:
  `lean/notes/openmath/O2a_rev2_check.gp`.

## 7. Verification checklist (where to press hardest)

1. **Transcriptions (L1)–(L9)** against the paper (arXiv:0807.2620v2): esp.
   eq. (16) + the Prop 2.7 identity; Def 4.15's twist product f₀⋯f_{r−1} and
   its INDEXING at r = i in Theorem 2(C); Def 3.10's sprouting-from-non-complete;
   the order-1 residual coefficient formula (no twist at order 1); Remark
   4.14's region and its consequences (every Def-4.12 summand ≥ 0); and NEW:
   (L3+)'s slope-−∞ convention and the E_∞·H_fin term of (L8) — is the
   finite-slope-only quantification of Def 3.10 faithful?
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
   (ι's well-definedness at orders ≥ 2; deg; V-recursion), OL-2-min (Theorem
   2(D) levels ≥ 2 side + positional data — and NOTHING else; in particular
   Lemma R must nowhere consume any part of OL-2, and (D) must nowhere
   consume OL-2(a)/(b) — V14-2), OL-3-min ((c2) at orders ≥ 2 in (D) — and
   NOTHING else; in particular (D) must nowhere consume full OL-3's residual
   identity R^nrm = c·R_{λ_{i+1}}(f) or its whole-multiset consequence —
   V25), OL-4
   (well-formedness + (c0) in (D)), OL-5 ((b′)/(c′) = (c1)/(c2) at i = 1 in
   (D), at the read OL-6(a) binds — and NOTHING else: rev 3's clause (a)
   must be consumed nowhere, P2-3), OL-6 (the run/read binding in (D), base
   and step — and NOTHING else, P2-1) is flagged, and that no OTHER unproved
   step hides in Theorem 2. Minimality direction too: each hypothesis list
   must name no more than the proof consumes.
7. **The (†) consumption**: only (L9), only in finite-sum form; in Theorem
   2(C) only at k' ≥ 1 (the k' = 0 branch must not cite it); in Theorem 1
   the r = 1 cites (all three cases) pass through the displayed Lemma B —
   verify the bridge (level-0-only dependence of ind₁; the Thm-2.11 family
   extension; the transport) — P2-2.
8. **Carrier coherence**: every field of every carrier object now has a
   declared domain (V10-C1); equalities are literal on constructed objects;
   no isomorphism-class or choice-dependent object appears in either carrier;
   the codomain is formal and Θ's totality genuinely unconditional (V10-C6);
   no GMN-valued object is used without ι being granted at that order
   (V10-C2).
9. **The terminal seam** (V10-C3/C5/C7): verify Lemma R's restriction to
   𝔈°_f is used consistently — no clause of Theorems 1/2 or of the consumer
   remarks claims recovery of terminal fields; verify the consumer audit
   (3′): every exported quantity really is a function of 𝐇°.
10. **The k' = 0 corners** (V10-C4/C9): instantiate every clause of Theorem 1
   at 𝐇 = (ρ₀) and at (ρ₀; ν₁ terminal), and every clause of Theorem 2 at
   k' = 0 — each must be well-formed and proved as stated (no undefined
   μ_{k'}, no "last read", no (L9) at r = 0).
11. **The stage interface**: are OL-2/OL-2-min/OL-3/OL-3-min/OL-4/OL-5/OL-6
   exactly
   attackable as stated — i.e., is every object in their statements either
   GMN-defined (§1), carrier-defined (§2), displayed in §4's interface
   (whose c is now the stage's bound parameter — P2-1), or (for OL-5's frame)
   intrinsic per (c1)'s positional clause? (V10-G2/G3 asked for precisely
   this.)
12. **The level-1 base (V14-1/P2-3)**: instantiate Theorem 2(D)'s induction
   at i = 1 — does OL-6(a) + OL-5 yield (c1) INCLUDING the positional clause
   and (c2), with no residual appeal to the engine's internals and no use of
   rev 3's clause (a)? And does the (a)+(b) ⇒ OL-2-min display in §4
   genuinely collapse (the at-most-one-side-per-slope step)?
13. **The run/read seam (P2-1)**: at every level i + 1 ≥ 2 of (D)'s
   induction, verify the read to which OL-2-min/OL-3-min are applied is BOUND —
   its chain parameter is OL-6(b)'s c = Θ(𝐇_{≤i}) with key
   Φ̂_{i+1} = Lift_i(c) — and that no stage-wise lemma anywhere in the note
   is applied to a run-emitted record without an OL-6 clause supplying its
   read; verify OL-6's own statement needs no consistency or OL-1 input
   (Θ is total and formal); sweep for any OTHER consumer of the run/read
   seam with an unbound chain parameter.

Charge: quote-and-classify only; critical error vs justification gap; check
steps downstream of a gap by assuming the gap's conclusion. The six OL's are
DECLARED open — they are not findings; an UNDECLARED dependence is.

