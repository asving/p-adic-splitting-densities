# O2a — the upstream engine↔GMN dictionary (invariants + order placement) — Phase-B attempt (Fable, 2026-07-31)

Leaf (docs/MATH_COMPLETION_TREE_2026-08-01.md, §D1.2 node D-13): **O-2a** = clauses
(i)–(iv) of O-2 — invariant matching, injective order placement, normalization
crossing, representative admissibility — PLUS the D-5 carrier/equality design for
the dictionary Θ's domain and codomain. Upstream by construction: provable against
the GMN text without realization semantics. **Explicitly NOT attempted here**
(per D-13): O-2b = O-2 clauses (v)–(vi) (K-DICT-OB1 trace/tree correspondence,
K-DICT-OB2 σ-invariance under Okutsu equivalence) — those join the O-3 cluster.

RESULT IN ONE LINE: the carrier design is delivered (dressed histories ↔ type
chains over the engine's pinned representative family, both DISCRETE with literal
componentwise equality — the V5-defect answer); the dictionary is PROVED at order
≤ 1 (Theorem 1: all four clauses + the dCert ≤ ind(f) charge, from GMN Thm
1.15/1.19/Cor 1.20 + Defs 4.11/4.12/4.15 + Thm 4.18(1) and the two-line ind2
algebra); at order ≥ 2 it is REDUCED (Theorem 2, proof complete given the
interface) to THREE exactly-stated open lemmas — OL-2a-1 (engine-lift
admissibility + (16)-normalization), OL-2a-2 (raw-frame → v_r-frame crossing),
OL-2a-3 (anchor-normalized residual = GMN twisted residual) — with the
invariant-matching and charging clauses THEOREMS given those three. Falsifiers
executed first, all pass (§8): 3600-poly order-1 dictionary sweep (0 mismatches),
ind₁ ≤ ind_p executed for the first time (M15's proposed N3; 0 violations),
two order-2 families exact including a wild f₀ = 2 case where the measured index
6/10/14 equals the predicted 4k+2 WITH the Def-4.15 twist factor f₀f₁ = 2.

Labels: (a) known / (b) new proof of known / (c) claimed new. "Corpus" = this
repo's machine-checked Lean or dual-accepted notes, cited as evidence, never as
proof of a mathematical claim in this note.

## 0. What O-2a demands, and who consumes it

From the tree's O-2 statement, the four upstream clauses, for a correspondence Θ
between canonical-engine branch histories and GMN types with representatives:
(i) accumulated invariants match — (accE, accF) = (e₁⋯e_r, f₀⋯f_r), saturation
accE·accF = d ⇔ ω = 1; (ii) every certified increment node maps injectively to a
GMN order with a type realizing it; (iii) the engine's raw-frame side read
transports to the v_r-normalized frame with the same (e, h) and per-certified-node
ind ≥ 1; (iv) the engine's canonical key lifts form one universally-fixed
GMN-admissible representative family. Plus D-5: Θ's domain must be a coherent
carrier with a declared equality.

Consumers served (per the tree): K-10 (`cl15_align`, via the machine-checked KE8
reduction — §7); O-6 Lemma A's e·g form; O-5's (LEAF) = LIT-4-through-O-2 (the
saturation clause is exactly the (OM-SAT) interface); O-7's alignment leg; D-11.

## 1. The GMN side, pinned [(a) known; sources verified this session]

All from arXiv:0807.2620v2 (= Trans. AMS 364 (2012) 361–416; printed-numbering
caveat of `docs/GMN_citations.md` carried), re-read this session from the
extracted text (/tmp/gmn_full.txt, from the M15 session's download). Base: K
finite over ℚ_p, O = O_K, v(K*) = ℤ, F = F_q. Our instance K = ℚ_p (everything
below is stated by GMN for general K, so the unramified bases q = p^δ needed by
D-3 are covered verbatim).

* **Types** (§2.1): t = (φ₁(x); λ₁, φ₂(x); ⋯; λ_{r−1}, φ_r(x); λ_r, ψ_r(y)) with
  φ₁ a monic lift of a monic irreducible ψ₀ ∈ F[y]; λ_i = −h_i/e_i (e_i, h_i
  coprime positive); ψ_i ∈ F_i[y] monic irreducible, ψ_i ≠ y for i ≥ 1;
  residue tower F₀ = F ⊂ F₁ ⊂ ⋯, F_{i+1} = F_i[y]/(ψ_i), f_i := deg ψ_i,
  [F_{i+1} : F] = f₀f₁⋯f_i. Degrees: m₁ = f₀, m_{i+1} = m_i e_i f_i.
* **Order-r valuation** (Def 2.5): v_r(P) := e_{r−1}·H_{r−1}(S_{r−1}(P)); v_r is
  a discrete valuation on K(x)* whose restriction to K extends v with index
  e₁⋯e_{r−1} (Prop 2.6); v_r(a) = e_{r−1}v_{r−1}(a) for a ∈ O.
* **Order-r polygon and residual** (Defs 2.3, 2.19–2.21): N_r(P) from the φ_r-adic
  development under v_r; principal part N_r^−; per side S of slope −h_r/e_r,
  length E = e_r·d, height H = h_r·d, degree d = d(S); residual R_{λ_r}(P) ∈
  F_r[y] of degree d, never divisible by y (c_s and the leading coefficient
  nonzero). ω_{i+1}(P) := ord_{ψ_i}(R_i(P)). deg f_t = m_r·ω_r(P) (Def 2.3).
* **Representatives** (Thm 2.11 / Def 2.12): a representative of t (order r−1) is
  a monic φ_r ∈ O[x] of type t with R_{r−1}(φ_r) ∼ ψ_{r−1}. Thm 2.11 constructs
  one with eq. (16): deg φ_r = m_r, ω_r(φ_r) = 1, v_r(φ_r) = e_{r−1}f_{r−1}·
  v_r(φ_{r−1}); with (Prop 2.7, as used in the proof of Prop 2.15)
  v_r(φ_{r−1}) = h_{r−1} + e_{r−1}v_{r−1}(φ_{r−1}).
* **The §4.1 Convention (the "universally fixed family"), verbatim content**: fix
  a monic lift φ₁ of EVERY monic irreducible ψ₀ ∈ F[y]; recursively, for every
  type t built from previously chosen polynomials, fix ONE representative
  φ_{i+1}(x) of t; all types are made up only of chosen polynomials. "Once these
  choices are made, the set t_r(P) is uniquely determined by r and P(x)."
  §4.2's opening re-affirms it for the index sections.
* **Index vocabulary** (Defs 4.11/4.12/4.15, Remarks 4.13/4.14): ind(f) :=
  Σ ind(F_i) + Σ_{i<j} v(Res(F_i, F_j)) over the monic irreducible factorization
  (Def 4.11), with q^{ind(F)} = (O_L : O[θ]) per irreducible factor;
  ind(S) := ½(EH − E − H + d) for a finite-slope side, 0 otherwise; ind(N) :=
  Σ_i ind(S_i) + Σ_{i<j} E_i H_j (+ E_∞·H_fin for a slope-−∞ side); ind(N) is a
  lattice-point count (Remark 4.14), so every summand is ≥ 0 and ind(N) ≥ ind(S)
  for each side; ind_t(P) := f₀⋯f_{r−1}·ind(N_r^−(P)) for t of order r−1 (Def
  4.15 — NOTE the f₀⋯f_{r−1} twist factor, confirmed exactly by falsifier F3B),
  ind_r(P) := Σ_{t ∈ t_{r−1}(P)} ind_t(P); Def 4.15 carries the explicit warning
  that ind_t depends on the representative choice — dissolved here by DES-3.
* **Theorem 4.18(1)** (theorem of the index): for f monic separable and r ≥ 1,
  ind(f) ≥ ind₁(f) + ⋯ + ind_r(f). The finite-sum face (†) — for every finite
  R ⊂ ℕ_{≥1}, Σ_{r∈R} ind_r(f) ≤ ind(f) — follows with nonnegativity (M15 §4).
* **Type tree** (Def 3.10): t_r(f) sprouts from NON-COMPLETE t ∈ t_{r−1}(f) by
  choosing a finite slope λ_r of N_r^−(f) and a monic irreducible ψ_r | R_{λ_r}(f);
  f-complete (Def 3.9) ⇔ ω = 1 ⇔ f_t irreducible; Cor 1.20 (order 1) / Cor 3.8
  (order r): a multiplicity-1 residual factor certifies an irreducible factor
  with e = e₁⋯e_r, f = f₀f₁⋯f_r.

## 2. The engine side: the stage invariants [(a)/(c): project definitions]

The project's per-read node record (Lean `MovesX.XNode`; MOVES §B2-DEF stage data
F.0–F.2; M06 §4.2's node-data list): at each read the engine records

    ν = (e, h, ℓ, s₀, u₀, sel, inc),   sel ∈ {⊥} ∪ {(g, μ) : 1 ≤ g, 1 ≤ μ, μg ≤ ℓ}

with e, h ≥ 1 coprime (the read side has slope −h/e in the stage frame,
horizontal lattice length eℓ, height hℓ, residual degree ℓ, initial point
(s₀, u₀)); sel = (g, μ) records the selected monic irreducible residual factor's
degree g and multiplicity μ; inc records whether the step is a genuine key-degree
increment. Row classification (T1: ℓ ≥ 2; T2: ℓ = 1, e ≥ 2, h ≥ 2; T3: ℓ = 1,
e ≥ 2, h = 1; T4: ℓ = 1, e = 1; T5: terminal), with the coherence laws: T2/T3
continuing nodes are increments, T4 continuing nodes are recenterings. The
certified population at the ALIGN state ⟨true, false⟩ is exactly {T1 increments}
∪ {T2 nodes}; dCert(H) counts them.

Stage structure carried behind the node (MOVES F.0–F.2, dual-accepted as
SYMBOLIC-engine theorems per DELTA-1 §D1.5(e)): a monic key Φ_i; a stage side
valuation u_i with weight lattice (1/(e₁⋯e_{i−1}))ℤ; the digit algebra
𝒟 = F_i[u]/(u^{e_b} − ζ) with the anchor-unit normalization converting the stage
residual to an F_i-polynomial before factor selection (F.2: "normalizing by the
anchor unit u_{ρ₀} converts R to an F-polynomial; ψ is taken irreducible in F[z],
ψ ≠ z"); the standard lift Φ̂_{i+1} built from the selected ψ̂_i by the explicit
slot construction (F.2/B1.3), a FUNCTION of the accumulated discrete data. At
stage 1 the digit algebra is F₁ itself (e_b = 1) and u₁ = v.

The dictionary data to be matched are therefore: per level, (e_i, h_i, ℓ_i,
g_i, μ_i) and the derived accumulations accE_k = ∏_{i≤k} e_i, accF_k = f₀·∏ g_i,
key degrees deg Φ̂, and the stage weights — against GMN's (e_i, h_i, d_i, f_i,
ω), m_r, and v_r/V_r.

## 3. THE CARRIER DESIGN (the D-5 deliverable) [(c) claimed new — design]

V5's architectural defect (1), absorbed into D-5: "K-DICT lacks a coherent
carrier/equality design". The design, as numbered decisions:

* **DES-1 (domain objects).** The domain of Θ is the set 𝔈 = 𝔈_n of **dressed
  histories** 𝐇 = (ρ₀; ν₁, …, ν_k): a level-0 record ρ₀ = (ψ̂₀, a₀) with ψ̂₀ ∈
  F_q[y] monic irreducible (f₀ := deg ψ̂₀), a₀ ≥ 1; and nodes ν_i as in §2, each
  DRESSED with the selected residual polynomial ψ̂_i itself — a monic irreducible
  of degree g_i over the CONSTRUCTED field F_i (F₁ := F_q[y]/(ψ̂₀),
  F_{i+1} := F_i[z]/(ψ̂_i)) — not merely its degree. Well-formedness laws:
  **W1** (row laws of §2); **W2** (increment law, a D-5 pin): for continuing ν_i,
  inc_i = 1 ⇔ e_i·g_i ≥ 2 (consistent with W1: T2/T3 force e ≥ 2; T4 forces
  e = g = 1); **W3** (interior non-completeness): μ_i ≥ 2 for i < k, and a₀ ≥ 2
  whenever k ≥ 1; **W4**: ψ̂_i monic irreducible in F_i[z], deg ψ̂_i = g_i,
  ψ̂_i ≠ z; **W5**: only the last node may be terminal. The dressing is
  canonical relative to the engine's pinned anchor-unit normalization (F.2) —
  the residual factor an engine run selects IS an F_i-polynomial after that
  normalization, so the dressing is a function of the run, not a choice.
* **DES-2 (domain equality).** Literal componentwise equality of the discrete
  data. Every constituent lives in an explicitly constructed countable set (ℕ's;
  polynomials over the CONSTRUCTED F_i — iterated explicit quotients, no
  isomorphism classes); equality is decidable. Truncation: every prefix of a
  well-formed dressed history is one (W3/W5 are prefix-stable for prefixes
  ending at a continuing node).
* **DES-3 (codomain objects; dissolving Def 4.15's choice-dependence).** Define
  the **pinned representative family** F_rep by recursion: Lift₀(ψ̂₀) := the
  canonical coefficientwise lift of ψ̂₀ (the engine's `liftKey`: each residue
  coefficient to its distinguished representative); Lift_i(c) := the engine's
  standard lift Φ̂ of the length-i chain datum c (F.2/B1.3 — a function of c
  alone). The codomain 𝔗 is the set of GMN **type chains over F_rep**: chains
  t^{(0)} ≺ t^{(1)} ≺ ⋯ where t^{(i)} = (φ₁; λ₁, φ₂; ⋯; λ_i, ψ_i) with
  φ_{j+1} := Lift_j(discrete data of t^{(j)}). Because every φ is a FUNCTION of
  the discrete data (ψ₀; (λ_j, ψ_j)_j), a codomain element IS its discrete
  datum. F_rep has, by construction, exactly the shape of GMN's §4.1 Convention
  (one lift per ψ₀; one representative per chain; functionality = universal
  fixedness); that its members are GMN-ADMISSIBLE (Def 2.12 representatives) is
  clause (iv): proved at level 0 (Theorem 1 (D4)), open lemma OL-2a-1 at levels
  ≥ 1. Under the Convention, N_r^−(f), R_r, t_r(f), ind_t(f), ind_r(f) are all
  single-valued — Def 4.15's warning is dissolved, not ignored.
* **DES-4 (codomain equality).** Equality of discrete data ((ψ̂₀; (λ_i, ψ̂_i)_i)).
  NO quotient by Okutsu/OM-equivalence is imposed: that quotient is O-2b content
  (σ-invariance, LIT-5 consumption) and will be a further quotient OF this
  carrier; taking it here would smuggle O-2b (the V4/M15 trap, avoided).
* **DES-5 (truncation compatibility).** Θ (§4) is defined by structural
  recursion, so Θ(prefix) = truncation of Θ(𝐇) — the compatibility across
  levels D-5 demands, for free from the design.
* **DES-6 (the realization interface).** f enters ONLY through the predicate
  Cons_f ⊂ 𝔈 (§4, "GMN-consistency"), defined by GMN-side data of f — never
  through "the run of the classifier on f". O-3's realized runs will map into 𝔈
  by forgetting (each run emits exactly the ρ₀/ν data, dressed via the anchor
  normalization); the seam "engine-emitted ⇒ Cons_f" is clause (iii)'s content
  (Theorem 1 (D3) at order ≤ 1; OL-2a-2/3 at order ≥ 2). Lean re-key
  recommendation: the interface field `inStratum f H` should be typed as
  ∃ dressing 𝐇 of H with Cons_f(𝐇) — this is the mathematical answer to M15's
  OL-4 (stratum scope): the row's quantifier then ranges over exactly the
  histories Theorem 2(C) covers.
* **DES-7 (what the carrier is NOT).** No f in the domain; no realized-run
  predicate; no measure; no Okutsu quotient; no "canonical value" of ind_t
  without the pinned family. W2/W3 are carrier LAWS here; that the intended
  engine's emitted histories satisfy them (inc records key-degree growth; the
  (τ-irr) rule halts at μ = 1, so interior reads have μ ≥ 2) is part of the
  O-3-side seam, not of this leaf.

## 4. The dictionary Θ and the statement DICT(n)

**Definition (Θ).** For 𝐇 = (ρ₀; ν₁, …, ν_k) ∈ 𝔈 with continuing nodes
ν₁, …, ν_{k'} (k' = k or k−1 by W5): Θ(𝐇) := the type chain over F_rep with
ψ₀ := ψ̂₀, and for 1 ≤ i ≤ k': λ_i := −h_i/e_i, ψ_i := ψ̂_i,
φ_{i+1} := Lift_i(⋯). The **placement** of node ν_i is the GMN order i — the
identity on continuing-node indices. [(c) design; this REPLACES M15's OL-1
"find an injective placement": every continuing node — recenterings included —
extends the strict GMN tuple by one order (a same-degree step is a GMN order
with e_i f_i = 1; the paper's own §4.3 example does exactly this, cf. M15 §7),
so injectivity of the placement is free BY CONSTRUCTION, and only the CHARGE
(ind ≥ 1) distinguishes certified nodes.]

**Definition (Cons_f).** For f ∈ O[x] monic separable (disc f ≠ 0) and 𝐇 ∈ 𝔈:
Cons_f(𝐇) iff (c0) ord_{ψ̂₀}(f̄) = a₀ ≥ 1; and for 1 ≤ i ≤ k' inductively,
with t^{(i−1)} := the order-(i−1) truncation of Θ(𝐇) (a valid type over F_rep —
see Theorem 2(A)): (c1) N_i^−(f) (over F_rep) has a side S_i of slope −h_i/e_i
with initial point (s_i, u_i-normalized) and degree d(S_i) = ℓ_i; (c2)
ord_{ψ̂_i}(R_{λ_i}(f)) = μ_i. [All clauses are GMN-defined data of f — no
realization semantics.]

**DICT(n) — the O-2a dictionary statement.** For every prime power q, every
monic separable f over O, and every 𝐇 ∈ 𝔈_n with Cons_f(𝐇):
(i) **invariant matching**: the GMN invariants of Θ(𝐇) are the engine
    accumulations — e_i, h_i, f_i = g_i levelwise; [F_{i+1} : F_q] = f₀⋯f_i;
    m_{i+1} = accE_i·accF_i; V-recursion V_{i+1} = e_i f_i (e_i V_i + h_i) for
    the pinned lifts; **saturation**: at the last read, μ_{k'} = 1 ⇔ the
    cluster degree equals accE·accF, and then the certified factor is
    irreducible with (e, f) = (accE_{k'}, accF_{k'});
(ii) **order placement**: the identity placement is injective and lands in
    genuine orders: t^{(i−1)} ∈ t_{i−1}(f) for all i ≤ k';
(iii) **normalization crossing + charge**: the engine's raw-frame read data at
    each level ARE the (c1)/(c2) data of N_i^−(f) in v_i-normalized coordinates
    (so engine-emitted histories satisfy Cons_f), and each CERTIFIED node's
    order is charged: ind_{t^{(i−1)}}(f) ≥ 1; consequently
    dCert(𝐇) ≤ ind(f);
(iv) **admissibility**: F_rep is one universally-fixed GMN-admissible
    representative family (each Lift_i(c) a Def-2.12 representative of its
    chain, with the (16) normalization).
Also (0) **well-posedness**: Θ total on 𝔈, truncation-compatible, and injective
on Cons_f-histories for each fixed f.

Status: order ≤ 1 — PROVED (Theorem 1, §5). All orders — Theorem 2 (§6):
(0)/(i)/(ii) and the charge of (iii) PROVED given Cons_f and OL-2a-1; the
engine-seam half of (iii) and (iv) at levels ≥ 1 are the open lemmas
OL-2a-1/2/3. The (†) consumption is the LITERATURE face (Thm 4.18(1)), to be
declared per M15 §6's axiom shape, never wider.

## 5. Theorem 1: the dictionary at order ≤ 1 [(b) new proof of known content,
stated at the project carrier; the order-1 mathematics is classical Ore]

**Theorem 1.** Let q be a prime power, K/ℚ_p finite with residue field F_q
(instance: K = ℚ_p, q = p), f ∈ O[x] monic of degree n with disc f ≠ 0, and
𝐇 = (ρ₀) or (ρ₀; ν₁) a dressed history of length ≤ 1 with Cons_f(𝐇). Then all
clauses of DICT(n) hold for 𝐇; moreover dCert(𝐇) ≤ ind₁(f) ≤ ind(f).

*Proof.* Write ψ₀ := ψ̂₀, f₀ = deg ψ₀, φ₁ := Lift₀(ψ₀), a := a₀.

**(D4) = clause (iv) at level 0.** Lift₀(ψ₀) is monic and reduces to ψ₀ — by
GMN §1/§4.1 that is ALL an order-0 representative must be; Lift₀ is a function
of ψ₀, one lift per ψ₀, which is verbatim the first layer of the §4.1
Convention. So every order-1 object of f below (N₁^−, R_λ, t₀(f), ind_t, ind₁)
is well-defined and single-valued over F_rep. ∎(iv, level 0)

**(D3) = clause (iii), order-1 crossing.** At stage 1 the engine frame IS the
GMN frame: u₁ = v (F.0 stage-1 data), the weight lattice is ℤ, the digit algebra
is F₁ (e_b = 1), and the stage-1 window polygon of f is the lower hull of
{(j, v(b_j))} over the φ₁-adic development f = Σ b_j φ₁^j, deg b_j < f₀ — which
is definitionally N₁(f); its negative-slope part on abscissas [0, a] is N₁^−(f)
(v(b_j) ≥ 1 for j < a and v(b_a) = 0, since ψ₀^a ∥ f̄ makes the ψ₀-adic
development of f̄ vanish in degrees < a with nonzero a-th digit). The engine's
recorded (e₁, h₁, ℓ₁, s₁, u₁) are the side data of a side S of this hull —
i.e., of N₁^−(f): slope −h₁/e₁ in lowest terms, d(S) = ℓ₁. The engine's
residual read is, per slot j ∈ {0, …, ℓ₁}, the unit-part class
c_j = (b_{s+je₁}/π^{u_s−jh₁}) mod (π, ψ₀) ∈ F₁ when the point lies ON S and 0
otherwise (the anchor normalization at stage 1 is trivial: e_b = 1) — which is
GMN's order-1 residual coefficient (Def 2.20 at order 1 carries no twist: the
z-power normalization enters only at orders ≥ 2), so the engine residual equals
R_{λ₁}(f) on the nose, and the selected (ψ̂₁, μ₁) satisfy (c1)/(c2). Hence
engine-emitted length-≤1 histories satisfy Cons_f. [Corpus witnesses of the same
identification at the Lean level: `OM/NewtonPolygon`/`OM/Development` (the hull
and development), `OM/ResidualBridge` Theorems 1–3 (the descent reader IS GMN
Def 2.21's Σ C(·)Xᵗ at the develop-digit datum, at f₀ = 1, with the honest
μ = residualDeg+1 reconciliation and its recorded open Lean sub-target — a
Lean-side residue, not a gap in the mathematical identification above, which is
by inspection of the two definition sets.] ∎(iii, engine seam, order 1)

**(D1) = clause (i).** λ₁ = −h₁/e₁ with e₁, h₁ coprime positive (W-laws),
ψ̂₁ ∈ F₁[z] monic irreducible ≠ z (W4; under Cons_f automatic, since R_λ(f) is
never divisible by y): so Θ(𝐇) = (φ₁; λ₁, ψ̂₁) is a genuine order-1 type over
F_rep, with f₁ = deg ψ̂₁ = g₁, F₂ = F₁[z]/(ψ̂₁), [F₂ : F_q] = f₀f₁ (GMN §2.1),
m₂ = m₁e₁f₁ = f₀e₁g₁ = accE₁·accF₁. V-recursion: v₂(φ₁) = h₁ + e₁v₁(φ₁) and
v₁(φ₁) = v(φ₁) = 0 (monic with a unit coefficient), so V₂ = e₁f₁·v₂(φ₁) =
e₁f₁h₁ = e₁f₁(e₁·0 + h₁) — the displayed recursion at i = 1, for the
Thm-2.11-normalized representative (for Lift₁ itself this is OL-2a-1(c)).
**Saturation:** by Thm 1.15 the side S splits off the factor F_S with
N_φ(F_S) = S; by Thm 1.19 the choice ψ̂₁ with R_{λ₁}(f) ∼ ∏ ψ_i^{a_i} splits
F_S = ∏ G_i with R_{λ₁}(G_i) ∼ ψ_i^{a_i}; the residual degree of G_i is
a_i·deg ψ_i, so its side length is e₁·a_i f_i and deg G_i = m₁·e₁·a_i·f_i =
m₂·a_i. Thus the tracked cluster factor G := G_{ψ̂₁} has degree d = m₂·μ₁ =
(accE·accF)·μ₁, giving accE·accF = d ⇔ μ₁ = 1. If μ₁ = 1, Cor 1.20: G is
irreducible with e(L/K) = e₁ = accE₁ and f(L/K) = f₀·f₁ = accF₁. ∎(i)

**(D2) = clause (ii).** Placement is the identity on the ≤ 1 continuing node —
injective. Landing: t^{(0)} = ψ̂₀ ∈ t₀(f) since ω₁(f) = ord_{ψ₀}(f̄) = a ≥ 1
by (c0); if ν₁ exists then a ≥ 2 (W3), so t^{(0)} is non-complete and Θ(𝐇) ∈
t₁(f) by Def 3.10 ((c1)+(c2): λ₁ a slope of N₁^−(f), ψ̂₁ | R_{λ₁}(f)). ∎(ii)

**Charge + the bound.** Let ν₁ be certified, i.e. (W1/W2) T1 with e₁g₁ ≥ 2, or
T2. The side S is then T1 (ℓ ≥ 2) or T2 (ℓ = 1, e, h ≥ 2), and ind(S) =
½(EH − E − H + d) ≥ 1 by an explicit lattice witness [(b); the two-line algebra:
with E = eℓ, H = hℓ, d = ℓ, 2·ind(S) = ℓ(ehℓ + 1 − e − h), and Remark 4.14's
region contains, at T1, the ON-side integer point (s + e, u_s − h) (x > s ✓;
y − u_end = h(ℓ−1) > 0 ✓); at T2, the point (s + 1, u_end + 1) (h + e ≤ eh ⇔
(e−1)(h−1) ≥ 1 ✓)]. Then ind(N₁^−(f)) ≥ ind(S) (Remark 4.14: all summands of
Def 4.12 are ≥ 0), ind_{t^{(0)}}(f) = f₀·ind(N₁^−(f)) ≥ 1 (Def 4.15, r = 1),
ind₁(f) = Σ_{t ∈ t₀(f)} ind_t(f) ≥ ind_{t^{(0)}}(f) ≥ 1 (t^{(0)} ∈ t₀(f),
terms ≥ 0), and dCert(𝐇) ≤ 1 ≤ ind₁(f) ≤ ind(f) by Thm 4.18(1) at r = 1.
Histories with dCert = 0 are trivial. ∎(charge)

**(D0).** Totality/truncation: structural recursion. Injectivity on Cons_f
histories: Θ(𝐇) determines (ψ̂₀, e₁, h₁, ψ̂₁, g₁); Cons_f then pins a₀ =
ord_{ψ̂₀}(f̄), (s₁, u₁, ℓ₁) — a polygon has at most ONE side of a given slope —
and μ₁ = ord_{ψ̂₁}(R_{λ₁}(f)); inc₁ is pinned by W2. ∎ **(Theorem 1)**

Remark (T3/T4/recentering corner): an uncertified continuing ν₁ (T3, T4, or a
T1 recentering with e₁g₁ = 1) needs NO charge — its side has ind(S) = 0 exactly
in the T3/T4 cases (Remark 4.13's degenerate shapes: E = 1 or H = 1), which is
why the ⟨true, false⟩ state excludes it; a T1 recentering has ind(S) ≥ 1 but is
excluded anyway (the engine does not claim its charge — harmless for ≤).

## 6. Theorem 2: all orders — proof given three exactly-stated open lemmas

**OL-2a-1 (engine-lift admissibility + normalization). OPEN.** For every
well-formed chain datum c of order i ≥ 1 over F_rep, with type t = t^{(i)},
the engine's standard lift Φ̂_{i+1} = Lift_i(c) satisfies: (a) Φ̂_{i+1} ∈ O[x]
monic of degree m_{i+1} = m_i e_i f_i; (b) Φ̂_{i+1} is of type t with
R_i(Φ̂_{i+1}) ∼ ψ̂_i — i.e. a GMN Def-2.12 representative of t; (c)
v_{i+1}(Φ̂_{i+1}) = e_i f_i·v_{i+1}(Φ̂_i), i.e. V_{i+1} = e_i f_i(e_i V_i + h_i).
*Mechanism:* GMN Thm 2.11 proves existence of a representative with (a)–(c) by
the Prop 2.10 construction; the engine's lift differs by its choice of
weight-realizing slot monomials (F.2/B1.3), and (b) for it is the same residual
computation run over the engine's slot presentation. *Design note:* one could
instead pin Lift_i := GMN's own construction, making OL-2a-1 a citation — but
the engine READS against ITS lift, so the mismatch would reappear inside
OL-2a-2/3 with interest (Okutsu-equivalence transport = O-2b territory).
Adjudicated: keep the engine lift; OL-2a-1 is the honest seam. [= M15's OL-3.]

**OL-2a-2 (frame crossing at orders ≥ 2). OPEN.** For f monic separable and c a
Cons_f chain of order i ≥ 1 (well-defined given OL-2a-1): the engine's
stage-(i+1) window polygon of f — the lower hull of (j, u_{i+1}(B_j) +
j·w_{i+1}(Φ̂_{i+1})) over the Φ̂_{i+1}-development f = Σ B_j Φ̂_{i+1}^j, written
in the stage's integer slot coordinates — equals N_{i+1}^−(f) (Defs 2.3/2.5
over F_rep) up to the recorded translation; side-for-side with EQUAL lowest-term
(e, h), equal ℓ and initial data, hence equal T1–T4 classification. Load-bearing
sub-claim: u_{i+1} = v_{i+1}/(e₁⋯e_i) on development coefficients, so the two
frames differ by exactly the scaling the slot coordinates clear; the (e, h)
claim is about the lowest-term data AFTER the frames are correctly matched.
*Warning:* this is where stretch failures live — the corpus's compiled
HK52_stretchGate refutes a naive unguarded engine-internal vertex transport at
e′ ≥ 2 (factor-e′ stretch); that gate is adjacent evidence that OL-2a-2 must
pin frames explicitly, not a countermodel to the statement above. *Evidence:*
exact order-2 matches — M15 N4 (hand-derived v₂-frame reads confirmed by ind
arithmetic at 9 configurations), this session's F3B (§8); the sealed Case-J
12-strata transport gate. [= M15's OL-2, sharpened to the explicit frame map.]

**OL-2a-3 (residual identification at orders ≥ 2). OPEN.** Same setting: the
engine's anchor-normalized stage residual of f at the read side equals
R_{λ_{i+1}}(f) (Def 2.21 over F_rep) up to a nonzero constant of F_{i+1} —
hence equal irreducible-factor multisets with equal multiplicities — the
engine's tower F_{i+1} = F_i[z]/(ψ̂_i) being GMN's tower on the nose (DES-1).
*Mechanism:* the engine's F.1 side-residual calculus (anchor congruence +
(S-Ore) multiplicativity) against GMN Defs 2.19–2.21; the z_{i−1}-power twists
in Def 2.20 must be absorbed by the anchor-unit normalization. *Shared-lemma
discipline:* this is the same exponent-map content as O-9's OL-B (twisted
residues) — ONE proof should serve both consumers. *Corpus state:* order-1
instance machine-checked in shape (ResidualBridge); the order-≥2 extension
reader is explicitly recorded as not yet existing (`OM/OrderTwoContext`) — the
lemma is genuinely open even at the definition level on the Lean side.

**Theorem 2.** Let f ∈ O[x] be monic separable, 𝐇 ∈ 𝔈_n. Then:
(A) [unconditional] Θ is total on 𝔈 and truncation-compatible; and if Cons_f(𝐇)
    (with OL-2a-1 granting well-definedness of the order-≥2 clauses), every
    truncation lands in the type tree: t^{(i)} ∈ t_i(f) for 0 ≤ i ≤ k'−1... and
    t^{(i−1)} is non-complete for i ≤ k'; the identity placement is injective;
    Θ is injective on Cons_f-histories.
(B) [Cons_f + OL-2a-1] clause (i) in full: levelwise (e_i, h_i, f_i = g_i);
    [F_{i+1} : F_q] = f₀⋯f_i; m_{i+1} = accE_i·accF_i; the V-recursion;
    saturation at the last read with the Cor 3.8 leaf data
    (e, f) = (accE_{k'}, accF_{k'}).
(C) [Cons_f + OL-2a-1] the charge: every certified ν_i has
    ind_{t^{(i−1)}}(f) ≥ 1, distinct certified nodes charge distinct orders,
    and dCert(𝐇) ≤ Σ_{r=1}^{k'} ind_r(f) ≤ ind(f).
(D) [OL-2a-1 + OL-2a-2 + OL-2a-3] every history emitted by the engine's stage
    flow on f is (dressed to) a Cons_f history — so (B)/(C) apply to the
    intended instance, and the KE8 carrier is inhabited (§7).

*Proof.* (A) Totality/truncation: recursion (DES-5). Landing: induction on i.
Base: ω₁(f) = a₀ ≥ 1 gives t^{(0)} ∈ t₀(f); k ≥ 1 forces a₀ ≥ 2 (W3), i.e.
non-completeness. Step: t^{(i)} sprouts from the non-complete t^{(i−1)} ∈
t_{i−1}(f) by the finite slope λ_i of N_i^−(f) ((c1)) and ψ̂_i | R_{λ_i}(f)
((c2), μ_i ≥ 1), which is Def 3.10 membership verbatim; interior
non-completeness is W3 (μ_i ≥ 2 ⇔ ω_{i+1}(f) ≥ 2). Injectivity: as in (D0),
levelwise — a polygon has one side per slope, and ord pins μ_i; a₀, s, u, ℓ, inc
pinned as before. Placement injective: identity on indices.
(B) Induction on i. The levelwise identifications are the construction of Θ
(λ_i := −h_i/e_i lowest terms = the engine's coprime pair; f_i := deg ψ̂_i =
g_i by W4); the tower and m-recursion are GMN §2.1 arithmetic over F_rep, with
deg Φ̂_{i+1} = m_{i+1} from OL-2a-1(a); the V-recursion is OL-2a-1(c) + Prop
2.7. Saturation: t^{(k'−1)} ∈ t_{k'−1}(f) non-complete... the last read's
selected (ψ̂_{k'}, μ_{k'}) give ω_{k'+1}(f) = μ_{k'} w.r.t. t^{(k')}; Def 2.3:
the tracked cluster factor f_{t^{(k')}} has degree m_{k'+1}·μ_{k'} =
(accE·accF)·μ_{k'}, so accE·accF = d ⇔ μ_{k'} = 1; when μ_{k'} = 1, Def 3.9 +
Cor 3.8 give irreducibility and (e, f) = (e₁⋯e_{k'}, f₀⋯f_{k'}) =
(accE_{k'}, accF_{k'}).
(C) Certified ν_i is T1-with-e_ig_i ≥ 2 or T2 (W1/W2); by Cons_f (c1) the side
S_i of N_i^−(f) has the engine's (e_i, h_i, ℓ_i), so it is a T1/T2 side and
ind(S_i) ≥ 1 by the Theorem-1 lattice witnesses (pure Def-4.12 arithmetic —
order-agnostic); ind(N_i^−(f)) ≥ ind(S_i) ≥ 1 (Remark 4.14 nonnegativity);
ind_{t^{(i−1)}}(f) = f₀⋯f_{i−2}·... = f₀⋯f_{i−1}·ind(N_i^−(f))/f_{i-1}-free
form per Def 4.15 (the factor is a product of positive integers), so
ind_{t^{(i−1)}}(f) ≥ 1; ind_i(f) ≥ ind_{t^{(i−1)}}(f) since t^{(i−1)} ∈
t_{i−1}(f) ((A)) and Def 4.15's sum has nonnegative terms. Distinct certified
nodes sit at distinct orders (identity placement), so
dCert(𝐇) = #{certified i} ≤ Σ_{i certified} ind_i(f) ≤ Σ_{r=1}^{k'} ind_r(f)
≤ ind(f), the last step Thm 4.18(1) at r = k' [the (†) face — the LITERATURE
consumption, to be declared exactly as M15 §6's `AX_GMN_index_finsum`].
(D) Induction along the history: at each level, OL-2a-2 says the engine's read
side data are (c1) data of N_{i+1}^−(f); OL-2a-3 says the engine's selected
residual factor and multiplicity are (c2) data; OL-2a-1 keeps the next level's
GMN objects defined over F_rep. Base level: Theorem 1 (D3), unconditional. ∎

Corrigendum note on the Def 4.15 display in (C): ind_{t^{(i−1)}}(f) :=
f₀f₁⋯f_{i−2}·ind(N_i^−(f)) per Def 4.15 at r = i (the twist product runs over
the type's residual degrees f₀ … f_{r−1} with r = i, top factor f_{i−1});
either way it is a product of POSITIVE integers times ind(N_i^−(f)) ≥ 1 — the
charge is insensitive to the exact truncation of the twist product. The
falsifier F3B pins the product convention numerically: ind = f₀·ind(N₁^−) +
f₀f₁·ind(N₂^−) = 2·2 + 2·(2k−1) = 4k + 2, matched exactly at k = 1, 2, 3.

## 7. Consumers served

* **K-10 / `cl15_align` (the ALIGN row).** Theorem 2(C)+(D) inhabits the
  machine-checked KE8 carrier `GmnOrderAccounting` at the intended instance:
  orderInd f r := ind_r(f) over F_rep (0 at r = 0); finsum_le := (†) [the M15
  axiom face]; place := node-index (identity); place_inj := (A); place_charged
  := (C). The row follows by the proved `x1aAlignInc_of_orderAccounting`. The
  `inStratum` scope pin is DES-6 (M15's OL-4 resolved by re-key, not by proof).
* **O-6 Lemma A (key-degree budget, e·g form).** W2 + (B): every certified T1/T2
  increment multiplies the key degree by e_i·g_i ≥ 2, so ≤ ⌊log₂ n⌋ increments —
  the "e·g strengthening through O-2" the tree names is exactly W2 + m-recursion.
* **O-5 (LEAF).** The saturation clause of (B) is verbatim the (OM-SAT)
  interface (M06 §4.2): accE·accF = d ⇔ ω = 1, leaf data (accE, accF) — LIT-4
  is consumed through THIS dictionary, as the tree requires.
* **O-7 (X1 alignment leg)** consumes (C)'s per-order charging; **D-11/O-12**
  untouched (value-side).

## 8. Numerics executed this session (falsifier-first; script
`lean/notes/openmath/O2a_order1_check.gp`, gp; plus a 20-line python re-run)

* **F1 (EXECUTED, PASS — the Theorem-1 falsifier).** 3600 monic f over ℤ read at
  p ∈ {2,3,5}, n ∈ {2,…,6} (120 plain-random + 120 forced-repeated-residue per
  (p, n); seed 20260731). For each f: full order-1 read per repeated residue
  factor (canonical lift, development, lower hull, per-side (e,h,ℓ), residual
  over F_{p^{f₀}} via unit-part classes with gp `ffgen`, factorization). For the
  3432 fully order-1-decided f, the predicted (e,f) multiset (Hensel (1, f₀) +
  Cor 1.20 (e, f₀·deg ψ)) was compared against `idealprimedec` ground truth
  (orders maximal at p): **0 mismatches, 0 degree-checksum failures**. Any
  mismatch would refute Theorem 1's (D1)/(D3).
* **F2 (EXECUTED, PASS — Thm 4.18(1) at r = 1; M15's proposed N3, first
  execution).** For ALL 3600 samples: ind₁(f) = Σ f₀·ind(N₁^−) (Def 4.12 with
  cross terms) vs the étale-algebra ind_p(f) (per-factor (v_p(disc g) −
  v_p(disc K_g))/2 + pairwise resultant valuations): **0 violations** of
  ind₁ ≤ ind_p.
* **F3 (EXECUTED, PASS — order-2 invariant matching, the order-≥2 statement's
  instances).** Family A: f = (x²−p)² − p^{2k+1}x, p ∈ {2,3,5}, k ∈ {1,2,3}:
  predicted chain (e₁,f₁) = (2,1) → (e₂,f₂) = (2,1), saturated: (e,f) = (4,1);
  ground truth 9/9. Family B (wild, f₀ = 2, hand-derived in full): p = 2,
  φ₁ = x²+x+1, f = (φ₁² − 2x)² − 2^{2k+1}φ₁; order-1 read (2,1,2) with residual
  z² + (w+1) = (z+w)² over F₄ (w² = w+1), selected (g,μ) = (1,2), T1 increment;
  φ₂ = φ₁² − 2x IS a representative (its own polygon (0,1)–(2,0) has residual
  z + w ∼ ψ̂₁; deg = 4 = m₂; v₂(φ₂) = 2 = e₁f₁v₂(φ₁)); order-2 read
  (2, 4k−1, 1) T2, saturated: (e,f) = (accE, accF) = (4, 2): ground truth 3/3.
  Sharper: measured ind₂(f) = 6, 10, 14 = 4k+2 = f₀·ind(N₁^−) + f₀f₁·ind(N₂^−)
  = 2·2 + 2·(2k−1) EXACTLY — confirming Def 4.15's twist factor (without it the
  prediction would be 2k+1: the twist is falsifiable and survived) and, via
  Thm 4.18(2), consistent with saturation at order 2 (ind₃ = 0). dCert = 2 ≤
  ind ✓ at all k.
* **F4 (EXECUTED, PASS — the ind2/Def-4.12 lattice dictionary re-run).** The
  M15 N1 check re-executed: 1548 configurations (coprime e, h ≤ 8, ℓ ≤ 6,
  offsets), 2·|region| = EH − E − H + d = the T1/T2/T3/T4 table value, and
  region ≥ 1 exactly on T1/T2: **0 violations** on both counts.

## 9. Honesty ledger

**Proved here (order ≤ 1, Theorem 1):** all four O-2a clauses + the
dCert ≤ ind(f) charge, at the declared carrier, over any finite K/ℚ_p, from the
pinned citations only. [(b): the mathematics is classical Ore/GMN order-1; the
carrier-level statement and its falsifier are new.]

**Proved here (all orders, Theorem 2):** well-posedness, landing, injectivity,
invariant matching, saturation, charging, and the ALIGN assembly — GIVEN Cons_f
and OL-2a-1; plus the engine seam GIVEN OL-2a-1/2/3. [(c) the reduction and
carrier design; the placement-by-construction idea replaces M15's OL-1.]

**Open (the exact residue of O-2a):** OL-2a-1 (lift admissibility +
normalization), OL-2a-2 (frame crossing, orders ≥ 2), OL-2a-3 (residual
identification, orders ≥ 2). M15's OL-1 is DISSOLVED (placement is by
construction); M15's OL-4 is RESOLVED as the DES-6 re-key, not a theorem.
W2/W3 are carrier laws; "engine-emitted histories are well-formed" is O-3-side.

**Literature consumption:** exactly (†) = Thm 4.18(1) + Def 4.15 nonnegativity +
Def 4.11, keyed to F_rep (M15 §6's `AX_GMN_index_finsum` shape) — NOT the KE8
carrier (M15 §4's axiom-scoping trap re-affirmed); plus the order-1 theorems
(Thm 1.15/1.19/Cor 1.20), Thm 2.11/Def 2.12, Cor 3.8/Def 3.9/Def 3.10 — all
LITERATURE-CONDITIONAL pending the printed-TAMS confirmation (DELTA-1 D1.5(b)).

**Not attempted (out of scope by D-13):** O-2b (trace/tree correspondence with
the published Montes flow; σ-invariance under Okutsu equivalence); O-3
realization; any BNS/LIT-5 consumption.

## VERDICT

O-2a: **carrier design DELIVERED (DES-1..7); order ≤ 1 PROVED (Theorem 1);
order ≥ 2 REDUCED with complete conditional proof (Theorem 2) to the three
exactly-stated open lemmas OL-2a-1/2/3.** Falsifiers executed first, 4/4 pass
(3600-poly sweep 0 mismatches; first execution of the r = 1 index inequality
0 violations; order-2 families exact incl. the Def-4.15 twist). Status
recommendation for the tree: O-2a = PROVED-UNVERIFIED at order ≤ 1 scope +
REDUCED at order ≥ 2 (three named lemmas), pending hostile verification of
`O2a_phaseB_verifybrief.md`.
