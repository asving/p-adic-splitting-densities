# ITER-LAW-3 PROOF — the level-3 composed cocycle law proved on the 3-read standard-lift harness class via the CONVERGED GAUGE ROUTE: c₃(γ,γ′) = z̄^{δ₃}·z₂^{D₂}·z₁^{D₁} by L6-(3) (anchor value = ε-chain) + W-MULT-(3) (single inflated top carry), one Bézout kernel per level, the accepted order-2 L6/L7 consumed verbatim on the inner digit — proved on ALL pairs except one sharp double-cascade corner (empty at e₀ ≤ 2), boxed OPEN as (W-MULT-3-DCX)

**Unit:** WAVE-19 UNIT 2 = the (ITER-LAW-3) proof compose, per the convergence
judgment `L3CONVERGENCE_2026-08-08.md` S3 (the per-level gauge-normalization
strategy) and its S4 decision default ("the compose/proof unit for (ITER-LAW-3)
via L6-(n)+W-MULT-(n) can proceed IN PARALLEL with the n = 4 probe"). Genre:
attempt-grade leaf proof note in the accepted ITERLAW genre (finite algebra
executed in full; acceptance counter 0 — the 2-clean hostile-pass arc is the
NEXT wave's; this note is composed verification-ready: explicit claim DAG in
S8, every citation pinned to note-section or ledger-block). Author: Fable,
wave-19 unit 2, campaign date 2026-08-08 (wallclock 2026-08-03).

**Statement of record being proved:** the sealed PRIMARY candidate
(ITER-LAW-3) of `ITERLAWR_PROBE_2026-08-08.md` S1 — measured law at
0 violations / 123,564 sealed samples (103,772 run + 19,792 m4 supplement,
ITERLAWR S5) and ≈ 133k samples across six decorrelated methods
(L3CONVERGENCE S1 row 3, CONVERGED 6/6) — here upgraded from measured law to
PROVED on the class below, except on the displayed DCX corner where it stays
an instance-true open lemma. Until this note passes the 2-clean hostile bar,
its own standing is: proof attempt; (ITER-LAW-3) remains formally
conjecture-grade at the campaign level, the accepted order-2 ITER-LAW being
the only PROVED-AND-ACCEPTED rung.

**The accepted order-2 base (citation PASTED from the ledger defined-term
block, `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "ITER-LAW ACCEPTED —
2026-08-03"):** "Scope as accepted: the harness tower class (superset of
DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence restricted to
E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂)
wrapper rides the accepted GRB retarget; orders ≥ 3 untouched." This unit
works in the third residual's territory and CONSUMES the accepted theorem: the
proved clauses L1–L7 + Lemma EXP of `ITERLAW_2026-08-08.md` (cited below as
[IL S2]/[IL S3]/[IL S4]) are consumed freely with citation, per the wave-19
charter. Nothing here edits the accepted note, the sealed prereg, or any
sealed artifact.

**PRINT-CONSUMPTION DISPLAY (decorrelation position).** This note consumes NO
printed formula and NO text extraction. Every object below is consumed as a
DEFINITION — the harness calculus of `verification/openmath/grb_order2_check.py`
(eq12/bezout :448–463; standard lift Φ₁ :499–507; R1w :556, eps1 reading C
:587, R2w :594; realize1 :632; build_Phi2 :648) and
`verification/openmath/strata3_probe.py` (Tower3 :225; eps2 :248; R2v :255;
w3 :266; R3w :278), plus val₃ per `iterlawr_probe.py` :137 (val₃(f) :=
Σⱼ R3w(f)ⱼ·z̄^j). These are the exact pins ITERLAWR S0 declares as the harness
of record. Print faithfulness (FGMN operators, Def 3.15/3.16, GMN conventions)
lives upstream in the accepted GRB/TR3 arcs and is NOT consumed: a reader who
distrusts every extraction can check this proof end-to-end from the code-level
definitions.

## S0. Setting, calculus, statement, and status

### S0.1 The 3-read standard-lift harness class (the class pin, E-positivity spelled)

O a DVR with uniformizer π, residue field k₀, valuation w₀ (extended to O[x]
coefficientwise — Gauss content; harness instances ℤ₂, ℤ₃, F₂[[t]], F₃[[t]],
but the proof is ring-blind: any DVR with the stated data). Tower data:

* Φ₀ ∈ O[x] monic, deg Φ₀ = d₀ ≥ 1, w₀(Φ₀) = 0, reduction φ̄ irreducible over
  k₀; K₀ := k₀[X]/(φ̄); res: {b : deg b < d₀, w₀(b) ≥ δ} → K₀, b ↦ class of
  b/π^δ; lift = the coefficientwise degree-< d₀ lift K₀ → O[x].
* Read 0: e₀ ≥ 1, h₀ ≥ 1, gcd(e₀,h₀) = 1; ψ₀ ∈ K₀[y] monic irreducible,
  deg ψ₀ = g₀ ≥ 1, ψ₀(0) ≠ 0; K₁ := K₀[z₁]/(ψ₀).
* Φ₁ := the STANDARD LIFT Σ_{k=0}^{g₀} lift(ψ₀,k)·π^{(g₀−k)h₀}·Φ₀^{e₀k}
  (grb_order2_check :499–507); deg Φ₁ = e₀g₀d₀; w₁Φ₁ := e₀g₀h₀.
* Read 1: e₁ ≥ 1, h₁ ≥ 1, gcd(e₁,h₁) = 1; ψ₁ ∈ K₁[y] monic irreducible,
  deg ψ₁ = g₁ ≥ 1, ψ₁(0) ≠ 0; K₂ := K₁[z₂]/(ψ₁); γ₂ := e₁·w₁Φ₁ + h₁.
* Φ₂ := the CANONICAL ε₁-CORRECTED LIFT (build_Phi2, :648–658):
  Φ₂ = Σ_{k ≤ g₁, ψ₁ₖ ≠ 0} C_k·Φ₁^{e₁k}, C_{g₁} = 1 and, for k < g₁,
  C_k := realize1(ε₁((g₁−k)γ₂)^{−1}·ψ₁ₖ, (g₁−k)γ₂) (realize1 :632–644; the
  well-definedness of every C_k on this class is Lemma WELL-DEF, S4.0).
  deg Φ₂ = e₁g₁·deg Φ₁; w₂Φ₂ := e₁g₁γ₂.
* Read 2: e₂ ≥ 1, h₂ ≥ 1, gcd(e₂,h₂) = 1; ψ₂ ∈ K₂[y] monic irreducible,
  deg ψ₂ = g₂ ≥ 1, ψ₂(0) ≠ 0; K₃ := K₂[z̄]/(ψ₂); γ₃ := e₂·w₂Φ₂ + h₂.
* E₃ := e₀e₁e₂; normalized Bézout pairs (ℓ₀,ℓ₀′), (ℓ₁,ℓ₁′), (ℓ₂,ℓ₂′):
  ℓⱼhⱼ + ℓⱼ′eⱼ = 1, 0 ≤ ℓⱼ < eⱼ (bezout :448; ℓⱼ = 0, ℓⱼ′ = 1 at eⱼ = 1).

E-positivity, spelled: every eⱼ ≥ 1 individually; NO joint constraint
(E₃ > 1 is NOT assumed). CLASS-COINCIDENCE DISPLAY (the VC36b/ITERLAW-erratum
lesson, applied proactively): the sealed prereg's class pin (ITERLAWR S0
"Class pin") imposes the same per-read conditions and no E₃ floor, so the
class proved here IS the sealed statement's class on the nose; the sealed
ROSTER additionally has E₃ ≥ 4 throughout, so all instance evidence sits in
the E₃ ≥ 4 part; the fully-degenerate legs (some eⱼ = 1, down to E₃ = 1,
where the corresponding carries are identically trivial) are covered by this
proof as honest degenerations (COR-3), not as extrapolated instance claims
**[errata r1: coverage is on the proved perimeter — the e₂ = 1 / e₁ = 1
degenerations do NOT evacuate DCX (S6.3 erratum); it is unconditional
exactly where DCX is empty, e₀ ≤ 2]**.
The (ITER-LAW-LIFT) residual propagates verbatim: Φ₁ standard, Φ₂ canonical
ε₁-corrected — nothing is claimed for any other lawful lift at any level
(S7; the measured lift-sensitivity is exactly LIFT-DEV-3, L3XCHECK S7).

### S0.2 The calculus (verbatim semantics of the pinned code)

eq-(12-int): for β ∈ ℤ and a read (e,h), (s(β|e,h), u(β|e,h)) is the unique
pair with u·e + s·h = β, 0 ≤ s < e. Abbreviations: (s(·),u(·)) := level-1
data at (e₀,h₀); (s₂(·),u₂(·)) := at (e₁,h₁); (s₃(·),u₃(·)) := at (e₂,h₂).

* w₁(A) := min_k{e₀·w₀(bₖ) + k·h₀} over the Φ₀-development A = Σ bₖΦ₀^k
  (defined for all A ∈ O[x], A ≠ 0).
* ε₁(β) := z₁^{ℓ₀′s(β) − ℓ₀u(β)} ∈ K₁^×; R₁-read at β of a digit a
  (deg a < deg Φ₁, w₁(a) ≥ β): R_{1,β}(a)(z₁) := Σ_{m≥0}
  res(b_{s(β)+me₀}/π^{u(β)−mh₀})·z₁^m, a Φ₀-digit contributing iff its w₀
  equals u(β)−mh₀ exactly (R1w :556; res is additive and kills strict
  excess — the only base facts consumed, as in [IL S1]).
* w₂(f) := min_j{e₁·w₁(aⱼ) + j·γ₂} over the Φ₁-development f = Σ aⱼΦ₁^j
  (all f ∈ O[x], f ≠ 0). Level-2 read at γ := w₂(f): slot grid
  sⱼ = s₂(γ) + je₁, slot weights γⱼ = (γ − sⱼγ₂)/e₁; Cⱼ :=
  ε₁(γⱼ)·R_{1,γⱼ}(a_{sⱼ})(z₁) if w₁(a_{sⱼ}) = γⱼ (on-line), else 0 (R2w
  :594). R2v(f) := Σⱼ Cⱼ·z₂^j ∈ K₂ (Tower3.R2v :255 — this is the accepted
  note's val with the letter renamed z̄ ↦ z₂).
* ε₂(β) := z₂^{ℓ₁′s₂(β) − ℓ₁u₂(β)} ∈ K₂^× (eps2 :248 — reading C one level
  up). w₃(f) := min_j{e₂·w₂(Aⱼ) + j·γ₃} over the Φ₂-development f = Σ AⱼΦ₂^j
  (w3_data :266). Level-3 read at γ := w₃(f): grid sⱼ = s₃(γ) + je₂, slot
  weights γⱼ = (γ − sⱼγ₃)/e₂; Cⱼ := ε₂(γⱼ)·R2v(A_{sⱼ}) if w₂(A_{sⱼ}) = γⱼ,
  else 0 (R3w :278). **val₃(f) := Σⱼ Cⱼ·z̄^j ∈ K₃** (iterlawr_probe :137).

### S0.3 Anchors, window, cocycle (the iterated eq-(12-int) split)

For γ ∈ ℤ (ITERLAWR S0, verbatim):

    (s₃,u₃) := (s₃(γ), u₃(γ));   β₂(γ) := u₃ − s₃·w₂Φ₂   [γ = e₂β₂ + s₃γ₃]
    (s₂,u₂) at β₂(γ);            β₁(γ) := u₂(β₂) − s₂(β₂)·w₁Φ₁
                                                          [β₂ = e₁β₁ + s₂γ₂]
    (s₁,u₁) at β₁(γ):            s₁(γ) := s(β₁(γ)), u₁(γ) := u(β₁(γ)).

ABBREVIATION (as in the sealed display): s₂(γ) := s₂(β₂(γ)) and
s₁(γ) := s(β₁(γ)) whenever the argument is an anchor index γ; the level of
the split is always the subscript's.

Anchor φ_γ := π^{u₁(γ)}·Φ₀^{s₁(γ)}·Φ₁^{s₂(γ)}·Φ₂^{s₃(γ)}; window
W₃ := {γ ∈ ℤ : u₁(γ) ≥ 0}; cocycle on anchors, for γ, γ′ ∈ W₃ (γ+γ′ ∈ W₃ by
Lemma WINDOW, S2):

    c₃(γ,γ′) := val₃(φ_γ·φ_{γ′}) / val₃(φ_{γ+γ′}).

Level-2 anchors of the SAME tower (levels 0–1 form an accepted-class 2-read
tower on the nose): φ⁽²⁾_β := π^{u(γ₁(β))}Φ₀^{s(γ₁(β))}Φ₁^{s₂(β)} with
γ₁(β) := u₂(β) − s₂(β)w₁Φ₁, the accepted note's anchor at index β [IL S0].
Consumption dictionary: [IL]'s γ ↦ our β₂(γ); [IL]'s γ₁(γ) ↦ our β₁(γ);
[IL]'s z̄ ↦ z₂; [IL]'s val ↦ R2v; [IL]'s W ↦ {β : u(γ₁(β)) ≥ 0}. Under this
dictionary φ⁽²⁾_{β₂(γ)} = π^{u₁(γ)}Φ₀^{s₁(γ)}Φ₁^{s₂(γ)} and γ ∈ W₃ ⟺
β₂(γ) ∈ [IL]'s W.

### S0.4 THEOREM (ITER-LAW-3) and status

**THEOREM (ITER-LAW-3; the sealed ITERLAWR S1 primary display, verbatim).**
For all γ, γ′ ∈ W₃, with

    δ₃ := ⌊(s₃(γ)+s₃(γ′))/e₂⌋ ∈ {0,1}                          [top carry]
    D₂ := (s₂(γ)+s₂(γ′)−s₂(γ+γ′) + ℓ₁·γ₃·δ₃)/e₁ ∈ ℤ            [middle exponent]
    Σ  := D₂·γ₂ + δ₃·γ₃·(ℓ₁′ − ℓ₁·w₁Φ₁) ∈ ℤ                    [composed inner shift]
    D₁ := (s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀·Σ)/e₀ ∈ ℤ                [inner exponent]

it holds that  c₃(γ,γ′) = z̄^{δ₃} · z₂^{D₂} · z₁^{D₁}.

STATUS OF PROOF: proved below for every pair (γ,γ′) OUTSIDE the sharp
double-cascade corner

    DCX := { (γ,γ′) : g₀ = g₁ = 1, δ₁ = 1, s₂(γ) = s₂(γ′) = e₁−1,
             (s₁(γ)+s₁(γ′)) + s(γ₂) ≥ 2e₀ }        (δ₁ := ⌊(s₁(γ)+s₁(γ′))/e₀⌋)

— which is EMPTY unless e₀ ≥ 3 — and holds on DCX conditional on the open
Lemma (W-MULT-3-DCX) (S4.7; instance-true on every probed DCX pair). The
integer-layer clauses (integrality of D₂, D₁; the composed-shift identity;
the exponent-level cocycle identity) are proved UNCONDITIONALLY on the whole
class.

| clause | status | where |
|---|---|---|
| L1 EQ12-ADD at a general read (e,h) | PROVED (accepted, [IL S2 L1]) | S2 |
| L2-(3a) INNER-SHIFT-TOP: β₂(γ+γ′) = β₂+β₂′+δ₃γ₃ | PROVED | S2 |
| D₂-INT: e₁ | (s₂-defect + ℓ₁γ₃δ₃) | PROVED | S2 |
| L2-(3b) COMPOSED-SHIFT: β₁(γ+γ′) = β₁+β₁′+Σ | PROVED | S2 |
| D₁-INT: e₀ | (s₁-defect + ℓ₀Σ) | PROVED | S2 |
| L3-(3) WINDOW: W₃ closed under + | PROVED | S2 |
| EXP-KIT (a) EPS-CLOSED / (b) EPS-MULT / (c) EXP-SHIFT, generic in the level | PROVED | S3 |
| WELL-DEF: canonical Φ₂ exists on the class; exact 2-term form at g₁ = 1 | PROVED | S4.0 |
| DIGIT-SPLIT + DEV-1 (the bounded reduction engine, level 1) | PROVED **[errata r1: inductive step at e₀ ≥ 2; at e₀ = 1 base range only — the corner e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀ is a fenced non-consumed gap (S4.1 erratum); every use in this note unaffected]** | S4.1 |
| L6-(3) ANCHOR-VAL: val₃(φ_γ) = ε₂(β₂)·ε₁(β₁) ≠ 0 | PROVED | S4.2 |
| CASE-SPLIT (the exact partition of pairs) | PROVED | S4.3 |
| W-MULT-(3), Case I (single top digit; all g₁ ≥ 2 + no-overflow g₁ = 1) | PROVED | S4.4 |
| W-MULT-(3), Case II-1 (g₁ = 1, δ₂ = 1, inner Case I — ALL g₀) | PROVED | S4.5 |
| W-MULT-(3), Cases II-2/II-3 (double cascade) outside DCX | PROVED | S4.6 |
| W-MULT-(3) on DCX | **OPEN** (W-MULT-3-DCX), instance-true | S4.7 |
| THEOREM off DCX | **PROVED (the unit's content)** | S5 |
| THEOREM on DCX | conditional on (W-MULT-3-DCX) | S5 |
| COR-1 integrality · COR-2 cocycle identity · COR-3 degenerations (e₂=1 ⟹ the ACCEPTED law verbatim **[errata r1: on the proved perimeter — off DCX; S6.3 erratum]**) · COR-4 ℤ/E₃ descent + monodromy · COR-5 gauge form c₃ = z̄^{δ₃}·∂F · COR-6 the (ITER-LAW-n) recursion at n = 3 **[errata r1: reads; = RUNG n = 2 — S6.6 rung bracket]** · COR-7 W-MULT product form | PROVED (conditionalities displayed per-item) | S6 |
| general lawful lifts · orders ≥ 4 · gr(w₃) wrapper · GMN transport | NOT TOUCHED (fences) | S7 |

## S1. What the proof is (the converged gauge route, executed)

The L3CONVERGENCE S3 strategy, literally: the induction carrier is the
ε-chain gauge, not the exponents. Two lemma families do all the work:

1. **L6-(3)** (S4.2): val₃(φ_γ) = ε₂(β₂(γ))·ε₁(β₁(γ)) — the anchor value is
   the ε-chain; a one-slot, one-digit read at the top with the ACCEPTED L6
   consumed verbatim on the inner digit (which IS the level-2 anchor
   φ⁽²⁾_{β₂(γ)} on the nose).
2. **W-MULT-(3)** (S4.3–S4.7): val₃(φ_γφ_{γ′}) = z̄^{δ₃}·val₃(φ_γ)·val₃(φ_{γ′})
   — the one hard step. The Φ₂-development digit of the anchor product
   P = π^UΦ₀^{S₁}Φ₁^{S₂}·Φ₂^{S₃} is A := π^UΦ₀^{S₁}Φ₁^{S₂}, which is EXACTLY
   the level-2 anchor pair product φ⁽²⁾_{β₂}φ⁽²⁾_{β₂′} — the accepted L7
   ("L7 stacked on L7", the sealed provenance ITERLAWR S1) computes its
   level-2 read. The top overflow (S₃ ≥ e₂) is absorbed by the slot grid as
   the z̄^{δ₃} shift (top Case I = the accepted Case-I mechanism one level
   up). The middle overflow (g₁ = 1 with the Φ₁-slot of A reaching e₁) is
   the genuinely new stratum: it is resolved by ONE exact reduction step
   Φ₁^{e₁} = Φ₂ − Ĉ, where Ĉ is the canonical lift's correction digit, and
   the resulting digit reads are computed by a bounded level-1 reduction
   engine (DEV-1) whose key property is READ-TRANSPARENCY: the standard-lift
   substitution Φ₀^{e₀g₀} = Φ₁ − Σ lift(ψ₀ᵢ)π^{(g₀−i)h₀}Φ₀^{e₀i} preserves
   formal reads because Σᵢ<g₀ ψ₀ᵢz₁^i = −z₁^{g₀} (ψ₀(z₁) = 0). The
   ε₁-correction built into Ĉ cancels the Bézout carry of ε₁(B₁+γ₂) exactly
   — this is the structural reason the law is pinned to the CANONICAL lift
   (and the mechanism behind the measured LIFT-DEV-3 deviation of the plain
   lift, L3XCHECK S7).

Given L6-(3) and W-MULT-(3), the theorem is division plus ONE two-line Bézout
kernel per level (EXP-KIT(c) at (e₁,h₁,ℓ₁,z₂) with shift T = δ₃γ₃, then at
(e₀,h₀,ℓ₀,z₁) with T = Σ) — no cross-level denominators, per the converged
integrality reading (L3CONVERGENCE S3 item 2 / L3FINGER S8). The cocycle
identity, integrality, degenerations, descent, the gauge form and the
(ITER-LAW-n) recursion at n = 3 **[errata r1: reads; = RUNG n = 2, see the
S6.6 rung bracket]** are then DERIVED corollaries (S6) — never
guessed constant-by-constant.

**Consumption manifest (everything non-self-contained, with pins):**

* [IL] = `ITERLAW_2026-08-08.md`, ACCEPTED 2026-08-03 (ledger block pasted in
  the header). Consumed: L1 (S2, general read), L4/L5/EXP (S3 — re-proved
  here inside the generic EXP-KIT for self-containment), L6 (S4), L7 (S4,
  both displayed forms AND the displayed development shapes of its proof:
  Case I "single digit a = π^UΦ₀^{S₁} at slot S₂, w₁(a) = β+β′"; Case II
  "digit A₁ = π^UΦ₀^{S₁″} at slot S₂+1, digit A₀ = −ĉπ^{U+h₀}Φ₀^{S₁″} at
  slot S₂, zero elsewhere, w₁(A₀) = β+β′, w₁(A₁) = β+β′−e₀h₀"), COR-4's
  shift arithmetic (S6.4). All consumed under the S0.3 dictionary.
* Base commutative algebra, as in [IL S1]: the division algorithm in O[x]
  (Φ monic ⟹ unique developments), w₀ a valuation, res additive and
  vanishing on strict π-excess, and O[x] → K₀ = O[x]/(π, Φ₀) a ring
  homomorphism (used by DIGIT-SPLIT). Nothing else.
* Sealed artifacts cited as INSTANCE EVIDENCE ONLY (never proof steps):
  ITERLAWR S5 verdict block, the m4 supplement, L3CONVERGENCE S1 matrix.

## S2. The integer layer (all proved, unconditional)

**Lemma L1 (EQ12-ADD; [IL S2 L1], accepted, general read (e,h)).** For
β, β′ ∈ ℤ with eq-(12-int) data (s,u), (s′,u′), (s″,u″) at β, β′, β+β′ and
δ := ⌊(s+s′)/e⌋: δ ∈ {0,1}, s″ = s+s′−δe, u″ = u+u′+δh. ∎ (Consumed; the
two-line proof is in [IL S2].)

Fix γ, γ′ ∈ W₃ and write (here and through S5): sⱼ := sⱼ(γ), sⱼ′ := sⱼ(γ′),
sⱼ″ := sⱼ(γ+γ′) for j = 1,2,3; u₁ := u₁(γ), u₁′ := u₁(γ′); β₂ := β₂(γ),
β₂′ := β₂(γ′), β₂″ := β₂(γ+γ′); β₁, β₁′, β₁″ likewise; S₃ := s₃+s₃′,
S₂ := s₂+s₂′, S₁ := s₁+s₁′, U := u₁+u₁′; B₂ := β₂+β₂′, B₁ := β₁+β₁′;
δ₃ := ⌊S₃/e₂⌋, δ₂ := ⌊S₂/e₁⌋, δ₁ := ⌊S₁/e₀⌋ (all in {0,1} by L1);
Γ″ := γ+γ′.

**Lemma L2-(3a) (INNER-SHIFT-TOP).** β₂″ = β₂ + β₂′ + δ₃γ₃.
*Proof.* L1 at (e₂,h₂): s₃″ = S₃−δ₃e₂, u₃(Γ″) = u₃(γ)+u₃(γ′)+δ₃h₂. Then
β₂″ = u₃(Γ″) − s₃″·w₂Φ₂ = [u₃(γ)+u₃(γ′)] + δ₃h₂ − [S₃−δ₃e₂]w₂Φ₂
= β₂ + β₂′ + δ₃(e₂w₂Φ₂ + h₂) = B₂ + δ₃γ₃. ∎ ([IL S2 L2] one level up.)

**Lemma D₂-INT.** e₁ | (s₂ + s₂′ − s₂″ + ℓ₁γ₃δ₃); hence D₂ ∈ ℤ.
*Proof.* From u·e₁ + s·h₁ = β and ℓ₁h₁ ≡ 1 (mod e₁): s₂(β) ≡ ℓ₁β (mod e₁)
for every β. So s₂+s₂′−s₂″+ℓ₁γ₃δ₃ ≡ ℓ₁(β₂+β₂′−β₂″+γ₃δ₃) = ℓ₁·0 ≡ 0 (mod e₁)
by L2-(3a). (At e₁ = 1 trivially.) ∎

**Lemma L2-(3b) (COMPOSED-SHIFT).** β₁″ = β₁ + β₁′ + Σ, with
Σ = D₂γ₂ + δ₃γ₃(ℓ₁′ − ℓ₁w₁Φ₁) ∈ ℤ (D₂ ∈ ℤ by D₂-INT).
*Proof.* From β₂ = e₁β₁ + s₂γ₂ at all three arguments and L2-(3a):
e₁(β₁″−β₁−β₁′) = (β₂″−β₂−β₂′) + (s₂+s₂′−s₂″)γ₂ = δ₃γ₃ + (e₁D₂ − ℓ₁γ₃δ₃)γ₂
= e₁D₂γ₂ + δ₃γ₃(1 − ℓ₁γ₂). And 1 − ℓ₁γ₂ = 1 − ℓ₁(e₁w₁Φ₁+h₁)
= ℓ₁′e₁ − ℓ₁e₁w₁Φ₁ = e₁(ℓ₁′ − ℓ₁w₁Φ₁) by the Bézout identity. Divide by e₁. ∎
(The sealed provenance's INNER-SHIFT-3, now an identity; equivalently: Σ IS
the realized inner shift β₁″−β₁−β₁′ on every pair — the M5/M1 realized-shift
form and the sealed closed form are one lemma, L3XCHECK S4 / L3FIT S0
confirmed instance-side.)

**Lemma D₁-INT.** e₀ | (s₁ + s₁′ − s₁″ + ℓ₀Σ); hence D₁ ∈ ℤ.
*Proof.* s(β) ≡ ℓ₀β (mod e₀) as above; the sum ≡ ℓ₀(β₁+β₁′−β₁″+Σ) = 0
(mod e₀) by L2-(3b). ∎

**Lemma L3-(3) (WINDOW).** γ, γ′ ∈ W₃ ⟹ γ+γ′ ∈ W₃.
*Proof.* e₀u(β₁″) = β₁″ − s₁″h₀ = e₀U + (S₁−s₁″)h₀ + Σ ≥ −(e₀−1)h₀ + Σ + e₀U
and U ≥ 0. Three cases.
(i) δ₃ = 0, δ₂ = 0: then s₂″ = S₂−δ₂e₁ = S₂ wait — **[errata r1 (PE-N1):
the fragment "= S₂ wait —" is a struck composition artifact (mid-sentence
false start); the sentence of record reads "then s₂″ = S₂−δ₂e₁:"]**
at δ₃ = 0, β₂″ = B₂ and
L1 at (e₁,h₁) gives s₂″ = S₂ − δ₂e₁ directly, so D₂ = δ₂ and Σ = γ₂δ₂. At
δ₂ = 0: Σ = 0 and u(β₁″) = u(β₁)+u(β₁′)+δ₁h₀ ≥ 0 by L1 at (e₀,h₀).
(ii) δ₃ = 0, δ₂ = 1: Σ = γ₂ = e₀e₁g₀h₀ + h₁ ≥ e₀h₀ + h₁ > (e₀−1)h₀, so
e₀u(β₁″) > 0. ([IL S2 L3]'s two cases, verbatim under the dictionary.)
(iii) δ₃ = 1 (so e₂ ≥ 2): e₁Σ = δ₃γ₃ + (S₂−s₂″)γ₂ ≥ γ₃ − (e₁−1)γ₂
[s₂+s₂′−s₂″ ≥ −(e₁−1); note S₂−s₂″ here uses the DEFINITION of D₂:
e₁Σ = e₁D₂γ₂ + δ₃γ₃(1−ℓ₁γ₂) recombined as in L2-(3b) equals
δ₃γ₃ + (s₂+s₂′−s₂″)γ₂]. Since γ₃ = e₂e₁g₁γ₂ + h₂ ≥ e₁γ₂ + h₂:
e₁Σ ≥ γ₂ + h₂ = e₀e₁g₀h₀ + h₁ + h₂ > e₁(e₀−1)h₀, so Σ > (e₀−1)h₀ and
e₀u(β₁″) > 0. ∎

## S3. The character layer: ONE Bézout kernel per level

**Lemma EXP-KIT (the per-level compose kernel; generic).** Fix a read (e,h),
gcd(e,h) = 1, its normalized Bézout pair (ℓ,ℓ′), a field K with a unit
z ∈ K^×, and set ε(β) := z^{ℓ′s(β) − ℓu(β)} on the eq-(12-int) data of
(e,h). Then:

(a) **EPS-CLOSED**: (s(β) − ℓβ)/e ∈ ℤ and ε(β) = z^{(s(β)−ℓβ)/e}.
*Proof.* ℓβ = ℓeu(β) + ℓh·s(β) = ℓeu(β) + (1−ℓ′e)s(β), so
s(β) − ℓβ = e(ℓ′s(β) − ℓu(β)). ∎ (At e = 1: ℓ = 0, s ≡ 0, ε ≡ 1.)

(b) **EPS-MULT**: ε(β)ε(β′) = z^{δ}·ε(β+β′), δ := ⌊(s(β)+s(β′))/e⌋.
*Proof.* Exponents via (a): LHS (s(β)+s(β′)−ℓ(β+β′))/e; RHS
δ + (s(β+β′)−ℓ(β+β′))/e; equal by L1 (s(β+β′) = s(β)+s(β′)−δe). ∎

(c) **EXP-SHIFT** (general shift): for any T ∈ ℤ and β″ := β+β′+T, with
δ := ⌊(s(β)+s(β′))/e⌋:

    z^{δ} · ε(β+β′)/ε(β″) = z^{D},   D = (s(β)+s(β′) − s(β″) + ℓT)/e ∈ ℤ.

*Proof.* By (a) the LHS exponent is δ + [(s(β+β′)−ℓ(β+β′)) − (s(β″)−ℓβ″)]/e;
substitute s(β+β′) = s(β)+s(β′)−δe (L1) and ℓ(β″−β−β′) = ℓT; the δ-terms
cancel. Integrality: δ plus a difference of two integers by (a) twice. ∎

Instantiations used below (the "one kernel per level" of the converged
strategy — each level's denominator cured inside its own kernel, NO
cross-level denominator ever formed):

| level | (e,h,ℓ,ℓ′) | z | ε | shift T | output |
|---|---|---|---|---|---|
| 1 (inner) | (e₀,h₀,ℓ₀,ℓ₀′) | z₁ | ε₁ (harness eps1, reading C) | T = Σ | z₁^{δ₁}ε₁(B₁)/ε₁(β₁″) = z₁^{D₁} |
| 2 (middle) | (e₁,h₁,ℓ₁,ℓ₁′) | z₂ | ε₂ (harness eps2) | T = δ₃γ₃ | z₂^{δ₂}ε₂(B₂)/ε₂(β₂″) = z₂^{D₂} |

([IL S3 L4/L5/EXP] are (a)/(b)/(c) at level 1 with T = γ₂δ₂; the accepted
proofs are the generic ones above verbatim, so nothing is weakened by citing
EXP-KIT instead.)

## S4. The value layer

### S4.0 Lemma WELL-DEF (the canonical lift exists; its exact g₁ = 1 form)

(i) For every k < g₁ with ψ₁ₖ ≠ 0, C_k = realize1(τ⁽ᵏ⁾, gp) with
gp := (g₁−k)γ₂ and τ⁽ᵏ⁾ := ε₁(gp)^{−1}ψ₁ₖ ∈ K₁^× is well-defined: realize1
needs u(gp) ≥ (g₀−1)h₀, and indeed e₀u(gp) = gp − s(gp)h₀ ≥ γ₂ − (e₀−1)h₀
= e₀e₁g₀h₀ + h₁ − (e₀−1)h₀ = e₀(g₀−1)h₀ + h₀(e₀g₀(e₁−1) + 1) + h₁
> e₀(g₀−1)h₀. By its definition (realize1 :632–644),
C_k = Σ_{m<g₀} lift(τ⁽ᵏ⁾_m)·π^{u(gp)−mh₀}·Φ₀^{s(gp)+me₀} (τ⁽ᵏ⁾_m ∈ K₀ the
z₁-power-basis coordinates), so: deg C_k < deg Φ₁; every term of C_k lies on
the level-1 line gp (e₀(u(gp)−mh₀) + (s(gp)+me₀)h₀ = gp); w₁(C_k) = gp; and
R_{1,gp}(C_k)(z₁) = τ⁽ᵏ⁾ (each term sits on its own grid abscissa
s(gp)+me₀ at exact w₀; res additive).

(ii) **At g₁ = 1** (ψ₁ = y + c₁, c₁ := ψ₁(0) ≠ 0, z₂ = −c₁ under
K₂ = K₁[z₂]/(z₂+c₁) ≅ K₁):

    Φ₂ = Φ₁^{e₁} + Ĉ,   Ĉ := C₀ = Σ_{m<g₀} lift(τ_m)π^{u_γ−mh₀}Φ₀^{s_γ+me₀},

with τ := ε₁(γ₂)^{−1}c₁ ∈ K₁^×, (s_γ, u_γ) := (s(γ₂), u(γ₂)). Properties
(from (i)): (Ĉ1) deg Ĉ < deg Φ₁ — Ĉ is a single Φ₁-slot-0 digit; (Ĉ2) every
term on the level-1 line γ₂, w₁(Ĉ) = γ₂; (Ĉ3) R_{1,γ₂}(Ĉ)(z₁) = τ. ∎

(Sanity, not consumed: (Ĉ1–3) are exactly what makes R₂(Φ₂) = ψ₁ exact —
the harness-certified T5 property.)

### S4.1 The bounded reduction engine

**Lemma DIGIT-SPLIT.** For α, β ∈ O[x] of degree < d₀:
αβ = lift(q(α)q(β)) + πX + Φ₀Y with deg X < d₀, deg Y < d₀, where
q: O[x] → K₀ = O[x]/(π, Φ₀) is the reduction ring-homomorphism.
*Proof.* Divide: αβ = YΦ₀ + ρ, deg ρ < d₀, deg Y ≤ 2d₀−2−d₀ < d₀ (Φ₀
monic). Apply q: q(ρ) = q(α)q(β). A degree-< d₀ polynomial with q-image
t ∈ K₀ differs from lift(t) by an element of πO[x] of degree < d₀. ∎

**Lemma DEV-1 (bounded level-1 development with read transparency).** Fix a
target weight β* ∈ ℤ with level-1 data (s*, u*) := (s(β*), u(β*)). Let
G = b·Φ₀^j with b ∈ O[x], 0 ≠ b, deg b < d₀, and 0 ≤ j < 2e₀g₀; put
λ := e₀w₀(b) + jh₀ and assume λ ≥ β*. Then there exist R₀, Q ∈ O[x] with
deg R₀ < deg Φ₁, deg Q < deg Φ₁, such that

    G = R₀ + Q·Φ₁,   w₁(R₀) ≥ λ,   w₁(Q) ≥ λ − w₁Φ₁ (Q = 0 allowed),

and the level-1 read of R₀ at β* is:

    R_{1,β*}(R₀)(z₁) = res(b/π^{w₀(b)})·z₁^{(j−s*)/e₀}  if λ = β*   [tracked]
    R_{1,β*}(R₀)(z₁) = 0                                if λ > β*.  [junk]

(When λ = β*, automatically j ≡ s* (mod e₀) — from e₀w₀(b) + jh₀ = β* and
s* ≡ ℓ₀β* (mod e₀) — and j ≥ s*, so the exponent is a non-negative integer.)

*Proof.* Strong induction on j.

Base j < e₀g₀: R₀ := G (deg < d₀ + (e₀g₀−1)d₀ = deg Φ₁), Q := 0. The
Φ₀-development of R₀ is the single digit bπ⁰ at abscissa j with
w₀-line-requirement at β*: (β* − jh₀)/e₀. If λ = β*: the requirement equals
w₀(b) exactly and j = s* + ((j−s*)/e₀)·e₀ is a grid abscissa: the read is
res(b/π^{w₀(b)})·z₁^{(j−s*)/e₀}. If λ > β*: either j is off the grid (read
skips it) or the requirement is < w₀(b) strictly (res of strict excess = 0).

Step j ≥ e₀g₀ (then j − e₀g₀ < e₀g₀ by the hypothesis j < 2e₀g₀): the
standard lift gives the EXACT identity Φ₀^{e₀g₀} = Φ₁ − Σ_{i<g₀}
lift(ψ₀ᵢ)π^{(g₀−i)h₀}Φ₀^{e₀i} (ψ₀ monic). Hence

    G = bΦ₀^{j−e₀g₀}·Φ₁ − Σ_{i<g₀} lift(ψ₀ᵢ)·b·π^{(g₀−i)h₀}Φ₀^{e₀i+j−e₀g₀}.

The Φ₁-cofactor bΦ₀^{j−e₀g₀} has degree < deg Φ₁ and w₁ = λ − e₀g₀h₀
= λ − w₁Φ₁ (single digit) — it joins Q. Each summand: DIGIT-SPLIT on
lift(ψ₀ᵢ)·b gives three children of G with Φ₀-exponents and lines

    child⁽ⁱ⁾  := −lift(ψ₀ᵢ·b̄)π^{w₀(b)+(g₀−i)h₀}Φ₀^{e₀i+j−e₀g₀}, line λ;
    junkπ⁽ⁱ⁾  := −X·π^{w₀(b)+(g₀−i)h₀+1}Φ₀^{e₀i+j−e₀g₀},        line λ+e₀;
    junkΦ⁽ⁱ⁾  := −Y·π^{w₀(b)+(g₀−i)h₀}Φ₀^{e₀i+j−e₀g₀+1},        line λ+h₀,

(b̄ := res(b/π^{w₀(b)}); note w₀ of the coefficients is ≥ the displayed
values, which only raises lines — the line values shown are lower bounds,
with equality for child⁽ⁱ⁾ exactly when ψ₀ᵢb̄ ≠ 0). All children have
Φ₀-exponent ≤ e₀(g₀−1) + j − e₀g₀ + 1 = j − e₀ + 1 ≤ j − 1 < j (e₀ ≥ 1) and
< 2e₀g₀, with lines ≥ λ ≥ β*: the induction applies to each; sum the R₀'s
and Q's (w₁ of a sum ≥ min of the w₁'s — developments add, w₀ a valuation).
Reads at β*, when λ = β*: junk children have lines > β*, so they contribute
0; the tracked children contribute, by induction and additivity of the read
(res is additive; digits at one abscissa add):

    Σᵢ (−ψ₀ᵢb̄)·z₁^{(e₀i+j−e₀g₀−s*)/e₀}
      = −b̄·z₁^{(j−e₀g₀−s*)/e₀} · Σᵢ ψ₀ᵢz₁^i
      = −b̄·z₁^{(j−e₀g₀−s*)/e₀} · (ψ₀(z₁) − z₁^{g₀})
      = b̄·z₁^{(j−s*)/e₀}                                 [ψ₀(z₁) = 0]

= the claimed value (the READ-TRANSPARENCY of the standard-lift reduction).
When λ > β*: every child has line > β*, all reads 0 by induction. The
intermediate exponent (j−e₀g₀−s*)/e₀ is an integer of either sign; z₁ is a
unit, and the FINAL abscissas of all tracked terms are ≥ 0 and ≡ s*
(mod e₀), hence ≥ s*: only non-negative powers appear in the actual read. ∎

**[ERRATUM (errata round 1, 2026-08-03; convergent findings PC-F1 [GAP] =
PE-F2 [GAP]; reports `ITERLAW3_passPC_report.md` (997c467) /
`ITERLAW3_passPE_report.md` (be9a77b)): the induction-measure display in the
step above — "j − e₀ + 1 ≤ j − 1 < j (e₀ ≥ 1)" — is STRUCK as written: the
decrease requires **e₀ ≥ 2**, not e₀ ≥ 1. At e₀ = 1 the junkΦ⁽ⁱ⁾ child at
i = g₀−1 has Φ₀-exponent exactly j, and the strong induction on j does not
close as stated (that child's line rises by h₀ each round; no j-descent
occurs). CORRECTED SCOPE OF RECORD: the inductive step of DEV-1 is proved
for e₀ ≥ 2; at e₀ = 1, DEV-1 is proved on the base range j < e₀g₀ only.
Every use of DEV-1 in this note survives verbatim (PE-verified): S4.5's
inputs G_m at e₀ = 1 have Φ₀-exponent J + me₀ with J = S₁ + s(γ₂) = 0 (all
eq-(12-int) s-values vanish at e₀ = 1), i.e. exponent m ≤ g₀−1 < e₀g₀ —
base range only; S4.6 requires g₀ = 1 ∧ δ₁ = 1, forcing e₀ ≥ 2; and at
d₀ = 1 the DIGIT-SPLIT cofactor Y vanishes identically (deg αβ ≤ 2d₀−2 =
0 < d₀ = 1 forces Y = 0), so junkΦ ≡ 0 and the non-descending child is
absent.

    ┌─ FENCED NON-CONSUMED CORNER (open; a displayed gap, NOT a proved ─┐
    │  case):  DEV-1 as originally quantified is UNPROVED exactly on    │
    │      { e₀ = 1  ∧  d₀ ≥ 2  ∧  j ≥ g₀ }.                            │
    │  WHY IT IS UNREACHED by this note: every DEV-1 call at e₀ = 1     │
    │  has base-range Φ₀-exponent (S4.5's J = 0 computation above), and │
    │  S4.6's hypotheses force e₀ ≥ 2 — so no consumer enters the       │
    │  corner. A repair route exists (at e₀ = 1 the only non-descending │
    │  child is the junkΦ chain, whose coefficient π-depth strictly     │
    │  grows; a secondary induction on target-relative depth closes     │
    │  it) but that argument is NOT in this note.                       │
    └───────────────────────────────────────────────────────────────────┘
]**

### S4.2 Lemma L6-(3) (ANCHOR-VAL): val₃(φ_γ) = ε₂(β₂(γ))·ε₁(β₁(γ)) ∈ K₃^×

*Proof.* φ_γ = a·Φ₂^{s₃} with a := π^{u₁}Φ₀^{s₁}Φ₁^{s₂} = φ⁽²⁾_{β₂(γ)} (S0.3
dictionary). deg a = s₁d₀ + s₂e₀g₀d₀ ≤ (e₀−1)d₀ + (e₁−1)e₀g₀d₀ < e₁g₁e₀g₀d₀
= deg Φ₂, so the Φ₂-development of φ_γ is the single digit a at slot s₃.
By the accepted L6 [IL S4 L6] under the dictionary (β₂(γ) ∈ [IL]'s W since
γ ∈ W₃): the level-2 read of a is the single coefficient ε₁(β₁(γ)) at
slot 0, i.e. R2v(a) = ε₁(β₁), and w₂(a) = β₂ (displayed inside [IL S4 L6]'s
proof: single Φ₁-digit π^{u₁}Φ₀^{s₁} at slot s₂, itself a single Φ₀-digit
π^{u₁} at abscissa s₁, so w₂(a) = e₁(e₀u₁+s₁h₀) + s₂γ₂ = e₁β₁ + s₂γ₂ = β₂).
Then w₃(φ_γ) = e₂β₂ + s₃γ₃ = γ; the level-3 grid at γ is s₃ + je₂, the
single digit sits at j = 0 with slot weight (γ − s₃γ₃)/e₂ = β₂ = w₂(a):
on-line. All other grid slots carry the zero digit. Hence
val₃(φ_γ) = ε₂(β₂)·R2v(a)·z̄⁰ = ε₂(β₂)ε₁(β₁), a unit (ε's are unit powers,
K₃ a field). ∎

### S4.3 W-MULT-(3): statement and the exact case partition

**Proposition W-MULT-(3).** For γ, γ′ ∈ W₃, with P := φ_γ·φ_{γ′}
= π^UΦ₀^{S₁}Φ₁^{S₂}Φ₂^{S₃} and A := π^UΦ₀^{S₁}Φ₁^{S₂} = φ⁽²⁾_{β₂}φ⁽²⁾_{β₂′}:

    val₃(P) = z̄^{δ₃} · ε₂(B₂) · z₂^{δ₂} · z₁^{δ₁} · ε₁(B₁)
            = z̄^{δ₃} · val₃(φ_γ) · val₃(φ_{γ′}),

the second equality by EXP-KIT(b) at both levels
(ε₂(β₂)ε₂(β₂′) = z₂^{δ₂}ε₂(B₂), ε₁(β₁)ε₁(β₁′) = z₁^{δ₁}ε₁(B₁)) plus
L6-(3); moreover the level-3 read of P is a SINGLE nonzero coefficient, at
slot z̄^{δ₃}, at weight w₃(P) = Γ″ (the sealed G2 shape clause). Proved in
S4.4–S4.6 for all pairs outside DCX; open on DCX (S4.7).

**Lemma CASE-SPLIT.** Exactly one of the following holds, and they exhaust
all pairs:

* **Case I** (deg A < deg Φ₂; equivalently: g₁ ≥ 2, or g₁ = 1 ∧ inner Case I
  ∧ S₂ ≤ e₁−1, or g₁ = 1 ∧ inner Case II ∧ S₂ ≤ e₁−2).
* **Case II-1**: g₁ = 1, inner Case I, δ₂ = 1 (so S₂ ≥ e₁, e₁ ≥ 2).
* **Case II-2**: g₁ = 1, inner Case II, δ₂ = 1.
* **Case II-3**: g₁ = 1, inner Case II, S₂ = e₁−1 (δ₂ = 0).

Here "inner Case I/II" is the accepted L7 dichotomy for A [IL S4 L7]:
inner I ⟺ S₁ < e₀g₀ (automatic at g₀ ≥ 2); inner II ⟺ g₀ = 1 ∧ δ₁ = 1.

*Proof.* [IL S4 L7]'s displayed developments give the Φ₁-slot support of A:
inner I — single digit a := π^UΦ₀^{S₁} at slot S₂ (deg a = S₁d₀ < deg Φ₁);
inner II — digits A₁ := π^UΦ₀^{S₁″} at slot S₂+1 and A₀ := −ĉ₀π^{U+h₀}Φ₀^{S₁″}
at slot S₂ (S₁″ := S₁−e₀ ≤ e₀−2, ĉ₀ := lift(c₀), c₀ := ψ₀(0), z₁ = −c₀).
So deg A < deg Φ₂ = e₁g₁·deg Φ₁ ⟺ top Φ₁-slot of A ≤ e₁g₁ − 1. At g₁ ≥ 2:
top slot ≤ S₂+1 ≤ 2e₁−1 < 2e₁ ≤ e₁g₁ always. At g₁ = 1: inner I overflows
iff S₂ ≥ e₁ (⟺ δ₂ = 1, which forces e₁ ≥ 2 since s₂, s₂′ ≤ e₁−1); inner II
overflows iff S₂+1 ≥ e₁, i.e. δ₂ = 1 (II-2) or S₂ = e₁−1 (II-3). ∎

Weights of the [IL] digits, re-derived for the top-line bookkeeping (all
one-line computations from the displayed shapes): inner I: w₁(a) = e₀U+S₁h₀
= B₁, so w₂(A) = e₁B₁ + S₂γ₂ = B₂ (single slot). Inner II: w₁(A₀) = B₁ at
slot S₂ (line e₁B₁+S₂γ₂ = B₂), w₁(A₁) = B₁−e₀h₀ at slot S₂+1 (line
B₂ + (γ₂ − e₁e₀h₀) = B₂ + h₁, using g₀ = 1); so w₂(A) = B₂, attained at
slot S₂ only. In both cases (used throughout): **w₂(A) = B₂**, and by the
accepted L7's read clause, **R2v(A) = z₂^{δ₂}z₁^{δ₁}ε₁(B₁)** — the read of A
is the single coefficient z₁^{δ₁}ε₁(B₁) at slot δ₂ of the grid of B₂.

### S4.4 Case I (single top digit) — PROVED

The Φ₂-development of P is the single digit A at slot S₃. w₃(P) =
e₂w₂(A) + S₃γ₃ = e₂B₂ + S₃γ₃ = Γ″ (from γ = e₂β₂+s₃γ₃ summed). By L1 at
(e₂,h₂): s₃(Γ″) = S₃ − δ₃e₂, so the level-3 grid at Γ″ is s₃″ + je₂ and the
digit A sits at abscissa S₃ = s₃″ + δ₃e₂, i.e. slot j = δ₃, with slot weight
(Γ″ − S₃γ₃)/e₂ = B₂ = w₂(A): on-line. Every other grid slot carries the zero
digit (single-digit development) and contributes 0. Hence the read of P is
the single coefficient

    C_{δ₃} = ε₂(B₂)·R2v(A) = ε₂(B₂)·z₂^{δ₂}z₁^{δ₁}ε₁(B₁)

at slot δ₃, and val₃(P) = z̄^{δ₃}ε₂(B₂)z₂^{δ₂}z₁^{δ₁}ε₁(B₁). ∎
(The accepted Case-I slot-grid absorption, one level up — the sealed
provenance's top-slot mechanism, now a proof.)

### S4.5 Case II-1 (g₁ = 1, δ₂ = 1, inner Case I; ALL g₀) — PROVED

Setup: g₁ = 1, so WELL-DEF(ii) gives Φ₂ = Φ₁^{e₁} + Ĉ exactly; e₁ ≥ 2,
k := S₂ − e₁ ∈ [0, e₁−2]; A = a·Φ₁^{S₂} with a = π^UΦ₀^{S₁}, S₁ < e₀g₀.
Substituting Φ₁^{e₁} = Φ₂ − Ĉ once:

    P = a·Φ₁^{k}·Φ₂^{S₃+1} − a·Ĉ·Φ₁^{k}·Φ₂^{S₃},

and both Φ₂-cofactors have degree < deg Φ₂ (aΦ₁^k: < (k+1)deg Φ₁ ≤
(e₁−1)deg Φ₁; aĈΦ₁^k: deg(aĈ) < 2deg Φ₁, so < (k+2)deg Φ₁ ≤ e₁deg Φ₁), so
this IS the Φ₂-development: digit E₁ := aΦ₁^k at slot S₃+1, digit
E₀ := −aĈΦ₁^k at slot S₃.

**The E₀ digit (the level-2 read through DEV-1).** Set β* := B₁ + γ₂,
(s*, u*) := level-1 data of β*, ε′ := ⌊(s(B₁)+s(γ₂))/e₀⌋ ∈ {0,1}. Expanding
Ĉ (WELL-DEF(ii)) against the monomial a:

    aĈ = Σ_{m<g₀} G_m,   G_m := lift(τ_m)·π^{V−mh₀}·Φ₀^{J+me₀},
    V := U + u(γ₂),  J := S₁ + s(γ₂),

every G_m on the level-1 line e₀(V−mh₀) + (J+me₀)h₀ = e₀V + Jh₀
= (e₀U+S₁h₀) + (e₀u(γ₂)+s(γ₂)h₀) = B₁ + γ₂ = β*, with Φ₀-exponent
J+me₀ ≤ (2e₀−2)+(e₀−1)+(g₀−1)e₀ = e₀g₀+2e₀−3 < 2e₀g₀ at g₀ ≥ 2, and
≤ (e₀−1)+(e₀−1) = 2e₀−2 < 2e₀g₀ at g₀ = 1 (inner Case I: S₁ ≤ e₀−1 there).
DEV-1 applies to each G_m with target β*: aĈ = Rem + Q·Φ₁,
Rem := Σ R₀-parts, Q := Σ Q-parts, with w₁(Rem) ≥ β*, w₁(Q) ≥ β* − w₁Φ₁, and

    R_{1,β*}(Rem)(z₁) = Σ_{m<g₀} τ_m·z₁^{(J+me₀−s*)/e₀}
                      = z₁^{(J−s*)/e₀}·Σ_m τ_m z₁^m = z₁^{δ₁+ε′}·τ,

using L1 twice for the exponent: s(B₁) = S₁ − δ₁e₀ and s* = s(B₁)+s(γ₂)−ε′e₀
give J − s* = (δ₁+ε′)e₀; and Σ τ_m z₁^m = τ = ε₁(γ₂)^{−1}c₁ ≠ 0. In
particular w₁(Rem) = β* exactly. So E₀ = −RemΦ₁^k − QΦ₁^{k+1} with Φ₁-slot
support ⊆ {k, k+1}:

* w₂(E₀) = B₂: slot k has line e₁β* + kγ₂ = e₁B₁ + S₂γ₂ = B₂, attained
  (Rem's read ≠ 0 forces an exact on-line digit); slot k+1 has line
  ≥ e₁(β*−w₁Φ₁) + (k+1)γ₂ = B₂ + (γ₂ − e₁w₁Φ₁) = B₂ + h₁ > B₂.
* Level-2 read of E₀ at B₂: grid abscissas s₂(B₂) + je₁ with
  s₂(B₂) = S₂ − δ₂e₁ = k (L1, δ₂ = 1). j = 0: digit −Rem, slot weight
  (B₂ − kγ₂)/e₁ = β* = w₁(Rem), on-line; coefficient
  C₀ = ε₁(β*)·(−z₁^{δ₁+ε′}τ) = −ε₁(β*)ε₁(γ₂)^{−1}·c₁·z₁^{δ₁+ε′}
     = −c₁·z₁^{δ₁}·ε₁(B₁) = z₂^{δ₂}·z₁^{δ₁}·ε₁(B₁),
  by EPS-MULT (ε₁(β*)ε₁(γ₂)^{−1} = z₁^{−ε′}ε₁(B₁)) and z₂ = −c₁, δ₂ = 1.
  j ≥ 1: abscissa k+je₁ ≥ k+2 carries the zero digit; abscissa k+1 is OFF
  the grid (e₁ ≥ 2). So R2v(E₀) = C₀ = z₂^{δ₂}z₁^{δ₁}ε₁(B₁).

**The top level.** w₂(E₁) = e₁B₁ + kγ₂ = B₂ − e₁γ₂ (single digit a at
slot k, w₁(a) = B₁). Slot line values: S₃ ↦ e₂B₂ + S₃γ₃ = Γ″; S₃+1 ↦
e₂(B₂−e₁γ₂) + (S₃+1)γ₃ = Γ″ + (γ₃ − e₂e₁γ₂) = Γ″ + h₂ (g₁ = 1). So
w₃(P) = Γ″, attained at slot S₃ only. Grid: s₃(Γ″) = S₃ − δ₃e₂ (L1); E₀
sits at slot j = δ₃, slot weight B₂ = w₂(E₀): on-line. The digit at S₃+1 is
off-grid when e₂ ≥ 2, and on-grid-but-strictly-above-the-line when e₂ = 1
(slot weight Γ″ − (S₃+1)γ₃ = B₂ − γ₃ < B₂ − e₁γ₂ + h₂ = w₂(E₁) + 0 — i.e.
w₂(E₁) = B₂ − γ₃ + h₂ > slot weight): read 0 either way. Hence

    val₃(P) = z̄^{δ₃}·ε₂(B₂)·R2v(E₀) = z̄^{δ₃}·ε₂(B₂)·z₂^{δ₂}z₁^{δ₁}·ε₁(B₁). ∎

(The ε′-cancellation above is the structural content of the CANONICAL
ε₁-corrected lift: with the plain lift, τ is replaced by c₁ and the residual
factor ε₁(γ₂)^{−1} survives into the value — exactly the measured
(LIFT-DEV-3) deviation ε₁(γ₂)^{δ₂}, L3XCHECK S7.)

### S4.6 Cases II-2 and II-3 (the double cascade, g₀ = g₁ = 1, δ₁ = 1) — PROVED outside DCX

Now g₀ = g₁ = 1 (so K₁ = K₀ with z₁ = −c₀, K₂ = K₁ with z₂ = −c₁, τ ∈ K₀ a
scalar), inner Case II: A = A₁Φ₁^{S₂+1} + A₀Φ₁^{S₂}, A₁ = π^UΦ₀^{S₁″},
A₀ = −ĉ₀π^{U+h₀}Φ₀^{S₁″}, S₁″ = S₁−e₀ ≤ e₀−2. Put ω := S₁″ + s(γ₂)
(≤ 2e₀−3), β* := B₁+γ₂, ε′ := ⌊(s(B₁)+s(γ₂))/e₀⌋ = ⌊ω/e₀⌋ (s(B₁) = S₁″ at
δ₁ = 1). The two Ĉ-products are generalized monomials:

    A₀Ĉ = −ĉ₀·lift(τ)·π^{U+h₀+u(γ₂)}·Φ₀^{ω}   [line β*]
    A₁Ĉ =      lift(τ)·π^{U+u(γ₂)}·Φ₀^{ω}      [line β* − e₀h₀],

(for A₀Ĉ: apply DIGIT-SPLIT to ĉ₀lift(τ) = lift(c₀τ) + πX + Φ₀Y, giving the
tracked main term with residue −c₀τ on line β* plus junk children on lines
β*+e₀, β*+h₀; then DEV-1 on each with target β*; for A₁Ĉ: DEV-1 with target
β*−e₀h₀, only the weight clauses used). Write A₀Ĉ = Rem⁰ + Q⁰Φ₁ and
A₁Ĉ = R¹ + Q¹Φ₁ per DEV-1; note **Q¹ = 0 unless ω ≥ e₀** (at ω < e₀ no
reduction fires on A₁Ĉ), and Q¹ ≠ 0 requires e₀ ≥ 3 (ω ≤ 2e₀−3 ≥ e₀ forces
e₀ ≥ 3). Key read (DEV-1 transparency, any ω):
R_{1,β*}(Rem⁰)(z₁) = −c₀τ·z₁^{(ω−s*)/e₀} = −c₀τ·z₁^{ε′} (s* = ω − ε′e₀).

**Case II-2 (δ₂ = 1; k := S₂−e₁ ∈ [0,e₁−2], e₁ ≥ 2).** Substituting
Φ₁^{e₁} = Φ₂ − Ĉ on both slots:

    P = [A₁Φ₁^{k+1} + A₀Φ₁^{k}]·Φ₂^{S₃+1} − [A₁ĈΦ₁^{k+1} + A₀ĈΦ₁^{k}]·Φ₂^{S₃}.

E₁ := A₁Φ₁^{k+1} + A₀Φ₁^{k}: slots ≤ k+1 ≤ e₁−1, a digit; w₂(E₁) ≥
B₂ − e₁γ₂ (slot k line e₁B₁+kγ₂ = B₂−e₁γ₂; slot k+1 line
e₁(B₁−e₀h₀)+(k+1)γ₂ = B₂−e₁γ₂+h₁, using γ₂−e₁e₀h₀ = h₁ at g₀ = 1). E₀ :=
−A₁ĈΦ₁^{k+1} − A₀ĈΦ₁^{k} = −Rem⁰Φ₁^{k} − (Q⁰+R¹)Φ₁^{k+1} − Q¹Φ₁^{k+2}.
**Provided k+2 ≤ e₁−1 OR Q¹ = 0** (i.e. outside DCX), E₀ is a digit
(deg < deg Φ₂) and:

* slot k: line β*·e₁ + kγ₂ = B₂, attained (read of −Rem⁰ = c₀τz₁^{ε′} ≠ 0);
* slot k+1: −R¹ on line ≥ e₁(β*−e₀h₀)+(k+1)γ₂ = B₂+h₁; −Q⁰ on line
  ≥ e₁(β*−w₁Φ₁)+(k+1)γ₂ = B₂+h₁ (w₁Φ₁ = e₀h₀ at g₀ = 1) — both > B₂;
* slot k+2 (only if Q¹ ≠ 0): line ≥ e₁(β*−2e₀h₀)+(k+2)γ₂ = B₂+2h₁ > B₂
  (off-grid at e₁ ≥ 3; on-grid-above-line at e₁ = 2 — read 0 either way).
  **[errata r1 (PE-N3): the e₁ = 2 branch of this parenthetical is vacuous
  in the proved region — Q¹ ≠ 0 with k+2 ≤ e₁−1 forces e₁ ≥ 3 (at e₁ = 2 a
  Q¹ ≠ 0 pair lands in DCX); harmless defensive text, kept as such.]**

So w₂(E₀) = B₂; grid s₂(B₂) = k (L1, δ₂ = 1); the j = 0 read coefficient is
C₀ = ε₁(β*)·c₀τ·z₁^{ε′} = c₀c₁·ε₁(B₁) = (−z₁)(−z₂)·ε₁(B₁)
= z₂^{δ₂}z₁^{δ₁}ε₁(B₁) (δ₂ = δ₁ = 1; the same EPS-MULT cancellation
ε₁(β*)ε₁(γ₂)^{−1} = z₁^{−ε′}ε₁(B₁)); higher grid slots: zero digits or the
above-line/off-grid slots listed. R2v(E₀) = z₂z₁ε₁(B₁). Top level verbatim
as in S4.5 (slot S₃ on-line at B₂; slot S₃+1 at line ≥ Γ″+h₂):
val₃(P) = z̄^{δ₃}ε₂(B₂)z₂^{δ₂}z₁^{δ₁}ε₁(B₁). ∎

**Case II-3 (S₂ = e₁−1, δ₂ = 0).** Only the A₁-slot overflows:
Φ₁^{S₂+1} = Φ₁^{e₁} = Φ₂ − Ĉ, so

    P = A₁·Φ₂^{S₃+1} + [A₀Φ₁^{e₁−1} − A₁Ĉ]·Φ₂^{S₃}.

E₁ := A₁: slot S₃+1 line = Γ″ + h₂ + e₂h₁ > Γ″ (compute with
B₂ = e₁B₁+(e₁−1)γ₂: e₂e₁(B₁−e₀h₀) + (S₃+1)γ₃ − Γ″ = (γ₃−e₂e₁γ₂) +
e₂(γ₂−e₁e₀h₀) = h₂ + e₂h₁). E₀ := A₀Φ₁^{e₁−1} − R¹ − Q¹Φ₁. **Provided
e₁ ≥ 2 OR Q¹ = 0** (outside DCX), E₀ is a digit, with slot e₁−1 carrying A₀
(w₁(A₀) = B₁, line e₁B₁+(e₁−1)γ₂ = B₂), slot 0 carrying −R¹ (line ≥
e₁(β*−e₀h₀) = B₂+h₁), slot 1 (if Q¹ ≠ 0, e₁ ≥ 3... at e₁ = 2 slot 1 = e₁−1
COLLIDES with A₀'s slot — benign: w₁(Q¹) ≥ β*−2e₀h₀ = B₁ + (γ₂−2e₀h₀) =
B₁ + h₁ > B₁ at e₁ = 2, so the collision adds an above-line summand inside
the digit and the exact-w₀ residues are unchanged) — all non-A₀
contributions strictly above B₂'s line. So w₂(E₀) = B₂; grid s₂(B₂) =
S₂ − 0 = e₁−1; the j = 0 coefficient is C₀ = ε₁(B₁)·R_{1,B₁}(A₀)(z₁) =
ε₁(B₁)·(−c₀) = z₁^{δ₁}ε₁(B₁) (A₀'s single Φ₀-digit −ĉ₀π^{U+h₀} at abscissa
S₁″ = s(B₁), w₀ = U+h₀ = u(B₁) exact — L1 at δ₁ = 1); higher grid slots
zero/above-line. R2v(E₀) = z₂⁰z₁^{δ₁}ε₁(B₁), matching δ₂ = 0. Top level as
before: val₃(P) = z̄^{δ₃}ε₂(B₂)z₂^{δ₂}z₁^{δ₁}ε₁(B₁). ∎

### S4.7 The open corner: (W-MULT-3-DCX)

**OPEN LEMMA (W-MULT-3-DCX).** W-MULT-(3) (S4.3 display) for the pairs

    DCX = { (γ,γ′) ∈ W₃² : g₀ = g₁ = 1, δ₁ = 1, s₂(γ) = s₂(γ′) = e₁−1,
            S₁ + s(γ₂) ≥ 2e₀ }
        (equivalently: double cascade with ω := S₁−e₀+s(γ₂) ≥ e₀ and the
         extreme middle track s₂ = s₂′ = e₁−1; EMPTY unless e₀ ≥ 3).

**Exactly what breaks:** on DCX the DEV-1 carry Q¹ ≠ 0 lands at Φ₁-slot
k+2 = e₁ (Case II-2 at S₂ = 2e₁−2) or slot 1 = e₁ (Case II-3 at e₁ = 1),
i.e. the reduced digit RE-OVERFLOWS Φ₂: a second Φ₂-round
Φ₁^{e₁} = Φ₂ − Ĉ fires on Q¹, feeding a new Ĉ-product back into slot 0 and
a new term into Φ₂-slot S₃+1. The rewriting is FINITE (each Φ₂-round
strictly drops the total degree of the slot-S₃ cofactor) but its read
assembly needs a level-2 analogue of DEV-1 — a bounded Φ₂/Φ₁/Φ₀ reduction
engine with 𝔯-transparency across Ĉ-insertions ("DEV-2"). **Price:** one
dedicated unit (state DEV-2 with the Ĉ-insertion transparency clause
𝔯₂(XΦ₁^{e₁}) = 𝔯₂(XΦ₂) − 𝔯₂(XĈ) and the degree induction; then S4.6
closes verbatim with Q¹'s tree replaced by its DEV-2 normal form).

**Instance evidence (cited as such, NEVER a proof step):** sealed roster
row B = (1; 3,2,1; 2,1,1; 2,1,1) has e₀ = 3, g₀ = g₁ = 1, γ₂ = 13,
s(γ₂) = 2 (ℓ₀ = 2), so DCX pairs are exactly those with s₁ = s₁′ = 2,
s₂ = s₂′ = 1 (then S₁+s(γ₂) = 6 = 2e₀, ω = 3 = e₀), realized in every
W1×W1 block (all E₃ split-triples occur once per window — the COR-4
bijection); the sealed G2/G3 families printed 0 violations on all 52 towers
× all blocks (ITERLAWR S5: G2 0/13,440, G3 0/13,440), row B over 4 rings
included, and the m4-supplement re-ran the battery on M4A/M4B (0/19,792).
So (ITER-LAW-3) and the W-MULT-(3) shape are instance-true ON DCX at every
probed instance; the display above is the exact honest gap in the PROOF.

## S5. The theorem

*Proof of (ITER-LAW-3) (off DCX unconditionally; on DCX assuming
(W-MULT-3-DCX)).* Let γ, γ′ ∈ W₃; then Γ″ = γ+γ′ ∈ W₃ (WINDOW). By L6-(3)
at Γ″ (ε-values are units) and W-MULT-(3):

    c₃(γ,γ′) = val₃(φ_γφ_{γ′})/val₃(φ_{Γ″})
             = z̄^{δ₃} · [z₂^{δ₂}ε₂(B₂)/ε₂(β₂″)] · [z₁^{δ₁}ε₁(B₁)/ε₁(β₁″)].

Level-2 bracket: β₂″ = B₂ + δ₃γ₃ (L2-(3a)), so EXP-KIT(c) at
(e₁,h₁,ℓ₁,z₂) with T = δ₃γ₃ gives z₂^{D₂}, D₂ = (s₂+s₂′−s₂″+ℓ₁γ₃δ₃)/e₁ ∈ ℤ.
Level-1 bracket: β₁″ = B₁ + Σ (L2-(3b)), so EXP-KIT(c) at (e₀,h₀,ℓ₀,z₁)
with T = Σ gives z₁^{D₁}, D₁ = (s₁+s₁′−s₁″+ℓ₀Σ)/e₀ ∈ ℤ. Hence

    c₃(γ,γ′) = z̄^{δ₃}·z₂^{D₂}·z₁^{D₁},

the sealed display verbatim; the internal carries δ₂, δ₁ cancel inside the
per-level kernels and do not appear in the law. ∎

## S6. Corollaries (derived, not guessed; per-item conditionality displayed)

Convention: "on the proved perimeter" = for pairs (or triples all of whose
constituent pairs are) outside DCX; every item is unconditional once
(W-MULT-3-DCX) closes. Integer-level items are unconditional NOW.

### S6.1 COR-1: integrality (the sealed G4 family as a theorem)
e₁ | (s₂-defect + ℓ₁γ₃δ₃) and e₀ | (s₁-defect + ℓ₀Σ) for ALL pairs
(D₂-INT, D₁-INT — integer layer, unconditional). The per-level denominator
architecture is exactly as converged: each eⱼ₋₁ cured inside its own level's
kernel; NO e₀e₁ denominator ever forms (L3FINGER S8's measured FP7, now
structural).

### S6.2 COR-2: the cocycle identity (sealed G5)
For a, b, t ∈ W₃: c₃(a,b)·c₃(a+b,t) = c₃(b,t)·c₃(a,b+t).
*Structural proof (on the proved perimeter):* by W-MULT-(3) + L6-(3),
c₃(γ,γ′) = z̄^{δ₃(γ,γ′)}·F(γ)F(γ′)F(γ+γ′)^{−1} with F(γ) := val₃(φ_γ): a
coboundary times z̄^{δ₃}; and δ₃ is a 2-cocycle: by L1 at (e₂,h₂),
associating both ways, e₂[δ₃(a,b)+δ₃(a+b,t)] = s₃(a)+s₃(b)+s₃(t)−s₃(a+b+t)
= e₂[δ₃(b,t)+δ₃(a,b+t)]. ∎
*Closed-form proof (UNCONDITIONAL, all triples, integer level):* the
exponent tables satisfy the additive cocycle identity slotwise:
δ₃-slot as above; D₂-slot: D₂(a,b)+D₂(a+b,t) = [s₂-defects telescope to the
symmetric s₂(a)+s₂(b)+s₂(t)−s₂(a+b+t)]/e₁ + ℓ₁γ₃[δ₃-total]/e₁, symmetric;
Σ-slot: Σ(a,b)+Σ(a+b,t) = γ₂[D₂-total] + γ₃(ℓ₁′−ℓ₁w₁Φ₁)[δ₃-total],
symmetric; D₁-slot likewise with ℓ₀[Σ-total]. So the DISPLAYED law is a
2-cocycle on the nose (M2 S2(iv)'s measured fact, now proved), and on DCX
the measured c₃ satisfies the identity as soon as the display holds there. ∎

### S6.3 COR-3: degenerations (sealed G6; all unconditional — DCX needs δ₁ = 1 ∧ g₀ = 1 ∧ e₀ ≥ 3, none of which survives the respective degeneration)

**[ERRATUM (errata round 1, 2026-08-03; convergent findings PC-F2 [CRITICAL]
= PE-F1 [CRITICAL]; reports `ITERLAW3_passPC_report.md` (997c467) /
`ITERLAW3_passPE_report.md` (be9a77b)): the header clause "all unconditional
— DCX needs δ₁ = 1 ∧ g₀ = 1 ∧ e₀ ≥ 3, none of which survives the respective
degeneration" is STRUCK. The DCX predicate (S0.4/S4.7) has NO e₂-condition,
and at e₁ = 1 the track condition s₂(γ) = s₂(γ′) = e₁−1 = 0 is automatic
(ENLARGING the locus — S4.7 itself displays the e₁ = 1 DCX flavor: "slot
1 = e₁ (Case II-3 at e₁ = 1)"). Executed witnesses (PE pass): the e₂ = 1
tower (3,2,1)(2,1,1)(1,1,1)/ℤ₅ realizes 4 DCX pairs per W₁×W₁-equivalent
block; the e₁ = 1 battery tower TW2 = (4,1,1)(1,3,1)(2,1,1)/F₃[[t]]
realizes 48. CORRECTED CLAIM OF RECORD: the e₂ = 1 (CX) and e₁ = 1 (CW)
FIELD-LEVEL clauses below hold on the proved perimeter (off DCX, the S6
preamble convention) — unconditional exactly where DCX is empty, i.e.
e₀ ≤ 2, and unconditional in full once (W-MULT-3-DCX) closes. Genuinely
unconditional NOW (PE-verified, machine-checked): every INTEGER-LEVEL
reduction displayed below (e₂ = 1: δ₃ = 0, β₂(γ) = γ, D₂ = δ₂, Σ = γ₂δ₂,
D₁ = the accepted exponent; e₁ = 1: D₂ = 0, Σ = δ₃γ₃; e₀ = 1: D₁ = 0), and
the CV bullet in FULL (e₀ = 1 contradicts DCX's e₀ ≥ 3, and DCX needs
S₁ ≥ e₀+1 ≥ 2 > 0 = S₁|_{e₀=1}). With this re-scope the S0.4 status-row
note "(conditionalities displayed per-item)" is accurate.]**

* **e₂ = 1** (control CX): s₃ ≡ 0, δ₃ = 0, β₂(γ) = γ; D₂ = δ₂, Σ = γ₂δ₂
  (L1), D₁ = (s₁-defect + ℓ₀γ₂δ₂)/e₀ — **the ACCEPTED order-2 law verbatim
  in the letters (z₂, z₁)** [IL S0 THEOREM under the S0.3 dictionary]; the
  level-3 anchors coincide with the level-2 anchors (Φ₂-exponent 0) and the
  proof specializes to Case I + the accepted L7. This is the exact e₂ = 1
  embedding the sealed F0b tested (0/64) and the (ITER-LAW-n) descent rung.
* **e₁ = 1** (control CW): s₂ ≡ 0, ℓ₁ = 0, ℓ₁′ = 1: D₂ = 0, Σ = δ₃γ₃,
  c₃ = z̄^{δ₃}·z₁^{(s₁-defect+ℓ₀γ₃δ₃)/e₀} — the sealed CW display.
* **e₀ = 1** (control CV): s₁ ≡ 0, ℓ₀ = 0: D₁ = 0,
  c₃ = z̄^{δ₃}·z₂^{D₂} — the sealed CV display.
  (Iterating: any two of e₀, e₁, e₂ equal 1 gives the pure single-carry
  law z^{δ} one level; all three: c₃ ≡ 1 — the E₃ = 1 leg is trivially
  covered, cf. the S0.1 class-coincidence display.)

### S6.4 COR-4: ℤ/E₃ descent and representative independence (sealed G7)
γ ↦ γ + E₃ fixes s₃ (E₃ ≡ 0 mod e₂), shifts u₃ by e₀e₁, hence β₂ by e₀e₁;
fixes s₂ (e₀e₁ ≡ 0 mod e₁), shifts β₁ by e₀; fixes s₁, shifts u₁ by 1 — so
φ_{γ+E₃} = π·φ_γ exactly, and every constant of the display (δ₃, D₂, Σ, D₁)
depends only on (γ mod E₃, γ′ mod E₃): the closed form descends to ℤ/E₃
(unconditional). The gauge does NOT descend: by EXP-KIT(a),
F(γ+E₃)/F(γ) = ε₂(β₂+e₀e₁)/ε₂(β₂) · ε₁(β₁+e₀)/ε₁(β₁)
= z₂^{−ℓ₁e₀}·z₁^{−ℓ₀} =: ρ, a CONSTANT monodromy — only weight-matched
RATIOS descend (M2 S2(iii)'s measured ρ, now an identity; on the proved
perimeter the measured c₃ therefore descends too, mixed blocks included —
the sealed G7 family and the COR-4 lesson).

### S6.5 COR-5: the gauge form (the convergence judgment's row 6)
On the proved perimeter: **c₃ = z̄^{δ₃}·∂F**, F(γ) = ε₂(β₂(γ))·ε₁(β₁(γ))
= val₃(φ_γ), with the closed monomial form (EXP-KIT(a) twice)

    F(γ) = z₂^{(s₂(γ) − ℓ₁β₂(γ))/e₁} · z₁^{(s₁(γ) − ℓ₀β₁(γ))/e₀},

both exponents integral. Modulo the single top carry the entire law is the
explicit coboundary of the ε-chain — M2's gauge decomposition (44/44
measured) as a theorem. The H²-class statement class(c₃) =
[z̄^{(E₃/e₂)ℓ₂}·z₂^{e₀ℓ₁}·z₁^{ℓ₀}] stays CITED-MEASURED (M2 S3, 42/42;
single-source row 11 of the convergence matrix) — the ρ-monodromy leg above
is proved here, the δ₃-telescope class computation is NOT re-derived in this
note; flagged for the n = 4 prereg (F-CLASS), not consumed by anything
below.

### S6.6 COR-6: the exponent recursion — (ITER-LAW-n) at n = 3, derived

**[ERRATUM (errata round 1, 2026-08-03; convergent findings PC-F3
[CRITICAL, nominal] = PE-N2; rung relabel per the 997c467 adjudication,
aligned with the dated RUNG-INDEXING bracket at the head of
`ITERLAW4_PROBE_2026-08-08.md`): naming only, no math content changes. Per
the L3CONVERGENCE convention (an (n+1)-read tower = rung n), this 3-READ
theorem is **RUNG n = 2** of (ITER-LAW-n); the "at n = 3" in this section's
title, in the display sentence below, in the S1 close, and in the S0.4
status row counts READS (3 reads, matching the note NAME "ITERLAW3"), not
the rung index. The 4-read battery (ITERLAW4_PROBE, verdict 13b026b) is
RUNG n = 3. The confirmed-rungs sentence below already uses the RUNG
convention and stands as written; the rung ledger of record: n = 1 PROVED +
ACCEPTED (2-read, the accepted order-2 law), n = 2 PROVED-OFF-DCX at
attempt grade + MEASURED (3-read, this note), n = 3 MEASURED GREEN (4-read
battery).]**

With S₂ᵗᵒᵖ := δ₃γ₃ and S₁ᶜᵒᵐᵖ := Σ, the proved display is EXACTLY the
uniform recursion of L3CONVERGENCE S2 Candidate 2 at n = 3:

    S_2 = δ·γ₃ (δ = δ₃);  D_2 = (s₂-defect + ℓ₁S_2)/e₁;
    S_1 = D₂γ₂ + S_2·(ℓ₁′ − ℓ₁w₁Φ₁);  D_1 = (s₁-defect + ℓ₀S_1)/e₀;
    c₃ = z̄^{δ}·z₂^{D₂}·z₁^{D₁},

i.e. the recursion's constants are the shadow of ∂F through one EXP-KIT
kernel per level — derived, not fitted. Confirmed rungs of (ITER-LAW-n):
n = 1 accepted [IL], n = 2 this note (off DCX); the n ≥ 3 recursion remains
conjecture-grade pending the ITERLAW4 probe (parallel wave-19 unit) and its
own compose.

### S6.7 COR-7: anchor-pair W-MULT product form (sealed G2(b))
val₃(φ_γφ_{γ′}) = z̄^{δ₃}·val₃(φ_γ)·val₃(φ_{γ′}) on the proved perimeter —
the second display of W-MULT-(3) (S4.3), recovered from pure development
bookkeeping; nothing here consumes or re-prices the accepted GRB (W-MULT)
one level down — on the contrary, the level-2 instance used is [IL COR-5],
already accepted.

## S7. Scope box — what is NOT proved here

* **(W-MULT-3-DCX)** — the S4.7 open corner (needs e₀ ≥ 3 + extreme middle
  track + double cascade). THE one honest gap of this note; instance-true
  on every probed instance; price displayed in S4.7.
* **General lawful lifts.** The proof consumes Φ₁'s standard-lift two-term
  shape (inside DEV-1 and [IL S4 L7 Case II]) and Φ₂'s canonical
  ε₁-corrected form (WELL-DEF; the ε′-cancellation in S4.5/S4.6 is exactly
  where the correction is spent). (ITER-LAW-LIFT) propagates: nothing is
  claimed for any other lawful lift at any level; the measured plain-lift
  deviation is (LIFT-DEV-3) = ε₁(γ₂)^{δ₂} at g₁ = 1 (L3XCHECK S7,
  conjecture-grade, sealed cycle owed — consistent with, and now explained
  by, the S4.5 mechanism, but NOT proved here).
* **Orders ≥ 4.** Untouched; COR-6's recursion display at n ≥ 3 is
  conjecture pending the parallel n = 4 probe unit **[errata r1: the
  "n ≥ 3" here is already RUNG-indexed (= orders ≥ 4); the "n = 4 probe"
  counts READS — its battery is RUNG n = 3, see the S6.6 rung bracket]**.
* **The gr(w₃) semantics wrapper and the H²-class.** The theorem is about
  the harness calculus objects (S0.2), exactly as the accepted note's scope;
  the graded-algebra identification and the class invariant stay
  consumer-side (M2 S3/S6 conjecture-grade; MOVES carry-algebra echo
  likewise).
* **GMN transport.** FGMN-calculus-internal throughout; the GMN side is the
  TWIST-3/TR3-S4 lane, not touched.
* **No record edits.** ITERLAW / ITERLAWR / the five method notes /
  L3CONVERGENCE / DITER_RESTATE are byte-untouched; the sealed artifacts are
  cited read-only. Display upgrades ride the next r-fold (S9).

## S8. Verification-readiness (for the next wave's hostile passes; 2-clean bar)

**Claim DAG (arrows = "consumed by"):**

    [IL L1] ─→ L2-(3a), D₂-INT, L2-(3b), D₁-INT, WINDOW, CASE-SPLIT, S4.5/6 grids
    L2-(3a) ─→ D₂-INT ─→ L2-(3b) ─→ D₁-INT, WINDOW, S5
    EXP-KIT(a,b,c)  [self-contained] ─→ S4.5/S4.6 (ε′-cancellation), S5, S6.4/6.5
    WELL-DEF ─→ S4.5, S4.6          DIGIT-SPLIT ─→ DEV-1 ─→ S4.5, S4.6
    [IL L6] ─→ L6-(3)               [IL L7 + displayed devs] ─→ CASE-SPLIT, S4.4
    L6-(3) + W-MULT-(3) ─→ S5 (THEOREM) ─→ S6.2(structural), S6.3–S6.7
    (W-MULT-3-DCX) [OPEN] ─→ S5 on DCX only

**Per-claim checkable falsifiers (all against EXISTING sealed artifacts; NO
new numerics were run by this unit — any future spot-check is a post-seal
diagnostic and must be labeled as such):** L6-(3) ↔ sealed G1 (0/1,344);
W-MULT-(3) both forms + single-top-slot shape ↔ G2 (0/13,440); the theorem ↔
G3 (0/13,440) + M5's 248/248 + M1's holdout 588/588 + M2's 1,616/1,616 + M3's
6,320/6,320 + M4's 0/1,600; COR-1 ↔ G4; COR-2 ↔ G5 (0/9,408) + M2/M4 triple
scans; COR-3 ↔ G6 + F0b + M3 S3; COR-4 ↔ G7 (0/26,880, mixed blocks); the
integer layer ↔ G8 (0/20,000 symbolic). Suggested hostile-pass charges:
(i) content pass on S4.5/S4.6 (the DEV-1 induction, the sign bookkeeping,
the collision cases at e₁ = 2 and e₂ = 1 — the places an error would hide);
(ii) an execution pass implementing DEV-1 + the S4.5/S4.6 digit predictions
FROM THIS NOTE ALONE on off-roster towers (the F2c genre), including a
DCX-locus meter confirming the proved/open boundary is where this note says
it is (predicted: engine-vs-harness agreement everywhere; DCX pairs occur
only at e₀ ≥ 3 with s₂ = s₂′ = e₁−1).

**Erratum surface (declared):** the exact-line-number code pins (S0.2, the
header) were read from the working tree at composition time; if any drift,
the pinned FUNCTION NAMES govern.

**[POST-SEAL DIAGNOSTIC (labeled; run at composition, NOT a proof step, NOT
part of any seal):** `verification/openmath/iterlaw3_proof_diag.py` +
`iterlaw3_proof_diag_output.txt` — the note's NEW intermediate claims
(CASE-SPLIT partition; Φ₂-digit slot support ⊆ {S₃, S₃+1} with S₃ present;
w₂(E₀) = B₂; R2v(E₀) = z₂^{δ₂}z₁^{δ₁}ε₁(B₁); the full W-MULT-(3) value)
cross-checked against the harness of record on 5 fresh g₁ = 1 tower shapes
× {ℤ₃, F₂[[t]]} (incl. g₀ = 2 II-1, e₁ = 3, e₁ = 1, and two e₀ = 3 DCX-live
shapes), full W1×W1 blocks: **1,424 pairs, case census I 912 / II-1 368 /
II-2 40 / II-3 88 / DCX 16, ZERO violations, first run** — the DCX census
lands exactly on the note's predicted locus (4 pairs per DCX-live tower:
s₁ = s₁′ = e₀−1... the s₂ = s₂′ = e₁−1 ∧ ω ≥ e₀ combinations, s₃ free), and
the checked identities hold ON the DCX pairs too (instance evidence for
(W-MULT-3-DCX), consistent with the sealed record — the PROOF there stays
open).]**

## S9. Consumers and owed displays (ride the next r-fold; NOT applied here)

* L3CONVERGENCE S2 Candidate 1 status: measured law → **PROVED on the class
  off DCX at attempt grade** (this note); the S2 "conjecture-grade" brackets
  stay until the hostile arc closes — display upgrade owed AT ACCEPTANCE,
  not before.
* ITERLAWR S5 "Standing of the law": same owed bracket at acceptance
  (measured law → proved-on-class, DCX residual displayed).
* The ITERLAW4 probe unit (parallel): its F0/F-SUB legs may cite this note's
  S6.3 (e₂ = 1 embedding proved) once accepted; until then instance-grade
  wording stands. **[errata r1 (PC-F2 = PE-F1): the parenthetical is
  corrected to "e₂ = 1 embedding proved OFF-DCX" — any future cite must
  carry the DCX conditionality on DCX-live e₂ = 1 towers (witness:
  (3,2,1)(2,1,1)(1,1,1)/ℤ₅ realizes 4 DCX pairs per block), per the S6.3
  erratum. Out-of-fence sweep at errata r1: NO existing consumer cites
  S6.3 unconditionally — ITERLAW4_PROBE's F0b/F-SUB legs cite the sealed
  MEASURED (ITER-LAW-3), not this note's corollary; L3CONVERGENCE does not
  cite this note; ITERLAWLIFT_CORNER's "COR-3" reference is the accepted
  order-2 note's COR-3 (e₀ = 1 leg, theorem-backed there, unaffected).
  Nothing owed beyond this bracket.]**
* HARDEST_FIRST / PROJECT_STATE / ROOT: (ITER-LAW-3) row gains "proof
  composed, attempt grade, DCX corner open, hostile arc owed" — at the
  r37 fold.
* The (W-MULT-3-DCX) unit (DEV-2 engine) enters the wave-20 candidate
  queue with the S4.7 price display.

— (ITER-LAW-3) proof compose unit, wave 19 unit 2, campaign date 2026-08-08
(wallclock 2026-08-03).
