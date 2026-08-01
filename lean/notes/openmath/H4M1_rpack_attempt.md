# H4M1-rpack — attempt (Fable prover H4-M1, 2026-08-06)

## Unit charge and resolution in one paragraph

*(Unit H4-M1 of `lean/blueprints/HDISCHARGE_H4.md` §M: the (R1)–(R3) re-scoping
pass over W(F_q) — a derivation-grade walk of §B2-DEF's displays
D.0/(S1)–(S6)/D.1/D.3(e)/D.9(a) (MOVES_2026-07-24.md line 1849 ff., ACCEPTED)
over an arbitrary finite residue field, per the blueprint §2's eight-section
plan. Named duties executed: the step-1 Lemma-2 connective display (Codex fold
finding 13, §1.3 below); the step-5 base-clause onto-ness checkpoint (finding
4, §5.5); the step-7 consumption audit (§7); the step-8 δ-instance display +
the (EQ-1) slice check that H4-M6 consumes (finding 8, §8). Gate N-T4 was run
BEFORE this pass — record in §N at the end (ALL PASS, one test-spec defect
found and repaired in the test itself, not in the theory).)*

RESOLUTION. M14's (R1), (R2), (R3) (`M14-eq2-alphabet_attempt.md` §2) are
PROVED over A^(q) := W(F_q)[x] for an ARBITRARY finite field F_q, q = p^f, at
the perimeter displayed in §0.4: every §B2-DEF tower over W(F_q) presented by
the base + standard-lift-increment recipe with re-built residue data and
(I-aug) reads satisfies (S1)–(S6) with the D.0 scale bookkeeping (§§1–4), the
D.3(e) digit/alphabet displays (§5), and the D.9(a) weight-set recursion with
its base clause (§6). Base ℤ_p is the q = p instance and base O_δ = W(F_{p^δ})
is the q = p^δ instance of the ONE theory (§8) — the blueprint's strategic
decision, executed. The consumption audit (§7) closes with NO perimeter
widening: no §A/§B1 residue-theoretic statement is consumed beyond the items
re-proved here, and none of REL.1's counting layer (Theorem C(a)/(b),
PIN-WELLDEF, (ZC)) is touched. Two genuinely new base-touch displays surfaced
by the walk, both repaired in place: the Frobenius-twist reconciliation
between leaf coordinates and leading residues ((O4), §0.2 — invisible at
q = p), and the x-dependent base-clause realizer family (§5.5 — constants
realize only F_q ⊊ F₁ at d > 1; the finding-4 correction, now a displayed
lemma). Nothing here discharges (R4) or the (a6)/(EQ-1) matching dictionary
(unit H4-M2), and nothing here re-scopes the run-production layer D.8/D.10
(REL.1's wider walk); §0.4 and §7 display the exact fence.

## The two governing rules, quoted (and obeyed)

**The mutatis-mutandis rule** (REL.1, MOVES ~9382; quoted verbatim):

> "hold over O_δ under (R0-box)–(R0-ledger) MUTATIS MUTANDIS, NOT verbatim
> (pass-1 gap 2): every residue-theoretic object — base residue field,
> residual polynomials, tower fields, graded pieces, attainable images,
> irreducibility conditions, residue bases — is RECONSTRUCTED over F_δ, never
> obtained by substituting a cardinality (the re-based tower is not the scalar
> extension of the old one); only the base-independent skeleton (coefficient
> order, unitriangular polynomial identities, valuation geometry, pin-status
> arguments, additive equal-fiber counting) carries over as written."

Blueprint gloss, also binding: "The LAWS' statements are verbatim; the objects
are rebuilt." Every display below marks its objects [REBUILT] or its steps
[SKEL] accordingly; §7 is the ledger of those marks.

**The walk-order rule** (REL.1, MOVES ~9397): "Walk order — the one flagged
hiding spot FIRST: (i) TYP(a)'s per-digit linearity: the accepted text reads
'per-digit 𝔽_p-linear on the base coordinates …'; over O_δ this must RETYPE
to per-digit ADDITIVE on O_δ-digit blocks (F_δ-linearity is the EXPECTED
outcome, walked not available by fiat; additivity is all TYP(b) consumes)."
Obeyed: the retype checkpoint is §1.2, executed before anything else in the
walk consumes a digit display.

## §0 Setting, base-ring inputs, and the walk's perimeter

### 0.1 The re-based ring

Fix q = p^f. O_q := W(F_q), the Witt vectors of F_q; A^(q) := O_q[x]. v_p :=
the valuation of O_q normalized v_p(p) = 1 (W(F_q) is absolutely unramified:
p generates the maximal ideal — Serre, *Corps Locaux* II §5–6); v := the Gauss
valuation on A^(q), v(Σ aᵢxⁱ) = minᵢ v_p(aᵢ). Class remark (blueprint §2): an
absolutely-unramified complete DVR with finite residue field F_q IS W(F_q)
(Serre II §5, Thm 3/4), so quantifying over q covers exactly the {O_δ} family
and the root instance ℤ_p = W(F_p) at once.

Base-ring facts consumed, displayed once (each (a) known — Serre II §4–6):

- **(O1)** O_q is a complete DVR with uniformizer p, v_p(p) = 1, residue field
  O_q/pO_q = F_q, and the reduction O_q ↠ F_q is SURJECTIVE.
- **(O2)** **Leading residues.** For v_p(b) ≥ n define r_n(b) :=
  (p^{−n}·b) mod p ∈ F_q. Canonical (no section chosen); ADDITIVE on
  {v_p ≥ n} (divide by p^n, then apply the reduction ring hom); r_n(b) ≠ 0
  ⟺ v_p(b) = n on that domain.
- **(O3)** **Witt leaf coordinates.** b ↦ (b⁽⁰⁾, b⁽¹⁾, …), b⁽ⁿ⁾ ∈ F_q, with:
  v_p(b) = min{n : b⁽ⁿ⁾ ≠ 0}; and sums/products are digit-level unitriangular
  with UNIVERSAL carry polynomials over F_p — (b + b′)⁽ⁿ⁾ = b⁽ⁿ⁾ + b′⁽ⁿ⁾ +
  C_n(b⁽<ⁿ⁾, b′⁽<ⁿ⁾) with C_n the mod-p reduction of Witt's integral S_n
  (C_n(X, 0) = 0), products propagating strictly upward likewise (Serre II
  §6).
- **(O4)** **The twist display (NEW at q > p; invisible in the accepted
  text).** On {v_p(b) ≥ n}: b⁽ⁿ⁾ = r_n(b)^{p^n}. *Proof.* b = p^n·u; over a
  perfect residue field p = V∘F on W, so p^n u = V^n F^n u has components
  (0, …, 0, u⁽⁰⁾^{p^n}, …), and r_n(b) = u mod p = u⁽⁰⁾. ∎ At q = p the
  Frobenius is trivial and the two coordinate systems coincide — which is why
  the accepted §B2-DEF text never shows the twist. Over F_q it is a
  PER-ADDRESS F_p-linear bijection of the digit value space, so every
  unitriangularity, disjointness, and equal-fiber count is indifferent to the
  choice; but each display must FIX one. **Convention:** all (S5)/D.3(e)
  digit VALUES below are leading residues r_n (matching D.2's ū :=
  B/p^{v(B)} mod (p, φ)); Witt components serve only to certify (O3), and
  (O4) is the reconciliation whenever a leaf address is read at its minimal
  height.

### 0.2 Lemma ONTO (the finding-4 mechanism, displayed once)

Base stage data: φ ∈ A^(q) monic, deg_x φ = d ≥ 1, with φ̄ IRREDUCIBLE OVER
F_q — a [REBUILT] condition on the re-based datum, never inherited from
F_p-irreducibility (x² + x + 1 is irreducible over F₂ and splits over F₄).
F₁ := F_q[x]/(φ̄) = O_q[x]/(p, φ), a field, [F₁ : F_q] = d; θ := x̄;
C₁ := {B ∈ A^(q) : deg_x B < d}.

**Lemma ONTO.** For every v ≥ 0 the height-v base digit reading

  D_v : {B = Σ_{m<d} b_m x^m ∈ C₁ : min_m v_p(b_m) ≥ v} → F₁,
  D_v(B) := Σ_{m<d} r_v(b_m)·θ^m

is an ADDITIVE map ONTO F₁, with D_v(B) ≠ 0 ⟺ v(B) = v; and D_v(B) equals
the reduction (B/p^v) mod (p, φ) whenever v(B) ≥ v.

*Proof.* Additivity and the vanishing clause: (O2) per coefficient, plus
(θ^m)_{m<d} an F_q-basis of F₁ (so the reading vanishes iff every coordinate
does). Identification with the (p, φ)-reduction: B/p^v = Σ (b_m/p^v)x^m and
reduction mod (p, φ) reads each coefficient mod p and x as θ. ONTO: given
ξ = Σ_{m<d} ξ_m θ^m (ξ_m ∈ F_q — the θ-basis residue vector), choose ANY
b_m ∈ O_q with b_m mod p = ξ_m ((O1) surjectivity; no Teichmüller section —
any preimage), and set B := p^v·Σ b_m x^m; then D_v(B) = ξ. ∎

**Negative half (the finding-4 checkpoint's content).** A CONSTANT B ∈ O_q
reads to r_v(B)·θ⁰ ∈ F_q·1: constants — in particular Teichmüller units
τ(ζ) — realize exactly F_q ⊊ F₁ when d > 1. The base-clause realizer family
is therefore NECESSARILY x-dependent: it is p^v·C₁-lifts, not p^v·units of
O_q. (Consumed at §2 step (iv), §3 (S6), §5.5.)

### 0.3 Tower data (what "a §B2-DEF tower over O_q" quantifies over)

A tower is presented by the §B2-DEF recipe, all residue objects [REBUILT]:

- **Base datum** (φ, e₁, h₁): φ as in §0.2; gcd(e₁, h₁) = 1, h₁, e₁ ≥ 1.
- **Increment data**, per stage k = 1, …, K−1: ψ_k ∈ F_k[z] monic IRREDUCIBLE
  OVER THE RE-BUILT F_k, ψ_k ≠ z, g_k := deg ψ_k; the next key Φ_{k+1} := the
  D.5 standard lift; the next read (e_{k+1}, h_{k+1}), gcd = 1, satisfying
  (I-aug): h_{k+1}/e_{k+1} > w_k(Φ_{k+1}). Tower fields F_{k+1} :=
  F_k[z]/(ψ_k) — REBUILT, never F_k ⊗ F_q or a cardinality substitution.
- Recenterings are the g = 1 instances (ψ′ = z − c̃, c̃ ≠ 0, e_read = 1) per
  D.10's own reduction ("every recentering is the g = 1 case of the increment
  theory"); the recentering-specific residue (realizer EXISTENCE via Lemma
  REAL + (S6b), frame bookkeeping v = v′) is classified in §7, not walked.

### 0.4 Perimeter (displayed fence)

PROVED here: for every such tower, (S1)–(S6) hold at every stage with the D.0
bookkeeping ((R1)), the D.3(e)(i)/(ii) displays hold ((R2)), and D.9(a) holds
with its base clause ((R3)). NOT claimed here: (R4)/the (a6)/(EQ-1) matching
dictionary (H4-M2's unit); that the re-based CLASSIFIER RUN produces recipe
towers with (I-aug) reads — that is D.4 + D.8 + D.10's run-production layer,
REL.1's wider walk (D.4's three-bullet argument is itself walked base-free at
§3.4, so the residue of that fence is D.8/D.10 bookkeeping only); the
counting layer (not consumed — verified §7). This perimeter is exactly M14's
consumption shape: its §2 package quantifies over "the matched prefix over
O_δ" — a presented tower — and consumes nothing about how the run found it.

## §1 D.0 over W(F_q) — scales, conventions, and the flagged hiding spot

### 1.1 The stage datum and scale bookkeeping, walked

σ = (w, Φ, C, U, T, F, z) with A = A^(q) = O_q[x]. Per-item base touches:

- w : A∖{0} → ℤ a valuation, value GROUP ℤ, value set bounded below [SKEL —
  integer normalization; nothing residue-theoretic].
- Φ monic, C := {deg_x < deg_x Φ}, unique Φ-development by monic division
  [SKEL — monic division is defined over any commutative ring].
- U = explicit representatives p, φ = Φ₁, …, Φ_r ∈ A^(q); Y := [Φ] adjoined
  separately [SKEL — the representatives are literal elements of A^(q)].
- T carried as an INTEGER EXPONENT VECTOR over the representative list (P2)
  [SKEL — integer vectors; the transport formulas are Bézout arithmetic].
- F a finite field, z a degree-0 unit: F is [REBUILT] per §0.3 (F₁ =
  F_q[x]/(φ̄); F_{k+1} = F_k[z]/(ψ_k)); z is pinned by (P1)/D.7(vi) —
  monomial bookkeeping [SKEL] once the localization exists (§3).
- **Scale bookkeeping**: w(Σ B_j Φ^j) := min_j (e·w_prev(B_j) + j·h);
  w(Φ) = h; coefficient weights in e·ℤ [SKEL — arithmetic in the shared
  data]. Base display: w₁(c) = e₁·v(c) on constants, v the Gauss valuation of
  §0.1 with v(p) = 1 [(O1) — the ONE ring-level base touch of D.0; if O_q
  were ramified this display would shift, which is why "absolutely
  unramified" is part of the class statement].
- (P3) named-ring discipline, (P4) convention dictionary (R, R_anch, the
  absolute-slot form, the z-power relations with integrality from ht ≡ 1
  mod e) [SKEL — monomial identities and congruences].

### 1.2 FIRST CHECKPOINT — the retype of every 𝔽_p-typed reading (walked, not asserted)

Per the walk-order rule, the flagged hiding spot first. The walked slice's
F_p/F_Q-typed displays, enumerated, each with its retype:

- **(RT-1)** D.3(e)(ii.1) "digit_v(y_i) = digit_v(x_i) + (an F_p-polynomial
  in the digits at earlier addresses)". Over O_q the leaf addresses carry
  F_q-VALUED digits; the carries remain polynomial functions WITH
  F_p-COEFFICIENTS (the universal Witt carries (O3), reduced mod p), now
  evaluated on F_q-arguments. Type change: "one F_p-scalar per address" →
  "one F_q-digit per address, additively unitriangular". Reads at a minimal
  height reconcile with (S5) leading residues through the (O4) twist — a
  per-address additive bijection, so unitriangularity, block disjointness,
  and every equal-fiber count are unaffected. Walked at §5.2.
- **(RT-2)** D.3(e)(ii) base bullet "an F_p-linear BIJECTION between the
  block's digit vector and F₁". Retype: the reading D_v is an ADDITIVE
  bijection between the F_q-digit block (b̄_m)_{m<d} and F₁ (Lemma ONTO,
  kernel split off by the vanishing clause). Additive = F_p-linear
  automatically in characteristic p, so the verbatim sentence survives; but
  the WALKED claim is additivity + bijectivity only.
- **(RT-3)** D.3(e)(ii) "𝔸(γ) … an F_p-SUBSPACE of F_{k+1}" and "(ii.2) is
  an F_p-linear BIJECTION". Retype: additive subgroup / additive bijection
  (= F_p-structure for free, char p). SEPARATELY, the SET 𝔸(γ) is even
  F_q-stable — Lemma STAB, §5.4 — a two-line SET computation, carefully
  distinguished from any digit-MAP equivariance claim.
- **(RT-4)** D.3(e)(i) "each R_δ … ADDITIVE, F_Q-linear (unit lifts of F_Qˣ
  multiply pieces integrally)". Here F_Q is the BASE TOWER FIELD, not F_p:
  it re-bases to the REBUILT F₁ = F_q[x]/(φ̄), and the clause carries with
  its own mechanism (unit-lift multiplication through R's multiplicativity),
  walked at §5.1. No F_q-digit-block scalar structure is claimed by it.
- **(RT-5)** D.3(e)(ii.4) "an F_p-polynomial in strictly earlier f-digits":
  as (RT-1).

VERDICT of the checkpoint: every retype lands on ADDITIVITY (plus rebuilt
F₁-scalars where the accepted text already had F_Q-scalars). Nothing in the
walk claims F_q-linearity of any digit map. That claim has exactly one home:

### 1.3 The Lemma-2 connective display (finding 13's named duty)

M14 Lemma 2 (on file, `M14-eq2-alphabet_attempt.md` §4) proves: the height-γ
digit maps on graded pieces are F_q-EQUIVARIANT (via the Teichmüller action),
i.e. the full F_q-scalar structure the retype deliberately does not claim.
Its hypothesis package, item by item, against this walk:

| Lemma 2 consumes | supplied over W(F_q) at |
|---|---|
| (S1) w a valuation, multiplicative | §2 (base: B1.1 re-walk; step: D.7(iii) classification) |
| base display w₁(c) = e₁·v(c), w₁(p) = e₁ ≥ 1 | §1.1 (base touch (O1)) |
| D.0 stretch w_{k+1} = e_{k+1}·w_k on coefficients | §1.1 scale bookkeeping |
| (S4) (L^coeff)₀ = F | §3.1–3.2 |
| D.1(b)/(c)/(e): ties, initial forms of products, R_γ L₀-linear + R multiplicative | §4 |
| τ : F_q → O_q multiplicative, additive mod p | (a) known, Serre II §4–5 — consumed by Lemma 2's own proof, NOT by this walk |

Composition, displayed: the retyped coordinate statements (RT-1)–(RT-3)
assert additivity on F_q-digit blocks; adjoining rows 1–5 of the table — all
proved below — yields EXACTLY Lemma 2's hypothesis list, and Lemma 2's
conclusion is the F_q-scalar structure. Hence no scalar-structure gap opens
between this walk (additive, by design — REL.1 item (i): "additivity is all
TYP(b) consumes") and the on-file consumer (F_q-linear, by THEOREM). ∎

## §2 (S1)–(S3) over W(F_q)

Statements verbatim ((S1) valuation with value group ℤ; (S2) K1(Φ/w) slot
minimum; (S3) slot decomposition gr_γ(A) ≅ ⊕_j gr^C_{γ−jh}); objects rebuilt.

### 2.1 Base stage (the B1.1 four-step walk over O_q)

Setup: key φ per §0.2, read (e₁, h₁), w(Σ aᵢφ^i) := min_i (e₁·v(aᵢ) + i·h₁).

- **(i) Graded ring/submultiplicativity** [SKEL]. Product terms
  aᵢφ^i·b_jφ^j re-develop by monic division aᵢb_j = Qφ + r; monic division
  over the DVR O_q preserves Gauss lower bounds (each elimination step
  subtracts a φ-multiple by an already-bounded coefficient — the §A.1(i)
  computation verbatim, no residue data consumed), and the Q-term is
  strictly deeper by h₁. Iteration terminates on degree.
- **(ii) Degree-0 part** [REBUILT]. O_q[x]/(p, φ) = F_q[x]/(φ̄) = F₁, a FIELD
  by the re-based irreducibility datum (§0.2 — reconstructed, with the
  splitting counterexample displayed there); ρ := reduction mod (p, φ) on
  {deg < d, v ≥ 0} is a surjective ring hom (Lemma ONTO's identification).
- **(iii) Surjectivity** [REBUILT realizers]. The γ-piece is spanned by
  classes of p^v·û·φ^i over the slots {(v, i) : e₁v + i·h₁ = γ}, with û ∈ C₁
  a lift of any prescribed ū ∈ F₁ˣ — existence by Lemma ONTO (x-dependent at
  d > 1; the finding-4 correction already bites in this classical step).
- **(iv) Injectivity/dimension count** [REBUILT reading]. Per admissible
  slot i, the coefficient piece {v(a) ≥ v}/{v(a) > v} ≅ F₁ via the height-v
  reading D_v — additive, onto, kernel exactly {v > v} (Lemma ONTO); the
  count #slots = #degree-γ monomials π^a y^i matches [SKEL arithmetic].

Hence gr A^(q) ≅ F₁[π, y] (deg π = e₁, deg y = h₁), a domain, so w₁ is a
valuation (D.1(c)); value group ℤ from gcd(e₁, h₁) = 1 with w(p) = e₁ [(O1):
v(p) = 1 — named base touch] and w(φ) = h₁. **(S1) base ✓.** (S2) base is
definitional (the φ-development IS the defining decomposition) [SKEL].
(S3) base = step (iv)'s count, slotwise, plus additivity of monic division
[SKEL]. **✓**

### 2.2 (S2) at increment keys — the D.5 K1 walk

The standard lift Φ̂ := Φ^{eg} + Σ_{ψ_k ≠ 0} t_k Φ^{ek}: the t_k are (S6b)
realizers with digit scalar ψ_k ∈ Fˣ — scalars in the REBUILT current field
(§3.3 supplies them; range check h(g−k) ≥ h > e·w_prev(Φ) is (I-aug)
arithmetic [SKEL]). Equal weights, monicity, and R(Φ̂) = z^{m̂}·ψ(z) are
monomial computations in (P2) vectors + D.1(b) no-cancellation at distinct
exponents [SKEL].

Lemma K1(Φ̂/w), proof walked: (≥) is (S1) + ultrametric [SKEL]. (≤): pass to
gr, apply R (D.1(e), §4): Σ_j z^{jm̂}·R(B_j)·ψ(z)^j = 0 in L₀ = F[z^{±1}];
each term has ψ-adic order exactly j because ψ ∤ R(B_j) — the D.3(d) width
bound (§5.0): deg R_anch(B_j) < g [SKEL degree bookkeeping]; F[z^{±1}] is the
localization of the UFD F[z] at {zⁿ} and ψ ≠ z stays prime there — FIELD-
GENERIC facts over the rebuilt F [REBUILT object, SKEL argument]; a finite
sum of nonzero terms of pairwise distinct ψ-orders is nonzero. Contradiction.
**✓** — no step consumed the residue field's size or any ℤ_p-specific fact.

### 2.3 (S1)/(S3) at the next stage — D.7(i)–(iii) + D.6, classification walk

- D.7(i) submultiplicativity of w′: Lemma DIV(i) (K1 slot bookkeeping) + the
  (I-aug) strict-depth estimate — valuation arithmetic [SKEL].
- D.7(ii) K1(Φ̂/w′) definitional (w′ IS the slot minimum); (S3′) slot
  decomposition + Y′ transcendental [SKEL].
- D.7(iii) domain/valuation: leading slots multiply by DIV(iii):
  dig′(B)·dig′(B″) ≠ 0 in F′ := F[z]/(ψ) — a FIELD because ψ is irreducible
  over the REBUILT F [REBUILT]; value group ℤ from coefficient weights
  (D.9(b) cofiniteness, §6.3 — arithmetic) + gcd(e′, h′) = 1 [SKEL].
- D.6 DIV, walked: (i) K1 applied to the development of BB″ [SKEL]; (ii)
  D.1(b) ties [SKEL, §4]; (iii) reduce mod ψ: the Q-term dies, the left side
  is a product of nonzero elements of the FIELD F′ [REBUILT], forcing δ₂ = 1
  and dig′(R_dev) = dig′(B)·dig′(B″). No base touch beyond F′'s rebuild. **✓**

## §3 (S4)–(S6) over W(F_q)

### 3.1 (S4) base

U = {π} (representative p), L = F₁[π^{±1}, y^{±1}]; degree-0 monomials π^a y^b
need e₁a + h₁b = 0, so (a, b) ∈ ℤ·(−h₁, e₁): the degree-0 exponent group is
infinite cyclic generated by z := y^{e₁}π^{−h₁} (P1); L₀ = F₁[z^{±1}];
(L^coeff)₀ = F₁[π^{±1}]₀ = F₁. All monomial arithmetic over the rebuilt F₁
[SKEL given §2.1]. **✓**

### 3.2 (S4) at the next stage — D.7(iv)–(vi), classification walk

- (iv) Unit survival: R(ũ) monomial by (S5)/D.3(b), ψ ∤ c·z^k [SKEL].
- (v) (L′^coeff)₀ = F′: D := R(·) mod ψ additive per piece, multiplicative
  (DIV(iii)), injective (width < g); image ALL of F′ by the three displayed
  ingredients: (1) powers of in(p) supply unboundedly many coefficient
  weights — the weight of p is the base display e₁ stretched
  deterministically [(O1) once more]; (2) g consecutive positions in one
  piece — stride arithmetic + the D.9(b) bound [SKEL]; (3) F-scalars via
  (S6b) in the large-weight regime — §3.3's recursion, scalar group the
  REBUILT current field; then z̄^pos·{P(z̄) : deg P < g} = F′ because
  (1, z̄, …, z̄^{g−1}) is an F-basis of F′ [REBUILT basis fact, field-generic
  given ψ irreducible over F]. **✓**
- (vi) Exponent-group cyclicity, V′ transport, z′ pinning: (P2) integer-
  vector arithmetic + the F′-line statement of (v) [SKEL].

### 3.3 (S5) and (S6), both tiers

**(S5) base**, walked: B ∈ C₁∖0: [B] = π^{v(B)}·ū with ū := D_{v(B)}(B) ∈ F₁ˣ
(Lemma ONTO's nonzero clause — this IS the [REBUILT] residue representative
reading the plan's step-2 named risk points at); dig(B) = ū·z^{−t₁v(B)} by
the D.2 monomial computation, which carries verbatim [SKEL]. At e = 1:
dig(B) = ū at position 0 (P2: t = 0). **✓** **(S5) next stage** = D.7(vii):
T′ pinned as a (P2) vector, the D.3(b) literal identity re-runs, stride and
width re-derive "in the new frame (nothing level-specific was used)" —
verified: the D.3 computations of §5.0 consume only (P2) pins, gcd Bézout
data, and D.1 [SKEL]. **✓**

**(S6a)** (exactness + basic realizers): the index set 𝒜 (base
{(e₁v, −t₁v) : v ≥ 0}; step 𝒜′ per D.7(viii)'s displayed formula with pos
instantiated by the Y′-exponent count) is integer-lattice bookkeeping [SKEL].
Basic realizers: base p^v·û with û a C₁-unit-lift of any prescribed
ū ∈ F₁ˣ — Lemma ONTO (x-dependent at d > 1); step t_{γ,j} := (stage
realizer)·Φ^j, dig′ = c·(forced monomial class) [SKEL given (S5)]. The
CONSTANT ORBIT GROUP re-bases to 𝒪_orb := (F₁^(q))ˣ — the units of the
REBUILT base tower field F₁ = F_q[x]/(φ̄). (Collision note: §B2-DEF writes
this group "O := F_Qˣ"; O_q here is the base RING — the two O's are unrelated
and this note never uses the bare letter for the group.) Closure under the
induction is trivial exactly as in the accepted text (same group asserted at
every stage). **✓**

**(S6b)** (full scalars above the key weight — the offset-P-lift): the claim
is stage-uniform realizability of ANY digit scalar in the CURRENT field's
unit group at every parent-scale coefficient weight W > w_prev(Φ). Walked:
the anchor offset m and the slot set are forced arithmetic [SKEL]; P ∈
F_prev[z] with deg P < g_prev and z̄^m·P(z̄) = target exists uniquely by the
basis fact of §3.2(3) over the REBUILT F′_prev [REBUILT]; the two-line mutual
recursion's inequalities — summand weights ≥ (W − (e_prev g_prev − 1)h_prev)/
e_prev > h_prev/e_prev > w_prevprev(Φ_prev) by (I-aug) at the previous read —
are pure arithmetic in the shared data [SKEL]; the recursion BOTTOMS at the
base: "digits are F_Q-unit lifts with no threshold" re-bases to: any
prescribed ū ∈ F₁ˣ at any base height e₁v is realized by p^v·û, û a C₁-lift —
Lemma ONTO again; the finding-4 correction lands at the recursion's bottom
too. **✓** Consumers' range checks (D.5's realizers; D.10's recentering lift)
are (I-aug) verbatim [SKEL].

### 3.4 D.4 (I-aug), briefly (the range-check supplier)

Walked in one pass, all three bullets: ROOT — on the initial cluster the lead
coefficient is a v-unit and every other coefficient has v ≥ 1, so every side
slope is positive [(O1)-level Gauss-valuation facts over O_q, verbatim];
AFTER AN INCREMENT — the landing-box chord/convexity computation in the
parent valuation [SKEL]; AFTER A RECENTERING — the same in the primed frame
[SKEL]. Base-free. (Its per-run induction "every non-root read is preceded by
a landing" is run-production bookkeeping — outside this slice, §0.4.)

## §4 D.1 over W(F_q) — the flag VERIFIED by walking

Lemma GR's hypotheses: A a commutative ring, w : A∖0 → ℤ ultrametric with
w(fg) ≥ w(f) + w(g). A^(q) qualifies. Each clause's proof, checked for base
touches:

- (a) Ring: A_{≥γ}·A_{≥δ} ⊆ A_{≥γ+δ} — hypothesis unfolding. NONE.
- (b) Ties: three cases from the definitions of [·]. NONE.
- (c) Domain ⟺ valuation: unfold [f][g] = [fg] or 0. NONE.
- (d) Localization at homogeneous S in a graded domain: generic commutative
  algebra; degree-0 elements form a subring. NONE.
- (e) Rank-1 pieces: T degree-1 unit ⟹ L_γ = T^γ·L₀ free rank 1, R_γ :=
  (·)·T^{−γ} L₀-linear isos, L ≅ L₀[T^{±1}]; R linear on pieces and
  multiplicative when w is a valuation. Monomial algebra in T. NONE.

M14 flagged D.1(e) as "purely graded-algebra … base-agnostic"; the flag is
hereby VERIFIED by the walk (blueprint §2 step 4's demand): zero base
touches — the proofs never mention F, p, q, or any residue object. F need
not even be finite here. **✓**

## §5 D.3(e)(i)/(ii) over W(F_q) — (R2)'s home

### 5.0 Prerequisite displays D.3(a)–(d), walked

(a) anchor congruence: e·(w_prev-difference) = (j′−j)·h with gcd(e, h) = 1
forces e | j′−j — three lines of arithmetic [SKEL]. (b) key residual
R(Φ) = z^s: a LITERAL monomial identity in the (P2)-pinned (V, Y) vectors
[SKEL]. (c) stride rule: p_j(γ) = (j − tγ)/e ∈ ℤ, stepping by 1 per e-step —
monomial computation [SKEL]. (d) width bound: R(B) = Σ_min c_j z^{p_j} by
D.1(b)+(e); positions span < g, so R_anch(B) is a polynomial of degree < g
and ψ ∤ R(B) for B ∈ Ĉ∖0 — degree bookkeeping in F[z^{±1}] over the rebuilt
F [SKEL argument, REBUILT ambient]. **✓**

### 5.1 (e)(i) — the piece maps

Per piece: R_δ : gr^Ĉ_δ → L₀ is ADDITIVE (D.1(e) restricted — §4), INJECTIVE
(R(x) ∈ (ψ) with width < g forces R(x) = 0 forces x = 0 in the piece — §5.0
(d)), with image the ADDITIVE span of the slot images ((S3) slotwise + (S5)
digits — §§2–3). The F_Q-linearity clause carries with F_Q ↦ REBUILT F₁ (per
(RT-4)): for û ∈ C₁ a unit lift of ū ∈ F₁ˣ, multiplication by [û] preserves
each piece (w(ûB) = w(B), (S1)) and R(û·ξ) = ū·R(ξ) by R's multiplicativity
(D.1(e)) with R(û) = ū ((S5) at position 0); on coefficient pieces the
development re-alignment is Lemma DIV(iii) with dig′(û) = ū [REBUILT F′
field]. NO integral F-span beyond this is claimed (the F′-span statement
lives in the (S6b) large-weight regime only — accepted text's own fence,
preserved). **✓**

### 5.2 (e)(ii) leaf coordinates — (RT-1) executed

Iterating developments bottoms every C_k in O_q-coefficients ("leaves"); a
LEAF DIGIT ADDRESS is (leaf, height n), value space now F_q. Fact A taken
digit-level: one division step is y_i = x_i + P_i(x_earlier), P_i a
ℤ-polynomial — COEFFICIENT-level, base-free [SKEL]; composing with (O3)'s
unitriangular carries gives (ii.1) retyped: digit_n(y_i) = digit_n(x_i) + (an
F_p-coefficient polynomial function of the F_q-digits at strictly earlier
addresses in the global well-order — height ascending, then Fact A's
elimination order). Every development map and every move is a digit-level
affine unitriangular bijection FOR F_q-DIGIT BLOCKS. Where a display reads a
leaf at its minimal height, (O4) converts between the Witt component and the
(S5) leading residue by the per-address twist — additive, bijective, so
nothing downstream shifts. **✓**

### 5.3 Height scales, the anchor, and the digit recursion (ii.2)

Scales: digits of B ∈ C_k are indexed by γ ∈ 𝒲_k := w_k(C_k∖0) ⊆ e_k·ℤ; the
top space by the current scale [SKEL declarations]. Stretch conversion
γ* := γ/e_{k+1} (exact: 𝒲_{k+1} ⊆ e_{k+1}·ℤ) [SKEL]. Anchor slot j₀ ≡ t_k·γ*
(mod e_k) — a class forced by γ alone (Bézout t_k exists: gcd(e_k, h_k) = 1);
slot heights γ_i := γ* − (j₀ + i·e_k)·h_k, landing in e_k·ℤ by the anchor
congruence h_k t_k ≡ 1 (mod e_k) [SKEL — the accepted text's own repaired
scale arithmetic, carried verbatim]. ATTAINABLE INDICES I(γ) := {i < g_k :
γ_i ∈ 𝒲_k}, 𝒲_k the ACTUAL weight set (computed by D.9(a), §6): for
i ∉ I(γ) the summand is ABSENT — no zero-filled coordinate is invented (the
D¹¹c discipline, carried) [SKEL given §6]. By D.3(c)–(d),
R_k(B) = Σ_j c_j·z^{p_j(γ*)} over the congruent slots, c_j = d_{γ*−jh_k}(B_j)
by induction ((S5) scalar at a minimizing slot, 0 at congruent
non-minimizing, automatic at unattainable heights); reducing mod ψ_k
[REBUILT F_{k+1}] and applying the D.7(v)+(vii) normalization — u(γ) ∈
F_{k+1}ˣ FORCED by the stage data and γ alone, same pin computation in the
rebuilt field — gives

  **(ii.2)^(q)**  d_γ(B) = u(γ)·Σ_{i∈I(γ)} d_{γ_i}(B_{j₀+i·e_k})·z̄^i,
  values in the REBUILT F_{k+1};  β(B, γ) := ⊔_{i∈I(γ)} β(B_{j₀+i·e_k}, γ_i).

The LAW is verbatim; every object in it (digit values, z̄, u(γ), F_{k+1}) is
rebuilt. **✓**

### 5.4 The alphabet product display and Lemma STAB

𝔸_k(γ) := the value set of d_γ on {B ∈ C_k : w_k(B) ≥ γ} (likewise at the
top). The domain {w ≥ γ} is the PRODUCT of the per-slot domains (K1/(S3) min
formula) [SKEL], so by (ii.2)^(q) and induction:

  **𝔸(γ) = u(γ)·{ Σ_{i∈I(γ)} c_i·z̄^i : c_i ∈ 𝔸_k(γ_i) },
  |𝔸(γ)| = Π_{i∈I(γ)} |𝔸_k(γ_i)|.**

INJECTIVITY MECHANISM, displayed: distinct attainable tuples give distinct
values because (1, z̄, …, z̄^{g_k−1}) is an F_k-BASIS of F_{k+1} =
F_k[z]/(ψ_k) and u(γ) is a unit — this consumes ψ_k IRREDUCIBLE OVER THE
REBUILT F_k (stage data, §0.3; the mutatis-mutandis rule bites exactly here:
no irreducibility is transported from the ℤ_p side), plus 𝔸_k(γ_i) ⊆ F_k.
OFF-ALPHABET GUARD: pinning d_γ(B) = X is solvable iff X ∈ 𝔸(γ) — verbatim
(𝔸 is BY DEFINITION the value set). [SKEL given the rebuilt objects.]

**Lemma STAB (set-level F_q-stability — new display, needed for the block
bookkeeping's retype).** Each 𝔸(γ) is an F_q-stable additive subgroup of its
tower field. *Proof.* Induction. Base: 𝔸₁(e₁v) = F₁ (§5.5), an F_q-space.
Step: for ζ ∈ F_q ⊆ F₁ ⊆ F_k, ζ·u(γ)·Σ c_i z̄^i = u(γ)·Σ (ζc_i)·z̄^i and
ζ·c_i ∈ 𝔸_k(γ_i) by the induction hypothesis. ∎ Hence |𝔸(γ)| = q^{a_q(γ)}
with a_q := dim_{F_q}, and the block-size display retypes to |β(B, γ)| =
Σ_{i∈I(γ)} |β(B_{j₀+ie_k}, γ_i)| = log_q |𝔸(γ)| (one F_q-digit per leaf
address); M14's F_p-normalization is a = f·a_q. REMARK (the (RT-3)
distinction, kept sharp): STAB is a statement about the SET 𝔸(γ) — two lines
of commutative-field algebra on the displayed product form. It asserts NO
equivariance of the digit maps d_γ; that is M14 Lemma 2's theorem (§1.3),
walked nowhere in this pass. **✓**

### 5.5 THE BASE CLAUSE — the onto-ness checkpoint (finding 4's named duty)

  **𝔸₁^(q)(e₁v) = F₁  for every v ≥ 0.**

DISPLAYED PROOF (not "unit lifts"): the realizer family is x-DEPENDENT slot
content p^v·B with B = Σ_{m<d} b_m x^m running over coefficient lifts; the
base digit reading is the θ-basis map (b̄₀, …, b̄_{d−1}) ↦ Σ_m b̄_m θ^m, and
it is ONTO F₁ by Lemma ONTO — the two ingredients being exactly the
blueprint's: reduction W(F_q) ↠ F_q surjective ((O1)) and the θ-power basis
of F₁ over F_q. Containment ⊆ is the (S5) display (digit values lie in F₁).
NEGATIVE HALF, displayed (why the pre-fold draft was wrong): constants —
Teichmüller units included — read into F_q·θ⁰, a PROPER subfield of F₁
whenever d > 1 (§0.2); so no constant realizer family can discharge the base
clause, and the corrected family is forced. NO TEICHMÜLLER SECTION is
consumed anywhere in this section (any coefficientwise lift works — the GD23
V26 discipline, "no proof uses completeness, perfectness, or a Teichmüller
section", preserved on the alphabet side). **✓**

Bottom-up vanishing (the display's last clause): w_k(B) ≥ γ ⟺ d_{γ′}(B) = 0
for every γ′ < γ in the space's scale — base: (O2)'s vanishing clause per
coordinate (the reading at height v(B) is NONZERO); step: expand (ii.2)^(q)
at each γ′* and use (S2) [SKEL]. **✓**

### 5.6 (ii.3)/(ii.4) — carried, with their consumers fenced

(ii.3) disjointness: slot partition + the t_k-invertibility argument +
per-fixed-slot height injectivity — arithmetic [SKEL]; induction bottoms at
distinct heights of the same leaves — distinct F_q-digit addresses. (ii.4):
compose with (ii.1) retyped per (RT-1)/(RT-5): each leaf equation pins ONE
fresh F_q-digit coordinate with unit diagonal, carries polynomial in earlier
digits. The MASS/counting consumers of (ii.3)/(ii.4) (per-digit factors
|𝔸|^{−1}, Theorem C's products) are the counting layer — NOT consumed by
this pass and not re-scoped here (§7). **✓ (carriage only)**

## §6 D.9(a) over W(F_q) — (R3)'s home

### 6.1 The recursion, walked

In the stage-k scale, the weight set of the next coefficient space Ĉ is

  **𝒲̂_k = ⋃_{0≤j<e_k g_k} (𝒲_k + j·h_k)**, hence in the stage-(k+1) scale
  **𝒲^(q)_{k+1} = e_{k+1}·⋃_{0≤j<e_k g_k} (𝒲^(q)_k + j·h_k)** (D.0 stretch).

⊆: for B = Σ B_j Φ^j ∈ Ĉ∖0, w(B) = min_j (w(B_j) + j·h_k) by (S2), each term
in the union [SKEL]. ⊇: SINGLE-SLOT REALIZERS t·Φ^j with t an (S6a) realizer
of weight ω − j·h_k ∈ 𝒲_k (§3.3), deg(tΦ^j) < deg Φ^{e_k g_k} ✓, and
w(tΦ^j) = w(t) + j·h_k by (S1)/(S2) — "minima of achievable values are
achievable" [SKEL given (S6a)]. **✓**

### 6.2 The base clause, and the two-clause STRENGTH SEPARATION (step-6 duty)

  **𝒲₁^(q) = e₁·ℤ≥0.** ⊆: w₁ = e₁·v on C₁. ⊇: B := p^v (v ≥ 0) has
  w₁(B) = e₁v. **✓**

DISPLAYED SEPARATION (blueprint step 6: "the two base clauses are DIFFERENT
in strength"): the WEIGHT clause consumes ONE realizer per weight — p^v·(any
unit constant) suffices, indeed p^v·1; no residue prescription, no onto-ness,
no x-dependence. The ALPHABET clause (§5.5) consumes the FULL image F₁ —
onto-ness of the θ-basis reading over the x-dependent family. Quantifier
display: (weight) ∀v ∃B : w₁(B) = e₁v — witness p^v; (alphabet) ∀v ∀ξ∈F₁
∃B : w₁(B) ≥ e₁v ∧ d_{e₁v}(B) = ξ — witness family Lemma ONTO. Conflating
these two was the pre-fold blueprint's drafting error (finding 4); they are
kept separate here and consumed separately ((R3) needs only the former;
(R2)'s base clause needs the latter). **✓**

### 6.3 D.9(b)/(c) — consumed remarks, classified

(b) cofiniteness (the union contains every lattice value ≥ e_k f_k +
(e_k−1)h_k; base f₁ = 0 exact): arithmetic on gcd(e, h) = 1 and j-ranges
[SKEL] — consumed by D.3(e)'s fullness remark and D.7(v)(2). (c) per-stage
domination h_r > e_r f_r: arithmetic + (I-aug) + D.5's equal-weights number
[SKEL]. (d) recentering realizability: OUTSIDE this slice (D.10's move);
classified §7. **✓**

## §7 Consumption audit (step-7 duty)

Legend: [SKEL] base-independent skeleton, carries as written (the
mutatis-mutandis rule's second half); [REBUILT] residue-theoretic object
reconstructed over F_q in this note (pointer given); [RING] base-ring input
re-supplied as (O1)–(O4); [EXT] slice-external §B2-DEF cite, classified at
its use site.

| walked display | consumes | class |
|---|---|---|
| D.0 | monic division / Φ-developments | [SKEL] |
| D.0 | Gauss v with v(p) = 1 | [RING (O1)] — the absolute-unramifiedness touch |
| D.0 | base field F₁ | [REBUILT §0.2] |
| D.0 (P1)–(P4) | integer vectors, congruences, z-power identities | [SKEL] |
| D.1(a)–(e) | ultrametric w on a commutative ring; graded/localization generalities | [SKEL] — ZERO residue touches, verified §4 |
| D.2 base ((S1)–(S6) base) | §A.1/B1.1 four steps | steps (i) [SKEL]; (ii) F₁ = O_q[x]/(p,φ) field [REBUILT §2.1]; (iii)–(iv) digit readings/unit lifts [RING (O1)–(O2) + Lemma ONTO] |
| D.2 base | gcd/value-group arithmetic (w(p) = e₁, w(φ) = h₁) | [SKEL] + [RING (O1)] |
| D.3(a)–(d) | (P2) pinned vectors; stride arithmetic; F_k[z^{±1}] degree/UFD facts | [SKEL] over [REBUILT] F_k |
| D.3(e)(i) | D.1(e); (S3)+(S5); DIV(iii); unit lifts of F₁ˣ | walked §5.1; F′ field [REBUILT]; lifts [Lemma ONTO] |
| D.3(e)(ii) leaf layer | Fact A (§0), coefficient level | [SKEL] — ring polynomials |
| D.3(e)(ii) leaf layer | digit carries + minimal-height reads | [RING (O3), (O4)] — (O4) is a NEW display, degenerate at q = p |
| D.3(e)(ii.2) | (S2)/(S3)/(S5) per stage; ψ_k reduction; u(γ) pin (D.7(v)+(vii)) | walked §§2–3, §5.3; F_{k+1} [REBUILT]; pin [EXT, classified base-free §3.2/§3.3] |
| D.3(e)(ii) product display | F_k-basis (1, z̄, …, z̄^{g_k−1}) of F_{k+1} | [REBUILT §5.4] — consumes ψ_k irreducible over rebuilt F_k |
| D.3(e)(ii) fullness remark | D.9(b) | [SKEL arithmetic, §6.3] |
| D.9(a) | (S2) + (S6a) realizers + arithmetic | walked §6.1; realizers §3.3 |
| (S6b) | (I-aug) (D.4); D.9(b)/(c) bounds; F′_prev-basis division; base bottoming | (I-aug) walked base-free §3.4; bounds [SKEL]; basis [REBUILT]; bottoming [Lemma ONTO] |
| D.10 / D.9(d) (recentering leg) | Lemma REAL(d), v = v′ frame bookkeeping | [EXT — outside the slice; g = 1 instances of the walked increment theory at the AXIOM level; realizer existence rides (S6b) + (I-aug), both walked; the frame bookkeeping (slot-minimum arithmetic) is [SKEL]-classified but NOT walked at derivation grade here — it belongs to REL.1's wider pass, §0.4] |

**NOT-CONSUMED verification** (M14's claim, checked display-by-display): the
walked texts cite §A/§B1/§0-Fact A and intra-§B2-DEF items ONLY. No walked
display cites C.0, C.0.5, C.1, C.1.5/(ZC), PIN-WELLDEF, Theorem C(a)/(b),
LST, TYP, or DOM. The counting layer is untouched. ✓

**PERIMETER VERDICT (the blueprint's open point (i) — the known-unknown):**
the audit surfaced NO §A/§B1 residue-theoretic consumption beyond the items
re-proved here (B1.1's graded identification, §2.1; the base digit
readings/unit lifts, Lemma ONTO; Fact A's coefficient bookkeeping, [SKEL]).
The pass's perimeter did NOT widen. The likeliest wobble point named in the
blueprint (open point (ii), the (S6) constructive tier's residue-
representative bookkeeping) resolved into exactly two displays: Lemma ONTO
(base) and the F′-basis division (§3.2(3)/§3.3), both [REBUILT] and both
walked.

**Generality notes (GD23 V26 discipline):** no Teichmüller SECTION is
consumed anywhere in this walk (Lemma ONTO takes any lift; τ appears only in
M14 Lemma 2's own on-file proof, outside this pass). COMPLETENESS of O_q is
consumed only through (O3)'s Witt coordinates, i.e. only by the leaf-
coordinate layer (ii.1)/(ii.3)/(ii.4); the (R1)–(R3) core (axioms, (ii.2),
product display, base clauses, D.9(a)) consumes (O1)–(O2) only and is
DVR-generic in the same sense as the GD23/M08 precedents.

## §8 The δ-instance display + the (EQ-1) slice check (step-8 duty, expanded per finding 8)

### 8.1 Base-index convention, displayed (binding: MovesRBase / REL.2)

Fix an algebraic closure F̄_p once; F_m is THE subfield of order p^m and
O_m := W(F_m) ⊂ W(F̄_p). ALL INDICES ABSOLUTE: δ names W(F_{p^δ}) itself,
never a relative extension; nested base changes compose LITERALLY as subrings
— (O_m)_{δ′} = O_{m·δ′} (Lean: `relExt m δ' = O (m·δ')`) — bookkeeping inside
W(F̄_p), never an identification up to isomorphism.

### 8.2 The instances

Set q := p^δ (δ ≥ 1). The walk above specializes to O_δ verbatim; M14's
package (its §2, quoted heads) is re-derived as instances:

| M14 item (verbatim head) | = this note at q = p^δ |
|---|---|
| **(R1)** "§B2-DEF's axioms (S1)–(S6) over the base O_δ with the D.0 scale bookkeeping (w a valuation; w₁(c) = e₁·v(c), v = Gauss, v(p) = 1; stretch w_{k+1} = e_{k+1}·w_k; (L^coeff)₀ = F^(δ); R_γ L₀-linear, R multiplicative — D.1(e))" | §1 (D.0 + both named clauses), §2 ((S1)–(S3)), §3 ((S4)–(S6)), §4 (D.1(e)) |
| **(R2)** "D.3(e)(ii) over O_δ — the digit recursion (ii.2), the alphabet product display with mechanism ((1, z̄, …, z̄^{g_k−1}) an F_k^(δ)-basis of F_{k+1}^(δ)), and the base clause 𝔸₁^(δ)(e₁v) = F₁^(δ)" | §5.3 ((ii.2)^(q)), §5.4 (product + mechanism), §5.5 (base clause) |
| **(R3)** "D.9(a) over O_δ: 𝒲^(δ)_{k+1} = e_{k+1}·⋃_{0≤j<e_k g_k}(𝒲^(δ)_k + j·h_k), base 𝒲₁^(δ) = e₁·ℤ≥0" | §6.1–6.2 |

δ = 1 is the root instance: F_q = F_p, the (O4) twist degenerates to the
identity, Lemma ONTO's reading is the accepted D.2 display, and the walk
reproduces the accepted §B2-DEF text verbatim — ONE theory, all bases.

**Lemma-1 leverage (the blueprint's strategic dividend), displayed:** M14
Lemma 1 (unconditional, on file) applies to the PAIR of instances (q = p,
q = p^δ) at matched numerical data: both instances' weight sets, anchors,
slot heights, and attainable index sets satisfy the SAME integer recursion
((R3), now proved on both sides by §6), so the skeletons coincide at matched
stage tuples. The two-sided comparison consumes NOTHING further from this
pass — in particular NO cross-base dictionary and no per-δ theory: (R4) and
the (a6)/(EQ-1) matching dictionary remain H4-M2's separate unit.

### 8.3 The (EQ-1) slice check (finding 8's second head — the input H4-M6 consumes)

(EQ-1)'s named checkpoint (MOVES §R.1, quoted): "the formal check ('no
species definition consumes q') is a named checkpoint of REL.1's re-scoping
pass, where it is walked, not asserted." Walked here against the same
§B2-DEF text, display by display — for each, the DEFINING fields and the
verdict:

| display | defining fields | consumes q? |
|---|---|---|
| D.0 stage σ | read index (e, h) ∈ ℤ², gcd 1; deg_x Φ (= d·Π e_k g_k, integers); C (determined by deg); U/T/z conventions (integer exponent vectors); F (an OBJECT — its role in the species grammar is the degree data d, (g_k) only) | NO |
| (S1)–(S3) | value group ℤ; slot lattices; development indices | NO |
| (S4) | "F a finite field", L₀ = F[z^{±1}], cyclic exponent group | NO — finiteness is consumed, the SIZE never; the field is a rebuilt object, not a grammar field |
| (S5) | digit positions k(B) = −t·w_prev(B), p_j(γ) = (j − tγ)/e | NO — Bézout/stride integers |
| (S6) | index set 𝒜 (integer lattice, recursive); scalar groups 𝒪_orb, Fˣ | NO for the grammar; the scalar groups are REALIZATION data (they set multiplicities, not letters) |
| D.1 | none (generic) | NO |
| D.3(a)–(d) | anchor congruence, stride, width < g; ψ enters as "monic irreducible, degree g, ψ ≠ z" | NO — g is a degree datum; WHICH ψ's exist over F_k is realization, and irreducibles of every degree exist over every finite field, so no letter (e, h, g) is q-forbidden |
| D.3(e) | scales 𝒲_k-lattices; γ*; j₀ = t_k γ* mod e_k; γ_i; I(γ) ⊆ {0..g_k−1}; u(γ) (a forced UNIT — realization datum, parameterizes nothing in the grammar); alphabets 𝔸 (realization: value sets, size q-dependent) | NO for every defining field: by (R3) + M14 Lemma 1 the whole skeleton (𝒲, j₀, γ_i, I(γ)) is determined by the integer stage tuples alone |
| D.9(a) | the integer recursion + base e₁·ℤ≥0 | NO |

VERDICT: **within the walked §B2-DEF slice, no species definition consumes
q.** What changes under re-basing is exactly the REALIZATION side — digit
value sets 𝔸 (cardinality q^{a_q}, Lemma STAB), scalar groups, u(γ)'s value
— never a defining field. SCOPE FENCE, displayed: this check covers the T-1
stage/ledger grammar (§B2-DEF's slice); species fields living OUTSIDE the
walked text — the multiplicity μ (D.8's landing/read selection), side
selection, polygon conventions of the catalogue layer — are not walked here,
and H4-M6's §3.3 plan item (2) consumes exactly THIS slice check plus its own
type-catalogue display for the remainder (blueprint's consumes-line, synced).

## VERDICT

**PROVED at the displayed perimeter (§0.4).** (R1), (R2), (R3) hold over
A^(q) = W(F_q)[x] for every finite F_q, for every tower presented by the
§B2-DEF recipe with rebuilt residue data and (I-aug) reads; base ℤ_p and
every O_δ are instances of the one theory (§8.2). The mutatis-mutandis rule
was obeyed throughout: laws verbatim, objects rebuilt, and the audit (§7)
certifies the skeleton/residue split display-by-display with no perimeter
widening. NOT discharged here (honest fence): (R4) + the matching dictionary
(H4-M2); the run-production layer D.8/D.10 (REL.1's wider walk; only D.4's
(I-aug) argument itself is walked, §3.4); the counting layer (not consumed).
Status labels: base-ring inputs (O1)–(O4) and the Teichmüller/Witt facts —
(a) known (Serre, Corps Locaux II §4–6); Lidl–Niederreiter Thm 3.46 — (a)
known, consumed ONLY by the N-gate's domain grounding, never by the walk; the
re-scoped displays over W(F_q), Lemma ONTO, Lemma STAB, and the (O4) twist
display — (c) claimed new in this packaging (project constructions; the
literature's OM/Montes theory has the full-residue-field case only, per M14's
verdict block). Consumers may now read: M14's Lemma 2 hypotheses are supplied
(§1.3); M14's Theorem inputs (R1)–(R3) are supplied at both instances; the
(EQ-1) slice input for H4-M6 is §8.3's table.

## §N NUMERIC-GATE RECORD — N-T4 (run BEFORE pass 1, per the §M gate)

Spec (blueprint §N / M14 Test 4): two-stage tower p = 2, stage 1 (e₁, h₁) =
(2, 1), ψ₁ = z² + z + 1 (g₁ = 2, d = 1); stage 2 (e₂, h₂) = (2, 3), ψ₂ an
irreducible cubic over F₄ (g₂ = 3); δ = 5 (gcd(6, 5) = 1, in-domain);
symbolic alphabet recursion both sides, all heights γ ≤ 100; REFUTES
(R2)/(R3) drafting if any a^(δ)(γ) ≠ 5·a(γ).

SEALED PREDICTIONS (in-script, before the run): P1 a^(δ) = 5·a everywhere;
P2 stage-2 profile 1, 1, then 2 from γ = 4; P3 top profile {0:1, 2:1, 3:1,
4:2, 5:1, 6:3, 7:2, 8:3, 9:3, 10:4, 11:3, 12:5, 13:4, 14:5, 15:5, 16:6,
17:5, 18:6, …} with full value 6 for all γ ≥ 18 — heights 14/15/17 exercise
a NESTED proper sub-alphabet (all three slots attainable, one nested-shallow
a(2, 2) = 1), the configuration T1 could not reach (M14's own caveat); P4
irreducibility ground checks per Lidl–Niederreiter 3.46.

RESULT: **P1–P4 ALL PASS** (stage 1, stage 2, and top space; every height
γ ≤ 100; both irreducibility legs at both conjugate embeddings).

**TEST-SPEC DEFECT, found and recorded (not a theory refutation):** M14 T4's
EXAMPLE cubic "z³ + z + w" is REDUCIBLE over F₄ — z = w² is a root
(w⁶ + w² + w = 1 + (w+1) + w = 0); the spec's own instruction "verify
irreducible" caught it. Substituted ψ₂ := z³ + w, VERIFIED irreducible over
F₄ (w is a non-cube: cubes in F₄ˣ = {1}) and over F₄·F₃₂ = F_{2^10} (no root
at either conjugate embedding of F₄; consistent with gcd(3, 5) = 1). The
recursion legs are unaffected (only g₂ = 3 enters them). Owed ledger note:
M14's T4 spec text should be repaired at its next touch (H4-M7 sync item).

Script (verbatim, reproducible; run 2026-08-06, python3, no dependencies):

```python
#!/usr/bin/env python3
# N-T4 -- M14 Test 4 (HDISCHARGE_H4 gate; run BEFORE H4-M1 pass 1).
E, H, G = [2, 2], [1, 3], [2, 3]
T = [pow(h, -1, e) for e, h in zip(E, H)]  # Bezout t_k: h_k t_k = 1 mod e_k
GMAX, MARGIN = 100, 40
W1 = set(range(0, (GMAX + MARGIN) * 2, E[0]))              # W_1 = e1*Z>=0
U = set()
for j in range(E[0] * G[0]):
    U |= {x + j * H[0] for x in W1}
W2 = {E[1] * x for x in U if E[1] * x <= GMAX + MARGIN}    # D.9(a) step
What2 = set()
for j in range(E[1] * G[1]):
    What2 |= {x + j * H[1] for x in W2}                    # top-space heights

def a_stage2(gamma, dbase):
    gs = gamma // E[1]                    # gamma* (D.0 stretch)
    j0 = (T[0] * gs) % E[0]               # anchor slot
    return sum(dbase for i in range(G[0])
               if gs - (j0 + i * E[0]) * H[0] in W1)

def a_top(gamma, a2):
    j0 = (T[1] * gamma) % E[1]
    return sum(a2[g] for i in range(G[1])
               for g in [gamma - (j0 + i * E[1]) * H[1]] if g in W2)

a2b = {g: a_stage2(g, 1) for g in sorted(W2)}
a2d = {g: a_stage2(g, 5) for g in sorted(W2)}
a3b = {g: a_top(g, a2b) for g in sorted(What2) if g <= GMAX}
a3d = {g: a_top(g, a2d) for g in sorted(What2) if g <= GMAX}
assert all(a2d[g] == 5 * a2b[g] for g in a2b if g <= GMAX)         # P1 stage 2
assert all(a3d[g] == 5 * a3b[g] for g in a3b)                      # P1 top
assert all(a2b[g] == (1 if g in (0, 2) else 2) for g in a2b if g <= GMAX)  # P2
P3ref = {0:1, 2:1, 3:1, 4:2, 5:1, 6:3, 7:2, 8:3, 9:3, 10:4, 11:3, 12:5,
         13:4, 14:5, 15:5, 16:6, 17:5}
assert all(a3b[g] == v for g, v in P3ref.items())                  # P3
assert all(a3b[g] == 6 for g in a3b if g >= 18)                    # P3 full
def gmul(a, b, f, k):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> k & 1: a ^= f
    return r
def gpow(a, n, f, k):
    r = 1
    while n:
        if n & 1: r = gmul(r, a, f, k)
        a = gmul(a, a, f, k); n >>= 1
    return r
F4, F32, F1024 = 0b111, 0b100101, 0b10000001001
x = 0b10
assert gpow(x, 2**10, F1024, 10) == x            # F_1024 modulus certified
assert all(gpow(x, 2**d, F1024, 10) != x for d in (1, 2, 5))
psi1 = lambda z, f, k: gmul(z, z, f, k) ^ z ^ 1
assert all(psi1(z, F4, 2) for z in (0, 1))                         # P4
assert all(psi1(z, F32, 5) for z in range(32))                     # P4
w4 = 0b10; w4sq = gmul(w4, w4, F4, 2)
spec = lambda z, w, f, k: gmul(gmul(z, z, f, k), z, f, k) ^ z ^ w
assert spec(w4sq, w4, F4, 2) == 0        # SPEC DEFECT: z=w^2 root of z^3+z+w
psi2 = lambda z, w, f, k: gmul(gmul(z, z, f, k), z, f, k) ^ w
assert all(psi2(z, w4, F4, 2) for z in range(4))                   # P4 (subst)
Wemb = [z for z in range(1024) if gmul(z, z, F1024, 10) ^ z ^ 1 == 0]
assert len(Wemb) == 2
assert all(all(psi2(z, W, F1024, 10) for z in range(1024)) for W in Wemb)
print("N-T4: ALL PASS")
```

## HOSTILE-PASS LEDGER (gate: ×2, fresh contexts, one Codex)

- Pass 1 (Codex, fresh context): see below this line after the run.
- Pass 2 (fresh context): see below after pass 1's repairs, if any.
