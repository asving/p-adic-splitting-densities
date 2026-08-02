# H4M1-rpack — attempt (Fable prover H4-M1, 2026-08-06; rev 2 = pass-1 fold, 2026-08-08)

*(Rev 2 status: ALL TEN pass-1 findings (2 CRITICAL + 8 GAP,
`H4M1_pass1_2026-08-08.md`) accepted and folded in place — the headline
CRITICAL by WALKING D.10's recentered stage package (new §3.5), not by
scoping it out. Authoritative gate record: the HOSTILE-PASS LEDGER and
REVISION RECORD at the end. Clean counter 0/2.)*

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
(I-aug) reads satisfies (S1)–(S6) at every stage — INCLUDING recentered
stages, whose stage package (D.10's TRANS-RS) is walked at §3.5 (rev 2) —
with the D.0 scale bookkeeping (§§1–4), the
D.3(e) digit/alphabet displays (§5), and the D.9(a) weight-set recursion with
its base clause and the (b)/(c) bounds (§6). Base ℤ_p is the q = p instance and base O_δ = W(F_{p^δ})
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
(unit H4-M2), and nothing here re-scopes the run-production layer — D.8's
landing and D.10's RS-landing/lift-independence legs (REL.1's wider walk);
D.10's STAGE package is inside, walked (§3.5). §0.4 and §7 display the
exact fence.

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
- **Recenterings** (at an e_read = 1 stage): a center c̃ ∈ Fˣ — F the
  REBUILT current field — and Φ′ := Φ̂ − t with v(t) = v(Φ̂), dig(t) = c̃.
  The recentered STAGE PACKAGE — realizer existence, v = v′, K1 for the
  recentered key, coefficient-localization preservation, and (S1)–(S6) in
  the primed frame (D.10's TRANS-RS) — is WALKED at §3.5 (rev 2; pass-1
  finding 1): D.10's "every recentering is the g = 1 case of the increment
  theory" is INSTANTIATED there at derivation grade, not cited.

### 0.4 Perimeter (displayed fence)

PROVED here: for every such tower, (S1)–(S6) hold at every stage — increment
stages (§§1–4) AND recentered stages (§3.5, rev 2) — with the D.0
bookkeeping ((R1)), the D.3(e)(i)/(ii) displays hold ((R2)), and D.9(a) holds
with its base clause ((R3)), with the D.9(b)/(c) bounds walked (§6.3). NOT
claimed here: (R4)/the (a6)/(EQ-1) matching
dictionary (H4-M2's unit); that the re-based CLASSIFIER RUN produces recipe
towers with (I-aug) reads — that is the run-production layer,
REL.1's wider walk (D.4's three-bullet argument is walked at §3.4 and
D.10's stage package at §3.5, so the residue of that fence is D.8's landing
bookkeeping and D.10's RS-landing/lift-independence legs only — consumed by
NOTHING in (S1)–(S6)); the
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
  (D.9(b) cofiniteness — WALKED §6.3) + gcd(e′, h′) = 1 [SKEL].
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
- (v) (L′^coeff)₀ = F′ — WALKED (rev 2; pass-1 finding 5). D := R(·) mod ψ
  on each coefficient piece gr^Ĉ_δ: ADDITIVE per piece (D.1(e) restriction,
  §4), MULTIPLICATIVE across pieces (DIV(iii), §2.3), INJECTIVE per piece
  (R(x) ∈ (ψ) with width < g (§5.0(d)) forces R(x) = 0 forces x = 0 in the
  piece); D extends multiplicatively to the degree-0 part of the coefficient
  sub-localization 𝒞′^loc. IMAGE = ALL OF F′, the large-weight argument
  walked in its three steps:
  (1) UNIT-MONOMIAL WEIGHTS: w′(pⁿ) = n·w′(p) ((S1)) with w′(p) = e′·w(p)
      > 0 [(O1): v(p) = 1, the base display, stretched deterministically
      through the D.0 chain], so powers of in_{w′}(p) supply
      ⟨U′⟩-monomials of unboundedly many coefficient-side weights δ.
  (2) g CONSECUTIVE POSITIONS IN ONE PIECE: fix such a δ with
      δ ≥ e′·(the §6.3(b) cofiniteness bound + e·g·h). The weight-δ
      coefficient piece decomposes over Φ-slots ((S3)); at the slots
      j = r·e (0 ≤ r < g, all < eg) the required stage-scale coefficient
      weights δ/e′ − r·e·h are each ≥ the §6.3(b) bound, hence IN the
      actual weight set 𝒲 (cofiniteness, WALKED §6.3), and their
      z-positions are CONSECUTIVE integers by the stride rule (§5.0(c):
      j stepping by e steps the position by 1).
  (3) F-SCALARS VIA (S6b): enlarge δ so that each slot realizer's
      PARENT-scale coefficient weight δ/(e′·e) − r·h exceeds the current
      stage's clean threshold w_prev(Φ) — possible since the expression
      grows with δ at each fixed r < g. Then (S6b) AT THE CURRENT STAGE
      (§3.3, walked — scalar group the REBUILT current field F) supplies,
      for each slot j = r·e and each prescribed c_r ∈ Fˣ (slot absent at
      c_r = 0), an INTEGRAL realizer at that slot and weight; their SUM is
      one element of the weight-δ piece (equal total weights, distinct
      slots — (S3)-independence), with D-image Σ_r c_r·z̄^{pos+r} =
      z̄^{pos}·P(z̄), P := Σ_r c_r z^r ARBITRARY of degree < g. Since z̄ is
      a unit of F′ and (1, z̄, …, z̄^{g−1}) is an F-BASIS of F′ = F[z]/(ψ)
      [REBUILT: ψ irreducible over the rebuilt F, §0.3],
      z̄^{pos}·{P(z̄) : deg P < g} = F′.
  INJECTIVITY ON DEGREE-0 FRACTIONS: a degree-0 element of 𝒞′^loc is a
  ratio x/M with M a ⟨U′⟩-monomial of x's weight and D(M) ∈ F′ˣ ((iv));
  D(x/M) = 0 forces D(x) = 0 forces x = 0 per piece — so D is injective on
  degree-0 fractions and (L′^coeff)₀ ≅ F′. [The naive "z̄ is a ratio of
  unit-monomials" shortcut generates only the subfield F[z̄^s] and is NOT
  used — the source's own fence, carried.] **✓**
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

**(S6a)** (exactness + basic realizers) — WALKED (rev 2; pass-1 finding 3:
the rev-1 text closed this "exactly as in the accepted text", citation-style).
Base: 𝒜₁ = {(e₁v, −t₁v) : v ≥ 0}, read off the (S5) base display on C₁∖0
(weights e₁v exhaust 𝒲₁, §6.2; positions forced −t₁v). Step, D.7(viii)'s
displayed formula DERIVED in the rebuilt frame:

  **𝒜′ = { (e′·(γ + j·h), −t′·(γ + j·h)) : (γ, κ) ∈ 𝒜, 0 ≤ j < e·g }.**

⊆ (every realized index is of this form): for B ∈ Ĉ∖0, w′(B) = e′·w(B)
(slot-0 stretch, D.0) and w(B) = min_j (w(B_j) + j·h) ((S2)); a minimizing
Φ-slot j gives w(B) = γ + j·h with γ := w(B_j) a first coordinate of 𝒜 and
0 ≤ j < e·g. The new POSITION is not free data: by (S5′) (§3.2(vii)-classified,
mechanism = the D.7(vi) Y′-exponent count: dig′ of a coefficient class of
w′-weight W′ sits on the F′-line of Y′-exponent −t′·W′/e′), the position is
−t′·(γ + j·h) — a function of the new WEIGHT alone. WHY THE OLD POSITION κ
IS CONSUMED: at every stage the position is itself weight-forced (base:
κ = −t₁·γ/e₁ on 𝒜₁; step: the display above), so κ carried no independent
data — it forced the OLD digit's monomial class and does not propagate; the
new pair is recomputed from the new weight. WHY EVERY NEW POSITION IS
FORCED: the same (S5′) line count applies to EVERY Ĉ-element — there is no
element realizing the weight e′(γ + jh) at any other position.
⊇ (every index of this form is realized): the SINGLE-SLOT element
t_{γ,j} := t_γ·Φ^j, t_γ the stage-(S6a) realizer of (γ, κ) with digit scalar
c ∈ 𝒪_orb: deg t_{γ,j} < deg Φ·(1 + j) ≤ e·g·deg Φ so t_{γ,j} ∈ Ĉ ✓;
w(t_{γ,j}) = γ + j·h ((S1) + w(Φ) = h) ✓; and dig′(t_{γ,j}) =
(c·z^{κ}·z^{s·j}) mod ψ = c·z̄^{κ+sj} — c times a FORCED monomial class,
nonzero in F′ˣ (z̄ a unit, c ≠ 0) [(S5) + D.3(b), §5.0]. The CONSTANT ORBIT
GROUP re-bases to 𝒪_orb := (F₁^(q))ˣ — the units of the REBUILT base tower
field F₁ = F_q[x]/(φ̄). (Collision note: §B2-DEF writes this group
"O := F_Qˣ"; O_q here is the base RING — the two O's are unrelated and this
note never uses the bare letter for the group.) CLOSURE, walked: the step
realizer's scalar is LITERALLY the stage realizer's scalar c (the monomial
class z̄^{κ+sj} carries no new scalar), so the scalar group propagated by
iterated single-slot realizers is the SAME 𝒪_orb at every stage — the
induction closes on the constant group. **✓**

**(S6b)** (full scalars above the key weight — the offset-P-lift) — the
CONSTRUCTION WALKED (rev 2; pass-1 finding 4: rev 1 named the construction's
pieces without building it). CLAIM (stage-uniform, all objects rebuilt): at
the stage with field F_cur = F_prev[z]/(ψ_prev), g_prev := deg ψ_prev,
coefficient space C (Φ_prev-developments, slots 0 ≤ j < e_prev·g_prev),
every digit scalar τ ∈ F_curˣ is realizable at every parent-scale
coefficient weight W > w_prev(Φ_cur), ANY residue class. CONSTRUCTION:

  t := Σ_{0 ≤ k < g_prev, P_k ≠ 0} t_k·Φ_prev^{j₀ + e_prev·k},

with each ingredient forced, in order:
- ANCHOR: minimizing slots at weight W satisfy j ≡ t_prev·W (mod e_prev)
  (anchor congruence §5.0(a)); j₀ := the representative in [0, e_prev) —
  exists for EVERY W (that is "any residue class"). The common offset
  m := p_{j₀}(W) = (j₀ − t_prev·W)/e_prev ∈ ℤ is forced by W alone (stride
  rule §5.0(c)); the slots j₀ + e_prev·k, 0 ≤ k < g_prev, sit at the
  CONSECUTIVE positions m, m+1, …, m+g_prev−1, and j₀ + e_prev·k ≤
  (e_prev − 1) + e_prev(g_prev − 1) < e_prev·g_prev, so t ∈ C ✓.
- P: since z̄ ∈ F_curˣ, P is the UNIQUE polynomial of deg < g_prev with
  P(z̄) = z̄^{−m}·τ — existence/uniqueness by the F_prev-basis
  (1, z̄, …, z̄^{g_prev−1}) of F_cur [REBUILT: ψ_prev irreducible over the
  rebuilt F_prev]. NO ZERO-SCALAR TERMS: slots with P_k = 0 are ABSENT — no
  realizer of scalar 0 exists or is needed.
- SLOT REALIZERS: t_k ∈ C_prev realizes digit scalar P_k ∈ F_prevˣ at
  stage-scale weight W − (j₀ + e_prev·k)·h_prev (≡ 0 mod e_prev by the
  anchor congruence, h_prev·t_prev ≡ 1) — supplied by (S6b) ONE STAGE DOWN,
  whose scalar group is exactly F_prev: the two-line MUTUAL RECURSION.
  THRESHOLD CHECK, walked: each t_k's parent-parent-scale weight is
  (W − (j₀ + e_prev·k)·h_prev)/e_prev ≥ (W − (e_prev·g_prev − 1)·h_prev)/e_prev
  > (e_prev·h_prev·g_prev − (e_prev·g_prev − 1)·h_prev)/e_prev = h_prev/e_prev
  > w_prevprev(Φ_prev), using W > w_prev(Φ_cur) = e_prev·h_prev·g_prev (the
  D.5 equal-weights number, §2.2) and (I-aug) AT THE PREVIOUS READ (§3.4) —
  exactly the (S6b) hypothesis one stage down.
- EQUAL WEIGHTS + THE RESIDUAL, verified: each present summand has weight
  (W − (j₀+e_prev k)·h_prev) + (j₀+e_prev k)·h_prev = W, distinct slots, so
  w(t) = W by (S2)/(S3); and R(t) = Σ_k P_k·z^{m+k} — the slot residuals
  land at the DISTINCT consecutive positions m+k (stride rule), so D.1(b)
  sums them without cancellation: R(t) = z^m·P(z), the forced residual
  window, and dig(t) = R(t) mod ψ_prev = z̄^m·P(z̄) = τ ✓.
- BOTTOM: the recursion bottoms at the base — any prescribed ū ∈ F₁ˣ at any
  base height e₁v is realized by p^v·û, û a C₁-lift (Lemma ONTO; x-dependent
  at d > 1 — the finding-4 correction lands at the recursion's bottom too),
  NO threshold. **✓**

Consumers' range checks ((D.5)'s realizers; the recentering lift, now walked
§3.5(b)) are (I-aug) verbatim [SKEL].

### 3.4 D.4 (I-aug), all three bullets WALKED (rev 2; pass-1 finding 7)

(I-aug): at every read, the side slope strictly exceeds the current key's
weight, λ > w(Φ).

- ROOT: on the initial cluster (non-lead coefficients ≡ 0 mod p, key x,
  w(x) = 0) the lead coefficient is a v-unit and every other has v ≥ 1
  [(O1)-level Gauss-valuation facts over O_q, verbatim]; the polygon
  descends to (deg f, 0) with integer drops, so every side's slope is
  ≥ 1/deg f > 0 = w(x) — positivity is all (I-aug) asserts here.
- AFTER AN INCREMENT, entirely in the parent valuation w (no w′ exists
  yet). The landing box — w(B_j) + j·w(Φ̂) > w(f) = w(B_μ) + μ·w(Φ̂) for
  j < μ, which is (S2) bookkeeping on f's Φ̂-development at the landing
  datum — yields the CHORD INEQUALITY, derived: for j < μ the chord from
  (j, w(B_j)) to the pinned vertex (μ, w(B_μ)) has descent slope
  (w(B_j) − w(B_μ))/(μ − j), and the box gives w(B_j) − w(B_μ) >
  (μ − j)·w(Φ̂), so every such chord's slope > w(Φ̂). SIDE ENDING AT THE
  VERTEX, identified: the lower-hull side of the child polygon over [0, μ]
  that ENDS at (μ, w(B_μ)) has its left endpoint at a polygon point
  (j, w(B_j)) with j < μ, so its slope IS one of those chord slopes —
  > w(Φ̂). MONOTONICITY of lower-hull slopes, displayed: adjacent sides of
  a lower hull have strictly increasing descent slopes leftward (else the
  shared vertex would lie on or above the segment joining the outer
  endpoints, contradicting hull minimality), so every side over the
  continuing window is steeper still. The next read's side is one of these:
  h′/e′ > w(Φ̂). Pure polygon/valuation arithmetic — base-free; the only
  input is (S2) at the walked stage.
- AFTER A RECENTERING: the SAME two displays verbatim, in the primed frame,
  which is one single scale by v = v′ — WALKED at §3.5(e) (the finding-7
  dependency on the frame identification is discharged there; no
  circularity: §3.5's own (S6b) range check consumes (I-aug) at the read
  that PRODUCED Φ̂, available by the history induction before the
  recentering move is made).

(The per-run induction "every non-root read is immediately preceded by a
landing" is run-production bookkeeping — outside this slice, §0.4.)

### 3.5 The recentered stage package (D.10's TRANS-RS) over W(F_q) — WALKED (rev 2; pass-1 finding 1, the headline CRITICAL)

*(Rev 1 claimed "(S1)–(S6) hold at every stage" over a perimeter INCLUDING
recentered stages while classifying D.10's frame content "[SKEL], not
walked". The verifier is right that D.10 does substantially more than
instantiate g = 1: it proves v = v′, K1 for the recentered key, and
preservation of the coefficient localization. Each is walked here over the
rebuilt objects — fold option (a), the walk, not the scope-out. The
RS-landing, lift-independence, and anchored-display legs of D.10 are
run-production/ledger content, consumed by NOTHING in (S1)–(S6), and stay
outside the fence (§0.4).)*

SETTING. An e_read = 1 stage σ = (v, Φ̂, C, U, T, F, z) over W(F_q) with all
six axioms held (the walk's induction hypothesis, §§1–3), produced by a read
of index (1, h) — so v(Φ̂) = h — satisfying (I-aug): h > w_prev(Φ̂). By (P2)
at e = 1, T is coefficient-pure (Bézout exponent t = 0): every coefficient
digit has z-position 0 ((S5): k(B) = −t·w_prev(B) = 0) and R(Φ̂) = z (D.3(b)
with s = 1). Recentering datum: a center c̃ ∈ Fˣ — F the REBUILT current
field. (Below, t names the recentering realizer, as in the source; the
Bézout exponent is 0 at this stage and never reappears.)

**(a) Species lemma [SKEL arithmetic].** A same-degree recentering
Φ′ := Φ̂ − t needs v(t) = the side value at slot 1, which must lie in the
coefficient value group; at an e_read ≥ 2 side the slot-1 value is NOT in
that group (gcd(e, h) = 1), so recenterings exist exactly at e_read = 1
sides. Integer arithmetic — no residue object enters, hence no q.

**(b) Realizer existence [REBUILT scalars].** Take t ∈ C with v(t) = v(Φ̂)
and dig(t) = c̃: this is (S6b) — WALKED at §3.3, scalar group the rebuilt
Fˣ — at the parent-scale weight W := v(Φ̂) (the e = 1 stretch is trivial;
position 0 automatic by (P2)); the threshold check W > w_prev(Φ̂) is
LITERALLY (I-aug) at this read (§3.4). [The source's own rev note applies
verbatim: Lemma REAL's Frobenius machinery is NOT needed — (S6b) + (I-aug)
supply the realizer directly; D.9 stays in the DAG only for D.7(v), §3.2.]

**(c) Equal weight and the primed key residual.** Both Φ̂ and t have weight
v(Φ̂), and the tie is NON-DEGENERATE: R(Φ̂) − R(t) = z − c̃ ≠ 0 in
F[z^{±1}] (a Laurent monomial minus a nonzero constant, c̃ ≠ 0). By D.1(b)
(§4): v(Φ′) = v(Φ̂ − t) = v(Φ̂) and **R(Φ′) = z − c̃ EXACTLY** — no unit
normalization (m̂′ = 0), matching D.10's unit note.

**(d) K1(Φ′/v) — §2.2 INSTANTIATED at g = 1, not cited.** Set ψ′ := z − c̃
∈ F[z]: monic of degree 1, hence irreducible over ANY field — the one
residue touch of this section is field-generic over the REBUILT F — and
ψ′ ≠ z since c̃ ≠ 0. Φ′ IS the D.5 standard lift for ψ′ at (e, g) = (1, 1):
Φ̂^{e·g} + t₀·Φ̂⁰ with t₀ := −t realizing the digit scalar ψ′₀ = −c̃ (R is
additive on the piece, D.1(e): dig(−t) = −c̃ ∈ Fˣ) at weight
e·h·(g − 0) = v(Φ̂) ✓ = (b)'s realizer up to sign. §2.2's K1 proof re-runs
verbatim: (≥) is (S1) + ultrametric; (≤): if the slot minimum were not
attained, applying R gives Σ_{min j} R(B_j)·(z − c̃)^j = 0 in F[z^{±1}]
(m̂′ = 0 by (c)); each term has ψ′-adic order EXACTLY j, because ψ′ ∤ R(B_j)
— at g = 1 the width bound (§5.0(d)) says R(B_j) is a nonzero MONOMIAL
c·z^k ((S5) directly), and (z − c̃) divides no monomial (evaluate at c̃:
c·c̃^k ≠ 0 in the field F); ψ′ stays prime in F[z^{±1}] (ψ′ ≠ z); a finite
sum of nonzero terms of pairwise distinct ψ′-orders is nonzero.
Contradiction. **K1(Φ′/v) holds.** ∎

**(e) v = v′ and the frame identification.** deg Φ′ = deg Φ̂, so the
coefficient space is UNCHANGED: C′ = C. For coefficients the two side
valuations agree tautologically (no key slots involved). For a general
Φ′-development, (d) gives v(Σ_j B_j Φ′^j) = min_j (v(B_j) + j·v(Φ′)) — and
that slot minimum IS the definition of the recentered stage's weight v′.
Hence **v = v′ as valuations on A**, the filtrations coincide, and
gr_{v′}(A) = gr_v(A) — one graded ring, one scale (the typing D.4's third
bullet consumes, §3.4).

**(f) The substitution identity [graded algebra — zero residue touches,
§4].** In gr_v(A): Y_Φ̂ = [Φ̂] = [Φ′] + [t], all three homogeneous of degree
v(Φ̂) ((c)'s non-degenerate tie). Set z′ := R_v(Φ′) = z − c̃. In the common
localization L_both := gr_v(A)[⟨U ∪ {Y_Φ̂, Y_{Φ′}}⟩^{−1}] (a localization of
a graded domain at homogeneous elements, D.1(d)), both z and z′ are
degree-0 units, and R′(f) := [f]·T^{−v(f)} = R(f) AS ELEMENTS of L_both for
every f — same T (coefficient-pure, untouched by the move), same v ((e)).
What changes is only the display variable: R′(f) as a z′-Laurent polynomial
= R(f)(z′ + c̃).

**(g) TRANS-RS — (S1)–(S6) in the primed frame, item by item.**
- (S1): v′ = v is the SAME valuation ((e)), value group ℤ unchanged. ✓
- (S2): K1(Φ′/v) — (d). ✓
- (S3): slot decomposition at Φ′ from (S2) + additivity of monic division
  [SKEL]; Y′ := [Φ′] transcendental over the coefficient classes,
  degreewise. ✓
- (S4): the coefficient-side representatives are UNCHANGED (p and the
  previous keys including Φ — all of degree < deg Φ′ = deg Φ̂, so still in
  C); the coefficient sub-localization is LITERALLY the same ring, so
  **(L′^coeff)₀ = (L^coeff)₀ = F** — the coefficient-localization
  preservation the pass-1 finding named, with NO residue growth (the g = 1
  degeneracy: F[z]/(z − c̃) ≅ F by evaluation z ↦ c̃ — the "new field" is
  the old one). L′₀ = F[z′^{±1}]: D.7(vi)'s exponent-group
  argument at Φ′ in (f)'s common localization — a degree-0 element with
  Y′-exponent k needs k·v(Φ̂) ∈ the coefficient value group, and two
  degree-0 monomials of equal Y′-exponent differ by a degree-0 coefficient
  unit ∈ Fˣ (the F-line statement, unchanged coefficient side) — so the
  exponent group is infinite cyclic on z′ ((P1) pins z′; the (P2) vector
  transports with T unchanged). ✓
- (S5): coefficient digits LITERALLY unchanged — same C, same v, same T:
  dig′(B) = dig(B) for every B ∈ C∖0, all at position 0 (e′ = 1). ✓
- (S6): same index set 𝒜 (a value-set computation on the unchanged (C, v))
  and the SAME realizers, (S6a) and (S6b) verbatim with the same scalar
  groups (𝒪_orb and Fˣ — same F). ✓
The recentered stage σ′ = (v, Φ′, C, U, T, F, z′) satisfies (S1)–(S6): the
next read in the primed frame has a full stage. ∎

CONSUMPTION AUDIT (local): (S6b) + (I-aug) (§§3.3–3.4, both walked) for
(b); §2.2's K1 walk instantiated at g = 1 for (d) — residue touch: ψ′ =
z − c̃ irreducible over the rebuilt F, a degree-1 field-generic fact; D.1
(§4, zero residue touches) for (c)/(f); (P2) coefficient-purity [SKEL].
NOT consumed: RS-landing, lift independence, the anchored display
(a′ = μ, R′_anch), the well-typedness lemma a ≥ 0, D.8, D.9(d) — all
run-production/ledger legs, outside (§0.4).

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
top space C_{K+1} (no read K+1 exists) by the CURRENT scale, γ ∈ 𝒲̂_K :=
w_K(C_{K+1}∖0) [SKEL declarations]. Stretch conversion, BOTH cases displayed
(rev 2; pass-1 finding 2 — rev 1 dropped the top case, leaving its displayed
recursion undefined there, a silent weakening of D.3(e)(ii)):

  γ* := γ/e_{k+1}  for k+1 ≤ K (the D.0 stretch w_{k+1} = e_{k+1}·w_k on
  coefficients; exact since 𝒲_{k+1} ⊆ e_{k+1}·ℤ);
  γ* := γ  at the TOP SPACE (k = K): the top space carries the current
  scale itself — no read K+1 exists, hence no e_{K+1} and NO stretch.

Every use of γ* below (anchor, slot heights, u(γ), the product display of
§5.4 "likewise at the top") reads through this two-case display. Anchor slot
j₀ ≡ t_k·γ*
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
rebuilt field; AT THE TOP SPACE the pinned datum is dig′ itself: the same
pin with u(γ) = z̄^{p_{j₀}(γ*)}, γ* = γ (the k = K case of the display
above) — gives

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
tower field. *Proof.* Induction, BOTH clauses walked (rev 2; pass-1 finding 9: the rev-1
proof displayed only the scalar computation while claiming a stable additive
SUBGROUP). Base: 𝔸₁(e₁v) = F₁ (§5.5), an F_q-space. Step, all via the
displayed product form 𝔸(γ) = u(γ)·{Σ_{i∈I(γ)} c_i·z̄^i : c_i ∈ 𝔸_k(γ_i)}:
- ADDITIVE CLOSURE: for two members u(γ)·Σ c_i z̄^i and u(γ)·Σ c′_i z̄^i,
  the sum is u(γ)·Σ (c_i + c′_i)·z̄^i with c_i + c′_i ∈ 𝔸_k(γ_i) by the
  induction hypothesis (each 𝔸_k(γ_i) an additive subgroup) — again of the
  product form, hence in 𝔸(γ). 0 ∈ 𝔸(γ): all c_i = 0, 0 ∈ 𝔸_k(γ_i) by
  induction.
- ADDITIVE INVERSES: −1 ∈ F_p ⊆ F_q, so the inverse is the ζ = −1 instance
  of the scalar clause below.
- SCALAR STABILITY: for ζ ∈ F_q ⊆ F₁ ⊆ F_k, ζ·u(γ)·Σ c_i z̄^i =
  u(γ)·Σ (ζc_i)·z̄^i (ζ commutes into the F_k-coefficients of the z̄-basis
  expansion) and ζ·c_i ∈ 𝔸_k(γ_i) by the induction hypothesis. ∎ Hence |𝔸(γ)| = q^{a_q(γ)}
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

### 5.6 (ii.3)/(ii.4) — WALKED (rev 2; pass-1 finding 8), consumers fenced

**(ii.3) block disjointness, the case split displayed.** Distinct
development slots have disjoint leaf subtrees — the development is a
coordinate partition [SKEL]. For the SAME B and heights γ ≠ γ′ in one
scale (hence γ* ≠ γ′* — both cases of §5.3's stretch display are injective):
- CASE γ* ≢ γ′* (mod e_k): the forced slot classes t_k·γ* and t_k·γ′*
  differ mod e_k because t_k is INVERTIBLE mod e_k (h_k·t_k ≡ 1 (mod e_k),
  the Bézout datum) — the two blocks draw on DISJOINT slot sets.
- CASE γ* ≡ γ′* (mod e_k): the anchors agree, j₀ = j₀′; at each shared slot
  j = j₀ + i·e_k the two SLOT HEIGHTS differ — γ_i = γ* − j·h_k ≠
  γ′* − j·h_k = γ′_i (for FIXED j the map γ ↦ γ* − j·h_k is the injective
  stretch followed by a translation) — and the induction hypothesis (this
  statement one stage down) makes β(B_j, γ_i) ∩ β(B_j, γ′_i) = ∅; the
  induction bottoms at the base, where distinct heights v ≠ v′ of the same
  leaves are distinct F_q-digit ADDRESSES (leaf, v) ≠ (leaf, v′) by
  construction.
So no two equations of one system pin the same digit coordinate.

**(ii.4) one fresh diagonal digit, derived (not carried).** By
(ii.2)^(q) + (ii.3), a block equation d_γ(B) = X is CARRY-FREE in the
development frame's own leaf coordinates: it pins exactly the fresh leaves
of its own block β(B, γ), through the additive bijection of §5.4's
mechanism. In the other frame (f's plain coefficients, where the ledger
counts), compose with (ii.1) retyped per (RT-1)/(RT-5): every development
map is a digit-level affine unitriangular bijection for the global
well-order (height ascending, then Fact A's elimination order), so each leaf
equation transforms to

  digit(f, block address) = (the value forced by X) + (an F_p-coefficient
  polynomial function of the F_q-digits at strictly earlier addresses),

with UNIT DIAGONAL — the coefficient of the fresh coordinate is 1, read off
(ii.1)'s display digit_n(y_i) = digit_n(x_i) + (earlier), composed finitely
many times (each composition adds only strictly-earlier terms). Hence,
processing the level-N leaf digits in the global order, a free leaf admits
q values and a pinned leaf admits EXACTLY ONE value given its predecessors,
whatever those predecessors are — solvability per coordinate never spoils.

FENCE (unchanged): the MASS/counting consumers of (ii.3)/(ii.4) (per-digit
factors |𝔸|^{−1}, Theorem C's products) are the counting layer — NOT
consumed by this pass and not re-scoped here (§7). **✓**

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

### 6.3 D.9(b)/(c) — WALKED (rev 2; pass-1 finding 6)

*(These are CONSUMED — by D.7(iii)'s value-group step, D.7(v)(2)'s
consecutive positions, and the (S6b) discussion — so [SKEL] labels were not
a derivation.)*

DEFINITIONS, displayed (rev 1 never defined f_r): per stage r, 𝒲_r :=
w_r(C_r∖0) ⊆ e_r·ℤ, h_r := w_r(Φ_r), and **f_r := the least integer bound
with 𝒲_r ⊇ (e_r·ℤ) ∩ [e_r·f_r, ∞)** — the cofiniteness threshold, shown to
exist by (b)'s induction. INDUCTION ORDER (the source's pass-10 repair,
carried): all stage-r quantities (e_r, h_r, f_r, inequality (c)) are fixed
BEFORE Φ_{r+1} is constructed; w_r(Φ_{r+1}) = e_r·h_r·g_r enters only as the
number fixed by D.5's equal-weights design (§2.2).

**(b) Cofiniteness — the residue-class argument walked.** By §6.1 (walked),
𝒲̂_r = ⋃_{0≤j<e_r·g_r} (𝒲_r + j·h_r) — the NEXT coefficient space's weight
set in the stage-r scale. Claim: 𝒲̂_r contains EVERY integer
V ≥ e_r·f_r + (e_r − 1)·h_r. Derivation: gcd(e_r, h_r) = 1, so
j ↦ j·h_r mod e_r is a bijection on residues mod e_r, and j ranges over
0 ≤ j < e_r·g_r ⊇ e_r consecutive values; pick the unique j ∈ [0, e_r) with
j·h_r ≡ V (mod e_r). Then V − j·h_r ∈ e_r·ℤ and V − j·h_r ≥
e_r·f_r + (e_r−1)·h_r − (e_r−1)·h_r = e_r·f_r, so V − j·h_r ∈ 𝒲_r by the
induction hypothesis (f_r's defining property), i.e. V ∈ 𝒲_r + j·h_r ⊆
𝒲̂_r. After the D.0 stretch, 𝒲_{r+1} = e_{r+1}·𝒲̂_r ⊇ (e_{r+1}·ℤ) ∩
[e_{r+1}·(e_r f_r + (e_r−1)h_r), ∞), so f_{r+1} exists with
**f_{r+1} ≤ e_r·f_r + (e_r−1)·h_r** (the "next bound, before rescaling").
Base: 𝒲₁ = e₁·ℤ≥0 EXACTLY (§6.2), f₁ = 0. Pure arithmetic on the shared
integer data — no residue object. Consumed by: D.3(e)'s fullness remark
(I(γ) full above the bound), D.7(iii)'s value-group-ℤ step (§2.3: the
coefficient weights contain e′·(every integer above the bound), whose
differences generate e′·ℤ), and D.7(v)(2) (§3.2 — the g slot weights all
land in 𝒲 once δ clears the bound). **✓**

**(c) Per-stage domination h_r > e_r·f_r — the induction walked.** Base:
h₁ ≥ 1 > 0 = e₁·f₁. Step: by (b)'s bound and the hypothesis h_r > e_r·f_r,
f_{r+1} ≤ e_r·f_r + (e_r−1)·h_r < h_r + (e_r−1)·h_r = e_r·h_r ≤
e_r·h_r·g_r = w_r(Φ_{r+1}); by (I-aug) at the next read (§3.4, walked), the
read slope exceeds the key weight: h_{r+1}/e_{r+1} > w_r(Φ_{r+1}) > f_{r+1},
i.e. h_{r+1} > e_{r+1}·f_{r+1}. Induction closes. Consumed by: D.7(v)(3)'s
threshold headroom and the (S6b) discussion (§3.3). **✓**

**(d) Recentering realizability:** the realizer itself is walked DIRECTLY at
§3.5(b) via (S6b) + (I-aug) (the source's own rev note: Lemma REAL's
Frobenius machinery is no longer needed for it); (d)'s remaining content —
persistence of the bound along whole histories — is run-production
bookkeeping, outside this slice (§0.4). **✓**

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
| D.3(e)(ii) fullness remark | D.9(b) | WALKED §6.3 |
| D.9(a) | (S2) + (S6a) realizers + arithmetic | walked §6.1; realizers walked §3.3 |
| D.9(b)/(c) | gcd residue-class argument; (I-aug); D.5's equal-weights number | WALKED §6.3 (rev 2) |
| (S6b) | (I-aug) (D.4); D.9(b)/(c) bounds; F′_prev-basis division; base bottoming | (I-aug) walked §3.4; bounds walked §6.3; construction walked §3.3 (rev 2); basis [REBUILT]; bottoming [Lemma ONTO] |
| D.10 recentered STAGE package (TRANS-RS: realizer, v = v′, K1(Φ′/v), coefficient-localization preservation, (S1)–(S6)′) | (S6b)+(I-aug); §2.2's K1 at g = 1; D.1; (P2) purity | WALKED §3.5 (rev 2); residue touch: ψ′ = z − c̃ irreducible over the rebuilt F (degree 1, field-generic) |
| D.10 RS-landing / lift independence / anchored display / a ≥ 0; D.8 landing; D.9(d) history persistence | run-production & ledger legs | [EXT — outside the slice (§0.4); consumed by NOTHING in the (S1)–(S6)/(R1)–(R3) chain] |

**NOT-CONSUMED verification** (M14's claim, checked display-by-display): the
walked texts cite §A/§B1/§0-Fact A and intra-§B2-DEF items ONLY. No walked
display cites C.0, C.0.5, C.1, C.1.5/(ZC), PIN-WELLDEF, Theorem C(a)/(b),
LST, TYP, or DOM. The counting layer is untouched. ✓

**PERIMETER VERDICT (the blueprint's open point (i) — the known-unknown):**
the audit surfaced NO §A/§B1 residue-theoretic consumption beyond the items
re-proved here (B1.1's graded identification, §2.1; the base digit
readings/unit lifts, Lemma ONTO; Fact A's coefficient bookkeeping, [SKEL]).
The pass's perimeter did NOT widen. REV-2 AMENDMENT: pass 1's headline
CRITICAL caught the ONE row where rev 1's claim exceeded its walk — the
recentered stage package; that leg is now WALKED (§3.5) rather than
re-fenced, and its sole new residue touch (ψ′ = z − c̃ irreducible over the
rebuilt F) is degree-1 field-generic, so the verdict stands with the walk
extended, not the perimeter narrowed. The likeliest wobble point named in the
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
verdict (rev 2 typing: each row's field list is a CLASSIFICATION against the
grammar convention displayed in the re-scoped verdict below; the per-row
"NO" is derived only for the integer-skeleton fields):

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

VERDICT, RE-SCOPED (rev 2; pass-1 finding 10 — the rev-1 verdict ASSUMED
its grammar/realization classification instead of deriving it from a
displayed species definition). Two claims of different grades, separated:

**(DERIVED — theorem-grade, from this walk):** the integer SKELETON of the
walked slice — weight sets 𝒲, anchors j₀, slot heights γ_i, attainable
index sets I(γ), digit positions, index sets 𝒜, degrees — is determined by
the integer stage tuples (d, (e_k, h_k, g_k)) alone, identically over every
W(F_q): no walked display computes any of those fields from q, and the
recursion producing them is the SAME integer recursion on both sides
((R3) + M14 Lemma 1, §8.2).

**(CLASSIFIED — a displayed convention, NOT a derivation):** the table's
grammar/realization split (F an object contributing only its degree data;
the scalar groups, alphabets 𝔸, u(γ)-values — and, after §3.5, D.10's
center c̃ ∈ Fˣ — as REALIZATION data; recentering EXISTENCE itself is
q-free arithmetic, §3.5(a)) sorts the walked displays against a species
grammar whose DEFINITION this note does not display. The source's species
data do include the actual field F, the actual irreducibles ψ_k, the scalar
groups, and D.10's center — so the sentence "no species definition consumes
q" cannot be concluded from the walked B2 displays alone, and is NOT
certified by this note. Whether the T-1 species grammar reads exactly the
integer-skeleton fields — making the derived claim above equal to that
sentence — is a statement about the species definition, discharged where
that definition is displayed: H4-M6's type-catalogue display (its §3.3 plan
item (2)). WHAT H4-M6 MAY CONSUME FROM HERE: the derived integer-skeleton
claim, plus the classification table AS A CLASSIFICATION (fields sorted
with pointers), never the headline sentence.

SCOPE FENCE (unchanged): species fields living OUTSIDE the walked text —
the multiplicity μ (D.8's landing/read selection), side selection, polygon
conventions of the catalogue layer — are not walked here, and H4-M6's §3.3
plan item (2) consumes exactly THIS slice check plus its own type-catalogue
display for the remainder (blueprint's consumes-line, synced).

## VERDICT

**PROVED at the displayed perimeter (§0.4).** (R1), (R2), (R3) hold over
A^(q) = W(F_q)[x] for every finite F_q, for every tower presented by the
§B2-DEF recipe with rebuilt residue data and (I-aug) reads — at every stage,
increment AND recentered (§3.5, rev 2); base ℤ_p and
every O_δ are instances of the one theory (§8.2). The mutatis-mutandis rule
was obeyed throughout: laws verbatim, objects rebuilt, and the audit (§7)
certifies the skeleton/residue split display-by-display with no perimeter
widening. NOT discharged here (honest fence): (R4) + the matching dictionary
(H4-M2); the run-production layer — D.8's landing and D.10's
RS-landing/lift-independence legs (REL.1's wider walk; D.4's (I-aug)
argument is walked at §3.4 and D.10's stage package at §3.5); the counting
layer (not consumed); and the (EQ-1) headline sentence "no species
definition consumes q", which is re-scoped at §8.3 (rev 2) to the DERIVED
integer-skeleton claim + a displayed classification, the species-definition
tie being H4-M6's obligation.
Status labels: base-ring inputs (O1)–(O4) and the Teichmüller/Witt facts —
(a) known (Serre, Corps Locaux II §4–6); Lidl–Niederreiter Thm 3.46 — (a)
known, consumed ONLY by the N-gate's domain grounding, never by the walk; the
re-scoped displays over W(F_q), Lemma ONTO, Lemma STAB, and the (O4) twist
display — (c) claimed new in this packaging (project constructions; the
literature's OM/Montes theory has the full-residue-field case only, per M14's
verdict block). Consumers may now read: M14's Lemma 2 hypotheses are supplied
(§1.3); M14's Theorem inputs (R1)–(R3) are supplied at both instances; the
(EQ-1) slice input for H4-M6 is §8.3's RE-SCOPED verdict — the derived
integer-skeleton claim plus the classification table, NOT the headline
sentence (rev 2).

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

- **Pass 1 (Codex, fresh context, 2026-08-08; full report
  `H4M1_pass1_2026-08-08.md`):** verdict as returned **CRITICAL** —
  2 CRITICAL + 8 GAP, alongside two explicit certifications: "The new (O4)
  identity itself checks out with the stated Witt-coordinate convention" and
  "Lemma ONTO correctly uses coefficientwise arbitrary lifts and the θ-basis
  to realize all of F₁; I found no substantive constant-realizer or
  Teichmüller-section defect in §5.5." ALL TEN findings ACCEPTED and FOLDED
  (rev 2, this file, 2026-08-08) — dispositions quoted in the REVISION
  RECORD below. The headline CRITICAL was folded by WALKING the missing
  derivation (option (a): new §3.5), not by narrowing the PROVED claim.
  **Clean counter: 0/2** (the §M bar is hostile pass ×2, fresh contexts,
  one Codex, and the standing discipline accepts only after consecutive
  clean passes — none is on record yet; pass 1 was not clean).
- Pass 2 (fresh context; the non-Codex slot of the §M mix, or Codex again
  per the division's call): PENDING — runs on the rev-2 text; its charge
  includes auditing each disposition recorded below.

## REVISION RECORD — pass-1 fold (rev 2, 2026-08-08; quote → disposition)

1. **CRITICAL (headline).** Quote: "the claimed perimeter includes
   recentered stages whose stage axioms are expressly not walked … The
   source's D.10 does substantially more than instantiate g = 1: it proves
   v = v′, K1 for the recentered key, preservation of the coefficient
   localization … Calling recentering a g = 1 increment 'at the AXIOM
   level' assumes precisely the stage package that must be proved."
   DISPOSITION: ACCEPTED — FOLDED BY WALKING (option (a)). New §3.5 walks
   D.10's TRANS-RS over W(F_q) at derivation grade: (a) species lemma;
   (b) realizer existence via the now-walked (S6b) + (I-aug); (c) equal
   weight + R(Φ′) = z − c̃ exactly; (d) K1(Φ′/v) as §2.2 INSTANTIATED at
   g = 1 (ψ′ = z − c̃ irreducible degree-1 over the rebuilt F — the leg's
   one residue touch); (e) v = v′; (f) the substitution identity in
   L_both; (g) (S1)–(S6) itemwise, including (L′^coeff)₀ = F preservation.
   §0.3/§0.4/§7/RESOLUTION/VERDICT re-pointed; the RS-landing,
   lift-independence, anchored-display, a ≥ 0, and D.9(d)-persistence legs
   remain fenced as run-production (consumed by nothing in (S1)–(S6)).
2. **CRITICAL.** Quote: "D.3(e)(ii.2) is mistranscribed at the top space …
   the authoritative source has two cases: 'γ* := γ/e_{k+1} …; γ* := γ at
   the top space (k = K)' … its displayed recursion is undefined there."
   DISPOSITION: ACCEPTED — FIXED at §5.3: the stretch conversion now
   displays BOTH cases (k+1 ≤ K stretch; k = K identity — no read K+1, no
   e_{K+1}), the top-space scale 𝒲̂_K is declared, the top-space pin
   u(γ) = z̄^{p_{j₀}(γ*)} (γ* = γ) is displayed, and §5.4's "likewise at
   the top" now reads through the two-case display.
3. **GAP.** Quote: "(S6a) is closed by reference instead of walking its
   defining display … 'Closure under the induction is trivial exactly as in
   the accepted text' is precisely citation-style closure forbidden by the
   charge." DISPOSITION: ACCEPTED — FIXED at §3.3: D.7(viii)'s formula
   𝒜′ = {(e′(γ+jh), −t′(γ+jh)) : (γ,κ) ∈ 𝒜, 0 ≤ j < eg} is displayed and
   derived both directions (⊆ via (S2) minimizing slots + the (S5′)
   position forcing; ⊇ via the single-slot realizers t_{γ,j} with their
   dig′ computed), with WHY κ is consumed (positions are weight-forced at
   every stage) and WHY every new position is forced (the Y′-exponent line
   count applies to every Ĉ-element) both displayed; orbit-group closure
   walked (the step realizer propagates literally the stage scalar).
4. **GAP.** Quote: "the constructive (S6b) offset-P-lift is not actually
   constructed … omits the source's essential construction
   t = Σ_{P_k≠0} t_k Φ_prev^{j₀+e_prev k} and does not walk equal weights,
   the forced residual window, absence of zero-scalar terms, or … residual
   is z^m P(z)." DISPOSITION: ACCEPTED — FIXED at §3.3: the construction is
   displayed and walked ingredient by ingredient — forced anchor j₀ and
   offset m (any residue class), unique P by the rebuilt basis, absent
   zero-scalar slots, the mutual-recursion threshold inequality derived
   from W > e_prev·h_prev·g_prev and (I-aug) at the previous read, equal
   summand weights verified, R(t) = z^m·P(z) by distinct consecutive
   positions + D.1(b), and the Lemma-ONTO bottoming.
5. **GAP.** Quote: "D.7(v), one of the source's delicate steps, is reduced
   to an ingredient list … does not walk the source's scale-sensitive
   choice … the g simultaneous slot weights, their conversion to
   parent-scale weights, the (S6b) threshold check for each slot, or
   extension and injectivity of D on degree-zero fractions."
   DISPOSITION: ACCEPTED — FIXED at §3.2(v): the three-ingredient argument
   is walked with the explicit δ-threshold δ ≥ e′·(bound + egh), the g
   slot weights δ/e′ − r·e·h checked into 𝒲 via the walked §6.3(b), the
   parent-scale conversion δ/(e′e) − r·h checked against w_prev(Φ) for the
   per-slot (S6b) supply, the consecutive positions via the stride rule,
   the basis span, and D's injectivity on degree-0 fractions displayed.
6. **GAP.** Quote: "D.9(b)/(c) are consumed but only asserted as
   'arithmetic' … The note neither defines f_r adequately nor walks the
   residue-class argument and the inductive bound." DISPOSITION: ACCEPTED —
   FIXED at §6.3: f_r defined (least cofiniteness threshold), (b)'s
   residue-class argument walked (gcd bijection on residues, the j-window,
   the V − j·h_r ≥ e_r·f_r estimate, the stretch giving f_{r+1} ≤
   e_r f_r + (e_r−1)h_r), (c)'s induction walked through (I-aug); the
   consumers (D.7(iii)/(v), (S6b)) re-pointed to the walked text.
7. **GAP.** Quote: "D.4 is closed by 'the same' and 'base-free' language
   rather than walked … The source explicitly derives the chord inequality,
   identifies the side ending at the pinned vertex, and uses monotonicity
   of lower-hull slopes … The recentering case additionally depends on the
   unwalked v = v′." DISPOSITION: ACCEPTED — FIXED at §3.4: chord
   inequality derived from the landing box, the vertex-ending side
   identified as a chord, hull-slope monotonicity displayed, root case
   walked; the recentering bullet now consumes §3.5(e)'s walked v = v′
   with the no-circularity note displayed.
8. **GAP.** Quote: "D.3(e)(ii.3)/(ii.4) are 'carried,' not walked … The
   source has a case split according to γ* mod e_k, then a separate
   fixed-slot height argument, followed by the global-order proof that
   every transformed equation has one fresh diagonal digit."
   DISPOSITION: ACCEPTED — FIXED at §5.6: the two-case split walked
   (t_k-invertibility; fixed-slot height injectivity with the base
   bottoming at distinct addresses), and (ii.4)'s unit-diagonal fresh-digit
   claim derived through finite composition of (ii.1)'s unitriangular
   display in the global order.
9. **GAP.** Quote: "Lemma STAB proves scalar stability but omits additive
   closure … The conclusion is plausible; the displayed proof does not
   establish its full statement." DISPOSITION: ACCEPTED — FIXED at §5.4:
   additive closure, 0-membership, and inverses (ζ = −1) walked through
   the product display + induction, alongside the original scalar clause.
10. **GAP.** Quote: "the (EQ-1) species conclusion assumes, rather than
    derives, what counts as grammar data … the note … cannot conclude from
    the walked B2 displays alone that no species definition consumes q. At
    most it has shown that the integer weight/anchor skeleton is
    independent of q." DISPOSITION: ACCEPTED — RE-SCOPED at §8.3 (the
    honest option; no bounded walk exists here because the species
    DEFINITION lives outside this note's slice): the verdict now separates
    the DERIVED integer-skeleton q-independence (theorem-grade) from the
    grammar/realization CLASSIFICATION (a displayed convention), states
    explicitly that the headline sentence is NOT certified by this note,
    and re-types what H4-M6 may consume; the table rows re-typed
    accordingly; D.10's center c̃ (now in scope via §3.5) classified.
    VERDICT section synced.
