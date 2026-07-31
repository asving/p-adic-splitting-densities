# O9 — the order-r stratum census (CL-6 at OM order ≥ 2) — Phase-B verify brief (Fable, 2026-08-01)

**Charge (tree DELTA 2 §D2.6 step 7 / node O-9).** Deliver the order-r census
statement + proof composing the PROVED level-1 result (M08 Theorem 2) with the
GD-3 anchored march ((GR-B), GD23 rev 2 §7.2), or the honest partial with the
exact residue; attack the OL-A slot ledger directly; extend the depth-3
harness to order-2 CENSUS counts.

**This brief is self-contained modulo four named in-repo imports**, quoted
where used: (M08) = `M08-cl6-general_fable.md` (Lemma 1; Theorem 2; Lemmas
A/B/C/D; the §3 OL-A..OL-D reduction); (GR-B) = `GD23_phaseB_verifybrief_rev2.md`
§7.2 (the anchored-march residue-structure package) with Theorems GD3-MIN/
GD3-FULL+OL-B; (GD23-W) = the same brief's (V1)/DEVID/(KP) layer; (LIT) =
`LITUNIT_2026-08-01.md` + `docs/GMN_citations.md` §6 (the pinned GMN/FGMN/
MacLane statements). GMN = Guàrdia–Montes–Nart, Trans. AMS 364 (2012),
arXiv:0807.2620v2 numbering.

## 0. Status table (the whole unit at a glance)

| item | statement | status here |
|---|---|---|
| OL-A(i) coordinates | φ-adic development is a level-compatible coordinate system | **PROVED** (Lemma A1; any O) |
| OL-A(ii) triangularity + ledger counts | v_{r+1} is slot-triangular on deg < m; valuation-condition counts are pure q-powers with p-free exponents | **PROVED** (Lemmas TRI, LED); Route G = GMN scope via pinned Prop 2.7/Lemma 2.2(2); Route W = any O, conditional on GD23's (V1)+(KP) beyond order 1 |
| OL-A(iii) line/digit structure | graded digit reads are per-slot F_{q^d}-bijections | = **GD-3/OL-B**, consumed not re-proved; order 1 PROVED (GD23 RES-1); orders ≥ 2 = (GR-B) [OPEN there] |
| OL-A(iv) determinacy + stacking | (DET) working-level formula PROVED (window); the joint-with-parent freshness clause (FRESH) displayed, order-1 instance proved, deep = GD-2/CL-13 territory | **PARTIAL** (§5) |
| OL-B | twisted residues / exponent-map audit | **RE-POINTED at GD-3** (executes the tree's D2.2 row); nothing owed here beyond (GR-B) |
| OL-C | the order-(r+1) census formula | **PROVED conditional on (GR-B) + (FRESH)** (Theorem CEN-W outright from (GR-B); CEN-J adds (FRESH)); r = 0 instance = M08 Thm 2, unconditional |
| TYPE-MARCH | the anchored march preserves factorization types | **PROVED** (new, one page; the V26-2 lesson made load-bearing) |
| JUNCTION-PIN | the window chain's right end is realization-pinned; telescope gives exactly ∏M (no stray (q^d−1)) | **PROVED** given (GR-B)(2′)+(3); measured ε = 0 on 18 cross-p cells |
| OL-D | per-row T-counts at the built tables | **OPEN** (officialization; the order-r Remark-2.7 analogue displayed, (GR-B)-conditional) |
| falsifier | order-2 census harness (K1–K4, T2) | RUN: 0 violations; §10 |

Honest headline: **the order-r census is REDUCED to exactly two named open
inputs — (GR-B) (GD-3's package, already the GD campaign's residue) and
(FRESH) (the GD-2/CL-13 vertex-law layer at deep states, already CU-1's
step content). No open input is new to this unit.** Everything else is
proved below, and the r = 0 instance recovers M08 Theorem 2 exactly.

## 1. Setting, indexing, and the pinned imports

O = a complete DVR with finite residue field F_q (q = p^δ), maximal ideal
(π), v_π(π) = 1; mixed or equal characteristic. Route G (GMN's printed
scope) additionally assumes O = the ring of integers of a finite extension
of ℚ_p (LIT §6.0(2)); Route W removes this via GD23 (§3 below).

**The type.** t = (φ₁; λ₁, φ₂; …; λ_r, ψ_r), a type of order r ≥ 0 in GMN's
§2.1 sense (r = 0: t = ψ₀ alone). Data: f_i = deg ψ_i; λ_i = −h_i/e_i in
lowest terms; m_i = deg φ_i, m₁ = f₀; the residue tower
F_q = F₀ ⊆ F₁ ⊆ … ⊆ F_{r+1}, F_{i+1} = F_i[y]/(ψ_i). Write:

    d := [F_{r+1} : F_q] = f₀f₁⋯f_r,        e := e₁⋯e_r  (e = 1 at r = 0),
    φ := φ_{r+1} = a representative of t (GMN Thm 2.11/Def 2.12),
    m := deg φ = m₁·∏_{i=1}^r e_i f_i = e·d,
    w := v_{r+1}  (GMN Def 2.5; ℤ-valued, w(c) = e·v_π(c) for c ∈ O),
    V̂ := w(φ)    (the V-recursion value; GMN Thm 2.11 / Prop 2.7(4)).

**INDEX FLAG (recorded correction to the tree's display).** The tree's O-9
node text and M08 §3 write the census field as F_{q^{f̄_r}} with
f̄_r := f₀⋯f_{r−1}. In GMN indexing the order-(r+1) residual polynomials of
a type of order r live over F_{r+1}, of degree d = f₀⋯f_r — one more factor.
The harness instance: order-1 parent (e, h, ψ of degree g) has f₀ = 1
(root key X), f₁ = g, d = g, reads over F_{q^g}. All statements below use d.
Nothing mathematical changes ("ONE polynomial in q" is insensitive); the
tree display should be read with d.

**Pinned literature statements consumed** (all quoted verbatim in LIT):

* (P1) GMN Prop 2.7(1): w(P) ≥ e_r·v_r(P), equality iff ω_r(P) = 0; with
  Lemma 2.2(2) (deg P < m_r ⟹ ω_r(P) = 0): deg b < m_r ⟹ w(b) = e_r v_r(b).
* (P2) GMN Prop 2.7(3): the φ_r-adic development computes w by minima.
* (P3) GMN Prop 2.7(4) + Thm 2.11: the V-recursion for w(φ_i), w(φ).
* (P4) GMN Lemma 2.17 + §2.1 ω-definition + Def 1.8: length of N_{r+1}^−(f)
  = ω_{r+1}(f) = ord_{ψ_r}(R_r(f)), including the slope-−∞ side; the
  printed proof gives the FIRST-ATTAINMENT form.
* (P5) GMN Prop 2.10: realizability of any prescribed residual value at any
  admissible weight by some P with deg P < m (corroboration for (GR-B)'s
  surjectivity clause; not load-bearing — see §5.1).
* (P6) GMN Thm 2.26 (theorem of the product, order r) — corroboration only.
* (P7) FGMN Thm 4.2 / Cor 4.4(2) / Thm 4.8 / Cor 5.6(2) / Prop 5.14+Cor 5.15
  — (GR-B)'s per-clause printed homes (LIT §5); consumed only THROUGH (GR-B).

**The one big displayed open input.** (GR-B) [GD23 rev 2 §7.2], at state
order r+1: the anchored-march residue-structure package — the degree-0
generator ȳ with Δ = F_{r+1}[ȳ]; the invertible anchor-monomial system; the
residual operator R^{gr} with (1) multiplicativity up to F_{r+1}^×, (2′) the
anchored-march identity in(f) = ϕ_{w(f)}·R^{gr}(in f)(ȳ) with slot-κ stride
monomial ϕ·ȳ^κ (LINEAR in κ) and marched per-slot digit reads, and
R^{gr}(in f) ∼ R_λ(f); (3) R^{gr}(ψ̂) ∼ ψ_r; (4) faithfulness
ord_{ψ_r}(R^{gr}(α)) = ord_{ψ̂}(α). Order-1 instance PROVED (GD23 RES-1);
orders ≥ 2 OPEN, cited clause-by-clause. This unit consumes (GR-B) as a
black box; its internal transcription caveats stay priced there.

## 2. The stratum datum and the two census statements

Fix a type t of order r, a representative φ, a monic f ∈ O[x] of degree n,
and the working level N. Write the φ-adic development

    f = Σ_{k=0}^{ℓ} a_k φ^k,   deg a_k < m,   ℓ := ⌊n/m⌋,   a_ℓ monic iff m | n,

and the order-(r+1) polygon heights u_k := w(a_k) + k·V̂ (GMN Def 2.3 via
(P2)/(P3); the principal part N^−_{r+1}(f) is the negative-slope part of the
lower hull of {(k, u_k)}, slope-−∞ side included, per Def 1.8).

**Definition (level-N stratum datum D over t).** D consists of:

* a chain of faces S = 1..s with vertices (k₀, U₀), …, (k_s, U_s) in
  ℤ × ℤ (u in w-units), k₀ < ⋯ < k_s ≤ ℓ, slopes strictly increasing and
  all < 0;
* the LEFT-TAIL CUTOFF convention for k < k₀ (the finite-level reading of
  the slope-−∞ side, GD-8's corner): the only condition imposed at k < k₀
  is u_k > (the extended line of face 1 at k) — deep heights are NOT pinned;
* for each face S: λ_S, a factorization type over F_{r+1} — a multiset of
  (degree, multiplicity) pairs with Σ deg·mult = d(S) := (k_S − k_{S−1})/e_S,
  where −h_S/e_S is the face's slope in lowest terms (types are invariant
  under F^×-scaling and under y ↦ ρy, ρ ∈ F^×; both invariances are used);
* the RIGHT-TAIL condition for k > k_s: u_k ≥ U_s.

The stratum conditions on f: N^−_{r+1}(f) has exactly the faces of D below
the cutoff (equivalently: u_k = the face value at on-line lattice slots
k = k_{S−1} + j·e_S with vertex digits nonzero, u_k > the local face line at
all other k ≥ k₀, the left/right tail conditions), and type(R_{λ_S}(f)) =
λ_S for every S, with R_λ the GMN Def 2.21 residual polynomial of order r+1.

**(DET) — the level-N determinacy condition (proved sufficient, §5.2):**

    max_{0 ≤ k ≤ ℓ}  ( line_D(k) − k·V̂ )  ≤  e·N − 1,            (DET)

where line_D(k) := max over faces of the extended face line's value at k.
Under (DET) every stratum condition is determined by f mod π^N (Lemma LED
(iii)), so the census below is well-defined:

    C_{D,N}(t, ρ) := #{ f mod π^N : f in the stratum (D over the parent
                        realization ρ) },

where ρ = a concrete realization of the tower through order r (the fixed
concrete φ_i, ψ_i, and the parent stratum data that produced t).

**Theorem CEN-W (window census; conditional on (GR-B) at order r+1).** For
the WINDOW-ONLY stratum — the conditions of D imposed on the development
coordinates (a_k) with the frame φ fixed, no parent-membership conditions —
under (DET):

    #window stratum in (O/π^N)-coordinates
        = q^{E′(D,N)} · (q^d − 1)^{ε(D)} · ∏_S M_{λ_S}(q^d),

with ε(D) = 0 if the datum pins the right-end digit (k_s = ℓ with m | n:
the monic top) and ε(D) = 1 otherwise (free right end; in CEN-J the parent
realization supplies the pin — JUNCTION-PIN, §5.4 — so ε never appears
there), M_λ the M08 Lemma-B type-count polynomial, evaluated at q^d, and

    E′(D,N) = Σ_{k=0}^{ℓ} [ m·N − s_k ] − d·(#on-line lattice slots),
    s_k := Σ_{𝐣} max(0, ⌈(β_k − wt(𝐣))/e⌉),   β_k := ⌈line-or-pin value at k⌉ − k·V̂,

where 𝐣 runs over the m slot monomials of the ledger (§4) and wt(𝐣) their
w-weights. One ℕ-valued polynomial in q; independent of p, O, δ, and of ρ.
At r = 0 this IS M08 Theorem 2 (with E′ = E(D,N), d = f₀; §6.4).

**Theorem CEN-J (joint census; conditional on (GR-B) + (FRESH)).** Under
(DET) additionally over the parent's own reads:

    C_{D,N}(t, ρ) = (#parent-realization stratum) · q^{E″(D,N)} · ∏_S M_{λ_S}(q^d)

with E″ = E′ minus the exponent already charged by the parent's conditions
— i.e. the refinement factor is the SAME for every realization ρ of the
same discrete parent shape, and is the displayed polynomial. (FRESH) is the
stacking clause of §5.4. Falsifier: harness checks K2 (realization
independence) and K4 (cross-p atom fit), 1,128,288 order-2 instances, 0
violations (§10).

## 3. The valuation layer: two routes (mirrors GD23's Route A/B split)

* **Route G (GMN scope: O = integers of a finite extension of ℚ_p).** All of
  §4 consumes only the pinned (P1)–(P4). Unconditional.
* **Route W (any complete DVR O, perfect-residue not even needed here since
  F_q is finite).** Replace (P2) by GD23's Theorem DEVID (the development
  identity at every order, PROVED there given (V1) + the (KP) block) and
  (P1) by the (V1)-tower rescaling law (GD23 §5, MacLane-composed via
  Lemma BRIDGE). Route W inherits GD23's conditionality: (KP)/GD-1 beyond
  order 1 + the pinned TIE transcriptions. Either route suffices; Route G
  is unconditional at the intended instance (pools O = W(F_{p^δ})
  unramified — inside GMN's scope).

## 4. OL-A(i)(ii): coordinates, triangularity, and the slot ledger (PROVED)

**Lemma A1 (coordinates).** φ monic of degree m ⟹ iterated Euclidean
division gives a bijection f ↔ (a_0, …, a_ℓ) (deg a_k < m), O-linear in the
coefficients, hence compatible with reduction mod π^N: f ≡ f' (mod π^N) ⟺
a_k ≡ a'_k (mod π^N) for all k. Same statement for the mixed-radix monomial
basis below (the change of basis is unitriangular over O since every B_𝐣 is
monic of degree deg B_𝐣, one per degree). *Proof:* division by a monic
polynomial is an O-linear operation with O-coefficient formulas. ∎

**Definition (the slot ledger).** With φ₀ := x, the ledger monomials are

    B_𝐣 := φ_0^{j_0} φ_1^{j_1} ⋯ φ_r^{j_r},   0 ≤ j_0 < f₀,  0 ≤ j_i < e_i f_i,

m of them, degrees Σ j_i m_i = each of 0..m−1 exactly once (mixed radix,
m_{i+1} = e_i f_i m_i). Slot weights wt(𝐣) := w(B_𝐣) = Σ j_i·w(φ_i)
(w is a valuation, (P1)-scope), computed by the (P3) V-recursion — integer,
≥ 0, and p-free lattice data of the type.

**Lemma TRI (triangularity; the ledger computes w below deg m).** For
c_𝐣 ∈ O, not all zero:

    w( Σ_𝐣 c_𝐣 B_𝐣 ) = min_𝐣 ( e·v_π(c_𝐣) + wt(𝐣) ).

*Proof.* Induction on r. r = 0: w is the Gauss valuation on deg < f₀ and
all weights are 0. Step: for deg a < m_{r+1} write the φ_r-development
a = Σ_{j_r < e_r f_r} b_{j_r} φ_r^{j_r} (deg b_{j_r} < m_r; the index bound
from the degree). By (P2) at order r+1: w(a) = min_{j_r}(w(b_{j_r}) +
j_r·w(φ_r)). By (P1): w(b) = e_r·v_r(b) on deg < m_r. By the inductive
hypothesis for v_r (whose own ledger is the sub-radix 𝐣' = (j_0..j_{r−1})):
v_r(b_{j_r}) = min_{𝐣'}(e'·v_π(c) + wt_r(𝐣')). Multiplying by e_r and using
(P1) on the monomials themselves (e_r·wt_r(𝐣') = w(B_{𝐣'}) for
deg B_{𝐣'} < m_r) recombines the nested minima into the displayed one. ∎
[Route W: (P2) ↦ DEVID, (P1) ↦ the (V1)-tower rescaling; same skeleton.]

**Lemma LED (ledger counts; all PROVED from A1 + TRI).** Write
W_N := {a : deg a < m} ⊗ O/π^N ≅ (O/π^N)^m via the ledger coordinates.
For β ∈ ℤ, 0 ≤ β ≤ eN:

* (i) the condition w(a) ≥ β is well-defined on W_N (adding π^N b shifts w
  by ≥ eN ≥ β), and for β ≤ eN − 1 so is the exact condition w(a) = β
  together with the graded class of a in G_β := {w ≥ β}/{w > β};
* (ii) #{a ∈ W_N : w(a) ≥ β} = ∏_𝐣 q^{N − max(0, ⌈(β − wt(𝐣))/e⌉)}
  =: q^{mN − s(β)} — a pure power of q whose exponent is a p-free function
  of (N, β, the type's lattice data);
* (iii) G_β is an F_q-vector space of dimension s(β+1) − s(β).

*Proof.* (ii): by TRI, w(a) ≥ β ⟺ per coordinate v_π(c_𝐣) ≥
⌈(β − wt(𝐣))/e⌉; count each coordinate in O/π^N. (i),(iii): direct. ∎

## 5. OL-A(iii)(iv): the digit reads, (DET), and (FRESH)

### 5.1 The digit read is a fiber-uniform F_q-linear surjection [(GR-B)]

Assume (GR-B) at order r+1. For deg a < m the φ-development of a is a
itself, so R^{gr}(in a) has ȳ-degree 0: by (GR-B)(2′),
in(a) = ϕ_{w(a)}·c(a) with c(a) ∈ F_{r+1}^× — the LINE clause: initial
forms of degree-< m elements of weight β live on the line ϕ_β·F_{r+1}.
Define the read r_β : {a ∈ W_N : w(a) ≥ β} → F_{r+1} by r_β(a) := c(a) if
w(a) = β, else 0 (well-defined for β ≤ eN − 1 by LED(i)).

* **Additive:** if w(a) = w(b) = β and w(a+b) = β then in(a+b) = in(a) +
  in(b) in G_β so c adds; if w(a+b) > β then in(a) + in(b) = 0; the mixed
  and zero cases are immediate. F_q-linear: for a unit u ∈ O,
  in(ua) = ū·in(a), ū ∈ F_q ⊆ F_{r+1}.
* **Surjective onto F_{r+1}** for attained β: (GR-B)(2′)'s slot clause (the
  per-slot digit read is a BIJECTION of F_{r+1}); corroborated by the
  pinned (P5) (GMN Prop 2.10 constructs a realizer for every prescribed
  residual value; not load-bearing).
* **Fiber-uniform (the counting consequence):** a surjective homomorphism
  of finite abelian groups has equal fibers, so for EVERY z ∈ F_{r+1}
  (zero included):  #{a ∈ W_N : r_β(a) = z} = q^{mN − s(β) − d}.

This is the exact order-r analogue of M08 Lemma A's second display, and the
only place the residue-field structure enters the counts.

### 5.2 (DET) suffices (PROVED)

Under (DET) (§2), every per-coordinate condition of the stratum has
β_k ≤ eN (inequality conditions) or β_k ≤ eN − 1 (exact + digit read at
on-line lattice slots), so by LED(i) the stratum is a well-defined subset
of the level-N boxes. The non-lattice abscissas of a face carry
non-integral line values (slope −h_S/e_S in lowest terms), so the ceiling
⌈line − kV̂⌉ implements "strictly above" exactly as M08's c_i convention;
interior lattice slots stay free (their zero digit class = strictly above);
vertex nonvanishing is forced by the types (R_λ has exact degree d(S) and
nonzero constant term — M08 §2.1's note, verbatim at order r+1). ∎

### 5.3 The census key must be level-determined — two compiled traps

The falsifier surfaced two instructive finite-level failure shapes, both
now displayed as part of OL-A(iv)'s content (they are what (DET) fences):

* **The u-space visibility trap.** A slot whose coefficient valuation
  exceeds the working cap can still fall BELOW an extended face line of
  the visible window (the comparison lives in u = β + kV̂ coordinates, not
  β): reading the visible faces as the polygon then mis-keys strata. Any
  census claim without (DET) is false at that level.
* **The cap-split artifact.** Splitting a stratum by "coefficient
  vanishes at working level" produces censuses like (q−1)(q³−1) — NOT of
  the census-atom form q^{E}·∏M: the deep tail of a stratum must be left
  free (the left-tail cutoff convention), never keyed. Measured concretely
  at the (0,2)→(4,0), slope −1/2 design before the fence was installed.

### 5.4 (FRESH) — the joint-with-parent stacking clause [displayed OPEN]

**(FRESH).** For every realization ρ of the parent tower (level-N₀
conditions, N₀ ≤ N): conditioned on ρ, (a) the window's below-line height
conditions at the created order-(r+1) state hold automatically (the
polygon/vertex laws transport the parent's pins: WGEO/VTX content), and
(b) each on-line window read of §5.1 is, on the ρ-fiber, an affine
function of one fresh digit with unit slope — so the joint census factors
as (#ρ-fiber)·(the window factors). Status: order-1 instance PROVED (it is
M08 §2.2's separation together with the KEY1 standard-lift shape; the Lean
order-≤1 twin is the CL-13/LVL-DET layer); general order = the GD-2
vertex-law layer at deep states — EXACTLY CU-1's step content, not a new
obligation of this unit. Falsifier: check K2 below (realization
independence; 1,128,288 order-2 instances, 0 violations).

**JUNCTION-PIN (a clause of (FRESH), stated separately because the census
formula's shape depends on it).** Conditioned on ρ, the digit read at the
window's right-end vertex (the first-min-attainment slot, k_s = ω_{r+1};
(P4)) is a ρ-determined nonzero CONSTANT (the transported anchor/VTX read),
not a free unit. Consequence: the vertex chain below telescopes to exactly
∏_S M_{λ_S}(q^d) with NO stray (q^d − 1) factor. Measured: all 18 cross-p
cells fit ε = 0 (§10). In the window-only theorem (no ρ), the right end is
free and the factor (q^d − 1) appears — the ε(D) dichotomy in CEN-W.

## 6. OL-C: the census proof

### 6.1 Lemma TYPE-MARCH (new; why the march makes the census polynomial)

Let F be any field, τ_κ = τ₀·ρ^κ (τ₀, ρ ∈ F^×) a GEOMETRIC per-slot twist
system, R(y) = Σ_κ c_κ y^κ, and R̃(y) := Σ_κ τ_κ c_κ y^κ. Then
R̃(y) = τ₀·R(ρy), and y ↦ ρy is a degree-preserving F-algebra automorphism
of F[y] fixing (y) — so R̃ and R have the SAME factorization type, and
R̃(0) ≠ 0 ⟺ R(0) ≠ 0. ∎

Consequence: (GR-B)(2′)'s anchored march has per-slot normalizer exponents
AFFINE in the slot index κ (the "one fixed step, linear in κ" clause), so
the digit-vector polynomial of any face and GMN's R_λ(f) differ by a
scalar and y ↦ ρy: all TYPE conditions transfer verbatim. **Warning
display (this is load-bearing, not cosmetic):** a general fixed
invertible per-slot twist system does NOT preserve types — over F₃ the
twist (1, 1, 2) sends y² + y + 1 = (y+2)² [type {(1,2)}] to
2y² + y + 1 ∼ y² + 2y + 2, irreducible [type {(2,1)}]. A wrong (slot-fresh)
normalization therefore breaks census polynomiality exactly as M08 §2.5's
character phenomenon predicts — the anchored march is not a convention
choice but the mechanism that makes CL-6 true at order ≥ 2. (This is the
census-side face of CU-1's 1,818× slot-fresh refutation.)

### 6.2 The finite-field layer imports verbatim at F_{q^d}

M08 Lemma B (M_λ ∈ ℚ[X], M_λ(Q) counts monic type-λ polynomials with
nonzero constant term over F_Q), Lemma C (end-pinned counts are ratio-class
functions ν_λ with Σ_t ν_λ(t) = M_λ(Q)), and Lemma D (the vertex-chain
telescope) are statements about an ABSTRACT finite field F_Q: their M08
proofs use only |F_Q| = Q and the F_Q^×-scaling action. Import them at
Q = q^d. Note M_λ(q^d) = (M_λ ∘ X^d)(q): still ONE polynomial in q.

### 6.3 Proof of Theorem CEN-W (and the ε(D) dichotomy)

By A1 the window stratum is a condition set on the coordinates (a_k),
separately per k. Per abscissa: right tail, left tail, and off-line slots
contribute the LED(ii) q-powers (their β_k as displayed in E′); each
on-line lattice slot contributes, per prescribed digit z ∈ F_{r+1}, exactly
q^{mN − s_k − d} (§5.1 fiber uniformity — z-independent). Summing over the
digit vectors compatible with the polygon and the types:

    #window = q^{E′(D,N)} · Z_D,   Z_D := #{ digit vectors : vertex digits
              ≠ 0, type(face S) = λ_S for all S }

where the type of a face's digit vector is read through TYPE-MARCH (§6.1)
as the type of the corresponding R_λ — the (GR-B) dictionary. Z_D is now
verbatim M08 §2.6 over F_{q^d}: group interior slots per face (Lemma C),
telescope across the shared vertices (Lemma D). If the datum pins the
right-end digit (k_s = ℓ, m | n: a_ℓ = 1, read = fixed constant — ε = 0)
the telescope gives Z_D = ∏_S M_{λ_S}(q^d) exactly; otherwise the right
end is a free unit and Z_D = (q^d − 1)·∏_S M_{λ_S}(q^d) (ε = 1). ℕ-valued,
p/O/δ-free: all exponents are ledger data (LED(ii)), M_λ by Lemma B. ∎

### 6.4 Proof of Theorem CEN-J, and the r = 0 cross-check

Condition on ρ. By (FRESH)(a) the automatic conditions charge nothing new;
by (FRESH)(b) each window read is fresh-digit affine with unit slope, so
the per-slot counts of §5.1 apply on the ρ-fiber; by JUNCTION-PIN the
chain's right end is a ρ-determined nonzero constant, so the telescope
yields exactly ∏M (Lemma D with pinned end; Lemma C makes the value of the
pin irrelevant — only its nonvanishing and fixedness enter). Hence the
refinement factor q^{E″}·∏_S M_{λ_S}(q^d), the same for every ρ of the
discrete shape. ∎ (Conditional on (GR-B) + (FRESH).)

r = 0 instance: e = 1, d = f₀, all ledger weights 0, s(β) = f₀·β; E′
collapses to f₀·Σ_i(N − c_i) with M08's c_i, the top digit is pinned by
monicity (ε = 0), and the formula reads q^{f₀E}·∏M_λ(q^{f₀}) — exactly M08
Theorem 2 with Remark 2.8's general-block scaling. The unconditional M08
proof and this one agree clause by clause at r = 0 ((GR-B)'s order-1
instance is proved, (FRESH)'s order-1 instance is proved). ∎

## 7. OL-D (open) and the representative-independence remark

OL-D (per-row T-counts at the BUILT tables) remains the table-build
officialization: for each (e, τ, o) row, the one-window transition count
from a fixed representative is one polynomial of degree ≤ W_loc, ℕ-valued
at every pool. The order-r analogue of M08 Remark 2.7 now reads: given
(GR-B), a one-window count from ANY representative of t has the CEN-J
shape, and Lemma C makes the count independent of the representative's
fixed residues (they enter only as fixed nonzero ν-arguments and junction
pins). Officialization waits on the table build fixing the windows; the
degree-≤-W_loc clause is the W-ledger's definition of W_loc.

## 8. Assembly to cl6 (the Lean row)

M08 Lemma 1 (proved): cl6 at any pack ⟺ (H_T) ∧ (H_S). CEN-J supplies both
laws for order-(r+1) cells at every r once the pack's cells match the §2
datum shape (OL-A's "matching cellLvl/cellInst" clause = the table-build
side of OL-D): countS := the honest census polynomial q^{E″}·∏M_λ(X^d)
(0 on empty fibers, per the n = 2 padding discipline), countT := the
one-window polynomial of §7. Residues to a full cl6 discharge: (GR-B),
(FRESH), the OL-D officialization, and the pack construction itself.

## 9. Consumption and residue table

| consumer / tree row | served by | residue |
|---|---|---|
| O-9 OL-A | A1/TRI/LED proved; digit clause = (GR-B); (DET) proved; (FRESH) displayed | (GR-B) ≥ 2; (FRESH) deep = GD-2/CU-1 layer |
| O-9 OL-B | RE-POINTED at GD-3 (tree D2.2 row executed); GD23 GD3-FULL+OL-B | (GR-B) |
| O-9 OL-C | CEN-W/CEN-J + TYPE-MARCH + JUNCTION-PIN | (GR-B) + (FRESH) |
| O-9 OL-D | §7 remark, conditional | table build |
| M08 §3 assembly | §8 via Lemma 1 | pack build |
| GD-3 full-form value-side consumption (D2.2) | this unit is the named consumer; TYPE-MARCH shows WHY the full form (march incl.) is what the value side needs | — |
| tree O-9 node display | INDEX FLAG §1 (f̄_r vs d) — recorded correction | DELTA-3 line |

Arbitrary-DVR scope: Route G unconditional at the intended pools; Route W
inherits GD23's (KP)/TIE conditionality. No new axiom, no new literature
pull beyond the LITUNIT pins.

## 10. Falsifier record (falsifier-first; run before §§2–6 were finalized)

`verification/openmath/o9_order2_census_check.py` — M08's proposed T6,
executed as an extension of the depth-3 harness's coherent anchored-march
reader. Full enumeration of coefficient boxes (plus valuation-restricted
supersets, poolable because a stratum's census is superset-independent);
per box: level-1 stratum classification, then per repeated residual factor
the order-2 window read; censuses tabulated by discrete stratum key under
the (DET) fence. Checks: K1 = level-1 census equals M08 Thm 2 exactly
(regression); K2 = refined census identical across parent realizations of
one discrete shape (the (FRESH)/OL-B shadow); K3 = census/∏M_λ'(p^g)
type-vector-independent per child polygon (the CEN product law, per p);
K4 = the normalized census fits ONE exponent vector in the atoms
{p, p^g − 1, p − 1} across all primes at fixed (n, M) (the cross-p
polynomiality; any M08-§2.5 character dependence kills it); T2 = principal
part length = μ (the pinned Lemma 2.17(2), per instance).

RUN (2026-08-01, log `verification/openmath/logs/`): 10 configurations —
full enumeration (p,n,M) ∈ {2,3}×{(3,5),(4,4),(4,3)} ∪ {(5,4,3)};
restricted (5,3,5) at mins (3,2,1) and (2/3,4,6) at mins (4,3,2,1) (the
g = 2 design: order-2 residuals over F_{p²}) — 8,220,994 boxes,
1,128,288 order-2 instances, 100 K1 stratum rows, 18 cross-p census cells
(one at g = 2). RESULT: **0 violations on every check**; fitted spectrum
all pure q-powers times ∏M (ε = 0 throughout — JUNCTION-PIN confirmed at
the tested perimeter). Any single K4 hit would have refuted OL-C before it
was written up.

Coverage honesty: child residual types of degree ≥ 2 (where the character
phenomenon lives) are exercised at p ∈ {2, 3} (the (n,M) = (4,4) configs;
9 mod-4-sensitive cells) but not yet at p = 5 (the needed restricted run
(5,4,4) at mins (2,2,1,1), 5^10 boxes, ships behind the `slow` flag);
g = 2 cells have trivial types (degree-1 child residuals) — a d₁ ≥ 2,
g ≥ 2 census cell needs M = 7-scale runs (proposed, not run). Depth-3
(order-3 census) untested. The march itself at g ≥ 2 is separately covered
by the depth-3 harness's 470,736-instance run (CU-1's gate).

## 11. Attack list for the hostile pass

1. TRI's induction: is (P2) (Prop 2.7(3)) being applied at the right index
   at every level, and is the (P1) rescaling composition (e_r·wt_r = wt)
   legitimate for the monomials themselves?
2. §5.1's LINE clause: does (GR-B)(2′) really force R^{gr}(in a) constant
   for deg a < m (the "development of a is a itself" step) — or does that
   need an extra degree lemma? (GMN Lemma 2.2(2) is the fallback pin.)
3. The ε(D) dichotomy and JUNCTION-PIN: is the right-end pin correctly
   attributed to (FRESH)/VTX, and is the harness's ε = 0 finding forced by
   the theorem or by the tested strata's shape?
4. (DET): is the displayed formula really sufficient (check the vertex
   digit reads at β = eN − 1 and the left-tail cutoff against Def 1.8's
   −∞ convention)?
5. TYPE-MARCH: verify the F₃ counterexample and that (GR-B)(2′)'s stride
   clause gives exponents AFFINE in κ (not just monotone).
6. The K4 atom set {p, p^g−1, p−1}: could a genuine census produce atoms
   outside it (e.g. p² + p + 1 from a norm-type aggregation) that the
   harness would mis-flag — or, worse, that the exponent search could
   accidentally fit at small primes?
7. The INDEX FLAG: confirm d = f₀⋯f_r against GMN §2.1 and Def 2.21 (and
   that M08 §3's f̄_r display is indeed off by one, not this brief).

— O9 Phase-B rev 0. Verdict: PARTIAL — the order-r census REDUCED to
(GR-B) + (FRESH), both pre-existing named opens; the reduction's own
mathematics (A1/TRI/LED/(DET)/TYPE-MARCH/CEN-W/CEN-J assembly) proved
above; r = 0 = M08 Thm 2 recovered; falsifier run clean at 1.13M
order-2 instances.
