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
  surjectivity clause; not load-bearing — see §5.3).
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

    #window stratum in (O/π^N)-coordinates = q^{E′(D,N)} · ∏_S M_{λ_S}(q^d),

with M_λ the M08 Lemma-B type-count polynomial, evaluated at q^d, and

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
independence) and K4 (cross-p atom fit), 1,127,286 order-2 instances, 0
violations (§10).
