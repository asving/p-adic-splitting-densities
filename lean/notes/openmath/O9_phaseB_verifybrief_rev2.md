# O9 — the order-r stratum census (CL-6 at OM order ≥ 2) — Phase-B verify brief REV 2 (Fable, 2026-07-31)

You are verifying a mathematics note. Quote each offending passage and
classify it as *critical error* (breaks the logical chain) or *justification
gap* (assume and continue); fix nothing. This is REV 2, repairing the pass-1
hostile verification (`O9_pass1_verify.md`, fresh context, 2026-07-31: NOT
ACCEPTED — 2 critical, 3 gaps) of rev 0 (`O9_phaseB_verifybrief.md`). Pass 1
explicitly CONFIRMED: TYPE-MARCH + its F₃ countermodel, Lemmas A1/TRI/LED,
(DET) sufficiency (both adversarial corners), §5.1 fiber uniformity, §6.2's
F_{q^d} import, the CEN-W assembly spot-check, the INDEX FLAG, and — the
charge's central question — that the window layer consumes NO open input
beyond (GR-B) ("Window-layer conditionality audit: CLEAN"). Everything
confirmed is carried **byte-stable**: §§1, 3, 4 (A1/ledger/TRI/LED), 5.1,
5.2, 5.3, 6.1, 6.2, 7, 8 are verbatim rev 0 except for explicitly marked
*rev-2 appended notes* (no statement or proof text touched). The repairs
live in §0, §2, §4 (one appended lemma), §5.4, §6.3, §6.4, §10, §11.

## 0-pre. Rev-2 changelog (pass-1 findings → dispositions → repair sites)

| pass-1 finding | class | disposition | repair site |
|---|---|---|---|
| C1: E′'s left-tail β_k used ⌈line⌉, which is non-strict at integral extended-line abscissas (every k < k₀ with e₁ \| (k₀−k)); machine-refuted 256 vs 64; overcount q^d per such slot | CRITICAL | **REPAIRED** — strict threshold ⌊line⌋+1 at all strictly-above slots (= ⌈line⌉ at non-integral values, so within-face slots unchanged); (DET) still suffices (⌊L⌋+1 ≤ L+1 ≤ eN); NEW falsifier K5 *predicts* censuses from the repaired ledger formula and passes on every case incl. the verifier's countermodel (64 exact) and refutes the rev-0 formula at every integral-left-tail case | §2 (the (STRICT) display); §6.3; §10 K5 |
| C1 downstream (b): does M08 Thm 2 share the bug? | — | **RESOLVED: NO** — M08's printed datum is a full polygon from (0, y₀) (no left tail exists in its statement), and the harness's level-1 keying drops every box with v(a_0) ≥ M (`parent_data`, o9_order2_census_check.py lines 121–124), so K1 never keyed a left-tail stratum. The rev-0 E′ display was the sole bug site; "r = 0 IS M08 Thm 2" is rescoped to k₀ = 0 data (which is all M08 states) | §6.4 |
| C2: JUNCTION-PIN carried a PROVED label with no derivation; §5.4 files it as a clause of the OPEN (FRESH) | CRITICAL | **REPAIRED (honest rescope)** — the PROVED label is WITHDRAWN. The pin is now (FRESH)(c), displayed OPEN beyond order 1; what IS proved given the clause is its telescope consequence (exactly ∏M, no stray (q^d−1): Lemma D pinned-end + Lemma C). CEN-J's conditionality "(GR-B)+(FRESH)" is unchanged (the pin was always ⊂ (FRESH)); only the accounting was wrong. A mechanism note (labeled NOT-A-PROOF) records why (GR-B)(3)+(4)+(P4) make the pin the expected VTX transport | §0 table; §5.4 |
| G3: attainment of on-line β_k assumed; formula positive on empty strata | GAP | **REPAIRED** — new hypothesis **(ADM)** (ledger-admissibility: every on-line β_k mod e ∈ {wt(𝐣) mod e}) added to CEN-W/CEN-J; proved AUTOMATIC at orders ≤ 1 (r = 0: e = 1; r = 1: wt ≡ j₁h₁ mod e₁, gcd(h₁,e₁) = 1); unattained-vertex data have census 0 (the §8 padding value); general-order coverage left explicitly open (a p-free per-datum decidable) | §2 |
| G4: E″ undisplayed (circularity risk); monic-top box vs free W_N box unreconciled; "a_ℓ monic iff m\|n" false as written | GAP | **REPAIRED** — (a) E″ now has a DISPLAYED closed form (E″) with one named ingredient, the (FRESH)(a′) transported floors g_k; validated exactly = Σ(N−c_i) against M08's printed formula at r = 0 (§6.4 step 5); (b) CEN-W restated over TWO explicit boxes (free / monic-top), E′ summed over K_D which drops the pinned top slot; the m ∤ n coset top is handled by NEW Lemma LED-top and consumed only through CEN-J's ρ-pinned end; (c) slip fixed: a_ℓ is monic of degree n − ℓm; a_ℓ = 1 iff m \| n | §2; §4 LED-top; §6.4 |
| G5: falsifier scope — K1–K4 fit censuses, never evaluate E′ (how C1 survived a clean run); K4 underdetermined at p ∈ {2,3} deg-≥2 cells; "JUNCTION-PIN confirmed" non-discriminating | GAP | **REPAIRED (disclosure + new check)** — §10 rewritten: the form/value distinction is explicit; NEW check K5 (predict-from-ledger, r = 0, 7 data × all types, ALL PASS; rev-0 formula refuted at every integral-left-tail case); K4's two-points-vs-three-atoms underdetermination stated in the headline, (5,4,4) run queued; ε = 0 restated as shape-forced at every tested cell (non-discriminating for (FRESH)(c)), the discriminating free-end CEN-J cell queued | §10 |

Statement-change disclosure (per the repo statement-fence): CEN-W, CEN-J,
and (FRESH) are restated in this rev — CEN-W/CEN-J gain the (ADM)
hypothesis, explicit boxes, and the strict thresholds; (FRESH) gains the
quantitative floor clause (a′) and absorbs JUNCTION-PIN as clause (c). All
three are THIS unit's own displays (introduced in rev 0, no external
consumer yet); the pass-1 verifier's charge demanded exactly these repairs.
No pinned literature statement and no imported theorem is touched.

## 0. Status table (the whole unit at a glance)

| item | statement | status here |
|---|---|---|
| OL-A(i) coordinates | φ-adic development is a level-compatible coordinate system | **PROVED** (Lemma A1; any O) |
| OL-A(ii) triangularity + ledger counts | v_{r+1} is slot-triangular on deg < m; valuation-condition counts are pure q-powers with p-free exponents | **PROVED** (Lemmas TRI, LED, LED-top); Route G = GMN scope via pinned Prop 2.7/Lemma 2.2(2); Route W = any O, conditional on GD23's (V1)+(KP) beyond order 1 |
| OL-A(iii) line/digit structure | graded digit reads are per-slot F_{q^d}-bijections | = **GD-3/OL-B**, consumed not re-proved; order 1 PROVED (GD23 RES-1); orders ≥ 2 = (GR-B) [OPEN there] |
| OL-A(iv) determinacy + stacking | (DET) working-level formula PROVED (window); the joint-with-parent freshness clause (FRESH) displayed, order-1 instance proved, deep = GD-2/CL-13 territory | **PARTIAL** (§5) |
| (ADM) admissibility | every on-line lattice slot's β_k is ledger-attained (β_k mod e ∈ wt-classes) | **HYPOTHESIS** on the datum (rev 2): automatic at orders ≤ 1 (proved, §2); general order = a p-free, per-datum decidable, left open |
| OL-B | twisted residues / exponent-map audit | **RE-POINTED at GD-3** (executes the tree's D2.2 row); nothing owed here beyond (GR-B) |
| OL-C | the order-(r+1) census formula | **PROVED conditional on (GR-B) + (FRESH), under (ADM)** (Theorem CEN-W from (GR-B)+(ADM) alone; CEN-J adds (FRESH)); r = 0 instance on k₀ = 0 data = M08 Thm 2, unconditional |
| TYPE-MARCH | the anchored march preserves factorization types | **PROVED** (new, one page; the V26-2 lesson made load-bearing) |
| (FRESH)(c) = the junction pin | the window chain's right-end read is, conditioned on ρ, a ρ-determined nonzero constant | **OPEN — a clause of (FRESH)** (rev 2: the rev-0 PROVED label is withdrawn; pass-1 CRITICAL 2). Given the clause, the telescope consequence — exactly ∏M, no stray (q^d−1) — is PROVED (Lemma D pinned-end + Lemma C). Order-1 instance proved with (FRESH)'s. Measured ε = 0 on 18 cross-p cells is consistent but NON-discriminating (§10) |
| OL-D | per-row T-counts at the built tables | **OPEN** (officialization; the order-r Remark-2.7 analogue displayed, (GR-B)-conditional) |
| falsifier | order-2 census harness (K1–K4, T2) + rev-2 K5 (predict-from-ledger, r = 0) | RUN: 0 violations / ALL PASS; scope split (form vs value) displayed; §10 |

Honest headline: **the order-r census is REDUCED to exactly two named open
inputs — (GR-B) (GD-3's package, already the GD campaign's residue) and
(FRESH) (the GD-2/CL-13 vertex-law layer at deep states, junction pin
included, already CU-1's step content) — plus the per-datum lattice
hypothesis (ADM) (automatic at orders ≤ 1; decidable from the type's
lattice data per cell, not a research-open input). No research-open input
is new to this unit.** Everything else is proved below; the r = 0 instance
on k₀ = 0 data recovers M08 Theorem 2 exactly, and the repaired ledger
formula now PREDICTS brute-force censuses (K5, §10).

## 1. Setting, indexing, and the pinned imports

[Byte-stable = rev 0 §1 verbatim.]

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

## 2. The stratum datum and the two census statements (REPAIRED)

Fix a type t of order r, a representative φ, a monic f ∈ O[x] of degree n,
and the working level N. Write the φ-adic development

    f = Σ_{k=0}^{ℓ} a_k φ^k,   deg a_k < m,   ℓ := ⌊n/m⌋,
    a_ℓ monic of degree m′ := n − ℓm  (so a_ℓ = 1 iff m | n),
    a_k for k < ℓ ranging over {deg < m}          [rev-2 fix of G4(c)]

and the order-(r+1) polygon heights u_k := w(a_k) + k·V̂ (GMN Def 2.3 via
(P2)/(P3); the principal part N^−_{r+1}(f) is the negative-slope part of the
lower hull of {(k, u_k)}, slope-−∞ side included, per Def 1.8).

**Definition (level-N stratum datum D over t).** [Unchanged from rev 0.]
D consists of:

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

**The per-slot thresholds (REPAIRED — pass-1 CRITICAL 1).** In a_k-coordinate
w-units (u_k = w(a_k) + kV̂, and kV̂ ∈ ℤ throughout), the stratum's per-slot
conditions and thresholds are:

    STRICT slots (left tail k < k₀ against the extended face-1 line, and
    off-line k ∈ [k₀, k_s] against the local face line; L_k := that line's
    value at k, so the condition is w(a_k) > L_k − kV̂):
        β_k := ⌊L_k⌋ + 1 − k·V̂                                    (STRICT)
    ON-LINE lattice slots (k = k_{S−1} + j·e_S; line value integral):
        β_k := L_k − k·V̂,  condition w(a_k) ≥ β_k + digit read at β_k
                                                                   (READ)
    RIGHT-TAIL slots k > k_s (non-strict):
        β_k := U_s − k·V̂,  condition w(a_k) ≥ β_k                  (TAIL)

*Repair note.* At non-integral L_k, ⌊L_k⌋ + 1 = ⌈L_k⌉, so (STRICT) agrees
with rev 0's ⌈·⌉ at every off-line slot within a face (slope −h_S/e_S in
lowest terms ⟹ non-lattice line values non-integral — the §5.2 argument,
which pass 1 verified *within faces*). At the LEFT TAIL the extended face-1
line takes the INTEGER value U₀ + ((k₀−k)/e₁)h₁ whenever e₁ | (k₀ − k) —
every k < k₀ when e₁ = 1 — and there rev 0's ⌈L⌉ counted u_k ≥ L: it
admitted tuples whose face 1 extends to a left endpoint at k, which under
this datum's own keying is a DIFFERENT stratum (larger d(1)). Machine
countermodel (pass 1, reproduced as K5 case 1): r = 0, q = 2, N = 4,
D = (2,1)→(3,0), rev-0 formula 256 vs truth 64; the strict thresholds give
64 exactly. (DET) still suffices for (STRICT): ⌊L_k⌋ + 1 − kV̂ ≤
(L_k − kV̂) + 1 ≤ eN, within LED(i)'s inequality scope (§5.2 rev-2 note).

**(ADM) — ledger admissibility (NEW hypothesis; pass-1 GAP 3).** Say D is
*ledger-admissible* if every on-line lattice slot's β_k is attained by the
slot ledger: β_k mod e ∈ {wt(𝐣) mod e : 𝐣 a ledger index} — equivalently
G_{β_k} ≠ 0 (LED(iii)). This is a p-free lattice condition on D, decidable
from the type's lattice data. Facts:

* By TRI, the w-values attained on {deg < m} \ {0} are exactly
  {e·v + wt(𝐣) : v ≥ 0}, i.e. the classes {wt(𝐣) mod e} and nothing else.
  Hence an UNATTAINED VERTEX β_k empties the stratum (a nonzero vertex
  digit needs w(a_k) = β_k): census = 0, the §8 padding value — while the
  rev-0 display was positive there (the refuted overcount's cousin). An
  unattained INTERIOR on-line slot forces its digit to 0 (the slot behaves
  as strictly-above; the displayed formula's −d and its digit index would
  have to be dropped — that variant is NOT displayed here).
* (ADM) is AUTOMATIC at orders ≤ 1. r = 0: e = 1, every class attained.
  r = 1: e = e₁ and wt(𝐣) = j₀·0 + j₁·w(φ₁) with w(φ₁) ≡ h₁ (mod e₁) by
  the (P3) V-recursion (v₂(φ₁) = e₁V₁ + h₁, V₁ = 0); j₁ ranges over
  0..e₁f₁−1 ⊇ e₁ consecutive values and gcd(h₁, e₁) = 1, so {j₁h₁ mod e₁}
  is everything.
* General order: expected always to hold by the same V-recursion residue
  mechanism (corroborated by (P5)'s "any admissible weight" scope), but NOT
  proved here — (ADM) is carried as an explicit hypothesis; consumers (§8)
  evaluate it per constructed cell.

**(DET) — the level-N determinacy condition (proved sufficient, §5.2):**

    max_{0 ≤ k ≤ ℓ}  ( line_D(k) − k·V̂ )  ≤  e·N − 1,            (DET)

where line_D(k) := max over faces of the extended face line's value at k.
Under (DET) every stratum condition is determined by f mod π^N (Lemma LED
(iii); (STRICT) thresholds included, per the rev-2 note in §5.2), so the
census below is well-defined:

    C_{D,N}(t, ρ) := #{ f mod π^N : f in the stratum (D over the parent
                        realization ρ) },

where ρ = a concrete realization of the tower through order r (the fixed
concrete φ_i, ψ_i, and the parent stratum data that produced t).

**The two coordinate boxes (REPAIRED — pass-1 GAP 4(b)).** The window
statements live on explicit boxes of development coordinates:

* the FREE box: (a_0, …, a_ℓ) ∈ W_N^{ℓ+1} (every slot a full deg-< m box;
  the pure window object, no monicity);
* the MONIC-TOP box (requires m | n, k_s = ℓ, U_s = ℓV̂): (a_0, …, a_{ℓ−1})
  ∈ W_N^ℓ and a_ℓ = 1 (so slot ℓ carries no choices and its read is the
  constant 1 ≠ 0);
* the m ∤ n monic-coset top (a_ℓ ∈ B_{𝐣*} + W′_N, deg B_{𝐣*} = m′) is
  covered by Lemma LED-top (§4) and consumed only through CEN-J, where the
  chain's right end is ρ-pinned (§6.4) — it is NOT a CEN-W branch here.

Write K_D := {0, …, ℓ} for the free box and {0, …, ℓ−1} for the monic-top
box, and L := #{on-line lattice slots in K_D}.

**Theorem CEN-W (window census; conditional on (GR-B) at order r+1; D
ledger-admissible (ADM)).** For the WINDOW-ONLY stratum — the conditions of
D imposed on the development coordinates (a_k), the frame φ fixed, no
parent-membership conditions — under (DET):

    free box:       #stratum = q^{E′(D,N)} · (q^d − 1) · ∏_S M_{λ_S}(q^d)
                    [ε = 1: the right-end vertex read is a free unit]
    monic-top box:  #stratum = q^{E′(D,N)} · ∏_S M_{λ_S}(q^d)
                    [ε = 0: the right-end read is the constant 1 — the
                    window-internal instance of the junction pin]

with, in both cases (β_k the REPAIRED thresholds above, over the box's K_D),

    E′(D,N) = Σ_{k ∈ K_D} [ m·N − s(β_k) ] − d·L,
    s(β) := Σ_{𝐣} max(0, ⌈(β − wt(𝐣))/e⌉),

where 𝐣 runs over the m slot monomials of the ledger (§4) and wt(𝐣) their
w-weights. M_λ is the M08 Lemma-B type-count polynomial, evaluated at q^d.
One ℕ-valued polynomial in q; independent of p, O, δ, and of ρ. At r = 0,
on k₀ = 0 data, the monic-top branch IS M08 Theorem 2 (E′ = f₀·Σ(N − c_i)
with M08's c_i; §6.4).

**Theorem CEN-J (joint census; conditional on (GR-B) + (FRESH), under
(ADM)).** Under (DET) additionally over the parent's own reads: for every
realization ρ of the parent tower (level-N₀ conditions, N₀ ≤ N),

    C_{D,N}(t, ρ) = (#parent-realization stratum at level N₀)
                      · q^{E″(D,N)} · ∏_S M_{λ_S}(q^d),

with the DISPLAYED exponent (pass-1 GAP 4(a) repair)

    E″(D,N) = n·(N − N₀) − Σ_{k ∈ K_D} max(0, s(β_k) − s(g_k)) − d·L′, (E″)

where: K_D and β_k are as in CEN-W over the monic-adjusted box (at an
m ∤ n coset top, s(·) is replaced at that slot by LED-top's sub-ledger
count s′(·)); g_k = g_k(discrete parent shape) are the parent-transported
floors — the minimal w(a_k) forced by ρ's conditions, supplied by
(FRESH)(a′) below, with g_k ≤ β_k at on-line slots (else the stratum is
empty and both sides are 0); and L′ := L − [k_s ∈ K_D] (the chain's
right-end read is ρ-pinned — (FRESH)(c) — hence charged to the parent, not
to the window; when the top is monic, k_s = ℓ ∉ K_D and the pin is the
monicity constant, so nothing is subtracted). In particular the refinement
factor is the SAME for every realization ρ of the same discrete parent
shape and is one displayed ℕ-valued polynomial in q. E″'s well-definedness
(existence and shape-only dependence of the floors g_k) is exactly
(FRESH)(a′)'s content — the formula is displayed, not circular, and its one
open ingredient is priced to the named open input. Rev-0's gloss "E″ = E′
minus the exponent already charged by the parent" survives as a remark, not
a definition. Falsifier: harness checks K2/K4 (§10) plus the r = 0
validation E″ = Σ_i(N − c_i) against M08's printed formula (§6.4 step 5).

## 3. The valuation layer: two routes (mirrors GD23's Route A/B split)

[Byte-stable = rev 0 §3 verbatim.]

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

[Byte-stable = rev 0 §4 verbatim, with ONE appended rev-2 lemma (LED-top)
after Lemma LED; A1/ledger/TRI/LED statements and proofs untouched.]

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

**Lemma LED-top (the monic-coset top slot; rev-2 addition, pass-1 GAP
4(b)).** Suppose m′ := n − ℓm ∈ (0, m) (the m ∤ n case), and let a range
over the monic coset box a ∈ B_{𝐣*} + W′_N, where 𝐣* is the unique ledger
index with deg B_{𝐣*} = m′ and W′ := {b : deg b < m′} (this coset equals
{monic, deg = m′} + π-adic truncation: x^{m′} − B_{𝐣*} has degree < m′, so
the two cosets coincide; the sub-radix monomials of degree < m′ are an
O-basis of W′ by A1). Write w* := wt(𝐣*) and
s′(β) := Σ_{deg 𝐣 < m′} max(0, ⌈(β − wt(𝐣))/e⌉). Then, by TRI applied to
the full coordinate vector (c_{𝐣*} = 1, plus b's coordinates):

* (i) [anchor cap] w(a) = min(w*, w(b)) ≤ w* always; for β ≤ min(w*, eN):
  #{a in the coset box : w(a) ≥ β} = q^{m′N − s′(β)}; for β > w* the count
  is 0.
* (ii) [below the anchor] for β < w*, β ≤ eN − 1: the graded read on the
  coset is r_β(a) = r_β(b) — §5.1 applies verbatim on the sub-ledger
  (fiber-uniform onto F_{r+1} iff β is attained in the SUB-ledger).
* (iii) [at the anchor] at β = w* ≤ eN − 1: w(a) = w* forces
  r_{w*}(a) = c(B_{𝐣*}) + r_{w*}(b), an affine function of b with constant
  part c(B_{𝐣*}) ≠ 0; its value set is the coset c(B_{𝐣*}) + V, V :=
  r_{w*}(W′) an F_q-subspace of F_{r+1} of dimension s′(w*+1) − s′(w*), and
  0 ∉ c(B_{𝐣*}) + V (the same-class ledger in-forms are F_q-independent —
  LED(iii) for the FULL ledger — so c(B_{𝐣*}) ∉ V; consistently, TRI's
  equality already forbids w(a) > w*). The read is uniform on its value
  coset: q^{m′N − s′(w*) − dim_{F_q} V} per attained value.

*Proof.* All three are TRI + the LED counting on the sub-ledger; (iii)'s
non-vanishing is the F_q-independence of {in(B_𝐣) : wt in the class of w*}
inside G_{w*}, which is LED(iii)'s dimension count. ∎ *Consumption note:*
the top slot's read is NOT F_{r+1}-fiber-uniform in general ((iii) is a
proper subspace coset when the sub-ledger misses classes); CEN-W therefore
does NOT get an m ∤ n branch. CEN-J consumes only (i)+(ii) for the ledger
charges, plus (iii)'s non-vanishing: there the chain's right-end read is a
ρ-determined CONSTANT ((FRESH)(c)), and Lemma C makes the pin's value
irrelevant — only nonvanishing and fixedness enter (§6.4).

## 5. OL-A(iii)(iv): the digit reads, (DET), and (FRESH)

### 5.1 The digit read is a fiber-uniform F_q-linear surjection [(GR-B)]

[Byte-stable = rev 0 §5.1 verbatim.]

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

[Byte-stable = rev 0 §5.2 verbatim + one appended rev-2 note.]

Under (DET) (§2), every per-coordinate condition of the stratum has
β_k ≤ eN (inequality conditions) or β_k ≤ eN − 1 (exact + digit read at
on-line lattice slots), so by LED(i) the stratum is a well-defined subset
of the level-N boxes. The non-lattice abscissas of a face carry
non-integral line values (slope −h_S/e_S in lowest terms), so the ceiling
⌈line − kV̂⌉ implements "strictly above" exactly as M08's c_i convention;
interior lattice slots stay free (their zero digit class = strictly above);
vertex nonvanishing is forced by the types (R_λ has exact degree d(S) and
nonzero constant term — M08 §2.1's note, verbatim at order r+1). ∎

*Rev-2 note (scope of the ⌈·⌉ claim; pass-1 CRITICAL 1).* The paragraph
above is correct exactly as scoped: WITHIN a face's span. Rev 0 silently
extended the ⌈·⌉ convention to the left tail, where extended-line values
CAN be integral and ⌈·⌉ then implements ≥, not >. The repaired thresholds
(§2, (STRICT)) use ⌊L⌋ + 1 at every strictly-above slot — equal to ⌈L⌉
precisely where this paragraph applies, strictly larger at integral
left-tail values. Well-definedness under (DET): a (STRICT) threshold obeys
β_k = ⌊L_k − kV̂⌋ + 1 ≤ (eN − 1) + 1 = eN, inside LED(i)'s inequality
scope; reads still need (and have) β_k ≤ eN − 1.

### 5.3 The census key must be level-determined — two compiled traps

[Byte-stable = rev 0 §5.3 verbatim.]

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
(REWRITTEN in rev 2: quantitative floors added, JUNCTION-PIN refiled as
clause (c) with its rev-0 PROVED label WITHDRAWN — pass-1 CRITICAL 2)

**(FRESH).** For every realization ρ of the parent tower (level-N₀
conditions, N₀ ≤ N), conditioned on ρ:

* **(a′) [transported floors — quantitative form of rev-0 (a)]** the
  parent's conditions, rewritten in the window coordinates (a_k) via A1,
  amount to per-slot valuation floors w(a_k) ≥ g_k together with the
  clause-(c) pin, where (g_k) is a function of the DISCRETE parent shape
  only (the WGEO/VTX transported pins). Rev-0 (a)'s "the window's
  below-line height conditions hold automatically" is the special case
  g_k ≥ β_k at those slots (the slot then charges nothing — the max(0, ·)
  in (E″)).
* **(b) [fresh reads]** each on-line window read of §5.1 is, on the
  ρ-fiber, an affine function of one fresh digit with unit slope, jointly
  independent across the on-line slots — so the joint census factors as
  (#ρ-fiber)·(the window factors).
* **(c) [the junction pin — rev-0's "JUNCTION-PIN", now correctly filed]**
  the digit read at the window chain's right end (the first-min-attainment
  slot k_s = ω_{r+1}; (P4)) is a ρ-determined nonzero CONSTANT (the
  transported anchor/VTX read), not a free unit.

Status: order-1 instance PROVED (it is M08 §2.2's separation together with
the KEY1 standard-lift shape; the Lean order-≤1 twin is the CL-13/LVL-DET
layer); general order = the GD-2 vertex-law layer at deep states — EXACTLY
CU-1's step content, not a new obligation of this unit. Falsifier: check K2
below (realization independence; 1,128,288 order-2 instances, 0
violations) — supporting evidence, NOT proof.

**Consequence of (c), PROVED given the clause:** the vertex chain
telescopes to exactly ∏_S M_{λ_S}(q^d) with NO stray (q^d − 1) factor
(Lemma D with pinned end; Lemma C makes the pin's value irrelevant — only
its nonvanishing and fixedness enter). In the window-only theorem (no ρ),
the free box leaves the right end a free unit and the factor (q^d − 1)
appears; the monic-top box pins it by monicity — the ε dichotomy in CEN-W.

**Mechanism note for (c) — NOT A PROOF (recorded so the open step is
named).** By (P4), k_s = ω_{r+1}(f) = ord_{ψ_r}(R_r(f)); on the ρ-fiber the
parent's residual data fixes the ψ_r-cofactor class of R_r(f) at the
marked root, and (GR-B)(3)+(4) identify the window's k_s-read with that
cofactor value up to march normalizers. The missing step — transporting
this graded-level identification to the finite-level digit read at working
level N — is precisely the GD-2/VTX vertex law, i.e. (c) is genuinely a
clause of (FRESH), not a corollary of (GR-B). Rev 0's status table asserted
(c) PROVED from (GR-B)(2′)+(3); no such derivation existed (pass-1
CRITICAL 2) and the label is withdrawn. The measured ε = 0 on 18 cross-p
cells is consistent with (c) but non-discriminating (§10).

## 6. OL-C: the census proof

### 6.1 Lemma TYPE-MARCH (new; why the march makes the census polynomial)

[Byte-stable = rev 0 §6.1 verbatim.]

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

[Byte-stable = rev 0 §6.2 verbatim.]

M08 Lemma B (M_λ ∈ ℚ[X], M_λ(Q) counts monic type-λ polynomials with
nonzero constant term over F_Q), Lemma C (end-pinned counts are ratio-class
functions ν_λ with Σ_t ν_λ(t) = M_λ(Q)), and Lemma D (the vertex-chain
telescope) are statements about an ABSTRACT finite field F_Q: their M08
proofs use only |F_Q| = Q and the F_Q^×-scaling action. Import them at
Q = q^d. Note M_λ(q^d) = (M_λ ∘ X^d)(q): still ONE polynomial in q.

### 6.3 Proof of Theorem CEN-W (and the ε dichotomy) — REPAIRED

By A1 the window stratum is a condition set on the coordinates (a_k),
separately per k, over the declared box (§2). Per abscissa k ∈ K_D:

* right-tail, left-tail, and off-line slots contribute the LED(ii)
  q-powers q^{mN − s(β_k)} at the REPAIRED thresholds of §2. The (STRICT)
  ⌊L⌋+1 thresholds implement u_k > line exactly at EVERY strictly-above
  slot: at integral left-tail values the rev-0 ⌈L⌉ counted u_k ≥ line,
  i.e. admitted tuples whose face 1 extends to a left endpoint at k — a
  different stratum under §2's keying (pass-1 countermodel: 256 vs 64;
  repaired formula machine-verified, K5). Within faces ⌊L⌋+1 = ⌈L⌉ (§5.2).
* each on-line lattice slot contributes, per prescribed digit
  z ∈ F_{r+1}, exactly q^{mN − s(β_k) − d} (§5.1 fiber uniformity —
  z-independent; the surjectivity behind it needs β_k attained, which is
  (ADM) + (GR-B)).
* in the monic-top box, slot ℓ carries no choices and its read is the
  constant 1 ≠ 0 (it is excluded from K_D and from L).

Summing over the digit vectors compatible with the polygon and the types:

    #window = q^{E′(D,N)} · Z_D,   Z_D := #{ digit vectors : vertex digits
              ≠ 0, type(face S) = λ_S for all S }

where the type of a face's digit vector is read through TYPE-MARCH (§6.1)
as the type of the corresponding R_λ — the (GR-B) dictionary. Z_D is now
verbatim M08 §2.6 over F_{q^d}: group interior slots per face (Lemma C),
telescope across the shared vertices (Lemma D). Free box: the right-end
vertex digit is a free unit and Z_D = (q^d − 1)·∏_S M_{λ_S}(q^d) (ε = 1).
Monic-top box: the end is pinned to the constant 1 and Z_D =
∏_S M_{λ_S}(q^d) exactly (ε = 0). ℕ-valued, p/O/δ-free: all exponents are
ledger data (LED(ii)), M_λ by Lemma B. ∎

### 6.4 Proof of Theorem CEN-J, the (E″) validation, and the r = 0
cross-check — REPAIRED

Condition on ρ. Five steps; (GR-B) + (FRESH) assumed, D ledger-admissible.

1. **(lift)** The parent's conditions are determined by f mod π^{N₀}
   ((DET) over the parent's own reads, the theorem's standing hypothesis).
   Monic degree-n f mod π^N has n free coefficient coordinates, so
   #{ρ-fiber at level N} = (#parent stratum at level N₀) · q^{n(N − N₀)}.
2. **(floors)** By (FRESH)(a′), on the fiber the parent's conditions in
   window coordinates are exactly the per-slot floors w(a_k) ≥ g_k plus
   the clause-(c) pin — a product box. The window's height conditions
   therefore charge, per slot k ∈ K_D, the relative LED factor
   q^{−max(0, s(β_k) − s(g_k))} (LED(ii); LED-top(i) with s′ at an m ∤ n
   coset top; slots with g_k ≥ β_k charge nothing — rev-0 (a)'s
   "automatic" clause).
3. **(reads)** By (FRESH)(b) each on-line read in K_D except the chain's
   right end is fresh-digit affine with unit slope, so per prescribed
   digit it charges q^{−d}, uniformly and jointly independently (§5.1 on
   the fiber; surjectivity = (ADM) + (GR-B)); there are L′ = L − [k_s ∈ K_D]
   of them. By (FRESH)(c) the chain's right-end read is a ρ-determined
   nonzero constant — charged to the parent, nothing here (when the top is
   monic the pin is the monicity constant, same accounting).
4. **(telescope)** Summing over digit vectors compatible with the types
   (TYPE-MARCH dictionary as in §6.3): Lemma C + Lemma D with PINNED end
   give exactly ∏_S M_{λ_S}(q^d), no stray (q^d − 1); Lemma C makes the
   pin's value irrelevant — only its nonvanishing and fixedness enter.
5. **(assembly)** Multiplying: C_{D,N}(t, ρ) = (#parent at N₀) ·
   q^{n(N−N₀) − Σ_{k∈K_D} max(0, s(β_k) − s(g_k)) − d·L′} · ∏M — the
   displayed (E″). ∎

**Validation of (E″) at r = 0 against M08's printed formula (pass-1 GAP
4(a)).** Take r = 0, f₀ = 1 (M08's x^e-block; Remark 2.8 scales to general
f₀): m = 1 = d = e, w = v_π, V̂ = 0, n = e = ℓ, monic top (K_D = {0..e−1},
k_s = e ∉ K_D so L′ = #lattice slots i < e). The parent IS the block
condition v(a_i) ≥ 1: N₀ = 1, #parent stratum at level 1 = 1, floors
g_k = 1. On M08's data (k₀ = 0, no left tail): a non-lattice slot i
charges s(β_i) − s(g_i) = ⌈Δ(i)⌉ − 1 = c_i − 1 (height only); a lattice
slot i charges (Δ(i) − 1) height + d·1 read = c_i − 1 (M08's
c_i = Δ(i) + 1, so the +1 IS the read charge). Hence, reads folded in,

    E″ = e(N−1) − Σ_{i<e}(c_i − 1)
       = eN − Σ_{i<e} c_i = Σ_{i<e}(N − c_i) = M08's E(D,N)  — exact,

and CEN-J's display is verbatim M08 Theorem 2 (with the general-f₀ Remark
2.8 scaling, q ↦ q^{f₀}). The unconditional M08 proof and this one agree
clause by clause at r = 0 ((GR-B)'s order-1 instance is proved, (FRESH)'s
order-1 instance is proved, (ADM) automatic).

**r = 0 scope of the regression (pass-1 C1 downstream (b), RESOLVED).**
"At r = 0 this IS M08 Theorem 2" holds on k₀ = 0 data — full polygons,
which is ALL that M08 Theorem 2 states (its Δ runs from (0, y₀); no left
tail exists in its datum) and all that the harness keys at level 1
(`parent_data` drops every box with v(a_0) ≥ M: o9_order2_census_check.py
lines 121–124 — checked at source for this rev). So M08 Thm 2 does NOT
share the rev-0 bug, and K1's clean run was consistent: the rev-0 E′
display was the sole bug site. r = 0 data with k₀ ≥ 1 (left-tail strata)
are NOT single M08 strata (they are deep-tail unions of full polygons);
the repaired CEN-W covers them directly and K5 verifies it exactly (§10).

## 7. OL-D (open) and the representative-independence remark

[Byte-stable = rev 0 §7 verbatim.]

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

[Byte-stable = rev 0 §8 verbatim.]

M08 Lemma 1 (proved): cl6 at any pack ⟺ (H_T) ∧ (H_S). CEN-J supplies both
laws for order-(r+1) cells at every r once the pack's cells match the §2
datum shape (OL-A's "matching cellLvl/cellInst" clause = the table-build
side of OL-D): countS := the honest census polynomial q^{E″}·∏M_λ(X^d)
(0 on empty fibers, per the n = 2 padding discipline), countT := the
one-window polynomial of §7. Residues to a full cl6 discharge: (GR-B),
(FRESH), the OL-D officialization, and the pack construction itself.

## 9. Consumption and residue table

[Rev 0 §9 with two marked edits: the OL-C row names (FRESH)(c) instead of
the withdrawn PROVED pin and adds (ADM); all other rows verbatim.]

| consumer / tree row | served by | residue |
|---|---|---|
| O-9 OL-A | A1/TRI/LED proved; digit clause = (GR-B); (DET) proved; (FRESH) displayed | (GR-B) ≥ 2; (FRESH) deep = GD-2/CU-1 layer |
| O-9 OL-B | RE-POINTED at GD-3 (tree D2.2 row executed); GD23 GD3-FULL+OL-B | (GR-B) |
| O-9 OL-C | CEN-W/CEN-J + TYPE-MARCH (the junction pin = (FRESH)(c), OPEN) | (GR-B) + (FRESH); (ADM) per cell [rev 2] |
| O-9 OL-D | §7 remark, conditional | table build |
| M08 §3 assembly | §8 via Lemma 1 | pack build |
| GD-3 full-form value-side consumption (D2.2) | this unit is the named consumer; TYPE-MARCH shows WHY the full form (march incl.) is what the value side needs | — |
| tree O-9 node display | INDEX FLAG §1 (f̄_r vs d) — recorded correction | DELTA-3 line |

Arbitrary-DVR scope: Route G unconditional at the intended pools; Route W
inherits GD23's (KP)/TIE conditionality. No new axiom, no new literature
pull beyond the LITUNIT pins.

## 10. Falsifier record (REV 2: form/value scope split + the new K5)

**Form vs value (pass-1 GAP 5(a), disclosed).** K1–K4 tabulate empirical
censuses and FIT exponent vectors; none evaluates the E′/E″ closed forms.
They certify the FORM claims (censuses are pure q-powers times ∏M with
p-free exponents; realization-independence; cross-p polynomiality) and are
SILENT on the VALUE claims (the displayed ledger formulas) — which is
exactly how rev 0's left-tail error survived a clean run. Rev 0's status
row conflated the two; this rev separates them: FORM = K1–K4 (clean),
VALUE = K5 (r = 0, clean) + a queued order-2 predictor (evaluate E′/E″
from the ledger, compare to tabulation).

`verification/openmath/o9_order2_census_check.py` — M08's proposed T6,
executed as an extension of the depth-3 harness's coherent anchored-march
reader. Full enumeration of coefficient boxes (plus valuation-restricted
supersets, poolable because a stratum's census is superset-independent);
per box: level-1 stratum classification, then per repeated residual factor
the order-2 window read; censuses tabulated by discrete stratum key under
the (DET) fence. Checks: K1 = level-1 census equals M08 Thm 2 exactly
(regression; k₀ = 0 keying only — see §6.4); K2 = refined census identical
across parent realizations of one discrete shape (the (FRESH)/OL-B
shadow); K3 = census/∏M_λ'(p^g) type-vector-independent per child polygon
(the CEN product law, per p); K4 = the normalized census fits ONE exponent
vector in the atoms {p, p^g − 1, p − 1} across all primes at fixed (n, M)
(the cross-p polynomiality); T2 = principal part length = μ (the pinned
Lemma 2.17(2), per instance).

RUN (2026-08-01, log `verification/openmath/logs/`): 10 configurations —
full enumeration (p,n,M) ∈ {2,3}×{(3,5),(4,4),(4,3)} ∪ {(5,4,3)};
restricted (5,3,5) at mins (3,2,1) and (2/3,4,6) at mins (4,3,2,1) (the
g = 2 design: order-2 residuals over F_{p²}) — 8,220,994 boxes,
1,128,288 order-2 instances, 100 K1 stratum rows, 18 cross-p census cells
(one at g = 2). RESULT: 0 violations on every check. Honest reading
(pass-1 GAP 5(b)(c) folded into the headline, not a footnote):

* the fitted spectrum is all pure q-powers times ∏M with ε = 0 throughout —
  but ε = 0 is FORCED BY SHAPE at every tested cell (all tested strata
  have monic-top right ends, k_s = ℓ, m | n), so the run does NOT
  discriminate (FRESH)(c); the discriminating test is a CEN-J cell with a
  free-end shape (k_s < ℓ) — queued;
* at the 9 character-sensitive cells (child residual types of degree ≥ 2)
  only p ∈ {2, 3} are exercised: two data points against the three-atom
  exponent set are generically underdetermined, so rev 0's "any single K4
  hit would have refuted OL-C" was overstated FOR THOSE CELLS; the (5,4,4)
  restricted run (mins (2,2,1,1), 5^10 boxes, `slow` flag) is the fix and
  is queued. For the remaining cells the fit is over ≥ 3 primes and the
  refutation claim stands.

**K5 (NEW, rev 2): predict-from-ledger at r = 0.**
`verification/openmath/o9_rev2_ledger_predict_check.py` (run 2026-07-31,
log in `verification/openmath/logs/`). For 7 stratum data — the pass-1
countermodel (2,1)→(3,0); integral left tails at e₁ = 1 for p ∈ {2, 3};
a mixed integral/fractional left tail (slope −1/2); left tail + right
tail; left tail + monic top; the k₀ = 0 M08 regression — and EVERY
admissible type assignment (11 (D,λ) cells), the repaired formula
q^{E′}·(q^d−1)^ε·∏M is EVALUATED from the ledger and compared to
brute-force enumeration of the declared box (up to 2^16 tuples per case;
membership = §2's strict keying, an independent reimplementation, not the
harness's). RESULT: **ALL PASS — 11/11 cells exact** (countermodel:
truth 64, formula 64, E′ = 6) **+ the M08 c_i regression
E′_monic = Σ(N − c_i) exact**; the rev-0 formula is REFUTED at every case
with an integral left-tail slot (8 cells: 256; 128 ×4; 16 ×2; 324 — vs
truths 64 ×5; 8 ×2; 108) and agrees with the repaired one
elsewhere (no left tail, or fractional-only left-tail values).

Coverage honesty (unchanged from rev 0 where still true): child residual
types of degree ≥ 2 are exercised at p ∈ {2, 3} but not yet at p = 5 (the
(5,4,4) run above); g = 2 cells have trivial types; a d₁ ≥ 2, g ≥ 2 census
cell needs M = 7-scale runs (proposed, not run). Depth-3 (order-3 census)
untested. K5 is r = 0 only — brute force is infeasible at order-≥1 box
sizes; the order-2 VALUE check is the queued predictor. The march itself
at g ≥ 2 is separately covered by the depth-3 harness's 470,736-instance
run (CU-1's gate).

## 11. Attack list for the hostile pass (rev 2)

1. The (STRICT) threshold: check ⌊L⌋+1 against §2's keying in both
   left-tail regimes (e₁ | (k₀−k) integral and not), and the β_k = eN
   boundary against LED(i)'s inequality-only scope (§5.2 rev-2 note).
2. Lemma LED-top(iii): the non-vanishing rests on "the same-class ledger
   in-forms are F_q-independent", attributed to LED(iii)'s dimension
   count. Does LED(iii) really give independence of the in(B_𝐣), or only
   dim G_β = #(class monomials passing the threshold)? (The two coincide
   iff the in(B_𝐣) span — check the argument.)
3. (E″): the max(0,·) floor semantics vs (FRESH)(a′)'s product-box claim;
   the g_k ≤ β_k-at-on-line-slots emptiness dichotomy; and is (b)'s
   "jointly independent across the on-line slots" strong enough for step 3
   of §6.4, or does the product need an explicit joint-distribution
   clause?
4. §6.4 step 1: is "(DET) over the parent's own reads" exactly the
   hypothesis needed for "parent conditions determined by f mod π^{N₀}"?
5. (ADM) at r = 1: verify w(φ₁) ≡ h₁ (mod e₁) against the pinned (P3)
   V-recursion (the V₁ = 0 convention).
6. K5's membership semantics vs §2's stratum definition: are visible
   steeper deep faces at k < k₀ grouped into the stratum by both (the
   left-tail cutoff reading), and does the brute-force implement exactly
   that?
7. The mechanism note for (FRESH)(c) (§5.4): confirm it is consumed as a
   proof NOWHERE in §§6–8 (it must not be).
8. (Carried from rev 0.) The K4 atom set {p, p^g−1, p−1}: could a genuine
   census produce atoms outside it (e.g. p² + p + 1) that the harness
   would mis-flag — or that the exponent search could accidentally fit at
   small primes?

— O9 Phase-B rev 2. Verdict: PARTIAL — the order-r census REDUCED to
(GR-B) + (FRESH) (the junction pin filed as (FRESH)(c), its rev-0 PROVED
label withdrawn), under the per-datum lattice hypothesis (ADM) (automatic
at orders ≤ 1); the reduction's own mathematics — A1/TRI/LED/LED-top,
(DET), TYPE-MARCH, the STRICT-threshold CEN-W over explicit boxes, CEN-J
with the DISPLAYED (E″) — proved above; r = 0 on k₀ = 0 data = M08 Thm 2
recovered exactly, (E″) validated against M08's printed formula; falsifier:
1.13M order-2 instances clean (FORM) + K5 predict-from-ledger exact at
r = 0 (VALUE), with the rev-0 formula refuted by K5 at every integral
left-tail case.
