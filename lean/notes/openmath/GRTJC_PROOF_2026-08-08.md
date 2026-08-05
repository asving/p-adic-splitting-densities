# GRTJC — J-C, THE CARRY-ALGEBRA JUNCTION (W-6..W-9): the composite-stage graded target exists (localize + gauge, with the ℤ → ℤ/E collapse proved), TC-3 is load-bearing EXACTLY at δ ≥ g_m (theorem, not observation), the anchor-transport isomorphism Ψ with the measured inner normalization ∏_{j≤m} z_j^{D_j}, harness-val = TC-read, and the cocycle semantics — four separately boxed clauses, each an honest proof or an honestly boxed obstruction

**Unit:** GRTJC COMPOSER (Phase 1 of `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`,
dispatched on the instrument's verdict). **Genre: PROOF NOTE at attempt grade —
own acceptance counter 0/2.** No `.lean` touched, no gate fires, **no gate
retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note
DISPLAYS the tie it would need, and by construction cannot retire it — J3b
retires only when (J-C)(ii) survives its own hostile arc), the Asvin P0
application gate stands, and no density/menu/count statement is made anywhere.
**Author:** Fable composer unit, campaign date 2026-08-08 (wallclock 2026-08-05).

**Instrument consumed:** `lean/notes/openmath/GRTJC_PROBE_2026-08-08.md` (seal
`7212e56` → verdict `fc89b03`; runner `verification/openmath/grt_jc_probe.py`):
29 towers, m ∈ {1,2,3}, 669 scored pairs, **22 families all GREEN, 0
violations**, all 29 rows EXHAUSTIVE (structure constant determined with zero
witness input from the harness side; per-pair uniqueness machine-proved). Its
five measurements M1–M5 are this note's structure constants. **Its refutation is
honored:** the brief's germ hypothesis ("the inner normalization factor at
general m is −z_{m+1}") is reading H-D and FAILS on 138/669 pairs; the measured
inner factor is ∏_{j=1}^{m} z_j^{D_j} — the INNER letters. This note proves the
instrument's law, not the brief's guess.

**Own machine leg:** `verification/openmath/grt_jc_checks.py` (two-commit seal;
predictions §9.1 sealed BEFORE the run at commit `6ad01d1`) — it tests THIS
note's clauses, not the instrument's: the slot-span theorem, the scalar-image
lemma, the ψ-kernel witness, the fibred-index bijection, the cocycle identity,
the cyclic-genre law, with five planted teeth. **VERDICT (§9.2): 10 families,
8,566 scored samples, 0 violations, all five teeth fired (1,054 firings),
29 rows, 2.0 s** — including the note's own new sharp prediction (slot set of an
anchor product == {δ}) at **609/609**, and one battery-driven correction applied
to §6(d) (the cyclic law's converse is FALSE — 13 collapse-geography rows are
NOT-CYCLIC).

---

## §0. INPUTS AND THE CONDITIONALITY STACK (read before any clause)

Every clause below is stated with its inputs named. There are five, and no
clause is stronger than the weakest input it uses.

**(IN-1) [ILN]† = (ITER-LAW-n), ACCEPTED** (`ITERLAWN_PROOF_2026-08-08.md`,
arc closed 2026-08-03 at the 2-clean model-diverse bar; PC6 CLEAN + PE7 CLEAN).
Scope as accepted: for all n ≥ 1 on the (n+1)-read **standard-lift** harness
class, the closed form for the harness value cocycle

    c_{n+1}(γ,γ′) = z̄^δ · ∏_{j=1}^{n} z_j^{D_j},   δ = ⌊(s_{n+1}(γ)+s_{n+1}(γ′))/e_n⌋,

with residuals: the open engine families (RM-m, m ≥ 2) and (W-MULT-DCX-m), the
fenced corners, and DCX-(n) = ∪_m DCX_m excluded. **In this note c_T denotes
this closed form**, and "the scored stratum" means [ILN]†'s own: all D_j
integral ∧ the pair off DCX. (Instrument census: on its 29-row roster **DCX
pairs 0, non-integral-D pairs 0** — the whole grid sat inside the accepted
stratum.)

**(IN-2) GRB Lemma D-REAL + CARRY-1 + (W-MULT), ACCEPTED-WITH-CONDITIONS**
(`GRB_ORDER2_2026-08-05.md` §S5.2/§S6a; conditional on the GRB §0 ladder
((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN)) and the §3.3 [T] pins — that
conditionality is inherited here forever). This is the **last-read layer**: the
gauged anchor system at the last read is K_{m+1}[u]/(u^{e_m} − z̄), CARRY-1 is
φ_γφ_{γ′} = φ_{γ+γ′}·ȳ^δ at that layer, and (W-MULT) is
R^{gr}_{γ+γ′}(αβ) = y^{δ}R^{gr}_γ(α)R^{gr}_{γ′}(β). **CONSUMED, NOT RE-PROVED.**
J-C(i) is this layer; §§2–5 below are the composite-stage content.

**(IN-3) The FGMN graded package, CITED LITERATURE, transported by W-1.** As
pinned and quoted in the corpus (`GRB_ORDER2_2026-08-05.md` §S6a verbatim: "Thm
4.2 three times … gr_K(w) is a domain … Thm 4.8 (evaluation at ȳ is an
isomorphism F_r[y] → Δ) … ord_y-additivity from s(gh) = s(g) + s(h), Cor 2.7"):

    (a) w = w_{m+1} is multiplicative: w(fg) = w(f) + w(g);
    (b) gr(w) is a DOMAIN, and in(fg) = in(f)·in(g);
    (c) gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y] on the anchor basis
        in(φ_γ) at attained γ  [Thm 4.2];
    (d) evaluation y ↦ z̄ is an isomorphism K_m[y]/(ψ_m) ≅ K_{m+1}
        [Thm 4.8 / Cor 4.9];
    (e) the minimal on-line Φ_m-abscissa is additive: s(fg) = s(f)+s(g)
        [Cor 2.7].

FGMN state these for types of ARBITRARY order, so the composite-stage instance
is a citation, not an extrapolation by this note — **but the theorem numbering
above is the corpus's pinned quotation, re-verified against no printed source in
this session (citation-precision owed; flagged in JC-BOX-3).** Their transport to
the HARNESS objects (w = v_{m+1} in the sheared frame; R_{m,λ} = c·R_λ^{GMN} with
c a line-wise unit) is **W-1 (J-A), ATTEMPT GRADE**.

**(IN-4) W-2 / J-A / J-B, ATTEMPT GRADE (counter 0/2).** W-2 (the lift junction,
`GRTW2_PROOF_2026-08-08.md`), J-A (the dictionary), J-B (the tree;
`GRTJB_PROOF_2026-08-08.md`, whose JB-BOX-2 conditionality — (VD-m) free only at
m ≤ 1, JA-VDIND at m ≥ 2, JA-BOX-2's (R-coll) at m ≥ 3, the pinned-ℓ orbit,
the shared-key perimeter q ≤ qcap — rides in wherever a print-residual statement
is used). §5's germ display cites J-B's JB-CREAD + JB-EPS and inherits their
fences verbatim.

**(IN-5) The corpus's own construction layer, ACCEPTED as part of [ILN]†:** the
class pin ([ILN]† S0.1: ψ_j monic irreducible with ψ_j(0) ≠ 0, gcd(e_j,h_j) = 1,
g_j ≥ 1), the split/anchor conventions (S0.2), REALIZE-(m) with its R1/R2/R3 laws
(S4.1: deg < deg Φ_m, w = β, read = τ), and the level reads. Everything in §1 is
definition, not claim.

**THE STACK, ONE LINE.** Every clause of §§2–5 rides
`[ILN]† ACCEPTED (scored stratum) + GRB/CARRY-1 ACCEPTED-conditional (§0 ladder) + FGMN (c)(d)(e) CITED + W-1/W-2/J-A/J-B ATTEMPT (0/2)`,
and this note's own arc starts at **0/2**. Nothing here may be consumed at proof
grade before its hostile arc.

---

## §1. OBJECTS (definitions; nothing is claimed in this section)

Fix a complete DVR O with uniformizer π and finite residue field, and a
standard-lift tower T of the [ILN]† class with reads (e_j,h_j,g_j), j = 0..m,
so NR := m+1 reads. Write E := e_0e_1⋯e_m (= E_{m+1} of the blueprint), and:

* **keys** Φ_0 (monic, deg d_0, irreducible mod π), and Φ_{j+1} built by
  REALIZE: Φ_{j+1} = Φ_j^{e_jg_j} + Σ_{k<g_j} C_kΦ_j^{e_jk} with
  deg C_k < deg Φ_j. Hence **deg Φ_{j+1} = e_jg_j·deg Φ_j**.
* **weights** γ_1 = h_0, wΦ_{j+1} = e_jg_jγ_{j+1}, γ_{j+1} = e_jwΦ_j + h_j;
  the MacLane weight w_{j+1}(f) = min_a (e_j w_j(A_a) + aγ_{j+1}) over the
  Φ_j-development f = Σ_a A_aΦ_j^a, and w_0 = the coefficientwise π-valuation.
  **w := w_{m+1}** throughout; gr(w) := ⊕_{γ∈ℤ} P_γ/P_{γ+1}, P_γ := {w ≥ γ},
  and in(f) := the class of f in gr_{w(f)}.
* **residues** K_0 = k_0[x]/(Φ̄_0), K_{j+1} = K_j[y]/(ψ_j) = K_j[z_{j+1}],
  g_j = deg ψ_j; **z̄ := z_{m+1}**, K := K_{m+1}. Note ψ_j(0) ≠ 0 ⟹ z_{j+1} ≠ 0,
  so every letter is a unit.
* **split** γ ↦ (s_1..s_{NR}, u_1) by iterated eq-(12): s_{NR},u_{NR} = eq12(γ,e_m,h_m),
  β_{j-1} = u_j − s_jwΦ_{j-1}, s_{j-1},u_{j-1} = eq12(β_{j-1},e_{j-2},h_{j-2});
  s_{j+1} ∈ [0,e_j) always. **Window** W := {γ : u_1(γ) ≥ 0}.
* **anchors** φ_γ := π^{u_1}∏_{j=0}^{m}Φ_j^{s_{j+1}} for γ ∈ W (Tower.tanch).
* **the level read** at line λ: develop f in Φ_m, keep the digits at abscissas
  a ≡ s_{NR}(λ) (mod e_m) that lie ON the line (weight exactly λ), ε-correct
  them, and pack them as read(λ,f) = Σ_j C_j z̄^{\,j}, **grid slot**
  j := (a − s_{NR}(λ))/e_m. Define the **digit polynomial**

      𝑅_λ(f) := Σ_j C_j y^{\,j} ∈ K_m[y]     (Tower.read_coeffs, packed in y)

  so that **read(λ,f) = 𝑅_λ(f)(z̄) = 𝑅_λ(f) mod ψ_m** — a definitional identity
  of the corpus's own read. By the definition of w as a min, **𝑅_λ(f) = 0 ⟺
  w(f) > λ** (for f with w(f) ≥ λ); so 𝑅_λ is an injective K_m-linear map on
  gr_λ.
* **the scalar lift** Λ_N(c) := realize(NR,c,N) for c ∈ K, N ≡ 0 (mod E) with
  N ≥ wΦ_{NR}: by R2/R3, w(Λ_N(c)) = N and read(N,Λ_N(c)) = c. X_N := Λ_N(1).
* **the TC chain** (blueprint S2.3): TC-1 localize gr(w) at in(π); TC-2 gauge
  π ↦ 1 (the [F.0] weight gauge), collapsing ℤ → ℤ/E; TC-3 the residue quotient
  Δ = K_m[y] ↠ K_m[y]/(ψ_m) = K_{m+1}. **𝒜(T)** := the K-span of the anchor
  classes in the degree-0 component of the TC-transported gr(w).
* **the harness cocycle** c_T(γ,γ′) := z̄^{δ}∏_{j=1}^{m}z_j^{D_j} with δ, D_j the
  [ILN]† recursion data; δ = (s_{NR}(γ)+s_{NR}(γ′) − s_{NR}(γ+γ′))/e_m.
  **Since s_{NR} ∈ [0,e_m) on both arguments, δ ∈ {0,1} always** (used
  constantly below).

---

## §2. CLAUSE W-6 — THE CARRY TARGET EXISTS AT EVERY COMPOSITE STAGE

> **THEOREM W-6.** For every tower T of the [ILN]† class and every level m with
> E > 1: (i) TC-1 and TC-2 are legitimate ring-level operations on gr(w_{m+1});
> (ii) the gauged ring A(T) := gr(w)[in(π)^{-1}]/(in(π) − 1) is **ℤ/E-graded**,
> with A_ν ≅ gr_n(w)-piece for any n ≡ ν, and the surviving index is the
> abscissa-coset index of §1's split (LEMMA JC-FIB); (iii) the anchor map
> γ ↦ [φ_γ] is E-periodic on the nose (LEMMA JC-PER), so it is defined on ℤ/E;
> (iv) **TC-3 is load-bearing exactly on the pairs with δ ≥ g_m** (THEOREM
> JC-LOAD), and the outer factor z̄^δ of c_T is TC-3's image of the graded slot
> shift y^δ — not obtainable from TC-1/TC-2 alone; (v) TC-3 is not a relabeling:
> the level-NR read is non-injective on a graded piece, with the classifier's own
> next key Φ_{m+1} as the kernel witness (COROLLARY JC-PSIKER).
>
> **GRADE: PROVED at general m** on inputs (IN-3)(a)(b)(c)(e) + (IN-5), with the
> single located exception of the **top-flat corner e_m = 1 ∧ g_m = 1** in
> JC-LOAD's sharp form (JC-BOX-4). Attempt grade 0/2.

### 2.1 LEMMA JC-DOM (TC-1 is legitimate at every stage)

*Statement.* gr(w) is a commutative ℤ-graded domain; in(π) is homogeneous of
degree **E** and is a nonzerodivisor; hence the localization
B := gr(w)[in(π)^{-1}] exists as a ℤ-graded ring, gr(w) ↪ B, and
B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}.

*Proof.* By (IN-3)(a) w is multiplicative, so for f,g ≠ 0,
in(f)in(g) = in(fg) ≠ 0 in gr_{w(f)+w(g)}: gr(w) is a domain ((IN-3)(b), the
same domain property the accepted GRB S6a cancellation uses). For the degree:
w_0(π) = 1 and, since the Φ_j-development of the constant π is A_0 = π,
w_{j+1}(π) = e_jw_j(π); hence **w(π) = e_0e_1⋯e_m = E** by induction. A
nonzerodivisor homogeneous element of a graded domain may be inverted: the
graded localization at the multiplicative set {in(π)^k} is a ℤ-graded ring, with
the stated degree pieces, and the localization map is injective because gr(w) is
a domain. ∎

*Remark (what this settles).* GRW2_TIE_DESIGN's OB-1 asked for exactly this at
the composite stage and recorded "no accepted clause supplies it". The supply is
multiplicativity of w — which is (IN-3)(a), a literature fact for types of every
order, not a last-read-layer accident.

### 2.2 LEMMA JC-GAUGE (TC-2 is legitimate, and the grading collapses ℤ → ℤ/E)

*Statement.* Let B = ⊕_{n∈ℤ}B_n be any commutative ℤ-graded ring containing a
**unit** ϑ ∈ B_E, E ≥ 1. Put A := B/(ϑ−1)B. Then

    (i)  (ϑ−1)B = ⊕_{ν∈ℤ/E} (ϑ−1)B^{(ν)},  B^{(ν)} := ⊕_{n≡ν (E)} B_n,
    (ii) A = ⊕_{ν∈ℤ/E} A_ν  is ℤ/E-GRADED, A_ν := image of B^{(ν)},
         A_νA_{ν′} ⊆ A_{ν+ν′},
    (iii) for each ν and EACH n ≡ ν (mod E) the composite B_n → A_ν is an
          isomorphism of additive groups; in particular A_0 ≅ B_0 as rings.

*Proof.* (i) For homogeneous b ∈ B_n, (ϑ−1)b = ϑb − b has both terms in
B^{(n mod E)}; so (ϑ−1)B is the direct sum of its intersections with the
B^{(ν)}, and B^{(ν)}B^{(ν′)} ⊆ B^{(ν+ν′)}. (ii) is immediate from (i).
(iii) Fix n ≡ ν and define σ: B^{(ν)} → B_n by σ(Σ_k b_{n+kE}) := Σ_k ϑ^{-k}b_{n+kE}
(each summand lands in B_n because ϑ^{-k} has degree −kE). σ is additive and
surjective (restrict to k = 0). σ kills (ϑ−1)B^{(ν)}: for b ∈ B_{n+kE},
σ(ϑb − b) = ϑ^{-(k+1)}ϑb − ϑ^{-k}b = 0. Conversely, modulo (ϑ−1)B^{(ν)} we have
b_{n+kE} ≡ ϑ^{-k}b_{n+kE} (because ϑ^{-k}b·(ϑ^k − 1) ∈ (ϑ−1)B), hence
x ≡ σ(x) for every x ∈ B^{(ν)}; so σ(x) = 0 forces x ∈ (ϑ−1)B^{(ν)}. Thus
ker σ = (ϑ−1)B^{(ν)} and B_n ≅ B^{(ν)}/(ϑ−1)B^{(ν)} = A_ν. ∎

*Application.* Take B from JC-DOM and ϑ := in(π) ∈ B_E (a unit after TC-1, of
degree E by JC-DOM — the harness check w(π) = E the design note wanted). TC-2 is
therefore a legitimate ring-level operation at **every** stage, its output is
ℤ/E-graded, and the design note's C13 objection ("p ↦ 1 is not a graded
homomorphism from TC-1's output alone") is answered in the only way it can be:
the gauge is not a graded map but a **quotient by a non-homogeneous principal
ideal whose ideal splits along the E residue classes**, which is exactly why the
grading survives modulo E and not on the nose.

### 2.3 LEMMA JC-PER (the anchor system is E-periodic on the nose; OB-2)

*Statement.* For every γ ∈ W and k ≥ 0: the split satisfies
s_{j+1}(γ+kE) = s_{j+1}(γ) for all j and u_1(γ+kE) = u_1(γ) + k; hence
**φ_{γ+kE} = π^k·φ_γ as polynomials (byte-for-byte)**, and after TC-2
[φ_{γ+E}] = [φ_γ]. So u_γ ↦ [φ_γ] is well defined on ℤ/E, and (choosing window
representatives) independent of the representative.

*Proof.* By induction down the split. At the top, e_m | E, so
s_{NR}(γ+E) = (l_mγ + l_mE) mod e_m = s_{NR}(γ), and
u_{NR}(γ+E) = u_{NR}(γ) + E/e_m; hence β_{NR-1}(γ+E) = β_{NR-1}(γ) + E/e_m. The
same step at level j (with e_{j-1} | E/(e_j⋯e_m)) gives s_j unchanged and
β_{j-1} increased by E/(e_{j-1}⋯e_m); at the bottom
u_1(γ+E) = u_1(γ) + E/(e_0⋯e_m) = u_1(γ) + 1. The anchor formula then differs by
exactly one factor π. Iterate for k. ∎

*Machine:* instrument **P0-OB2 = 0/285 byte-for-byte** on every anchor of every
row (OB-2/COR-4 exact); this note's own battery re-tests it at k = 1,2,3
(family JC1).

### 2.4 LEMMA JC-FIB (which ℤ/E-indexing survives: the abscissa cosets)

*Statement.* γ ↦ (s_1(γ),…,s_{NR}(γ)) ∈ ∏_{j=0}^{m}ℤ/e_j is E-periodic and
induces a **bijection ℤ/E ≅ ∏_j ℤ/e_j**. Hence the ℤ/E-grading of JC-GAUGE is
indexed equivalently by γ mod E and by the abscissa-coset tuple — the fibred
ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19).

*Proof.* Periodicity is JC-PER. Both sides have E elements, so it suffices to
show injectivity on [0,E). If γ,γ′ have equal tuples then s_{NR} equal forces
γ ≡ γ′ (mod e_m) (as s_{NR} = l_mγ mod e_m with l_m invertible mod e_m), and
then β_{NR-1} − β′_{NR-1} = (γ−γ′)/e_m; descending, equality of s_{NR-1} forces
(γ−γ′)/e_m ≡ 0 (mod e_{m-1}), and so on down to (γ−γ′)/(e_1⋯e_m) ≡ 0 (mod e_0),
i.e. E | γ−γ′. ∎

*Machine:* family **JC2** (tuple injectivity on E consecutive γ + periodicity);
the instrument's P4-DEG (0/29) is its weaker shadow.

### 2.5 LEMMA JC-ANCHMON (the anchor is a single Φ_m-digit)

*Statement.* For γ ∈ W: (a) Σ_{j<m}s_{j+1}·deg Φ_j < deg Φ_m; hence (b) the
Φ_m-development of φ_γ has exactly one nonzero digit, at abscissa s_{NR}(γ);
hence (c) 𝑅_γ(φ_γ) is a nonzero **constant** in K_m (slot set {0}) and
(d) deg φ_γ < (s_{NR}(γ)+1)·deg Φ_m.

*Proof.* (a) s_{j+1} ≤ e_j − 1 and deg Φ_{j+1} = e_jg_j deg Φ_j ≥ e_j deg Φ_j,
so s_{j+1}degΦ_j ≤ e_jdegΦ_j − degΦ_j ≤ degΦ_{j+1} − degΦ_j; summing over
j = 0..m−1 telescopes to ≤ deg Φ_m − deg Φ_0 < deg Φ_m. (b) φ_γ =
(π^{u_1}∏_{j<m}Φ_j^{s_{j+1}})·Φ_m^{s_{NR}} with the parenthesis of degree
< deg Φ_m by (a) — that IS the Φ_m-development. (c) The single digit sits at
abscissa s_{NR}(γ) = the line's base abscissa, so its slot index is 0; it is
nonzero and, being the only digit, is on the line (w(φ_γ) = γ). (d) Immediate
from (a),(b). ∎

### 2.6 LEMMA JC-SCAL (the scalar image: slots 0..g_m−1, and X_N is a constant)

*Statement.* For N ≡ 0 (mod E), N ≥ wΦ_{NR}, and c = Σ_{i<g_m}c_iz̄^i ∈ K
(c_i ∈ K_m, the canonical representative): (a) s_{NR}(N) = s_{NR}(0) = 0 and
the on-line slot set of Λ_N(c) is contained in {0,…,g_m−1}, with slot i digit
the ε-corrected c_i; so **𝑅_N(Λ_N(c)) is the canonical degree-<g_m
representative of c, up to one line-wise unit**; (b) 𝑅_N(X_N) is a nonzero
CONSTANT (slot set {0}); (c) consequently the "scalar image" at line N is
exactly 𝑅_N(X_N)·{K_m-polynomials of degree < g_m}.

*Proof.* s_{NR}(N) = 0 because E | N and s_{NR} is E-periodic with s_{NR}(0) = 0
(JC-PER/JC-FIB). REALIZE's construction (§1, `_realize`) expands
τ = (c_0,…,c_{g_m−1}) as Σ_i child_i·Φ_m^{k_i} with k_i = s_{NR}(N) + i·e_m and
deg child_i < deg Φ_m; hence the abscissas are exactly {i·e_m : c_i ≠ 0}, i.e.
slots i < g_m, and by R3 the packed read is c. For c = 1 only i = 0 survives, so
X_N has slot set {0} and 𝑅_N(X_N) ∈ K_m^*. (c) is (a) + (b). ∎

*Machine:* family **JC4** (slot support of Λ_N(c) and X_N; digit-to-coefficient
match); the instrument's P0-LIFT (0/138) and P0-SCAL (0/293) are its shadows.

### 2.7 THEOREM JC-SPAN (the slot span of an anchor product is the singleton {δ})

*Statement.* Let γ,γ′ ∈ W with γ+γ′ ∈ W, and let δ = δ(γ,γ′) ∈ {0,1} be the top
carry. Assume **e_m ≥ 2**. Then the on-line slot set of φ_γφ_{γ′} at its own
weight γ+γ′ is exactly **{δ}**, i.e.

    𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^{δ}  for some u ∈ K_m^*.

If e_m = 1 (so δ = 0), the same argument gives slot set ⊆ {0,1} with 0 attained,
i.e. deg 𝑅 ≤ 1.

*Proof.* **Lower end.** By (IN-3)(e) (Cor 2.7 abscissa additivity) the minimal
on-line abscissa of φ_γφ_{γ′} is s_{NR}(γ) + s_{NR}(γ′), and the line's base
abscissa at λ = γ+γ′ is s_{NR}(λ) = s_{NR}(γ)+s_{NR}(γ′) − δe_m; so the minimal
slot is exactly ((s+s′) − (s+s′−δe_m))/e_m = **δ**, and it is attained.
**Upper end.** By JC-ANCHMON(d), deg(φ_γφ_{γ′}) < (s+1)degΦ_m + (s′+1)degΦ_m,
so the largest abscissa occurring in the Φ_m-development is ≤ s+s′+1. On-line
abscissas are ≡ s+s′−δe_m (mod e_m), so their slots k satisfy
k ≤ (s+s′+1 − (s+s′−δe_m))/e_m = δ + 1/e_m, i.e. **k ≤ δ when e_m ≥ 2**
(and k ≤ δ+1 = 1 when e_m = 1). Combining, the slot set is {δ}: a single
nonzero K_m-coefficient u at slot δ. ∎

*Comment.* This is the composite-stage replacement for CARRY-1
(φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ, last-read layer, IN-2): at a composite stage the
identity acquires **exactly one extra K_m-unit u**, and the theorem proves that
the extra factor is a unit of K_m — a scalar that TC-3 never touches — while the
y-degree is exactly δ. **The outer/inner split of c_T is therefore structural,
not a coordinate choice**: outer = the slot shift y^δ; inner = u ∈ K_m^*.

*Machine:* family **JC3** — sealed prediction: slot set of φ_γφ_{γ′} == {δ} on
every scored pair with e_m ≥ 2, and ⊆ {0,1} with 0 attained when e_m = 1.

### 2.8 THEOREM JC-LOAD (TC-3 is load-bearing EXACTLY at δ ≥ g_m)

*Statement.* Fix a pair (γ,γ′) as above with e_m ≥ 2, and consider the
**pre-TC-3** (RAW) equation in gr(w) localized and gauged but NOT quotiented by
ψ_m: does there exist c ∈ K^* with

    𝑅(φ_γφ_{γ′}·X_N) = 𝑅(Λ_N(c)·φ_{γ+γ′})   at the line γ+γ′+N ?   (RAW)

Then: **(RAW) is solvable ⟺ δ < g_m.** Equivalently (δ ∈ {0,1}): the pre-TC-3
scalar exists on every pair except those with δ = 1 ∧ g_m = 1, where the
ψ_m-relation — i.e. TC-3 — is unavoidable. Consequently:

    (a) c_T's OUTER factor z̄^δ is the image under TC-3 (y ↦ z̄) of the graded
        slot shift y^δ; it is NOT obtainable from TC-1/TC-2 alone;
    (b) c_T's INNER factor ∏_j z_j^{D_j} lies in K_m^* and needs no quotient;
    (c) the sealed set identity {no pre-TC-3 scalar} = {δ ≥ g_m} of the
        instrument (0/29 set-mismatches, 134/669 pairs) is a THEOREM, not an
        observation.

*Proof.* Multiplying by X_N transports lines additively and, by (IN-3)(c) and
JC-SCAL(b), multiplies the digit polynomial by the constant 𝑅(X_N) without
changing its y-degree (offset transport, §4.2; note s_{NR}(N) = 0 so
δ(γ+γ′,N) = 0). So by JC-SPAN the LHS has digit polynomial
𝑅(X_N)·u·y^δ, of exact y-degree δ; by JC-SCAL(a)(c) the RHS ranges exactly over
𝑅(X_N)·{polynomials of degree < g_m} as c ranges over K^*. Since K_m[y] is a
polynomial ring, u y^δ (u ≠ 0) equals a polynomial of degree < g_m iff δ < g_m.
For (a): after TC-3 the class of y^δ is z̄^δ, and by §3.2 the value of the
constant is c_T = z̄^δ·u; the pre-TC-3 object y^δ is not in the K_m-span of
{y^i}_{i<g_m} when δ ≥ g_m, so no relabeling of scalars produces it. ∎

*Honest fence.* The proof of the ⟸ direction rides the offset-transport step
(§4.2), which rides (IN-3)(c); the ⟹ direction (the obstruction) rides only
JC-SPAN + JC-SCAL. The instrument's k-distribution **{0 : 669}** says the
π-clearing ladder is never needed on its roster: the canonical division by
Φ_{m+1} alone discharges TC-3 there.

### 2.9 COROLLARY JC-PSIKER (TC-3 is not a relabeling: the ψ-kernel, witnessed)

*Statement.* At every stage the level-NR read is **non-injective on a graded
piece**: with λ := wΦ_{NR} = e_mg_mγ_{m+1},

    𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0   in K_m[y],  but  read(λ, Φ_{m+1}) = ψ_m(z̄) = 0,

so in(Φ_{m+1}) ≠ 0 in gr_λ lies in the kernel of the read; and (when λ ∈ W, so
that the anchor φ_λ exists — otherwise use the π-translate) Φ_{m+1} + φ_λ and
φ_λ are two elements of gr_λ with equal reads and different classes. Hence TC-3
has a nonzero kernel on every graded piece (namely ψ_m·Δ under the anchor
coordinate) and **cannot be a relabeling of scalars.**

*Proof.* Φ_{m+1} = Φ_m^{e_mg_m} + Σ_{k<g_m}C_kΦ_m^{e_mk} with
w(C_kΦ_m^{e_mk}) = λ for every k with ψ_{m,k} ≠ 0 (REALIZE's construction of
C_k at weight (g_m−k)γ_{m+1}, [ILN]† S0.1) — that is the defining property of the
key polynomial: all its terms sit on the λ-line, its slot digits are the
coefficients of ψ_m, and w(Φ_{m+1}) = λ exactly (the corpus's own wΦ gate). So
𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0 while its evaluation at z̄ is ψ_m(z̄) = 0. The read is
additive on a fixed line, giving the second display. ∎

*Instrument corroboration (independent):* the build-phase disclosure that the
naive class identity [π·Λ_N(c)] = [Λ_{N+E}(c)] is **FALSE** — two weight-(N+E)
lifts with the same read need not be the same class — is the same phenomenon
measured from the other side, and is why the instrument's offset clause (P2-OFF,
0/116) is stated on the CONSTANTS.

*Machine:* family **JC6** (the Φ_{m+1} kernel witness: w exact, read 0, slot
digits = ψ_m's coefficients) + tooth **MJ4**.

### 2.10 What TC-3 IS in this note (and why the coordinate calculus is legitimate)

Two facts fix the coordinate calculus used from here on. Both are named inputs,
not new claims.

**(COORD)** For λ ∈ W the digit map 𝑅_λ : gr_λ(w) → Δ := K_m[y] is a K_m-linear
**isomorphism**, carrying in(φ_λ) to a nonzero constant a_λ ∈ K_m^*
(JC-ANCHMON(c)). Injectivity is definitional (§1: 𝑅_λ(f) = 0 ⟺ w(f) > λ);
surjectivity/rank-one is (IN-3)(c) — FGMN Thm 4.2's freeness of gr_λ over Δ on
the anchor basis. Write ρ_λ := 𝑅_λ/a_λ, so ρ_λ(in φ_λ) = 1.

**(MULT)** in(fg) = in(f)in(g) ((IN-3)(b)) plus (COORD) give a unique
**anchor cocycle** A(λ,μ) ∈ Δ with

    ρ_{λ+μ}(αβ) = A(λ,μ)·ρ_λ(α)·ρ_μ(β),  A(λ,μ) = ρ_{λ+μ}(in φ_λ·in φ_μ),

for α ∈ gr_λ, β ∈ gr_μ, λ,μ,λ+μ ∈ W. By JC-SPAN, A(λ,μ) = (u/a_{λ+μ})·y^{δ(λ,μ)}
with u ∈ K_m^*, so **A is a MONOMIAL of y-degree exactly δ** (e_m ≥ 2).

**TC-3 = the quotient by the homogeneous ideal 𝔦 := in(Φ_{m+1})·gr(w)** (this is
exactly what the instrument's certifier operationalizes as division by Φ_{NR}).
Under (COORD)+(MULT), 𝔦 ∩ gr_λ corresponds to ψ_m(y)·Δ, because
ρ_λ(in Φ_{m+1}·β) = A·ψ_m(y)·ρ(β) with ρ(in Φ_{m+1}) = ψ_m(y)/a_{wΦ}
(JC-PSIKER's computation; if wΦ_{NR} ∉ W replace Φ_{m+1} by its π-translate
π^kΦ_{m+1} with wΦ_{NR}+kE ∈ W — legitimate after TC-1, where in(π) is a unit,
and the ideal is unchanged). Hence for every λ ∈ W

    gr_λ/(𝔦 ∩ gr_λ)  ≅  Δ/(ψ_m)  =  K_{m+1} = K       (via y ↦ z̄),

a ONE-dimensional K-space with basis the image of in(φ_λ). This is the precise
sense in which TC-3 turns the Δ-coordinate into a K-scalar — and JC-PSIKER says
its kernel ψ_m·Δ ≠ 0, so no relabeling can replace it.

---

## §3. CLAUSE W-7 — THE ANCHOR-TRANSPORT ISOMORPHISM Ψ

> **THEOREM W-7.** Fix T of the [ILN]† class, m with E > 1, and window
> representatives γ_0,…,γ_{E−1} ∈ W of the E classes mod E (they exist: all
> large γ lie in W). Let 𝒜(T) be the K-span of the anchor classes [φ_{γ_ν}] in
> the degree-0 component of the TC-transported gr(w) (§2.10). Then the K-linear
> extension of u_ν ↦ [φ_{γ_ν}] is an isomorphism of K-algebras
>
>     Ψ : (⊕_{ν∈ℤ/E} K·u_ν, u_νu_{ν′} = c_{m+1}(ν,ν′)u_{ν+ν′})  ≅  𝒜(T),
>
> where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T), and the structure
> constant is
>
>     c_{m+1}(γ,γ′) = (u/a_{γ+γ′})·z̄^{δ}          [always, §3.2 EXISTENCE]
>                   = z̄^{δ}·∏_{j=1}^{m} z_j^{D_j} = c_T(γ,γ′)
>                                                  [on [ILN]†'s scored stratum]
>
> with u = the slot-δ coefficient of JC-SPAN and a_λ = 𝑅_λ(φ_λ) ∈ K_m^* the
> anchor's own digit constant.
>
> **GRADES (per obligation, honestly separated):**
> * **OB-2 (well-defined): PROVED, general m** — JC-PER, byte-exact.
> * **OB-3 EXISTENCE + STRUCTURE (there is a constant, and it is
>   (K_m^*-unit)·z̄^δ): PROVED, general m, on ALL window pairs** — no [ILN]†,
>   no stratum fence (§3.2). Sharp form needs e_m ≥ 2 (JC-BOX-4).
> * **OB-3 VALUE (the unit is ∏_{j≤m}z_j^{D_j}): PROVED, general m, on
>   [ILN]†'s scored stratum** (D integral ∧ off DCX), by transport through W-8
>   + [ILN]† ACCEPTED (§3.3).
> * **OB-4 (independence): PROVED, general m** — degree separation +
>   (COORD)/(IN-3)(c) base change (§3.4); the Δ-rank input is
>   literature-carried, NOT measured (JC-BOX-3).
> * **OB-5 (tautology fence): DISCHARGED as an architecture statement**
>   (§3.5), with the instrument's independent-code leg as its machine bracket.
> * Attempt grade 0/2; the whole clause rides §0's stack.

### 3.1 OB-2 — well-definedness (and representative-independence)

JC-PER gives φ_{γ+kE} = π^kφ_γ as polynomials, so [φ_{γ+kE}] = [φ_γ] after TC-2
(JC-GAUGE gauges in(π) to 1). Hence u_ν ↦ [φ_{γ_ν}] does not depend on which
window representative of ν is chosen, and Ψ is defined on ℤ/E. Every A_ν is
1-dimensional over K after TC-3 (§2.10), so Ψ maps the ν-summand onto A_ν's
K-line. **PROVED, general m.** *Machine:* JC1 (k = 1,2,3) + the instrument's
P0-OB2 0/285 and P2-REP 0/174.

### 3.2 OB-3, EXISTENCE + STRUCTURE — the composite CARRY law (no [ILN]† used)

**THEOREM JC-CARRY-m.** For γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:

    in(φ_γ)·in(φ_{γ′}) = (u/a_{γ+γ′})·y^{δ}·in(φ_{γ+γ′})   in the ρ-coordinate,
    u ∈ K_m^*,  δ = δ(γ,γ′) ∈ {0,1},

and after TC-3 the scalar (u/a_{γ+γ′})·z̄^δ ∈ K^* is the structure constant of
𝒜(T) at (γ,γ′). Pre-TC-3 it is a K-scalar iff δ < g_m (JC-LOAD).

*Proof.* JC-SPAN computes 𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^δ with u ∈ K_m^*; divide by
a_{γ+γ′} to pass to ρ, which is the definition of A(γ,γ′) in (MULT). TC-3 sends
y ↦ z̄ (§2.10). ∎

**This is the composite-stage generalization of CARRY-1** (IN-2: at the last-read
layer φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ with NO extra factor). The extra factor at a
composite stage is exactly one K_m-unit, and the theorem locates it: it is the
slot-δ digit coefficient of the anchor product, normalized by the target anchor's
own digit constant. **Three consequences worth displaying separately:**

1. **The outer/inner split is structural.** Outer = y^δ (slot shift, TC-3's
   z̄^δ); inner = a K_m^*-unit (TC-3-blind). No coordinate choice enters. In
   particular the instrument's rival readings H-B (inner dropped) and H-C
   (germ-signed outer) are refuted structurally as well as numerically (H-B
   fails on exactly the 215 pairs with nontrivial inner; H-C on 73).
2. **Existence is unconditional in the window.** The constant exists on EVERY
   window pair, including pairs off [ILN]†'s scored stratum (non-integral D_j,
   DCX pairs) where the closed form c_T is not even defined. This is a STRICT
   extension of the accepted law's scope — with **zero machine support**, since
   the instrument's grid contained 0 DCX and 0 non-integral-D pairs (JC-BOX-2).
3. **δ ∈ {0,1} always**, so "TC-3 load-bearing" ⟺ δ = 1 ∧ g_m = 1: the load
   set is a *geography*, not a growing set — it is empty on every g_m ≥ 2 stage.

### 3.3 OB-3, VALUE — the inner normalization is ∏_{j=1}^{m}z_j^{D_j}

**THEOREM JC-INNER.** On [ILN]†'s scored stratum (all D_j integral, pair off
DCX), for γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:

    c_{m+1}(γ,γ′) = c_T(γ,γ′) = z̄^{δ}·∏_{j=1}^{m}z_j^{D_j},
    equivalently   u = a_{γ+γ′}·∏_{j=1}^{m}z_j^{D_j}  in K_m^*.

*Proof.* By THEOREM W-8 (§4, proved independently of c_T) the gr-side constant
equals the harness ratio: c_{m+1}(γ,γ′) = c_val(γ,γ′) :=
read(γ+γ′,φ_γφ_{γ′})/read(γ+γ′,φ_{γ+γ′}). By [ILN]† (IN-1, ACCEPTED on exactly
this stratum) c_val = c_T. Compose. For the second form, divide by z̄^δ (a unit,
since ψ_m(0) ≠ 0) and use that ∏z_j^{D_j} and u/a lie in K_m, on which
y ↦ z̄ reduction is the injection K_m ↪ K. ∎

**The germ, split honestly (M3, and J-B's fence).** J-B's JB-CREAD gives the
(C-READ) transport constant c_m = ψ_{m,0} = −z_{m+1} at the level-m read, with
the ε-carry cancelling in print coordinates (LEMMA JB-EPS, unconditional). The
instrument measured this in the carrier and split it:

* **CONFIRMED as a value law**: on all **27 eligible (g_m = 1) stages**,
  val(Ĉ_m) = −z̄ = −z_{m+1} exactly, where Ĉ_m := Φ_{m+1} − Φ_m^{e_m} is the
  canonical correction digit (J-B's g_m = 1 well-definedness fence, JB-BOX-4);
  and the carrier-side class constant κ of multiplication by [Ĉ_m] satisfies
  **κ·val(φ_{e_mγ_{m+1}}) = −z_{m+1} on all 27 stages (0 violations)**, with κ
  itself ranging over {1, z̄, z̄², z̄³, z̄⁴}. In this note's coordinates that
  identity is the a_λ-normalization of §3.2: κ is the class constant of the
  correction digit measured against the anchor, so the bare letter appears
  **exactly when the anchor's own digit constant is 1**. The claim
  "c_m = −z_{m+1}" is therefore a statement about the transport constant modulo
  the anchor's value normalization — J-B's fence is honored, not widened (and
  J-B's own scope fences ride: (VD-m) free only at m ≤ 1, JA-VDIND above,
  g_m = 1 for the Ĉ_m instance).
* **REFUTED as OB-3's inner factor**: the brief's literal hypothesis is reading
  H-D (inner letters replaced by −z_{m+1}) and it FAILS on **138 of 669** scored
  pairs. §3.2 explains why structurally: the inner factor is a unit of **K_m**,
  and −z_{m+1} ∉ K_m whenever g_m ≥ 2; on g_m = 1 stages K_{m+1} = K_m and the
  two can coincide numerically without coinciding as laws (the instrument's own
  printer caveat, S6.2).

### 3.4 OB-4 — K-linear independence (Thm 4.2 analogue), and the zero-class genre

**THEOREM JC-IND.** The classes [φ_{γ_0}],…,[φ_{γ_{E−1}}] are K-linearly
independent in 𝒜(T), and each spans its own ℤ/E-graded line; so Ψ is bijective.

*Proof.* By JC-GAUGE the transported ring is ℤ/E-graded and [φ_{γ_ν}] ∈ A_ν
with ν = γ_ν mod E pairwise distinct (JC-FIB). A relation Σ_ν c_ν[φ_{γ_ν}] = 0
with c_ν ∈ K ⊂ A_0 therefore splits into c_ν[φ_{γ_ν}] = 0 in A_ν for each ν. By
§2.10 each A_ν (after TC-3) is a 1-dimensional K-space with basis [φ_{γ_ν}] — the
base change of the free rank-one Δ-module gr_{γ_ν} along Δ ↠ Δ/(ψ_m) = K. Hence
c_ν = 0. Spanning is definitional (𝒜(T) is DEFINED as the K-span; design note
C18) — the content is independence, and it is exactly the composite-stage
instance of FGMN Thm 4.2's rank-one freeness. ∎

**The case split FROM the census (examples-first).** The instrument's OB-4
censuses give exactly three genres, and each is now accounted for:

| genre (instrument) | count | status here |
|---|---|---|
| anchor classes (P4-DEG) | 29/29 rows bijective | never zero: a_λ ∈ K_m^*, coordinate a unit constant, not divisible by ψ_m |
| monomial perturbations (SPAN-M) | **328 certified / 0 zero-class / 0 failed** | coordinate = (unit)·y^k reducing into K ⟹ certifies; 0 genre rows, so no case is owed |
| weight-matched sums (SPAN-S, unscored) | 435 certified / **60 zero-class** / 0 unexplained | **PROVED AWAY**: a class dies in TC-3 iff its Δ-coordinate ∈ (ψ_m) (§2.10). The 60 are exactly that kernel; they are not anchors and carry no information about OB-4. The two build-phase "failures" were such zero-classes — which is why c = 0 was admitted |

**Honest rider.** The Δ-rank input (IN-3)(c) is *literature-carried*: the
instrument explicitly did NOT measure freeness over Δ before TC-3 (only its
degree-separation shadow and post-TC-3 spanning). If Thm 4.2's composite-order
instance failed, (COORD) and hence §§2.7–3.4 would fail together. JC-BOX-3.

### 3.5 OB-5 — the tautology fence: HOW the gr side is computed

The fence demands that 𝒜(T)'s multiplication be computed in gr(w) *before* c_T
is mentioned, and only then compared. This note's chain does exactly that, and
the dependency order is auditable:

1. **gr-side only** (no c_T, no harness read): JC-DOM, JC-GAUGE, JC-PER, JC-FIB,
   JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD, JC-PSIKER, §2.10's (COORD)/(MULT),
   JC-CARRY-m, JC-IND. Inputs used: the corpus's definitions of w, split,
   anchors, REALIZE, and FGMN (b)(c)(e). **The structure constant's existence,
   its outer/inner shape, its y-degree, and the TC-3 load set are all fixed
   here.**
2. **comparison only** (c_T enters ONCE): §3.3 evaluates the already-computed
   constant against the accepted closed form, through W-8's read identity.
   Deleting §3.3 leaves §§2–3.2 and 3.4 standing.

**Machine bracket for the fence** (the instrument's architecture, quoted): the
gr-side constant is the unique solution of a weight inequality whose decision
procedure calls exactly four primitives — schoolbook O[x] arithmetic, the weight
w by iterated Φ-development, the graded scalar lift REALIZE, and the classifier's
own next key Φ_{NR} — while `Tower.constants` (c_T) and `Tower.read` (the harness
val) are **never called inside the determination or the certification**; all 29
rows ran EXHAUSTIVE over K (zero witness input) with per-pair uniqueness
machine-proved; and the tautology tooth MT3 (one anchor rescaled by a nontrivial
scalar class) was **caught on 197/206 pairs, ≥ 1 per non-skipped row (28/28)**,
while the c_T-defined "check" reports 0 violations by construction. The 9
escapes are disclosed (single-pair, all prime-residue-field rows |K| ∈ {3,5},
planted rescaling coincides with a lawful constant) — they weaken the tooth's
resolution, not the fence's architecture.

---

## §4. CLAUSE W-8 — HARNESS-VAL = TC-READ (OB-6)

> **THEOREM W-8.** For γ,γ′ ∈ W with γ+γ′ ∈ W, and N ≡ 0 (mod E), N ≥ wΦ_{NR}:
> the gr-side structure constant of §3.2 equals the harness value ratio,
>
>     c_{m+1}(γ,γ′)  =  c_val(γ,γ′) := read(γ+γ′, φ_γφ_{γ′}) / read(γ+γ′, φ_{γ+γ′}),
>
> exactly, with every line-wise normalization cancelling; and the residue chain
> K_0 ⊂ … ⊂ K_{m+1} used by both sides is one and the same tower (J-C(iii)).
> **GRADE: PROVED at general m** on inputs (COORD)+(MULT)+JC-SPAN+JC-SCAL+R3
> (i.e. FGMN (b)(c)(e) via W-1, ATTEMPT). Attempt 0/2. Machine: the instrument's
> **P5-OB6 0/669** (both sides computed independently per pair).

### 4.1 Proof

Both sides are computed in the ρ-coordinate of §2.10.

*The read is the reduced coordinate.* By §1 (definition), read(λ,f) = 𝑅_λ(f)(z̄).
Hence for any f with w(f) = λ,

    read(λ,f) / read(λ,φ_λ) = 𝑅_λ(f)(z̄)/a_λ = ρ_λ(in f)(z̄)          (†)

(a_λ ∈ K_m^* is a constant, so its reduction is itself). **No unit is
unaccounted for: (†) is an identity of the corpus's own definitions, and the
line-wise ε-kit lives inside 𝑅_λ on both sides of the quotient.**

*The gr-side constant.* Let c := c_{m+1}(γ,γ′) be defined by the fence-clean
equation at the offset line λ+N, λ := γ+γ′:

    in(φ_γ)in(φ_{γ′})in(X_N) = in(Λ_N(c))·in(φ_λ)   in the TC-transported ring.

Apply ρ_{λ+N} and (MULT) to both sides. LHS = A(γ,γ′)·A(λ,N)·ρ_N(in X_N) and
RHS = A(λ,N)·ρ_N(in Λ_N(c)); A(λ,N) ≠ 0 cancels (Δ is a domain), leaving

    ρ_N(in Λ_N(c)) = A(γ,γ′)·ρ_N(in X_N).                              (‡)

*The lift is exactly normalized.* By JC-SCAL(b), 𝑅_N(X_N) is a constant, and by
R3 its reduction is read(N,X_N) = 1; a constant equal to 1 after the injection
K_m ↪ K **is** 1, so 𝑅_N(X_N) = 1 and ρ_N(in X_N) = 1/a_N. By JC-SCAL(a),
𝑅_N(Λ_N(c)) is a polynomial of y-degree < g_m whose reduction is
read(N,Λ_N(c)) = c (R3); the canonical degree-<g_m representative of c is unique,
so **𝑅_N(Λ_N(c)) = c̃(y)** on the nose and ρ_N(in Λ_N(c)) = c̃(y)/a_N.

*Conclusion.* (‡) becomes c̃(y) = A(γ,γ′) = (u/a_λ)y^{δ} (JC-CARRY-m). Reducing
mod ψ_m: c = (u/a_λ)·z̄^{δ}. On the other side, by (†) with f = φ_γφ_{γ′} and
JC-SPAN,

    c_val = ρ_λ(in φ_γ·in φ_{γ′})(z̄) = ((u/a_λ)y^{δ})(z̄) = (u/a_λ)z̄^{δ}.

The two agree. ∎

*Two remarks the design note asked for.* (a) The a_λ's — the anchor's own digit
constants, i.e. the ε-normalization the harness carries — **cancel** because both
reads in c_val sit on the SAME line λ; this is why no coboundary condition is
needed, and it is the general-m form of the ε-collapse J-B proved
unconditionally (JB-EPS). (b) C15's separation stands: nothing above uses N-1's
operator-level commuting diagram; what is used is (COORD)+(MULT), i.e. the
carrier-level content, which is precisely what C15 said was missing. This note
supplies it from FGMN Thm 4.2 + the corpus's read definition, at the cost of
riding W-1's dictionary for the transport of Thm 4.2 to the harness w.

### 4.2 The offset-transport lemma (used by JC-LOAD and by (‡))

*Statement.* For λ ∈ W and N ≡ 0 (mod E), N ≥ wΦ_{NR}: s_{NR}(N) = 0,
δ(λ,N) = 0, A(λ,N) is a **constant**, and multiplication by X_N carries ρ_λ
isomorphically onto ρ_{λ+N} up to that constant — in particular it preserves
y-degrees.

*Proof.* s_{NR}(N) = 0 by JC-FIB (E | N); then s_{NR}(λ+N) = s_{NR}(λ)
(JC-PER), so δ(λ,N) = 0 and JC-SPAN gives A(λ,N) constant. Apply (MULT) with
ρ_N(in X_N) = 1/a_N ∈ K_m^*. ∎

*Machine:* the instrument's **P2-OFF 0/116** (constants independent of the scalar
offset) and **P0-SCAL 0/293** (scalar multiplicativity in gr), plus this note's
family JC4.

### 4.3 J-C(iii) — the residue chain

The chain used on the gr side is K_0 = k_0[x]/(Φ̄_0) and K_{j+1} = K_j[y]/(ψ_j)
(§1), which is the classifier's residual tower `ResidueTower` by construction of
the type: ψ_j is the residual polynomial of Φ_{j+1} at level j, and TC-3's
identification Δ/(ψ_m) ≅ K_{m+1} is (IN-3)(d). Compatibility with (i)/(ii)'s
scalars is the statement that the K_m ⊂ K_{m+1} used by JC-CARRY-m's inner factor
is the same inclusion — true by construction, since the inner unit is literally a
product of the letters z_1..z_m of the same tower. **GRADE: PROVED, general m,
by construction — no independent content beyond the identification (IN-3)(d).**

---

## §5. CLAUSE W-9 — COCYCLE SEMANTICS (the S-priced corollary, composed as one)

> **COROLLARY W-9.** Given W-6, W-7, W-8: (i) c_{m+1} descends to a map
> ℤ/E × ℤ/E → K^* and **is a 2-cocycle**: c(a,b)c(a+b,c) = c(b,c)c(a,b+c) — this
> is [ILN]†'s COR-2, and on the gr side it is nothing but **associativity of
> gr(w)'s multiplication**; (ii) its y-degree part δ satisfies the integer
> cocycle identity δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c) (the {0,1}-valued
> carry cocycle); (iii) 𝒜(T) is the **twisted group algebra** K^{c}[ℤ/E] of the
> abscissa-coset group over the carry cocycle; (iv) COR-4's monodromy is the
> **gauge period**: φ_{γ+E} = π·φ_γ (JC-PER) is the period, in(π) is the
> gauge unit of degree E (JC-DOM), and the E-fold orbit product
> ζ_T := ∏_{k=1}^{E−1}c(1,k) is exactly the K-scalar by which the E-fold anchor
> product differs from the π-power that TC-2 sets to 1.
> **GRADE: PROVED given W-6..W-8 (general m), S-priced as the blueprint says.**

*Proofs.* (i) Descent is JC-PER. Associativity of gr(w) gives
(in φ_a·in φ_b)·in φ_c = in φ_a·(in φ_b·in φ_c); expanding both with (MULT)
yields A(a,b)A(a+b,c) = A(b,c)A(a,b+c) in Δ, and reducing mod ψ_m gives the
K^*-cocycle identity. (ii) Take y-degrees in the same Δ-identity (JC-CARRY-m:
deg A(a,b) = δ(a,b)) — degrees add, so the identity is the additive one. (iii)
Restatement of W-7's Ψ. (iv) With the representative γ_0 = 0 ∈ W we have
φ_0 = 1, and JC-PER gives φ_{kE} = π^k, whose gauged class is 1; iterating
(MULT) along the orbit of the class 1 gives [φ_1]^E = ζ_T·[φ_0] = ζ_T. ∎

**FINDING JC-F1 (blueprint display correction, REVIEW-OWED — read with §6).**
(iv)'s computation has a consequence the blueprint's cyclic-fence wording does
not survive as literally stated. Put v := [φ_{γ_1}] (the anchor class of the
residue class 1 ∈ ℤ/E). Then v^k = β_k·[φ_{γ_k}] with β_k := ∏_{i=1}^{k−1}c(1,i)
∈ K^* for k = 1..E−1, so {1,v,…,v^{E−1}} is a K-basis of 𝒜(T) and v^E = ζ_T:

    **𝒜(T) ≅ K[v]/(v^E − ζ_T) as a K-algebra — at EVERY composite stage.**

So "𝒜(T) is NOT F′[u′]/(u′^E − ζ′)" cannot be read as an abstract-isomorphism
claim; it is (and, in its own adjudication procedure, always was) a claim about
the ANCHOR-INDEXED presentation — see §6. Nothing measured is re-scored by this;
what is corrected is a display, exactly as J-B's JB-BOX-1 corrected the J-B(iii)
display.

---

## §6. THE CYCLIC FENCE, RESTATED AS A GENRE LAW (and kept consistent with the byte-frozen record)

The blueprint carries the fence as LAW: *at composite stages 𝒜(T) is NOT
F′[u′]/(u′^E − ζ′) (adjudicated NOT-CYCLIC at 22/28 towers, value set
{z₁, z̄, z̄z₁^b}, byte-frozen); only the last-read layer is cyclic.* The
instrument, computing the same adjudication from a completely different side
(gr-side certification instead of the harness value cocycle), returned
**14 NOT-CYCLIC / 6 CYCLIC / 9 UNDECIDED**, with the 6 cyclic rows
C2A/C2E/C2G/C2J/C3A/C4A. Both records stand. Here is the law that has both as
instances.

**(CYC), the property actually adjudicated (definition, quoted from both
runners).** The anchor-indexed presentation is *cyclic* iff
(α) image(c) ⊆ {1, ζ′} for a single ζ′ ∈ K^*, **and** (β) there are integers
σ_r (σ_0 = 0) with σ_r + σ_s = σ_{r+s} + E·carry(r,s) reproducing the table.
This is the **letter-monomial** shape: the anchors are, up to ζ′-power
normalization, the power basis of one generator — precisely the shape D-REAL
supplies one level down (K_{m+1}[u]/(u^{e_m} − z̄), anchors = powers of u).

**LAW JC-CYC (the refinement; each part graded).**

* **(a) [PROVED, general m]** As an abstract K-algebra 𝒜(T) ≅ K[v]/(v^E − ζ_T)
  always (JC-F1). Hence the fence's content is (CYC), not abstract cyclicity, and
  **the operative dead route is the letter-monomial one**: assuming the composite
  carrier is D-REAL's shape with a single letter ζ′ and the carry pattern. The
  design note's S4 dead end ("one-anchor-unit normalization does not trivialize a
  coset progression") is exactly this, and it stays dead.
* **(b) [PROVED, general m — the obstruction direction]** If the measured value
  table has two distinct non-1 values, (CYC) fails by (α). With JC-INNER's law
  image(c) = {z̄^δ∏_j z_j^{D_j}}, this happens as soon as the stage realizes two
  multiplicatively distinct (δ, D)-words — which is the generic composite
  situation and is why 14/29 (instrument) and 22/28 (byte-frozen strata probe)
  come back NOT-CYCLIC.
* **(c) [PROVED, general m — the twist-blind direction]** If |K| = 2 then
  K^* = {1}, so c ≡ 1 and (CYC) holds with ζ′ = 1, σ ≡ 0. Likewise if the table
  has at most one non-1 value AND (β) is solvable, (CYC) holds by definition.
* **(d) [MEASURED, m ≤ 3 — ONE-DIRECTIONAL; corrected by this note's own battery,
  §9.2 finding 1]** On both rosters the cyclic side is CONTAINED in the
  twist-blind/collapse geography: every CYCLIC row has \|K\| = 2 (C4A), or
  g_m = 1 so that K_{m+1} = K_m and z̄ ∈ ⟨z_1⟩ (C2A/C2E/C2G/C3A), or e_0 = 1
  (C2J) — 0 violations of "CYCLIC ⟹ collapse" on 29 rows. **The CONVERSE IS
  FALSE and this note does not claim it**: 13 collapse-geography rows are
  NOT-CYCLIC (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C),
  by two visible mechanisms — ≥ 2 distinct non-1 values (up to 7 on I4C), or a
  single value whose carry pattern no integer relabeling realizes (C2C, C3I). The
  decidable designated g_m = 2 row came back NOT-CYCLIC (C2I); C4I is UNDECIDED
  at E = 16 (compute fence, not a finding). **The general form of the inclusion —
  CYCLIC ⟹ collapse at every m — is OPEN (JC-BOX-5), and its measured resolution
  is low: only 2 of 29 rows lie off the collapse geography.**
* **(e) Consistency with the byte-frozen record, explicit.** The 22/28
  adjudication and its value set {z₁, z̄, z̄z₁^b} are **unamended**; no row is
  re-scored here; the instrument's 14/6/9 is a different roster and a different
  computation, and it reproduces the same SPLIT SHAPE (cyclic only where the
  twist collapses). The fence's program consequence is unchanged: **any route
  through a letter-monomial cyclic presentation at a composite stage is DEAD**,
  and (b) now says why — the cocycle needs the full inner (δ, D_j) word, not one
  letter.

**Consequence for the case split.** The genre column "cyclic / not-cyclic /
undecided" is carried into §7, and the cyclic side is *not* only the last-read
layer: it includes composite stages whose residual tower collapses (g_m = 1 ⟹
K_{m+1} = K_m). That was the instrument's M5, and it is now a stated law with a
proved obstruction direction.

---

## §7. THE CASE SPLIT (derived FROM the instrument's genre censuses; the case list matches the observed genre list)

| # | genre (as the instrument's censuses name it) | rows / pairs | this note's status |
|---|---|---|---|
| 1 | g_m ≥ 2, δ = 0 | C2B/C2I/C3I/C4I…; the majority of pairs on those rows | JC-CARRY-m + JC-INNER; RAW-solvable; canonical outer/inner split (1,z̄,…,z̄^{g_m−1} a K_m-basis) — **PROVED** |
| 2 | g_m ≥ 2, δ = 1 | the carry-boundary pairs on g_m = 2 rows | δ = 1 < g_m ⟹ still RAW-solvable (this is the smoke correction that sharpened the sealed identity from {δ≥1} to {δ≥g_m}) — **PROVED** |
| 3 | g_m = 1, δ = 0 | most pairs on the 27 g_m = 1 stages | K_{m+1} = K_m collapse: value identity holds; the outer/inner split is canonical on the gr side (y-degree) but NOT recoverable from the VALUE alone — **PROVED, with the display fence** (the instrument's printer caveat S6.2) |
| 4 | **g_m = 1, δ = 1 — the TC-3 load set** | **134 of 669 pairs, 0/29 set-mismatches** | THEOREM JC-LOAD: no pre-TC-3 scalar exists; the ψ_m-relation is unavoidable — **PROVED** (this is the case that makes TC-3 load-bearing) |
| 5 | top-flat stage e_m = 1 | C4H (+ any I4x with e_m = 1) | δ ≡ 0; JC-SPAN gives deg ρ ≤ 1 instead of the singleton; sharp form **MEASURED not proved** — JC-BOX-4 |
| 6 | interior-flat legs e_j = 1, j < m | C2J, C3E, C4H | no special role: the split/anchor calculus is uniform in e_j; the [RMG] fenced-corner genre is inherited via J-B, not re-opened — **PROVED (no case owed)** |
| 7 | twist-blind \|K\| = 2 | C4A | c ≡ 1; cyclic by JC-CYC(c); MT3 skipped there (no nontrivial scalar class) — **PROVED** |
| 8 | zero-class genre (SPAN-S) | 60 samples | the TC-3 kernel ψ_m·Δ (§2.10) — **PROVED AWAY**, not a failure genre |
| 9 | DCX / non-integral-D | **0 rows, 0 pairs observed** | existence + structure PROVED (§3.2); the VALUE c_T is not claimed and has no machine support — JC-BOX-2 |
| 10 | prime-residue-field rows (MT3's 9 single-pair escapes) | 9 rows, |K| ∈ {3,5} | a tooth-resolution artifact (planted rescaling coincides with a lawful constant), not a clause genre — disclosed, JC-BOX-7 |
| 11 | UNDECIDED cyclic rows (E > 8) | 9 rows | compute fence on (β)'s relabeling search — no clause depends on them |

---

## §8. HONEST BOXES

* **JC-BOX-1 (proof scope vs machine scope).** Every clause of §§2–5 is stated
  and proved at **general m**; the machine evidence (instrument + §9) covers
  **m ≤ 3, |K| ≤ 25, g_j ≤ 2, d_0 ≤ 3, orders ≤ 4, p ∈ {2,3,5}**, base rings ℤ_p
  and F_p[[t]] (equal-characteristic rows ride construction-identity + machine
  only, no PARI leg). No clause is extrapolated FROM m ≤ 3: where a proof is
  missing the clause is fenced (JC-BOX-2, JC-BOX-4, JC-BOX-5), not extended.
* **JC-BOX-2 (off-stratum).** §3.2's existence/structure statement is strictly
  wider than [ILN]†'s scope (it holds for every window pair, DCX or not,
  D-integral or not); the VALUE statement §3.3 is exactly [ILN]†'s stratum. The
  instrument's grid contained **0 DCX and 0 non-integral-D pairs**, so the wider
  half has **no machine support whatsoever** — it is proof-only, and a hostile
  pass should attack it there first.
* **JC-BOX-3 (the literature leg, and citation precision owed).** (COORD)'s
  surjectivity/rank-one half is FGMN Thm 4.2 at composite order, quoted from the
  corpus's own pinned quotation (`GRB_ORDER2_2026-08-05.md` §S6a) and **not
  re-verified against a printed source in this session**; likewise Thm 4.8 /
  Cor 4.9 (Δ/(ψ_m) ≅ K_{m+1}) and Cor 2.7 (abscissa additivity). Their transport
  to the harness w and R is W-1 (ATTEMPT). If the composite-order instance of
  Thm 4.2 failed, §§2.7–3.4 fail together. The instrument explicitly did NOT
  measure the Δ-rank refinement.
* **JC-BOX-4 (the top-flat corner e_m = 1 ∧ g_m = 1).** JC-SPAN's sharp
  conclusion (slot set = {δ}) is proved for e_m ≥ 2; at e_m = 1 the degree bound
  gives only deg ρ ≤ 1, which suffices whenever g_m ≥ 2 but NOT at
  e_m = 1 ∧ g_m = 1, where deg ρ = 0 is **measured** (C4H: all pairs
  RAW-solvable, 0 violations; family JC3 re-tests it) and unproved. JC-LOAD and
  JC-CARRY-m are therefore stated with e_m ≥ 2 and this corner is boxed OPEN.
* **JC-BOX-5 (the cyclic characterization).** JC-CYC(b)(c) are proved; the
  general form of (d)'s **inclusion** (CYCLIC ⟹ collapse geography) is OPEN, its
  measured resolution is low (only 2 of 29 rows lie off the collapse geography),
  and the **converse is FALSE** — 13 collapse-geography rows are NOT-CYCLIC
  (§9.2 finding 1). The 9 UNDECIDED rows are a compute fence. **JC-F1 (the abstract-cyclicity
  computation) is a blueprint-display correction and is REVIEW-OWED**: it must be
  adjudicated before any text repeats the fence in the abstract-isomorphism
  wording.
* **JC-BOX-6 (inherited conditionality, itemized).** [ILN]† ACCEPTED but with its
  own residuals riding through: the open engine families **(RM-m, m ≥ 2)** and
  **(W-MULT-DCX-m)**, the fenced corners, DCX-(n) excluded, standard-lift only
  (so the **(ITER-LAW-LIFT)** residual — open exactly at g_0 = 1 ∧ δ_1 = 1 —
  is displayed wherever a non-standard lift could enter). GRB/CARRY-1/D-REAL
  ACCEPTED-conditional on the GRB §0 ladder ((V1)_{≤i+1}, (KP)_{≤i−1},
  (H-CHAIN)) + §3.3 [T] pins. W-1/W-2/J-A/J-B at ATTEMPT (0/2), and §3.3's germ
  display additionally rides JB-BOX-2's geography ((VD-m) free only at m ≤ 1;
  JA-VDIND at m ≥ 2; JA-BOX-2's (R-coll) at m ≥ 3; the pinned-ℓ orbit;
  q ≤ qcap) and JB-BOX-4's g_m = 1 fence for Ĉ_m.
* **JC-BOX-7 (standing fences; nothing fires).** Statements are for γ in the
  window W at attained weights (outside, gr_γ = 0 and no anchor exists); E > 1
  throughout; **no gate fires and none retires** — DITERSUP §S3 gate J3b stays
  BLOCKED-ON-CARRIER-TIE (§10 displays the tie it needs), the Asvin P0
  application gate stands; no `.lean` file is touched; no density/menu/count
  statement is made; MT3's 9 single-pair escapes and the 9 UNDECIDED cyclic rows
  are disclosed above; **own acceptance counter 0/2** — nothing here may be
  consumed at proof grade before its hostile arc.

---

## §9. MACHINE BRACKET

### 9.1 SEALED PREDICTIONS (commit 1; battery NOT yet run)

Runner: `verification/openmath/grt_jc_checks.py`, whose docstring carries the
authoritative preregistration and **is part of this seal**. It imports the
instrument's tower/stage construction (`grt_jc_probe.ROSTER`/`Stage`, the same 29
rows) and then tests **this note's clauses**, several of which the instrument
never measured. Deterministic, exact arithmetic, no randomness.

| family | the note's clause it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext `install()`+`check_pins()`+`agreement_gate()` (standing rule) | **0** |
| JC1 | LEMMA JC-PER + JC-DOM's w(π) = E: φ_{γ+kE} == π^k φ_γ byte-for-byte at k = 1,2,3; s-tuple E-periodic; u_1 ↦ u_1+k | **0** |
| JC2 | LEMMA JC-FIB: the s-tuple map is injective on E consecutive γ (⟹ bijection ℤ/E ≅ ∏ℤ/e_j), s_{j+1} ∈ [0,e_j) | **0** |
| **JC3** | **THEOREM JC-SPAN, the note's NEW sharp prediction**: the on-line slot set of φ_γφ_{γ′} at its own weight is EXACTLY {δ}, δ ∈ {0,1}, slot-δ digit u ≠ 0 in K_m; w(φ_γφ_{γ′}) = γ+γ′ | **0** on e_m ≥ 2 rows |
| JC3-FLAT | the e_m = 1 corner (JC-BOX-4): min slot = 0 is PROVED (scored); "max slot = 0" is the unproved sharp form | **0 scored violations**; census reports the count of pairs with a slot > 0 — **measured, NOT scored** |
| JC4 | LEMMA JC-SCAL + §4.1's normalization: slot set of Λ_N(c) == {i : c_i ≠ 0} ⊆ {0..g_m−1} with slot-i digit == c_i; **𝑅_N(X_N) == 1 exactly** | **0** |
| JC5 | LEMMA JC-ANCHMON: Σ_{j<m}s_{j+1}degΦ_j < degΦ_m; the anchor's Φ_m-development is the single digit at abscissa s_{NR}; slot set {0}; a_λ ≠ 0 | **0** |
| JC6 | COROLLARY JC-PSIKER: w(Φ_{m+1}) == wΦ_{NR}; 𝑅(Φ_{m+1}) == ψ_m coefficientwise; read == 0; and Φ_{m+1}+φ_λ vs φ_λ = equal reads, different classes | **0** |
| JC7 | COROLLARY W-9: the mod-E 2-cocycle identity (E \| G_0 so the classes match), the integer carry identity δ(r,s)+δ(r+s,t) = δ(s,t)+δ(r,s+t), and the E-fold chain c(φ_1^E) == ∏_{k=1}^{E−1}c_val(γ_1,kγ_1) (monodromy = gauge period, two ways; E ≤ 8) | **0** |
| JC8 | LAW JC-CYC + FINDING JC-F1: a CYCLIC verdict ⟹ the collapse geography (\|K\| = 2 ∨ g_m = 1 ∨ e_0 = 1); every structure constant is a UNIT (so JC-F1's power basis exists) | **0** |
| **MJ1** | tooth: "TC-3 is never load-bearing" (a RAW scalar on every pair) | **≥ 1 firing**; and 0 pairs where RAW fails at δ < g_m or succeeds at δ ≥ g_m (either would REFUTE JC-LOAD) |
| **MJ2** | tooth: mutated periodicity φ_{γ+E} == π²φ_γ | **≥ 1 firing per row** |
| **MJ3** | tooth: mutated scalar image "slots ⊆ {0}" | **≥ 1 firing per g_m ≥ 2 row** |
| **MJ4** | tooth: "the read is injective on gr_λ" (read(wΦ,Φ_{m+1}) ≠ 0) | **≥ 1 firing per row** |
| **MJ5** | tooth: mutated span law "slot set == {δ+1}" | **≥ 1 firing per row** |

A silent tooth is a RED. Exit code = (violations + silent teeth).

**BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest; part of this seal).** One
3-row smoke of this runner (C2A / C2I / C3A — one g_m = 1 wild row, one g_m = 2
row, one m = 2 row) ran during construction, elapsed 0.2 s. Result:
**0 violations in every family (JC1 147, JC2 32, JC3 224, JC4 30, JC5 48,
JC6 12, JC7 81, JC8 99 samples), all five teeth FIRED** (MJ1 8, MJ2 16, MJ3 2,
MJ4 3, MJ5 56 firings). Specifically: JC3's sharp slot-span prediction held on
**56/56** pairs; MJ1 found **8 of 32** tested pairs with no pre-TC-3 scalar and
**all 8 were in the δ ≥ g_m load set** (JC-LOAD's dichotomy, both directions);
JC7's E-fold chain matched the orbit product on all three rows
(C2A z̄¹ = z̄¹, C2I z̄² = z̄², C3A z̄² = z̄²); JC8 returned CYCLIC for C2A and
C3A (both g_m = 1 = collapse geography) and NOT-CYCLIC for C2I (g_m = 2) —
**agreeing row-for-row with the instrument's independent MT2 verdicts**. **No
sealed prediction was changed by the smoke, and no clause of §§2–6 was edited
because of it.** Two construction-time design choices were fixed BEFORE the
smoke and are disclosed: (i) JC7/JC8 use the full E² constant table when E ≤ 8
and the probe's designed subset above it (at E > 8 the adjudicator returns
UNDECIDED, so a truncated table cannot manufacture a CYCLIC verdict);
(ii) per-row tooth obligations are scored as their own family (TOOTH-ROW).

### 9.2 VERDICT (commit 2 — written FROM the artifacts)

**Artifacts:** `verification/openmath/grt_jc_checks_output.txt`,
`grt_jc_checks_results.json` (deterministic; 29 rows, elapsed **2.0 s**; seal
commit `6ad01d1`). **ALL 10 FAMILIES GREEN — 0 violations, every sealed
prediction hit exactly; ALL FIVE TEETH FIRED (no silent tooth).**

| family | the clause | samples | violations | verdict |
|---|---|---|---|---|
| EXT-GATE | engine_ext standing rule | 1 | 0 | GREEN (0 new) |
| JC1 | JC-PER + w(π) = E | 2,594 | **0** | GREEN — π^k-periodicity byte-for-byte at k = 1,2,3, s-tuple periodic, u_1 ↦ u_1+k, w(π) = E on all 29 rows |
| JC2 | JC-FIB | 570 | **0** | GREEN — the s-tuple map is injective on E consecutive γ on every row |
| **JC3** | **JC-SPAN (the note's new sharp prediction)** | 2,484 | **0** | GREEN — **slot set == {δ} on 609/609 pairs** with e_m ≥ 2; δ ∈ {0,1} everywhere; u ≠ 0 everywhere |
| JC3-FLAT | the e_m = 1 corner (JC-BOX-4) | 24 | **0** scored | GREEN; **census: 0 of 24 pairs have a slot > 0** — the unproved sharp form is measured true on the top-flat row (C4H) |
| JC4 | JC-SCAL + the lift normalization | 443 | **0** | GREEN — Λ_N(c)'s slot set == supp(c) ⊆ {0..g_m−1} with slot-i digit == c_i, and 𝑅_N(X_N) == 1 exactly, on every row and every c ∈ K |
| JC5 | JC-ANCHMON | 855 | **0** | GREEN — the telescoping degree bound, the single-digit development, slot set {0}, a_λ ≠ 0 |
| JC6 | JC-PSIKER | 116 | **0** | GREEN — w(Φ_{m+1}) = wΦ_{NR}, 𝑅(Φ_{m+1}) == ψ_m coefficientwise, read == 0, and the equal-read/different-class pair |
| JC7 | W-9 cocycle semantics | 581 | **0** | GREEN — **261 triples** satisfy both the K^*-cocycle identity and the integer carry identity; the **E-fold chain matched the orbit product on all 15 rows with E ≤ 8** |
| JC8 | JC-CYC + JC-F1 | 898 | **0** | GREEN — every structure constant a unit (so JC-F1's power basis exists on every row); no CYCLIC verdict off the collapse geography |
| MJ1 | tooth: "TC-3 never load-bearing" | 333 tested | **103 firings** | FIRED — 103 pairs have NO pre-TC-3 scalar and **all 103 lie in the δ ≥ g_m load set**; 0 anomalies in either direction (JC-LOAD's dichotomy, machine-confirmed both ways) |
| MJ2 | tooth: φ_{γ+E} = π²φ_γ | 285 | **285 firings** | FIRED on every row |
| MJ3 | tooth: "Λ_N slots ⊆ {0}" | 6 | **4 firings** | FIRED on every g_m ≥ 2 row (2 of the 6 opportunities are the c's whose slot 1 is genuinely empty) |
| MJ4 | tooth: "the read is injective on gr_λ" | 29 | **29 firings** | FIRED on every row — read(wΦ, Φ_{m+1}) = 0 everywhere |
| MJ5 | tooth: slot set == {δ+1} | 633 | **633 firings** | FIRED on every pair |

**The cyclic split reproduced: CYCLIC 6 / NOT-CYCLIC 14 / UNDECIDED 9**, with the
cyclic rows **C2A / C2E / C2G / C2J / C3A / C4A** — *the same six rows, and the
same 14/6/9 split, as the instrument's MT2*. **Disclosure (resolution, honest):**
this battery's constant table is the harness ratio c_val (via the probe's
`Stage.cval`), whereas the instrument's MT2 used the fence-clean gr-side
certified constant c_gr; the two tables agree because W-8/P5-OB6 says
c_gr = c_val (0/669), so the verdict-identity is a *consistency* check of W-8,
not a second independent measurement of the split. The adjudicator itself is a
fresh transcription.

**TWO BATTERY-DRIVEN FINDINGS, applied above:**

1. **The collapse geography does NOT imply cyclic** (the converse of JC-CYC(d) is
   FALSE): 13 rows sit in the collapse geography and still come back NOT-CYCLIC
   (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C). Two
   mechanisms are visible in the printed table: **≥ 2 distinct non-1 values**
   (C2B/C2D/C2H/C3D/C3E/C3F/C3H/C4B/C4G/I4B/I4C — up to **7** distinct values on
   I4C) and **a single value whose carry pattern is not realizable by any integer
   relabeling** (C2C, C3I). §6(d) is stated one-directionally because of this,
   and JC-CYC(b)'s obstruction direction is what does the work.
2. **The law's resolution on this roster is low and is disclosed**: only **2 of
   29 rows (C2I, C4I) are OFF the collapse geography**, and both are
   NOT-CYCLIC / UNDECIDED — so "CYCLIC ⟹ collapse" was tested against few
   potential counterexamples. A hostile pass should build g_m ≥ 2 rows with
   small tables.

---

## §10. GRADE BOX, THE CONDITIONALITY STACK, AND CONSUMERS

### 10.1 Per-clause grades

| clause | content | grade |
|---|---|---|
| **W-6** | carry-target existence: TC-1 legitimate (JC-DOM), TC-2 legitimate + ℤ→ℤ/E collapse (JC-GAUGE), the surviving fibred index (JC-FIB), OB-2 periodicity (JC-PER), the anchor-monomial and scalar-image lemmas, **THEOREM JC-LOAD** (TC-3 load-bearing exactly at δ ≥ g_m) and **COROLLARY JC-PSIKER** (TC-3 is not a relabeling) | **PROVED at general m**, attempt 0/2, one located box: the top-flat corner e_m = 1 ∧ g_m = 1 (JC-BOX-4) |
| **W-7** | Ψ: OB-2 **PROVED general m**; OB-3 existence/structure (constant = (K_m^*-unit)·z̄^δ) **PROVED general m on ALL window pairs**; OB-3 value (inner = ∏_{j≤m}z_j^{D_j}) **PROVED general m on [ILN]†'s scored stratum**; OB-4 independence **PROVED general m** (Δ-rank input literature-carried); OB-5 fence **DISCHARGED as architecture** | **PROVED on the stated scopes**, attempt 0/2; the germ split displayed honestly (val law CONFIRMED on 27 stages; H-D REFUTED 138/669) |
| **W-8** | harness-val = TC-read (OB-6), with every line-wise normalization cancelling; J-C(iii) residue chain | **PROVED at general m** on (COORD)+(MULT)+JC-SPAN+JC-SCAL+R3, attempt 0/2 |
| **W-9** | cocycle semantics: descent to ℤ/E, COR-2 = gr-associativity, the {0,1} carry cocycle, the twisted-group-algebra display, COR-4 monodromy = the gauge period | **PROVED given W-6..W-8** (S-priced, as the blueprint priced it), attempt 0/2 |
| **cyclic fence** | LAW JC-CYC: abstract cyclicity always (JC-F1, **review-owed display correction**); the adjudicated (CYC) property is the letter-monomial one; obstruction direction PROVED; twist-blind direction PROVED; the inclusion CYCLIC ⟹ collapse MEASURED (m ≤ 3, 0/29, low resolution) with its general form OPEN and its **converse REFUTED** by this note's own battery (13 collapse rows NOT-CYCLIC) | **REFINED, not refuted**; byte-frozen 22/28 record unamended |

### 10.2 The conditionality stack (one line, then itemized)

**`[ILN]† ACCEPTED (scored stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), (ITER-LAW-LIFT), standard-lift only) + GRB/CARRY-1/D-REAL ACCEPTED-conditional (§0 ladder + [T] pins) + FGMN Thm 4.2 / Thm 4.8 / Cor 2.7 CITED (composite order; numbering re-verification owed) + W-1/W-2/J-A/J-B ATTEMPT 0/2 (with JB-BOX-2's (VD-m) geography) ⟹ this note, attempt 0/2.`**

Nothing in §§2–6 is unconditional. The *weakest* links, ranked for a hostile
pass: (1) FGMN Thm 4.2 at composite order + its transport by W-1 — everything
coordinate-based dies with it (JC-BOX-3); (2) the off-stratum existence claim
with zero machine support (JC-BOX-2); (3) the top-flat corner (JC-BOX-4);
(4) JC-F1's display correction (JC-BOX-5).

### 10.3 Consumers — named, with what each may and may NOT take

* **DITERSUP §S3 gate J3b (BLOCKED-ON-CARRIER-TIE).** This note supplies exactly
  the missing item (ii) of J3b's three-item residual list — "the gr(w₂) semantics
  wrapper", i.e. §S3's *missing tie* — at **attempt grade 0/2 and at general m**,
  not only at order 2. **The gate does NOT retire here and this note does not
  retire it**: J3b retires only when (J-C)(ii) survives its own hostile arc, and
  its other legs (BLOCKED-ON-APPLICATION, the (ITER-LAW-LIFT) residual at
  g_0 = 1 ∧ δ_1 = 1, orders ≥ 3 of DITERSUP's own queue) are untouched. **The tie
  is displayed, the gate stands.**
* **`Scaffold/HDischarge/H1/DIterCarrier.lean` — JS1 / JS2.** JS1
  (`gateJS1_cocycle_assoc`, PROVED with the honest `hTrack : D.OuterTrackAdd`
  hypothesis) is the harness-side 2-cocycle/associativity gate; §5's COROLLARY
  W-9(i)(ii) is its **semantic home**: the cocycle identity is gr-associativity,
  and the outer-track additivity JS1 needed as a hypothesis is §5(ii)'s integer
  carry-cocycle identity on the δ-part. JS2 (`gateJS2_dreal_degeneration`,
  PROVED, no added hypotheses) is the e_0 = 1 D-REAL degeneration, which §6's
  genre law places in the *collapse geography* (flat control rows). **No Lean
  hypothesis is discharged by this note** — the compiled file's `hTrack` still
  needs a Lean-level supplier, and this note is not it (attempt grade, no Lean
  layer exists for gr(w_{m+1})).
* **MOVES B2-DEF.** Its accepted induction gains its intended **semantic home**:
  the level-indexed carry data B2-DEF manipulates is, by W-7/W-8, the structure
  constant of the anchor basis in gr(w_{m+1}) — the outer slot shift plus the
  inner K_m-unit. Display only; B2-DEF's own statements and grade are unchanged.
* **The (H1)(a) GR-B carry side.** §§3–4 give the composite-stage carry law that
  the (H1)(a) package's carry side asks for, on the scored stratum and at attempt
  grade, riding GRB's own §0 ladder. It does **not** discharge (H1) — the
  faithfulness handoff is J-D1 (W-12), not composed here.
* **The MOVES B2-FINAL bridge and bare-interface discharges stay DEAD** (brief
  fence 3): nothing above routes through them, and the option-(ii) vacuity trap
  (P1-FLAG-1/J3B-FLAG-1) is not re-opened.
