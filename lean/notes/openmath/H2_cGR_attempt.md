# H2-P1 — the (c-GR) graded-level junction identification: lemma + proof (attempt, rev 0; Fable prover H2-P1, 2026-08-01)

**Unit spec:** `lean/blueprints/HDISCHARGE_H2.md` §3.3 step (c-GR) + §6 unit
H2-P1 (wave 1, PAPER unit). **Authority for the target clause:**
`O9_phaseB_verifybrief_rev5.md` §5.4 clause (c) and its mechanism note
("NOT A PROOF" there — this note is the proof-attempt that upgrades it).
**Corrected input list honored (H2 blueprint review finding 4):** the
identification consumes (GR-B)(2′)'s march normalization in addition to
(3)+(4)+(P4), and a precise what-ρ-fixes lemma (Lemma ρ-FIX below) is
displayed, not presumed.

**What this note claims.** Lemma c-GR below: at the GRADED level, on every
parent-point fiber of a joint stratum, the window chain's right-end digit
read is a parent-determined NONZERO constant of F_{r+1} — identified, up to
one displayed parent-shape-fixed normalizer, with the ψ_r-cofactor value of
R_r(f) at the marked root. PROVED-CONDITIONAL: conditional exactly on
(GR-B) at the O-9 consumption state (OPEN at orders ≥ 2, cited
clause-by-clause) plus the pinned (P2)/(P4) and O-9's proved A1/TRI/LED
layer. Gate: fresh-context hostile pass (companion brief
`H2_cGR_verifybrief.md`).

**What this note does NOT claim.** (i) NO finite-level statement: the
descent of this graded pin to the working-level-N digit read is (c-TR) =
**(TRANS-DEEP)(J)** (blueprint §5), untouched here; (FRESH)(c) remains OPEN
as a finite-level clause. (ii) NO discharge of (GR-B): every firing is a
citation of the displayed open package. (iii) NO claim at the coarse-ρ
scope: the pin is proved constant per PARENT POINT (level-N₀ class); §1.4
shows per-point is the maximal true scope and §5 that it is exactly what
CEN-J §6.4 step 3 consumes.

---

## 1. Setting, the read, and the two scope conventions

### 1.1 Frame (verbatim pins from O-9 rev-5 §§1–2)

O a complete DVR with finite residue field F_q (q = p^δ); t a type of order
r ≥ 1 with residue tower F_q = F₀ ⊆ … ⊆ F_{r+1}, residual keys
ψ_i ∈ F_i[y] irreducible, F_{i+1} = F_i[y]/(ψ_i); d = [F_{r+1} : F_q],
e = e₁⋯e_r; φ = φ_{r+1} a representative of t (GMN Def 2.12:
R_r(φ) ∼ ψ_r), m = deg φ = e·d; w = v_{r+1}, V̂ = w(φ). For monic f of
degree n: the φ-development f = Σ_{k≤ℓ} a_k φ^k (deg a_k < m), heights
u_k := w(a_k) + k·V̂ (u_k := +∞ at a_k = 0). D a level-N stratum datum over
t: chain vertices (k₀,U₀) < … < (k_s,U_s), s ≥ 1 faces of strictly
increasing negative slopes, thresholds β_k per the repaired
(STRICT)/(READ)/(TAIL) table, right-tail u_k ≥ U_s at k > k_s, left-tail
cutoff at k < k₀. R_i(f) ∈ F_i[y] the GMN order-i residual polynomials in
the realized frame's normalization. Standing hypotheses of the consuming
theorem (CEN-J): (DET) at N, and (DET) over the parent's own reads at N₀.

**The marked root.** z_r := y mod (ψ_r) ∈ F_{r+1}. Evaluation of
P ∈ F_r[y] at z_r is reduction mod ψ_r; since F_r[y]/(ψ_r) = F_{r+1} is a
field, **P(z_r) = 0 ⟺ ψ_r | P**. (†0)

**The read.** r_β(a) ∈ F_{r+1} is O-9 §5.1's digit read of a coefficient a
(deg a < m, w(a) ≥ β) — via the (GR-B) line clause,
in(a) = ϕ_{w(a)}·c(a) with r_β(a) := c(a) if w(a) = β, else 0. The
JUNCTION READ of f is r_{β_{k_s}}(a_{k_s}). All reads in this note are in
the COHERENT anchored-march normalization ((GR-B)(2′)); the slot-fresh
alternative is the 1,818×-machine-refuted reading (CU-1 fence, O-9 §1).

### 1.2 The (GR-B) package as consumed (O-9 §1 pinned display; GD23 rev-4 §7.2 source)

At the O-9 consumption state (state order r+1): the localized graded ring
gr := gr(w)_loc with degree-0 polynomial subring Δ = F̃[ȳ] (F̃ the
package's displayed coefficient field — §4 note (N2): the proof is
insensitive to the F̃ = F_r vs F_{r+1} index reading); the invertible
homogeneous anchor monomials ϕ_α, ϕ(f) = ϕ_{w(f)}·ȳ^{j₀(f)},
j₀(f) = ⌊s₀(f)/e_r⌋; ψ̂ := in_w(φ_{r+1}), homogeneous PRIME of gr (the
(KPirr) display); the residual operator R^{gr}, total on nonzero
homogeneous elements, with:

* **(2′)** in(f) = ϕ(f)·R^{gr}(in f)(ȳ) for f satisfying the creating
  read's realized conditions; R^{gr}(in f) ∼ R_{λ_r}(f) = R_r(f), where
  the ∼-dictionary is the declared twist dictionary and — by the march
  clause ("one fixed step, LINEAR in κ") through O-9 §6.1's TYPE-MARCH
  consequence — has the geometric shape
      R^{gr}(in f) = τ(α, s₀) · R_r(f)(ρ_m z),                    (†1)
  with ρ_m ∈ F̃^× the state's ONE stride ratio and τ(α, s₀) ∈ F̃^× a
  normalizer depending only on (the realized frame, the weight α = w(f),
  the side's initial abscissa s₀(f)). (†1)'s shape-and-dependence claim is
  exactly (2′)'s march content — the clause review finding 4 added to the
  input list; it is a CITATION of the package, not a derivation.
* **(3)** R^{gr}(ψ̂) ∼ ψ_r (the representative's residual pin).
* **(4)** ord_{ψ_r}(R^{gr}(α)) = ord_{ψ̂}(α) (faithfulness; consumed per
  the disposition in §3, step F).
* **(LINE)** the line clause for deg a < m as O-9 §5.1 consumes it:
  in(a) = ϕ_{w(a)}·c(a), c(a) the F_{r+1}-digit.

Pinned unconditional imports: **(P2)** (w computed by minima on the
φ-development), **(P4)** (ω_{r+1}(f) = length of N⁻_{r+1}(f) =
ord_{ψ_r}(R_r(f)), first-attainment form).

### 1.3 Parent points

A **parent point** ρ̂ is a residue class f mod π^{N₀} lying in the
parent-realization stratum of ρ. The **fiber over ρ̂** at level N is
{f mod π^N : f ≡ ρ̂ (π^{N₀}), f in the joint stratum (D over ρ)}.

### 1.4 Scope display: per-point is the maximal true scope

(FRESH)(c) says "a ρ-determined nonzero constant". If "constant" were read
across a whole coarse parent-REALIZATION stratum, the clause would be
FALSE already at the proved r = 0 instance: parent = M08's x^e-block at
level N₀ = 1 with n > e (free end), parent stratum =
{f̄ = x^e·u(x) : u monic, u(0) ≠ 0}; the junction read is ā_{k_s} = u(0),
which VARIES across the stratum. It is constant on each parent POINT
(fixed f̄). So the honest clause — and everything §6.4 step 3 consumes
(§5) — is the per-point form. This note proves the per-point form.
Realizations that pin all parent reads (the K2 harness's realizations do)
get the constant uniform over the realization for free.

---

## 2. Lemma ρ-FIX (what ρ fixes)

**Lemma ρ-FIX.** Fix the realized frame (φ₁,…,φ_{r+1}; ψ₀,…,ψ_r) and a
parent point ρ̂, and assume (DET) over the parent's own reads (level N₀).
Then:

* **(i) [reads]** every datum the parent's conditions key — for each
  i ≤ r: the order-i principal-polygon data (faces, abscissa frames, in
  particular the λ_i-side's initial abscissa s₀ and length) and the
  marched digit reads along the realized sides — is a function of
  f mod π^{N₀} alone; hence so is each residual polynomial R_i(f) ∈ F_i[y]
  (realized normalization). On the fiber over ρ̂ they are constants; write
  R_r(ρ̂) := R_r(f)|_{fiber}.
* **(ii) [multiplicity + cofactor]** if f lies in the joint stratum over
  ρ̂, then ord_{ψ_r}(R_r(ρ̂)) = k_s; writing R_r(ρ̂) = ψ_r^{k_s}·U with
  ψ_r ∤ U, the **marked-root cofactor value**
      c_par(ρ̂) := U(z_r) ∈ F_{r+1}                                (†2)
  is well-defined, depends on ρ̂ only, and is NONZERO.

*Proof.* (i) The coefficients of R_i(f) are the marched digit reads of f
along the realized order-i side, and the abscissa frame is polygon data —
the (2′) march display at order i (= the pinned FGMN Thm 4.2 coefficient
clause: the κ-th coefficient is the residue of the stride digit at
abscissa s₀ + κ·e_i read through the marched normalizer); both are among
"the parent's own reads". The standing hypothesis (DET) over the parent's
own reads says precisely that every such read has its threshold within the
level-N₀ ledger scope (LED(i), proved layer), i.e. is a well-defined
function of f mod π^{N₀}. [Scope honesty: the r-fold A1/TRI bookkeeping
COMPOSITION is H2-P2's writing duty; here we consume only the standing
hypothesis's meaning — each parent-keyed read is level-N₀-determined —
which is CEN-J's own §6.4-step-1 usage, not new content.]

(ii) f in the joint stratum ⟹ N⁻_{r+1}(f) has exactly D's chain, whose
principal part ends at abscissa k_s ⟹ ω_{r+1}(f) = k_s; (P4) gives
ord_{ψ_r}(R_r(f)) = ω_{r+1}(f) = k_s. Factor R_r(ρ̂) = ψ_r^{k_s}·U,
ψ_r ∤ U (exactness of ord). By (†0), U(z_r) ≠ 0. ∎

---

## 3. Lemma c-GR (the graded-level junction identification)

**Lemma c-GR.** Assume (GR-B) as displayed in §1.2 (clauses (2′) with the
march shape (†1), (3), (4), (LINE)), and let D be a free-end datum
(k_s ∈ K_D; monic top: §4 note (N4)). Fix the realized frame, a parent
point ρ̂, and let f be ANY member of the joint stratum fiber over ρ̂ at
level N. Then, in gr = gr(w)_loc:

* **(c-GR-1) [multiplicity]** ord_{ψ̂}(in f) = k_s;
* **(c-GR-2) [pin value]** the junction read satisfies
      r_{β_{k_s}}(a_{k_s}) = 𝔫 · c_par(ρ̂)  in F_{r+1}^×,          (†3)
  where 𝔫 ∈ F_{r+1}^× depends only on (the realized frame, D, the
  discrete parent shape) — on NOTHING f-dependent, and not even on ρ̂
  within one discrete shape;
* **(c-GR-3) [(FRESH)(c), graded shadow]** hence the junction read is ONE
  nonzero constant of F_{r+1} on the whole fiber over ρ̂: parent-
  determined, never a free unit.

*Proof.* Seven steps; every firing bracketed.

**Step 0 (scope of (2′) on the fiber).** Membership in the joint stratum
(D over ρ) includes the parent-membership conditions, which are the
creating read's realized conditions at the state [(O-9 §2: "D over the
parent realization ρ"; GD23 (2′) scope restriction (a))]. Moreover
ω_{r+1}(f) = k_s ≥ 1 (k₀ < k_s in D), so ψ_r | R_r(f) and f's λ_r-side is
nonempty. So (2′) fires on in(f); it fires on in(φ_{r+1}) = ψ̂ since the
representative's λ_r-side is its defining datum [GMN Def 2.12].

**Step 1 (the two (2′) displays).** [(2′)-f, (†1), ρ-FIX]:
    in(f) = ϕ(f)·P_f(ȳ),   P_f(z) = τ_f·R_r(ρ̂)(ρ_m z)
             = τ_f·ψ_r(ρ_m z)^{k_s}·U(ρ_m z),
using R_r(ρ̂) = ψ_r^{k_s}U [ρ-FIX(ii)] and exact multiplicativity of
substitution: (ψ_r^{k_s}U)(ρ_m z) = ψ_r(ρ_m z)^{k_s}·U(ρ_m z). Here
τ_f := τ(α, s₀): α = w(f) is D-data (Step 3 below pins w(f) = u_{k_s},
whose normalized value is U_s), and s₀ = s₀(f) is parent-polygon data,
ρ̂-fixed by ρ-FIX(i) — indeed discrete-shape data. Write
Ψ(z) := ψ_r(ρ_m z): irreducible over F̃ of degree deg ψ_r (composition
with the unit rescale z ↦ ρ_m z), frame-fixed.
[(2′)-φ + (3)]:
    ψ̂ = in(φ_{r+1}) = ϕ_φ·P_φ(ȳ),   P_φ = τ_φ·Ψ,
with τ_φ ∈ F̃^× frame-fixed ((3) pins P_φ ∼ ψ_r; the march shape (†1) at
the frame element φ_{r+1} places the pin in the marched normalization Ψ).

**Step 2 (the transported factorization).** Anchors are invertible in gr
[(GR-B) anchor clause], so Ψ(ȳ)^{k_s} = ψ̂^{k_s}·(ϕ_φτ_φ)^{−k_s}, and
Step 1 gives, in gr:
    in(f) = 𝔪 · ψ̂^{k_s} · Ũ(ȳ),   Ũ(z) := U(ρ_m z),
    𝔪 := ϕ(f)·ϕ_φ^{−k_s}·τ_f·τ_φ^{−k_s}                            (†4)
— 𝔪 an invertible homogeneous element of gr, fixed by (frame, D,
discrete parent shape). In particular ψ̂^{k_s} | in(f).

**Step 3 (the development display).** The chain decreases strictly to
(k_s, U_s); left-tail and off-line slots sit strictly above their lines
> U_s; right-tail slots have u_k ≥ U_s. So min_k u_k = U_s, attained at
k_s and possibly at slots k > k_s. Right-end vertex attainment:
u_{k_s} = U_s exactly — else the lower hull's principal part would not
have its right-end vertex at (k_s, U_s) and f would key a different
stratum [§2 keying; the vertex-digit-nonvanishing note of O-9 §5.2]. Hence
w(a_{k_s}) = β_{k_s} and the junction read is c(a_{k_s}) ≠ 0. [(P2)]:
w(f) = min_k u_k = U_s-value = u_{k_s}; therefore f ∉ P⁺_{w(f)} and, the
grading map P_{w(f)} → P_{w(f)}/P⁺_{w(f)} being additive,
    in(f) = Σ_{k : u_k = w(f)} in(a_k)·ψ̂^k ≠ 0,   all such k ≥ k_s. (†5)

**Step 4 (division in the domain).** gr is a domain and ψ̂ ≠ 0, so by
Step 2 the cofactor γ := in(f)/ψ̂^{k_s} = 𝔪·Ũ(ȳ) is well-defined, and by
(†5), γ = Σ_{u_k = w(f)} in(a_k)·ψ̂^{k−k_s} with all exponents ≥ 0.

**Step 5 (reduction mod ψ̂ — the value extraction).** ψ̂ is PRIME in gr
[(KPirr) display], so 𝔊 := gr/(ψ̂) is a domain. Reducing γ's two
displays: the k > k_s terms of (†5) die, and [(LINE)] at the junction
coefficient (deg a_{k_s} < m, w(a_{k_s}) = β_{k_s}):
    γ̄ = in(a_{k_s}) mod ψ̂ = ϕ̄_β · ♮(c(a_{k_s}))  and  γ̄ = 𝔪̄ · Ũ(ȳ)‾.
Here 𝔊's degree-0 part: ψ̂ = ϕ_φτ_φ·Ψ(ȳ) with ϕ_φτ_φ invertible forces
Ψ(ȳ) = 0 in 𝔊, so Δ's image is F̃[ȳ]/(Ψ) ≅ F_{r+1}, the iso ♮ sending ȳ
to Ψ's root z_m := ρ_m^{−1}·z_r — frame-fixed. **The march twist and the
marched root cancel:**
    Ũ(ȳ)‾ = Ũ(z_m) = U(ρ_m·ρ_m^{−1}·z_r) = U(z_r) = c_par(ρ̂).    (†6)
No residual twist survives into the value: (†6) is exact, in GMN's own
normalization of U.

**Step 6 (assembly).** Both γ̄-displays are nonzero: c(a_{k_s}) ≠ 0
(Step 3) and c_par(ρ̂) ≠ 0 [ρ-FIX(ii)], with ϕ̄_β, 𝔪̄ ≠ 0 (ψ̂ prime
divides no invertible anchor). Both sit in the same homogeneous piece of
the domain 𝔊; the ratio ϕ̄_β^{−1}·𝔪̄ is homogeneous of weight
(w(f) − k_s·V̂) − β_{k_s} = u_{k_s} − k_s·V̂ − β_{k_s} = 0, and anchor-
ratio images lie in ♮(F_{r+1}^×) [ANCH: anchors are units-times-ȳ-powers;
their 𝔊-images lie in the degree-0 field]. So with
𝔫 := ♮^{−1}(ϕ̄_β^{−1}𝔪̄) ∈ F_{r+1}^×:
    c(a_{k_s}) = 𝔫 · c_par(ρ̂),
and 𝔫 inherits (†4)'s dependence: (frame, D, discrete parent shape) only.
This is (†3) = (c-GR-2), and (c-GR-3) follows since the right side is
f-free on the fiber. (c-GR-1): ψ̂^{k_s} | in(f) is Step 2;
exactness: γ̄ = 𝔪̄·♮(c_par) ≠ 0, so ψ̂ ∤ γ. ∎

**Step F (disposition of clause (4) — displayed per the blueprint's
clause list).** The value chain above consumes (2′)+(3)+(P2)+(P4)+(LINE)+
ρ-FIX; clause (4) is consumed as the package-level faithfulness WARRANT
and cross-check, not as a link of the value chain: (a) it is what makes
ord_{ψ̂} the graded carrier of the junction multiplicity in general (the
graded shadow of (P4), independent of any stratum), licensing the very
statement (c-GR-1); (b) on the stratum it returns
ord_{ψ_r}(R^{gr}(in f)) = ord_{ψ̂}(in f) = k_s, which cross-checks (†1)'s
dictionary against (P4)'s GMN-normalized count (a DERIVED compatibility:
the dictionary twist preserves the ψ_r-order on the stratum — consistent
with, and on the stratum implied by, the package's joint satisfiability).
A verifier finding that (4) is not load-bearing on the main chain is a
finding of slack, not of error; the blueprint's input list is honored as
an upper bound.

---

## 4. Notes and displayed insensitivities

* **(N1) Where the march is load-bearing (review finding 4).** Three
  sites: (†1)'s geometric dictionary shape with FIXED (τ, ρ_m) (a
  slot-fresh per-κ twist system would break Step 1's factorization
  transport — the CU-1 1,818× fence); the anchor normalizers inside (†4);
  and the ♮-identification in Step 5. The VALUE self-corrects at (†6) —
  the only surviving normalization debt is the single constant 𝔫, which
  Lemma C renders census-irrelevant.
* **(N2) Δ-index insensitivity.** O-9 §1 displays Δ = F_{r+1}[ȳ]; FGMN
  Thm 4.8 reads Δ = F_r[y_r] at the corresponding state. The proof
  consumes only: Δ = F̃[ȳ] a polynomial ring, Ψ ∈ F̃[ȳ] irreducible with
  F̃[ȳ]/(Ψ) ≅ F_{r+1}. Under F̃ = F_r this is the ψ_r-quotient; under
  F̃ = F_{r+1}, Ψ is linear and the quotient is trivial — Steps 5–6 read
  verbatim either way. The index question is (GR-B)-internal transcription
  residue, priced there.
* **(N3) What is NOT consumed.** No surjectivity/(ADM) clause (the pin
  needs no onto-ness); no (FRESH)(a′)/(b) content; no finite-level LED
  counting beyond ρ-FIX(i)'s scope usage; no exhaustiveness. (c-TR) —
  identifying the level-N digit of a_{k_s} with this graded read's
  Teichmüller shadow — is (TRANS-DEEP)(J), open, NOT used.
* **(N4) Monic top (k_s = ℓ ∉ K_D).** a_ℓ = 1: in(a_ℓ) = the monicity
  constant, read ≡ 1, and CEN-J charges nothing (L′ accounting). (c-GR)
  is vacuous-by-design there; the displayed lemma is the free-end clause.
* **(N5) r = 0 sanity instance (the proved case).** φ = x-lift of ψ₀,
  march trivial (ρ_m = 1, τ ≡ 1, 𝒟 = K₀ per GD23's order-1 display),
  𝔫 = 1: f̄ = ψ₀^{k_s}·ū gives junction read ā_{k_s} = ū(z₀) = c_par —
  M08 §2.2's separation with the KEY1 shape, on the nose. The free-end
  block with n > e is §1.4's scope witness.
* **(N6) Falsifier posture.** All existing K2 cells are monic-top
  (ε = 0 forced by shape — O-9 §10); the discriminating numeric gate for
  the (c) family is the queued free-end CEN-J cell (blueprint H2-N1).
  Nothing in this note is contradicted or confirmed by the current runs
  beyond K2's realization-independence, with which (†3) is consistent
  (the ρ̂-dependence rides only c_par, and Lemma C kills the value).

## 5. Fit to the consumer (CEN-J §6.4 step 3)

Step 3 of O-9 §6.4 consumes exactly: per parent point, the k_s-read is
determined and nonzero (so the junction slot contributes no digit factor
and no (q^d − 1); Lemma C makes the pin's value irrelevant; the per-point
window factors are point-independent since 𝔫·c_par varies only through a
value Lemma C ignores, and the floors/exponents are shape-only by (a′)).
Lemma c-GR delivers this at the graded level; the finite-level clause
CEN-J actually reads awaits (TRANS-DEEP)(J).

## 6. Consumption map

| input | clause fired | where | status of source |
|---|---|---|---|
| (GR-B)(2′) | anchored-march identity + (†1) dictionary shape + normalizer dependence (α, s₀) | Steps 0–2, 5; (†4) | OPEN ≥ 2 (GD23 §7.2), cited |
| (GR-B)(3) | R^{gr}(ψ̂) ∼ ψ_r | Step 1 (P_φ = τ_φΨ) | OPEN ≥ 2, cited |
| (GR-B)(4) | faithfulness ord-transport | Step F (warrant + cross-check) | OPEN ≥ 2, cited |
| (GR-B) structure | anchors invertible; ψ̂ prime; Δ = F̃[ȳ]; (LINE) | Steps 2, 5, 6 | OPEN ≥ 2, cited |
| (P2) | w by minima on the development | Step 3 (†5) | pinned (GMN Prop 2.7(3)) |
| (P4) | ω_{r+1} = ord_{ψ_r}(R_r f) | ρ-FIX(ii) | pinned (GMN Lemma 2.17) |
| (DET)-parent + LED(i) | reads are level-N₀ functions | ρ-FIX(i) | CEN-J standing hyp + proved layer |
| stratum keying (O-9 §2) | polygon = D's chain; vertex attainment | Steps 0, 3 | O-9 §2/§5.2 (proved layer) |
| M08 §2.2 / GD23 order-1 | sanity instance | (N5) | proved |

**Honesty line:** one new named object (c_par, (†2)); one new displayed
constant (𝔫, (†3)–(†4)); no new hypothesis beyond the cited package; the
lemma shrinks (FRESH)(c) to exactly (c-TR) = (TRANS-DEEP)(J) once accepted.
