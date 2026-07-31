# O9 Phase-B rev 0 — hostile verification pass 1 (fresh context, 2026-07-31)

**Charge.** Quote-and-classify audit of `O9_phaseB_verifybrief.md` rev 0, reading ONLY
that document. Audit targets: CEN-W's census exponent E′ (the slot ledger), the
(GR-B)-conditionality of the window layer, CEN-J's JUNCTION-PIN, the OL-A splits
(A1/TRI/LED against the pinned GMN statements *as quoted in the brief*), TYPE-MARCH +
its F₃ countermodel, and the r = 0 regression to M08 Theorem 2. Classification per the
repo's verifier protocol: **critical error** (breaks the logical chain; dependent steps
not certified) vs **justification gap** (assume the conclusion, keep verifying
downstream). Nothing is fixed here. Numerical checks were run fresh
(`/tmp/o9_verify_checks.py`, `/tmp/o9_check3b.py`, `/tmp/o9_check4.py`; key outputs
reproduced inline).

**Verdict: NOT ACCEPTED as written — 2 critical, 3 gaps.** The reduction *architecture*
(A1/TRI/LED + (DET) + TYPE-MARCH → CEN-W shape → CEN-J conditional on (GR-B)+(FRESH))
survives the audit; the two criticals are (1) an off-by-one in E′'s left-tail
convention, machine-refuted by an explicit r = 0 countermodel, and (2) an unsupported
PROVED label on JUNCTION-PIN that contradicts the brief's own §5.4.

---

## CRITICAL 1 — E′'s left-tail β_k is non-strict at integral extended-line abscissas; CEN-W's displayed count is false for every D with k₀ ≥ e₁ (machine-refuted)

**Quotes.** §2 (CEN-W display):

> s_k := Σ_𝐣 max(0, ⌈(β_k − wt(𝐣))/e⌉),   β_k := ⌈line-or-pin value at k⌉ − k·V̂

§2 (stratum definition, left-tail cutoff):

> the only condition imposed at k < k₀ is u_k > (the extended line of face 1 at k)

§5.2:

> The non-lattice abscissas of a face carry non-integral line values (slope −h_S/e_S in
> lowest terms), so the ceiling ⌈line − kV̂⌉ implements "strictly above" exactly as
> M08's c_i convention

§6.3:

> right tail, left tail, and off-line slots contribute the LED(ii) q-powers (their β_k
> as displayed in E′)

**Classification: CRITICAL ERROR.** The §5.2 justification covers only abscissas
*within a face's span*, where non-integrality of the local line value makes ⌈·⌉
implement strict inequality. It is silently extended to the left tail, where it fails:
at k < k₀ with e₁ | (k₀ − k) the extended face-1 line takes the **integer** value
U₀ + ((k₀−k)/e₁)·h₁, so ⌈line⌉ = line and the LED(ii) count q^{mN−s(β_k)} counts
**u_k ≥ line**, not u_k > line. When e₁ = 1, *every* left-tail abscissa is integral.
A tuple with u_k = line at such k has face 1 extended to left endpoint k — under the
brief's own keying ("the faces of D below the cutoff") that is a *different* stratum
(larger d(1)), so strictness is genuinely required and the displayed formula overcounts
by a factor q^{dim G_{β_k}} (= q^d at attained β_k) per such abscissa.

**Countermodel (machine-verified, correct cutoff semantics: steeper deep faces left of
k₀ allowed, membership = faces of slope ≥ λ₁ exactly D's).** r = 0, f₀ = 1 (m = d = 1,
e = 1, V̂ = 0, w = v_π), q = p = 2, N = 4, ℓ = 3; D = single face (2,1)→(3,0), slope −1
(e₁ = h₁ = 1), λ = {(1,1)}; free coordinate box (ε = 1). Displayed formula: β =
(3,2,1,0), E′ = (4−3)+(4−2)+(4−1)+(4−0) − 2·1 = 8, count = q⁸(q−1)·M_{(1,1)}(q) =
2⁸·1·1 = **256**. Brute force over (ℤ/16)⁴:

    count satisfying the displayed beta conditions:  256   (formula exact for its conditions)
    TRUE stratum count (faces-below-cutoff == D):     64
    overcount factor: 4  (= q^d per integral left-tail slot, slots k = 0, 1)
    all 192 extra tuples: face 1 extended to left endpoint (1,2) or (0,3)

The strict thresholds (β₀ = 4, β₁ = 3) give E′ = 6 and 2⁶·1·1 = 64 = truth — so the
defect is exactly and only the ⌈·⌉ convention at the left tail, not the assembly. (For
contrast, a no-left-tail instance was spot-checked exact: r = 0, N = 3, D = (0,1)→(1,0):
direct 8 = formula 8.)

**Downstream damage.** (a) Theorem CEN-W as displayed is false for every D with
k₀ ≥ e₁; the proof in §6.3 inherits the error verbatim (quote above). (b) §6.4's "At
r = 0 this IS M08 Theorem 2" and §2's "E′ collapses to f₀·Σ_i(N − c_i) with M08's c_i"
cannot both survive: either M08's c_i are strict at the left tail (then the collapse
claim is false as an identity of formulas) or M08 Thm 2 shares the bug (then the PROVED
r = 0 base is at risk). This document alone cannot decide which; note K1 (harness
level-1 census = M08 Thm 2 exactly, 0 violations) ran on configurations that contain
integral left-tail strata (e.g. n = 4, M = 4, face (2,1)→(4,0): k = 0 has extended-line
value 2 ∈ ℤ inside the (DET) fence), which suggests the harness-side M08 implementation
is strict and the display here is the outlier — but that is inference, not
verification. (c) The reduction headline ("REDUCED to (GR-B) + (FRESH)") survives in
shape: the repair is a strict threshold (⌊line⌋ + 1 in place of ⌈line⌉ at integral
left-tail values), which changes no conditionality. Not fixed here per charge.

**Why the clean falsifier run did not catch this: see GAP 5(a).**

## CRITICAL 2 — JUNCTION-PIN is labeled PROVED in the status table but is defined in §5.4 as a clause of the OPEN (FRESH); no proof from (GR-B)(2′)+(3) exists in the document

**Quotes.** §0 status table:

> | JUNCTION-PIN | the window chain's right end is realization-pinned; telescope gives
> exactly ∏M (no stray (q^d−1)) | **PROVED** given (GR-B)(2′)+(3); measured ε = 0 on 18
> cross-p cells |

§5.4:

> **JUNCTION-PIN (a clause of (FRESH), stated separately because the census formula's
> shape depends on it).** Conditioned on ρ, the digit read at the window's right-end
> vertex ... is a ρ-determined nonzero CONSTANT (the transported anchor/VTX read), not
> a free unit.

§5.4 header: "(FRESH) — the joint-with-parent stacking clause **[displayed OPEN]**".

**Classification: CRITICAL ERROR (unsupported PROVED claim / internal contradiction).**
The status table asserts JUNCTION-PIN is PROVED from (GR-B)(2′)+(3). No such derivation
appears anywhere: §5.4 merely *states* the pin with the gloss "(the transported
anchor/VTX read)", and §6.4 invokes it ("by JUNCTION-PIN the chain's right end is a
ρ-determined nonzero constant") under the (FRESH) umbrella. If the table row means only
that the *telescope consequence* is proved given the pin, the row's own first column
("the window chain's right end is realization-pinned") is precisely the pin, so the
PROVED label still attaches to an unproved statement. The "measured ε = 0 on 18 cross-p
cells" is evidence, not proof, and is itself non-discriminating (GAP 5(c)). Mitigation:
CEN-J's stated conditionality "(GR-B) + (FRESH)" happens to remain correct because
JUNCTION-PIN ⊂ (FRESH); the damage is confined to the status table's accounting — but a
status table is exactly where such an error propagates to consumers (the §9 residue
table and the tree's O-9 row would import "JUNCTION-PIN: PROVED" as a fact).

## GAP 3 — attainment of the on-line β_k is assumed, never established; D admits inadmissible data on which the formula is positive but the census is 0

**Quotes.** §5.1: "**Surjective onto F_{r+1}** for attained β"; §6.3: "each on-line
lattice slot contributes, per prescribed digit z ∈ F_{r+1}, exactly q^{mN − s_k − d}
(§5.1 fiber uniformity — z-independent)".

**Classification: JUSTIFICATION GAP.** §5.1's surjectivity (hence fiber-uniformity, and
the −d in E′) is scoped to *attained* β — those with G_β ≠ 0, i.e. ∃𝐣 with
wt(𝐣) ≡ β mod e. §6.3 applies the count at every on-line slot of D, but D's definition
(§2: vertices are arbitrary points of ℤ × ℤ with the slope conditions) contains no
admissibility clause, and no lemma shows the ledger weights cover the residues mod e
hit by a face's lattice line. If some on-line β_k is unattained, the true stratum is
empty (a nonzero vertex digit is required at a weight that no a_k of deg < m attains)
while the displayed q^{E′}·(…)·∏M is positive. At order 1 coverage is easy
(gcd(h₁,e₁) = 1 makes {j₁h₁ mod e₁} everything), and (GR-B)'s "invertible
anchor-monomial system" plausibly supplies ϕ_β for all β at higher order — but neither
is displayed. Needed: either a residue-coverage lemma (all β mod e attained by ledger
weights, derived from the pins or from (GR-B)) or an admissibility hypothesis on D in
both CEN-W and CEN-J.

## GAP 4 — CEN-J's E″ has no displayed formula, and the monic-top box is never reconciled between §2's C_{D,N} and CEN-W's free window box

**Quotes.** CEN-J (§2): "with E″ = E′ minus the exponent already charged by the
parent's conditions — i.e. the refinement factor is the SAME for every realization ρ
of the same discrete parent shape, and is the displayed polynomial." §2: "C_{D,N}(t, ρ)
:= #{ f mod π^N : … }" for **monic** f of degree n; CEN-W: "the WINDOW-ONLY stratum —
the conditions of D imposed on the development coordinates (a_k)". §6.4: "the per-slot
counts of §5.1 apply on the ρ-fiber".

**Classification: JUSTIFICATION GAP (underspecified statement).** (a) E″ is never given
a closed form; "the exponent already charged by the parent's conditions" is not defined
anywhere, so as stated the CEN-J display risks circularity — E″ is whatever makes the
equation true, and the theorem's non-circular content (ρ-independence + polynomiality of
the refinement factor) is essentially (FRESH)(b) restated. The E′ ledger formula has no
E″ analogue. (b) The joint census counts monic f of degree n, so at k = ℓ the
coordinate a_ℓ is monic of degree n − ℓm — NOT a full W_N box; every LED/§5.1 count is
proved on the full box W_N. §6.4 applies "the per-slot counts of §5.1 … on the ρ-fiber"
without reconciling the top slot (in the r = 0, m | n case the discrepancy between the
digit-pinned free box and a_ℓ = 1 is a factor q^{f₀(N−1)}). Possibly the parent charge
absorbs exactly this — but that is the undisplayed E″ again. (c) Minor feeding slip:
§2's "a_ℓ monic iff m | n" is false as written (the top development coefficient of a
monic f is always monic, of degree n − ℓm); "a_ℓ = 1 iff m | n" is evidently meant.

## GAP 5 — falsifier scope: the clean run does not certify what the brief's headline suggests (partially disclosed)

**Quotes.** §10: "RESULT: **0 violations on every check**; fitted spectrum all pure
q-powers times ∏M (ε = 0 throughout — JUNCTION-PIN confirmed at the tested perimeter).
Any single K4 hit would have refuted OL-C before it was written up."

**Classification: JUSTIFICATION GAP (evidence-strength accounting).**
(a) **None of K1–K4 evaluates the displayed E′ closed form.** The harness *fits*
exponent vectors to empirically tabulated censuses (K4: "fits ONE exponent vector");
it never predicts a census from the E′ ledger formula and compares. Consequently a
wrong E′ display coexists with a fully clean run — which is exactly what CRITICAL 1
demonstrates. The brief's status row "valuation-condition counts are pure q-powers with
p-free exponents: PROVED" conflates the (correct, LED-supported) *form* claim with the
(refuted-as-displayed) *value* claim.
(b) **K4's cross-p fit is underdetermined at the character-sensitive cells.** Child
residual types of degree ≥ 2 are exercised at p ∈ {2,3} only (disclosed); two data
points against a three-atom exponent vector {p, p^g−1, p−1} generically admit spurious
fits, so for those 9 cells "any single K4 hit would have refuted OL-C" overstates the
test's power. The proposed (5,4,4) run is the fix and is correctly queued.
(c) **"JUNCTION-PIN confirmed" is not discriminating.** All measured censuses are
CEN-J-side (conditioned tabulations), where ε = 0 is also what right ends pinned by the
tested strata's *shape* (k_s = ℓ, m | n tops) would produce; the CEN-W ε = 1 branch was
never exercised. The brief's own attack item 3 raises this; the §10 headline ignores
its own caveat.

---

## Audited and found SOUND (with the checks performed)

* **TYPE-MARCH (§6.1): PROVED as stated.** R̃(y) = τ₀·R(ρy) is a two-line identity;
  y ↦ ρy is a degree-preserving automorphism fixing (y); types and nonvanishing of
  R(0) transfer. **F₃ countermodel machine-verified**: (y+2)² = y²+y+1 over F₃ (double
  root at y = 1, type {(1,2)}); the twist (1,1,2) is non-geometric (ratios 1 then 2);
  2y²+y+1 has no F₃-root, is irreducible (type {(2,1)}), and 2·(2y²+y+1) = y²+2y+2 as
  claimed. The warning display is correct and genuinely load-bearing. The *application*
  (march ⟹ geometric scalar twist) rests on (GR-B)(2′)'s "LINEAR in κ" stride clause as
  quoted — internally coherent (a fixed consecutive-slot normalizer ratio of ȳ-degree 0
  lands in Δ^× = F_{r+1}^× since Δ = F_{r+1}[ȳ] is a polynomial ring), and correctly
  priced to the (GR-B) black box.
* **Lemma A1: sound.** Division by a monic is O-linear with O-coefficient formulas;
  the mixed-radix degrees Σ jᵢmᵢ (jᵢ < eᵢfᵢ, m_{i+1} = eᵢfᵢmᵢ) hit 0..m−1 exactly
  once; unitriangular change of basis follows.
* **Lemma TRI: sound against the pins as quoted.** (P2) is invoked at order r+1 for
  the φ_r-development (matching the quoted "the φ_r-adic development computes w by
  minima"); (P1)+Lemma 2.2(2) is applied only to elements of degree < m_r — including
  the sub-radix monomials B_{𝐣'} themselves, so the rescaling e_r·wt_r(𝐣') = wt(𝐣')
  is legitimate; the nested minima recombine. (Attack item 1 discharged, modulo
  fidelity of the pins to GMN, which is out of scope for this pass.)
* **Lemma LED: sound.** TRI ⟹ per-coordinate thresholds ⌈(β − wt)/e⌉ ≤ N for β ≤ eN;
  the well-definedness bounds (β ≤ eN for ≥, β ≤ eN−1 for exact + graded class) are
  exactly what (DET)'s right side provides.
* **(DET) sufficiency (§5.2): sound, including two corners checked adversarially:**
  (i) vertex reads at β = eN−1 are within LED(i)'s scope; (ii) the right-tail pin
  β_k = U_s − kV̂ is ≤ eN−1 for all k > k_s because (DET) at k_s gives
  U_s − k_sV̂ ≤ eN−1 and V̂ = w(φ) ≥ 0. Note (DET)'s line_D does not include the pin,
  but the V̂ ≥ 0 argument closes it. The ⌈·⌉-implements-strict claim is correct
  *within faces* (gcd(h_S,e_S) = 1 ⟹ non-lattice values non-integral); its failure is
  confined to the left tail (CRITICAL 1).
* **§5.1 fiber uniformity: sound given (GR-B) and attained β.** r_β is a genuine
  additive map (all four w-cases check) onto F_{r+1}, F_q-linear; equal fibers follow.
  The "development of a is a itself" step (attack item 2) is coherent under (2′) as
  quoted, with Lemma 2.2(2) correctly held as fallback pin.
* **Window-layer conditionality audit (the charge's (GR-B) question): CLEAN.** Beyond
  (GR-B), CEN-W's proof consumes only: the pinned (P1)–(P4) (Route G, declared), M08
  Lemmas B/C/D imported at F_{q^d} (§6.2's import argument — "only |F_Q| = Q and the
  F_Q^×-scaling action" — is plausible as stated; not checkable against M08 from this
  document), and the §2 conventions. No undeclared open input found. The honest
  headline's "no open input is new to this unit" survives, subject to CRITICAL 1's
  repair and GAP 3's admissibility clause.
* **CEN-W assembly spot-check (no left tail): exact.** r = 0, f₀ = 1, q = 2, N = 3,
  D = (0,1)→(1,0): direct enumeration 8 = formula q^{2N−c−2}(q−1)² = 8. The ε = 1
  free-end branch and the Z_D telescope reproduce the direct count.
* **INDEX FLAG (attack item 7): internally consistent.** From the brief's own tower
  (F_{i+1} = F_i[y]/(ψ_i), deg ψ_i = f_i, starting at F₁ = F₀[y]/(ψ₀)), order-(r+1)
  residual coefficients live in F_{r+1} of degree d = f₀⋯f_r over F_q; the harness
  instance (f₀ = 1, f₁ = g ⟹ reads over F_{q^g}) matches the K4 atom p^g − 1. Whether
  M08 §3's f̄_r display is the off-by-one (rather than this brief) cannot be confirmed
  from this document alone.
* **r = 0 regression (§6.4): structurally correct, not certifiable as "exact".** The
  collapse mechanics (e = 1, d = f₀, all weights 0, s(β) = f₀β, monic-top ε = 0) are
  right; the claim "At r = 0 this IS M08 Theorem 2" inherits CRITICAL 1 at left-tail
  strata and GAP 4(b)'s top-slot convention, so exactness of the match is not
  established by this document.

## Summary for the ledger

| finding | class | anchor | one-line content |
|---|---|---|---|
| 1 | CRITICAL | §2 E′ display / §6.3 / §5.2 | left-tail ⌈line⌉ non-strict at integral abscissas; refuted 256 vs 64 at r=0, D=(2,1)→(3,0), q=2, N=4; overcount q^d per slot, all D with k₀ ≥ e₁ affected |
| 2 | CRITICAL | §0 JUNCTION-PIN row vs §5.4 | PROVED label with no proof in document; §5.4 makes it a clause of the OPEN (FRESH) |
| 3 | GAP | §5.1→§6.3 | attainment of on-line β_k assumed; D lacks admissibility clause; formula positive on empty strata |
| 4 | GAP | CEN-J §2/§6.4 | E″ has no displayed formula (circularity risk); monic-top box vs free W_N box never reconciled; "a_ℓ monic iff m\|n" false as written |
| 5 | GAP | §10 | harness never evaluates E′ (hence CRITICAL 1 survived a clean run); K4 underdetermined at p∈{2,3} cells; ε = 0 does not discriminate JUNCTION-PIN |

Acceptance requires: repair + reproof of the E′ display (strict left-tail thresholds),
a corrected JUNCTION-PIN status row, an admissibility/attainment lemma, a displayed E″,
and (recommended) a harness check that *predicts* censuses from the ledger formula
rather than fitting them.

— O9 verify pass 1 (fresh-context verifier; brief-only perimeter as charged; M08, GD23,
LITUNIT, and the harness source were NOT consulted).
