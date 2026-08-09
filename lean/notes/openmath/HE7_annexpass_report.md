# HE7 ANNEX-PASS — HOSTILE VERIFIER REPORT (scoped to the two annexes)

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR (+3 remarks), scoped to the
annex stack.** Machine legs both re-run isolated GREEN and bit-identical;
fresh route (disjoint) GREEN — the K₃ = F_{p²} probe fills the exact hole
both annex legs disclose, with a 48/96 tooth on R1-b's within-class unit.
Per the charge: **the annex stack carries its FIRST clean mark — 1/2
toward the annex-acceptance bar.**

**Pass:** HE7-ANNEX-PASS, fresh context, zero prior stake, 2026-08-09.
**Target:** the TWO ANNEXES of `HE7_PROOF_2026-08-08.md` ONLY — ANNEX F-1
(a4a91ee/7b3f0f1: ANNEX-LEMMA HE7-13′ + `he7annex_supp.py`) and ANNEX R
(f3ca2f1/f2fbcf0: ANNEX-DEF HE7-2′, ANNEX-LEMMAS R1-a/R2-a, ANNEX-THEOREMS
R1-b/R1-c, ANNEX-COROLLARY R1-d, `he7rannex_supp.py`, riders R3–R5). The
frozen body's 2/2 acceptance was NOT at stake and is not graded here.
Protocol: quote-and-classify, fix nothing. Context read: body §S1 (frame +
both CONVENTIONs), §S3, §S4.1–4.3, §S5 (HE7-4/5/7/7′/9/10/11, DEFINITION
HE7-3), §S5.8 (HE7-12/HE7-13), §S6 (DEFINITION HE7-2 + the induction), plus
`CODEX_HE7RAT_2026-08-09.md` (what ANNEX R was repairing).

---

## S1. FINDINGS

### MINOR (1)

**M-1 (ANNEX R, R1.3 run record — instrument-count conflation).** Quote:
"The Λ₂Λ₁-monomial twist arithmetic fired on 102 slot instances (a₁ ≠ 0)."
The counter (`deep-letter-fired` in `sides3`) is SHARED between the
corrected-chain reads and the P3 naive tooth reader's re-reads (both
invoke `sides3`, which counts unconditionally). Isolated re-count with the
tooth reader disabled: the corrected chain alone fires the deep letter on
**47** slot instances; 102 = 47 (corrected) + 55 (naive re-reads).
*Failure scenario:* a coverage auditor reading "102" as corrected-chain
exercise overstates the deep-letter coverage ≈ 2.2×. *Scope:* one
record sentence; no σ, no violation count, and no prediction verdict
moves (the load-bearing evidence for the deep letter is the 18/79 flip
tooth, which is unaffected and reproduced exactly).

### Remarks (not findings)

**R-a (stack chronology).** ANNEX F-1's clause-(a) licensing of the §S5
package on the block factor f_C ("Ψ̃ ∤ f_C since Ψ̃ ∤ f_S") consumed the
§S1 CONVENTION's equivalence chain, which at F-1's commit date still
carried the gap Codex later named F2 (Ψ ∤ f ⇏ gcd = 1 for a reducible
key). Within the stack this is CLOSED: ANNEX-LEMMA R2-a's consumption
rider (ii) is exactly the f_C leg ("gcd(Ψ̃, f_C) ≠ 1 ⟹ Ψ̃ | f_C | f_S,
contradicting Ψ̃ ∤ f_S"). Recorded so the dependency direction (F-1 needs
R2-a) is explicit; no repair owed.

**R-b (R1.3 wording).** "K2R built by R1-c inverse-twisting": at the
probe's g₂ = 1 the inverse twist actually applied is the side-assembly
bracket (DEFINITION HE7-3's mechanism), not R1-b's within-class ϑ_t
(structurally invisible at g₂ = 1, as the leg itself discloses two
sentences later). Consistent under R1.2's "composite twist unit"
vocabulary — R1-c's own proof identifies the two mechanisms — but a
reader could misattribute. Self-correcting via disclosure (ii); no
repair owed.

**R-c (annex grade, as self-disclosed).** R1.2 item 2's composite twist
unit for the level-(i+1) test family is asserted through the audit, not
displayed as a closed formula (the level-2 instance IS displayed, §S5.3
Step 2 / DEFINITION HE7-3). This sits within the annex's own honesty
box ("R1.2 is a transfer audit of exactly §S6's and LEMMA HE7-12(c)'s
kind; none of it has been through a hostile pass"). The fresh route
below implements the claimed prescription at a LIVE within-class unit
(g₂ = 2) and scores PARI 96/96 including refine chains — the strongest
evidence short of a displayed general formula.

---

## S2. ATTACK-ORDER RECORD (the six charged surfaces)

**(1) ANNEX-DEF HE7-2′ + ANNEX-LEMMA R1-a — CLEAN.** Re-derived the
cocycle recursion (R1.1) from the re-based definition by hand:
τ_{i+1}(a,b) = [n_i(A)n_i(B)/n_i(m_i(a+b))]·Φ_i^{s_i(a)+s_i(b)−s_i(a+b)}
with A = m_i(a), B = m_i(b); the s-sum is ≡ 0 mod ℓ_i and lies in
(−ℓ_i, 2ℓ_i), so the carry c ∈ {0,1} — CONFIRMED; A + B = m_i(a+b) − cu_i
and Φ_i^{cℓ_i}/n_i(cu_i) = Λ_i^c give (R1.1) exactly as displayed.
"Fixed K_i^× residue" (R1-a(iii)): the abstract element Πβ_j^{e_j} ∈ K_i^×
is fixed given the ARGUMENTS (a,b) — and R1-b states the per-slot
dependence honestly ("depending on (k, t) and the s-bookkeeping only,
NOT on C or ξ"); it is per-argument, and no consumer needs k-independence
(R1-c inverts ϑ_t at its own (k,t)). Level-1/2 reproduction: HE7-2′ at
i = 1 gives n₂(k) = ϖ^{m(k)}Φ′^{s(k)} with the same (m,s) defining
equation and range — §S1's display symbol-for-symbol; Λ₁ = Φ′^ℓ/ϖ^u =
§S1's letter; the transport tower at i = 1 = DEFINITION HE7-1's ι^{(2)};
τ₂ = Λ₁^c = the §S1 CONVENTION display (its "c ∈ ℤ" is the weaker claim;
R1-a sharpens to {0,1} — consistent). Machine: Q0 below re-verifies
R1.1 + the carry + θ-telescoping on 44,328 exact instances.

**(2) ANNEX-THEOREMS R1-b/R1-c — CLEAN.** (R1.2) re-derived as an exact
monomial identity; the θ_t telescoping checked (symbolically and by
machine). The collision worry (two θ_t coinciding) is HARMLESS: the
no-cancellation argument keys on the K_i-basis {1, β_i, …, β_i^{g_i−1}}
— coefficients γ_t·ϑ_t sit in DISTINCT basis coordinates regardless of
ϑ-coincidences, and ϑ_t ∈ K_i^× (R1-a(iii)) only rescales a K_i
coefficient, vanishing iff γ_t does. (LIFT_i)'s inverse pre-twist needs
NO g_i = 1: for every t with γ_t ≠ 0, (LIFT_{i−1}) is invoked at height
m_t = m₀ − tu_i ≥ bound_i for the K_i^× target γ_tϑ_t^{−1}, and R1-b
returns Σγ_tβ_i^t = c; the bound arithmetic (m₀ = (k−s₀u_i)/ℓ_i ≥
(g_i−1)u_i + bound_i at k ≥ bound_{i+1}) checks, and reproduces (‡₂) at
i = 1 where every θ_t = 1 (ϖ-powers multiply) — (SLOT₂)/(LIFT₂)
byte-for-byte as claimed. Fresh route exercises R1-c at g₂ = 2 with a
live ϑ (34/34 lift-contract roundtrips).

**(3) ANNEX-COROLLARY R1-d vs the n = 16 probe — CLEAN with the
disclosure verified.** The probe DOES exercise the level-3 τ₃-cocycle
(the Λ₂Λ₁-monomial exponent arithmetic in `twist3`, applied at the
level-3 side assembly — the F1 substance; 47 corrected-chain slot
instances, tooth 18/79) and R1-c's inverse-twist constructively (K2R).
It does NOT exercise R1-b's within-class ϑ_t (g₂ = 1 throughout — one
slot per class), and NO R1-b claim is machine-attributed to the
invisible part: disclosure (ii) states the scope exactly ("covers the
τ-cocycle substance of F1, not every letter of R1-b"). R1-d itself is a
package assembly (SLOT := R1-b, LIFT := R1-c, §S5 transfer per R1.2) at
the annex's self-disclosed grade; no overreach found in its text — the
"no hole developed" sentence is a report about the audit, not a grade
claim, and the honest-grade box sits directly beneath it.

**(4) ANNEX-LEMMA HE7-13′ (ANNEX F-1) — CLEAN.** Clause (a) re-derived:
partition via the minimal-polynomial reading of labels; Galois stability
by HE7-11 (proof audited — equivariance only, separability never used);
f_C ∈ O[x] | f_S by HE7-6's argument; single side via HE7-9(b) on f_C
(any second slope would carry roots at the wrong dv₂); R^{(C)} = c·r^k
via HE7-10 on f_C + uniqueness of the minimal polynomial; the k ∈ ℤ_{≥1}
arithmetic and the μ₂ ≥ 4 gate re-derivation (L_{λ,r} = kℓ₂deg r ≥ 4)
check. Clauses (b)–(e) re-derived from the single (LIFT₂) evaluation
fact; clause (e)'s residue is −ι_ρ^{(2)}(s₂) with minimal polynomial
Z + s₂ — CONFIRMED (value-0 minus residue-ι(s₂) at height λ₂), and (e)
is correctly fenced ("the per-block wiring never fires this clause").
The honesty box holds downstream: the wiring computes each block's OWN
node and branches on the block exponent k, never on the multiplicity m —
grep of the continuation logic (note text + both runners) finds no k = m
consumption; the k = 1 repeated-class corner is explicitly declared
harmless. The termination/W ≠ 0 bullets correctly reduce to HE7-8/
HE7-12(d) through the block route.

**(5) ANNEX-LEMMA R2-a — CLEAN.** The orbit-argument transplant verified
including the REFINED-key leg: for Ψ̃ = Ψ − W, a root ξ of
g₀ := gcd(F, Ψ̃) has dv₂(Ψ̃(ξ)) = ∞ > T₂, and LEMMA HE7-12(b)'s disk
criterion (verified present in the body at §S5.8) forces ξ to be a
level-2 point with level-1 label (λ, r); HE6-0′/HE7-5 then give
[L_ξ : K₀] ≥ D″ with no irreducibility of Ψ̃ used anywhere — the
argument is degree/orbit-based throughout (Ψ̃ ∈ O[x] keeps the root set
Galois-stable; deg g₀ ≥ #distinct roots ≥ orbit size ≥ D″ survives even
without separability of F; g₀ | Ψ̃ monic of degree D″ forces g₀ = Ψ̃).
Both consumption riders check; rider (ii) closes ANNEX F-1's f_C leg
(remark R-a). The grade flag paragraph accurately reproduces the fold
note's adjudication.

**(6) The two machine legs — GREEN, verified.** §S3 below.

---

## S3. MACHINE LEGS (isolated re-runs, `/tmp/he7_annexpass_sandbox`)

**Pins.** All md5 pins recorded in the two annexes verified against the
committed artifacts: `he7annex_supp.py` a5d00403…, `he7rannex_supp.py`
de5ba60c…, `he7rannex_supp_output.txt` 6b320011…,
`he7rannex_supp_results.json` aca0edc1…, `he7_pe3_probe12.py` 61d9f81c…,
probe12 results dfd9fe23… / output 710a31d1…. Byte-freeze pins verified
from git: accepted body (pre-F-1) md5 6f2f4c75 = file @ a4a91ee^;
post-F-1 body md5 85d57dfa = file @ de479f4 = f3ca2f1^; the current file
is a strict byte-append on BOTH freeze points (prefix identity checked
byte-for-byte).

**ANNEX F-1 leg (`he7annex_supp.py`).** Re-run isolated: **GREEN, 96
members, σ == PARI 96/96, 0 violations, 148 refines; P2 128/128
thread-entry exact + 132 persistent; P3 0 floor violations; P4 48/48
naive-route cycles; P5 16/16 pure controls lose the λ₂ side; R-a route
32×** — every number of the annex run record reproduced; output diff vs
committed artifact empty (mod nothing — even the 3.5 s timing leaf in
the results-JSON reproduced; leaf-diff EMPTY). Instrument audit: the σ
oracle (PARI global factor + idealprimedec with the p-maximal hint) is
independent of the reader; the hint's smoke cross-check against full
nfinit is disclosed in the docstring and re-runnable (`smoke` arg).

**ANNEX R leg (`he7rannex_supp.py`).** Re-run isolated: **GREEN, 79
members, σ == PARI 79/79, 0 violations; THE TOOTH REPRODUCES: 18/79
flip when the deep letter is dropped** (deterministic seed 20260809;
flips K2 10 + K2R 8, on all four (p,s) frames); 19 members fire the
level-3 α-refine (15 K2R + 4 K2), each terminating in one step; 0
level-4; σ genres {(16,1)}×32, {(8,1),(8,1)}×31, {(8,2)}×16; 1
disc-zero discard — every claim of the run record verified against the
fresh JSON. Artifact diff vs committed: identical except the `secs`
leaf (2.7 vs 2.6). Instrument audit: the forward ladder read
(level-1/2/3 polygons, twisted residuals, refine chains) is built
entirely from the exact ℤ[x] kit — PARI is consulted ONLY as the σ
oracle; the twist arithmetic is exact exponent-vector arithmetic with a
value-identity assert (4α + 10σ + u₂s₂ = k) on every monomial. One
count conflation found (finding M-1).

---

## S4. FRESH ROUTE (disjoint from both annex legs) — GREEN

`verification/openmath/he7annexpass_fresh.py` (committed 1857f20;
runner md5 dc7ddf63…, output 74d75634…, results b728a274…), two legs:

**Q0 (EXACT, symbolic).** The R1.1 cocycle recursion verified as an
exponent-vector identity at level 3 in BOTH frames (ℓ₂ = 2 rannex frame
u₂ ∈ {21,23}; ℓ₂ = 1 fresh frame), carry ∈ {0,1} at every instance, all
a, b ∈ [−60, 60], plus R1-b's θ_t telescoping identity — **44,328
checks, 0 violations.**

**Q1–Q5 (the K₃ = F_{p²} family — the disclosed hole of BOTH annex
legs, first coverage anywhere).** Same sealed frame ((2,1,1), Φ′ =
x²−p, u = 5), level-2 node at INTEGER slope u₂ ∈ {11,13} with residual
r₂², r₂ QUADRATIC irreducible over F_p (the jump gate ℓ₂·deg r₂ = 2
with g₂ = 2, so K₃ = F_{p²} and the level-3 slot read has TWO slots per
class with within-class unit ϑ₁ = Λ₁-power, LIVE at every even height
when s ∈ {2,3}); key per DEFINITION HE7-3's inverse-twisted
prescription; members f = Ψ₂² + B₁Ψ₂ + B₀ of degree 16, grid p ∈ {5,7},
s ∈ {2,3}, u₂ ∈ {11,13}, 2 quadratics per p, kinds M1/M2/M2R/M3.
Results: **96 members, ladder read-forward 96/96 (first machine contact
of a degree-2 repeated level-2 residual factor), σ == PARI 96/96, Σef =
16; THE ϑ-TOOTH: 48/96 members FLIP when the within-class unit is
dropped** (ϑ₁ := 1, all else identical — the first machine exercise of
R1-b's new letter anywhere in the program; all 48 are genuine
σ-differences, 0 naive-read errors; flips M2 17 + M2R 31, none on the
deg-1-residual kinds M1/M3, mirroring the annex leg's
monic-normalization-blindness pattern one letter deeper); **34 level-3
α-refines via R1-c's inverse-ϑ lifts, contract 34/34** (lift-then-read
roundtrip exact at live ϑ, including targets outside F_p), every chain
one-step-terminating above floor, 0 level-4 nodes; 0 violations, 3.6 s.

*What this establishes for the annex stack:* R1-b's within-class
residue display and R1-c's inverse pre-twist are EXTERNALLY validated
against PARI on the exact structural corner the annexes could only
claim by proof (g₂ ≥ 2), and the ϑ-unit is machine-load-bearing (48/96
mispredictions without it) — the R1-b analogue of HE7-T-BADTWIST.

---

## S5. CLEAN CHARGES (verified, no finding)

1. R1.1 carry c ∈ {0,1} (hand + 44,328 machine instances).
2. R1-a(iii) fixed-residue claim as stated (per-(a,b), ξ-only-through-ι).
3. HE7-2′ levels 1–2 byte-reproduction (n₂, Λ₁, ι^{(2)}, τ₂ = Λ₁^c).
4. R1-b collision robustness (basis-coordinate separation).
5. R1-c: no hidden g_i = 1; bound recursion = (‡₂) at i = 1.
6. R1-b/R1-c at i = 1 reproduce (SLOT₂)/(LIFT₂) exactly (θ_t ≡ 1).
7. HE7-13′(a)–(e) full re-derivation incl. the (e) residue −ι(s₂).
8. HE7-13′ honesty box: no downstream k = m consumption (text + code).
9. R2-a incl. the refined-key (Ψ̃ reducible) leg via HE7-12(b).
10. R3/R4/R5 riders: accurate to the displays they fence (R4's
    inventory checked against HE7-12(c) item (7)'s actual sentence;
    R5's F₈ witness checked: {1, β, 1+β} has size 3, no subgroup/coset).
11. All md5 + byte-freeze pins (S3); both annexes strictly appended.
12. The R1.3 disclosures (i)–(iii) accurate (ℤ_p-only; g₂ = 1
    ϑ-invisibility — now independently confirmed AND filled by the
    fresh route; smoke history consistent with the committed docstring).

## S6. GRADE LINE

**CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR (M-1, one record sentence; repair
= reword "102 slot instances" to "47 corrected-chain + 55 tooth-reader
slot instances" in a dated line, at the editors' convenience).** Nothing
GAP-or-worse survived verification. Machine legs bit-identical GREEN;
fresh route GREEN with the first g₂ ≥ 2 coverage. Per the pass charge:
**the annex stack (ANNEX F-1 + ANNEX R) carries its first clean mark —
1/2 toward the annex-acceptance bar.** The stack's standing
conditionality is unchanged and self-disclosed: R1.2/R1-d are at annex
(transfer-audit) grade pending the arc, and the ϑ-letter now has
machine coverage via this pass's fresh leg.
