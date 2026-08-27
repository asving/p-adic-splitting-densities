# MLFIX disposition — H.116b4 lift proof

**Unit:** MLFIX, 2026-08-27.  **Input verdict:** `runs/wave-b/verdict_VLIFT.md` (read in
full).  **Amended artifact:** `docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md`.

## Per-finding dispositions

1. **Citation/current-HEAD audit — ACCEPTED; no proof change required.**  Rechecked at
   current HEAD `29fb79834ab3f1b1e5ff09f3af562d907f68690b`: the cited declarations remain at
   `H115b.lean:88,100,111`, `H115c.lean:121`, `H116b2.lean:253,278,283`,
   `H116b1.lean:551`, `H116.lean:212`, and `H116bR.lean:316`.  The sole citation-status
   defect identified by VLIFT was the GR-11 overclaim, disposed in item 5 below.

2. **Wrong raw quotient — FIXED.**  Equations (1.3) and the definition of `S_n(F)` now use
   `Λ/π^N𝒞` and `Λ/π^n𝒞`, respectively.  This is the raw state quotient
   `π𝒞/π^n𝒞`; `Λ/π^nΛ` was one grade too large.  Consequently `S_1` really is a
   singleton when the target has zero low coefficients modulo `π`, and lifts from level
   `n` to `n+1` are represented by `x̂+π^n(u,v)`.  The repaired one-grade proof gives
   `K=q^s`, and its iteration starts from `#S_1=1`, hence the numerator
   `q^{s(N-1)}`.  The original displayed II-a theorem was false; the amended theorem is
   proved.

3. **False raw Lemma INJ — RETRACTED, with the counterexample recorded.**  Section 2.4 now
   reproduces the `ℤ₂`, `(μ,k,z)=(2,1,1)`, `r=1` common-factor counterexample and labels
   raw injectivity false.  All claims that derived injectivity from it were removed.
   Section 6.1 was strengthened in the useful direction: its Smith formula now permits
   zero diagonal slots (`e_i=∞`) and proves the saturated-image formula without
   injectivity.  The repaired II-a proof uses only FE and GRADE, so it survives this
   retraction.

4. **Nonexistent unique valuation extension — REMOVED, not assumed.**  The entire faulty
   root/resultant proof was deleted together with Lemma INJ.  The amended document notes
   explicitly that a general non-Henselian DVR need not have a unique extension to an
   algebraic closure.  No surviving proof invokes such an extension.

5. **GR-11 overclaim — DEMOTED TO A PRECISE OPEN LEMMA.**  MLIFT-3/GR-11 now states:
   every genre class `c` has `S_N(F_c)≠∅`, equivalently a raw planted presentation using
   the pinned `classSect`s.  The document explains exactly what `exists_peel_finset` does
   and does not supply: it gives arbitrary child lifts and a monic cofactor, but does not
   package level-`N` states or prove preservation after replacement by pinned sections.
   Positivity and §8 now assume MLIFT-3; neither is claimed unconditionally.

6. **Missing target-direction compatibility — FIXED BY A PROVED GRADE CONSEQUENCE.**
   New Lemma TDC (§6.1b) uses `Λ=π𝒞` and
   `image(T mod π)=W` (Lemma GRADE).  If

       T(Λ) = ⊕_{e_i<∞} π^{e_i} O A_i,

   then `T(Λ)=πT(𝒞)`, so cancellation in the torsion-free target gives

       T(𝒞) = ⊕_{e_i<∞} π^{e_i-1} O A_i.

   Reduction modulo `π` therefore identifies the exponent-1 target directions exactly
   with a basis of `W`.  Every remaining target-basis direction is independent modulo
   `W`, and for every `n≥1`

       dim V_n(T) = #{i : e_i≤n} - r.

   Thus for `n<N` the truncated exponent multiset plus GRADE determines `dim V_n`; the
   multiset alone still does not.  The verifier's first lattice has grade-one image
   `span(ē₁)` and violates GRADE for fixed `W=span(ē₂)`; only its second lattice is
   compatible.  Section 8.1 now invokes TDC explicitly.

   Certificate C7 independently checks both basis assertions and the dimension formula.
   Results:

   - CELL-1: `#e1=1=dim W`, quotient rank `2`; dimensions at `n=1..4` are
     `0,0,1,2 = #{e_i≤n}-1`.
   - CELL-2: `#e1=0=dim W`, quotient rank `4`; dimensions are `0,1,2,3`.
   - CELL-4: `#e1=0=dim W`, quotient rank `4`; dimensions are `0,1,2,2,3,3`.

7. **Prior REJECT — ACCEPTED AS TO THE OLD VERSION; repaired status below.**

## Final honest status

- **II-a:** the old statement was false because of its quotient.  The amended II-a
  one-grade `0/q^s` theorem on `Λ/π^n𝒞` is **PROVED mathematically** over an arbitrary
  DVR (residue-field finiteness is needed only for the cardinal `q^s`).  It does not use
  INJ, completeness, GR-11, MLIFT-1, MLIFT-2, or MSMITH.
- **II-b:** **OPEN in general.**  MLIFT-1 (deep sibling uniformity), MLIFT-2 (nonlinear
  obstruction image equals the saturated Smith-grade image), and MLIFT-3/GR-11
  (nonempty pinned presentation) remain open.  The MSMITH exponent-rigidity statement is
  a cited sibling interface, not proved by this unit.  Low-level reductions, the general
  Smith image formula, and TDC are proved in the amended document.
- **Section 8.1:** **PROVED AS A CONDITIONAL IMPLICATION** from MLIFT-1, MLIFT-2,
  MLIFT-3, and MSMITH.  The target-direction gap is closed by TDC.  The unconditional
  signed H.116b4 theorem is **NOT PROVED**.

## Verification

- `python3 -m py_compile verification/openmath/h116b4_lift_cert.py` — exit 0.
- `python3 verification/openmath/h116b4_lift_cert.py` — exit 0,
  `==== ALL CHECKS PASSED ====`, including C7/C7b in all three cells.
- `python3 runs/wave-b/h116b4_battery.py` — exit 0 after 153.8 s,
  `==== ALL CHECKS PASSED ====`.

No commit was made.  Only the amended document, the certificate extension, and this verdict
were touched by MLFIX.
