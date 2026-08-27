# Adversarial verdict — VLIFT2

1. **DISPOSED — the quotient repair makes the amended II-a theorem true.**  The repaired
   document now says

   > “`#Pres(c) = #{ x ∈ Λ/π^N 𝒞 : Φ(x) ≡ F_c (mod π^N) }`”

   and

   > “`S_n(F) := { x ∈ Λ/π^n 𝒞 : Φ(x) ≡ F (mod π^n) }`.”

   These are the correct quotients for `Λ=π𝒞`: a `ClusterState` coordinate is an element
   of `πO/π^NO`, not `πO/π^{N+1}O`.  Thus level 1 is a singleton and the kernel of level
   `n+1 → n` is represented by `π^n𝒞/π^{n+1}𝒞 ≅ 𝔽^{s+r}`.  Lemma FE is strong enough:
   a degree-`d≥2` Taylor term has valuation at least `id+d−1≥2i+1`, because at most one
   selected block is the cofactor.  GRADE then gives image `W`, kernel dimension `s`, and
   exactly the displayed `0/q^s` lift count.  This proof uses neither raw injectivity nor
   any open II-b input.  I found no off-by-one residue left in §§1–3.

2. **DISPOSED — false raw injectivity and the valuation-extension argument are genuinely
   retracted.**  Section 2.4 now records the predecessor's counterexample verbatim and says

   > “Both the lemma and that proof are deleted, rather than patched.”

   Subsequent invocations of INJ are gone.  Section 6.1 explicitly allows zero Smith slots
   (`e_i=∞`) and its saturated-image calculation does not require injectivity.  No surviving
   proof invokes a unique extension of the valuation to an algebraic closure.

3. **DISPOSED — GR-11 is no longer overclaimed.**  The repaired §4.4 says

   > “`MLIFT-3 = OPEN GR-11`”

   and accurately limits `exists_peel_finset` to arbitrary child lifts plus a monic
   cofactor.  Positivity and assembly now explicitly assume MLIFT-3.  At current HEAD,
   `H116b1.lean:551-565` still has exactly that narrower conclusion; it neither builds a
   raw pinned presentation nor proves invariance under replacement by `classSect`.

4. **DISPOSED — Lemma TDC closes the target-direction gap, including rank-deficient
   maps.**  The essential repaired passage is

   > “`T(Λ)=πT(𝒞), hence T(𝒞)=⊕_{e_i<∞} π^{e_i-1}O A_i.`”

   This cancellation is valid because the target is torsion-free.  Reduction modulo `π`
   shows that precisely the `e_i=1` target-basis directions span `image(T mod π)=W`; their
   independence forces exactly `r` such directions.  All complementary target-basis
   directions project to a basis modulo `W`.  Combining this with (6.1) gives
   `dim V_n=#{i:e_i≤n}−r`.  Zero slots cause no break: their `A_i` remain complementary
   target directions, but `e_i=∞` never enters the selected span in (6.1).  For `n<N`,
   capping exponents at `N` retains exactly the comparisons needed.  Section 8.1 now
   invokes both GRADE and TDC, rather than the exponent multiset alone.

5. **NO NEW BREAK — the compressed choice-independence sentence in §5.3 is sound.**  The
   prose ends with

   > “the `v*`-recomputation compensates the `W`-part exactly.”

   Although unnecessarily compressed, this is not an unfilled lemma.  If a representative
   changes by `π^{n−1}(d_u,d_v)`, uniqueness of the cofactor digit in GRADE changes the
   forced digit from `v*` to `v*−d_v`; consequently the two chosen `x₀` classes differ by
   exactly `π^{n−1}(d_u,0)`.  The already-proved shift formula changes `ω_n` by
   `−L̄(d_u)`, which vanishes in the stated quotient.  Thus the claimed map is
   choice-independent without INJ or a certificate assumption.

6. **Current-HEAD citation audit — PASS.**  Audited at HEAD
   `62a85329b10c3a764799aefc8f81834d821c7a68`.  The live declarations remain:
   `H115b.lean:88` (`alphaFrame`), `:100` (`alphaParent`), `:111`
   (`alphaParent_coeff`); `H115c.lean:121` (`proj_eq_iff_pow_dvd`);
   `H116b2.lean:253` (`mem_maximalIdeal_classSect`), `:278`
   (`plantedPoly_monic`), `:283` (`plantedPoly_natDegree`); and
   `H116b1.lean:551` (`exists_peel_finset`).  The raw signed fibre at
   `H116b4a.lean:525-529` is indeed a tuple of child `ClusterState`s and one cofactor
   `ClusterState` subject only to the planted-product congruence, matching (1.3).  The
   residue pins `H116.lean:212` and `H116bR.lean:316` also remain live.  The battery log
   rows cited for GRADE/aggregate/leaf counts still report the stated values.  The MSMITH
   statement is presented only as a conditional sibling interface; the document does not
   misreport the still-open unequal-slope work as landed.

7. **Executable checks — PASS.**

   - `python3 -m py_compile verification/openmath/h116b4_lift_cert.py`: exit 0.
   - `python3 verification/openmath/h116b4_lift_cert.py`: exit 0,
     `==== ALL CHECKS PASSED ====`, including C7/C7b in CELL-1/2/4.
   - `python3 runs/wave-b/h116b4_battery.py`: exit 0 after 153.5 s,
     `==== ALL CHECKS PASSED ====`.

8. **Scope verdict.**  The repaired document does not prove unconditional H.116b4 and
   does not claim to: MLIFT-1, MLIFT-2, MLIFT-3/GR-11, and the consumed MSMITH interface
   remain hypotheses/open research.  Within that honest scope, the amended II-a theorem,
   the general Smith image formula, TDC, and the conditional assembly implication survive
   adversarial re-verification.  All findings in `verdict_VLIFT.md` are disposed, and I
   found no new correctness break.

ACCEPT
