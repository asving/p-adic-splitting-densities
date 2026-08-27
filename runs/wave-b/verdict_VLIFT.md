# Adversarial verdict — VLIFT

1. **Citation and current-HEAD audit (no defect except the GR-11 overclaim in item 5).** Audited at HEAD `d08ebafa2b448d10a2e3e38f4050714af335e884`. At current lines, `H115b.lean:88` is exactly `alphaFrame`, `:100` is exactly `alphaParent`, and `:111` is exactly `alphaParent_coeff`; `H115c.lean:121` is exactly `proj_eq_iff_pow_dvd`; `H116b2.lean:253` is `mem_maximalIdeal_classSect`, `:278` is `plantedPoly_monic`, and `:283` is `plantedPoly_natDegree`; `H116b1.lean:551` is `exists_peel_finset`; `H116.lean:212` and `H116bR.lean:316` are the two residue-reduction theorems used by the proposed peel-to-presentation conversion. The battery citations `out_DEC5R_battery.log:48,49,65,66,74,75` and the reported leaf rows `:50,:67,:76` say what the document reports. Thus these line references are not stale. I also confirmed that A-C.17--A-C.20 and A-I.4 are landed at current HEAD; they concern Chapter C/I signatures and do not repair or invalidate any finding below.

2. **CRITICAL ERROR — the raw presentation tower uses the wrong quotient, so (1.3), the asserted root level, and every dependent lifting count are false as written.** Offending passages (verbatim):

   > “Write 𝒞 := O^{s+r} (the coordinate module) and Λ := 𝔪^{s+r} ⊂ 𝒞.”

   > “#Pres(c) = #{ x ∈ Λ/π^N Λ : Φ(x) ≡ F_c (mod π^N) },”

   > “S_n(F) := { x ∈ Λ/π^n Λ : Φ(x) ≡ F (mod π^n) },”

   > “S_1(F) is the single all-zero class if F ≡ X^m (mod π)”

   > “Lifts of x in Λ/π^{n+1} are exactly the classes x̂ + π^n(u,v)”

   Since `Λ = 𝔪^{s+r} = π𝒞`, the literal denominator `π^nΛ` is `π^{n+1}𝒞`. Raw `ClusterState` coordinates are classes in `𝔪/𝔪^N`, hence correspond to `Λ/π^N𝒞` (equivalently `Λ/π^{N-1}Λ`), not `Λ/π^NΛ`. In particular `Λ/πΛ` has `q^{s+r}=q^m` classes, all reducing to zero modulo `π`; it is not a singleton. Likewise the kernel of `Λ/π^{n+1}Λ → Λ/π^nΛ` is represented by increments `π^{n+1}(u,v)`, not `π^n(u,v)`. Thus (1.3) counts an extra coordinate grade and Theorem 3.2 is not a theorem about the displayed `S_n`. Per the binding stop rule, I did not verify the tower-dependent conclusions of §§3--5 and §§7--9 after this break.

3. **CRITICAL ERROR — Lemma INJ is false for the quantified raw space.** Offending passages (verbatim):

   > “T_x is injective for every x ∈ Λ (PROVED in §2.4).”

   > “**2.4 Lemma INJ (injectivity of T_x).** For every x ∈ Λ, T_x : 𝒞 → O^m is injective.”

   > “Roots of Q(x_a) satisfy v(root) > 0 = v(unit)·(monic X^r + 𝔪-low coefficients: its Newton polygon has all slopes > 0)… and child roots have v(θ) = k_p < ∞, while a root of Q with the same valuation as θ would need residue (root/π^{k_p}) ≡ 0 ≠ z_p when it has valuation exactly k_p — in all cases θ ≠ root.”

   Take `O = ℤ₂`, `π=2`, one frame `(μ,k,z)=(2,1,1)`, put `ŵ=resSect(1)` (so `ŵ` is odd), take `r=1`, child coordinates `b_0=b_1=0`, and cofactor coordinate `a_0=-2ŵ`. These are allowed points of `Λ`, but `P=(X-2ŵ)^2` and `Q=X-2ŵ` share a root. More explicitly, the nonzero differential increment with child digit `δb_1=1`, `δb_0=0`, and cofactor digit `δa_0=-2` gives
   `δP·Q + P·δQ = 2(X-2ŵ)^2 - 2(X-2ŵ)^2 = 0`.
   Hence `T_x` is not injective. The quoted normalized-residue assertion is itself false: the root `2ŵ` of `Q=X-2ŵ` has `(root/π) mod π = 1`, not `0`. Genre admissibility may exclude this example at a final genre fibre, but the document claims all `x∈Λ` and supplies no restricted injectivity proof in its place. This breaks every later use of Lemma 6.1 that obtains its injectivity hypothesis from §2.4; II-a's local Taylor calculation does not itself depend on INJ.

4. **JUSTIFICATION GAP — the claimed arbitrary-DVR proof invokes a nonexistent unique extension.** Offending passage (verbatim):

   > “Work in an algebraic closure of Frac(O) with the unique valuation extension.”

   An arbitrary DVR need not be complete or Henselian, and its valuation need not extend uniquely to an algebraic closure (for example, the `p`-adic valuation on `ℚ`, with valuation ring `ℤ_(p)`). The child-root valuation conclusion can plausibly be re-proved after choosing an extension, or directly by comparing valuations in the root equation, but that argument is not the one stated. Assuming the intended root-valuation conclusion, verification continued to the independent counterexample in item 3.

5. **JUSTIFICATION GAP — `exists_peel_finset` is landed, but GR-11 is not; the document claims more than the cited theorem.** Offending passages (verbatim):

   > “every genre target has nonempty S_N (landed `exists_peel_finset` packaged as GR-11)”

   > “By 4.2/4.3 and GR-11 (landed `exists_peel_finset` packaging: every genre class has a nonempty tower)”

   > “GR-11 (landed `exists_peel_finset`, packaged per outline §9) gives S_N(F_c) ≠ ∅”

   Current `H116b1.lean:551-565` lands an exact peel with arbitrary child lifts and a monic cofactor. It does not state a `Nonempty` planted-presentation fibre, construct the level-`N` child/cofactor states, or replace those lifts by the pinned `classSect`s. Current `H116B4_OUTLINE_2026-08-18.md:534-558` explicitly labels that conversion **OPEN GR-11**, and no `exists_plantedPresentation_of_genre` declaration exists at current HEAD. The conversion is described as mechanical and may be true, but it is neither proved in this document nor supplied by the cited landed theorem. This is overclaim, not line-number staleness.

6. **JUSTIFICATION GAP — the MSMITH interface stated in §6.5 does not by itself supply the target-direction information used in §8.1.** Offending passages (verbatim):

   > “V_n(T) = span_𝔽{ [Ā_i mod W] : e_i ≤ n }, of dimension #{i : e_i ≤ n} minus the 𝔽-relations among the Ā_i mod W.”

   > “the truncated Smith exponent multiset of the restricted multi-Sylvester map T_x|_Λ ... is one genre function:
   >
   >     { min(e_i(T_x|_Λ), N) }_{i=1..s+r} = gaugeExponents(L, D, N).”

   > “with V_n computed from gaugeExponents(L,D,N) by 6.1.”

   Section 6.1 correctly makes `V_n` depend not only on the exponents `e_i` but also on the target Smith directions `Ā_i` relative to the fixed quotient by `W`; §6.5 supplies only the exponent multiset. In general that multiset cannot determine `dim V_n`: with target basis `e_1,e_2` and `W=span(ē_2)`, the lattices `πOe_1 ⊕ π²Oe_2` and `π²Oe_1 ⊕ πOe_2` have the same exponent multiset `{1,2}`, but at `n=1` their images modulo `W` have dimensions `1` and `0`, respectively. In this particular setting, GRADE plausibly supplies the missing compatibility: `(TΛ/π) mod π=W` should force the exponent-`1` target directions to span `W`, after which the remaining Smith directions form a basis modulo `W`. But §8.1 neither states nor proves that lemma, and its written implication cites only MLIFT-2, the exponent-multiset interface 6.5, and 6.1. Thus the claimed “PROVED implication” has an omitted target-direction argument. Assuming that compatibility lemma, the interface objection is discharged. I checked only this independent interface-sufficiency implication after the earlier critical stops, not the dependent tower assertions themselves.

7. **REJECT**
