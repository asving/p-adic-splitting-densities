# CODEX ADVERSARIAL REVIEW — the dv-graded engine (2026-08-23)

**Reviewer: Codex (gpt-5 class), fresh context, adversarial verifier charge (quote-and-classify,
CRITICAL vs GAP, no fixes).**  Subject: `DV_GRADED_ENGINE_2026-08-20.md` v1.  Full transcript
captured without truncation (the tail-pipe lesson applied).  Thirteen findings; verdict at end.

1. **CRITICAL ERROR — `WT` is not actually defined at the stated Lean type.**  
   Quote: “`WT(P) := min` over the support of `e₁e₂·addVal(coeff) + a·e₂h + b·u₂`” ([document, line 36](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:36)).  
   For `P : Polynomial (Polynomial O)`, an outer coefficient has type `Polynomial O`, while `addVal O` accepts an element of `O`. The definition needs two support indices, but only “the support” and one coefficient are specified. Thus the proposed C.131a object is not a well-typed Lean definition as written. This breaks the formal chain rooted at L1. Subsequent findings assess independent mathematical claims only, not the now-broken chain.

2. **JUSTIFICATION GAP — L1’s inequality is plausible, but it is not “pure support-arithmetic” or free merely because monomial weights add.**  
   Quote: “`WT(PQ) ≥ WT P + WT Q` … this product law is FREE … Pure support-arithmetic over `ℕ∞`” ([line 60](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:60)).  
   The asserted direction is the correct valuation direction: `WT` is superadditive under multiplication. But an outer product coefficient is a convolution sum of products of inner polynomials, whose coefficients are themselves convolution sums. The proof must use `addVal_mul` for products and `addVal_add` repeatedly for both convolution layers. Cancellation can remove minimal-weight terms, which helps the inequality, but support combinatorics alone does not establish it. Exact additivity is not available; only the stated lower bound is plausible.

3. **JUSTIFICATION GAP — L2’s arithmetic and direction are correct, but the cited premise has not been extracted from `F.hpure`.**  
   Quotes: “tail branches at weight ≥ parent … the `Y`-branch at parent `+ δ` EXACTLY” ([line 50](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:50)); “the PREMISE … must come from `F.hpure` … not yet checked” ([line 126](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:126)).  
   Conditional on the coefficient-side inequality, multiplying by `e₂` gives the advertised tail bound, and
   \[
   u₂-D'e₂h=\delta
   \]
   makes the `Y`/`\Phi'` branch exactly `parent + δ`. This is faithful to EFF.GENTOW3.22 ([spec line 673](/data/users/asvin/math-and-lean/p-adic-splitting-densities/spec/EFF-GENTOW3.md:673)). However, `F.hpure` is only the endpoint formulation of `IsPure`; the needed all-coefficient inequality requires the `suppVal`/weight lemmas, not unfolding `hpure`. The document correctly admits that this bridge has not been checked.

4. **JUSTIFICATION GAP — L3 overstates both what is proved and where it is proved.**  
   Quote: “Every term of `composedKey`’s display sits at weight `E₂` exactly … C.46’s pins” ([line 72](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:72)).  
   The numerical scaling is correct conditionally: a lift of stage height \(M=(f₂-t)u₂\) has cleared weight \(e₂M\), while `Y^(e₂t)` contributes \(e₂tu₂\), totaling \(E₂=e₂f₂u₂\). The wrap exponent changes the stage-field argument, not that total, provided it remains nonzero. But:

   - C.46’s `slotRes_stageLiftO` is a private residue statement, not an exported exact-height theorem.
   - The exact-height lemma is private in C.47; the public statement is `composedKey_slot_height`, conditional on a nonzero label coefficient ([C47 line 565](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C47.lean:565)).
   - A zero lift summand has `WT 0 = ⊤`, not exactly `E₂`; “every term” is defensible only if it means every nonzero support monomial.
   - Exact stage height proves a minimum, not by itself that every nonzero monomial of the lift has the exact same weight.

   Thus the required lower bound is plausible, but the advertised exact termwise theorem is not supplied by the cited pins.

5. **JUSTIFICATION GAP — L4’s index direction matches the source, but the sketched induction does not establish the quotient ledger.**  
   Quote: “one division step replaces top·`Y^top` by top·(lift sum)·`Y^{top−e₂f₂}` … each `Φ₂`-extraction ‘spends `E₂`” ([line 79](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:79)).  
   Replacing `Y^(e₂f₂)` by a lift of weight `E₂` preserves total unreduced weight. But this only explains the remainder substitution. The ledger also needs a separate bound on the quotient coefficient created by removing `Y^(e₂f₂)`, namely a drop of `E₂`, followed through repeated quotient divisions. Linearity does not supply that bound automatically. The intended direction is nevertheless correct: larger `j` means more extracted `K₂` factors and the coefficient floor decreases from `μ₂E₂` to `(μ₂-j)E₂`, exactly as EFF.GENTOW3.23 states ([spec line 698](/data/users/asvin/math-and-lean/p-adic-splitting-densities/spec/EFF-GENTOW3.md:698)).

6. **CRITICAL ERROR — L5’s stated termination measure is not strictly decreasing.**  
   Quote: “measure: `Σ` over support of `a + b·D′`, strictly decreasing per move” ([line 87](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:87)).  
   On the `Y` branch of an x-carry,
   \[
   (a,b)\longmapsto(a-D',b+1),
   \]
   so
   \[
   (a-D')+(b+1)D'=a+bD'.
   \]
   The proposed measure is invariant, not strictly decreasing. Moreover, a support sum is not automatically compatible with a branching rewrite, support merging, or cancellation. The alternative lexicographic measure is only suggested and not verified. Therefore termination—and hence existence of the claimed normal form by this reduction-system argument—is unproved. Claims depending on the L5 normalization/census are not certified.

7. **JUSTIFICATION GAP — the recarry arithmetic is correct, but its hypotheses and natural-subtraction bookkeeping are omitted from the formal plan.**  
   Quote: “`(μ₂−j′)E₂ + kδ − (j−j′)E₂ ≥ (μ₂−j)E₂ + δ` for `k ≥ 1`” ([line 95](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:95)).  
   With `j′ ≤ j ≤ μ₂`, the left side simplifies exactly to `(μ₂-j)E₂+kδ`, so the inequality is faithful to EFF.GENTOW3.24 ([spec line 730](/data/users/asvin/math-and-lean/p-adic-splitting-densities/spec/EFF-GENTOW3.md:730)). “Recarry moves only upward in `j`” is also faithful. But those order hypotheses are essential when the expression is implemented with `Nat` subtraction, and the requisite division-uniqueness/upward-recarry lemma is still only cited, not identified.

8. **CRITICAL ERROR — Corollary A is not C.72’s `shadow_floor` statement.**  
   Quote: “Corollary A (= C.72’s clause (i), `shadow_floor`). `WT(shadowDev − dev) ≥ Θ_j`” ([line 99](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:99)).  
   `shadowDev T f j - dev (composedKey T) f j` is an element of `Polynomial O`, whereas the proposed `WT` is on `Polynomial (Polynomial O)`. The actual C.72 statement is
   `↑(T.theta μ₂ j) ≤ dv2Hgt ... (shadowDev ... - dev ...)` ([C72 line 224](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C72.lean:224)). Thus Corollary A is neither type-correct as displayed nor identical to the target until the entire L6 conversion is established. The numeric threshold itself is quoted correctly: `T.theta μ₂ j = (μ₂-j) * T.E₂ + T.margin` ([C71 line 152](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C71.lean:152)).

9. **JUSTIFICATION GAP — L6 substantially underestimates the weight-to-height conversion.**  
   Quote: “this should be close to definitional … `dv2Hgt` IS the cleared min over the digit’s slots” ([line 111](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:111)).  
   `dv2Hgt` unfolds to `dvSupp`, whose entries are `e₂ • dvHgt + u₂i`; `dvHgt` further unfolds through `stageHeight`, `suppVal`, `npHgt`, and `dev`. Therefore the desired identification requires flattening nested finite infima, proving the relevant `dev` calls recover the proposed reduced digits, covering the finite ranges, and handling zero digits and cancellation. “Heights separate classes” and the residue-field grading are additional content, not definitional reduction. The conclusion may be true, but it is a major missing theorem rather than a near-definitional annex.

10. **JUSTIFICATION GAP — Corollary B’s target expression matches C.52, but the claimed derivation does not.**  
    Quote: “Corollary B … = C.52’s `dvAbove_boxMonomial` … L1–L5 applied to a single monomial” ([line 102](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:102)).  
    The numeric expression does match the goal:
    `↑(F.e₁*T.e₂) * addVal c + ↑(slotOffset T a b + j*T.E₂)` ([C52 blocked line 74](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C52_BLOCKED_2026-08-18.md:74)). The coercions and slot expression are faithful. But `DvAbove` means a universal bound over every `Φ′`-development index,
    `∀ i, w ≤ e₂ • dvHgt F P i + u₂*i` ([C52 line 80](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C52.lean:80)). A branch-weight statement in a free polynomial does not yield this definition without the same flattening/development theorem missing in L6. Consequently L1–L5 alone do not discharge the goal “verbatim.”

11. **CRITICAL ERROR — the document does not clear C.52’s exact purity and residual obstructions.**  
    Quotes: “the whole difficulty … lives in the REDUCTION” ([line 60](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:60)); “the only [genuinely valuation-theoretic step] in the whole engine” ([line 117](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:117)); “Corollary C … Membership `f ∈ 𝒯 ↔` digit floors” ([line 106](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:106)).  
    C.52’s obstruction inventory explicitly requires more than lower-bound combinatorics: `IsDvPure` closure under products/powers and normalized `dvResPoly` multiplicativity or an exact power theorem ([blocked record line 155](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C52_BLOCKED_2026-08-18.md:155), [retirement route line 180](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C52_BLOCKED_2026-08-18.md:180)). Neither L1–L6 nor the census proves those exact/purity claims. C.118’s capped congruence transports visible reads; it does not create purity or prove the required normalized residual power identity. Therefore Corollary C and the claim that this one engine clears all C.52 legs break independently of the L5 termination failure.

12. **JUSTIFICATION GAP — the document overstates EFF.GENTOW3.25 when claiming the faithful band is automatic.**  
    Quote: “C.72 `shadow_floor`/`shadow_faithful_band` | literally the ledger’s clause (i)+(ii)” ([line 15](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:15)).  
    The source says “(ii) is (i) restated” ([spec line 763](/data/users/asvin/math-and-lean/p-adic-splitting-densities/spec/EFF-GENTOW3.md:763)), but the actual Lean carrier asserts both equality of finite heights and equality of `dv2Res`, under an `hval` guard ([C72 line 229](/data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal/Uniformity/ChapC/C72.lean:229)). Turning a lower bound on the height of a difference into those two conclusions requires ultrametric exactness and residue-stability lemmas. The document contains no node for that passage and overlooks C.72’s documented drain-stratum qualification.

13. **JUSTIFICATION GAP — the numerical certification is presented too broadly.**  
    Quote: “the box-monomial floor (Corollary B / `dvAbove_boxMonomial`’s exact statement) EXHAUSTIVELY” ([line 162](/data/users/asvin/math-and-lean/p-adic-splitting-densities/docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md:162)).  
    The tests concern one specialized `s2` slice and bounded exponents/degrees. They may exhaust the script’s finite test range, but they do not exhaust the universally quantified Lean statement over arbitrary DVRs, frames, tower data, coefficients, and indices. They cannot certify L1’s general convolution law, L3’s arbitrary lifts, L5 termination, or the `DvAbove` conversion.

**verdict NEEDS-REDESIGN** — the central weight is not well-typed as specified, the stated termination measure is false, and the proposed engine omits the exact purity/residual mechanisms required by C.52.
