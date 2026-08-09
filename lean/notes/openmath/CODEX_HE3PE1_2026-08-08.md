# HE3 pass PE1 — CODEX ADVERSARIAL VERIFICATION (independent model, fresh context) + ADJUDICATION

**Pass:** PE1 (first hostile pass on HE3). **Verifier:** Codex
`gpt-5.6-sol`, fresh context, charged quote-and-classify / fix-nothing.
Input: HE3_PROOF §§S1, S3–S6 pasted inline (31,115 chars; the sandbox
cannot read repo files on this box — the standing workaround).
**Prompt:** /tmp/he3_pe1_prompt.txt · **raw log:** /tmp/he3_codex_pe1.log.

## VERDICT OF THE PASS: 5 CRITICAL + 2 GAPS, ALL ADJUDICATED

Codex returned a strong report. Adjudication, finding by finding — and
the headline: **every CRITICAL finding is unreachable at μ ≤ 3, or is a
proof-display error whose conclusion survives a restatement. So the
unit's claim as graded at commit 3 — [GENHN-HE(μ)] UNCONDITIONAL for
μ ≤ 3 (degrees n ≤ 7), BOXED at μ ≥ 4 — SURVIVES the pass; two of its
statements are now sharper, and one new μ ≥ 4 hypothesis (SEP) is named.**

| # | Codex finding | adjudication | action taken (commit 4) |
|---|---|---|---|
| 1 | ramified base change: rescaling dv does not multiply a root-set cardinality; label can split; char \| ℓ can make the new residual inseparable | **UPHELD.** This unit had already found and boxed it (HE3-BOX-6, commit 3, BEFORE the pass); Codex sharpens it with the inseparability point | HE3-BOX-6 amended; branch marked BOXED in-line |
| 2 | labels/invariants NOT unchanged under EITHER base change; if Φ′ splits over O₁ the key degree drops from D′ to D′/gcd(f₁,c), so "each rational root contributes D′" is false | **UPHELD, and broader than my own box** (I had thought the unramified branch safe). Choosing c coprime to f₁ repairs it only when gcd(deg r, f₁) = 1 | in-line REPAIR note; both branches marked BOXED |
| 3 | HE3-3's integer-sampling independence is FALSE: three slopes inside one open integer interval give only 2 equations | **UPHELD.** Genuine error | LEMMA HE3-3 now carries hypothesis **(SEP)**, PROVED automatically for μ ≤ 3 (Σℓ_λd_λ = μ ≤ 3 permits at most one non-integral slope; three crammed slopes need μ ≥ 9) |
| 4 | HE3-2's proof asserts each summand has dv EXACTLY dv(A_i)+(i−j)κ, ignoring v(binom(i,j)) | **UPHELD as a proof error; the CONCLUSION survives.** Only the inequality is summand-wise; (b) is re-proved at the residue level, where binomials appear only via their images in K and the needed fact — (Z−s)^m ‖ R_λ ⟹ Z^m ‖ R_λ(Z+s) — is char-free | §S5 proof rewritten with the repair displayed |
| 5 | DEFINITION 2 ("every residual consulted is separable") contradicts §S6.3's stage-α step (which handles multiplicity m ≥ 2) | **UPHELD — a definitional inconsistency** | DEFINITION 2 restated: separability at TERMINAL nodes only (Ore-regularity at the leaf) |
| 6 | Galois-stability suppresses semilinearity: absolute Galois does not fix K; may act on a union of Frobenius-conjugate classes | **UPHELD as a gap.** §S4's universality-in-η supplies the compatibility but the composition is not written out; vacuous at f₁ = 1 (the battery's rows) | flagged in-line as an explicit JUSTIFICATION GAP |
| 7 | the "μ ≤ 3 composite-stage-free" exhaustion needs GENIND.A(I) (species partition), not just the quoted (IV) | **CORRECT AS AN OBSERVATION, not a defect**: GENIND.A(I) is a declared pinned supplier (§S0) and was simply not pasted into the verifier's input | no change; §S0 already pins it |

## WHAT THE PASS DID NOT FIND

No circularity (attack point 6 of the charge) and no defect in: LEMMA
HE3-1 / HE3-1′ (the resultant identity and evaluation display — the
engine, also the most heavily machine-checked leg at 115,662 identity
checks, 0 violations), LEMMA HE3-3 steps (1) and (2), the label read of
§S4, LEMMA HE3-5, or the μ ≤ 3 dictionary that the battery confirmed
against PARI on 947 jobs.

## GRADE AFTER PE1

Attempt grade **1/2** on the μ ≤ 3 statement (one hostile pass survived
with repairs, no CRITICAL finding surviving adjudication at μ ≤ 3);
μ ≥ 4 remains BOXED (HE3-BOX-6, now covering both base-change branches
and (SEP)). A second, model-diverse pass is owed before acceptance, and
it should be charged specifically at: the (SEP)-freeness claim for
μ ≤ 3, the at-most-one-non-rational-factor subtraction argument, and the
finding-6 semilinearity composition at f₁ ≥ 2.

---

## RAW CODEX REPORT (verbatim, first emission)

1. **CRITICAL ERROR — the ramified base-change argument simply assumes the missing factor \(\ell\).**

   > “Over \(O_2\) the slope \(\lambda\) becomes the integer \(\ell\lambda=u\) in the rescaled ladder … and (i) applies, giving the class sizes \(\ell\)-fold rescaled:
   > \[
   > |S_r|=D'\ell\deg r.
   > \]”

   Rescaling a valuation does not multiply the cardinality of a root set. After adjoining \(\Pi^\ell=\pi\), the key and the polynomial can split, and the original ramified label can split into several integer-slope labels. The integer-slope result counts those new labels separately; recovering their union requires exactly the ramification/conjugacy argument that HE3-4 is supposed to prove. “\(\ell\)-fold rescaled” is therefore unsupported and circular.

   Moreover, when the residue characteristic divides \(\ell\), the new integer-slope residual polynomial can become inseparable, so the previously proved separable linear-root case cannot automatically be applied.

2. **CRITICAL ERROR — labels and stage invariants are not unchanged under either base change.**

   > “\(\Phi'\) remains irreducible over \(O_1\) or splits into unramified-conjugate factors — in either case the SET of roots of \(f\) … the polygon \(P(F)\), and every label are UNCHANGED…”

   > “Again the root set and the labels of \(f\) are unchanged by the base change…”

   These conclusions do not follow from preservation of the geometric root set. If \(\Phi'\) splits, the stage key degree, residue degree, stage ring, normalization \(dv=e_1v\), and residual coefficient field all change. Irreducible residual factors \(r\) can split after unramified extension; ramified labels can split after the ramified extension. Thus labels are emphatically not unchanged.

   In the unramified case, applying the linear-root paragraph after \(\Phi'\) splits uses the new factor degree, not the original \(D'\). The claim that each new rational residual root contributes \(D'\) roots is unjustified. Consequently the counts cannot be transferred “verbatim” back to \(O\).

3. **CRITICAL ERROR — LEMMA HE3-3’s integer-sampling independence claim is false.**

   > “the functions \(\kappa\mapsto\min(\lambda,\kappa)\) for distinct \(\lambda\) are linearly independent…”

   > “for each pair of distinct slopes there is an integer \(\kappa\) with \(\min(\lambda_1,\kappa)\ne\min(\lambda_2,\kappa)\) up to the common-\(\kappa\) regime…”

   Take three distinct slopes in \((S,S+1)\), for example
   \[
   S+\tfrac14,\qquad S+\tfrac13,\qquad S+\tfrac12.
   \]
   Every allowed integer sample satisfies \(\kappa>S\), hence \(\kappa\ge S+1\), so all sampled functions are merely the constants \(\lambda_i\). Even adding the known total-root equation gives only
   \[
   \sum c_i=0,\qquad \sum c_i\lambda_i=0,
   \]
   which has a nonzero solution for three slopes. Integer samples therefore cannot recover the individual \(n_\lambda\).

   The proposed sample at \(\kappa_0=\lfloor\min\lambda\rfloor=S\) is illegal because the construction requires \(\kappa>S\). The bound on differences between rational slopes does not create integer gaps between them.

4. **CRITICAL ERROR — LEMMA HE3-2 ignores the valuation of binomial coefficients.**

   > “Each summand has \(dv\) exactly
   > \[
   > dv(A_i)+(i-j)\kappa
   > \]
   > by the SLOT LEMMA and \(dv(w)=\kappa\), giving (a).”

   The summand actually contains \(\binom{i}{j}\), so its valuation is
   \[
   dv(A_i)+(i-j)\kappa+dv\!\binom{i}{j}.
   \]
   For example, with \(i=p,j=1\), \(\binom p1=p\) has positive valuation in mixed characteristic and is zero in equal characteristic \(p\). A unique purported minimizer can therefore rise or disappear without any cancellation among attaining residues.

   The attempted qualification—

   > “The binomial coefficients may vanish in small characteristic; that only removes summands…”

   —does not repair the asserted equality, nor the later claim that off the supporting line a unique minimizing term guarantees equality. Thus the proof of the recentered polygon description fails, and HE3-4 and the stage-\(\alpha\) argument cannot use it.

5. **CRITICAL ERROR — the definition of “decided” conflicts with the stage-\(\alpha\) induction being used to prove the theorem.**

   > “A leaf \(\ell\) is decided iff along its history every residual polynomial consulted is separable…”

   But later:

   > “If the read refines at \((\lambda,s)\) (a residual root of multiplicity \(m\ge2\) — so the leaf is not decided at this node)…”

   A residual polynomial having a repeated root is not separable. If it was consulted anywhere in the leaf’s history, the leaf cannot later satisfy the stated definition of “decided.” Hence this stage-\(\alpha\) case cannot occur in the history of a decided leaf as defined. The induction either treats impossible histories or requires a different notion of decidedness.

6. **JUSTIFICATION GAP — the Galois-stability claim suppresses the nontrivial action on \(K\).**

   > “Each class \(S_{\lambda,r}\) is stable under \(\operatorname{Gal}(\bar K_0/K_0)\): Galois preserves \(dv\) and acts on residues through \(\bar k\)-automorphisms, and it permutes the roots of the irreducible \(r\)….”

   Absolute Galois does not generally fix the embedded copy of \(K\); it acts semilinearly and can send a polynomial \(r\in K[Z]\) to a Frobenius-conjugate polynomial. Stability requires proving that the root-dependent embedding
   \[
   K\hookrightarrow\bar k,\qquad \eta_\theta\mapsto\eta_\rho
   \]
   is transported compatibly when \(\rho\mapsto g\rho\). The quoted sentence does not supply that argument. Without it, the orbit argument may apply only to a union of conjugate label classes, whose size is larger than the stated \(N\).

7. **JUSTIFICATION GAP — the claimed exhaustion and base cases use external structure beyond the quoted descent inequality.**

   > “Therefore \(\mu=2\) and \(\mu=3\) are composite-stage-free: their leaves’ histories consist of order-1 reads and stage-\(\alpha\) refines only…”

   > “This exhausts the species (GENIND.A(I)) reachable inside a decided leaf’s history…”

   The numerical part quoted from GENIND.A(IV) does show that a stage-CS event satisfying those hypotheses cannot occur for \(\mu=2,3\). It does not show that all other possible events are exactly order-1 reads and stage-\(\alpha\) refines. That exhaustion relies on GENIND.A(I), which is not included. Therefore the asserted outright base cases and the claim that the recursion consumes no other recursive input are not established by the supplied document.
tokens used
18,684
1. **CRITICAL ERROR — the ramified base-change argument simply assumes the missing factor \(\ell\).**

   > “Over \(O_2\) the slope \(\lambda\) becomes the integer \(\ell\lambda=u\) in the rescaled ladder … and (i) applies, giving the class sizes \(\ell\)-fold rescaled:
   > \[
   > |S_r|=D'\ell\deg r.
   > \]”

   Rescaling a valuation does not multiply the cardinality of a root set. After adjoining \(\Pi^\ell=\pi\), the key and the polynomial can split, and the original ramified label can split into several integer-slope labels. The integer-slope result counts those new labels separately; recovering their union requires exactly the ramification/conjugacy argument that HE3-4 is supposed to prove. “\(\ell\)-fold rescaled” is therefore unsupported and circular.

   Moreover, when the residue characteristic divides \(\ell\), the new integer-slope residual polynomial can become inseparable, so the previously proved separable linear-root case cannot automatically be applied.

2. **CRITICAL ERROR — labels and stage invariants are not unchanged under either base change.**

