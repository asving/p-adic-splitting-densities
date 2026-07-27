# Codex FINAL CONFIRMATION audit — MOVESS_LEAN_BLUEPRINT_2026-07-28.md REV 4 (run 2026-07-27T14:47:43Z)
Verdict: REJECT (6 crit / 2 gap). Prompt: /tmp/leanaudit/movess_final_prompt.txt; raw output: /tmp/leanaudit/movess_final_verdict.txt.

1. **CRITICAL — `Sigmas` is an unconstrained menu, making RS.4 vacuously selectable.**

   Offending spec:

   > `Sigmas : Finset (Multiset T.VType)`  
   > `sig_ne : Sigmas.Nonempty`

   and U-28:

   > `(∑ σ ∈ C.Sigmas, Rsh … σ) = 1`

   The note sums over all verdict splitting types \(\sigma\). Nothing states that `Sigmas` is exactly that set, or even covers it. A singleton chosen to make `rs1_equates` true satisfies the blueprint. Deleting `sig_covers` without replacing it by a definition from the degree-\(n\) verdict roster leaves RS.4 strictly weaker and potentially vacuous.

2. **CRITICAL — W-1 inherits the same unrestricted-`Sigmas` weakening.**

   Offending spec:

   > `def W1_RS1SH … : Prop :=`  
   > `  ∀ σ ∈ C.Sigmas, ∀ p ∈ C.PrimePools, … = C.Rval σ p`

   RS.1-SH is the displayed identity for every applicable verdict type \(\sigma\), not merely for an arbitrary nonempty subcollection. Because `Sigmas` has no exactness condition, this pinned deferral does not faithfully pin RS.1-SH.

3. **CRITICAL — `PrimePools` is not pinned to base primes.**

   Offending spec:

   > `PrimePools : Set ℚ`  
   > `prime_sub : PrimePools ⊆ M.Pools`  
   > `prime_infinite : PrimePools.Infinite`

   `M.Pools` contains general prime powers. Thus `PrimePools` may consist of \(p^\delta\) with \(\delta>1\), or even powers of one fixed prime. The note’s RS.4 route uses the density identity at every base prime \(p\), followed by infinitely many prime evaluations. No field states that members of `PrimePools` are rational images of primes with exponent \(1\). Consequently `x3_total`, `rs1_equates`, and `rsh_interp` have different quantifier domains from the note.

4. **CRITICAL — U-24b lacks an infinite activity locus for each coordinate it identifies.**

   Offending spec:

   > “GIVEN an INFINITE pool set `S ⊆ M.Pools` with, at every `q₀ ∈ S`, a package `P` and the AVAgree read-off for every `(e, τA, σ')` consumed … any family `f` … equals `blockSolve`”

   `AVAgree` only speaks about `τA : P.Act`. If a fixed formal state \(\tau\) is inactive throughout, or at all but finitely many points of `S`, the read-off hypotheses say nothing about that coordinate. They may even be vacuous when `P.Act` is empty. Interpolation uniqueness therefore cannot establish equality for the full state-indexed family. The note’s cofinite all-active argument, or at least coordinatewise infinite activity, is missing.

5. **CRITICAL — the “absolute” base-change convention conflicts with nested substitution and the claimed pool coverage.**

   Offending specs:

   > `δ : ℕ+ -- ABSOLUTE base-change index`

   > `legFactor = … powSubst μ_j.δ (βlt …)`

   > `consumedDeltas T F := {1} ∪ (split-leg δ's …) ∪ …`

   > “these are ABSOLUTE indices … so leg-within-leg pools stay inside the roster”

   and:

   > `RegP … := ∀ e … ∀ δ ∈ consumedDeltas T F, Nonempty (PoolHyp … p^δ)`

   A nested `powSubst δ₂` inside a solution already evaluated through `powSubst δ₁` reaches \(p^{\delta_1\delta_2}\). Merely listing the individual roster indices does not ensure that product is in `consumedDeltas`. Conversely, if each stored `Member.δ` is genuinely absolute relative to the original base prime, nesting `powSubst` multiplies an already-absolute index and is semantically wrong. The specification must choose relative indices with multiplicative closure or absolute indices with non-nested evaluation; REV 4 asserts both incompatible readings. Thus `RegP`/`legs_reg` do not actually carry E0 over every consumed pool as the note requires.

6. **CRITICAL — W-10 omits positivity, so it does not pin unconditional/Tonelli convergence.**

   Offending spec:

   > `def W10_convergence … : Prop :=`  
   > `  … HasSum (fun f => FI.fibMass … f …) (B.βmeas …)`

   `FiberIface.fibMass` is an arbitrary real-valued function and has no nonnegativity law. `β_bdd` bounds only the final sum, not its summands. A conditionally convergent signed family can satisfy this `HasSum`, while the note requires a positive series bounded by \(1\), with rearrangements licensed by Tonelli. W-10 is therefore strictly weaker than the displayed convergence claim.

7. **GAP — U-24a1 is not plausibly typed as written.**

   Offending spec:

   > `B.βmeas … = ((1 - P.A)⁻¹ *ᵥ bhatMeas P B σ' h_ent) τA`

   `B.βmeas` and its measured split legs are `ℝ`, whereas `P.A : Matrix P.Act P.Act ℚ`. Matrix-vector multiplication requires a common scalar type. No mapped real matrix or explicit coercion is specified. This also obscures the exact statement used in the claimed active-subsystem derivation.

8. **GAP — U-29 violates the one-display decomposition requirement.**

   Offending spec:

   > “Constructs … simultaneous instances of ALL §2 structures: TableShape … MeasuredSide … LedgerIV, RatBurdens, SCSData, DegCons, PoolHyp … ShapeFam, RS1Bundle, RS4Chain … and CHECKS: the solve's denominator is \(q²+q+1\).”

   This is an extensive construction plus many independent law proofs, an escape proof, recursion proof, checksum setup, and a rational-function calculation. It cannot reasonably be one short unit or one-display sketch. It is a hidden multi-lemma batch, even though an explicit schema-consistency instance is an acceptable non-vacuity strategy.

Counts: **6 CRITICAL / 2 GAP**

**REJECT (6 crit / 2 gap)**
