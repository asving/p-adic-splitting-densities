# Codex SECOND FINAL-CONFIRMATION audit — MOVESS_LEAN_BLUEPRINT_2026-07-28.md REV 5 (run 2026-07-27)
Verdict: REJECT (2 crit / 4 gap). Prompt: /tmp/leanaudit/movess_final2_prompt.txt; raw output: /tmp/leanaudit/movess_final2_verdict.txt.

I'm checking the repaired interfaces against the note's actual displays, with special attention to the multiplicative δ path, the degree-3 roster, and the all-active uniqueness locus. I'll also sweep the carried-forward units for any remaining semantic or non-vacuity defects.

1. CRITICAL — `sig_exact` does not pin the note's verdict vocabulary.

   Offending spec:

   > `sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n`

   `TableShape.VType` remains an arbitrary finite type and `vdeg` an arbitrary map. Nothing requires exactly one verdict type `(e,f)` for each valid pair with degree `e·f`. At `n = 3`, extra degree-1/2/3 labels produce more than the note's five types, while missing labels produce fewer. Thus the claimed "exactly the displayed five" does not follow from the Lean statement, and `RS.4` may sum over a different roster.

2. CRITICAL — `PrimePools` is only an arbitrary infinite subset of base primes, not all base primes.

   Offending spec:

   > `prime_base : ∀ q₀ ∈ PrimePools, ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)`

   together with:

   > `x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1`

   > `rs1_equates : ∀ p ∈ PrimePools, ...`

   This proves only `PrimePools ⊆ {base primes}`. It lacks the converse that every prime belongs to `PrimePools`. Consequently X.3, RS.1 evaluation, `rsh_interp`, and `legs_reg` are assumed only on an arbitrary infinite selection of primes. The note states these primewise claims for every prime and carries E0 to every relevant base-prime pool.

3. GAP — U-10 contradicts the declared one-coercion-point architecture.

   Offending unit:

   > `theorem ksub_pool ... :`
   > `(∀ βA : P.Act, 0 ≤ P.A τA βA) ∧ (∑ βA : P.Act, P.A τA βA) ≤ 1`

   R19/D11 explicitly says U-10 is stated over `ℝ` through `Aℝ`, but its actual statement remains over the rational matrix `P.A`. Its proof sketch passes through `rowVal`, `μcell`, and `tg_interp/j_interp`, all in `ℝ`, so an additional cast/order-transfer step is required and the claimed "NOWHERE else coerces" discipline is false.

4. GAP — U-24b still has no precise statement for coordinate coverage.

   Offending unit:

   > "the AVAgree read-off for every `(e, τA, σ')` consumed (the explicit `hread` bundle)"

   Neither "consumed" nor `hread` is defined. The all-active locus itself is correct: on `S ⊆ allActivePools M`, every state coordinate is active at every point of `S`, matching RS.2's all-active uniqueness route. But the proposed statement does not specify whether `hread` quantifies over every `e ∈ Icc 1 n`, every `τ : State e`, and every verdict multiset `σ'`. Hence total coordinate coverage cannot be audited from the unit spec.

5. GAP — U-29b remains a hidden multi-lemma unit.

   Offending unit:

   > "Proves the LAWS: `LedgerIV` … `DegCons`, the `SCSData` laws."

   `LedgerIV` alone contains the nine logically separate displayed inputs, including XHD exactness, disjointness, PART-1, REP, MEAS, HMC, ACT, INIT/ENT-COUNT, and COMP-TYPING. Adding `DegCons` and every SCS law cannot be one short, one-display unit. The split from U-29 did not decompose this proof obligation adequately.

6. GAP — U-29d still bundles several independent and substantially nontrivial obligations.

   Offending unit:

   > "`RS1Bundle` (`βmeas :=` the evaluated solve, so `recursion_meas`/`xrb`/`β_bdd` hold by construction …) and `RS4Chain` …"

   `RS1Bundle` requires boundedness, XRB, the guarded measured recursion, `βfull`, and exactness. `RS4Chain` additionally requires all-active E0 packages, `legs_reg` at every consumed pool, the exact roster, shallow interpolation, primewise X.3/RS.1 identities, and symbolic-density read-off. U-29c supplies only a package at `q₀ = 2`; the remaining pool and read-off obligations are hidden inside U-29d. This still violates the one-display decomposition requirement and leaves the advertised simultaneous inhabitation gate underspecified.

The DELTA-ABS repair is otherwise coherent: a shallow factor followed by nested split factors evaluates at
`((p^δ₁)^δ₂)… = p^(δ₁·δ₂·…)`; `powSubst_mul` gives the matching symbolic composition. Strict block-size descent allows at most `n−1` deep split factors after one shallow factor, so products of at most `n` factors cover the nested legs. `nested_delta_mem`, `RegP`, and `legs_reg` therefore have the right intended coverage.

Counts: 2 CRITICAL / 4 GAP

REJECT (2 crit / 4 gap)
