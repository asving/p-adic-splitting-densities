# Codex THIRD FINAL-CONFIRMATION audit — MOVESS_LEAN_BLUEPRINT_2026-07-28.md REV 6 (run 2026-07-27)
Verdict: REJECT (1 crit / 7 gap). Prompt: /tmp/leanaudit/movess_final3_prompt.txt; raw output: /tmp/leanaudit/movess_final3_verdict.txt.

I’m sweeping the structural repairs first—especially the verdict equivalence, all-prime domain, read-off coverage, and the split gate units—then I’ll check the remaining statements against their exact displays and hypothesis tags.
1. **CRITICAL — U-29b3 makes the promised n = 2 consistency instance impossible.**

   Offending spec:

   > **U-29b3 `n2_degcons_scs`** … “the SCSData laws for the **one-outcome roster**”

   This conflicts with:

   > **U-29c** … “the single active entry is `< 1`”

   and:

   > **U-29e** … “the solve's denominator is `q² + q + 1`”

   With one outcome, `part1` and `rep_indep` force its measured row mass to be 1. If it is the `kcol` outcome, the sole kernel entry evaluates to 1, contradicting E0 and U-29c. If it is terminal or split, `K = 0`, so the determinant/solve denominator is a unit, not `q² + q + 1`. Thus the explicit non-vacuity instance cannot inhabit all advertised structures simultaneously.

2. **GAP — the polynomial degree burdens remain unpinned.**

   Offending spec:

   > `structure PolyGeom where`  
   > `  degBound : ℕ`  
   > `  deg_le : count.natDegree ≤ degBound`

   and:

   > `tgP : ∀ e τ (o : T.Out e τ), PolyGeom`  
   > `jP  : ∀ e τ (o : T.Out e τ), PolyGeom`  
   > `ιP  : ∀ e τ (ε : M.EntShape e τ), PolyGeom`

   The note requires the specific bounds `W_loc(m)`, `W_state(s)`, and `W_ent(ε)`. Here `degBound` is unconstrained data and can always be chosen after the polynomial. Consequently the CL-6/INIT-RAT degree-bound hypotheses are not represented.

3. **GAP — CL-17(ii)’s production hypothesis is reduced to arbitrary rational interpolation.**

   Offending spec:

   > `WshP : Shape T → PolyGeom`  
   > `WshVal : Shape T → ℚ → ℝ`  
   > `wsh_interp : … evalAt … (WshP Ŝ).val … = WshVal Ŝ q₀`

   The frozen note requires each `W_Ŝ` to be produced by the stated C.1.5 node volumes, CTS/[1] counts, XHD-s height sums, and the `(SIB)` COUNT face. No field relates `WshP` or `WshVal` to that machinery, and no nonnegativity/mass condition is imposed. Arbitrary interpolated rational functions satisfy this interface.

4. **GAP — U-29b1 remains a hidden multi-lemma unit.**

   Offending spec:

   > **U-29b1 `n2_ledger_counting`** … “LedgerIV items (1)–(5): xhd (sum + two-sided exactness), d4r0, part1, rep_indep, meas_card”

   This combines at least eight independent obligations, including two-sided exactness and eventual card-ratio identities. It is not one display or a short unit.

5. **GAP — U-29b2 remains a hidden multi-lemma unit.**

   Offending spec:

   > **U-29b2 `n2_ledger_flow`** … “kstep_one/hmc … act_target, init_agg/init_count/ent_count_card, comp_once”

   These are distinct kernel-factorization, ACT, entrance-counting, and height-summation displays. The rev-6 split has not reduced this to one-display units.

6. **GAP — U-29d1 remains a hidden multi-lemma unit.**

   Offending spec:

   > **U-29d1 `n2_rs1bundle`**: “`recursion_meas`/`xrb`/`β_bdd`/`βfull`/`rexact` hold by construction”

   Boundedness, the measured recursion, XRB, and exact/full agreement are separate substantive claims. “By construction” does not provide a one-display unit sketch.

7. **GAP — U-29d3 remains a hidden multi-lemma unit.**

   Offending spec:

   > **U-29d3 `n2_rs4chain`** … “Sigmas … PrimePools … decidedTotal … with `x3_total`/`rs1_equates`/`rsh_interp`”

   This combines roster exactness, the all-prime domain, X.3 totality, RS.1 aggregation, and symbolic/measured interpolation. These cannot fit one short statement/proof unit.

8. **GAP — the declaration-location repair is internally contradictory.**

   Offending specifications:

   > “**all of §2.E live in `MovesS/Interfaces.lean`**”

   versus:

   > “### 2.E `MovesS/SyncDefs.lean`”

   Therefore the promised import/declaration DAG does not uniquely specify where W-1/W-2/etc. are declared.

The `vEquiv + vdeg_spec + sig_exact` repair itself is sound: bijectivity prevents extra or missing verdict labels, and `sig_exact` then selects exactly all degree-`n` multisets—including precisely the five displayed types at `n = 3`. The all-prime iff, generic carriers, and typed `ReadOffBundle` also repair their stated rev-5 defects.

Counts: **1 CRITICAL, 7 GAP**

**REJECT (1 crit / 7 gap)**
