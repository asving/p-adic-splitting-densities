# Assumed vs. Proven — the Lean uniform-rationality formalization

**Project:** `forum-sigma/lean_urat/LeanUrat/`
**Re-verified:** 2026-06-22 (own `lake env lean LeanUrat/AxChk_baseline.lean` `#print axioms` on all 55 qualified constants; 0 `sorryAx`; aggregate `LeanUrat.olean` present and loadable)
**Scope:** the only-Montes (count-native) rationality/decomposition/palindromy path culminating in `goal_theorem_montes`, after the 2026-06-21 box-wise refactor.

This file is the authoritative ledger. It mirrors §"What the Lean formalization ASSUMES vs. PROVES" (`\label{sec:ledger}`) of `DECOMP_BLUEPRINT.tex` and the companion `paper/certificate.tex`, and matches the `#print axioms` reality exactly.

---

## Ground rule (enforced mechanically)

- **PROVED** = a Lean `theorem` whose `#print axioms` contains *only* the three Lean-core axioms `{propext, Classical.choice, Quot.sound}` and *no* `sorryAx`.
- **ASSUMED** = a declared `axiom`, OR a hypothesis (structure field / theorem argument) that the conclusion is stated *modulo*.
- "Sorry-free modulo axioms" is **NOT** "proved". Every headline below lists which axioms it depends on.

---

## ASSUMED (exhaustive, beyond the 3 Lean-core axioms)

### (A1) The minimal box-Haar / equidistribution axiom — the single irreducible measure residue

Carried as **two structure fields** of `MontesAxiom.MontesData` (NOT a global `axiom`; hypothesis-discharged, so it does NOT surface in `#print axioms`):

- `boxMeasure : CountCell → ℕ → ℚ` — the abstract per-box (p-adic Haar) volume of one cell.
- `boxHaarEquidist : ∀ c q' > 1, boxMeasure c q' = countCellCoeff c q'`
  where `countCellCoeff c q = (q^δ)^(dS-1) · bb1Value c.polygon q`.
  Asserts: the per-box Haar volume **equals** the proved box-volume × residual-count value.
- `nodeMeasure_boxSum : ∀ T, Tendsto (N ↦ stratumCount T N / q^(nN)) atTop (nhds (Σ_{cells c} boxMeasure c q · ∏_children clusterCount … / countPivot))`
  Asserts: the node measure **exists** and is the **box-additive** assembly over the cell partition.

**What is assumed** = exactly: (i) the abstract per-box Haar volume IS the proved closed value (box-Haar normalization `T_BB1` + C2 residual equidistribution `T_BB3`), and (ii) the node measure exists and is box-additive. The RHS factors (`bb1Value`, the `(q^δ)^(dS-1)` residual count, the box-additivity arithmetic) are all PROVED (see P1/P2/P3); only the *identification* of the abstract Haar volume with that proved value is assumed.

This is the genuine **measure wall**: mathlib v4.31.0 has no p-adic Haar measure, so the existence/normalization of `boxMeasure` cannot be constructed in Lean. It is **not** a renamed conclusion and **not** a def-unfold cheat — the asserted equality is to a separately-proved lattice/finite-field value, and the fields assert NO rationality, uniformity, or palindromy.

### (A2) The remaining MontesData / CountingModel structure fields (GMN count shadow, hypotheses)

None carries rationality / the conclusion:
- `shapesOf`, `partition` (unique-tree disjoint partition `decidedCount σ N = Σ_T stratumCount T N`);
- `treeSize`, `cells`, `cells_descend` (strict descent — count shadow of `omCells`/`descend_size_lt`, carried as FIELDS, not the `PadicMeasure` axioms; supplies well-foundedness);
- `finiteTermination` (GMN Thm 4.18, ≤ n leaves);
- elementary tail bounds: `undecided_le_split` (≤), `sepTail_tendsto` (separable pool → 0), `discriminantTail_envelope` (q^{-N} root-count envelope) — bounds, NOT the conclusion `U_N → 0` (which is DERIVED, see P6).

There is **no** `undecided → 0` field and **no** `C_T is rational` field — those are theorems.

### (A3) `tame_functionalEquation` (declared `axiom`, `Interface.lean`)

The genuine §5 H-tame input: an abstract `DensityFoundation`'s density admits a palindromic rational representative at tame primes. **Only non-core declared axiom** in the headline footprint; appears **only** on `goal_theorem_montes` (and the witness instance), NOT on any pure-rationality constant. Asserts nothing about the count-native `Σ_T C_T` directly — the link is via `hbridge`.

### (A4) `hbridge` (hypothesis argument of `goal_theorem_montes`, NOT an axiom)

`∀ q' > 1, F.density n σ q' = Σ_T coeff T q'`. The honest measure-wall identification ("abstract foundation density coincides with the count-native OM tree-sum"). RHS is an arbitrary function; the equality asserts NOTHING about rationality/palindromy/closed form. Introduces no axiom.

### NOT assumed (verified ABSENT from every audited footprint)

The `PadicMeasure` measure-route axioms — `clusterMeasure`, `AX_cellRecursion`, `AX_columnMeasure`, `omCells`, `descend_size_lt` — are genuine `axiom` declarations in the **dead** `PadicMeasure` module, and are absent from `#print axioms` of `goal_theorem_montes` and of every rationality/decomposition constant. No `sorryAx` in any audited footprint (the two flagged `sorry`s at `L3.lean:145,168` are off-path; the path uses sorry-free `L3Squarefree.card_squarefreeMonicDegree` and sorry-free `L3.card_monicDegree`).

---

## PROVED (theorems, core-only `#print axioms = {propext, Classical.choice, Quot.sound}`, no sorryAx)

| # | Theorem (qualified) | Content |
|---|---|---|
| P1 | `MontesAxiom.boxVolume_eq` | **Box-volume `T_BB1`**: Newton-box volume = `(1-Q⁻¹)^V · Q^{-A} = bb1Value` (re-exposes `L4.cellVolume_eq`, a `Finset.prod` collapse). |
| P2 | `MontesAxiom.residualBoxCount` (+ `residualBoxCount_eq_factor`) | **Residual-config count `T_BB3`**: #non-squarefree monic deg-dS over `F`, `|F|=Q`, is `Q^{dS-1}`; inline from sorry-free `L3.card_monicDegree` + `L3Squarefree.card_squarefreeMonicDegree`. Tie to the `(q^δ)^{dS-1}` factor. Genuine finite-field count, not a free monomial. |
| P3 | `MontesAxiom.clusterCount_boxSum` (+ `clusterCount_rec`) | **Box-additivity**: clusterCount = `List.sum` of per-box measures over the cell partition / pivot. Pure `List.sum` arithmetic. |
| P4 | `MontesAxiom.MontesData.nodeMultiplicativity` | **Per-node factorization (now a THEOREM)**: `lim_N stratumCount T N / q^{nN} = clusterCount … T q`. DERIVED from P1×P2×P3 + (A1). Was previously one opaque carried field. |
| P5 | `OMInduction.clusterVol_isRational` | **Geometric collapse / OM induction**: well-founded strong-induction over `treeSize`; divided sum-of-products recursion with strictly-smaller children + rational coeffs + pole-free pivot ⇒ uniform rational fn of q. Fed by `countCellCoeff_isRational`, `countPivot_isRational`, `countPivot_ne`. |
| P6 | `MontesAxiom.MontesData.undecidedVanishes` | **U_N → 0**: DERIVED by squeeze from `undecided_le_split` + `sepTail_tendsto` + `discriminantTail_envelope`. Not assumed. |
| P7 | `MontesAxiom.MontesData.countingDensity_eq_sum_coeff` | **Decomposition `ρ = Σ_T C_T`**: `tendsto_nhds_unique` between the decided limit (`density_isLimit`) and the finite-sum limit (`partition` + `nodeMultiplicativity`). Genuine limit-interchange, NOT `rfl`. `countingDensity := densityVal` (carried decided limit), not defined as `Σ_T C_T`. |
| P8 | `MontesAxiom.MontesData.coeff_isRational`, `countingDensity_isRational` | **Rationality of every C_T and of ρ**: generic engine (P5) + finite-sum closure. Faithful `RatFn.IsRationalFn`, numerators genuinely q-vary (residual `X^{δ(dS-1)}`, box `(X-1)^V/X^{V+A}`). |
| P9 | `L7.tame_to_all_primes`, `L7.isPalindromic_of_agree` | **Palindromy transfer**: ℚ(t) identity theorem (`Polynomial.eq_zero_of_infinite_isRoot`), degree-robust `Interface.IsPalindromic` `R(1/x)=R(x)`, onto the SAME count-native num/den. |

---

## Headline footprints (verbatim `#print axioms`, 2026-06-21)

```
goal_theorem_montes        → [propext, Classical.choice, LeanUrat.tame_functionalEquation, Quot.sound]
countingDensity_isRational → [propext, Classical.choice, Quot.sound]
countingDensity_eq_sum_coeff → [propext, Classical.choice, Quot.sound]
coeff_isRational           → [propext, Classical.choice, Quot.sound]
C                          → [propext, Classical.choice, Quot.sound]
undecidedVanishes          → [propext, Classical.choice, Quot.sound]
nodeMultiplicativity       → [propext, Classical.choice, Quot.sound]    (DERIVED, was a field)
stratum_tendsto_C          → [propext, Classical.choice, Quot.sound]
boxVolume_eq               → [propext, Classical.choice, Quot.sound]
residualBoxCount           → [propext, Classical.choice, Quot.sound]
residualBoxCount_eq_factor → [propext, Classical.choice, Quot.sound]
clusterCount_boxSum        → [propext, Classical.choice, Quot.sound]
clusterCount_rec           → [propext, Classical.choice, Quot.sound]
OMInduction.clusterVol_isRational → [propext, Classical.choice, Quot.sound]
montes_bundle_nonempty     → [propext, Classical.choice, Quot.sound]
montes_full_instance       → [propext, Classical.choice, LeanUrat.tame_functionalEquation, Quot.sound]
```

`goal_theorem_montes`: NO `clusterMeasure` / `AX_cellRecursion` / `omCells` / `descend_size_lt` / `sorryAx`. Rationality/decomposition path = Lean core only.

(Note: `DensityFoundation_nonempty` carries `PadicMeasure.clusterMeasure` because its `witnessOMBridge`/`witnessFoundation.clusterVolume` references the old measure route. This is the OLD `∀F` goal_theorem witness and is OFF the only-Montes path — it does not appear in `goal_theorem_montes` or any rationality constant.)

---

## Non-vacuity (the Witness nit — RESOLVED)

**The flag (audit):** `Witness.DensityFoundation_nonempty` inhabits only `DensityFoundation` (density ≡ 0), which is NECESSARY but NOT SUFFICIENT for `goal_theorem_montes`: `hbridge` couples `F` to a `MontesData D`, and density-0 is incompatible with any non-trivial D.

**Resolved:**
- `Witness.montes_bundle_nonempty` (core-only) — complete coupled witness `q=2,n=0`: `trivM : CountingModel`, `trivD : MontesData` (new box-wise fields: `boxMeasure := countCellCoeff` so `boxHaarEquidist` is `rfl`, `nodeMeasure_boxSum` the constant limit), `trivF` whose density IS the count-native tree-sum (so `hbridge` holds by `rfl`), with **non-trivial** density `g_σ ≡ 1`.
- `Witness.montes_full_instance` (= `goal_theorem_montes` applied to the bundle) — sorry-free, footprint `[propext, Classical.choice, tame_functionalEquation, Quot.sound]`.
- `DensityFoundation_nonempty` docstring corrected to drop the prior `goal_theorem_montes` over-claim and point at the coupled witness.

So `goal_theorem_montes` is demonstrably non-vacuous over genuine inhabited types, and the new minimal box-wise axiom is itself satisfiable.

**Measure wall stays honest:** `trivM` is a trivial degree-0 model, NOT the paper's p-adic ρ. No genuine p-adic Haar instance of `boxMeasure` is (or can be) constructed in mathlib v4.31.0. The Lean development proves the **conditional** statement: *given* the GMN count shadow + the minimal box-Haar identification, the counting density is a uniform rational, palindromic function of q. Faithful conditional theorem, not an unconditional construction of ρ.

---

## Audit findings — status

| Finding | Status |
|---|---|
| Semantic faithfulness (4 checks: density is the decided limit; rationality tied to it; hbridge honest; palindromy transfers) | PASS (audit), re-confirmed |
| Axiom footprint = `{propext, Classical.choice, Quot.sound, tame_functionalEquation}` | VERIFIED (own `#print axioms`) |
| Footprint/bugs (no false-modulo-sorry / unconstrained-universal / conclusion-as-hypothesis / def-cheat / off-path sorry leak) | PASS (audit), re-confirmed |
| Engine excludes non-rational targets (`montesData_forces_rational` + `not_isRationalFn_alt`) | Confirmed by audit (scratch); structurally forced content |
| **Witness nit** (DensityFoundation-only non-vacuity over-claim) | **FIXED** (`montes_bundle_nonempty` / `montes_full_instance`; docstring corrected) |
| Off-path `sorry`s at `L3.lean:145,168` | REMAIN (honest; off the audited path; path uses sorry-free `L3Squarefree`/`card_monicDegree`; no `sorryAx` in any footprint). True finite-field counts; re-proved sorry-free in `L3Squarefree.lean` / `L3Gauss.lean`. |

---

## Honest residual gaps

1. **The minimal box-wise axiom (A1) is genuinely irreducible.** It is the per-box Haar-existence + residual-equidistribution + box-additivity content. Cannot be reduced further: mathlib v4.31.0 has no p-adic Haar measure. The RHS is proved; only its equality with the abstract Haar volume is the wall.
2. **No genuine p-adic ρ instance.** The only inhabitant is the trivial degree-0 `trivM` (non-vacuity witness, not the paper's ρ). The theorem is conditional on the assumed ledger.
3. **Off-path `sorry`s** at `L3.lean:145` (`card_squarefreeMonicDegree`), `L3.lean:168` (`gauss_necklace_count`) — true counts, NOT on the audited path; superseded by the sorry-free re-proofs the path actually uses.

---

## Independent cross-checks (EVIDENCE, not proof) — reproducible

Run outside Lean; **evidence** that the symbolic arithmetic the Lean modules prove matches independent computation. Not part of the formal proof. Scripts (system `python3` + `sympy 1.13.3`, exact; exhaustive `GF(Q)` enumeration):

- **`_cert_crosschecks.py`** — 25 exact checks, all PASS (re-run 2026-06-22). Covers: self-loop exponents `w(s)=s(s+1)/2-1` (=2,5,9,14); C1 `selfLoopExponent=blockExponent-1` (s≤7); `closedI2=q/(q+1)`, `closedI3=q³(q²-q+1)/((q+1)Φ₅)`; L4 column-product `(1-Q⁻¹)^V Q^{-A}`; L3Squarefree `S(m)=Qᵐ-Qᵐ⁻¹` **for d≥2** + recursion (∗) `Qⁿ=ΣS(n-2j)Qʲ` (n≤8); L3Gauss `d·N_d=Σμ(e)Q^{d/e}` and `Σe·N_e=Q^d` by GF(Q) enum (Q∈{2,3,5}, d≤4); M1 `(q-1)P_n=q^{n+1}-1`; T_BB3 non-squarefree count `Q^{d-1}` **for d≥2** by enum; n=3 type densities palindromic & sum=1; n=4 wild slope-1/2 atom `q/(q+1)` vs recorded oracle (incl. wild p=2 Artin-Schreier, obs 0.6664 vs 0.6667); n=6 deep-wild β_(6,1)=q²(q-1)(q²+1)/(q⁵-1)=20/31 at p=2.
- **`_reconcile_om_bcfg.py`** — symbolic OM density engine vs BCFG, n=2..6, `sympy.simplify(OM-BCFG)==0` for every `P(n,r;q)` and moment; output `results/reconcile_om_bcfg.json` (`all_match: true`). Engine reproduces BCFG root-count distribution + moments EXACTLY through n=6 (incl. the first deep-wild OM-order-3 branch at n=6, 34 types), with `Σ_σ ρ(n,σ)=1` at every n.

**Honest note on the d≥2 hypothesis.** The Lean theorems `L3Squarefree.card_squarefreeMonicDegree` and `MontesAxiom.residualBoxCount` carry the hypothesis `2 ≤ m` (resp. `2 ≤ dS`): at degree 1 every monic `x+c` is squarefree, so `S(1)=Q≠Q-1` and the non-squarefree count is `0≠Q⁰=1`. The cross-checks mirror this hypothesis exactly (test d≥2); the recursion (∗) holds for all n with `S(0)=1, S(1)=Q, S(m≥2)=Qᵐ-Qᵐ⁻¹`.

**PARI oracle status.** The PARI `factorpadic` binary / `cypari2` venv is **absent** in the current environment, so the oracle was not freshly run. The cross-checks reuse the previously recorded MC-oracle data (`results/n4wild_insep_p*_s30*.json`, `results/om_oracle_*.json`) as the empirical anchor and re-verify the symbolic predictions + comparison, which are reproducible. The oracle agreement is MC (z-scores), not a proof.
