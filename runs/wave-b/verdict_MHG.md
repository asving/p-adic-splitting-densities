# Verdict — MHG closure of MH.8 and X1

**Date:** 2026-08-27

**Unit:** MHG (MATH)

**Inputs:** `docs/in-progress/HENSEL_ENGINE_2026-08-26.md` at its post-MHDISP/MHFIX
state; `runs/wave-b/verdict_MHDISP.md`

**Overall:** **both assigned gates PROVED.**  MH.8's bounded-window comparison, reverse
transport, and assembled graded limit are Lean-proved in the probe.  X1 is Lean-proved in
the stronger singleton-side form.  Theorem A and the complete engine are still not proved,
because the independent MH.1 transcription and downstream assembly nodes remain open.

## Gate verdicts

| gate | verdict | result |
|---|---|---|
| MH.8 | **PROVED** | For `deg(a)<d`, with `D′=F.e₁F.f₁`, `A=ℓF.e₁`, and `C_d=ℓF.h(D′-1)+u(d-1)`, proved `W(a)≤ℓ•(F.e₁•gaussVal(a))+C_d`, hence `A N+C_d≤W(a) ⇒ N≤gaussVal(a)`.  Proved the reverse `N≤gaussVal(a) ⇒ A N≤W(a)`, and assembled the exact degree-bounded graded-limit contract. |
| X1 / OPEN-4 | **PROVED** | If `g` is `(u′,ℓ′)`-pure and `u′ℓ≠uℓ′`, every `(u,ℓ)`-side abscissa equals `0` or every one equals `n=deg(g)/D′`, according to the cross-product ordering.  Therefore `dvSideMax=dvSideMin` and `dvSideDeg=0`. |

## MH.8 proof disposition

The repaired upper comparison has two finite losses and no hidden subtraction:

1. An inner digit `B` has `deg B<D′`.  A coefficient attaining `gaussVal(B)` occurs at
   `i≤D′-1`, so the definition of `stageHeight` gives
   `stageHeight(B)≤F.e₁•gaussVal(B)+F.h(D′-1)`.
2. For `a=Σ_j B_j F.key^j`, monicity gives `gaussVal(F.key^j)=0`; finite-sum
   ultrametricity gives `min_j gaussVal(B_j)≤gaussVal(a)`.  An attaining outer index
   satisfies `j≤d-1`.  Evaluating `dvSupp` there yields the stated upper comparison.
3. The forward conversion cancels the finite natural summand only after splitting off the
   `gaussVal(a)=⊤` case.  The positive scale is `A=ℓF.e₁`.
4. The reverse conversion uses public `C118a.dvSupp_min_congr` against zero and public
   `C130s6.dvSupp_zero_eq_top`; it does not consume B.40's private helper.
5. For a `W`-Cauchy sequence, use `q(j)=p(Aj+C_d)`.  Telescoping plus the forward
   conversion makes `q` coefficient-adically Cauchy; public
   `exists_adicLimit_of_degree_lt` supplies `P`; reverse transport and one more telescope
   recover `j≤W(P-p(j))`.

This directly repairs MHDISP finding 7 in the required direction and controls the exact
fixed window loss.

## X1 proof disposition

Let `H_j` be the finite height at a new-side abscissa `j`, and
`n=g.natDegree/D′`.  Old purity gives
`ℓ′H₀=ℓ′Hₙ+u′n`.  Comparing the old supporting-line inequalities with the
fact that `j` is no higher than either endpoint at the new direction gives:

* `j>0 ⇒ uℓ′≤u′ℓ`;
* `j<n ⇒ u′ℓ≤uℓ′`.

Since the cross-products differ, one implication forces every `j` to be `0`, and the
other ordering forces every `j` to be `n`.  This is the requested short convexity
argument, formalized directly from the support inequalities.

## Lean verification

Created `leanfinal/scratch/MHG_probe.lean` and ran:

```text
cd leanfinal
lake env lean scratch/MHG_probe.lean
```

Result: **exit 0**, zero `sorry`, zero declared `axiom`.  The probe proves
`stageHeight_le_gaussVal_add_loss`, `inf_devGauss_le_gaussVal`,
`dvSupp_le_scaled_gaussVal_add_window`, `gaussVal_of_shifted_dvSupp`,
`reverseTransport`, `exists_dvGradedLimit`, and `otherSlope_pointSide`.  Every printed
axiom footprint is exactly `[propext, Classical.choice, Quot.sound]`.

## Fleet ruling

* **Theorem A may not yet be declared proved.**  Its MH.8 leg is closed, but MH.1 has not
  landed and MH.5/MH.7 plus the stated perturbation/assembly dependencies remain.
* **The full MH engine Lean fleet may not yet fire** under the existing MHDISP/MHFIX
  ruling, because MH.1 is still only math-proved/transcription-ready and the proved MH.8/X1
  declarations still live in scratch rather than public modules.
* **MH.8 and X1 may be promoted/transcribed now.**  They are no longer mathematical,
  statement-shape, or elaboration gates.  Once MH.1 lands and these probe theorems are
  promoted, all three landing conditions are green and the dependent fleet may be
  rescheduled.

## Deliverables touched

* `docs/in-progress/HENSEL_ENGINE_2026-08-26.md`
* `leanfinal/scratch/MHG_probe.lean`
* `runs/wave-b/verdict_MHG.md`

No commit was made.
