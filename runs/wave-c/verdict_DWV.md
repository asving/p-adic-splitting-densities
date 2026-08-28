# Verdict DWV — adversarial verification of DWC

**Date:** 2026-08-28

1. Quote: “set `F0=leaf^2`, `μ=2`, `B'.Φ=leaf`, and `quot.F=leaf`” (§3.3), and “prove `RecenterStep`, `MP1StepCore`, then `MidPeelEmission`” (C5).

   Classification: **CRITICAL ERROR**

   Reason: Although `MP1StepCore.hmass` numerically accepts `16+16=32`, `hkey` makes `quot.Φ=leaf` and `hpeel` forces `quot.F=leaf`, contradicting the mandatory `BlockData.hkeyfree : IsCoprime quot.F quot.Φ` because a monic degree-16 polynomial is not coprime to itself.

2. Quote: “For `g=leaf^2`, prove actual principal slope membership, actual slope residual with `X+1` multiplicity one, and completed selected factor/base-change equality to `leaf`” (C4).

   Classification: **CRITICAL ERROR**

   Reason: The planned laws give `R5(leaf)=X+1` and `R5(leaf^2)=R5(leaf)^2=(X+1)^2`, so `ord_(X+1)=2`, not one; GN/FGMN therefore selects the whole multiplicity-two block (and if the theorem key is taken to be `leaf`, `leaf^2` lies in the separate key-power term), never one copy identified as `leaf`.

3. Quote: “The certificate checks … the formal mass-two recentering identity” (§1), and the certificate's final “the μ5 refinement is mass-two ready.”

   Classification: **JUSTIFICATION GAP**

   Reason: Its sparse model checks only degree, subtraction, and ordinary divisibility; it omits both quotient-block key-freeness and residual multiplicity, precisely the two predicates that refute the proposed input.

4. Quote: “Stop-line gates — all green before the fleet fires,” especially “R8 input gate. Prove `IsCoprime (leaf^2) (keyAt 4)` … Prove `μ=2` from the literal degree equation.”

   Classification: **JUSTIFICATION GAP**

   Reason: The ten gates omit a quotient-`BlockData` key-freeness gate, an actual `ord_ψ(R_λ(F0))=1` gate, and a GN valuation/key-index alignment gate; the listed R8 check concerns only the parent key `keyAt 4` and cannot catch either critical failure above.

5. Quote: “revised `RecenterStep` consumes it under the same existential owner” (G2), followed by “build successor block and quotient” (C5).

   Classification: **JUSTIFICATION GAP**

   Reason: The proposed amendment binds the analytic payload but adds no provenance/equality tying the other fields of `B'`—notably `B'.F` and `B'.T`—to the realized parent or transition, so an otherwise arbitrary synthetic `BlockData` can still serve as the advertised “successor block.”

6. Quote: “expose the `DeepTwistConjunctLive` arising-witness theorem and the ladder record with C5's live MP1 leg” (C6), while “The final capstone-wide universal supplier is outside this occurrence campaign” (§8).

   Classification: **JUSTIFICATION GAP**

   Reason: If “the ladder record” means the cited `LadderSupplyLive₂`, its `package`, `lb1`, universally quantified `mp1`, and universally quantified live `vartheta` fields do not follow from one C3/C5 occurrence, and the DAG contains no HE7A/LB1 construction or occurrence-to-universal quantifier gate.

7. Quote: “The single highest-risk node is C4,” together with G0/G1's “Land actual principal Newton-polygon … operators”/“Define the completed selected factor,” D3-03 and D3-10's new survival/convolution cores, and C3's “tau triangular spanning.”

   Classification: **JUSTIFICATION GAP**

   Reason: C4 is refuted rather than merely risky, while G0/G1 (absent analytic/completion infrastructure), D3-03/D3-10 (new multiplicative operator core), C3 (the TAU audit's open general-depth spanning theorem), and R3–R5 (new valuation realization, source thresholds, and canonical-letter descent) are each comparable research risks despite the blanket 30–60 minute “transcription unit” estimate.

## Verified controls (not findings)

- Independent recomputation gives `Dcum = (2,4,8,16)`, `E = (2,10,42,170)`, floor rows `4<5`, `20<21`, `84<85`, refinement floor `170<171`, and proper-continuation floor `340<341`; every margin is exactly one.
- Independent recursion from `C83.towerNorm` gives `towerNorm 2 85=(8,0,[0,1])` of polynomial degree `4`, `towerNorm 3 171=(1,1,[1,1,1])` of degree `15`, and `towerNorm 3 341=(16,0,[0,0,1])` of degree `8`.
- FGMN Definition 1.8 admits augmentation with any positive rational increment, Definition 3.1 does not require `e_i f_i≥2`, and Lemma 3.5 explains equal-degree refinement collapse in an optimal chain; thus `e'=1` operator data is source-admissible while correctly excluded from `DeepTower.hproper` as an additional proper stage. The actual operators and chain identification still belong behind G5.
- The outer divisibility direction `leaf ∣ leaf^2` is the right orientation for a selected factor of `g`; the failure is multiplicity/identification, not divisibility direction.

REJECT
