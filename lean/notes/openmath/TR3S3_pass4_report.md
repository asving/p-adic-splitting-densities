## Quote-and-classify

### GAP 1 — Def. 3.18 was added to PIN-GEN-i, but not to the pin’s owed verification leg

REVISION 2 successfully adds the missing operator to the attribution pin:

> “AND of Def 3.18 AT i = 3”

But the same paragraph still defines the owed nontextual verification as:

> “a fresh `pdftotext -layout` re-extraction … at Defs 3.15/3.16”

Def. 3.18 remains absent from that promised source-verification action. The omission is repeated in both downstream summaries:

> “ǫ₂ … and Def 3.16 at i = 3 are consumed”

in S7, and:

> “transcription scope of ǫ₂/Def-3.16-at-i=3”

in S9.6.

Thus Def. 3.18 is now nominally gated by PIN-GEN-i, but the pin’s owed discharge recipe and honesty-ledger propagation still cover only Defs. 3.15/3.16. This is an attribution/documentation gap, not an algebraic failure: Def. 3.18’s displayed normalization is used consistently, and its attribution is explicitly open.

### PASS — row O attribution

The operative correction is accurate:

> “row O’s violation branch is UNREACHABLE given E2B’s early-return + list equality”

The script confirms this. Failure of `side == glist` returns from `check_sample` during E2B. Row O is reached only afterward, where both values are computed by the same function and label:

```python
o1 = fp_ord(K2, glist, T3.psi2)
o2 = fp_ord(K2, side, T3.psi2)
```

Consequently its mismatch branch has no independent teeth. Only `ORD_HIST` remains live. E2B carries the stronger side-list equality check; K separately exercises the label tie. The unchanged “matched-label ord transport” labels in the sealed script/output are historical labels, superseded by the explicit REVISION 2 qualification.

## Full chain re-walk

- **Lemma KER:** clean. With \(e=1\), \(0\le s<1\) forces \(s=0\); normalized Bézout forces \((\ell,\ell')=(0,1)\); hence both consumed \(\epsilon\)-characters equal \(1\).

- **Lemma A3:** clean. Depth-3 chain truncation supplies the depth-2 MacLane substate using the same first two reads and keys. It satisfies \(e_0=1\), and the consumed TR3-S1 theorem is total in nonzero \(A\). The forced start is zero, so \(m_0=s_2(A)\), \(j_0=s_2(A)\), and the inner operator is exactly Def. 3.16 at level 2 on that substate.

- **Lemma Z2:** clean. From \(\beta<w_2(A)\), every nonzero \(\Phi_1\)-digit satisfies
  \[
  w_1(a_m)>\beta-m\gamma_2,
  \]
  and every subordinate \(\Phi_0\)-digit lies strictly above its requested level-0 weight. Reduction therefore vanishes, including negative requested weights. The filtration-domain direction is correct.

- **\(t_2\)-absorption:** clean:
  \[
  t_2(j)=\frac{s_2(A_j)-\ell_1u_j}{e_1}=s_2(A_j).
  \]

- **Construction of \(\sigma_2\):** clean. Cor. 5.6(2) is used chain-internally at \(2<r=3\); \((KP_i)\) is reserved for the extended-chain use at \(\Phi_3\). The monic/full-degree lift argument upgrades the associate relation at \(\Phi_2\) to equality.

- **Outer support and assembly:** clean conditional on (H-v3). The equality
  \[
  w_2(A_j)+j\gamma_3=\gamma
  \]
  is simultaneously the FGMN slot condition and GMN on-line condition. A3 and \(t_2\)-absorption give the on-line coefficient equality; Z2 gives all off-line zeros. The degree bound \(\deg R_{\lambda_2}(A)<g_1\) makes evaluation at \(\bar z_2\) nonzero. Hence support equality, \(j_0=s\), and division by \(y^s\) are justified.

- **\(\sigma_2\) through Cor. 5.6(2):** clean at index \(2<3\).

- **(H-v3) conditionality:** correctly present in the theorem hypotheses, S5’s outer-support identification, S6.1, the S6.2 conclusion, and S6.3. No consumer silently upgrades the GMN attribution to unconditional status.

- **Fences:** maintained. No \(e_j\ge2\) case, order \(\ge4\), D-ITER claim, generic induction, or discharge of (H-v3), \((KP_i)\), or [T]-properness is smuggled in.

## Falsifier reconciliation

The run-2 arithmetic is exact:

\[
2241+816+21741+3(1141)+768+816+144+24+816+24=30{,}813.
\]

The RI increase is \(21{,}741-14{,}797=6{,}944\), exactly matching \(30{,}813-23{,}869\). The histogram totals \(744+38+34=816\), matching E2B/O sample coverage. The added RI checks consume no randomness, so the stated run-2 perimeter is structurally credible.

The supplied provenance assigns the proper roles to seals `b4a142b` and `482150b`. I could not independently inspect the Git objects or log files because the workspace command runner failed before execution owing to a missing `bubblewrap`; therefore this is reconciliation of the supplied record, not fresh commit-object authentication.

The finite identity remains mathematically sound under its displayed hypotheses. The sole finding is incomplete propagation of Def. 3.18 through the open attribution pin’s owed verification scope. Acceptance counter remains 0/2.

TR3S3-P4 FINDINGS: 0 critical, 1 gaps  
VERDICT: GAPS-ONLY