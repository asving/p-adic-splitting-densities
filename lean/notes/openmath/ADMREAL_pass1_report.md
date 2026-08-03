The proof chain is not clean. The decisive failure is the unstated optimal-type restriction in W-LAD. Ordinary GMN types can contain stationary levels \(e_i f_i=1\); “type in GMN’s sense” does not imply a strictly increasing degree tower. Consequently, the submitted proof does not establish W-LAD under its stated quantifiers, and every downstream unconditional theorem depending on W-LAD is unproved.

## Defects

1. **CRITICAL ERROR** — false scope assertion in W-LAD.

   > “the tower of a GMN type is strict … with \(e_jf_j\ge 2\) at every stage”

   This is false for a general GMN type. Strictness characterizes an *optimal* type; stationary levels with \(e_j=f_j=1\) are permitted. The note’s fixed notation and NON-END theorem say “ANY type,” not “optimal type.” Its own falsifier grid also includes \((e,f)=(1,1)\).

   At such a stationary level, \(\deg\phi_i<m_j\) is unavailable, so the submitted one-term-development proof of \(\omega_j(\phi_i)=0\) does not apply. The scope note does not repair this: it merely declares degenerate stages outside scope without showing that O-9 or the theorem’s quantifiers exclude them.

   This breaks W-LAD as proved here. Per the requested dependency rule, W-CAP, the imported top-weight form used by CLASS-LAT, NON-END, LOC, and the unconditional ADM-REAL′ conclusion cannot be certified from this chain. The underlying W-LAD identity may be provable by other GMN results, but that proof is not supplied and must not be silently substituted. The GMN literature expressly distinguishes “type” from “optimal type”; see the primary [GMN paper](https://arxiv.org/abs/0807.2620).

2. **JUSTIFICATION GAP** — inaccurate/unchecked GMN attribution.

   > “**(P1)** [GMN Prop 2.7(1)]: \(w(P)\ge e_rv_r(P)\), equality iff \(\omega_r(P)=0\)”

   In the primary paper, uses of the valuation/\(\omega\) equality criterion are attributed to Proposition 2.8, while Proposition 2.7 contains the valuation formulas for distinguished \(\phi_i\)’s. The note needs an exact convention-and-index match; it currently quotes neither the proposition nor its hypotheses faithfully enough to pin the iteration.

3. **JUSTIFICATION GAP** — §5b proves variance of the displayed formulas, but not the entire consumer attribution.

   > “Every carrier-derived \(r\ge2\) conclusion keyed to `wt` … inherits it.”

   From the supplied formulas, direct `CensusData.wt` values cannot simultaneously equal the top-normalized O-9 values when some \(E_i>1\). The example \(\{0,1,5,6\}\) versus \(\{0,2,5,7\}\) confirms that distinction.

   But the stronger “every carrier-derived conclusion” and “no reading” attribution requires a call-path audit showing that no consumer rescales or interprets the stored birth weights before using them. No such audit is displayed. Thus F-ADM-3 is established at the field-definition level, not for every named downstream design.

4. **JUSTIFICATION GAP** — the asserted equivalence inside B-PIN is unproved.

   > “Equivalently: no consumption site fires the free-box CEN-W \((\varepsilon=1)\) on a realized cell.”

   Excluding free-box CEN-W is equivalent to “every charged right end is pinned/monic” only after proving that the listed CEN-J and monic-top routes exhaust all Step-14 consumption sites. The note identifies precisely that fan-out audit as open. It therefore cannot assert the equivalence before that audit.

5. **JUSTIFICATION GAP** — the consumption corollary claims an extra conjunct not supplied by ADM-REAL′.

   > “\((ADM′):=\) FULL at the \(L′\)-slots + value-attainment at vertices … is DISCHARGED”

   NON-END proves FULL at non-right-end on-line slots. B-PIN removes the right-end digit charge. Neither result in this note proves the separately stated “value-attainment at vertices” conjunct, nor is an imported theorem cited that makes it automatic. Hence the claimed ADM′ discharge exceeds the displayed proof.

6. **JUSTIFICATION GAP** — R2(a) does not check every advertised face step.

   > “within each face, consecutive on-line slots drop by EXACTLY … Prediction: 0 failures.”

   Shared vertices are deduplicated while retaining the preceding face label. The first step after every shared vertex therefore has different stored face labels and is skipped by:

   ```python
   if S1 == S2:
   ```

   R2(b) checks only strict decrease there, not the exact step formula. The advertised R2(a) coverage is incomplete.

7. **JUSTIFICATION GAP** — R2(d)/(e) tests the wrong failure predicate.

   > “every clearance failure …”

   Clearance is \(\beta>\mathrm{classmax}\), so failure is \(\beta\le\mathrm{classmax}\). The script counts only:

   ```python
   if cm is not None and b < cm:
   ```

   Equality failures are omitted. Thus the reported negative-pool count and sealed bound do not cover every clearance failure described in the header and note.

8. **JUSTIFICATION GAP** — R3′ does not seal the claimed exact count.

   > “88 failing \(r=2\) types”

   `run_R3prime()` accepts any positive count:

   ```python
   return dict(ok=(coded_fail > 0 and coded_ok and top_ok))
   ```

   A drift from 88 to 1, or 89, would still pass. The exact “88” claim may happen numerically, but it is not protected by the displayed addendum contract.

9. **JUSTIFICATION GAP** — the retired R3(b) diagnosis is no longer enforced.

   > “R3(b) … SEALED-PREDICTION-REFUTED”

   The final exit contract omits the condition `r2_fail == 0`. If a later change made top-normalized \(r=2\) failures appear, the script would print R3(b) as `PASS`, yet could still return exit 0. Thus “ALL LIVE PREDICTIONS PASS” does not preserve the claimed refutation state.

10. **JUSTIFICATION GAP** — chronology of the seals is asserted, not evidenced.

   > “predictions sealed before their first run”

   The combined file contains the original prediction, diagnosis, and post-run addendum, but no immutable pre-run artifact, commit identifier, timestamped output, or retained run-1 log. The prose documents that R3(b) failed rather than silently changing its text, which is good recordkeeping, but the supplied artifact alone cannot verify that R3′ and R3″ were genuinely sealed before execution.

## Conditional checks that are otherwise sound

- TRI’s single-monomial specialization does force `wt(j) = w(B_j)` if TRI is imported exactly as displayed. Hence the O-9 ledger convention is top-normalized.
- CLASS-LAT’s modular division is correct: multiplication by \(e_r\) identifies \(\mathbb Z/e'\mathbb Z\) with \(e_r\mathbb Z/e\mathbb Z\), and \(E_i=e_rE'_i\) for \(i<r\).
- Hand check for \(r=3\), \(e_1,e_2,e_3=(2,3,5)\), all \(h_i=f_i=1\): \(V_1=0,V_2=2,V_3=21\), and the top weights are \(15,35,106\) modulo \(30\). Reducing first modulo \(5\), then dividing by \(5\), leaves truncated weights \(3,7\) modulo \(6\), which enumerate all six classes once. This confirms the induction mechanism but is not proof.
- STEP’s merged-list argument is sound: adjacent faces with distinct slopes cannot share a non-vertex point; their abscissa intervals overlap only at the common vertex.
- W-CAP’s telescoping algebra and the NON-END inequalities are correct conditional on W-LAD and the stated imports.
- R4 is only a re-adjudication of stored `n_att`, not an independent recomputation. Section 7 admits this, so it is not falsely presented there as proof.
- The note correctly labels B-PIN, FRESH, and the consumption audit as open, and correctly treats numerical runs as falsifiers rather than proofs.

ADMREAL-P1 FINDINGS: 1 critical, 9 gaps
VERDICT: CRITICAL