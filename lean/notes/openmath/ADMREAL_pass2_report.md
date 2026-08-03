Full hostile pass completed. The mathematical chain survives; I found two documentation/audit gaps, no critical defect.

1. **GAP — prospective inheritance is stated too broadly.**

   > “The inheritance is PROSPECTIVE: it binds every r ≥ 2 instantiation of the r-generic decls…”

   This conflicts with the note’s earlier, correct qualification: the conventions diverge only where some relevant \(E_i=e_{i+1}\cdots e_r>1\). There are nondegenerate \(r\ge2\) types with all later \(e_j=1\), for which the stored birth weights already equal the top-normalized weights. The six-file classification and “zero rescale sites” conclusion are otherwise sound; the defect is the universal scope of “every \(r\ge2\) instantiation.”

2. **GAP — the claimed two-commit seal does not identify the second commit.**

   > “commit e05e660 — and the verdict lands in the separate follow-up commit: the commit pair is the immutable seal.”

   Only the preregistration hash is supplied. The verdict commit is unnamed, and the log is referenced only by the wildcard `verification/logs/admreal_rev1_*.log`. Thus the alleged pair cannot be reconstructed unambiguously from the note itself. This does not affect the mathematics or the reported R6 result, but it leaves the chronology seal incompletely auditable.

Everything else checked clean:

- GMN Lemma 2.14 really is stated under the section-wide fixed-type scope, with no optimality or strict-growth condition, and proves \(\omega_j(\phi_i)=0\) via the \(-\infty\)-side argument and Lemma 2.2. [Primary-source PDF, pp. 16–24](https://arxiv.org/pdf/0807.2620v2).
- Proposition 2.15(1), after replacing paper-\(r\) by note-\(r+1\), agrees term-for-term with the REC unroll:
  \[
  E_i(e_iV_i+h_i)=
  \sum_{j=1}^i(e_{j+1}\cdots e_r)
  (e_jf_j\cdots e_{i-1}f_{i-1})h_j.
  \]
- Stationary stages are admitted by the printed type definition and do not disturb W-LAD, W-CAP, or CLASS-LAT.
- CLASS-LAT’s \(j_r=a+e_rb\) split, division by \(e_r\), and truncated-weight identity \(w_i=e_rw_i'\) are valid.
- STEP’s merged-list argument is sound: adjacent face intervals overlap only at their common vertex, so each consecutive pair belongs to one face.
- NON-END, the \(r=0\) branch, realized \(\beta_{k_s}\ge0\), LOC, and the assembled theorem follow.
- B-PIN remains explicitly open; the \(\varepsilon=1\) equivalence is not smuggled in.
- The consumption corollary claims only FULL at the \(L'\)-slots; vertex value-attainment remains open.
- R2’s repaired equality predicate and coverage accounting, R3′’s exact 88 contract, R3(b)-STATE, and R6’s 43,536-versus-0 premise control are internally consistent. They remain falsifiers, not proofs.
- R4’s residual dependence on harness-produced `n_att` is disclosed honestly.

ADMREAL-P2 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY