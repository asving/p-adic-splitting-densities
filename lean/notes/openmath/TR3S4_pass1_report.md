The coefficient theorem survives hostile checking, but S6.2 contains a key-class orientation error and S8.3 omits the second seal hash. Neither flaw breaks the main TR3-S4 chain; both are GAPs. Clean-pass counter remains 0/2.

## Findings

1. **GAP — S6.2 conflates the two opposite key-normalization orientations.**

   Quote:

   > “\(R_{\lambda_3}(\Phi_3)=\bar z_2^{-\theta_2g_2}\cdot\text{(monicized twisted class)}\)”

   Step 0 defines the monicized twisted class as
   \[
   \bar z_2^{\theta_2g_2}T_{c^{-1}}\psi_2.
   \]
   Substitution makes the quoted right side \(T_{c^{-1}}\psi_2\), which generally is not associated to \(\psi_2\), contradicting the stated GMN lawfulness of \(\Phi_3\).

   The correct GMN-lawful calculation from the verified scalar pin
   \[
   t_2(g_2)=-\theta_2g_2
   \]
   is
   \[
   R_{\lambda_3}(\Phi_3)=\bar z_2^{-\theta_2g_2}\psi_2,
   \qquad
   \sigma_2(\psi_3^F)
      =\bar z_2^{-\theta_2g_2}T_c\psi_2.
   \]
   Fortunately, the subsequent ORD-INV-LIFT chain uses this latter, correct \(T_c\psi_2\) label, so the order conclusion remains valid after assuming the intended identity.

   Related wording is also reversed:

   > “the GMN-lawful level-3 key class is the \(\theta_2\)-TWISTED \(\psi_2\) class.”

   Step 0 actually describes the GMN residual class of an **FGMN-normalized** lift. Conversely, script row O uses
   \[
   k_G=\bar z_2^{\theta_2g_2}T_{c^{-1}}\psi_2,
   \]
   which is correct for matching an FGMN-side literal \(\psi_2\) label, but it is not the GMN-lawful-key orientation used in step 1. The class/literal divergence criteria themselves are correct.

2. **GAP — the first-run seal hash is absent from S8.3.**

   Quote:

   > “the first-run record = the commit of even date carrying this block + the outputs.”

   The preceding text promises that both commits are “cited … below,” but only `7fa8825` appears. The supplied second hash `79eaee6` is not displayed in the note. Assuming `79eaee6` is the intended record commit, the downstream reconciliation is unaffected.

## Attack-point audit

- **A, HV3-E2: clean.** At \(r=3\), GMN \(e_2=e_1\), \(|\lambda_2|=h_1/e_1\), so Proposition 2.7(3) gives
  \[
  v_3(P)
   =e_1\min_i\left(v_2(a_i)+i\left(v_2(\phi_2)+\frac{h_1}{e_1}\right)\right).
  \]
  Substituting \(v_2=w_1\) and distributing the positive \(e_1\) yields exactly
  \[
  \min_i\{e_1w_1(a_i)+i\gamma_2\}=w_2(P).
  \]
  The \(E_2=e_1\) dilation is used at precisely that last comparison. Definition 2.5’s erroneous-looking integral codomain for the intercept is not consumed: only \(e_1H_2\), equivalently Proposition 2.7(3), is used. The printed valuation and minimum formulas are confirmed in the primary GMN paper, [Definition 2.5 and Proposition 2.7](https://arxiv.org/pdf/0807.2620).

- **B, A-GEN-3: clean conditional on accepted TR3-S1.** Its substate has exactly \(e_0=1\), while \(e_1\) remains free. The application is total in nonzero \(A\), not degree-restricted. The congruence
  \[
  s_2(A)=s(\beta)+m_0e_1
  \]
  gives \(j_0=\lfloor s_2(A)/e_1\rfloor=m_0\). The Def-3.16-at-\(i=3\) inner operator is exactly Def 3.16 at \(i=2\) on the same \(\Phi_1\)-development and weight.

- **C, S6.2: one GAP**, as detailed above. The scalar pin, class-versus-literal criteria, and both matched-label transports are algebraically correct when their orientations are kept distinct.

## Remaining chain

- \(\sigma_2\) construction and monicity upgrade: clean.
- KER-13 and live \(\epsilon_2\): clean.
- Z2-e2, including negative weights and zero digits: clean.
- EXP-3: both sides reduce exactly to \((s_2-\ell_1\beta)/e_1\); clean.
- Per-slot \(t_2\)-absorption, support equality, evaluation nonvanishing, normalization by \(y^s\), and the two-form: clean.
- WIT-3 degree and weight bounds: clean.
- Fences \(e_0\ge2\), \(e_2\ge2\), orders \(\ge4\), and D-ITER: honored.
- Conditionality: (H-\(\ell\)) and PIN-GEN-i are displayed globally; \((KP_i)+[T]\) enter only S6.2; consumer conditionality is preserved.
- Numeric reconciliation: row totals sum to \(13{,}679\); all quoted meters match the supplied output. These are only falsifier results.
- F2c remains unsatisfied: the supplied harness explicitly disclaims model diversity and no verifier-owned implementation accompanies this pass.
- I could not independently execute Git or the harness because the workspace command sandbox failed to launch without `bwrap`; this does not alter the two textual/algebraic findings above.

TR3S4-P1 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY