Quote-and-classify audit:

- CLEAN — Revision 1 fix 1: D0 now explicitly includes condition “(iv) the standing GD23-row/TR-5 projective dictionary and the r = 3 type-hood identifications.” This closes pass-1 gap 1 at the theorem statement.

- CLEAN — Revision 1 fix 2: D3 now derives the second \(r=2\) equality by “applying the all-\(P\) identity at \(P=\phi_2\) with the dictionary \(\phi_2^{GMN}\leftrightarrow\Phi_1\).” That validly gives
  \[
  v_2(\phi_2)=w_1(\Phi_1).
  \]

- CLEAN — Generic extraction: the external arXiv-v2 PDF independently confirms the generic \(H_{r-1}\) intercept map, Definition 2.5, Proposition 2.6, and Proposition 2.7(3)(4), with exactly the formulas quoted in E1–E4. In particular, \(H_{r-1}(S)=u+|\lambda_{r-1}|i\) and \(v_r=e_{r-1}H_{r-1}\) are genuinely generic in \(r\). [GMN arXiv-v2 PDF](https://arxiv.org/pdf/0807.2620)

- GAP — D2 calls the location “§2.3, ‘The p-adic valuation of \(r\)-th order.’” The pinned paper identifies that subsection as §2.2; §2.3 is “Construction of a representative.” The formulas and TeX-line citations remain substantively correct, but the printed subsection citation is wrong.

- CLEAN — Five-step derivation:

  1. E1/E2 define \(v_3\).
  2. Proposition 2.7(3) at \(r=3\), together with \(e_2^{GMN}=e_1^{proj}=1\) and \(|\lambda_2|=h_1\), gives the stated minimum.
  3. TR3-S1 and the dictionary replace \(v_2\) and \(\phi_2\) by \(w_1\) and \(\Phi_1\).
  4. The standing augmentation formula gives the identical minimum defining \(w_2\).
  5. Equality for all nonzero \(P\), multiplicativity, and \(\phi_3\leftrightarrow\Phi_2\) yield the ordinate identity.

- CLEAN — Scope: \(e_0=1\) is used only through TR3-S1; \(e_1=1\) removes \(e_2^{GMN}\) and identifies \(|\lambda_2|=h_1\). Project \(e_2\) is never consumed.

- CLEAN — The \(r=2\) check reproduces both accepted equalities after the newly explicit substitution. No generic-to-evaluated normalization mismatch remains.

- CLEAN — Consequence:
  \[
  u_i=v_3(A_i\phi_3^i)=w_2(A_i)+i\,w_2(\Phi_2)
  \]
  follows for the finite-ordinate/nonzero-coefficient terms, using Proposition 2.6 multiplicativity and step 5. This matches GMN’s order-\(r\) Newton-polygon convention.

- GAP — D7 ends with “that reduction is (HV3-THM)’s clause list (D0 (i)–(iii)).” After Revision 1, the conditionality list is D0 (i)–(iv). This stale cross-reference locally re-omits precisely the dictionary condition added by fix 1. It does not invalidate D0 or the derivation, but the acceptance-summary sentence is inaccurate.

- CLEAN — The note itself claims no bracket edits and confines D7 to a census/future-fold description. Independent working-tree verification was unavailable because the repository shell runner failed before execution (`bubblewrap` missing); no files were modified during this review.

HV3-P2 FINDINGS: 0 critical, 2 gaps  
VERDICT: GAPS-ONLY