# Verdict MSM2 — unequal-slope restricted Smith cluster

Unit: MSM2 (MATH, certificate-first), 2026-08-27.

## Outcome by charged open

| open | verdict | result |
|---|---|---|
| GR-7b-0 | **BLOCKED AS STATED / REFUTED** | Clause `v(S[i,c]) ≥ V[i,c]` is false.  Exact B5 data give Schur valuations `8<9` at `(0,1)` and `4<5` at `(2,1)`.  The proved replacement U2R is `S_(p,j)=π F_p rem(E_(p,j)Q,P_p)`; corrected remainder-envelope/normal-form lemma GR-7b-0R remains OPEN. |
| GR-7b-I | **PROVED for r=0; PARTIAL overall** | For `r=0`, write the descending child-slope multiset as `w_0≥...≥w_(s-1)`.  Every entry in row `i` is at least `a_i=1+Σ_(h≥i)w_h`; deadline Hall matchings attain every suffix partial sum, and `{a_i}` is C2.  The cofactor case GR-7b-I+ remains OPEN. |
| GR-7b-II | **PROVED for r=0; PARTIAL overall** | U3 normalization plus the strict deadline inequality below a column's slope block makes every cheapest-suffix witness minor block upper triangular with unit diagonal after row-grade extraction.  The cofactor case GR-7b-II+ remains OPEN because the former V-inheritance route is invalid. |
| GR-4a | **PROVED** | Equal-slope scaling extracts `π^(k μν)`; distinct residual centres make the normalized resultant a unit. |
| GR-4b | **PROVED** | At the smaller slope, the normalized reductions are `(Y-z)^μ` and `Y^ν`; `z≠0` makes them coprime, giving valuation `μν min(k,l)`. |
| GR-4c | **PROVED** | Frame scaling extracts `π^(μ β_k)` and root-freeness makes `Res(P̃,Q̃)` a unit. |
| GR-5 | **PROVED** | Induction factors the n-factor map through the `(n-1)`-factor map and the binary Sylvester map for `(G,f_n)`; determinant multiplicativity and resultant multiplicativity give the pairwise product up to sign. |

## Consequences

- The unequal-slope restricted Smith theorem is paper-PROVED for every cofactor-free cell (`r=0`).
- The top determinant slot U4 is paper-PROVED for every `r`.
- The full multi-slope, cofactor-inclusive theorem remains PARTIAL: its intermediate determinantal ideals require GR-7b-0R, GR-7b-I+, and GR-7b-II+ or a replacement argument.
- The equal-slope Theorem E remains paper-PROVED.  MSM2 also repaired its false summand-wise divisibility sentence using the correct total-coefficient case split.
- U2 now proves exactly `r` exponent-1 factors: initial child columns and every Schur correction lie in `π²`, so the residual Schur block has no additional exponent 1.
- None of these paper proofs is claimed to be landed Lean.

## Certificate

`verification/openmath/h116b4_smith_cert.py` retains all prior Blocks A/B and adds Block C:

- exact row bounds, Hall witnesses, and DP assignment optima on three named `r=0` examples;
- the same proof schema on 73 bounded abstract slope configurations;
- the pinned exact B5 counterexample to old GR-7b-0;
- planted pair and planted/cofactor resultant checks;
- four exact multi-Sylvester determinant/product checks.

Fresh output: `runs/wave-b/out_MSM2_cert.log`.  Exit status is 0 with all checks passing.  The finite checks support the proof calculations and counterexample at their stated scopes; they do not replace the universal paper proofs.
