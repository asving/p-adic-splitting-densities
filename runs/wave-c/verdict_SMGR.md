# Verdict SMGR — Smith cofactor tails

[SMGR 2026-08-28]

| item | status | result / exact remaining gap |
|---|---|---|
| GR-7b-0R | **PROVED** | The genre envelope `V^rem` is defined by min-plus convolution followed by the literal top-down monic-division recurrence.  The ultrametric inequality proves it bounds every coefficient of `pi F_p rem(E_(p,j)Q,P_p)`.  At each own-slope frame, multiplication by the root-free residual cofactor is an automorphism of `kappa[Z]/(Z^mu)`; CRT across the slope block gives the exact C2-window residue span and an integral block normal form.  Integral block changes retain the minimum envelope of their input block.  The formula gives B5 values `8` and `4` at the two positions where raw `V` incorrectly gave `9` and `5`. |
| GR-7b-I+ | **PARTIAL** | The initial range `gamma_t(V)=t` for `t<=r` is proved.  **OPEN SMGR-I-COMB** is the exact gap: prove the nested raw-envelope assignment formula `gamma_(r+h)(V)=r+` the `h` smallest child-C2 grades.  A general min-plus Schur complement is insufficient because several residual edges may reuse one eliminated pivot; direct tropical division by `Phi` also loses the exact `F_p` factor retained by U2R. |
| GR-7b-II+ | **PARTIAL** | The 0R normal form gives determinantal-ideal upper-bound witnesses for `t<=r` and `r<t<=r+s_min`, where `s_min` is the smallest-slope block size; I+ would make these exact at the original orders.  The earlier U4 handles `t=m`, and Theorem E covers every order in the one-slope case.  **OPEN SMGR-RSE** is the exact multi-block gap: prove that every normalized C2 suffix is integral after extracting its row grades and reduces to a block-upper-triangular matrix with identity diagonal blocks.  This is a remainder-envelope cross-block inequality, not the refuted raw-V inheritance claim. |

## Certificate run

Command: `python3 runs/wave-b/h116b4_battery.py --smgr`

Fresh run: exit 0, `ALL CHECKS PASSED` (2.8s).

- Exact remainder bases: 100 total, using five structured planted lift tuples and four seeded admissible cofactors in each of five cells: CELL-1 `(q,N,L,r)=(2,5,[(2,1,1)],1)`, B4 `(2,6,[(2,1,1)],2)`, B5 `(2,10,[(2,1,1),(2,2,1)],1)`, B7 `(2,6,[(3,1,1)],1)`, and B11 `(3,11,[(2,1,1),(2,1,2),(2,2,1)],1)`.  B4 contributes two genres, so this is six cell-genre occurrences.  Working precision is `(s_mu+r)(N+1)`.
- Every exact base checks the `V^rem` coefficient bound, full rank of every own-slope C2 residue window, every suffix-minor valuation, and the exact Schur Smith list.  The B5 drops are separately pinned.
- Abstract combinatorics: 1,736 configurations.  Child types are one to three elements with repetition from `{(2,1),(2,2),(2,3),(3,1),(3,2)}`, child degree at most 7; `r in {1,2,3}`, total degree at most 8; every cofactor valuation vector in `{1,2,3,4}^r`, with monic top valuation zero.  Exact DP finds raw-`V`/C2 and `V^rem`/child-C2 partial sums equal in all 1,736 cases.

The computations certify only these finite instances.  They do not prove OPEN SMGR-I-COMB or OPEN SMGR-RSE.  No result is claimed landed in Lean, and no git commit was made.
