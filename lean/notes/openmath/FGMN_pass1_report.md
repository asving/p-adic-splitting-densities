The FGMN scale diagnosis is correct, but the numerical record overstates what its harness establishes. I find no critical mathematical defect, but four verification gaps prevent a clean pass.

Quote-and-classify:

1. **CONFIRMED — parent-scale diagnosis and double scaling.**

   The print explicitly defines `N_i := N_{μ_{i−1},φ_i}`, constructs `Q_s` using `μ_{i−1}(a_sφ_i^s)`, and equation (13)/Corollary 4.4(2) tests `μ_{i−1}(a_{s_j}) = α_j`. [FGMN arXiv v3 PDF](https://arxiv.org/pdf/1305.0775v3)

   Multiplication by `e(μ_i)=e_i e(μ_{i−1})` gives
   \[
   e_i\,wPrev(B_j)+j\,h=gam.
   \]
   At a graded read-pair stage with `w=e_i·wPrev`, the compiled clause becomes
   \[
   e_i(e_i\,wPrev(B_j))+j\,h,
   \]
   so the claimed extra factor of `e_i` is real.

2. **GAP — R2 contains an actual false-negative branch.**

   The script claims to test both recorded-`gam` failure and “any-gam solvability,” but uses:

   ```python
   if len(oldvals) <= 1 and (not oldvals or oldvals == {gam}):
       viol(...)
   ```

   If `oldvals` is a singleton different from recorded `gam`, an alternative single `gam'` exists, yet the test reports no violation. The correct roster may happen to have at least two supported slots everywhere, but neither R1 nor the report records/asserts that fact. Thus “compiled 0/336” as an **any-gam** discriminator is not established by this script.

   Row A itself is genuinely discriminating: corrected values are `{6}`, compiled values are `{6,12}`.

3. **GAP — “336/336 SAT” overstates R1.**

   `check_corrected` checks the lower bound, support/equality correspondence, nonzero stride slots, and a window-length/order consistency condition. It does not instantiate all of `SideReads`; notably, its comment labeled “(iii)” does not test the note’s actual clause-(iii) assertion `σ.R f` exact at the graded stage. Nor does it directly test the complete digit identity.

   Therefore this is a 336-site **scale-sensitive window/support check**, not 336 full corrected-bundle satisfiability proofs. The note partially acknowledges the owed Lean construction, but its repeated “336/336 SAT” wording remains too strong.

4. **GAP — R4 is not as independent as claimed.**

   The note says the from-print implementation shares “only ring primitives” with the certified stack. In fact it consumes certified `Tower` state and methods including `T.w1`, `T.res_digit`, `T.K1`, `T.z1`, keys, and chain parameters. Comparing its result with `T.R2s` is still a useful differential falsifier, but it is not an independently derived operator in the advertised sense.

5. **CONFIRMED — Row-A arithmetic and record.**

   Since
   \[
   f_A=(X+2)^2+24,
   \]
   the parent weights at slots `0,2` are `3,0`. With `(e,h)=(2,3)`, corrected values are `6,6`; with `w=2wPrev`, compiled values are `12,6`. The reported tuple
   `(2,3,6,0,2,(1,1),1,1)` is consistent with the displayed computation and output.

6. **CONFIRMED — PIN-GEN-i source leg.**

   Def. 3.15 prints
   \[
   \epsilon_i(\alpha)=z_i^{\ell'_i s(\alpha)-\ell_i u(\alpha)},
   \]
   not the swapped-prime reading. The PDF also gives the claimed generic ranges: Def. 3.15 for `0 ≤ i < r`, Def. 3.16 for `0 ≤ i ≤ r`, and Def. 3.18 for `1 ≤ i ≤ r`. [FGMN arXiv v3 PDF](https://arxiv.org/pdf/1305.0775v3)

7. **CONFIRMED — D0 and blast-radius wording.**

   The note does not resurrect D0; equation (14) gives the normalized pure-key residual `R_i(φ_i^s)=1`. It does not claim existing JuncForge refutations are mathematically false: it consistently describes them as true records of the old clause. It also does not promise consumer recompilation success—gate reruns and a consumer census are explicitly deferred. DITER’s cocycle and sanity gates remain stated obligations, not claimed discharges.

8. **GAP — local artifact verification could not be completed.**

   The managed local runner failed before every filesystem or script command because its sandbox helper could not find `bubblewrap`. Consequently I could not independently confirm the two local SHA-256 pins, inspect the actual JuncForge theorem types/consumer census, compare the JSON, or rerun the 1,093 checks. The arithmetic count reconciles as `28 + 336×3 + 1 + 56 = 1,093`, but that is reconciliation of the supplied record, not a fresh execution.

FGMN-P1 FINDINGS: 0 critical, 4 gaps
VERDICT: GAPS-ONLY