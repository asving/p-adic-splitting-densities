# MLF2 verdict — lift-side induction cluster

**Unit:** MLF2 (MATH, certificate-first), 2026-08-27.  This verdict amends
`docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md` at the marked
`[MLF2 2026-08-27]` passages.  No Lean theorem or battery source was changed.

## Per-open disposition

| Open | Verdict | What is now proved | What remains |
|---|---|---|---|
| MLIFT-1, sibling uniformity | **PARTIAL** | The existing proof gives `U(n|F)` for `n≤3` and the affine ranges. | General `n≥4` uniformity of the reduced tower map `ḡ_n` is still open. |
| MLIFT-2, schedule `I_n=#V_n` | **PARTIAL** | New Lemma SCHED-LOW proves the schedule for `n=1,2`; new Lemma SEC gives an exact general secant reduction. | For `n≥3`, mixed-secant flag rigidity (MSF) and secant realization (SR) remain open. |
| MLIFT-3 / GR-11, raw pinned-presentation existence | **PROVED** | New Lemma PKG converts landed `exists_peel_finset` output into an inhabitant of the raw planted-presentation fibre. | Lean packaging is not implemented by this math unit, but there is no remaining mathematical hypothesis. |

The unconditional H.116b4 count is therefore **not proved** by MLF2: it still needs
MLIFT-1, deep MLIFT-2, and the separately-owned MSMITH interface.  MLIFT-3 is no longer an
assembly hypothesis.

## 1. MLIFT-1 — PARTIAL, with stronger target-unconditional evidence

No general proof of the deep sibling-uniformity statement was found.  The exact remaining
statement is still that, for `n≥4`, the tower-reduction map

    ḡ_n : Live_{n-1}(F) -> V / image(L̄)

is uniform on its image.  Nothing in TDC controls this nonlinear pushforward distribution.

Certificate C8 materially strengthens the conjectured quantifier.  It exhausts complete
reachable target spaces rather than selecting one genre target:

* CELL-1 single-child/cofactor tower: `96/96` reachable targets satisfy `U(n|F)` at every
  tested level.
* Mixed two-child tower: `32/32` reachable targets satisfy `U(n|F)` at every tested level.
* C6 retains the earlier non-genre CELL-1 datapoint, where uniformity also holds at every
  level despite a different leaf count.

Thus the evidence supports a target-unconditional MLIFT-1, but finite scans do not prove it.

## 2. MLIFT-2 — PARTIAL; low schedule proved and deep gap isolated

### SCHED-LOW — PROVED

For a nonempty terminal tower and terminal presentation `x`:

* `I_1(F)=#V_1(T_x)=1` follows directly from GRADE.
* At level 2, the obstruction image on the unique child-digit torsor is exactly
  `image(L̄)`.  Independently, the divisibility definition of the saturated image gives
  `V_2(T_x)=image(L̄)`.  Hence `I_2(F)=#V_2(T_x)`.

This is a theorem over the DVR setting of the document, not a certificate inference.

### SEC — PROVED

Ordering the affine product blocks, define the mixed Sylvester secant

    D_{x,y}(delta)
      = sum_beta lambda_beta(delta_beta)
          * product_{gamma<beta} A_gamma(x)
          * product_{gamma>beta} A_gamma(y).

Ordered telescoping gives the exact identity

    Phi(x) - Phi(y) = D_{x,y}(x-y).

Also `D_{x,y} mod π = T̄` and `D_{x,y} ≡ T_x mod π²`.  Therefore every nonlinear
obstruction is exactly a saturated digit of a mixed secant; no Taylor remainder remains.

This shows precisely why TDC does not by itself close MLIFT-2.  Deep schedule equality needs:

1. **MSF:** `V_j(D_{x,y})=V_j(T_x)` for the relevant mixed secants, including equality of
   the quotient flags rather than only Smith exponent multisets.
2. **SR:** actual differences `x-y`, with `y` in the nonlinear truncated fibre, realize
   every direction of `V_n(T_x)`.

SEC plus MSF proves only `image(omega_n) ⊆ V_n(T_x)`; SR is the reverse inclusion.  Current
MSMITH concerns tangent maps at presentations and does not supply either assertion for mixed
secants.

Certificate evidence is uniformly positive:

* C3 checks the schedule on all 14 level rows of CELL-1/2/4.
* C8b checks it on every reachable target in the two complete scans: `96/96` and `32/32`.
  CELL-1 genuinely has two different schedule families, both correct.
* C10 checks SEC exactly on 36 sampled terminal/node pairs.  On all 36, the mixed secant
  also has the terminal tangent's Smith list and the same saturated quotient flag.  This is
  evidence for MSF, not its proof; C10 does not assert SR.

## 3. MLIFT-3 / GR-11 — PROVED

Apply `exists_peel_finset` to the genre class and its canonical lift.  It supplies
`b_p in m`, a monic cofactor `Q` of degree `r`, and the exact factorization.  Modulo `m`,
the target lift becomes `X^m` and every planted child factor becomes `X^{mu_p}`.  Hence

    X^m = X^s * Q_bar.

Cancellation in the residue-field polynomial ring and `m=s+r` give `Q_bar=X^r`; therefore
all low cofactor coefficients lie in `m` and define a cofactor `ClusterState`.  Project each
`b_p` and these cofactor coefficients modulo `m^N`.  Their canonical `classSect` lifts are
congruent to the peel lifts modulo `m^N`; exact affineness of `alphaParent` and product
congruence preserve the target class.  The resulting child/cofactor state tuple inhabits the
raw `Pres(c)` fibre, equivalently `S_N(F_c)`.

The shorter-window `betaChild` equality returned by the peel is not promoted to level `N`
and is not needed.  This is the distinction missed by the old overclaim: the landed theorem
does not already state a raw presentation, but its full lift and exact factorization are
enough to construct one.

C9 checks this conversion mechanism on all 32 genre targets in the complete CELL-1 scan and
C9b checks the established genre target in CELL-1/2/4.  All checks pass.

## 4. Executable verification

Fresh log: `runs/wave-b/out_MLF2_cert.log`.

* `python3 -m py_compile verification/openmath/h116b4_lift_cert.py`: exit 0.
* `python3 verification/openmath/h116b4_lift_cert.py`: exit 0,
  `==== ALL CHECKS PASSED ====`, including new C8/C8b, C9/C9b, and C10/C10b.
* `python3 runs/wave-b/h116b4_battery.py`: exit 0 after `153.4s`,
  `==== ALL CHECKS PASSED ====`.

## Scope verdict

MLF2 closes the mathematical existence/package open MLIFT-3, proves the first two schedule
levels of MLIFT-2, and replaces the vague deep schedule gap by the exact MSF+SR pair through
the proved secant identity.  MLIFT-1 and deep MLIFT-2 remain genuine research opens.

**OVERALL: PARTIAL**
