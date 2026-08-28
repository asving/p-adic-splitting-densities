# MSF3 verdict — lift tails

**Unit:** MSF3, 2026-08-28.  This verdict amends
`docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md` at the appended
`[MSF3 2026-08-28]` section.  It does not claim the unconditional H.116b4 count.

## Per-item status

| Item | Status | Result | Exact remaining gap |
|---|---|---|---|
| MSF, `j≥3` | **REFUTED-BY** | For one legal `(μ,k)=(2,1)` frame and `r=1`, set `Y=X−ŵπ`.  The raw presentations `(P,Q)=(Y²,Y)` and `(P′,Q′)=(Y²+π²Y+π⁴,Y−π²)` have products differing by `π⁶`, so they form a depth-6 secant.  Yet `V₆(T_x)=span([Y])` and `V₆(D_{x,y})=span([Y],[1])`.  The tangent/mixed exponent lists are `(1,3,∞)` and `(1,3,6)`. | The counterexample target is `Y³`, whose genre has a multiplicity-three child; its cofactor is not root-free for the requested multiplicity-two genre.  The narrowed **MSF-GENRE** statement needed by the schedule remains open.  Required `j=3,4` probes show no legal-cell mismatch. |
| SR | **PARTIAL** | C18 verifies `V_j(T_x)⊆image(ω_j)` independently on all 34,452 members of the eight listed `j=3,4` fibres.  Proposition PAIR-SEP proves SR for the separated target `Y²(Y−π)` for every `n≥5`. | General genre-compatible secant realization is unproved.  Finite equality of the sets is not promoted to a theorem. |
| Grade-shift pairing | **PARTIAL** | GSP-n is stated precisely as a triangular filtration of obstruction directions equipped with digit-shift fibre bijections, including the matched-gate condition.  Iterating the bijections proves `GSP-n ⇒ U(n)`, hence `GSP-5 ⇒ WASH-5`.  PAIR-SEP constructs two spanning digit translations in one genuine genre family. | Construct the triangular pairing for arbitrary frames, base points, live equations, and grades.  In particular, the coefficient-gated cross-level bilinears from grade 5 are not handled generally. |
| WASH-n, `n≥5` | **PARTIAL** | For `F=Y²(Y−π)`, two explicit translations prove `U(n|F)` for every `n≥5` over every DVR.  C19 exhausts this family at `n=5,6` for `q=2,3,5`. | No general WASH-5 or WASH-n theorem; deep MLIFT-1 remains open outside the proved family. |

## The counterexample and its fence

The simultaneous-defeat equations are exact:

    (Y²+π²Y+π⁴)(Y−π²)=Y³−π⁶.

On the restricted source lattice, the tangent generators are
`π³Y, π²Y², πY²`.  The mixed generators are
`π³(Y−π²), π²Y(Y−π²), πY²`; their combinations include
`−π⁴Y` and then `−π⁶`.  This creates the new constant target direction at exactly grade
6 while preserving the secant congruence to that grade.  C17 checks the identity and
the flags at `q=2,3,5`.

The `μ=1` companion fails already at grade 4:
`(Y+π²)(Y−π²)=Y²−π⁴`.  At `q=3`, C16 finds 18 flag mismatches among 27 depth-four
secants.  This regime is illegal under the standing frame condition, but it confirms why
the earlier `q=2` scans were structurally blind and why `μ≥2` delays rather than globally
prevents raw mixed-flag failure.

## Certificate run summary

Script: `verification/openmath/h116b4_msf3_cert.py` (Python 3 + SymPy, exact modular
arithmetic).

* **C16:** mixed flags at `j=3,4` over `q∈{2,3,5}`; seven legal frame shapes plus the
  illegal `q=3,μ=1` collision.  Grade 3: 1,036 secants.  Grade 4: 1,569 secants.  Large
  fibres use 256 evenly spaced partners; smaller fibres are exhaustive.  Legal-cell
  mismatches: 0.  Illegal grade-4 mismatches: 18/27.
* **C17:** two SymPy factor-transfer identities; the `μ=1,j=4` counterexample; and the
  legal-frame raw `μ=2,j=6` counterexample at `q=2,3,5`, including exact product
  differences and independently computed quotient flags.
* **C18:** SR reverse inclusion at `j=3,4`, using every fibre member (3,809 + 30,643 =
  34,452 cases).  All 16 rows pass; equality holds in every legal row.
* **C19:** separated `(μ,k,r)=(2,1,1)` genre family at `n=5,6`, `q=2,3,5`.  Level sizes
  `32/243/3125`, image sizes `4/9/25`, fibre sizes `8/27/125`; both explicit translations
  checked pointwise on every member and their two obstruction shifts have rank two.

Fresh run: exit 0, `==== ALL CHECKS PASSED ====`.  The pre-existing C1–C15 suite is also
rerun in this unit.

**OVERALL: PARTIAL.**  Unrestricted MSF is conclusively false and the SEC route must be
genre-restricted.  SR, general GSP-n, and general WASH-n remain honest opens.
