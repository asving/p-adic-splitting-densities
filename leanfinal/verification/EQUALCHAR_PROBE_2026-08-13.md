# Equal-characteristic density probe — 2026-08-13

**Status: empirical cross-check only. Not a proof. No Lean file was touched.**

## The question

The capstone Prop quantifies over *every* complete DVR with finite residue field —
that includes the equal-characteristic ones `F_q[[t]]`, not just `Z_p` and its finite
extensions. `genuine_density_check.py` had only ever exercised `O = Z_p`. Asvin's
question: at `n = 2`, do the `F_q[[t]]` splitting-type counts match the *same*
rational functions of `q` (the W-11 closed forms) that the `Z_p` counts follow at
`q = p`, or does equal characteristic diverge — and if so, where first?

W-11's closed forms (`lean/notes/openmath/W11_PROOF_2026-08-08.md`), stated purely as
functions of `q`:

```
undecided count at level N   = q^N
ram-decided count            = (q^(2N) - q^(2N-2K)) / (q+1),   K = floor(N/2)
split-decided = inert-decided = (q^(2N) - q^N - ram) / 2
limit densities: split = inert = q/(2(q+1)),  ram = 1/(q+1)
```

## Method

`equalchar_probe.py` mirrors `genuine_density_check.py`'s structure exactly: monic
quadratics `x^2+bx+c` with `b,c` ranging over `q^N` residue classes mod `t^N`; a class
is level-N *decided-σ* iff every refinement to precision `M=N+K` (all `q^{2K}`
extensions of both `b` and `c`) is classified `σ`. Only the atomic classifier changes:

- **q odd (q=3 here):** char `F_q` is odd, so the ordinary discriminant test survives
  unchanged (`d = b²-4c`, now a *t*-adic polynomial valuation instead of a *p*-adic
  integer valuation; ramified iff `v(d)` odd; split/inert by whether the unit's
  leading coefficient is a QR in `F_q`). This is a verbatim transport of the
  `genuine_density_check.classify` "p odd" branch — low risk, and it *is* the standard
  fact that quadratic extensions of a local field with odd residue characteristic are
  classified by residue-field data alone, independent of the field's own
  characteristic.
- **q=2:** char `F_q`=2 makes `4=0`, so the discriminant test is vacuous (`d=b²`
  always) — this is exactly the case the prompt flagged as unsafe to naively
  odd-characteristic-test. The correct invariant is Artin–Schreier, not Kummer.
  `classify_char2` decides via Hensel (separable residue ⇒ decide immediately from
  `b(0),c(0)`) plus, when `b≡0 mod t`, a recentre-and-Newton-polygon recursion tracking
  `β=v(b)` against `γ=v(recentred c)`: `γ` odd and `2β>γ` ⇒ ramified, `2β<γ` ⇒ split;
  `γ=2δ` even and `β<δ` ⇒ split, `β=δ` ⇒ inert (forced: `F_2` has one nonzero element,
  so the rescaled residue is *always* `y²+y+1`), `β>δ` ⇒ rescale and recurse one
  `t`-digit deeper. Verified by hand against `x²+x` (split), `x²+x+1` (inert), `x²+t`
  (Eisenstein ⇒ ram), `x²+tx+t²` (`=t²(y²+y+1)` under `x=ty` ⇒ inert), `x²+t²x+t`
  (Eisenstein ⇒ ram) — all five are asserted as a self-check at import time.

`classify_char2` is **sound but only partially complete**: it can exhaust the working
precision with both `β` and `γ` still unresolved, in which case it honestly returns
`None` rather than guessing (the task's explicit "certificate-limited" allowance).

**A real gap the probe caught, then fixed.** The first full run showed q=2, N=3
diverging from `Z_p`: split short by exactly 4 (16 vs 20), with those 4 classes
carrying type-set `{split, None}` — never a *second* decided type. That signature means
"my classifier can't finish," not "the math disagrees": the class `b≡t (mod t^3)`,
`c≡0 (mod t^3)` has `β=v(b)=1` pinned *regardless* of any extension digits, so `2β=2`
is already less than the guaranteed lower bound on `γ` (≥3 from the residue alone) —
split is forced without ever needing to resolve `γ` exactly, including the boundary
lift `c=0` exactly (`f=x(x+t)`, still two distinct roots, still split). The original
code only checked this style of lower-bound shortcut when `β` was the *unresolved* one;
the symmetric case (`γ` unresolved, `β` known and small) was missing. Added it
(`classify_char2`, the `if beta_known and 2*beta < Lc2: return "split"` branch); after
the fix, `ambiguous == undecided` at every tested cell for both `q` (no residual
certificate-limited cells within the tested precision), and every count below matches
`Z_p` exactly. This is worth flagging because it means the match reported below is not
a coincidence of a weak certificate — a real incompleteness was caught and closed
before trusting the comparison.

## Results (exact enumeration, no sampling; K=6 for q=2, K=3 for q=3, same K used for the Z_p side)

```
====================================================================================================
EQUAL-CHARACTERISTIC DENSITY PROBE  —  n = 2, O = F_q[[t]]  vs  O = Z_p  vs  W-11
(empirical cross-check; NOT a proof; no Lean touched)
====================================================================================================

--- q = 2   certificate: Artin-Schreier/Newton-polygon (classify_char2) ---
    W-11 limits: split = inert = 1/3, ram = 1/3
 N    box | EQchar split EQchar inert EQchar ram  EQ undec  EQ amb |  Zp split  Zp inert  Zp ram  Zp undec | W11 split  W11 ram  W11 und | cell-match
 1      4 |            1            1          0         2       2 |         1         1       0         2 |         1        0        2 |        YES   (0.0s)
 2     16 |            4            4          4         4       4 |         4         4       4         4 |         4        4        4 |        YES   (0.1s)
 3     64 |           20           20         16         8       8 |        20        20      16         8 |        20       16        8 |        YES   (0.3s)
 4    256 |           80           80         80        16      16 |        80        80      80        16 |        80       80       16 |        YES   (1.3s)
    EQchar decidedSeq(split) at N=4: 5/16 = 0.312500  vs W-11 limit 1/3 = 0.333333  (trend-consistent at this small N)
    VERDICT: q=2: cell-for-cell MATCH with Z_p and W-11 at every tested N.

--- q = 3   certificate: discriminant+QR (classify_odd, verbatim Z_p analogue) ---
    W-11 limits: split = inert = 3/8, ram = 1/4
 N    box | EQchar split EQchar inert EQchar ram  EQ undec  EQ amb |  Zp split  Zp inert  Zp ram  Zp undec | W11 split  W11 ram  W11 und | cell-match
 1      9 |            3            3          0         3       3 |         3         3       0         3 |         3        0        3 |        YES   (0.0s)
 2     81 |           27           27         18         9       9 |        27        27      18         9 |        27       18        9 |        YES   (0.3s)
 3    729 |          270          270        162        27      27 |       270       270     162        27 |       270      162       27 |        YES   (3.3s)
 4   6561 |         2430         2430       1620        81      81 |      2430      2430    1620        81 |      2430     1620       81 |        YES   (34.0s)
    EQchar decidedSeq(split) at N=4: 10/27 = 0.370370  vs W-11 limit 3/8 = 0.375000  (trend-consistent at this small N)
    VERDICT: q=3: cell-for-cell MATCH with Z_p and W-11 at every tested N.

====================================================================================================
SUMMARY VERDICTS
  q=2: cell-for-cell MATCH with Z_p and W-11 at every tested N.
  q=3: cell-for-cell MATCH with Z_p and W-11 at every tested N.
====================================================================================================
```

## Verdicts

- **q=2:** the equal-characteristic (`F_2[[t]]`) and mixed-characteristic (`Z_2`)
  decided-count trajectories agree **cell-for-cell** — not just in the N→∞ trend — at
  every tested level N=1..4, and both match the W-11 closed forms exactly (`split =
  inert = q^{2N}·(…)`, `ram`, `undecided = q^N`, all as printed above). This is despite
  the two settings using genuinely different arithmetic invariants (Artin–Schreier for
  `F_2[[t]]` vs. the mod-8 Kummer test for `Z_2`) to reach the same numbers — the
  agreement is not definitional.
- **q=3:** same conclusion, cell-for-cell match at N=1..4, and here the two settings
  use the *same* invariant (discriminant + Legendre symbol) transported verbatim from
  `p`-adic to `t`-adic valuation, so the match is closer to expected (odd residue
  characteristic is classically residue-field-only), but it is still confirmed exactly
  rather than assumed.
- No divergence was found at any tested `(q,N,σ)` cell after the completeness fix
  described above. The uniformity claim — that the *same* rational functions `R_σ(q)`
  govern both the mixed- and equal-characteristic families at `n=2` — is empirically
  supported at every level checked (N up to 4, q ∈ {2,3}), with q=2 (residue
  characteristic 2, the structurally delicate case in both settings) the more
  informative test since its two certificates are genuinely different constructions.

## Honesty notes

- This is a finite check (N ≤ 4, q ∈ {2,3}) of a claim about all N and all prime
  powers `q`; it is evidence, not a proof, and says nothing about `n>2` or about
  non-prime `q` (this probe never needed `F_q` for `q` a proper prime power, since 2
  and 3 are both prime — the `q=2` Artin–Schreier recursion's "sqrt in `F_q` is the
  identity" shortcut is specific to `q=2` and would need genuine Frobenius-inverse
  machinery for `q=4,8,…`).
- `classify_char2`'s completeness gap (found and fixed, see above) is disclosed rather
  than silently patched over; at the tested precision (K=6 for q=2) no
  certificate-limited cells remain (`ambiguous == undecided` exactly, matching the
  Z_p script's own soundness diagnostic), but a deeper N could in principle re-expose
  the same style of gap if the fix's lower-bound shortcut still isn't fully complete —
  it was validated empirically (exact match to Z_p) at N≤4, not proved complete in
  general.
- All counts above are exact enumerations (no sampling), reusing
  `genuine_density_check.decided_counts` and `.w11_prediction` by read-only import for
  the `Z_p`/W-11 columns — that file was not modified.
