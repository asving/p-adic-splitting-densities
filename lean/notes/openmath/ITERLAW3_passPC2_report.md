# ITERLAW3-PC2 — Codex content pass 2 (amended note @f9daca0): NOT-CLEAN, 1C/1G

Both findings NEW and narrow (round-1 remedies E1/E2 explicitly confirmed cured): (g) S4.5 e2=1 display-line algebra slip — 'B2−γ3 < B2−e1γ2+h2 = w2(E1)+0' is false as written (w2(E1)=B2−e1γ2); the true derivation is γ3=e1γ2+h2 ⟹ B2−γ3 = w2(E1)−h2 < w2(E1) — erratum bracket with the corrected line; (c) E3 residual: two 'at n = 3' tokens INSIDE S6.6's recursion dictionary (where n is the rung index by definition) must be struck to n = 2, not glossed as reads. Errata round 2 after PE2 lands; counter 0/2.

## Codex output (verbatim)

I’ll audit the amended file against the cited revisions, then re-derive the load-bearing algebra and check every residual scope/rung reference. I’ll keep execution limitations as notes only and report findings solely as quoted CRITICAL/GAP items.
1. [GAP] S4.5’s \(e_2=1\) above-line calculation contains a false equality:

   > “\(B_2-\gamma_3 < B_2-e_1\gamma_2+h_2 = w_2(E_1)+0\)”

   Since \(w_2(E_1)=B_2-e_1\gamma_2\), the displayed right-hand equality is false. The required conclusion is true because \(\gamma_3=e_1\gamma_2+h_2\), giving \(B_2-\gamma_3=w_2(E_1)-h_2<w_2(E_1)\), but that argument is not what the note states. This leaves the charged \(e_2=1\) read-vanishing step malformed as written.

2. [CRITICAL] E3 does not completely remove the rung mislabel. S6.6 still actively says:

   > “(ITER-LAW-n) at \(n=3\), derived”

   and

   > “the uniform recursion of L3CONVERGENCE S2 Candidate 2 at \(n=3\)”

   The erratum says these occurrences “count READS,” but `(ITER-LAW-n)` and Candidate 2 use \(n\) as the rung index. Under the declared convention, this formula is the \(n=2\) specialization. Unlike E1/E2, these claims are not declared struck; redefining their \(n\) locally as “number of reads” leaves a residual false source attribution, especially in the recursion dictionary itself.

E1 otherwise cures the COR-3/DCX overreach: S0.1, S0.4, S6.3, and S9 consistently restrict the \(e_2=1\) and \(e_1=1\) field-level claims to off DCX, while retaining unconditional integer reductions and the full \(e_0=1\) degeneration. E2 correctly restricts DEV-1 and gives a valid unreached argument for every downstream call.

NOTE: bubblewrap was unavailable, so I could not independently execute the git-chain, byte-stability, or sealed-artifact checks; this is not counted as a finding.

ITERLAW3-PC2 FINDINGS: 1 critical, 1 gaps
VERDICT: NOT-CLEAN
