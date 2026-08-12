## 1. Preregistered prediction / teeth block

Expected sealed verdict: `PASS`.

The runner registers exactly **213 rows**:

| Group | Rows |
|---|---:|
| two-commit seal | 5 |
| C1 letter recursion | 24 |
| C2 wrap/cocycle/telescope/carry | 48 |
| C3 corrected key and three reads | 24 |
| C4 attained-origin bridge | 18 |
| C5 normalized coefficient reads | 12 |
| C6 live lifts, boundary refusals, clearance | 35 |
| historical-coverage regressions | 23 |
| revised-note scope lint | 12 |
| mutation-tooth firing assertions | 12 |
| **Total** | **213** |

The historical regression rows cover X, FR-G, F4-JOINT’s quadratic and full \(\mu=3\) legs, and LP/LD. They are freshly recomputed; the 2026-08-10 verdict is not imported.

Every mutation must produce exactly the following failure set:

| Tooth | Mutation | Rows that must break |
|---|---|---|
| `gauge_naive` | Use \(\Gamma_t=c_t\), omitting \(\vartheta_s\) | `C3.F4Q.coherent_vector` |
| `wrong_sign` | Replace \(\eta^{\lfloor si(u)/e_1\rfloor}\) by its inverse | `C3.P5.coherent_vector` |
| `misindexed_telescope` | Use \(\lfloor (s+1)i(u)/e_1\rfloor\) | `C3.F4MU3.theta_vector` |
| `inverse_orientation` | Use \(\Theta=\vartheta\) instead of \(\vartheta^{-1}\) | `regression.F4MU3.canonical.t1`, `regression.F4MU3.canonical.t0` |
| `origin_drop_nu` | Identify the raw factor with \(\varepsilon\), dropping \(z^\nu\) | `C4.nu2_nonroot.raw_bridge` |
| `origin_iff_nu0` | Replace \(z^\nu=1\) by \(\nu=0\) as the equality criterion | `C4.nu2_root.equality_criterion` |
| `he6_bare_residue` | Replace normalized coefficient residues by bare residues | `C5.A.gamma_exact` |
| `he6_q_sign` | Replace \(\eta^{-q(k)}\) by \(\eta^{q(k)}\) | `C5.A.varpi_read` |
| `lift_boundary_accept` | Admit \(M=D'h\) by changing `>` to `>=` | `C6.boundary_eq.refused` |
| `eta_implies_xfree` | Infer \(x\)-freeness from \(\eta=1\) alone | `C6.eta1.xfree` |
| `weld_single_map` | Insert the affirmative claim “T1 proves one transport map” | `lint.no_single_transport_map` |
| `weld_drop_fences` | Remove the M3 scored-stratum and M4 accepted-W2-C3 fences | `lint.M3_scored_stratum`, `lint.M4_W2C3_fence` |

For `inverse_orientation`, all three canonical slots are evaluated. The `t2` control survives because \(\vartheta_1=1\); the `t1` and `t0` entries must fail.

## 2. Complete runner
