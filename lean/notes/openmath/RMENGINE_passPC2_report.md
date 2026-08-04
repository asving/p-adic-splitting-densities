# RMENGINE pass PC2 report (Codex, round 2) — 2026-08-04

Object: lean/notes/openmath/RMENGINE_2026-08-08.md as repaired at 8835d20.
Charge: /tmp/openmath/RMENGINE_PC2_charge.txt (132,772 chars, frozen-history trim; appendices: the repaired note @8835d20, both round-1 reports, [IL3] S4 engine slice).
Raw stream: /tmp/openmath/rmengine_pc2_out.jsonl. Extracted agent messages verbatim below.

---

I’ll audit the repaired proof as written, treating diagnostics as evidence only. I’ll also inspect the cited revision diff solely to verify the hygiene claim; I won’t execute any verifier or modify files.

=====MSG-BREAK=====

1. **GAP — the repair-record hygiene claim is literally false.** It says:
   > “No PROVED clause was weakened; the only statement changes are the T-scope/T-class STRENGTHENING … and the L-LEX regrade”

   But R3 explicitly changes the former S8 row 11 from “PROVED, generic” to row 11c:
   > “the floor-form pool identification — HEURISTIC”

   This is the correct mathematical repair, and it does not weaken RM-GEN, but it is nevertheless a regrading of a previously PROVED-labeled clause. The repair record should distinguish “no genuinely established theorem clause was weakened” from “no PROVED-labeled clause was regraded.”

2. **GAP — the dependency-claims table remains non-exhaustive under its stated charter.** The table promises enumeration of every “only/never/nothing/…” dependency claim, but omits the new load-bearing S4.2 assertion:
   > “NO leg other than L-MU consumed \(e_i \ge 2\).”

   That census is essential to the scope strengthening and deserves its own claims row. It also omits the repair-record claim:
   > “the only statement changes are …”

   The six-row spot check C15/C17/C18/C19/C20/C22 otherwise found C15 and C17–C20 supported. C22’s “display, not proof steps” wording should be read narrowly as “not used in RM-GEN”; the call-site structure is used to establish the proved COR-A consequence.

3. **CLEAN CHECK — L-NORM and its downstream uses.** Factoring \(\pi^{w_0(b)+w_0(c_d)}\), splitting the primitive parts, and restoring it gives:

   \[
   w_0(L)=w,\qquad w_0(\pi\text{-junk})\ge w+1,\qquad
   w_0(\Phi_0Y\text{-junk})\ge w.
   \]

   Hence L-LINE(ii) has \(\Delta\mathrm{line}=0\); L-LINE(iii) has respectively \(\Delta\mathrm{line}\ge E_m>0\) and \(\Delta\mathrm{line}\ge\Gamma_0>0\). The normalized L-child has residue \(\bar b\bar c_d\ne0\), so it is never lost. This preserves T-tele, DEV-(m), and RM-GEN’s initial-product factorization.

4. **CLEAN CHECK — the R2 extension.** In branch (b), \(d_0=1\) gives \(\rho_0=P_0-1\). Assuming \(w_{i-1}>S_{i-1}\),

   \[
   w_{i-1}P_{i-1}-S_i
   =w_{i-1}-S_{i-1}>0,
   \]

   so a rational \(w_i\in(S_i,w_{i-1}P_{i-1})\) exists and satisfies both \(w_i>S_i\) and \(w_ie_i>S_i\), even when \(e_i=1\). Conversely, a flat \(e_i=1\) forces the same inequality backwards until \(\rho_0<P_0\), equivalently \(d_0=1\). The amended T-scope and the remaining \(d_0\ge2\) fence are coherent throughout the headline, T-TERM, DEV-(m), RM-GEN, COR-A, tables, DAG, and scope box.

5. **CLEAN CHECK — L-GRID and L-VNZ.** At a cell’s own line, the affine recursion gives integral truncation lines and
   \[
   s_l(\lambda_l)\equiv \ell_{l-1}j_{l-1}\gamma_l
   \equiv j_{l-1}\pmod {e_{l-1}},
   \]
   proving on-gridness. L-VNZ then works by induction: a minimum-achieving digit supplies a nonzero coefficient, while the resulting polynomial in \(z_m\) has degree \(<g_{m-1}=\deg\psi_{m-1}\), so it cannot vanish in \(K_m\).

6. **CLEAN CHECK — round-1 proof surface.** Both L-MU branches, strict termination, exact promotion quanta, internal \(\mathfrak z\)-carry cancellation, both telescope families, the single-digit exit argument for (C-W_Q), and all four RM-GEN clauses re-derive correctly. LAW-DCX remains sealed/conjectural where required; the pool identification is now honestly heuristic. COR-A correctly delays ledger application until acceptance and treats \(n=1,2\) separately. No theorem proof consumes W-WIN or residue survival.

7. **NOTE — execution unavailable.** I attempted only a read-only revision inspection, but the local command launcher failed because `bubblewrap` is unavailable. Per the content-only role, I did not attempt an alternative execution route; diagnostics and hashes were treated solely as stated evidence.

RMENGINE-PC2 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY
