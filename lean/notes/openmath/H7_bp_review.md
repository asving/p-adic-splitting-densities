# H7_bp_review — Codex adversarial review of HDISCHARGE_H7.md (draft 1)

Date: 2026-08-05 (session clock 2026-08-01). Model: Codex (fresh context, repo-blind,
charge + full blueprint + carrier/citation context pasted). Verdict: **REVISE**
(15 criticals + 2 justification gaps). Disposition: every finding folded at blueprint
rev 2 — table in HDISCHARGE_H7.md §7. Prompt: /tmp/openmath/H7_bp_prompt.txt (527 lines).

---

1. **CRITICAL ERROR — the frame convention redefines the engine read instead of proving OL-3.**

> “branch-j continuation reads are the OM data of dec(x) computed in the SITE'S REALIZED KEY CHAIN … factor-side reads of f_j use the SAME chain.”

M07 OL-3 requires comparison after a cell-constant frame change with a fixed recentering/lift convention. Declaring both sides to use the same chain suppresses precisely that open comparison. Section 1.3 later admits that recentering absorption is unproved. Thus the target statement already assumes away part of K-LOC.

2. **CRITICAL ERROR — the off-roster factor \(f_0\) is inserted without the adapted-coordinate data required by O-10.**

> “ρ(c) := Σ_{0 ≤ i < j ≤ m} v_p(Res(f_i, f_j)) — f₀ INCLUDED in the pair sum”

> “the off-roster factor rides as the (m+1)-st no-prescription factor (O-10 Theorem 2's `Set.univ` option)”

> “the product (with the f₀ slot)”

O-10 applies to a product of explicitly pinned factor cells. Choosing `Set.univ` only removes an event restriction; it does not provide a factor cell, pinning depth, or extraction coordinate for \(f_0\). IT-1 defines only \(C_j\) for roster branches. Consequently the proposed \(m+1\)-factor use of \(\rho\), K-COUNT, and Theorem 2 lacks an \(f_0\) coordinate and is not justified by the cited sources.

3. **CRITICAL ERROR — K-LOC(iii) is not a consequence of (i)–(ii), and its use is circular with I-τ.**

> “(iii) consequently every prescribed-finite-subtree continuation event … is the pullback, under the O-10 Corollary-1 factor extraction ε, of an event E_j”

> “Clause (iii) is exactly the event-translation clause of the O-10 §4.3 (I-τ) display”

Corollary 1’s extraction map is available only after an adapted product presentation has been supplied. IT-1/IT-2 use K-LOC(iii) to construct that presentation. Thus K-LOC invokes an extraction map whose applicability depends on I-τ, while I-τ is then derived using K-LOC. Pointwise polygon and residual-polynomial identities also do not themselves prove finite-depth keying or factor-extraction well-definedness.

4. **CRITICAL ERROR — Lemma 2.17(3) is applied to the wrong polygon side.**

> “if at distinct polygon sides, the side of branch j's slope in N(f_i) has length 0 — Lemma 2.17(3) + Thm 1.15.”

The supplied pin for Lemma 2.17(3) concerns only the side of slope \(-\infty\), whose length is \(\operatorname{ord}_{\phi_r}(f)\). It does not state that an arbitrary finite branch slope has length zero. This breaks the advertised order-\(\le 1\) proof of KL-1 in the polygon-side divergence case.

5. **JUSTIFICATION GAP — the zero-\(\omega\) to constant-residual step needs more than the quoted statement.**

> “a cofactor with ω_{t_j,r}(f_i) = 0 has one-point principal polygon at level r … and its residual factor is the nonzero CONSTANT R_{λ_r}(f_i)”

Lemma 2.17(2) gives zero length for \(N_r^-\). Turning this into a one-point polygon at the required abscissa and a nonzero constant \(R_{\lambda_r}\) also depends on the exact principal-polygon and residual-operator definitions, including treatment of the \(-\infty\) side. Those definition-level implications are asserted rather than demonstrated.

6. **CRITICAL ERROR — the KL-2 target exceeds what Theorem 2.26 states.**

> “N_r^{t_j}(dec(x)) = N_r^{t_j}(f_j(x)) translated by δ_{j,r}(c)”

The cited theorem gives additivity of \(N_r^-\), not an unqualified/full \(N_r\). It also gives multiplication of residual polynomials for a fixed negative slope and normalization. The blueprint’s target ranges over general “per-level polygon translations” and engine reads. Section 1.3 acknowledges normalization and \(\ell\)-shift issues, so the literature citation does not establish the displayed target as written.

7. **JUSTIFICATION GAP — KL-3’s order-\(\le 1\) “PROVABLE NOW” grade has no supplied theorem behind its depth bound.**

> “both determined by f_i's data at depths ≤ (separation depth) + ρ_{ij}(c) (the resultant interaction bound)”

> “pinned mod p^{τ(c)} … hence pinned EXACTLY”

No cited result supplies the claimed separation-depth-plus-resultant bound. The congruence trick can stabilize valuations and suitable initial residues below the modulus, but “pinned exactly” for all normalization scalars and translations requires a separate precision analysis. The PROVABLE-NOW assignment is therefore under-supported.

8. **CRITICAL ERROR — the proposed proof of IT-2’s reverse inclusion applies K-LOC outside its domain.**

> “for (g_j) ∈ ∏C_j, the product … runs the SAME site history with datum c — K-LOC applied at the product”

K-LOC §1.1 is stated for \(x\in\Sigma_c\). In the reverse inclusion, membership of the arbitrary product in \(\Sigma_c\) is exactly what must be proved. Applying K-LOC to that product assumes the desired membership. Calling the remaining issue `RunRealizerExists` does not remove this circular step.

9. **CRITICAL ERROR — IT-3’s claimed upper bound is false under the stated hypotheses.**

> “τ(c) := max(ρ(c) + 1, the site's branch-pin depth); upper bound τ(c) ≤ thr(c) + ρ(c)”

This requires at least \(1\le\mathrm{thr}(c)\), which is absent from the target and from `SiteDatum`. For \(\rho=0\) and \(\mathrm{thr}=0\), the definition gives \(\tau\ge1\) while the claimed ceiling is \(0\). The same missing condition affects route B’s \(\tau'=\rho+1\) pricing.

10. **CRITICAL ERROR — Theorem 2 and Corollary 1 do not yield exact uniformity of continuation-read words.**

> “O-10 Theorem 2 gives the product law per sub-cell; per-factor keyed classes have EQUAL counts … so on each sub-cell the joint continuation-read word is EXACTLY UNIFORM”

Theorem 2 supplies a product count identity for keyed component events. Corollary 1 supplies a constant-fiber extraction to products of coefficient-depth classes. A continuation-read word can merge several coefficient classes, and the numbers of classes merged by different read words need not agree. Therefore exact uniformity of the continuation-word map does not follow from either result.

11. **CRITICAL ERROR — the common-alphabet assertion needed for aggregation is unsupported and generally sensitive to the sub-cell.**

> “with the SAME alphabet across sub-cells of one site”

The normalization data \(\delta_{j,r}(c)\) and \(u_{j,r}(c)\), available factor classes, and realized continuation prefixes may vary with the refined cell. Nothing cited identifies the attainable read-word sets across different sub-cells. Without a common word map and alphabet, H7-C1a cannot be applied to the intended partition.

12. **CRITICAL ERROR — `sib_of_uniform_words` is false as stated.**

> “theorem sib_of_uniform_words … {m : ℕ} …”

No assumption \(1\le m\) is present. For \(m=0\), the dependent-product alphabet is a singleton and exact uniformity merely says \(U=\#X\). The conclusion reduces to \(\#X=1\), which is false for, say, a two-element \(X\). The statement was only probe-typed using `sorry`, so it cannot land with the advertised proof. For the intended H7 case \(m\ge2\), exact joint uniformity would imply the componentwise SIB identity; the defect is in the Lean theorem’s unrestricted statement.

13. **CRITICAL ERROR — `ITauPresents` is a numerical shell, not an adapted engine-stratum presentation.**

> “the site stratum presents as an O-10 adapted cell”

> `∃ A : AdaptedCell p n N, ... A.cellCount = s.stratumCount ∧ Nat.card A.Factor = ∏ j, s.branchCount j`

Nothing connects `A.toMulFiberData` to `A.Factor`, the engine stratum, its multiplication map, its branch factors, or `branchCount`. All relevant carrier fields can be populated synthetically, while the displayed equalities merely assume the desired cardinal arithmetic. Consequently this proposition does not encode I-τ’s product presentation or conformance content.

14. **CRITICAL ERROR — `KLocCounts` is vacuous or freely engineerable.**

> “the K-LOC row, COUNT face”

> `∀ E : Events, joint E * s.stratumCount ^ (s.m - 1) = ∏ j, single E j`

`Events` and both count functions are arbitrary and have no connection to sets, cardinalities, continuation reads, factors, or the site. Taking `Events` empty proves the proposition vacuously; suitably chosen functions can also make it true by construction. It is not a semantic or even a nonvacuous integer shadow of OL-3.

15. **CRITICAL ERROR — H7-B1 is not a substantive conformance theorem.**

> “THE CONFORMANCE THEOREM — the H7 rows instantiate K11's `EngineSIBRow` opaque parameters with no re-key”

The theorem accepts an arbitrary proposition `KLoc` together with a proof of it, then copies `hK` and `hI` into fields of `EngineSIBRow`. Since `EngineSIBRow` itself treats K-LOC and I-τ as opaque Props, this proves only constructor compatibility. It does not establish either hypothesis or connect the chosen propositions to engine data. Calling this the receipt consumed by Step 18 smuggles the open semantic work behind trivially fillable parameters.

16. **CRITICAL ERROR — the order-0 gate demonstrates junk inhabitance, not non-vacuity of I-τ.**

> “THE GATE — `ITauPresents f1Datum` is inhabited: a compiled non-vacuous adapted-cell presentation”

> “take `Factor := Fin 2 → Fin 625` … `domainCount_eq` via a designated-element `factorCount`”

The proposed construction deliberately uses a synthetic domain, unit-sized fiber/chart data, and contrived `factorCount` values. Because those objects are unrelated to the actual \(5^8\)-element stratum or its two factor coordinates, inhabiting the proposition confirms the carrier loophole identified in Findings 13–15. It cannot serve as a non-vacuity gate for the intended mathematics.

17. **CRITICAL ERROR — the PROVABLE-NOW grading overstates what H7-C2 establishes.**

> “STATUS: order ≤ 1 PROVABLE NOW”

> “H7-C2 … branch-j residual reads cannot see a separated cofactor.”

H7-C2 proves only preservation of powers of one irreducible polynomial under multiplication by a coprime cofactor. It does not prove polygon-side separation, polygon translation, residual unit-scalar transport, cell constancy, event pullback, or the frame convention. Together with the incorrect Lemma 2.17(3) use, it cannot support the stated order-\(\le1\) K-LOC grade.

The reported H7-F1 index conflation is correct: `factorCount` is indexed by `Factor`, while the intended counts are roster-indexed. The blueprint also correctly observes that contrived values can inhabit the carrier despite this semantic mismatch.

The order-0 integers themselves are consistent with the intended two-factor shape:
\[
5^8\cdot 5^0=5^4\cdot5^4,
\]
and \(\rho=0\) is compatible with \(s(M)=0\). H7-C1a is also a valid abstract aggregation principle, assuming its stated common alphabet and genuine partition hypotheses. Those correct pieces do not repair the broken route from O-10/GMN to the engine interface.

REVISE
