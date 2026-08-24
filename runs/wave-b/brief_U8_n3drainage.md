# UNIT U8 — the cubic drainage block: HYP.04–HYP.09 (PROVING NEW MATH; HIGH reasoning)

You are a research mathematician. This is the ONE genuinely open mathematics block in the
project (ledger class "MATH — stated but not derived / remains unproved"). Deliver a
DOCUMENT (docs/in-progress/N3_DRAINAGE_PROOF_<date>.md) with COMPLETE proofs or honest
partials with exact named gaps. Full rigor: every step justified; a pattern verified on
small cases is a conjecture, not a proof.

READ FIRST: (1) spec/HYPOTHESIS_LEDGER.md rows HYP.04 through HYP.10 (the statements and
where they are consumed); (2) leancheck/notes/N3_CHECK_2026-08-13.md in FULL, especially
§§8–12 (the cubic classification, the triple-root recursion, the tail recurrence
u(N) ≤ q^(−N/2) + q^(−5)·u(N−3), and the STATUS block); (3) any landed Lean these touch:
grep leanfinal/ for `drainage_three`, `UndecidedVanishes`, `drainage_one`, `drainage_two`
and read the landed n=1,2 proofs as the pattern (probably Uniformity/Density/ files).

THE MATHEMATICAL TASK: over ℤ_p (any p, uniformly — mind wild p = 2, 3 for cubics!), the
monic cubic classification's undecided stratum after N OM-steps is the triple-root-like
recursion; prove (a) the tail recurrence bounding the undecided measure u(N), with the
EXACT constants derived, not asserted (HYP.08); (b) the null-complement/drainage statement
(HYP.09): the undecided mass → 0; (c) whatever of HYP.04–07 those depend on (read their
rows; prove or reduce each). State everything measure-theoretically over the coefficient
Haar measure on the monic-cubic box, matching the corpus's counting-density normalization
(Coeff boxes, residueCard q — see leanfinal/Uniformity/Density/LocalData.lean).

Every claim: PROVED (complete argument) / OPEN (exact statement of what's missing). No
"routine". If the recurrence constants come out DIFFERENT from the ledger's display, say so
loudly — a corrected true statement beats a transcribed false one.
