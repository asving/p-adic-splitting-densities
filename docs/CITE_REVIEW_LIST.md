# CITE REVIEW LIST — Asvin's secondary-check queue (opened 2026-08-24)

Per the 2026-08-24 protocol: literature-cite Lean statements are authored and landed by the
fleet with a faithfulness entry; Asvin reviews SECONDARILY from this list. A row is closed
by his initials + date. His own paper is never citable.

| # | cite | Lean name | where landed | faithfulness entry | status |
|---|---|---|---|---|---|
| 1 | [AGNPRW] Thm 5.6 (OM descent terminates; "Thm 5.2" = arXiv-v1 numbering) | `agnprw_termination : NS7TerminationStatementR` (pre-existing declaration) + NEW binding: I.01 `NS7Termination` body typed to the redraft's definiens, discharged by `ns7Termination_of_cite` | `leanfinal/Uniformity/ChapC/C94.lean` + `ChapI/I01.lean` | C94.lean module docstring (incl. the executed print-read) | OPEN — review the I.01 BINDING (the redraft grammar `DescentStepR` faithfulness was audited at A-C.6; the new surface is the binding only) |
| 2 | FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015): Thm 2.8 (PRINCIPAL-polygon additivity; entire-polygon analogue explicitly false) + Cor 4.12(3) (normalized residual multiplicativity) + Cor 4.9(3) (normalization) + Def 5.4 (one-sidedness) — all four VERBATIM print-read 2026-08-24 against the UPCommons author PDF | `fgmn_dv_exact_mul` (NEW axiom; coexists with C.66, stronger normalization explicit) | `leanfinal/Uniformity/ChapC/C66b.lean` | C66b.lean module docstring (quotes + the corpus↔paper DICTIONARY — the review surface: IsDvPure ↔ Def 5.4 one-sidedness; dvResPoly ↔ R_r up to twist) | OPEN — review the DICTIONARY + spot-check quotes vs the journal text |

## Row (2026-08-25): the Cor 4.12(2) grade-anchoring print-read (U14 / A-C.13)
Secondary-review request: `docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` reads
published FGMN Cor 4.12(2) as carrying the `β ∈ Γ_{r−1}` restriction ESSENTIALLY (the
proof's "because s_r(β) = 0"), correcting U9's earlier removal of the `PrevGrade` premise
(A-C.13 enacted: the premise restored to the class `Rgr_mul` + the source-law
`graded_mul`; the S2 twist law `R_{β+β′}(gh) = X^{(β%2)(β′%2)}R_β(g)R_{β′}(h)` is recorded
as the repo's own arbitrary-grade GENERALIZATION, machine-checked, not attributed to the
paper). Spot-check the two quoted clauses (Def 3.13's line parameterization; the
Cor 4.12(2) proof line) against the journal text.
