# CITE REVIEW LIST — Asvin's secondary-check queue (opened 2026-08-24)

Per the 2026-08-24 protocol: literature-cite Lean statements are authored and landed by the
fleet with a faithfulness entry; Asvin reviews SECONDARILY from this list. A row is closed
by his initials + date. His own paper is never citable.

| # | cite | Lean name | where landed | faithfulness entry | status |
|---|---|---|---|---|---|
| 1 | [AGNPRW] Thm 5.6 (OM descent terminates; "Thm 5.2" = arXiv-v1 numbering) | `agnprw_termination : NS7TerminationStatementR` (pre-existing declaration) + NEW binding: I.01 `NS7Termination` body typed to the redraft's definiens, discharged by `ns7Termination_of_cite` | `leanfinal/Uniformity/ChapC/C94.lean` + `ChapI/I01.lean` | C94.lean module docstring (incl. the executed print-read) | OPEN — review the I.01 BINDING (the redraft grammar `DescentStepR` faithfulness was audited at A-C.6; the new surface is the binding only) |
| 2 | FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015): Thm 2.8 (PRINCIPAL-polygon additivity; entire-polygon analogue explicitly false) + Cor 4.12(3) (normalized residual multiplicativity) + Cor 4.9(3) (normalization) + Def 5.4 (one-sidedness) — all four VERBATIM print-read 2026-08-24 against the UPCommons author PDF | `fgmn_dv_exact_mul` (NEW axiom; coexists with C.66, stronger normalization explicit) | `leanfinal/Uniformity/ChapC/C66b.lean` | C66b.lean module docstring (quotes + the corpus↔paper DICTIONARY — the review surface: IsDvPure ↔ Def 5.4 one-sidedness; dvResPoly ↔ R_r up to twist) | OPEN — review the DICTIONARY + spot-check quotes vs the journal text |
