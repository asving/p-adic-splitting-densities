# Unit U14 (codex HIGH) — print-read adjudication: Cor 4.12(2)'s grade anchoring vs the parity twist

You are a print-read adjudication unit in the p-adic-splitting-densities campaign. Repo
root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(`lake env lean <file>` from leanfinal/; NEVER bare `lake build`).

## The question (machine-checked finding, unit RP23, 2026-08-25)
The landed S2 graded residual (C130rp1.lean's `s2GradedRes`, grade-anchored per FGMN Def
3.12's line parameterization) satisfies R₁₀(Φ′²) = X but R₅(Φ′)² = 1 — so the abstract
`graded_mul` field in C130fg.lean (CC-13's `FGMNSourceLaws`, mirroring published Cor
4.12(2) as "R_{β+β′}(gh) = R_β(g)·R_{β′}(h)") is UNINHABITABLE at this operator
(`tooth_graded_mul_plain_shape_refuted` in C130rp2.lean). The corrected law that IS true
at S2 carries a parity twist: R_{β+β′}(g·h) = X^{(β%2)(β′%2)}·R_β(g)·R_{β′}(h)
(endpoint teeth verified: mixed no-carry 1 = 1·1; odd×odd carry 1 = coefficient at y¹).

DECIDE by print-reading the FGMN paper (docs/references/FGMN_residual_ideals_2015_authorpdf.pdf,
§§3–4 — Def 3.12/3.13, Prop 3.x on the graded pieces, Cor 4.12 and its proof; also the
arXiv copy docs/references/fgmn_residual_ideals_1305.0775v3.pdf for numbering drift, map
in docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md §2):

1. In the SOURCE, is R_{r,α} anchored per-polynomial (each g read on ITS OWN line through
   its own minimal point — in which case the product law has no twist because the lines
   compose differently than the repo's fixed-grade lines) or grade-anchored (the repo's
   reading)? Quote the defining text verbatim.
2. Under the source's actual convention, is the repo's corrected twist law the faithful
   transcription of Cor 4.12(2), or should the OPERATOR (RP-1's s2GradedRes) be re-anchored
   so the plain law holds? Which choice serves the consumers (CC-13's laws feed A-C.11's
   class whose `Rgr_mul` is the SCALAR projection — check what the twist does at coeff 0:
   does the scalar law survive either way)?
3. Deliver: the decided convention + the exact corrected field signature(s) for
   C130fg.lean's `graded_mul` (and `normalized_mul` if affected — the normalized operator
   R_r strips y-powers, which may absorb the twist entirely: check Cor 4.12(3)'s proof),
   as a diff proposal (do NOT apply; the orchestrator enacts), with the faithfulness
   argument quoting the source.

## Deliverables
docs/in-progress/COR412_ADJUDICATION_2026-08-25.md (the print-read + decision + diff);
runs/wave-b/verdict_U14.md (summary). Do NOT edit leanfinal/Uniformity/, leanspec/, or
roll-ups; do NOT git commit.
