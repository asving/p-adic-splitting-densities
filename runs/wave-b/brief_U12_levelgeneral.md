# Unit U12 — DESIGN: the level-general carrier (C.90 / OPEN-LEVEL-GENERAL / FGMN Cor 6.3)

You are a design unit (high reasoning) in the p-adic-splitting-densities campaign.
Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project:
leanfinal/ (mathlib v4.31.0, built; `lake env lean <file>` from leanfinal/; NEVER bare
`lake build`).

## Context
U7's audit (docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md §5) ruled that published
FGMN Corollary 6.3 (Q10) and Theorem 6.2 (Q9) "must not be faked as fields": they need
every truncated MacLane valuation, intermediate keys, polygons N_i, root values, ℓ_i, and
per-level residual fields — carriers the corpus lacks. U9 (FGMN_ADJUDICATION §9) decided
Q7: C.90 needs the FULL Cor 6.3 package (not just the residual-power fragment) and stays
OPEN-LEVEL-GENERAL. Meanwhile the chain-realization carrier has since LANDED (the CC wave,
2026-08-24): ChainRealization (C130fg.lean), KeyChain/LaurentNormalizer/NodePointSource
(C130k/C130ln/C130st/C130pt), TerminalReceiver (C130tr), stage carriers at every live
level. Much of what U7 said was missing may now EXIST. Your job: design the level-general
carrier ON TOP of the landed CC layer, in U11's style.

## Read (in order)
1. docs/PROJECT_STATE.md.
2. docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md (the landed carrier's design) +
   the landed files (C130k/fg/st/pt/tr/ln .lean in leanfinal/Uniformity/ChapC/ — what per-level
   data they ALREADY carry).
3. docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md §5 (the must-not-fake table) +
   FGMN_ADJUDICATION §9 (Q7's decided cost).
4. The FGMN paper (docs/references/FGMN_residual_ideals_2015_authorpdf.pdf): published
   Thm 6.2 + Cor 6.3 — print-read the exact statements.
5. C.90's signed statement + consumers: `rg -n "C.90" leanspec/Leanspec/ChapC.lean
   blueprint/CHAP-C_tower_grammar.md` (the C.90(b) "booked field" story) and the GENTOW5
   chain consumers (`rg -n "gentow5" leanspec/Leanspec/ChapC.lean`).

## Deliverable
docs/in-progress/LEVEL_GENERAL_DESIGN_2026-08-24.md: (1) the gap analysis — which Cor 6.3
ingredients the landed CC layer already carries vs genuinely missing; (2) the decided
carrier signatures (Lean, elaboration-checked in leanfinal/scratch/U12_check.lean — no
sorry, no axiom); (3) the honest per-field classification (source obligation w/ named
clause vs repo dictionary — no consumer conclusions); (4) how C.90 discharges from it +
what the GENTOW5 consumers actually need; (5) a 30–60-min node plan. If the honest verdict
is that Cor 6.3's full package needs objects (e.g. algebraic closure of the completion,
root valuations) that would import heavy new mathlib machinery, SAY SO with the exact cost
and propose the minimal faithful fragment that serves the actual consumers.

## Rules
- Do NOT edit leanspec/, leanfinal/Uniformity/, or blueprint files. Only the two
  deliverables. Do NOT git commit.
- Quote FGMN verbatim (published loci) for every load-bearing reading.
