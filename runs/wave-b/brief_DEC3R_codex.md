# Unit DEC3R (codex HIGH) — the μ₃ / Route-B campaign blueprint

You are a design unit in the p-adic-splitting-densities campaign. A Fable predecessor
(DEC3) died in an API storm with NO artifact — you own this from scratch. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(Lean 4.31.0 + mathlib, pre-built; verify with `lake env lean <file>` FROM leanfinal/;
NEVER bare `lake build`).

## The charge (PROJECT_STATE §4 item 2)

Blueprint the μ₃ campaign: the corrected-parameter depth-2 instance
`FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21` — the (2,1,21)
operators ONE level up from the landed depth-1 (2,1,5) instance — so the GENTOW consumer
CONCLUSIONS fire at S2 depth 2. U15 adjudicated this as ~20–30 nodes; its discharge plugs
into PK-3's landed `fgmnCalculusOf`/`fgmn_model_calculus_nonempty` (C130pk.lean) with
ZERO new packaging (PACKAGING_ROUTE §5 "Route B follow-on").

## Read (all, in this order)

1. docs/PROJECT_STATE.md (whole; short).
2. docs/in-progress/PACKAGING_ROUTE_2026-08-25.md — §2 (the (2,1,21) machine-pinning:
   the witness's own `u 3 = 21` rfl; the consumers' floor 20 < u' REJECTS 5), §3 (the
   node sizing), §5 (Route B), §6 rows 1–2 (the parameter amendment + the hprev/hcop
   tension — BOTH are YOUR inputs).
3. docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md §8 — OPEN-DICT-1..4. **The
   binding constraint: OPEN-DICT-2 (which clearing the μ₃ operators use — the
   PRECEDING-group clearing `β̂ = e(μ₂)β` vs evenness) must be DECIDED, with machine or
   print-read evidence, BEFORE your blueprint fixes its `nextValue`.**
4. docs/in-progress/COR412_ADJUDICATION_2026-08-25.md — A-C.13's restored `PrevGrade`
   field and why (`I.PrevGrade u'` is unsatisfiable at ANY evenness-realized instance
   passing `hcop`: `¬S2PrevGrade 5 ∧ ¬S2PrevGrade 21`, machine-pinned). Your blueprint
   must dispose hprev/hcop satisfiability at μ₃ — either the preceding-group clearing
   makes it satisfiable (show the arithmetic) or propose the `2 ≤ f'` fence re-sign
   (A-C.15-style) with its consumer audit.
5. runs/wave-b/verdict_NP0.md — the parameter-free-engine discovery (most depth-1 NV/RP/KP
   nodes are parameter-generic; your node table should mark each μ₃ node REUSE-WITH-
   NUMERALS vs GENUINELY-NEW accordingly).
6. runs/wave-b/verdict_U15.md + leanfinal/scratch/U15_check.lean — the depth-2 parameter
   adjudication record. NOTE: U15_check.lean no longer elaborates against the enacted
   corpus (consumed authority) — read it, don't run it.
7. The landed depth-1 instance: leanfinal/Uniformity/ChapC/C130sg.lean (the star
   `s2_calculus_discharge`), C130pk.lean (`fgmnCalculusOf`), C130fg.lean
   (FGMNSourceData/Laws), and the NV/RP/KP chain files they import (follow imports).
8. The FGMN paper §§2–4: docs/references/FGMN_residual_ideals_2015_authorpdf.pdf
   (inductive valuations, residual operators, the grade/clearing laws — Cor 4.12).

## Deliverables (write INCREMENTALLY, section by section to disk)

1. docs/in-progress/MU3_CAMPAIGN_2026-08-26.md — the blueprint: (a) the OPEN-DICT-2
   clearing DECISION with evidence; (b) the hprev/hcop disposition; (c) the per-node
   table (U11 §10 style: node id, statement sketch, named landed inputs, REUSE vs NEW,
   est. 30–60 min sizing); (d) the wiring row showing the final discharge plugging into
   `fgmn_model_calculus_nonempty`; (e) an honest OPEN list for anything undecidable
   without new print-reads (name the FGMN passage needed).
2. leanfinal/scratch/DEC3_probe.lean — elaboration/computation probes backing every
   load-bearing claim (the (2,1,21) numerals, the clearing arithmetic, any claimed
   reuse-signature match). Zero sorry, zero axiom, `lake env lean` exit 0.
3. runs/wave-b/verdict_DEC3R.md — LANDED/SUPPLY/BLOCKED verdict, ≤2 pages.

## Rules

Do NOT edit leanspec/, leanfinal/Uniformity/, roll-ups, or any file other than your three
deliverables. Do NOT git add/commit. If a needed fact is missing, record it as a named
OPEN row — never assume. Cite file:line for every claim about the landed corpus.
