# Unit U9 — adjudicate the FGMNCalculus design questions; deliver the A-C.11 diff

You are a mathematics adjudication unit (high reasoning) in the p-adic-splitting-densities
campaign. Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`.

## Context

Unit U7 audited the `FGMNCalculus` field list against the FGMN paper and delivered
`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md`. Its §4.3 assembled class
signature is type-checked; its §4.2 records citation/scope corrections to the seven
provisional law fields; its §9 lists eight open design questions. The orchestrator has
adopted U7's verdicts: `fgmn_calculus_exists` stays UNDECLARED (the class is a hypothesis
carrier, discharged only later via a future `FGMNChainRealization`), and — decision on
U7 §9 Q8 — the law fields LIVE IN THE CLASS for now (consumers C.99–C.106 need them to
fire; the trust story is unchanged because the class is a hypothesis, not an axiom).

Your job: settle U7's remaining §9 questions Q1–Q7 so the corrected class can be enacted
as recorded amendment **A-C.11**, and deliver the exact diff.

## Read (in this order)

1. `docs/PROJECT_STATE.md` (short).
2. `docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md` — whole document.
3. The FGMN paper: `docs/references/FGMN_residual_ideals_2015_authorpdf.pdf` (published
   numbering; U7 §2 has the arXiv-v3 ↔ published map). Read the actual clauses — do not
   trust U7's paraphrases where a question turns on the source's exact convention.
4. The consumer proofs that will use the laws:
   `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` (the [Q1]–[Q10] loci) and the
   sixteen consumer signatures in `leanspec/Leanspec/ChapC.lean` (provisional class at
   ~lines 1321–1375; `rg FGMNCalculus leanspec/`).

## Deliverables (one document: `docs/in-progress/FGMN_ADJUDICATION_2026-08-24.md`)

For each of U7 §9 Q1–Q7, a DECIDED answer with the deciding evidence quoted from the
source or the consumer proofs. The criterion is end-to-end-proof: pick the convention
under which (a) the C.99–C.106 proofs go through as written in the GENTOW2 proof doc,
and (b) a future `FGMNChainRealization` can actually be constructed from a MacLane
chain. Do not leave any of Q1–Q7 "for the owner" — the standing protocol (2026-08-24)
makes these the fleet's decisions; if a question is genuinely undecidable from the
evidence, say exactly what experiment or lemma would decide it and pick a provisional
answer with a named revisit trigger.

Specifically:
- **Q1 (index convention)** is load-bearing: fix whether the class describes depth `r`
  or the next augmentation `(e',f',u')`, and rewrite any law field whose indices change.
- **Q2 (scalar `Rgr` semantics)**: pick one of the three candidate meanings and check
  every law field against it — especially `Rgr_ne_zero` and `Rres_recipe`.
- **Q3 (PrevGrade domain)**, **Q4 (r = 0 support)**: decide; prefer the smaller class.
- **Q5 (Gauss transport)**: search mathlib and the repo for the monic transport theorem
  (`rg` in `leanfinal/`, `lake env lean` probes, mathlib's `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`
  or its actual current name — verify, do not trust this name). If found, `KP_irred`
  loses its OPEN-GAUSS flag with a named lemma; if not, keep the flag.
- **Q6 (μ-divisibility in C.100)** and **Q7 (C.90's needed strength)**: decide the
  faithful reading and record what it costs downstream.

Then: the final class signature (U7 §4.3 as corrected by your answers) as a ready-to-
apply unified diff against `leanspec/Leanspec/ChapC.lean`, replacing the provisional
class body. Do NOT apply it — leanspec is byte-frozen; the orchestrator enacts
amendments. Verify your proposed signature elaborates by writing it to
`leanfinal/scratch/U9_class_check.lean` (adjust imports to match how the leanspec file
elaborates) and running `lake env lean` on it from `leanfinal/`.

## Rules

- NEVER edit `leanspec/` or `leanfinal/Uniformity/`. Your only writes: the two named
  deliverable files.
- Quote the FGMN source verbatim (with published locus) for every load-bearing reading.
- Honesty: if a corrected law field cannot be faithfully typed, mark it OPEN and drop it
  from the diff rather than approximating.
