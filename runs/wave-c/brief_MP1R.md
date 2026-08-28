# UNIT MP1R — redesign the MP1 supplier route (the cite route is refuted)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

`Ladder.MP1Carrier` (leanfinal/Uniformity/ChapE/E40.lean, ~lines 152–178) quantifies over
EVERY recentered `B' : BlockData C` satisfying a key equality (`B'.Φ = B.Φ − Λ` with
`Λ ≠ 0`, `deg Λ < D`) and a divisibility (`B'.Φ ∣ B.F`); its conclusion asserts key-hood /
irreducibility for `B'.Φ`. The VAUD audit (runs/wave-b/verdict_VAUD.md; probe
leanfinal/scratch/VAUD_probe.lean, `mp1_inhabited_socket_forces_irreducible`;
adjudication in docs/in-progress/LADDER_SUPPLY_2026-08-27.md [VAUD] MP1 row) REFUTED the
planned literature route at its exact Lean premises: deriving `hirr` from only
`Λ ≠ 0 ∧ deg Λ < D ∧ B'.Φ = B.Φ − Λ ∧ B'.Φ ∣ B.F` is NOT what the checked sources say.
[GN15] Thm 2.3 starts from an inductive valuation/MacLane chain, a key polynomial φ in a
specified tangent class, and a monic g, and its irreducible-leaf clause additionally needs
residual multiplicity one; GMN Thm 2.11 constructs a representative of a type with
prescribed residual data. Neither identifies an arbitrary divisibility-only `B'.Φ` with
that representative.

The LVT precedent (2026-08-28): the vartheta supplier was superseded by a live-range twin
(`leanfinal/Uniformity/ChapI/IFC5.lean`, `CanonicalLadderLiveAt` pattern — a realization
witnessing the SAME external socket data restricts the quantifier). Read IFC5.lean and
runs/wave-b/verdict_LVT.md for the pattern.

## Your charge

Design the honest MP1 route. Work the options in this order and report on each:

1. **Live supersession**: formulate `MP1CarrierLive` — the same conclusion but quantified
   only over `B'` EXPORTED by an arising realization (the recentering the Montes/MacLane
   step actually produces). Key question: at the restricted premises, do the cited
   theorems ([GN15] Thm 2.3 / GMN Thm 2.11 — docs/references/ has the FGMN 2015 pdf and
   the s10208 pdf; the citation ledger is docs/AXIOM_FAITHFULNESS.md and the spec files
   in spec/) genuinely supply `hirr`? Produce the CITE MAPPING TABLE: each hypothesis of
   the source theorem ↔ the exact Lean premise of `MP1CarrierLive` that supplies it, and
   each conclusion clause ↔ the Lean conclusion. If a hypothesis has no Lean supplier
   (e.g. residual multiplicity one), say so — that becomes a new premise of the Live form,
   and you must check the funnel (E.24 `LadderSupply` → the capstone `ladder` field) can
   provide it at the arising sites (read leanfinal/Uniformity/ChapI/IFC0.lean's MP1
   supplier and the S2 socket teeth in ChapI/IFC2–IFC4).
2. **Direct mechanism**: can the restricted form be PROVED (not cited) from the landed
   corpus — e.g. the landed key-criterion/irreducibility banks in ChapC (C132kp* series,
   `s2Mu3_key_irreducible` etc.) generalized? Sketch the proof plan wired to exact landed
   declaration names if plausible; estimate Lean sizing.
3. **Countermodel**: is the UNRESTRICTED `MP1Carrier` false at the landed corpus?
   (A reducible `B'.Φ = B.Φ − Λ` dividing `B.F` with all premises satisfied.) If you can
   construct one concretely, land it as `leanfinal/scratch/MP1R_probe.lean`
   (verify: `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/MP1R_probe.lean`,
   zero sorry, `#print axioms` footer, Lean-core footprints only; NEVER bare `lake build`).

## Deliverables

- Dated `[MP1R 2026-08-28]` section APPENDED to
  docs/in-progress/LADDER_SUPPLY_2026-08-27.md: the chosen route, the cite mapping table
  (option 1) or proof plan (option 2) or countermodel (option 3), exact proposed Lean
  statement for `MP1CarrierLive`, and what remains open.
- `runs/wave-c/verdict_MP1R.md`: verdict + every claim labeled PROVED/CITED-FAITHFUL/GAP/
  BLOCKED-BECAUSE. Optional probe file as above.

## Rules

No git commits. No edits to landed .lean, leanspec, or existing scratch files. Never
weaken a statement silently — supersession twins with recorded reasons are the pattern.
The owner's own paper is NEVER citable. Cites must be published sources with precise
theorem numbers; if the pdf text does not support a claim, say so plainly.
