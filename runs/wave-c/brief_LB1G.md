# UNIT LB1G — the LB1 guard-link: refute or restrict the arbitrary-interface quantifier

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

`Ladder.LB1Carrier` (leanfinal/Uniformity/ChapE/E39.lean, ~lines 110–114) quantifies over
EVERY `RungInterface C B`, not merely interfaces exported by an arising realization. The
VAUD audit (runs/wave-b/verdict_VAUD.md; probe leanfinal/scratch/VAUD_probe.lean,
`lb1_inhabited_socket_tooth`; adjudication docs/in-progress/LADDER_SUPPLY_2026-08-27.md
[VAUD] LB1 row) showed the landed honest antecedent (`s2_degree_four_socket`) leaves the
interface `I` independently quantified — no realization-link premise exists — but did NOT
construct a malicious `I` on the landed S2 carrier, so LB1Carrier is NOT yet refuted at an
arising pair. The stop LS-G0 remains: no proof fleet may target LB1 until this is decided.

The LVT precedent (2026-08-28, leanfinal/Uniformity/ChapI/IFC5.lean +
runs/wave-b/verdict_LVT.md): the vartheta supplier was superseded by a live-range twin
(`CanonicalLadderLiveAt` — restrict the quantifier to data witnessed by a realization
exporting the SAME external socket data). Read it for the pattern.

## Your charge (in order)

1. READ: E39.lean (the `RungInterface` and `LB1Carrier` definitions in full),
   VAUD_probe.lean's LB1 section, the [VAUD]+[LVT] sections of
   docs/in-progress/LADDER_SUPPLY_2026-08-27.md, IFC0.lean's LB1 supplier, and the S2
   socket teeth (leanfinal/Uniformity/ChapI/IFC2.lean–IFC4.lean).
2. ATTEMPT THE MALICIOUS INTERFACE: on the landed S2 carrier (the arising pair supplied
   by `s2_degree_four_socket`), construct a concrete `I : RungInterface C B` for which
   LB1Carrier's conclusion FAILS while every antecedent holds. If it lands, that refutes
   the unrestricted LB1Carrier at an arising pair — land it as
   `leanfinal/scratch/LB1G_probe.lean`
   (verify: `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/LB1G_probe.lean`;
   zero sorry; `#print axioms` footer; footprints exactly
   [propext, Classical.choice, Quot.sound]; NEVER bare `lake build`).
3. WHETHER OR NOT the refutation lands, design `LB1CarrierLive`: the quantifier restricted
   to realization-exported interfaces (mirror `CanonicalLadderLiveAt`'s shape). Two
   sub-questions: (a) write the exact Lean statement; (b) check the E-chapter proof route
   (what E.39's own downstream proofs actually use — grep LB1Carrier's consumers across
   leanfinal/) still goes through at the restricted form, i.e. the funnel through E.24
   `LadderSupply` only ever INSTANTIATES the quantifier at exported interfaces. Produce
   the consumer table: each consumer ↔ the interface it instantiates ↔ exported-or-not.
4. Recommend: REFUTED+RESTRICT / RESTRICT-ANYWAY (with the consumer table as evidence) /
   KEEP-UNRESTRICTED (only if you find a genuine uniform proof strategy for arbitrary
   interfaces — state it as an open lemma with a plan, not optimism).

## Deliverables

- Dated `[LB1G 2026-08-28]` section APPENDED to
  docs/in-progress/LADDER_SUPPLY_2026-08-27.md.
- `runs/wave-c/verdict_LB1G.md`: verdict + claims labeled PROVED (decl names) / GAP /
  BLOCKED-BECAUSE. Optional probe file as above.

## Rules

No git commits. No edits to landed .lean, leanspec, or existing scratch files. Never
weaken statements silently — supersession twins with recorded reasons. Quote exact
declaration names + line numbers for load-bearing claims.
