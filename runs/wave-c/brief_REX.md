# UNIT REX — the producer-side recenter-step export (MP1's blocker; ladder campaign leg 2)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

MP1R (runs/wave-c/verdict_MP1R.md, 2026-08-28) PROVED the unrestricted
`Ladder.MP1Carrier` FALSE (countermodel leanfinal/scratch/MP1R_probe.lean, re-verified
exit 0) and identified THE blocker for the honest replacement: the funnel exposes no
"recenter-step export" — the datum that the arising realization's own Montes/MacLane
recentering step produced `B'` (key `Φ − Λ`) from `B` WITHIN the same inductive-valuation
chain, which is exactly what the checked sources ([GN15] Thm 2.3's chain/tangent-class
hypotheses; GMN Thm 2.11's prescribed residual data) require before their
irreducibility/key-hood conclusions apply. Read verdict_MP1R.md IN FULL first — it maps
which cite hypotheses are missing at which Lean premises, and sketches
`MP1CarrierLive`.

Related landed context: the A-I.6 pattern (I10LadderLive.lean's `CanonicalLadderLiveAt`
— quantifier restriction via same-socket realization data), the ChainRealization /
ArisingCore machinery (C130s18 territory), the BlockData/SlotCarrier definitions
(leanfinal/Uniformity/ChapE/E40.lean), and the μ₃ key-chain machinery (the landed
`s2DepthTwoKeyChain`, C132kp* — a concrete recentering chain instance).

## Your charge

1. DESIGN the export: what structure `RecenterStep C B B'` (working name) must the
   realization export so that (a) the arising chain genuinely produces it at every
   recentering it performs, and (b) its fields line up ONE-TO-ONE with the cite's
   hypotheses ([GN15] Thm 2.3: the inductive valuation, the key polynomial in a specified
   tangent class, the monic g, residual multiplicity one — docs/references/ has the pdfs;
   quote the exact hypothesis list from the source text). Produce the CITE MAPPING TABLE:
   source hypothesis ↔ export field ↔ which landed producer datum supplies it at the S2
   instance.
2. STATE `MP1CarrierLive` precisely: MP1's conclusion quantified over `B'` equipped with
   a `RecenterStep`, in the A-I.6/`CanonicalLadderLiveAt` style (same-socket realization
   + the step datum). Check the funnel (E.24 → the capstone ladder field, now
   `LadderSupplyLive`): the `mp1` field currently demands the UNRESTRICTED
   `Ladder.MP1Carrier` — which MP1R proved FALSE. Determine whether the falsity
   countermodel PASSES THROUGH the funnel (i.e. is `LadderSupplyLive` — and hence the
   rebound `CapstoneHypotheses` — ALSO refutable via its mp1 leg?!). THIS IS THE
   HIGHEST-PRIORITY QUESTION IN THE UNIT: if yes, a further amendment (A-I.7: mp1 → live
   form) is forced, and you must say so with a probe-grade construction plan (do NOT
   enact); if no (the countermodel's B' cannot arise inside the funnel's quantification),
   prove/argue exactly why.
3. THE LEAN SURFACE: probe file leanfinal/scratch/REX_probe.lean with `RecenterStep`,
   `MP1CarrierLive`, the S2-instance export construction as far as landed data allows,
   and (if item 2 answers yes) the refutation-shape statements. Verify
   `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/REX_probe.lean`; NEVER
   bare `lake build`; sorry allowed for shape validation, marked.

## Deliverables

- Dated `[REX 2026-08-28]` section APPENDED to docs/in-progress/LADDER_SUPPLY_2026-08-27.md.
- `runs/wave-c/verdict_REX.md`: the item-2 adjudication FIRST (funnel refutable via mp1:
  YES/NO/UNDECIDED + evidence), then the design, cite table, probe status.

## Rules

No git commits. No edits to landed .lean/leanspec/existing scratch. The owner's paper is
never citable; published sources with precise theorem numbers only. Rigor paramount;
quantifier slips are this campaign's chief enemy — machine-anchor every placement.
