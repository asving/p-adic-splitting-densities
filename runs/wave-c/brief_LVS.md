# UNIT LVS — the live vartheta supplier: mathematics + Lean surface (post-A-I.6 ladder campaign, leg 1)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

A-I.6 is ENACTED (2026-08-28, commit 367c47c7): `CapstoneHypotheses.ladder` now demands
`IFC5.LadderSupplyLive` — the vartheta leg only at indices live in a realization
witnessing the SAME socket data (`CanonicalLadderLiveAt`, home
leanfinal/Uniformity/ChapI/I10LadderLive.lean). The refuted unbounded form and its
history: runs/wave-c/verdict_AI6.md, verdict_AI6E.md, the [VAUD]/[LVT]/[AI6] sections of
docs/in-progress/LADDER_SUPPLY_2026-08-27.md. The open mathematics is LS-V10 (named in
verdict_LVT.md): PROVE `Ladder.VarthetaRes G Kt L N v ρ q i` at every gauge-live index
`i ≥ 3` of an arising realization, from the realization's own exports.

Landed material to build on: the GCW chain (IFC1–IFC4: the wired S2 witness
`s2SplitNodeWired`, `s2Wired_gentowWWindow_at_own_exports` — the first GentowWWindow at
an arising witness's own exports through the μ₃ endpoint), the unconditional depth-2 μ₃
calculus (`s2Mu3_calculus_nonempty`, C132kp6b.lean; consumer `s2Mu3_gentow5w_two`,
C132sg3.lean), the gauge machinery (C130vw.lean: `GaugeFamilyViewEq`, `GaugeLive`;
E.61/E.62: the typed `VarthetaRes` socket), and VAUD's replacement lemma showing exactly
what the guard pins at live indices.

## Your charge

1. READ (order): I10LadderLive.lean, IFC5.lean, verdict_AI6E.md, the LADDER_SUPPLY doc in
   full, E.61's `VarthetaRes` definition (rg in leanfinal/Uniformity/ChapE), C130vw.lean's
   GaugeLive/GaugeFamilyViewEq, and IFC4.lean's wired-witness exports.
2. THE MATH: at a gauge-live index (1 ≤ i < core.r), `GaugeFamilyViewEq` pins the
   `(v i, ρ i, q i)` package to the realization's exported normal-section data. Work out
   exactly what `VarthetaRes` demands there and PROVE it from the exports — starting at
   the landed S2 witness (core.r = 2: the live range is i ∈ {1}, but the supplier demands
   i ≥ 3 → live, which at r = 2 is VACUOUS — check this arithmetic first!). If the r = 2
   demand is vacuous, the S2-level supplier is a vacuity discharge (prove it as such,
   honestly labeled: the tooth is real only at r ≥ 4). Then do the real work: the GENERAL
   arising-realization case (any r): state precisely what per-level export data suffices
   (connect to the WLE exporter design in docs/in-progress/GC13_WIRING_2026-08-27.md's
   [WLE] section) and prove VarthetaRes at live indices from it, or reduce it to named
   open lemmas about the tower exports (the μ₃-calculus pattern at general depth).
3. THE LEAN SURFACE: exact statements (landed vocabulary) for: (a) the r = 2
   vacuity/discharge lemma; (b) the general live supplier
   `varthetaRes_of_live_of_exports`; (c) the bridge from (b) to
   `LadderSupplyLive.vartheta`'s exact field shape. Probe file
   leanfinal/scratch/LVS_probe.lean (statements may carry sorry for shape validation,
   marked; verify `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/LVS_probe.lean`;
   NEVER bare `lake build`). Prove in the probe whatever is within reach — the r = 2
   discharge especially.
4. Numeric spot-certificate if the math has computable content (verification/ pattern).

## Deliverables

- Dated `[LVS 2026-08-28]` section APPENDED to docs/in-progress/LADDER_SUPPLY_2026-08-27.md:
  the math (full rigor), the Lean surface, named opens.
- `runs/wave-c/verdict_LVS.md`: per-item PROVED / OPEN-LEMMA / BLOCKED-BECAUSE with exact
  landed-decl citations.

## Rules

No git commits. No edits to landed .lean/leanspec/existing scratch. Rigor paramount;
honest vacuity findings are first-class results (this campaign has been reshaped by five
of them). Statements in landed vocabulary; the `LadderSupplyLive.vartheta` field shape is
signed — consumed byte-as-is.
