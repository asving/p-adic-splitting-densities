# Unit HW1 (codex, default effort) — H116B4_MAP fireable rows GR-1/2 + GR-3/3b

You are a transcription unit in the p-adic-splitting-densities campaign. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(Lean 4.31.0 + mathlib, pre-built; `lake env lean <file>` from leanfinal/; NEVER bare
`lake build`).

## The charge

docs/in-progress/H116B4_MAP_2026-08-26.md (READ WHOLE; verdict:
runs/wave-b/verdict_DEC5R.md) marks two of H.116b4's five rows SUPPLY/fireable from
landed inputs. Land exactly those two rows' Lean-facing statements per the map:

1. GR-1/2 (ghosts): leaf count = ghost × image-multiplicity — landed shear congruences
   (leanfinal/Uniformity/ChapH/H115c.lean:164 region) + finite constant-fibre bookkeeping.
2. GR-3/3b (cofactor/Fit): monic division mechanics + reverse admissibility via the landed
   exact planted frame profile (leanfinal/Uniformity/ChapH/H116b2.lean:448 region).

These are SUB-LEMMAS toward `planted_presentation_card` (H.116b4) — the signed node itself
stays research-open. HARD FENCES: (a) the peel-shift-REPLANT route is CLOSED,
machine-refuted (blueprint/CHAP-H_general_induction.md fence A-H.7/F1) — do not use any
fibre-to-fibre replant map; (b) no leanspec statement changes; (c) do not claim or state
the three BLOCKED research cores (restricted Smith, one-grade lifting, uniform-pushforward
induction) — if a row's map-sketch secretly needs one of them, STOP that row and record
BLOCKED-BECAUSE.

## Protocol

1. Read the map's two row entries in full: the battery evidence cited, the Lean-facing
   statement sketch, the named landed inputs. Read those landed inputs
   (H115c.lean, H116b1.lean, H116b2.lean — the relevant sections).
2. Land in ONE new file leanfinal/Uniformity/ChapH/ named per its neighbors' convention,
   with the local docstring/dated-note style.
3. Every declaration: `lake env lean` exit 0, zero sorry, zero new axiom; `#print axioms`
   footer in the verdict (expect Lean-core only).
4. If the map's statement sketch does not elaborate as written, adjust ONLY plumbing
   (binders/imports/universes), never content; record every deviation. If content itself
   is wrong, STOP the row and record BLOCKED-BECAUSE with the elaboration error.

## Deliverables

Your ONE new ChapH landing file + runs/wave-b/verdict_HW1.md (LANDED per declaration,
file:line, AxChk footer, deviations). Do NOT git add/commit. Do NOT touch leanspec/,
blueprint/, roll-ups, the battery, leanfinal/Uniformity/ChapI/, or anything outside your
deliverables.
