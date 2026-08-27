# Unit MADJ (codex HIGH) — the Dv2ResSurv numeral adjudication (μ₃ chain gate)

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean: leanfinal/
(`lake env lean <file>` from leanfinal/; NEVER bare `lake build`). You may edit ONLY your
deliverables listed at the end.

## The question

MNV3b (runs/wave-b/verdict_MNV3b.md + leanfinal/Uniformity/ChapC/C132nv3b.lean) proved
`Dv2ResSurv`'s slot-0 equality at the S2 instance but found the slot-1 carry bound
BLOCKED at (u₂,ℓ₂) = (5,2) — landed facts give exactly `Ha+Hb ≤ Hq₀+10` (dvSupp(Φ₂) = 10
is landed), 8 short of the needed `Hq₀+2` — while the SAME clause CLOSES cleanly at
(21,2), matching the campaign's own `s2Hgt₃ Φ₂ = 21` (C132nv1.lean). This echoes the U15
depth-parameter lesson ((2,1,5) is depth 1; (2,1,21) is depth 2 — see
docs/in-progress/PACKAGING_ROUTE_2026-08-25.md §2).

ADJUDICATE: which numeral pair does the μ₃ endpoint theorem (node M3-NV4, not yet landed
— its consumption is specified by C132nv2.lean's endpoint/convolution bank, which takes
`Dv2ResSurv L Ψ u₂ ℓ₂` as a parameter) ACTUALLY need at the S2 instance? Trace the
consumption: read C132nv2.lean's endpoint theorem statements (which (u₂,ℓ₂) the digit
values are priced at — the digits live at the inner μ₂ level, but check whether the
carry-slot clause is applied at the inner pair or the outer key value), C132nv1.lean's
`s2Hgt₃` definition (outer 21/2), C132nv3.lean + C132nv3b.lean (what's proved where), and
the blueprint row M3-NV2/NV4 (docs/in-progress/MU3_CAMPAIGN_2026-08-26.md §6). MACHINE-PIN
the answer: an elaboration probe (leanfinal/scratch/MADJ_probe.lean) showing the NV4-shaped
application firing with the (21,2)-instantiated hypothesis — or, if (5,2) is genuinely
needed, the precise missing fact as a named statement.

## Outcomes (all legitimate)

A. (21,2) is the right instance → write the finding + the probe; the μ₃ chain proceeds
   with MNV3b's landed (21,2) clause; note any C132nv2 docstring clarification needed (do
   NOT edit C132nv2 — record the suggested clarification in the verdict).
B. (5,2) genuinely needed → name the missing fact precisely (the `dvSupp(Φ₂) ≤ 2`-flavored
   bound is FALSE — dvSupp(Φ₂)=10 is landed — so say what else could close it or declare
   the row's mechanism wrong and propose the blueprint amendment).
C. Both needed at different clauses → say exactly which clause needs which.

## Deliverables

leanfinal/scratch/MADJ_probe.lean (zero sorry, zero axiom, exit 0) +
runs/wave-b/verdict_MADJ.md (the adjudication, ≤2 pages, file:line evidence). No commits;
no edits outside these two files.
