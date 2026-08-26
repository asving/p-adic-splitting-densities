# Unit CIFACE (FABLE) — the capstone interface nodes L0 / DT0 / W0 / WIN0

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean: leanfinal/
(+ leanspec/ READ-ONLY). `lake env lean <file>` from the project dir; NEVER bare
`lake build`.

## Context and charge

CHFD's supply map (docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md — READ WHOLE; its
probe leanfinal/scratch/CHFD_probe.lean is the machine-checked boundary) reduced
`CapstoneHypotheses 2` to ns7 + ladder + deepTwist, and identified the decisive missing
campaigns as guard-to-conclusion bridges, NOT more packaging:

    arising realization/views → HE7A + LB1 + MP1 + HVarthetaRes → ladder
    arising joint arena/views → per-live HVarthetaRes + GentowW → deepTwist

Your job is the four INTERFACE NODES the map names: LADDER-SUPPLY-L0, DEEP-TWIST-DT0,
WELD-SITE-W0, WINDOW-PINNING-WIN0. For each: author the interface — the precise Lean
carrier/def/statement that a supplier campaign proves and the capstone field consumes —
such that (a) it elaborates against the landed corpus TODAY (probe it), (b) the
capstone-field side provably follows from it (probe the implication where cheap, or state
it as the node's exit gate), and (c) it does not smuggle a conclusion (the non-swallowing
fence discipline of C130s18 §5 — read it; your interfaces must be auditable the same way).

## Read

The map (whole, esp. the eleven-field table rows ladder/deepTwist/jd0/genhnBox2/
windowPinning and the DAG section); CHFD_probe.lean; leanspec/Leanspec/ChapI.lean's I.10
sections + A-I.1/A-I.3 notes (the socket shapes and the fences); C130s18.lean §§4-5 (the
enacted socket bodies + anti-swallow audits); C130sg.lean (the S2 instantiations);
F04w.lean:85-91 + F11.lean:46-51 (the intended weld halves the map cites);
I05.lean:90-94 (windowPinning's True body); the HE7A/LB1/MP1 vocabulary via
spec/EFF-HE7.md and the landed ChapE/ChapF files the map points at.

## Honesty fences

You author NEW statements — the trust boundary applies: flag every new carrier for the
standing review; no leanspec edits (interfaces live in leanfinal; the eventual leanspec
re-signs are later recorded amendments, note them as such in the doc). If a bridge
genuinely cannot be stated without new mathematics, say so (BLOCKED-BECAUSE) and name the
missing mechanism precisely.

## Deliverables (write INCREMENTALLY, ≤200 lines per Write/Edit)

1. docs/in-progress/CAPSTONE_IFACE_2026-08-26.md — per-node: the interface statement, its
   design rationale, the supplier-campaign sketch (who proves it, sized), the consumer
   derivation, the anti-swallow audit note.
2. leanfinal/Uniformity/ChapI/IFC0.lean — the four interface carriers + any cheap
   implication proofs; zero sorry, zero new axiom; AxChk footer.
3. runs/wave-b/verdict_CIFACE.md (≤2 pages).
No commits. Do NOT touch roll-ups, leanspec, ChapC (a μ₃ unit is opening the C132 series
concurrently), or the CW wrapper files. Final message ≤25 lines.
