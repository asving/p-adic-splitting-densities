# Units CW1a / CW1b (SONNET) — the CHFD first-wave public wrappers

Shared brief; each unit takes its assigned two wrappers. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean: leanfinal/ (`lake env
lean <file>` from leanfinal/; NEVER bare `lake build`).

Source of truth: docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md (CHFD) — the a0/a1/a2
rows and the "First wave" paragraph; the machine-checked boundary is
leanfinal/scratch/CHFD_probe.lean (READ it — your wrappers largely replay its proofs as
public production declarations).

- CW1a: the `DecidedSliceAt 2` wrapper (supply: I02.lean:116-125 replay, G.51) and the
  `MenuLawAt 2` wrapper (supply: I03.lean:177-210 gate content).
- CW1b: the `DrainageAt 2` wrapper (supply: the landed n≤3 drainage, see the map's a2 row)
  and the `MenuLawAt 3` wrapper (supply: the cubic menu G54.lean:35-38).

Land as PUBLIC theorems in ONE new file per unit in leanfinal/Uniformity/ChapI/ (follow
the local naming convention; dated docstrings). Statements must instantiate the
definitional layer (I.01–I.07 defs) at the stated degree — no statement invention: if the
map's sketch doesn't elaborate, adjust plumbing only, else STOP that wrapper and record
BLOCKED-BECAUSE. Every declaration: zero sorry, zero new axiom, `#print axioms` footer in
the verdict (expect Lean-core; the ns7-adjacent wrapper may inherit `agnprw_termination` —
report exactly what prints). Do NOT touch roll-ups, leanspec, any ChapC file (a concurrent
amendment unit owns ChapC right now), or the other unit's file.

Deliverables: your one landing file + runs/wave-b/verdict_CW1a.md (resp. CW1b.md).
Write incrementally; no commits; final message ≤20 lines.
