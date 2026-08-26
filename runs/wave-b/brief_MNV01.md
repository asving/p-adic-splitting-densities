# Unit MNV01 (SONNET) — μ₃ campaign chain head: nodes M3-NV0 + M3-NV1

Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean: leanfinal/
(`lake env lean <file>` from leanfinal/; NEVER bare `lake build`).

Source of truth: docs/in-progress/MU3_CAMPAIGN_2026-08-26.md §6 rows M3-NV0 and M3-NV1 —
execute exactly those two nodes, in order, with the landed inputs the rows cite
(file:line). §5 (reuse boundary) tells you which μ₂ banks port; §1 pins the parameters
(depth-2 target (2,1,21); u₃ = 21; Φ₂ = composedKey at depth 2, degree 4).

* M3-NV0: generalize the basic `dvSupp` zero/finiteness/add/negation bank to
  `dv2Supp L Ψ` — NO S2 numerals in the theorem statements (parameter-free shell).
* M3-NV1: define `s2Hgt₃ g := toZ (dv2Supp L Φ₂ g 21 2)` and pin: zero, ne-top, add
  inequality/equality, the `Φ₂` value 21, and the field shape.

File convention: this campaign opens the C132 series — land M3-NV0 in
`leanfinal/Uniformity/ChapC/C132nv0.lean` and M3-NV1 in `C132nv1.lean` (C132nv1 imports
C132nv0). Follow the C130-series docstring style (dated node tags `[M3-NV0, 2026-08-26]`).

Rules: no statement invention beyond the rows' specs — where a row's sketch doesn't
elaborate, adjust plumbing only, else STOP and record BLOCKED-BECAUSE with the error.
Zero sorry, zero new axiom; `#print axioms` footer per file, reported in the verdict
(expect Lean-core). Do NOT touch roll-ups, leanspec, any existing file. Deliverables:
your two files + runs/wave-b/verdict_MNV01.md. Write incrementally (≤200 lines per
Write/Edit call); no commits; final message ≤20 lines.
