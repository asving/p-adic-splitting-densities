# Uniformity — the final Lean proof, simplified form

**Charter (Asvin, 2026-08-13).** This repo holds THE final machine-checked
proof of the uniformity theorem (p-adic splitting densities are given, at
every prime including the wild ones, by one rational function of the local
field's residue size q), built against the COMPRESSED form of the informal
proof (the T-unit corpus in `../lean/notes/openmath/`).

**Relation to `../lean/` (LeanUrat, 1209 modules).** That corpus is a
QUARRY, not a dependency: nothing here imports it. Code may be copied from
it ONLY after verification, and every copied declaration carries a
provenance comment (`-- verbatim from LeanUrat/<file>:<line>, verified
<date>`). Everything else is authored fresh against the certified notes.

**Part 1 (in progress):** the genuine density — for a complete DVR with
finite residue field (ℤ_p or an extension) and a splitting type σ, the
density of monic degree-n polynomials of type σ, defined honestly as a
limit of level-N decided proportions. This definition (not any engine) is
what the main theorem quantifies over.

**Discipline (inherited from the parent project):** zero sorries in landed
state; no axioms beyond Lean core, plus owner-signed gate-(b) literature
cites (each with a faithfulness entry and a `#print axioms`-visible
footprint) — record in `../docs/PROJECT_STATE.md` #61/#66, first exercised
2026-08-16 by `Uniformity/ChapB/B42.lean`; new definitions are the trust boundary —
each ships with a faithfulness note for human review; statement changes
need sign-off. Toolchain pinned to Lean 4.31.0 / mathlib v4.31.0 to match
the quarry (upgrade is a deliberate later step).
