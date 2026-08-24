# Unit F3 — type the I.10a/I.10b sockets against the tower-instantiation freeze v2

You are a blueprint-conversion unit (high reasoning) in the p-adic-splitting-densities
campaign. Repo root: `/data/users/asvin/math-and-lean/p-adic-splitting-densities`. Lean
project: `leanfinal/` (mathlib v4.31.0, built; verify per-file with `lake env lean <file>`
from inside `leanfinal/` — NEVER bare `lake build`; chapter roll-up targets like
`lake build Uniformity.ChapI` are allowed).

## Context

Chapter I is the capstone-conditionality chapter: `CapstoneHypotheses n` →
I.15–I.18 assembly → `UniformityStatement`. Its `ladder`/`deepTwist` fields are guarded
by the **I.10a/I.10b sockets**, whose bodies are currently `True` — placeholder types
owed to the tower-instantiation freeze. The freeze v2 is now DELIVERED:
`docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` (D-TIF-4 carrier,
non-swallowing residue design). Your job is to give the sockets their real content,
typed against the freeze v2, following the I01 precedent.

## Read (in this order)

1. `docs/PROJECT_STATE.md` (short state-now file).
2. `docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` — whole document,
   including its two signed-shape findings (single-Kt must be terminal K_r; E.63's
   unbounded ∀i vs the finite live range).
3. The I01 precedent (how a `True` socket body gets typed honestly): `rg NS7Termination
   leanfinal/ leanspec/` and read the surrounding files + `git log --oneline -20` for
   commit bc95d0d3's pattern (byte-wise redraft target, `Iff.rfl` anti-drift pin).
4. The sockets themselves: `rg -n "I\.10a|I\.10b|I10a|I10b" leanfinal/ leanspec/
   blueprint/` and the `CapstoneHypotheses` structure (`rg CapstoneHypotheses
   leanfinal/Uniformity/ChapI/`).

## Deliverables

1. New file(s) in `leanfinal/Uniformity/ChapI/` giving the socket types (the freeze's
   D-TIF-4 carrier transcribed into Lean) and re-typing the I.10a/I.10b socket bodies
   against them, following the I01 anti-drift pattern (keep a byte-wise `Iff.rfl` or
   definitional pin so the socket cannot silently drift from the freeze text).
2. If typing a socket forces a change to a SIGNED leanspec statement (the two
   signed-shape findings suggest E.63 and a single-Kt site need re-signing): do NOT
   edit `leanspec/` — write the exact proposed amendment diff(s) into your verdict file
   for the orchestrator to enact as A-I.x, and structure your Lean so the amendment can
   land without rework (state the corrected form locally, pin it, note the dependency).
3. Verdict file `runs/wave-b/verdict_F3.md`: LANDED / SUPPLY / BLOCKED per socket, the
   list of new declarations, any proposed leanspec amendments (exact diffs), and the
   `lake env lean` commands verified.

## Rules (honesty invariants — non-negotiable)

- NO `sorry`, NO new axioms, NO weakening. A socket typed as anything less than the
  freeze's content must be flagged, not silently narrowed.
- NEVER edit `leanspec/`. Never edit files owned by the in-flight C131 fleet
  (`leanfinal/Uniformity/ChapC/C131*.lean`) or the ChapC roll-up.
- The `CapstoneHypotheses` structure and everything on the capstone path: after your
  edits, run `lake build Uniformity.ChapI` and confirm green; a break there is
  stop-the-line — revert and report BLOCKED.
- Commit early (compiling carrier skeleton within ~20 min), then per increment;
  `git add` ONLY your own files; on index.lock contention sleep 5s and retry.
- Never trust a lemma name from memory: `rg` first.
