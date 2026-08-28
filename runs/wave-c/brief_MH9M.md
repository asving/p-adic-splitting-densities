# UNIT MH9M — the engine's last math node: mixed reads ABOVE the support line, then Theorem A

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

The dv-graded one-slope Hensel engine (docs/in-progress/HENSEL_ENGINE_2026-08-26.md) is now
Lean-landed EXCEPT Theorem A's assembly. Landed tonight (leanfinal/Uniformity/ChapC/):
C133mh3.lean — Theorem M unconditional AT THE SUPPORT LINE (m1TwistProductLaw, dvSupp_mul,
dvSideMin/Max/Deg_mul, dvResPoly_mul_gen with τ = 1, mixedResidualLaw); C133mh0.lean — the
M4 perturbation family; C133mh4.lean — M-monic; C133mh5.lean — MH.5 CLOSED (the side lift
Λ: twistLiftO / dvWindowLift / dvSideLift with R(Λ(P)) = P exact) plus the MH.7 prefix
(window read-faithfulness `le_dvSupp_succ_of_lineReads_eq_zero`, Bézout-with-degree-control
existence/uniqueness at the stage field); C133mh8.lean — the graded limits and both
bounded-window conversions; C133mh10–13 — H0, Theorem B, the §6 primitives, Theorem C;
C133mh14.lean — `blockFrontier_of_context_of_theoremA` (BlockContext + `TheoremAStatement`
⟹ signed BlockFrontier). ONE application of Theorem A discharges the whole C.35 family.

THE ONE MISSING LEG (recorded in C133mh5.lean's header and verdict_MH5S.md): the assembled
Lemma S (§4.2) needs the grade-c MIXED product read law — Theorem M clause 3 at an
ARBITRARY grade c ABOVE the support line: for the §4.2 solve, one must read the product
p₂·U (p₂ pure at the support line with W(p₂) = w₂; U a window lift with W(U) ≥ c − w₂) at
grade c and get `read_c(p₂·U) = R(p₂)·read_{c−w₂}(U)` (τ = 1 twisted form) — the landed
`dvResPoly_mul_gen` reads only at the support line W(g)+W(z). C133mh5 packaged the exact
demanded shape as the Prop-def `LemmaSStatement` (read it — it is the statement you must
supply the missing leg FOR).

## Your charge (math first; Lean transcription is a later unit)

1. READ: HENSEL doc §§1–4 (especially §3.1′/§3.3's coefficientwise proof of M and §4.2's
   Lemma S), C133mh5.lean's header + `LemmaSStatement` + the dvWindowLift clause lemmas,
   C133mh3.lean's header (the proof route that worked at the support line), and
   verdict_MH5S.md.
2. PROVE (math level, full rigor, every step justified): the above-line mixed read law.
   Recommended attack: the §3.3 coefficientwise route generalizes — the grade-c line of a
   product dev(gz) is the convolution of the lines of dev(g), dev(z) at complementary
   grades; when one factor is PURE with W(g) = w (all its mass ON its support line) and
   the other has W(z) ≥ c − w, the only surviving convolution terms pair g's support line
   with z's grade-(c−w) line — everything else prices strictly above c by the ultrametric
   (the same strict-pricing device MH3 used for the sideMax half). Handle the twist
   cocycle exactly as TW-δ did (C133mh1.twistExp_add_carry) — state precisely where δ = 0
   is forced or where the η^δ carry appears and why it cancels at τ = 1.
   State the law in the LANDED vocabulary (dev, dvHgt, dvSupp, twistRead, dvResPoly /
   line-read maps as in C133mh5) so transcription is mechanical.
3. ASSEMBLE Lemma S (§4.2) from that law + the landed Bézout solve + the landed window
   lift clauses + read-faithfulness — i.e. discharge `LemmaSStatement`'s content at math
   level, checking each landed hypothesis you consume against its ACTUAL Lean signature
   (quote decl names; C133mh5's clause lemmas are the ground truth, not the doc's prose).
4. ASSEMBLE Theorem A (§4.3–4.4): the induction invariants are landed (M4 =
   C133mh0.dv_pure_add_of_lt), the limits are landed (C133mh8), the initialization is
   landed (dvSideLift + M-monic). Write the full induction + limit-exactness argument
   against those exact signatures, flagging any signature mismatch as a named open
   (the transcription unit will need the list). The §2 target is
   C133mh14.TheoremAStatement — quote it and confirm your assembled A discharges it
   clause by clause.
5. NUMERIC CERTIFICATE: extend verification/dv_hensel_cert.py (§10) with a Part checking
   the above-line read law on the doc's worked frames (several grades above the line,
   both τ-branches); run it; report exact counts.

## Deliverables

- A dated `[MH9M 2026-08-28]` section APPENDED to
  docs/in-progress/HENSEL_ENGINE_2026-08-26.md: the above-line law (statement + full
  proof), Lemma S's discharge, Theorem A's assembly, the transcription node list with
  Lean-ready statements, and any named opens.
- `runs/wave-c/verdict_MH9M.md`: per-item PROVED / GAP / BLOCKED-BECAUSE with exact
  landed-decl citations; certificate counts.

## Rules

No git commits. No edits to landed .lean or leanspec files (scratch probes allowed:
leanfinal/scratch/MH9M_probe.lean, verified via
`cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/MH9M_probe.lean`; NEVER
bare `lake build`). Rigor is paramount — an honest GAP beats a papered step. Statements
in landed vocabulary; never weaken `LemmaSStatement` or `TheoremAStatement`.
