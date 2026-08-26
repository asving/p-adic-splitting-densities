# Unit AMND (codex HIGH) — the two DEC3R-mandated signed consumer amendments

You are an amendment-enactment unit in the p-adic-splitting-densities campaign. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Projects: leanspec/ (SIGNED
statements — byte-frozen EXCEPT recorded amendments, which is exactly your job) and
leanfinal/ (landed corpus). Lean 4.31.0 + mathlib, pre-built; verify with `lake env lean
<file>` from the respective project dir; NEVER bare `lake build`.

## The charge

DEC3R's μ₃ blueprint (docs/in-progress/MU3_CAMPAIGN_2026-08-26.md — READ WHOLE; its
verdict runs/wave-b/verdict_DEC3R.md) found the depth-2 GENTOW endpoint cannot fire until
two signed consumer amendments are enacted. Both are honesty-preserving re-signs under the
standing statement-change authority (no fake axioms, no silent weakening, dated recorded
amendments). Machine evidence: leanfinal/scratch/DEC3_probe.lean (green; do not edit —
extend into leanfinal/scratch/AMND_check.lean if you need new probes).

AMENDMENT 1 — the hprev fence. `hprev : I.PrevGrade u'` is source-faithfully impossible
at u′ = 21 (full-current clearing, FGMN Def 3.12 = evenness at S2; `Coprime 21 2` and
`¬PrevGrade 21` hold simultaneously). Re-sign per the blueprint: `hprev : 2 ≤ f' →
I.PrevGrade u'` (or the blueprint's equivalent f′=1 base-theorem form if that is what it
pins). Affected signed nodes per DEC3R's consumer audit: C.99 `gentow2_Bpp`, both C.89
paths. The f′=1 base case is machine-proved in DEC3_probe.lean (the literal ratio identity
via cancellation, no graded multiplication) — cite it in the amendment comment.

AMENDMENT 2 — the chainNorm re-index. `chainNorm 2 21 = keyAt 2` falsifies the signed
strict degree premise; the source's n̂₂ is the landed `towerNorm 1`
(leanfinal/Uniformity/ChapC/C83.lean:182-187; probe computes the S2 realization
`16·keyAt 1`, degree 2 < 4). Enact the blueprint's COORDINATED
`chainNormBelow`/`thetaRatio`/consumer re-index — NOT a weakened degree claim. Follow the
blueprint's exact diff. If any part of the diff is not fully pinned by the blueprint,
enact only the pinned part and record the rest as a named OPEN row in your verdict —
never guess a statement.

AMENDMENT 3 — the shadow_persistence degree fence (ADDED 2026-08-26 ~19:50, unit MBRIDGE's
stop-the-line finding; runs/wave-b/verdict_MBRIDGE.md §1 + docs/in-progress/
RB3_BRIDGE_PROOF_2026-08-26.md). The signed `shadow_persistence`
(leanspec/Leanspec/ChapC.lean:3482-3494) is REFUTABLE as signed: `g := (composedKey T)^μ₂`
satisfies `hbudget` vacuously (all Φ₂-digits below μ₂ vanish, `addVal 0 = ⊤`) while
`hc : TouchCert` pins the discrepancy height at exactly `θ_j`, contradicting clause 1's
`θ_j + 1` (TouchCert certified non-vacuous at three coordinates in
verification/rb3_bridge_cert.py, 210 PASS / 0 FAIL). Enact: insert
`(hdeg : g.natDegree < μ₂ * T.D₂)` — automatic for the intended `g = f − Φ₂^μ₂`, mirrors
the landed `towerLocus_iff_budget`'s own `hdeg`, and is exactly what MBRIDGE's proof
consumes. Consumer audit: grep landed leanfinal consumers of `shadow_persistence` (RB3's
closures elaborate in scratch/DEC4_check.lean:147-188 — re-check they still elaborate with
the added binder).

AMENDMENT 4 — the HasLabel degree pin (ADDED 2026-08-26 ~20:10, unit MHENS's stop-the-line
finding; runs/wave-b/verdict_MHENS.md §1 + docs/in-progress/HENSEL_ENGINE_2026-08-26.md §7).
`HasLabel` (C.29) is LEAKY on the defective stratum `D′ ∤ deg g`: it absorbs any monic
unit-content factor of degree < D′ (weight 0, slot read 1), so the concrete ℤ₂ instance
(Φ′ = x²+2x+12, fS = x²+6x+12, g = fS·(x+1)) yields TWO labelled splits — machine-verified
(verification/dv_hensel_cert.py Sec 5, 2832 checks 0 fails), normalization-robust. REFUTED
as signed: C.34's uniqueness clause, C.35 `blockFactor_spec` clause 3, and the planned
BlockFrontier-from-BlockContext. Enact repair R1: pin the degree — `HasLabel ∧ D′ ∣ deg` —
in C.34's clauses and `BlockFrontier`'s maximality quantifier (this matches the classical
LEMMA HE7-6 degree pin `D″ | deg f_S`, spec/EFF-HE7.md:1653, which the corpus surrogate
dropped). The `D′ ∣ deg` stratum is immune (floor-cap pigeonhole, doc §5 B1). The eight
`_of_frontier` rows survive unchanged as conditionals. Consumer audit: grep landed
leanfinal consumers of the amended clauses (C35b's D13 refutation record is this leak's
visible tip — keep it verbatim).

## Protocol

1. Read: MU3_CAMPAIGN_2026-08-26.md (whole), verdict_DEC3R.md,
   docs/REVIEW_QUEUE_2026-08-26.md's amendment-table format (A-C.13/A-C.14/A-C.15 rows are
   your precedent), docs/in-progress/COR412_ADJUDICATION_2026-08-25.md (A-C.13's enactment
   style), the affected leanspec/Leanspec/ChapC.lean nodes, and the landed consumers:
   leanfinal/Uniformity/ChapC/C99r.lean, C107ac14.lean, C130la.lean, C83.lean.
2. Determine the next free amendment numbers: grep leanspec + the review queue for the
   highest `A-C.` tag (A-C.16 exists; likely you take A-C.17 and A-C.18 — verify).
3. Enact in leanspec with dated `[A-C.x, 2026-08-26]` comments citing MU3_CAMPAIGN +
   DEC3_probe.lean, in the exact style of the A-C.13/A-C.15 comments you find.
4. Ripple: grep leanfinal for every landed twin/consumer of the amended statements
   (comment-strip aware — check `#print axioms`-bearing declarations, not just names).
   Repair them so everything you touched re-elaborates green. If a landed proof cannot be
   mechanically repaired, STOP that amendment, revert to a green state, and record
   BLOCKED-BECAUSE.
5. Re-elaborate every touched file (`lake env lean`, exit 0, zero sorry, zero new axiom);
   `#print axioms` footers in the verdict for every re-proved declaration.
6. Add the two amendment rows to docs/REVIEW_QUEUE_2026-08-26.md following its table
   format (they are Tier-2 amendment rows for the owner's later read).

## Deliverables

leanspec edits (the two amendments) + minimal leanfinal consumer repairs +
leanfinal/scratch/AMND_check.lean (if needed) + the review-queue rows +
runs/wave-b/verdict_AMND.md (LANDED/SUPPLY/BLOCKED per amendment, files touched, AxChk).
Do NOT git add/commit. Do NOT touch leanspec/Leanspec/ChapI.lean or
leanfinal/Uniformity/ChapI/ (a concurrent unit owns them). Do NOT touch roll-ups.
