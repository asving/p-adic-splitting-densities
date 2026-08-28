# UNIT A8D — the A-I.8 adjudication: replace the GN payload leg with the direct key-irreducibility route?

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

DWR's stop-line (runs/wave-c/verdict_DWR.md — READ FIRST, especially "Stop-line finding"):
`I10RecenterLive.GNCitePayload`'s shape is structurally defective — `exactLeaf` identifies
GN Thm 2.3's slope-residual-selected factor `g_{λ,ψ}` with `phi := B'.Φ`, while
`leaf_dvd_input`/`RecenterStep` demand `phi ∣ B.F`; in GN's factorization literal-`phi`
divisors form the separate key-power term (φ has no finite principal side in its own
φ-development), so NO input in ANY tower yields a source-faithful occurrence under this
payload. The fork (A-I.8-grade, flagged not enacted): (α) redesign the payload shape so
the GN citation indexes honestly (the selected factor ≠ the key; the payload would carry
the selected factor SEPARATELY and derive B'.Φ's key-hood from it), or (β) REPLACE the GN
leg entirely with the direct key-irreducibility route.

THE (β) MODEL IS LANDED: `C134p1d.isMuKey_of_isTestKey` (leanfinal/Uniformity/ChapC/
C134p1d.lean) proved key-hood at the level valuation CITE-FREE — monic + degree cap +
the residual lift through the μ-cofactor `g /ₘ Ψ`, all from the landed engine (Theorem M
clause 3 + the C.26 degree law + the C130kp1 remainder mechanism made frame-generic).
MP1CarrierLive's CONCLUSION is precisely key-hood/irreducibility of `B'.Φ` (read
I10RecenterLive.lean's MP1CarrierLive + what E40's MP1Carrier conclusion actually asserts
— rg both). If the P1D mechanism generalizes to the deep-level valuations (the μ₄/μ₅
data of the revised blueprint), the mp1 leg needs NO literature cite at all.

## Your charge

1. READ: verdict_DWR (the stop-line + the revised blueprint's §11), I10RecenterLive.lean
   in full, E40.lean's MP1Carrier conclusion, C134p1d.lean's proof architecture (which
   parts are level-generic already vs level-2-specific), C134dv2g.lean's IsMuKey, and
   verdict_P1D.md's per-clause dictionary.
2. ADJUDICATE (α) vs (β) by the end-to-end criterion, with (β) presumed favored unless
   you find a genuine obstruction: for (β), work out exactly what
   `MP1CarrierLive`'s conclusion needs at a deep occurrence and whether P1D's three legs
   (monic — definitional; μ-minimality — the degree count; μ-primality — M clause 3 +
   the residual lift) each generalize from the level datum (L : LevelDatum, level 2) to
   the deep tower levels (the μ₄ calculus at (2,1,85), the μ₅ refinement (1,1,171) per
   the revised blueprint). Name precisely which landed generic pieces carry over (Theorem
   M is frame-generic — it should) and which need level-r twins (the C.26 degree law?
   the remainder mechanism? — these may be the SAME level-2 twins the F1.4–F1.6 tail
   already needs, i.e. the blueprint's level-2 engine sub-blueprint: check §11).
3. DELIVER: the A-I.8 amendment DRAFT (exact diff shape: MP1CarrierLive's RecenterStep
   loses the GNCitePayload field, gains the direct-criterion demand — or (α)'s corrected
   payload if you find (β) blocked), the consumer/supplier obligation table, and the node
   additions/deletions to the revised blueprint (a dated [A8D] section appended to
   docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md). Do NOT enact any Lean/leanspec
   edit — the enactment is the orchestrator's next pass.
4. Probe leanfinal/scratch/A8D_probe.lean for any statement-shape validation you need
   (verify per-file; NEVER bare `lake build`; sorries marked as shape-only).

## Deliverables

- The [A8D] blueprint section + `runs/wave-c/verdict_A8D.md` (the adjudication with the
  generalization table: per-leg, per-level, landed vs twin-needed vs blocked).

## Rules

No git commits. No edits to landed .lean/leanspec files. Rigor paramount; the (β) route
must be checked leg-by-leg against actual landed signatures, not by analogy. Owner's
paper never citable.
