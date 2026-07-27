# MovesS-CORE — Codex final-confirmation pass 9 (rev 12, the acceptance rev)

*(2026-07-27. Corpus: MovesS-CORE (95-unit core, §W4-SYNC seam out of scope).
Note: §S-RESUM (frozen note text, lines 11557–12431 of MOVES_2026-07-24.md,
trailing PASS RECORD blocks for §H-DOMAINS/§X-EXHAUST trimmed). Blueprint:
lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md, REV 12. Charge appended the
rev-11→rev-12 diff summary (countS_cells DELETED; U-22 re-scoped to
all-active BASE pools with U-22c consumed; wshval_card owned; wsh_ok's
CL-17(ii) inheritance cross-referenced to the seam pin; device unit split;
scope sentences fixed) and asked for a full end-to-end sweep, not just a
diff check. Verdict: **REJECT (2 crit / 2 gap)** — NOT the acceptance pass.)*

1. **CRITICAL — `cellP_count` is restricted to active pools.**

   Offending spec:

   > `cellP_count : ∀ e τ c q₀, q₀ ∈ M.Pools → M.activeState q₀ e τ →`
   > `((cellP e τ c).eval q₀ : ℚ) = ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)`

   The note requires each cell-size polynomial to be "valued correctly at
   every prime power," including wild pools where cells vanish. The
   activity guard removes precisely those inactive-pool evaluations,
   allowing the polynomial and actual cell count to disagree there.
   `act_iff` only detects a zero polynomial value; it does not restore the
   missing count equality.

2. **CRITICAL — `consumedDeltas`/`RegP` still over-quantify E0.**

   Offending spec:

   > `consumedDeltas T F` as the "MULTIPLICATIVE CLOSURE … all products of
   > AT MOST n factors drawn from {split-leg δ's …} ∪ … shape legs"

   together with:

   > `def RegP … := ∀ e ∈ Finset.Icc 1 n, ∀ δ ∈ consumedDeltas T F,`
   > `Nonempty (PoolHyp … p^δ)`

   The note requires E0 for δ = 1 and every base-change index an actually
   consumed leg reaches. Arbitrary products of factors drawn from
   unrelated or unrealizable legs need not occur along any nesting chain.
   Requiring E0 at all such products strengthens the note's hypothesis.
   `nested_delta_mem` proves coverage of real chains but not that every
   member of the closure is realized.

3. **GAP — the per-cell `(J-RAT)` production dependency remains
   underspecified.**

   Offending specs:

   > `jP : ∀ e τ (o : T.Out e τ), PolyGeom`

   > `j_interp : … routeOf … = .split → evalAt … (jP …).val = M.rowVal …`

   and the separate `cellP_count` field.

   The note's owner-side deliverable is per branching cell: its count
   polynomial together with its XHD-s height sum, followed by the
   cell-sum defining J_{τ,o}. The blueprint supplies an aggregate rational
   interpolant and per-cell count polynomials, but no per-cell rational
   height-mass presentation or typed dependency connecting those
   presentations to `jP`. The measured equality `j_interp` + `rep_indep`
   correctly records the cell-sum's values, but not the displayed
   per-cell rationality provenance.

4. **GAP — U-28 does not formally carry CL-17(ii).**

   Offending spec:

   > `theorem rs4_rational_step (C : RS4Chain …) (hdet : …) :`
   > `(∑ σ ∈ C.Sigmas, Rsh … C.WshP σ) = 1`

   `RS4Chain` contains `wsh_ok`, interpolation and event-card fields, but
   no hypothesis field asserting `W17ii`. U-28 mentions the seam pin only
   in prose:

   > "CL-17(ii)'s PRODUCTION burden is the seam pin W17ii/S-8 — INHERITED
   > AND OPEN"

   The frozen note explicitly attaches CL-17(ii) to RS.4's inherited
   hypothesis set. A cross-reference or acceptance comment is not a Lean
   hypothesis, so the core theorem can be instantiated without the
   production obligation.

Counts: **2 CRITICAL / 2 GAP**

**REJECT (2 crit / 2 gap)**

## Note on the rev-11 → rev-12 diff

R50 (countS_cells deletion) and R53 (wsh_ok/CL-17(ii) declaration) were NOT
flagged by this pass — the pass found them faithful as re-scoped. R51 (U-22
re-scoping) survives only in weakened form: the pass's finding 2 shows the
re-scoping traded one over-quantification (every active pool) for another
(the full multiplicative closure of consumed deltas, not just the deltas
actually realized along a consumption chain) — a genuinely new defect, not
a residual of the rev-11 finding it replaced. Findings 3–4 are the same
GAPs carried forward from pass 8 (rev 11), now joined by a new CRITICAL on
`cellP_count`'s active-pool restriction — a defect introduced BY the R50
per-cell counting pattern itself (the accepted G4 pattern from another
unit, applied here without the domain-of-validity guard the note needs).
