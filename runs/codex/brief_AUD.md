# CODEX BRIEF AUD — fresh-context adversarial audit of the census master chain

You are a fresh-context adversarial referee (the project's standing decorrelated-verifier
role). Your charge: audit the REDUCTION SPINE of the Lean census campaign for semantic
drift, vacuity, and statement-level errors. You fix NOTHING; you quote each offending
passage and classify: CRITICAL (breaks the chain) vs JUSTIFICATION GAP.

THE SPINE (audit in this order; all in leanfinal/Uniformity/ChapI/):
1. IFCG55.lean — decidedSliceAt_all_of_MASTER + capstoneHypotheses_of_MASTER (the master).
2. The wrapper chain it composes: IFCG24 (ConeRemainderLaw/ZcURLim defs), IFCG33
   (the unramified zero-law + decidedSliceAt_all_of_ram5_even4_bridge), IFCG32
   (the bridge discharge), IFCG21 (decidedSliceAt_all_of_cones), IFCG14/15/18/20
   (the sockets + kernels).
3. Spot-audit the definitions for vacuity/drift: DecidedSliceAt (I02), DecidedAt /
   decidedCount / gapSeq (Density/GenuineDensity + Drainage), ConeRemainderLaw's carrier
   (IFCG24 vs IFCG35's remainderCarrier), ZcURLim (IFCG24).
4. The newest reductions: IFCG71/72/73's master recomputations — check the premise
   handoffs compose (the same Props, byte-level, no silent strengthening).

KNOWN-GOOD ANCHORS (don't relitigate): the axiom footprints are checked per-file; the
B.42 cite is owner-signed; the n≤3 instances are landed independently.

DELIVERABLE (write to runs/codex/AUD_report.md): the classified finding list with exact
file:line quotes; an explicit PASS/FAIL per spine link; a final verdict on whether
decidedSliceAt_all_of_MASTER's premises genuinely imply ∀ n DecidedSliceAt n as stated.
