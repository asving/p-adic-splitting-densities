# Repair-diff Codex confirm (2026-07-29): FLAG 3/1 — 7 of 10 repairs ratified (both overrules, D5, S1-S4 incl. the projection-def); D2/D4/S5 flagged, repair round 2 charged

I’ll verify the applied commit against the actual Lean sources, not just the pasted diff. I’ll trace each D/S repair to its underlying definitions and run read-only checks where the workspace permits, then report only defects with severity.

The shell is unavailable in this environment because its sandbox launcher is missing, so I’m continuing from the complete supplied diff and cross-checking the declarations against one another. The main semantic pressure points are the canonical-policy pin, whether the empty case is truly wired rather than duplicated, and whether the new S-side obligations can still be bypassed.

The repairs are not fully ratified.

- **CRITICAL — D2 remains semantically under-typed.**  
  `OffsetPPin` contains:
  > `Realizes : Node ... → Polynomial ... → Prop`  
  > `total : ... → Realizes ν (pol.liftOf ν)`  
  > `realizes_ne_zero : ... → Realizes ν t → t ≠ 0`

  Because each instance chooses `Realizes`, it may define it as merely `t ≠ 0`. Thus any policy producing nonzero recentering lifts can obtain an `OffsetPPin`, without satisfying the offset-P formula, prescribed residue, or forced slot class. Consequently `CD_canonical` can label a noncanonical policy canonical. The quoted one-lift-rule requirement remains prose rather than a fixed typed predicate.

- **CRITICAL — D4 leaves the originally identified objects wrong.**  
  The finding named `Presented.event` and `Presented.mult`, but the diff leaves them unchanged and adds parallel objects:
  > `def Presented.eventO ... := if ... then Set.univ else S.event`  
  > `def Presented.multO ... := if ... then 1 else S.mult x`

  Therefore, at the empty shape, `Presented.event` still denotes `∅` and `Presented.mult` still denotes `0`; existing consumers remain guarded away from the case. A correct alternative API does not wire the empty case into the note-designated objects and introduces two competing event/multiplicity semantics.

- **CRITICAL — S5 still permits the count semantics to be fabricated or bypassed.**  
  `PolyGeomLaws` declares:
  > `tCount : ... → ℚ → ℕ`  
  > `tcount_val : ... countT.eval q₀ = tCount ... q₀`

  `tCount` is arbitrary data with no typed connection to the actual CTS/[1] table count. It can be chosen to match an absorbed `countT`, so the countT defect remains. Moreover, both `_counted` variants accept `hPGL` but do not use it, while the original uncounted consumers remain available. Hence the principal proof chain can still ignore both value-law obligations.

- **GAP — D6 explicitly leaves sealed classifier checks untyped.**  
  The new unit states:
  > `STILL MISSING ... prediction (5)'s FC8/FC9 PARTITION checks`

  Moving ownership to the census/HC-2 wave may explain the omission, but it does not complete the accepted finding that classifier-side sealed-gate obligations must be typed. The added `C` values, multiplicity, and four event counts are otherwise stated correctly.

The remaining items pass:

- D1’s ruling is consistent with the supplied two-scale excerpts, and `gamTie_stage_form` exposes exactly `gam = e·(STR·ustar) + jstar·h`.
- D3’s `card_classes_abs` states the requested bijective equality with the policy-free `EtaGalEq` quotient under `PresentNorm`.
- D5 correctly types the piecewise L12 threshold and transports `D4R4_all` to `noteNP ≤ N`.
- S1 supplies the per-consumed-pool active-value agreement burden without imposing junk-block determinant nonvanishing.
- S2 loses no note-required pool: all continuing split members remain, halted members consume no β factor, and shape-leg δ values remain included.
- S3 supplies per-cell tables, interpolation, and aggregation.
- S4 fully kills the vacuous-tag defect: `wsh17_pin` is no longer instance-selected data and reduces to `W17ii` at the chain’s own carriers; the `h17 : C.wsh17_pin` binder remains meaningful.

I could not independently rerun Lean because the workspace shell’s bubblewrap launcher is unavailable; none of the findings above depends on build failure.

**FLAG (3 crit / 1 gap)**