# MovesS Lean blueprint — Codex final-confirmation pass 7 (REV 10, CORE ONLY), 2026-07-27
Prompt: /tmp/leanaudit/movess_final7_prompt.txt · Raw transcript: /tmp/leanaudit/movess_final7_verdict.txt

1. **CRITICAL — activity is still keyed to one outcome-level polynomial, not every cell-size polynomial.**

   Offending spec:

   > `act_iff : ... M.activeState q₀ e τ ↔`
   > `(∀ o, routeOf ... ≠ .split → (tgP e τ o).countS.eval q₀ ≠ 0) ∧`
   > `(∀ o, routeOf ... = .split → (jP e τ o).countS.eval q₀ ≠ 0)`

   `MeasuredSide.Cell` permits multiple cells over one outcome through `cellOut`, and `rep_indep` explicitly sums those cells. The note's ACT/cofiniteness argument concerns every individual cell-size polynomial; `(J-RAT)` likewise requires per-branching-cell polynomial data. One `countS` attached to the aggregate `tgP` or `jP` cannot detect an individual empty cell whose aggregate outcome mass remains nonzero. Consequently `act_iff`, `cellsize_nonzero`, and U-22b do not state the displayed CTS-M(ii) mechanism.

2. **CRITICAL — the advertised core inhabitation gate omits mandatory core fields.**

   Offending specs:

   > "the CORE §2 structures … `RS4Chain`'s core fields … are SIMULTANEOUSLY inhabitable"

   > "NOT the shallow-production carriers (`WshP/WshVal/shDom/shEvtH/… = seam duties`)"

   > `n2_rsh ... CHAIN FIELDS INSTANTIATED ... NOT the shallow-production carriers`

   Those carriers and their laws are required fields of the core `RS4Chain`; Lean structures cannot be partially instantiated. Moreover, `rsh_interp` itself mentions `WshP`, so `n2_rsh` cannot be supplied without that omitted data. Thus the core lacks the promised explicit inhabitation story for `RS4Chain`, leaving U-28 and other chain consumers vulnerable to the forbidden empty-hypothesis-structure trap. This also means the core is not fully self-contained at the claimed consistency gate.

3. **GAP — several core units still contain multiple independent displays or hidden proof groups.**

   Offending examples:

   > **U-12c**: "`theorem powSubst_mul ...` and `theorem pow_pool ...`"

   > **U-22b**: "TWO statements"

   > `n2_polygeom` — "the three PolyGeom presentations … + tg_ok/j_ok/ι_ok"

   > `n2_interp` — "tg/j/ι interpolation laws"

   > `n2_degpins` — "the six per-piece degree pins"

   > **U-29e**: determinant identity, two distinct solve-entry identities, and the checksum.

   These are separable theorem obligations, not single-display units. The S5 construction heading also calls its batch "nine units" while enumerating twelve. The total core count of 85 is arithmetically correct, but the claimed one-display decomposition is not.

**Counts:** 2 CRITICAL / 1 GAP

**REJECT (2 crit / 1 gap)**

---

**Process caveat (not part of Codex's audit content, added by the runner):** the workdir
`/tmp/leanaudit` was shared with a prior pass and still held `final_output.md`
(the saved pass-6/REV-9 verdict, 10 crit/3 gap) plus `movess_final6_prompt.txt` /
`movess_final6_verdict.txt`. With `--sandbox danger-full-access`, Codex ran
`rg --files` + `sed` in the workdir, found that leftover file, and its FIRST
response block verbatim reproduced the old pass-6 findings and verdict
("REJECT (10 crit / 3 gap)") — i.e. momentarily answered from stale cached
content rather than a fresh read of the pasted REV-10 core. It then produced a
SECOND, distinct response in the same turn (the one recorded above, ending
"REJECT (2 crit / 1 gap)"), which is the one that actually engages the new
prompt's specifics (`act_iff`'s per-outcome vs per-cell polynomial, the
`n2_rsh`/`RS4Chain` inhabitation gate, the still-bundled units) rather than
repeating rev-9 language. This transcript recorded the LAST verdict as final,
per normal codex exec turn semantics, but flags that the self-correction should
not be taken as fully independent of having just read the rev-9 saved output —
a clean re-run in a scrubbed workdir would be the way to rule out anchoring.
