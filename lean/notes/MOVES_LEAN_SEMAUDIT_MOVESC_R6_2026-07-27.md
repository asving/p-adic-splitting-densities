## Round-6 semantic-faithfulness audit

1. **R6.A.1 — `fineSlot` has the exact C.1.0(a) index arithmetic: PASS.**

   > `def Node.fineSlot ... (b : ℕ) : ℕ := b / ν.Dwidth`

   Rev 14 assigns slot `j` the base-index block `[j·Dwidth, (j+1)·Dwidth)`. Thus `b / Dwidth` is exactly that slot index. In every coherent history `Dwidth > 0`: the root width is `1`, and the successor-width law multiplies positive `e`, `g`, and `Dwidth`.

2. **R6.A.2 — `slotVal` is exactly the recorded fine-slot valuation: PASS.**

   > `def Node.slotVal ... (j : ℕ) : ℚ := ν.line.at (j * ν.Dwidth)`

   This is literally rev 14’s `new(j) = line.at(j·Dwidth)`, evaluated at the left edge of the fine block. It does not accidentally evaluate at the coordinate’s raw base index or at a `childWidth` edge.

3. **R6.A.3 — the new boundary composes the two definitions correctly: PASS.**

   > `H.htH i (coordOf c) ≤ ν.slotVal (ν.fineSlot (coordOf c).2)`

   Expanding the definitions gives

   `ht(c) ≤ line.at(((b / Dwidth) · Dwidth))`

   where `b = (coordOf c).2`. This is precisely `ht(c) ≤ new(j)` for the unique fine slot containing `b`.

4. **R6.A.4 — the comparison directions match the inventory: PASS.**

   > `H.floorH ... < ht(c)`

   > `ht(c) ≤ slotVal(...)`

   Hence the band is `(F_i(b), new(j)]`. The lower edge is correctly strict because freshness selects content “STRICTLY ABOVE `F_i`.” The upper edge is correctly inclusive:

   - At span slots, equality is the value-digit level.
   - At β/γ slots, the strict valuation bound makes the line level itself a zero, so equality belongs to the strip.

5. **R6.A.5 — forward direction, no coordinate above the true valuation survives: PASS.**

   Any admitted coordinate satisfies `ht(c) ≤ slotVal(fineSlot b)` directly. Therefore, at `e·g > 1`, none of the former interval

   `(slotVal(fineSlot b), lineStep b]`

   can enter the band. The round-5 spurious-zero mechanism is closed completely, not merely narrowed.

6. **R6.A.6 — reverse direction for α species: PASS.**

   Rev 14’s α inventory consists of:

   - strip zeros with `F_i(b) < ht(c) < new(j)`, and
   - the complete on-lattice level set with `ht(c) = new(j)`.

   Both satisfy the new band predicate. Equality is then classified by `IsValueCoord`; the strict interior is classified as strip content. No α coordinate in the inventory is excluded.

7. **R6.A.7 — reverse direction for β/γ species: PASS.**

   Rev 14’s fresh β/γ strips are `(F_i(b), new(j)]`. Every such coordinate satisfies both band inequalities. Since the slot is not a span slot, `IsValueCoord` fails even at equality, so the `new(j)` level is correctly forced to zero rather than misclassified as a value digit.

8. **R6.A.8 — crossing, endpoint, and rim behavior are exact: PASS.**

   If `new(j) ≤ F_i(b)`, the conjunction

   > `F_i(b) < ht(c) ∧ ht(c) ≤ new(j)`

   is impossible. Thus γ self-truncation happens at the exact fine slot.

   A non-adjacent endpoint has `j* < μ`, so its fine block lies below `prevRim` and its strip/value content remains included. An adjacent endpoint has `j* = μ`; its block begins at `μ·Dwidth = prevRim`, so the strict region bound excludes it, matching the inherited `(VERTEX)/(HV)` treatment.

9. **R6.A.9 — both directions of inventory equality hold: PASS.**

   Summarizing findings 5–8:

   - Every coordinate admitted by `inFreshBand` is genuine C.1 fresh content at its own fine slot.
   - Every base coordinate occurring in C.1’s fresh α/β/γ inventory satisfies `inFreshBand`.

   There is neither residual over-inclusion above `new(j)` nor new under-inclusion at the upper edge, crossing, non-adjacent endpoint, or β/γ equality level.

10. **R6.B.1 — coarse `lineStep` remains faithful for (ZC-a): PASS.**

   > `def Node.lineStep ... := ν.line.at ((b / ν.childWidth) * ν.childWidth)`

   > `Node.staircase` uses the same `childWidth` left-edge convention.

   Rev 14’s cumulative floor is explicitly the maximum of post-landing line staircases on their factor interiors. Thus retaining the coarse `childWidth` staircase for `(ZC-a)` is correct. The fresh read’s clause geometry and the inherited state floor intentionally live at different granularities.

11. **R6.B.2 — no law mixes the coarse and fine conventions: PASS.**

   `inFreshBand` uses only `fineSlot` and `slotVal`. The three consumers use `inFreshBand` by name:

   > `fresh_band ... inFreshBand ...`

   > `fresh_cover ... inFreshBand ...`

   > `mstar_eq ... {c // inFreshBand ...}`

   None separately reintroduces `lineStep`. Uses of `childWidth` in `TransitionAdmissible`, `prevRim`, width coherence, and rim thresholds are base-index translations or post-landing geometry, not fresh upper bounds.

   When `e·g = 1`, `childWidth = Dwidth`, so `lineStep b = slotVal(fineSlot b)` on coherent histories. The stated recentering coincidence is exact.

12. **R6.C.1 — fresh 978-line semantic sweep: no regression found.**

   The round-5 species controls remain intact:

   - strip clauses cannot occupy `IsValueCoord` positions;
   - value supports are complete fine-block level sets by an iff;
   - `fresh_band`, `fresh_cover`, and pairwise disjointness give exact coverage;
   - per-clause codimensions still sum to the now-correct band cardinality;
   - the root still needs no special value-support constructor.

   The previously noted empty value-support possibility remains harmless: a span slot with no coordinates can yield an empty, codimension-zero clause, but it changes neither the locus nor `mstar`.

13. **R6.D.1 — declared gaps remain honest and nonblocking.**

   The outstanding perimeter is unchanged:

   - existence of a genuine `JetSetup` for sufficiently large `N`;
   - identification of `htH` with the actual K1-chain coordinate heights;
   - identification of `TypObject.φ` with the graded-piece map;
   - provenance of the emitted `v` as the recorded pattern digit;
   - fine DIG level-set presentation;
   - evaluation/residue and final quotient identifications;
   - off-state stratum provenance;
   - endpoint attainability and the other existence-side graded-bridge obligations.

   These are openly hypotheses or deferred construction obligations. No new statement silently claims them. Recentring-center nonvanishing remains derivable from unit-valued `zbar` and the recorded center equality, so it is not a gap.

## Verdict: ACCEPT

The round-5 blocker is closed exactly. The 13 RETYPE/NEW units **GO TO PROVERS**.
