1. **R5.A.1 — STRIP support shape: faithful.**

   The branch

   > `cl.support = {c} ∧ cl.codim = 1 ∧ (∀ x, (cl.sat x ↔ x c = 0))`

   exactly represents one base-coordinate zero equation. The additional

   > `¬ IsValueCoord ... c`

   correctly prevents a strip-labelled clause from occupying a geometrically identified value coordinate.

2. **R5.A.2 — `IsValueCoord` slot arithmetic: faithful.**

   The definition uses

   > `ν.fineSlot b := b / ν.Dwidth`

   and

   > `ν.slotVal j := ν.line.at (j * ν.Dwidth)`.

   This matches C.1.0(a): frame-`i` coefficient slot `j` occupies the base block beginning at `j·D_i`, with `D_i = ν.Dwidth`. The height equality

   > `H.htH i (...) = ν.slotVal (...)`

   is in the same absolute scale as both operands. No off-by-one or stretch-factor error occurs here.

3. **R5.A.3 — `IsValueSupport`: faithful for nonempty value supports.**

   The law

   > `∀ c, c ∈ S ↔ (ν.fineSlot (...) = j ∧ H.htH i (...) = ν.slotVal j)`

   pins both directions of the complete level set of one slot. It excludes:

   - partial level sets;
   - unions or cross-block regroupings;
   - off-span slots;
   - clauses at a non-recorded valuation;
   - arbitrary constant-height supports spanning several slots.

4. **R5.A.4 — strip/value overlap: excluded.**

   Membership in a legal value support implies `IsValueCoord` for the same coordinate. The strip branch requires its negation, while `FreshData.disj` prevents distinct nonempty clauses from sharing support coordinates. Thus a coordinate cannot legally carry overlapping strip and value clauses.

5. **R5.A.5 — singleton value levels: geometry is fixed, predicate provenance is not.**

   If the complete level set has cardinality one, `{c}` is correctly forced into the VALUE branch. Nevertheless, choosing a suitable `T` and `v = 0` can make its predicate extensionally identical to `x c = 0`.

   This does not revive the support/species permutation loophole: the clause remains species-correct. It does show that the blueprint’s statement that impersonation “dies at every branch” is too strong at the locus level. Distinguishing the actual value clause from this zero fiber still depends on the openly declared piece-map and emitted-`v` provenance gap.

6. **R5.A.6 — empty phantom value clauses remain legal, but harmless.**

   `IsValueSupport` permits `S = ∅` whenever a recorded span-slot valuation has no coordinate in the finite box. Such a clause has codimension zero and is vacuous; duplicate empty clauses also satisfy disjointness. This is not an exact inventory of actual clauses, but it changes neither locus nor mass. It belongs with finite-cutoff/attainability provenance rather than constituting the round-4 impersonation.

7. **R5.A.7 — BLOCKER: the fresh-band upper boundary uses the wrong block width.**

   `inFreshBand` still uses

   > `H.htH i (...) ≤ ν.lineStep (...)`

   while `Node.lineStep` is

   > `ν.line.at (((b / ν.childWidth) * ν.childWidth))`.

   But fresh clauses are frame-`i` slot clauses, whose correct upper line at base index `b` is determined by the fine slot:

   > `ν.line.at ((b / ν.Dwidth) * ν.Dwidth)`

   equivalently `ν.slotVal (ν.fineSlot b)`.

   Since

   > `ν.childWidth = ν.e * ν.g * ν.Dwidth`,

   an increment with `e·g > 1` groups several fine slots under one coarse left-edge line value. Because the line descends, later fine slots in that coarse block satisfy

   `lineStep(b) > slotVal(fineSlot b)`.

   Consequently, any available coordinate with height strictly between those values is admitted into `inFreshBand`, classified as a non-value coordinate, and forced into a zero STRIP clause. Rev 14 leaves coordinates above that fine slot’s valuation unconstrained. This can shrink the locus and inflate `mstar`.

   The comments correctly describe `lineStep` as the post-landing `(ZC-a)` staircase convention, but the code also uses it as the pre-landing fresh-inventory boundary. Those are different granularities.

8. **R5.B.1 — round-4 partition impersonation: closed only on the band actually encoded.**

   Given the current `inFreshBand`, the new laws do prevent replacing an encoded nonempty value level set by arbitrary singleton strip clauses. However, finding 7 means the encoded band itself is too large in general. The interface can therefore still force non-geometric singleton zeros, now above the true fine-slot line rather than directly on a value level set.

9. **R5.C.1 — root treatment: faithful; no missing root clause species.**

   Rev 14 explicitly defines

   > `E_fresh(ν₀) := E(ν₀)`

   with `E(ν₀)` consisting of cluster zeros plus the root side pattern. The root side-pattern values are therefore ordinary fine-slot value digits. `(VERTEX)+(TRANSPORT)` are the post-landing `Λ(ν₀)`/`DIG₀` representation, not additional fresh-clause species. No root-specific value-support constructor is required.

   The coarse/fine defect in finding 7 can affect the root as well, but it does not invalidate the no-root-special-case interpretation itself.

10. **R5.D.1 — declared graded provenance: genuine gap.**

    The missing identification of `T.φ` and `v` with the actual graded piece map and recorded pattern digit is openly deferred. Conditional counting from a supplied `TypObject` remains sound. This is a gap, not a silently weakened proof—though it explains the singleton behavior in finding 5.

11. **R5.D.2 — remaining previously listed perimeter items: gaps, not new weakenings.**

    Setup existence for sufficiently large `N`, fine DIG level-set presentation, evaluation/residue identification, final quotient identification, off-state stratum provenance, and endpoint attainability remain explicitly outside the vocabulary theorem interface. Nothing in round 5 falsely proves them.

12. **R5.D.3 — recentering-center nonvanishing remains derivable.**

    As in round 4, the unit-valued `zbar` and the recorded center equality force the center to be nonzero. It is not a substantive remaining gap.

13. **R5.C.2 — fresh 938-line sweep result: one semantic regression/blocker.**

    Apart from the harmless empty-support issue and already declared provenance boundaries, the new support predicates compose coherently with `fresh_band`, `fresh_cover`, disjointness, and per-clause codimension. The material regression is precisely the fine/coarse mismatch in finding 7.

**Verdict: REJECT.**

Blocking list:

1. `inFreshBand` uses the coarse post-landing `childWidth` staircase as the fresh-clause upper boundary.
2. For `e·g > 1`, this admits coordinates above their true fine-slot valuation and forces spurious zero strips.
3. Therefore the round-5 laws still permit a locus and `mstar` different from rev 14’s actual C.1 species inventory, even though the value-support partition loophole itself is substantially closed.
