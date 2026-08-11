# GENTOW5-W(i) passPE2 — hostile acceptance attempt (report in progress)

Target: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md` at HEAD
(note chain 07fa3676 → 4c959409 → ec30256c; PE1 CLEAN 0C/0G/4m at
884edd2c). This pass verifies the COMPOSITION (the four steps as one
argument), re-derives the S11.2 resting point (PE1 MINOR-2), checks
the consumers-to-be (the S11.2 fence, WFRAME OPEN-1, T1 r1), re-runs
the machine leg, and drives a fresh route disjoint from LW3/FR4.

## VERDICT: PENDING (sections A–C below are final; D–F follow)

- S-A composition: DONE — no finding at GAP-or-worse
- S-B resting point (S11.2 adjudication re-derivation): DONE — holds
- S-C consumers: DONE — all three interfaces supply-match
- S-D machine: IN PROGRESS
- S-E fresh route (e_{i+1} ≥ 2 at i ≥ 3 — the untested axis): PENDING
- S-F findings + grade line: PENDING

Byte-freeze spot-check: `git diff b0e5c648 HEAD` over GENTOW5_PROOF
and GENTOW2_PROOF is EMPTY — the pinned line numbers used below read
identically at HEAD.

---

## S-A. THE COMPOSITION (the four steps as one argument)

PE1 walked each step; this pass verified the INTERFACES and the
quantifier structure. All checks re-derived from the notes' own
lemmas, at the pinned sources.

1. **(0)→(i) interface.** Step (0) delivers μ_{i+1}(G) = d·κ̄_i =
   β_t EXACT; step (i)'s iterated Cor 4.7(2) peel needs each factor
   N at exact grade κ̄_i and the product landing at grade β_t —
   supplied. R_{i+1,β_t}(G) is then the graded piece at the grade
   the expansion (ii) minimizes at. Consistent.
2. **(ii)/(iii)/(iv)→equate interface.** The equate takes y-degree-0
   parts of Cor 4.7(1)'s sum. Each j ≥ 1 term individually has zero
   y-degree-0 component ((iii): dies by Lemma 3.17, or sits at
   y-degree j/e_{i+1} ≥ 1, or at y-degree j ≥ 1 when e_{i+1} = 1) —
   so no cross-term cancellation issue can arise: the equate needs
   only per-term vanishing at y-degree 0, which is what (iii)
   proves. The j = 0 term is y-degree-0 by Cor 4.4(3). Sound.
3. **Quantifier over i.** The proof is per-level (fix i, 3 ≤ i < r;
   fix t): NO induction on i inside S2. The inductive objects
   consumed (GENTOW5-C's (SLOT_{i-1}) recursion) carry their own
   induction in the accepted record, and GENTOW5-C's proof consumes
   exactly four clauses — (SLOT_{i-1}), the P-membership clause,
   gcd(u_{i+1}, e_{i+1}) = 1, the basis clause (@ b0e5c648
   L580–588, read at source) — none of which is [GENTOW5-W(j)] at
   any j. No hidden circular induction.
4. **Hypothesis supply (the composition-level check PE1 did not
   run).** The lemma's ambient assumes P_{i+1} nonempty. Its
   consumers (the fence's clause-(a) discharge at level i) can
   supply this NON-circularly: Thm GENTOW5-B clause (b) at index i
   proves Φ_{i+1}-roots ∈ P_{i+1}, and the exact-value + P-locus
   clause is on the fence's NOT-conditional (w-blind) list
   (@ b0e5c648 L1925–1928 and the [GT5-r2 rider] at L825–833:
   "The exact-value clause and the P_{i+1} clause are w-blind ...
   a psi^{(w)}-root FGMN-side IS a psi-root repo-side"). So
   P_{i+1} ≠ ∅ never routes through [GENTOW5-W(i)] itself.
5. **Factorization self-consistency.** The u_i-family display
   applied to g = n̂_i(β̂) itself gives R = u_i(β)·digit(n̂) =
   u_i(β)·1 — the definitional display; consumed at exactly one
   other g (= Q_0) inside its stated scope (Φ_i-free, exact grade,
   deg < D_i). The peel step uses only the DEFINITIONAL identity
   u_i(κ̄) = R_{i+1,κ̄}(N) = w_i, not the fenced law. No self-use.

**S-A verdict: the composition holds; nothing at GAP-or-worse.**

## S-B. THE S11.2 RESTING POINT (re-derivation of PE1's MINOR-2)

Re-derived independently at source (b0e5c648):

* The fence's "What IS proved" block (L1897–1908) places on the
  PROVED side at i ≥ 3: per-grade FIXEDNESS of u_i(β) — credited
  to "S2.3 step (3)'s tau_i-cocycle letter computation"; x0- and
  g-freeness — credited to "the (SLOT_i) value clause"; and the
  reciprocity θ_i(t) = ϑ_{i,f_{i+1}−t}^{−1}. It withholds ONLY the
  single-w form. The note's C-2 consumption is exactly the proved
  triple + the factorization it constitutes, never the single-w
  display — confirmed against S2's use sites ((i) definitional,
  (iv) factorization at Q_0).
* GENTOW5-C's proof (L580–601) consumes the four clauses listed in
  S-A.3 plus the ANNEX R argument (accepted 2/2 per the dated fold
  in its grade-honesty box). Thm 4.8 and T(b)'(iii) appear in
  NEITHER GENTOW5-C's four-clause table NOR the fence's i ≥ 3
  credit line. So the elimination claim's resting point is: the
  W-note's own steps consume no Thm 4.8; the consumed C-2 content
  rests on GENTOW5-C + the S2.3 cocycle at i ≥ 3 (fence's own
  adjudication); the i = 2 ancestor B′(3) DOES consume Thm 4.8,
  but i = 2 is outside the lemma's binder and C-1 is consumed as
  proof-shape only. PE1's MINOR-2 restated the resting point
  correctly; it holds at source. Not a gap.

## S-C. CONSUMERS-TO-BE (supply/consume interface checks)

1. **GENTOW5's S11.2 fence.** The fenced display (L1912–1913) and
   the note's S1 statement: equation bodies byte-identical (PE1
   surface 3; re-spot-checked). The fence's conditional list
   (clause (a)'s ψ_{i+1}^{(w_i)} display, the (a)-certificate legs,
   (b)'s FGMN-side residual displays at i ≥ 3) consumes the display
   at slot grades of the SAME datum; the note's S4 discharge
   display re-runs the S3(a) algebra (L941–954: the ϑ twist cancels
   the θ leg, the w-leg survives, R_{ν_i}(Φ_{i+1}) = ψ_{i+1}^{(w_i)})
   — verified against the source algebra, which uses only the
   lemma + reciprocity (C-4). Supply matches consumption; ambient
   hypotheses (datum, P_{i+1} ≠ ∅) available w-blind (S-A.4).
2. **WFRAME OPEN-1.** WFRAME_NOTE §5 OPEN-1 pins "statement and
   status exactly as GENTOW5 S11.2 (span pin @ b0e5c648
   L1888–1933)" with the same conditional/not-conditional split,
   and its §3 ladder displays the identical two-line form. The
   note supplies that statement verbatim at i ≥ 3; WFRAME's
   accepted-corpus rule keeps its fence up until 2/2 — the as-of
   annotation (r1, PE1 F-3) already anticipates exactly this
   acceptance event. Interface exact.
3. **T1 r1.** T1_GAUGE_COCYCLE pins the carrier unit w_i :=
   R_{i+1,κ̄_i}(n̂_i(u_{i+1})) (§(10)) — byte-consistent with the
   note's second display line — and its consumption row "A7 GENTOW2
   S5.2 B-law | C3 | u(β_t) = Θ_i(t)w_i^{f−t}" with Θ_i(t) =
   ϑ_{i,f−t}^{−1} — the note's display + its C-4 reciprocity,
   same orientation. T1's internal derivation (its L732–771)
   parallels the note's S2 but T1 is grade 1/2 and is NOT consumed
   by the note (no circularity; the note cites WFRAME as geography
   only, and T1 not at all — grep-confirmed in PE1).

**S-C verdict: all three consumers get exactly the statement they
consume; nothing at GAP-or-worse.**

---

(S-D machine, S-E fresh route, S-F findings follow.)
