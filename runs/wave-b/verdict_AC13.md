# Verdict — unit AC13: amendment A-C.13 ENACTED (restore the Cor 4.12(2) source restriction)

Date: 2026-08-25 · Authority: U14 `docs/in-progress/COR412_ADJUDICATION_2026-08-25.md`
(print-read: published Cor 4.12(2) requires `β ∈ Γ_{r−1}`, proof uses `s_r(β) = 0` verbatim;
plain law at arbitrary grades machine-refuted by RP23's tooth), correcting U9 Q3
(`FGMN_ADJUDICATION_2026-08-24.md` §5: removal wrong at the graded level — the premise is
dischargeable at the GENTOW2 consumer clearing but must be PRESENT in the abstract carrier).
Files touched (exactly the authorized five; every edit dated `[A-C.13]`; NOT committed):

## Per-file diffs

1. **`leanfinal/Uniformity/ChapC/C130fg.lean`** (CC-13). `FGMNSourceData` gains the field
   `PrevGrade : ℕ → Prop` (U14 §8.1's predicate form — realization obligation: preceding-group
   membership; under full-current-group clearing `e' ∣ β`, at S2 evenness; predicate kept
   until OPEN-DICT-2 proves the divisibility test). `FGMNSourceLaws.graded_mul` regains the
   premise `S.PrevGrade β' →` (U14's exact diff position, after the two `ExactGrade`
   binders). `normalized_mul` UNCHANGED (Cor 4.12(3), U14 §7). Module-docstring dictionary
   updated with the correction record.
2. **`leanspec/Leanspec/ChapC.lean`** (the A-C.11 class, NODE C.92). `FGMNCalculus` gains
   `PrevGrade : ℕ → Prop` (after `AboveGrade`); `Rgr_mul` regains `PrevGrade β' →` (U14 §6:
   the scalar law fails under odd-odd carry — coeff₀(X·P·Q) = 0 vs 1). Class docstring's
   A-C.11 note gains the [A-C.13] correction paragraph. CONSUMER RE-SIGN in the same file:
   the `gentow2_Bpp` axiom gains the supply hypothesis `(hprev : I.PrevGrade u')` (see §
   consumer repair below).
3. **`leanfinal/Uniformity/ChapC/C130pk.lean`** (CC-16 twin). Class mirrored byte-parallel
   (field + premise + comments); `ChainRealization.toCalculus` fills
   `PrevGrade := A.fgmn.PrevGrade`; new `rfl` anti-drift tooth
   `A.toCalculus.PrevGrade = A.fgmn.PrevGrade`; design-§7 table row added.
4. **`leanfinal/Uniformity/ChapC/C130la.lean`** (CC-14). `exactGrade_mul`, `Rgr_mul`,
   `Rgr_mul_eq` carry the restored `S.PrevGrade β'` premise (scalar projection follows from
   the restored polynomial law, proofs otherwise unchanged). `Rgr_pow` RESTRICTED by
   `S.PrevGrade β` per U14 §8.3 (each induction step multiplies by a grade-`β` factor).
   Regression teeth (i).3/(i).6 updated to the restored shapes.
5. **`leanfinal/Uniformity/ChapC/C99r.lean`** (GTR landing, NODE C.99). `gentow2_Bpp` gains
   `(hprev : I.PrevGrade u')` byte-parallel with the amended leanspec axiom; the power-law
   induction passes `hprev` to `I.Rgr_mul` at its second grade `u'`.

## Consumer-repair list (and the one judgment call)

Build-reachable consumers of the restored law: C130la's four scalar theorems + teeth
(repaired, premise carried), C130pk's `toCalculus` (pass-through), C99r's `gentow2_Bpp`
(the ONLY term-level `Rgr_mul` consumer; repaired via `hprev`). Pass-through sites needing
NO edit: C130s17 (`S2SourceFrontier`/`toChainRealization` carry `fgmn`/`fgmnLaws` whole),
C130s18 (`twistRealization` ditto), C130in/C130vw (hypothesis-position only), C130lb (laws B
only). Not in any build target: scratch (`GSW_check.lean`'s certificate predates the premise
— superseded note recorded in the leanspec comment), C130rp0/rp1/rp2/np6 (shape pins only —
verified compiling). **Judgment call, recorded:** the mandate's "discharge it, don't weaken"
cannot mean abstract discharge at `gentow2_Bpp` — `Nat.Coprime u' e'` puts `u'` OUTSIDE the
preceding group under the full-current-group clearing (U14 §6: "cannot discharge that premise
at the S2 u' = 5 step"), so no proof from the other binders exists. Enacted as the A-C.12
supply pattern instead: `hprev` is an explicit hypothesis, trivially dischargeable at the
intended GENTOW2 instance because U9 §5's consumer clearing `β̂ = e(μ₂)β` puts every
ℕ-cleared grade in the preceding group. Law NOT weakened; conclusion unchanged.

## Build results

- `leanfinal`: `lake build Uniformity.ChapC` — SUCCESS (8803 jobs); per-module
  `lake env lean` / `lake build` on C130fg, C130la, C130pk, C99r all clean, every
  `#print axioms` row `[propext, Classical.choice, Quot.sound]` (Lean-core only).
- Refuting tooth: `lake build Uniformity.ChapC.C130rp2` — SUCCESS (8742 jobs) with the file
  byte-UNCHANGED: `tooth_graded_mul_plain_shape_refuted` is a local statement on the RP-1
  operator `s2GradedRes` (C130fg's field appears only in its docstring), so no historical
  pinning was needed; it now refutes what the docstrings describe — the pre-A-C.13 plain
  shape — and coexists with the restored restricted field.
- `leanspec`: `lake build Leanspec.ChapC` — SUCCESS (9276 jobs).
- Honesty: 0 `sorry` (all grep hits are pre-existing "sorry-free" docstring phrases), 0 new
  `axiom` (leanspec diff has no `axiom`-line additions/removals), no statement weakened
  beyond the recorded amendment, no other file touched (spec/*.md modifications in
  `git status` pre-date this unit). No git commit (per brief).
