# Verdict ANORM — A-C.21: the hnorm-family grade re-index, and the UNCONDITIONAL μ₃ GENTOW5W

**Date:** 2026-08-27
**Unit:** ANORM (Fable) — the amendment MSG2's refutation demanded
(`runs/wave-b/verdict_MSG2.md`; `C132sg2.s2Mu3_gentow5w_two_hnorm_refuted`).

## The print-read (the amendment's evidence, pinned before enacting)

* **Source grades are PRE-clearing.** GENTOW2_PROOF S5.2 defines `κ̄ := u₃/e(µ₂)`
  (ll.324–325, 711: "the top slot's grade") and `β_t := u₃(f₃−t)/e(µ₂)` (l.1546) — the
  B-1 line ll.740–744 grades the ladder normalizers `n̂₂(u₃)`/`n̂₂(u₃d)` at these
  Γ-valued RATIONALS.
* **The interface coordinate is full-current clearing** (MU3_CAMPAIGN §2's decision:
  `grade = e(μ₃)·β`; §2.2's identity `e(μᵢ)β = eᵢ·(e(μᵢ₋₁)β)`), so the honest integer
  grade of the `d`-th normalizer is `e(μ₃)·(d·u₃/e(μ₂)) = e₃·(d·u₃) = e'·(d·u')`.
  Machine: depth-2 grade `42 = 2·21` (`C132rp9` + `C132rp10b.s2Hgt₃_corr`); depth-1
  `10 = 2·5` vs printed `5`. **The expected correction `ExactGrade (e'·(d·u'))` is
  exactly what the evidence supports.**
* **The landed `C99r.gentow2_Bpp` proof audit** (the charge's consumer check): its `Rgr`
  reads sit at exactly the `hnorm` grades, and the power-law induction consumes `hprev`
  at the SECOND FACTOR's grade — so the conclusion grades AND the `hprev` grade re-index
  with `hnorm`: `hprev : PrevGrade (e'·u')`.  This is the source's own peel premise
  ("the split-off factor's grade, κ̄ resp. 0, **lies in Γ₂**", S5.2 l.748; Γ₂-membership
  = `e₃ ∣ cleared grade` by §2.2) — TRUE at `e'·u'`, healing the A-C.17 fence.

## Enacted — A-C.21 (`leanspec/Leanspec/ChapC.lean`, 7 hunks, dated comments each)

| site | change |
|---|---|
| `FGMNCalculus.thetaRatio` (def) | ratio read at `e'·(t·u')` |
| C.99 `gentow2_Bpp` | `hprev : PrevGrade (e'·u')`; `hnorm : ExactGrade (e'·(d·u'))`; conclusion `Rgr (e'·((f'-t)·u'))` / RHS base `Rgr (e'·u')` |
| C.99 `theta_letter_valued` | `hnorm` re-indexed (conclusion inherits via `thetaRatio`) |
| C.89 `GENTOW5W` (def) | carrier `Rgr` read at `e'·((f'-t)·u')` |
| C.89 `gentow5w_two` | `hprev`/`hnorm` re-indexed |
| C.89 `gentow5w_one_shape` | `hprev`/`hnorm`/conclusion re-indexed |
| C.90 `gentow5_key_certificate` | the `hres` display's `Rgr` read at `e'·((f'-t)·u')` (fifth family site, found by the consumer grep — its proof rewrites through the `𝒲` law) |

`hnormdeg`/`hnormz` carry no grade — unchanged.  `lake env lean Leanspec/ChapC.lean`
exit 0 (all in-file gates pass).  Cross-chapter grep: no other leanspec file references
the family.

## The two-name architecture (why leanfinal repairs are NEW declarations)

The do-not-edit refutation record `C132sg2.lean` passes the OLD-shape `hnorm` term to
`C107ac14.gentow5w_two` and states against the pre-A-C.21 `GENTOW5W`; any in-place
re-index breaks it.  So: pre-A-C.21 family RETAINED VERBATIM with dated supersession
comments (`C99r.gentow2_Bpp`, `C107gt5.GENTOW5W`/`Wle`, `C107ac14.gentow5w_two`/
`gentow5w_one_shape_of_letter_tie`/`gentow5_key_certificate`; two `wconj` helpers
de-privatized in C107ac14, statements byte-unchanged), and the A-C.21 twins land in the
NEW `leanfinal/Uniformity/ChapC/C132sg3.lean`.

**Charge deviation, evidence-forced:** "fire `s2Mu3_gentow5w_two_of_norm` with the
corrected hnorm" is a TYPE ERROR — that theorem's binder IS the refuted pre-A-C.21
shape.  Enacted instead: the same wiring rebuilt at the corrected signature
(`gentow5w_two_cleared` fed by the discharged supply), per the charge's
enact-what-the-evidence-supports clause.

## Landed — `C132sg3.lean` (sorry-free, no new axiom, first-attempt modulo one cast)

* Carriers: `FGMNCalculus.thetaRatioCleared`, `GENTOW5WCleared`, `WleCleared`.
* Abstract twins: `ratio_power_law_cleared` (engine; grade bookkeeping via
  `Nat.mul_left_comm`), `gentow2_Bpp_cleared` (C.99), `gentow5w_two_cleared` (C.89 i=2),
  `gentow5w_one_shape_of_letter_tie_cleared` (C.89 i=1; OPEN-LETTERS tie still carried —
  untouched by this amendment), `gentow5_key_certificate_cleared` (C.90(a)).
* `s2Mu3_B1_exact_grade_supply_cleared` — **A-C.21's hnorm DISCHARGED at the μ₃ point**
  (`d ∈ {1}` at `f' = 1`): rp9's identification `chainNormBelow 2 21 = 2⁴Φ′` + rp10b's
  `s2Hgt₃_corr = 42` through the sg2 `rfl` grade pin.
* ★★★ `s2Mu3_gentow5w_two : GENTOW5WCleared (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus
  h2 hq)` — **the signed GENTOW5W at (2,1,21), UNCONDITIONAL** (every leg discharged;
  `hprev` vacuous at `f' = 1`; floor `20 < 21` machine).  Campaign exit gate 4 CLOSED.
* ★★ `s2Mu3_gentow5w_old_refuted : ¬ GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus
  h2 hq)` — the pre-A-C.21 carrier is FALSE at the honest instance (grade 21 < honest 42
  ⇒ `Rgr_zero_of_above` ⇒ witness forced to 0): the definitional-level justification.

## AxChk footer (`lake env lean Uniformity/ChapC/C132sg3.lean`, exit 0)

Every declaration Lean-core — `[propext, Classical.choice, Quot.sound]`:

```text
thetaRatioCleared · GENTOW5WCleared · WleCleared · ratio_power_law_cleared ·
gentow2_Bpp_cleared · gentow5w_two_cleared · gentow5w_one_shape_of_letter_tie_cleared ·
gentow5_key_certificate_cleared · s2Mu3_B1_exact_grade_supply_cleared ·
s2Mu3_gentow5w_two · s2Mu3_gentow5w_old_refuted
```

**Cite note:** NO footprint carries a declared cite (`fgmn_dv_exact_mul` remains on the
untouched dv-engine chain only).

## Builds run

* `lake env lean Leanspec/ChapC.lean` — exit 0 (post-amendment).
* `lake build Uniformity.ChapC.C132sg2` — green, 8817 jobs (re-elaborates the three
  touched consumer files; the do-not-edit `C132sg2.lean` still green against the
  retained signatures, footprints unchanged Lean-core).
* `lake env lean Uniformity/ChapC/C132sg3.lean` — exit 0, footprints above.
* `lake build Uniformity.ChapC.C132sg3` — green (fresh oleans).

## Flagged, NOT enacted (follow-up amendment)

C.100 `gentow2_Bp`/`gentow2_Bp_unit_iff` pair a CLEARED grade `β` with the
pre-clearing-indexed normalizer `chainNormBelow 2 β`, and C.101 `gentow2_B`'s
`hlift`/`hunit` grade the recipe lifts at `(f'-t)·u'` — the same defect genre.  Both are
HELD on OPEN-EVAL-ISO with explicitly carried discharge hypotheses (not on the μ₃ star
path), so the re-index there belongs to the eval-iso follow-up, coordinately with the
`Rres_recipe` CLASS FIELD's `khat` grades (a class change — out of unit scope).  Recorded
in the A-C.21 review row.

## Not done (orchestrator scope)

No commit (per charge).  Roll-ups untouched (`C132sg3` unwired — wiring is the
orchestrator's, as with sg2).  PROJECT_STATE/frontier update left to the milestone pass.
