# UNIT CSX verdict — the exported context-split theorem (2026-08-28)

## Re-grounding

`runs/wave-c/verdict_CFS.md` landed the engine-application sweep (`C134cfs.lean`) but
recorded F1.2–F1.8 as BLOCKED-BECAUSE: `C133mh14.blockFrontier_of_context_of_theoremA`'s
proof (§8 steps 3-6) *constructs* the full context split `f = g₁ · g₂ · Wf` — `g₁` the
labelled pure block, `g₂` its complement with a non-`r`-divisible residual, `Wf` the
point-sided below/other-slope product — but the exported `BlockFrontier L f` keeps only
existence + maximality + the `D′` rider; the split data is dropped at the door. The
verdict named the exact fix: "a single ~60-line MH14 re-export node ('context split',
F1.H1 consumer form) unlocks F1.2 and re-opens F1.3-F1.8."

## What landed

New file `leanfinal/Uniformity/ChapC/C134csx.lean`, single import `C133mh9` (which
transitively pulls `C133mh14`, `C133mh10`, `C133mh4`, `C133mh13`, `C33Cite`, `C35`).
One theorem:

```
theorem context_split {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    ∃ g₂ Wf : Polynomial O,
      f = blockFactor L f * g₂ * Wf ∧
      g₂.Monic ∧ Wf.Monic ∧
      (∀ hneW : (dvSideSet F Wf L.u L.ℓ).Nonempty, dvSideDeg F Wf L.u L.ℓ hneW = 0) ∧
      ∀ (hne₂ : (dvSideSet F g₂ L.u L.ℓ).Nonempty) (M₂ : ℕ)
        (hp₂ : dvHgt F g₂ (dvSideMin F g₂ L.u L.ℓ hne₂) = (M₂ : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g₂ L.u L.ℓ hne₂ M₂ hp₂
```

This is exactly the F1.H1 consumer form the CFS verdict specified: `blockFactor` (C.35's
selector) is pinned as the pure factor, `g₂`'s residual is non-`r`-divisible at every
pin, `Wf` is point-sided at `(L.u, L.ℓ)`.

**Route taken: Route 1 (RE-DERIVE).** `C133mh14.residual_transport` and
`C133mh14.dvSideDeg_mul_prod_eq_zero` are already PUBLIC in `C133mh14` — consumed
directly, not re-derived. The proof replays MH14's §8 steps 1–6 verbatim (STEP 2 the
C.33 dissection cite; STEP 4 Theorem H0 = `C133mh10.dvResidualBezout` on the M-monic
residual `C133mh4.dvResPoly_monic_of_isDvPure`; STEP 5 the now-UNCONDITIONAL
`C133mh9.theoremA`, landed the same night MH14 was — so no `hA` carry is needed here
either), but instead of packaging the witness `g₁` into `BlockFrontier` and discarding
`(g₂, Wf)`, it identifies `g₁ = blockFactor L f` via `blockFactor_eq_of_frontier` (the
same identification `C134cfs.keyDeg₁_dvd_blockFactor_natDegree` uses) and returns
`(g₂, Wf)` with their clauses.

Five of MH14's Part-0 plumbing lemmas (`isKey_X`, `localFieldStageField`, `floor_assoc`,
`dvOnSide_of_mem'`, `exists_pin`) are `private` there and hence unreachable across
files; they are re-declared here byte-identical in mechanism, credited per declaration.
`C133mh14.lean` was never edited.

## Verification record

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134csx.lean
# exit 0, zero warnings, zero errors
```

AxCheck footer for `context_split`:
`[propext, Classical.choice, Quot.sound, Uniformity.Density.Tower.exists_dvDissection]`
— Lean core + exactly the one allowlisted C.33 cite, inherited once through
`C133mh14.residual_transport`'s dependency chain. Zero `sorry`; no landed file edited;
no new axiom.

## Consistency check (the mismatch the charge asked to guard against)

`blockFactor L f = g₁` is established via `blockFactor_eq_of_frontier L hlab hfd₁ hg₁dvd
hmax` — the identical selector-identification lemma `C134cfs.lean`'s
`keyDeg₁_dvd_blockFactor_natDegree` uses (`C35.lean:286`). No incompatible split: the
pure factor in `context_split`'s conclusion is definitionally C.35's `blockFactor`, not
an independent witness.

## What this unlocks (not landed here — out of CSX's scope)

Per `verdict_CFS.md`'s row table, `context_split` is the exact missing premise for:

* **F1.2 `block_complement_notdvd`**: still needs one more step downstream — the
  signed target is stated over `f /ₘ blockFactor L f` (the monic-division quotient),
  not an abstract `(g₂, Wf)` pair; a consumer combines `context_split` with
  `blockFactor_dvd` (`C134cfs.lean`) and monic-division exactness
  (`f /ₘ blockFactor L f = g₂ * Wf`) to read off the three clauses. Not attempted here
  — out of the CSX charge (one node only).
* **F1.3 `dv2Supp_translation`**: F1.2 + the no-interaction lemma
  `dv2Pin_mul_complement` (still to be written, plan sizing 70-120 lines).
* **F1.4–F1.8**: as recorded in `verdict_CFS.md`'s row table (unchanged by this unit).

## Status

Sorry-free. `C134csx.lean` is a pure addition; no landed file touched; no new axiom.
