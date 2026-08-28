# UNIT A24E verdict — A-C.24′ ENACTED per A24B's delivered draft (2026-08-28)

**Charge:** enact amendment A-C.24′ in `leanspec/Leanspec/ChapC.lean` per
`runs/wave-c/verdict_A24B.md` §4 (the C.38a′ carrier insertion + the C.38/C.39 re-signs +
the dated numbered record), after re-verifying the zero-consumer claim; gate by
re-elaboration; REVIEW_QUEUE Tier 2 row; adjudicate whether the re-signed C.39 is now
provable (checking `verdict_L2E4.md`).

## STATUS FIRST

| charge item | status | result |
|---|---|---|
| 1. enact per draft | **DONE** | `leanspec/Leanspec/ChapC.lean`: NODE C.38a′ inserted (`dv2FullReadPoly`, `dv2FullRead`, `dv2ResPolyAnch` — draft §4.1 verbatim); C.38 re-signed `dv2ResPoly_radical_eq → dv2ResPolyAnch_radical_eq` (§4.2 verbatim); C.39 re-signed `dv2ResPoly_scalar → dv2ResPolyAnch_scalar` with `γgAnch` (§4.3 verbatim + the archive-commit sentence, the 135/135 counts, and the L2E4 adjudication note added to the record). Consumer claim RE-VERIFIED before touching bytes (§2). Bare `dv2ResPoly`/`dv2Res`/`γg`/`pinHeight` and C.104's `repoRead` byte-untouched. |
| 2. gates | **PASS** | `cd leanspec && timeout 580 ~/.elan/bin/lake env lean Leanspec/ChapC.lean` → **EXIT 0** (sole warning: the pre-existing `sideCensus` overlapping-instances lint, present in A24A's pre-amendment gate log at line 2817, shifted to 2902 by the insertion). `git diff` confirms the only declaration-level changes are the 4 new defs + the 2 axiom replacements + 2 re-signed headers — conclusions elsewhere byte-unchanged. Leanfinal carrier gate re-run per draft checklist: `lake env lean Uniformity/ChapC/C136f14b.lean` exit 0. |
| 3. REVIEW_QUEUE | **DONE** | Tier 2 row A-C.24′ prepended (newest-first), carrying A24B §3's three trust-boundary statement flags: `dv2ResPolyAnch`, `dv2FullReadPoly_eq_shift`, `dv2FullRead_modByMonic`. |
| 4. is re-signed C.39 provable? | **NO — honest remainder recorded** | `verdict_L2E4.md` EXISTS but supplies NEITHER missing piece: its generic `hconv` row is RED (the bare unweighted convolution is unsuppliable — `fixedGrade_unweighted_add_forces_letter_one`; only the S2-specific D3-10 mirror landed), and the carry law `Dv2FullReadCarryLawStatement` remains a recorded `def`. So the digit-split convolution assembly (now known to need the anchored/WEIGHTED form) + the carry law are both still open; **no `C136f14c.lean` created; the F1.4/F1.5 rows stay open** — recorded in the C.39 record comment and the REVIEW_QUEUE row. |

## 1. What was enacted (the three hunks)

### 1.1 NODE C.38a′ (INSERTED after the `dv2ResPoly` def, before the C.38 header)

Draft §4.1 byte-faithful: `dv2FullReadPoly` (transcription of `C136l2e0.dv2FullReadPoly`
— verified against the leanfinal source, bodies identical modulo the explicit
`{F : KeyFrame O π} {H₀ hpin}` binders replacing section variables), `dv2FullRead`
(`AdjoinRoot.mk L.r` of it), and `dv2ResPolyAnch` (the guarded/anchored classical R₂:
coefficient `t` = `dv2FullRead L (M₂ − t·u₂) (dev Ψ f (min₂ + t·ℓ₂))`, GC-1 pin binders
`(M₂, hp₂)`). Vocabulary pre-checked in leanspec: `LevelDatum.shift` (:897),
`LevelDatum.cocycle` (:901), `KeyFrame.twistRead` (:654), `KeyFrame.stageField` (:409),
`dv2Pin` (:533); no name clashes (`dv2FullRead*`, `dv2ResPolyAnch`, `γgAnch` absent from
all of `leanspec/Leanspec/`).

### 1.2 C.38 re-sign — before/after diff

Hypotheses (old → new):

```text
  (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)          [old]
  (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)                   [new: hcop ADDED]
  (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)                          [A-C.22 floor RETAINED]
  … (hne) (hne') unchanged …
  {M₂ M₂' : ℕ}                                                 [new: ADDED]
  (hp₂  : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))         [new: ADDED]
  (hp₂' : dv2Pin L Ψ (blockFactor L f)
      (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞))        [new: ADDED]
```

Conclusion: shape UNCHANGED (natDegree equality ∧ ∀ monic-irreducible divisor iff),
carrier repaired:

```text
old: (dv2ResPoly L Ψ f u₂ ℓ₂ hne).natDegree = (dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne').natDegree ∧
     ∀ q …, (q ∣ dv2ResPoly L Ψ f u₂ ℓ₂ hne ↔ q ∣ dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')
new: (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
         = (dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂').natDegree ∧
     ∀ q …, (q ∣ dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂
         ↔ q ∣ dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂')
```

### 1.3 C.39 re-sign — before/after diff

`γg`/`pinHeight` defs RETAINED byte-unchanged (γg is the record + the on-side
dictionary's right-hand side; pinHeight is consumed by the new row). NEW def `γgAnch L f
:= dv2FullRead L (complementConst L f) (f /ₘ blockFactor L f)` — the pin-anchored
normalization of PE3 F-1's `γ_g`. Hypothesis diff identical to C.38's (hcop + pin binders
added, floor retained). Conclusion — the SOURCE-FAITHFUL scalar, byte-unchanged except
`dv2ResPoly ↦ dv2ResPolyAnch` and `γg ↦ γgAnch`:

```text
old: dv2ResPoly L Ψ f u₂ ℓ₂ hne
       = C (γg L f * root^(L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f)))
           * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne'
new: dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂
       = C (γgAnch L f * root^(L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f)))
           * dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂'
```

The scalar's root-power exponent `L.cocycle (pinHeight …) (complementConst …)` is
byte-identical to the signed A-C.1 form — over the anchored carrier it is the faithful
transcription of EFF.HE6R1.39's `β^{c₁(m₁^{f_S}, c_g)}` (A24A §1: the source's
normalizers ARE pin-anchored).

### 1.4 The record (at C.39, dated 2026-08-28, archive commit `dea24337`)

Quotes both refutation channels verbatim from the draft — (1) root-power
(`C136l2e1.dv2Res_mul` clean ⇒ signed factor forces `root^cocycle = 1`, unsuppliable);
(2) off-side junk (`C136f14.dv2ResPoly_scalar_shape_digit_kill`, live block×block
battery instances) — plus the battery: 120 generic + 15 F1.4-territory μ-value ties =
**135/135 anchor shifts (δ = 1, injection genre), all absorbed by the anchored read
(0 violations)**, absorber now the theorem `C136f14b.dv2FullRead_modByMonic`. Additions
beyond the draft text (all record-preserving, none semantic): the archive-commit
sentence (A-C.23 precedent), the explicit 135/135 counts, the A-C.22 pointer comments
retained on both rows (the engine-honest floor survives into the new rows), and one
sentence in the proof-target inventory recording L2E4's adjudication (bare unweighted
convolution unsuppliable ⇒ the remaining assembly must be the anchored/weighted form).

## 2. The consumer re-verification (STOP-gate, run BEFORE editing)

`rg -n "dv2ResPoly_radical_eq|dv2ResPoly_scalar" -g '*.lean'` over the whole repo:
the only non-comment hits were the two leanspec axiom declarations themselves
(ChapC.lean:1707, :1734) and one leanspec docstring list (:957). All leanfinal hits are
comments/docstrings in blocked-record files (C134f12c, C134frt, C134cfs, C134f13a,
C136f14, C136f14b, C38a) plus the DISTINCT declaration
`C136l2e3.dv2ResPoly_radical_eq_of_scalar`, which takes the scalar identity as an
explicit premise and never references the axiom (and leanfinal does not import leanspec).
**Zero term-level consumers — A24B's pre-verification confirmed; no STOP.**

## 3. Verification

```text
cd leanspec && timeout 580 ~/.elan/bin/lake env lean Leanspec/ChapC.lean
EXIT: 0   (sole warning: pre-existing sideCensus overlapping-instances lint)

cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14b.lean
EXIT: 0   (leanfinal untouched by this unit; re-run per draft checklist item 2)
```

First-attempt green; zero repairs. `git diff --stat`: `leanspec/Leanspec/ChapC.lean`
+102/−17 — the three hunks only.

## 4. Flagged for human review (carried from A24B §3, now in REVIEW_QUEUE Tier 2)

New statement shapes at the trust boundary: `dv2ResPolyAnch` (the carrier definition),
`dv2FullReadPoly_eq_shift`, `dv2FullRead_modByMonic` (proofs Lean-core, machine-checked
in `C136f14b.lean`; the leanspec twins are defs/axioms whose faithfulness rests on the
A24A source-chain reading).

## 5. Honest remainder (charge item 4)

The re-signed `dv2ResPolyAnch_scalar` is an axiom, not a theorem. Missing supplier legs
(A24B §2 fence, re-checked against `verdict_L2E4.md` this unit):
(i) the digit-split convolution assembly — L2E4 adjudicated the bare unweighted form
unsuppliable (`fixedGrade_unweighted_add_forces_letter_one`), so this leg must be built
in the anchored/weighted form (the landed `dv2FullReadPoly_eq_shift` supplies the
per-term weights); (ii) the carry law (`C136l2e2.Dv2FullReadCarryLawStatement`, a `def`
with no inhabiting theorem; battery-certified 8128/8128 at S2). The F1.4/F1.5 rows stay
open pending those two pieces. No `C136f14c.lean` created.

## 6. File inventory

* `leanspec/Leanspec/ChapC.lean` — EDITED (the three hunks; the only Lean file changed).
* `docs/REVIEW_QUEUE_2026-08-26.md` — Tier 2 row A-C.24′ prepended.
* `runs/wave-c/verdict_A24E.md` — this record.
* No leanfinal edit, no git operation, no blueprint edit.
