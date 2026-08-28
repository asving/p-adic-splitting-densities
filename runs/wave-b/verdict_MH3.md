# Verdict — MH3: Theorem M assembled (clauses 1–3) + the cite derivation [IN PROGRESS]

**Date:** 2026-08-27/28
**Unit:** MH3 (Fable tier)
**Charge:** transcribe Theorem M's mixed product law (`R(gz) = R(g)·R(z)`, τ = 1, all
nonzero `g, z`) per `docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §§2–3 ([MHFIX] state),
node MH.3 (§9); payoff: derive the declared cite `fgmn_dv_exact_mul`'s statement (§9.2).

## Landed: `leanfinal/Uniformity/ChapC/C133mh3.lean` (~1040 lines, compiles clean)

`lake env lean Uniformity/ChapC/C133mh3.lean` — exit 0, ZERO errors/warnings/`sorry`,
zero new axiom, every footprint exactly `[propext, Classical.choice, Quot.sound]`.

### Ground truth found on arrival (differs from the charge's premise)

The charge said MH.1's slot form is "landed" in C133mh1.  In fact `C133mh1.lean` landed
TW-δ + the carry⟹twist bridge as PROVED theorems but the three M1′ clauses only as
STATEMENT SHAPES (`verdict_MH1.md` "Explicitly out of scope: the full M1′ proof");
MH.2 has no landed file.  PROJECT_STATE's "MH.1 transcribed" is shapes-only.

### What this unit proved

* **`m1DigitFaithful : M1DigitFaithfulStatement O` — PROVED UNCONDITIONALLY.**
  M1′ clause (3) (digit read faithfulness) discharged from the landed C.23
  `slotRes_ne_zero` + the C.22 twist.  One of MH.1's three clauses is now CLOSED.
* **Theorem M, all three clauses, PROVED conditional on ONE pinned hypothesis**
  `h1 : C133mh1.M1TwistProductLawStatement O` (M1′ clause (1), the twist-form digit
  product law — MATH-PROVED in the doc §3.1′, the single remaining Lean-open piece):
  - `dvSupp_mul_of_twistLaw` (clause 1, `W(gz) = W(g)+W(z)`);
  - `dvSideMin_mul_of_twistLaw`, `dvSideMax_mul_of_twistLaw`, `dvSideDeg_mul_of_twistLaw`,
    `dvHgt_dvSideMin_mul_of_twistLaw` (clause 2 + the pin law; the sideMax half — the
    doc's PROOF-OUTLINE-grade piece, node MH.2 — is here fully Lean-proved via the
    `(jmax, jmax)`-pair survival + strict convolution pricing);
  - `dvResPoly_mul_gen_of_twistLaw` (★ clause 3, τ = 1, ALL nonzero `g, z` — §3.3's
    coefficientwise assembly on `dev_mul_conv_split` + the rp2/rp4 read stack + `h1`);
  - packaged: `MixedResidualLawTauOneStatement` (probe-verbatim shape, declared here per
    the MH.1 verdict's scoping) + `mixedResidualLaw_of_twistLaw` +
    `existsUnit_of_tauOne` (the ∃-τ weakening, probe-verbatim).
* **The §9.2 payoff**: `isDvPure_mul_of_twistLaw` (purity closure) and
  `fgmn_dv_exact_mul_of_twistLaw` — the cite's hypotheses and conclusion matched, proved
  from Theorem M, conditional on `h1` AND `hh : 0 < F.h` (see finding 2).

### Two statement-level findings (for the doc/owner)

1. **MH.1's remaining gap is exactly ONE clause.**  With faithfulness proved here and
   TW-δ/bridge landed in C133mh1, the whole engine root reduces to
   `M1TwistProductLawStatement O` alone.  (Clause (2), the slot-carry form, follows from
   (1) + the landed bridge直... — the bridge gives (2)⟹(1); (1)⟹(2) is a unit juggle not
   needed by any consumer here.)
2. **§9.2's retirement claim has a previously-unrecorded h-fence gap**: `KeyFrame`
   admits the DEGENERATE `h = 0` frame (C01 docstring) and the cite quantifies over it,
   but Theorem M (doc §2) carries `hh : 0 < F.h`.  Byte-identical retirement of
   `fgmn_dv_exact_mul` therefore needs, besides MH.1's twist law, a separate `h = 0` leg
   (C.05 degenerate dictionary + the landed order-1 exact chain).  The payoff theorem
   carries `hh` explicitly and documents this.

### Status of the stretch goal

Attempt of `M1TwistProductLawStatement O` itself (the unconditional root): see below —
[TO BE UPDATED].

## AxChk footer (`lake env lean Uniformity/ChapC/C133mh3.lean`, exit 0)

```
'Uniformity.Density.Tower.C133mh3.m1DigitFaithful' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.digit_stageHeight_modKey_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSupp_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideMin_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideMax_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideDeg_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvResPoly_mul_gen_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.mixedResidualLaw_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.existsUnit_of_tauOne' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.isDvPure_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.fgmn_dv_exact_mul_of_twistLaw' : [propext, Classical.choice, Quot.sound]
```

No roll-up/leanspec/existing files touched; C66b untouched.  No commits.
