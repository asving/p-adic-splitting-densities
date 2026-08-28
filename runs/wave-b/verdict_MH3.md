# Verdict — MH3: THEOREM M LANDED UNCONDITIONALLY (root M1′ + clauses 1–3 + cite payoff)

**Date:** 2026-08-27/28
**Unit:** MH3 (Fable tier)
**Charge:** transcribe Theorem M (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §§2–3,
[MHFIX] state; §9 row MH.3), `R(gz) = R(g)·R(z)` τ = 1 for all nonzero `g, z`; payoff:
derive the declared cite `fgmn_dv_exact_mul`'s statement (§9.2).

## RESULT — beyond the charge: the ROOT itself is proved

`leanfinal/Uniformity/ChapC/C133mh3.lean` (1935 lines): `lake env lean` exit 0, ZERO
errors/warnings/`sorry`; `lake build Uniformity.ChapC.C133mh3` green (8748 jobs); all 24
printed footprints EXACTLY `[propext, Classical.choice, Quot.sound]`.  Zero new axiom.

### Ground truth found on arrival (differs from the charge's premise)

The charge assumed MH.1's slot form was landed.  In fact C133mh1 landed TW-δ + the
carry⟹twist bridge as theorems but the three M1′ clauses only as STATEMENT SHAPES
(`verdict_MH1.md` left the full M1′ proof open); MH.2 had no landed file.  This unit
closed the whole gap.

### Landed, UNCONDITIONAL (Lean-core)

* **M1′, all three clauses — MH.1 CLOSED**: `m1DigitFaithful` (clause 3, from C.23's
  `slotRes_ne_zero`), `m1SlotCarryLaw` (clause 2, the η^δ carry law),
  `m1TwistProductLaw` (clause 1, the twist form) — discharging C133mh1's pinned shapes
  BY NAME.  Proof per the doc §3.1′'s coefficientwise route: a private `fullRead` (the
  C.21 window without the `t < f₁` fence); `fullRead_mul_of_le` (the TW-δ convolution
  law, all polynomials, floors only); `fullRead_key` (`ψ(η) = 0` via
  `AdjoinRoot.eval₂_root` on B.28/B.29 unwound) with private MH.0a (`stageHeight_key_eq`)
  and the pin identification `pin_eq : H₀ = h·f₁`.
* **Theorem M clauses 1–2 (MH.2)**: `dvSupp_mul`, `dvSideMin_mul`, `dvSideMax_mul`,
  `dvSideDeg_mul`, pin law `dvHgt_dvSideMin_mul_of_twistLaw` — including the doc's
  PROOF-OUTLINE-grade `dvSideMax` half, fully proved via `(jmax,jmax)`-pair survival +
  strict convolution pricing on the landed C130nv2/rp2/rp4 banks.
* **Theorem M clause 3 (MH.3)**: `dvResPoly_mul_gen` — τ = 1, ALL nonzero `g, z`, no
  fence; packaged `mixedResidualLaw : MixedResidualLawTauOneStatement O` (probe-verbatim
  shape declared here per the MH.1 verdict's scoping) + `existsUnit_of_tauOne`.
* **The §9.2 payoff**: `isDvPure_mul` (purity closure) and **`fgmn_dv_exact_mul_thm`**
  — the declared cite's statement AS A THEOREM, hypothesis list matched plus ONE honest
  extra `hh : 0 < F.h` (finding 2 below).  C66b untouched, per charge.
* Architecture: Parts 1–9 = the assembly layer conditional on the single pinned
  hypothesis (`_of_twistLaw` names, independently auditable); Part 10 = the root;
  Part 11 = instantiations.

### Two statement-level findings (for the doc/owner)

1. **§9.2's retirement claim has an unrecorded h-fence gap**: `KeyFrame` admits the
   DEGENERATE `h = 0` frame (C01 docstring) and the cite quantifies over it; Theorem M is
   `0 < F.h`-fenced.  Byte-identical retirement of the AXIOM needs a separate `h = 0` leg
   (C.05 degenerate dictionary + the landed order-1 exact chain).  At `h ≥ 1` — every
   live consumer — the cite's content is now a theorem.
2. `Nat.Coprime h e₁` (frame field `hcop`) is what makes alignment = slot congruence
   (`aligned_iff`); the strict floor is consumed only via `V ≤ D′h` (no MH.0a exactness
   needed for MH.2/MH.3 — exactness IS needed and proved for the key-kill in Part 10).

### Consequences for the fleet (per the doc's gates)

* MH.1 (all clauses), MH.2, MH.3 are LANDED → the doc's fleet fence condition "MH.1
  lands" is met (MH.8/X1 remain probe-proved, promotion pending elsewhere).
* Retirement pass for `fgmn_dv_exact_mul` (orchestrator): consumers at `h ≥ 1` frames
  can cite `C133mh3.fgmn_dv_exact_mul_thm`; the axiom's full quantifier still needs the
  `h = 0` leg — recommend either a fence amendment or a small C.05-route unit.
* Parallel landings noted: C133mh0 (MH0A6 unit) independently landed a public
  `stageHeight_key`; my Part-10 twin is private (D9 convention), no clash.

## AxChk footer (`lake env lean Uniformity/ChapC/C133mh3.lean`, exit 0 — 24 decls,
each exactly Lean-core; headline lines)

```
'Uniformity.Density.Tower.C133mh3.m1DigitFaithful' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.m1SlotCarryLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.m1TwistProductLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSupp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideMin_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideMax_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvSideDeg_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.dvResPoly_mul_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.mixedResidualLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.mixedResidualLawExistsUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.isDvPure_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh3.fgmn_dv_exact_mul_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No roll-up/leanspec edits by this unit (orchestrator wired the roll-up at its checkpoint
commit a55fbd43); C66b untouched; no commits by this unit.
