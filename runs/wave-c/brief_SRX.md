# UNIT SRX — S2-RECENTER-EXPORT: the mp1 live leg's one open node

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

A-I.7 is ENACTED (2026-08-28, commit 39e3ed55): the capstone ladder record is
`IFC5.LadderSupplyLive₂` whose `mp1` field demands `MP1CarrierLive` — MP1's conclusion
only over blocks equipped with a `RecenterStep` (the same-realization recentering datum;
home leanfinal/Uniformity/ChapI/I10RecenterLive.lean, promoted byte-identically from
REX's design: `GNCitePayload` one-to-one with Guàrdia–Nart CM 637 Thm 2.3,
`MP1StepCore` = MidPeelEmission items 2–4, neither hirr nor hef). The S2 landed prefix
is in I10RecenterLiveS2.lean; the NAMED OPEN is **S2-RECENTER-EXPORT**: construct the
actual `RecenterStep` at the landed S2 occurrence — i.e. exhibit the S2 producer's own
recentering as the export (the GN payload fields discharged from the landed C132 μ₃
key-chain bank), so `MP1CarrierLive` has its first honest inhabitant route.

READ FIRST: runs/wave-c/verdict_REX.md (the design + the S2 seed), verdict_AI7E.md (what
landed where; the S2 gap rows), I10RecenterLive.lean + I10RecenterLiveS2.lean in full,
and the C132 μ₃ bank's key-chain machinery (C132kp0–kp6b: S2Mu3KeyPoly,
s2Mu3_key_irreducible, S2Mu3InitialEquiv, the initial↔residual iff; C130s17's
s2InputPolynomial/s2InputData — the producer whose Λ = −1 legal block powered the
refutation).

## Your charge

1. THE MATH: at the S2 occurrence, identify the genuine recentering the Montes/MacLane
   step performs (the μ₂ → μ₃ key step: Φ₂ → the depth-2 keys — the C132 bank has the
   whole apparatus) and fill `GNCitePayload`'s fields for it: source/sourceLaws (the
   landed FGMNSourceData/Laws at (2,1,21) — C132fd0), keyPolynomial, tangentClass,
   monicInput, slope, the monic irreducible psi, the residual factorization with
   `¬ psi ∣ residualQuot` (multiplicity one), the leaf with exactLeaf. For each field:
   either the landed decl that discharges it, or the precise gap.
2. THE FAITHFULNESS CHECK: the payload's fields must match what GN Thm 2.3 actually
   consumes (REX quoted the exact hypothesis list — verify against it; the pdf is in
   docs/references/). Any field the S2 data cannot honestly supply is a finding, not
   something to force.
3. THE LEAN SURFACE: extend the probe route — leanfinal/scratch/SRX_probe.lean
   (verify `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/SRX_probe.lean`;
   NEVER bare `lake build`) — landing the S2 `RecenterStep` as far as the landed bank
   allows (sorries marked for shape validation only). If fully constructible: the probe
   should end with `s2RecenterStep : RecenterStep ...` sorry-free — the campaign's first
   mp1-live inhabitant datum.
4. Whatever remains: named opens with exact statements (these become the next
   transcription unit's rows).

## Deliverables

- Dated `[SRX 2026-08-28]` section APPENDED to docs/in-progress/LADDER_SUPPLY_2026-08-27.md
  (the field-by-field discharge table).
- `runs/wave-c/verdict_SRX.md`: per-field status + the faithfulness check + probe status.

## Rules

No git commits. No edits to landed .lean/leanspec/existing scratch. Owner's paper never
citable; GN CM 637 with precise clause references only. Rigor paramount.
