/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D53 — instance `GT3-THRESHOLD`: the certificate frame at GENTOW-3's tower

**Chapter D, NODE D.53** [interface] [fresh — GC-13 placeholders]
(`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate witness (T4); amendments A-1 and A-D.1
govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag, so the composed text is
its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none in
chapter D` — verbatim: "the instance is C's `CertFrame` term; D supplies the frame and lemmas"
— together with `PROOF. n/a`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`. §12 rule 4 is the
reason and it is mandatory: **"No stub for another chapter's placeholder: the
`[supplied-by: chapter C]` rows are NOT axiomatized in leanspec (axiomatizing a supplier's
theorem would fake the discharge — exactly the class of defect the honesty items fence)."** The
stage-0e stub gate held that line (`leanspec/Leanspec/ChapD.lean`: "D.42, D.43, D.53, D.54,
D.56 and D.61 declare nothing … and no chapter-C/E/F node ID is guessed anywhere in this
file"), and this landed copy holds it too: the file **imports nothing and defines nothing**, so
it can never become a silent dependency of a proof, and no `EFF.GENTOW3` fact acquires a Lean
name here.

What the node *is*, then, is the instantiation record: which chapter-D frame objects the
GENTOW-3 instance binds, which facts it consumes from chapter C, what the absorption says, and
which fences travel with it. That record is transcribed below.

## The instance

The certificate frame of D.46 (`Uniformity.Density.Gauge.CertFrame`) instantiated at GENTOW-3's
composed tower:

| frame datum | GENTOW-3 binding |
|---|---|
| the discrepancy map | `Δ_j = ShC_j − C_j` |
| the thresholds | `Θ_j = thresholdTheta μ₂ E₂ δ j` (D.45; `E₂ = e₂f₂u₂`, `δ = u₂ − e₂D′h ≥ 1`) |
| the certificate witness | `ω_j` = the key power's **assembled** height-`Θ_j` digit (D.48) |

The un-collapsed layers of the source — `ShC_j`, the grid `𝒜_j`, the member slot condition —
are the supplier's concrete objects (`EFF.T4.03`–`.09 [supplied-by: chapter C]`); D.46's frame
carries only the composite `grΔ` plus additivity, because "Linearity is the ONLY property used
downstream" (`EFF.T4.06`), and complete assembly is `grΔ`'s **instantiation obligation** — i.e.
it is discharged *here*, at the instance, not at the frame.

## The four consumed facts, each a chapter-C placeholder

1. **`(FLOOR)` on `𝔐`** = GENTOW-3(i), read at its Steps 0–2 quantification domain
   (`EFF.GENTOW3 [supplied-by: chapter C]`; the R5-F1 supplier cite). This is the hypothesis
   field `floor` of D.46's `CertFrame`.
2. **The per-genre, per-coordinate computation of `ω_j`** = GENTOW-3(iv), through GT3-r2/r3.
3. **The `Θ_j + 1` perturbation margin** = GENTOW-3 S8.1. This is what feeds D.50's
   SPECIALIZATION hypothesis (`∀ m, m ≤ F.Θ j → F.grΔ m j g = 0`) — D.50's own PROOF block
   names the discharge as "the supplier's S8.1 box … `[supplied-by: chapter C]` at D.53".
4. **The x-free extreme** = GENTOW-3(iii): every discrepancy zero, every `ω_j = 0`.

## The result: the absorption, transcribed verbatim

> "GENTOW-3(iv)'s phrase 'touched coordinate(s)' is exactly DEFINITION T4.1. Its attainment
> conclusion is LEMMA T4.2(a), and its repaired deep-perturbation persistence is
> LEMMA T4.2(b)."

In landed Lean names (all in `Uniformity.Density.Gauge`, all already green at HEAD): DEFINITION
T4.1 is `CertFrame.omega` / `CertFrame.Touched` (D.48); LEMMA T4.2(a) is
`CertFrame.touched_iff_nu_eq` with its sibling `CertFrame.nu_gt_of_untouched` (D.49); LEMMA
T4.2(b) is `CertFrame.perturb_stable` with its sibling `CertFrame.perturb_nu_eq` (D.50). The
absorption claim is that GENTOW-3's own vocabulary needs no translation layer — but the claim
is *about the instance*, and the instance is C's term, which is precisely why nothing is
declared here.

## The four fences carried

1. **One-sidedness scope** (`EFF.T4.19`). `ω_j = 0` does NOT bar other members from attaining
   the threshold: the `W` member attains `Θ₀` through entry-driven content. This is the same
   fence as D.52's ⚠ (ii) and it is what keeps D.49's equivalence about `f_key` alone.
2. **The measured-configuration set** (`EFF.T4.20`) — inherited evidence, retained as §12
   regressions, never re-derived in Lean: FAM-A5/A7/B/C and FR-GL attained; FR-M3 with
   thresholds `[10,7,4]` against self-shadow pins `[12,7,4]`, `ω₀ = 0`, `ω₁, ω₂ ≠ 0`; FR5X's
   identically zero rows. The FR-M3 row is also D.48's committed separator (`EFF.T4.11`: the
   self-shadow has pin 12 while `Θ₀ = 10` and `ω₀ = 0` — a shadow coordinate may be nonzero
   while its height-`Θ_j` digit cancels), and its slack check is anchored in Lean by gate D.66
   leg 4 (bare `decide`, pure `ℕ`/`ℕ∞`).
3. **The six-span GT3 pin stack** (`EFF.T4.21`) is the placeholder's provenance, **fail-closed**
   per `EFF.T4.29`.
4. **The `ω_j` wording seam** (`EFF.T4.18`'s NOTE): pre-r3 vocabulary survives in the
   Substitution block; the governing definition is D.48's r3 one. Carried to §13.

## Reading notes for a consumer

* **Chapter D does not discharge any of the four consumed facts.** A chapter-D node that
  appears to prove one of them has found a defect, not a discharge — the same rule D.64's
  routing table states for its own rows.
* **The frame lemmas are unconditional; the instance is where the burden sits.** D.51's
  full-exposure premise (`HYP.113`) and D.52's provenance-exclusion fence (`HYP.114`) are
  hypotheses at frame level and obligations at instance level; this node is the GT3 half of
  that ledger, D.54 the GT6 half.

**DEPENDS.** D.45–D.52 · `EFF.GENTOW3 [supplied-by: chapter C]` (spans per `EFF.T4.21`).

**SOURCE.** `EFF.T4.18` (the instance and the absorption), `.19` (the one-sidedness scope),
`.20` (the measured configurations), `.21` (the six-span pin stack; fail-closed per `.29`).

**TEETH.** S8 PE2 GT3 consumption, in full → §12. The executable regressions are retained
Python/PARI-side (inherited evidence, `EFF.T4.37`'s fence); the FR-M3 slack `[12,7,4]` versus
`[10,7,4]` check is additionally gate material (D.66's ⚠, leg 4).

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
