/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D46 — `CertFrame`, T4's certificate frame

**Chapter D, NODE D.46** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate
witness (T4); amendments A-1, A-D.1 govern). ENVIRONMENT: ENV-D3 (a bare `[Field K]` for the
digit field) **plus the two extra parameters `(Dv, Slot)`** the node's own ENVIRONMENT line
adds. One public declaration — the schema every §7 node after it is stated over.

*The certificate frame.* Over a dividend group `Dv` (the `𝒟_{≤μ₂}` module, `AddCommGroup`), a
slot type `Slot`, and a digit field `K`, a certificate frame carries:

| field | corpus object |
|---|---|
| `μ₂ : ℕ` | the level-2 multiplicity |
| `Θ : ℕ → ℕ` | the thresholds `Θ_j` (the instances set `Θ := thresholdTheta μ₂ E₂ δ`, D.45) |
| `M : Set Dv` | the member class `𝔐`, the affine development slice |
| `fkey : Dv`, `fkey_mem` | the distinguished member `f_key`, and membership fact 1 |
| `grΔ : ℕ → ℕ → Dv →+ (Slot →₀ K)` | the composite assembled read `(m,j) ↦ gr_m(Δ_j ·)` |
| `floor` | **(FLOOR)**: `∀ f ∈ M, ∀ j < μ₂, ∀ m < Θ j, grΔ m j f = 0` |

**`M` carries NO discriminant hypothesis and no decidedness hypothesis** (`EFF.T4.05`): it is a
pure coefficient condition, and the concrete slot-weight definition is the suppliers'. (FLOOR)
is landed at exactly the R5-F1-rebound quantification — "for every `f ∈ 𝔐`, every `j < μ₂`, and
every `m < Θ_j`" (`EFF.T4.13`) — no more, no less.

## Why the five corpus layers collapse to one field (the §7 design note)

T4's machinery defines `𝒟_{≤μ₂}`, `𝒜_j`, `C_j/ShC_j`, `Δ_j`, `gr_m`, but its four lemmas
consume ONE composite: the assembled height-`m` digit of the `j`-th discrepancy, plus its
additivity — "Linearity is the ONLY property used downstream" (`EFF.T4.06`). So `grΔ` is a
single `AddMonoidHom`-valued field, and "distinct canonical slots form separate components"
(`EFF.T4.07`) is the CODOMAIN's structure (`Slot →₀ K`) rather than a hypothesis. Complete
assembly — "all branches, carries, recarries … added before the class is taken" — is then the
**instantiation obligation** on whoever supplies `grΔ`, which is the honest relocation of the
r3/r4 exposure repairs (honesty item D-H7(2)).

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one structure; parent CLAUDE.md trust boundary).
The blueprint discloses three deltas, all consumption-neutral; they are repeated here verbatim
in substance and are **flagged for the chapter cross-read (§13 item 4)**:

* *(i) the layer collapse.* `C_j`/`ShC_j`/`Δ_j`/`gr_m` are not separate fields; only the
  composite and its additivity are consumed downstream (the spec's own sentence). The identity
  `Δ_j(f_key) = ShC_j(Φ₂^{μ₂})` (`EFF.T4.09`'s `C_j(f_key) = 0`) is an instantiation-side fact,
  not a frame field. The un-collapsed layers are the suppliers' concrete objects
  (`EFF.T4.03–.09 [supplied-by: chapter C]`, at the GT3/GT6 instances D.53/D.54).
* *(ii) membership fact 2 is not a field.* In-budget closure of `𝔐` is a supplier lemma,
  consumed as a HYPOTHESIS at D.50's specialization; the corpus derives it from the concrete
  slot condition ("pure coefficient arithmetic"), which this schema does not see.
* *(iii) the slot type is abstract.* `Slot` is an arbitrary type; separateness of canonical
  slots is carried by `Finsupp`.

One further Lean-side note, not a delta: **`Θ` is an arbitrary `ℕ → ℕ`**, not `thresholdTheta`
specialized. D.45 is a DEPENDS in the blueprint's sense that the instances instantiate the
field with it; keeping the field general is what lets the gate frames (D.66's `[12,7,4]`
self-shadow separator) sit in the same schema as the composed thresholds.

**DEPENDS.** D.45 (the instances set `Θ := thresholdTheta …` — an instantiation edge, not a
Lean import: this file introduces no dependence on `thresholdTheta`'s body) · mathlib `Finsupp`,
`AddMonoidHom`, `Set`.

**PROOF.** definitional.

SOURCE: `EFF.T4.03` (`𝒟_{≤μ₂}`, `𝒟_{<μ₂}`), `.04` (`𝒜_j`, one `K₂`-digit per height), `.05`
(`𝔐` + the three membership facts + NO-disc), `.06` (`ShC_j`, `Δ_j`, linearity), `.07` (`gr_m`,
complete assembly), `.08` (full exposure — all-provenance), `.09` (`f_key`), `.13` ((FLOOR) and
the R2-G1/R5-F1 binding chain).

**TEETH.** S8 PE1(1)–(3) → carried to the instances (D.53/D.54) and §12. **Non-vacuity is NOT
scored here**: `CertFrame` is inhabited with (FLOOR) satisfied AND its coordinate `j = 0`
TOUCHED, and that witness is gate content owned by **D.68** (A-D.1 item (v)) — duplicating it
in this file would put two copies of a gate row in the chapter, exactly as D.45 declines to
duplicate D.66's `Θ` table.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.46** T4's certificate frame (`EFF.T4.01`–`.13`, composite-read packaging per the §7
design note).

The member class `M` (`𝔐`) is a **pure coefficient condition**: it carries NO discriminant
hypothesis and no decidedness hypothesis (`EFF.T4.05`); the concrete slot-weight definition is
the suppliers'. Instantiating `grΔ` = supplying COMPLETE assembly — every branch, carry and
recarry added before the class is taken (`EFF.T4.07`/`.08`). Instantiating `floor` =
GENTOW-3(i) at `𝔐` `[supplied-by: chapter C]`; its quantification is the R5-F1 rebound's,
verbatim: for every `f ∈ 𝔐`, every `j < μ₂`, and every `m < Θ_j` (`EFF.T4.13`). -/
structure CertFrame (Dv : Type*) [AddCommGroup Dv] (Slot : Type*)
    (K : Type*) [Field K] where
  /-- The level-2 multiplicity `μ₂`; the coordinate range of the certificate is `j < μ₂`. -/
  μ₂ : ℕ
  /-- The thresholds `Θ_j`.  The instances set this to `thresholdTheta μ₂ E₂ δ` (D.45). -/
  Θ : ℕ → ℕ
  /-- The member class `𝔐` — a pure coefficient condition (`EFF.T4.05`). -/
  M : Set Dv
  /-- The distinguished member `f_key` (`EFF.T4.09`). -/
  fkey : Dv
  /-- Membership fact 1: `f_key ∈ 𝔐`. -/
  fkey_mem : fkey ∈ M
  /-- The composite assembled read `(m, j) ↦ gr_m(Δ_j ·)`, additive in its argument —
  "Linearity is the ONLY property used downstream" (`EFF.T4.06`). -/
  grΔ : ℕ → ℕ → Dv →+ (Slot →₀ K)
  /-- **(FLOOR)** at the R5-F1-rebound quantification (`EFF.T4.13`). -/
  floor : ∀ f ∈ M, ∀ j < μ₂, ∀ m < Θ j, grΔ m j f = 0

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame

end AxCheck
