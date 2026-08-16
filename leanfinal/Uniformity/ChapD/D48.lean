/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D46

/-!
# Uniformity.ChapD.D48 — `CertFrame.omega` / `CertFrame.Touched`, the certificate witness

**Chapter D, NODE D.48** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate
witness (T4); amendments A-1, A-D.1 govern — this node's signature is unamended). ENVIRONMENT:
as D.46 (ENV-D3 plus the two extra parameters `(Dv, Slot)`). Two public declarations, both
definitional; the node the whole of §7 is named after.

*The certificate witness and touchedness.* For a certificate frame `F` (D.46) and a coordinate
`j : ℕ`:

```
omega   F j  :=  F.grΔ (F.Θ j) j F.fkey   : Slot →₀ K
Touched F j  :=  F.omega j ≠ 0            : Prop
```

`ω_j` is "the fully assembled height-`Θ_j` `K₂`-digit of the key power" (`EFF.T4.10`, r3 text):
the threshold comes from the frame's own `Θ` field, the coordinate is `j`, and the argument is
the distinguished member `f_key`. The corpus's second display `ω_j = gr_{Θ_j}(ShC_j(Φ₂^{μ₂}))`
is the same object through `EFF.T4.09`'s `C_j(f_key) = 0` — an INSTANTIATION-side fact about a
layer this schema collapsed away (D.46 faithfulness (i)), not a Lean identity here.

Untouched is spelled `¬ F.Touched j` at every consumer (D.49's corollary, D.51's
`omega_zero_iff_untouched`); the blueprint signs it as that negation and NOT as a separate
declaration, so none is introduced.

## What "fully assembled" means, and where the obligation sits

"Its assembly includes every input landing in the canonical composed grid … Every collision and
cancellation is completed before the digit is taken" (`EFF.T4.10`). That sentence is **not** a
property of this definition — it is `grΔ`'s instantiation obligation, exactly as the §7 design
note relocates it (D.46's docstring; honesty item D-H7(2)). At the schema level `omega` is a
projection of the frame; the r3/r4 exposure repairs are discharged by whoever supplies `grΔ`.

## Faithfulness

**⚠ Trust-boundary definition** (parent CLAUDE.md trust boundary). The one point that matters,
transcribed from the corpus's own fence (`EFF.T4.11`):

* *`Touched` is DELIBERATELY STRONGER than the two nearby conditions it is easy to confuse it
  with.* It is not "`ShC_j(Φ₂^{μ₂}) ≠ 0`", and it is not "some unassembled single-extraction
  branch is nonzero": "A shadow coordinate may be nonzero while its height-`Θ_j` digit
  cancels." The corpus commits a separator for exactly this — **FR-M3 at `j = 0`: the
  self-shadow has pin `12`, but `Θ₀ = 10` and `ω₀ = 0`**, so that coordinate is UNTOUCHED
  despite a nonzero shadow. The separator is a retained §12 regression and a D.53 instance row;
  it is executed at the D.66 gate, not duplicated here.
* *the codomain is `Slot →₀ K`, not `K`.* `ω_j` is a whole digit — one `K`-coefficient per
  canonical slot — and `≠ 0` is nonvanishing of the `Finsupp`, i.e. SOME slot is nonzero. The
  slot-indexed sharpening (a NAMED slot with a named nonzero coefficient) is D.51's
  `touched_of_slot`, whose hypotheses are `(F.omega j) σ = ξ` and `ξ ≠ 0` — a strictly stronger
  input, deliberately kept out of this definition.
* *no coordinate range, no membership.* `omega` and `Touched` are defined at every `j`, with no
  `j < F.μ₂` side condition; `fkey_mem` is not consumed here. The range enters at the theorems
  (D.49's `hj`), which is where `EFF.T4.14` puts it.

**Flagged for human review** (definition faithfulness).

DEPENDS: D.46 (`CertFrame`, landed at `Uniformity.ChapD.D46`) · mathlib `Finsupp` (for the
codomain and its `0`). Nothing else; D.45's `thresholdTheta` enters only through the frame's own
`Θ` field, which is an arbitrary `ℕ → ℕ` at this schema.

**PROOF.** Definitional. Both bodies are the gate-verified `leanspec/Leanspec/ChapD.lean` stub
bodies verbatim, with the blueprint's `namespace Uniformity.Density.Gauge` header restored (the
leanspec wrapper `LeanspecD` is a stub-side artifact; the landed namespace assignment is
`Uniformity.Density.Gauge`, GC-6.2). `omega` is signed `noncomputable`; `Touched` is a plain
`Prop`-valued `def` (not `abbrev`, not a class), so consumers unfold it by
`CertFrame.Touched`/`CertFrame.omega` exactly as D.49's proof does.

SOURCE: `EFF.T4.10` (DEFINITION T4.1 — `ω_j := gr_{Θ_j}(Δ_j(f_key)) = gr_{Θ_j}(ShC_j(Φ₂^{μ₂}))`,
the second form via `EFF.T4.09`; touched ⟺ `ω_j ≠ 0`); `EFF.T4.11` (the fence, and the FR-M3
`j = 0` separator quoted above); `EFF.T4.09` (`f_key`).

**TEETH.** S8 PE1(1) → the codomain structure plus the GT3/GT6 instances (D.53/D.54); the FR-M3
separator → §12's retained regression and the D.66 gate. Nothing to score at this node — two
definitions.

ENVIRONMENT: as D.46 — ENV-D3 (`[Field K]` for the digit field) plus `(Dv, Slot)`, all written
inline as each declaration's own binders (no `variable` block, B.42 binder rule).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.48** The certificate witness `ω_j` — the fully assembled height-`Θ_j` `K₂`-digit of the
key power, `ω_j := gr_{Θ_j}(Δ_j(f_key))` (`EFF.T4.10`, r3 text). "Every collision and
cancellation is completed before the digit is taken" is `grΔ`'s INSTANTIATION obligation (the
§7 design note), not a property of this projection. -/
noncomputable def CertFrame.omega {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Slot →₀ K :=
  F.grΔ (F.Θ j) j F.fkey

/-- **D.48** Touched: `ω_j ≠ 0` (`EFF.T4.10`); untouched is the negation, spelled at the
consumers. ⚠ Deliberately stronger than "`ShC_j(Φ₂^{μ₂}) ≠ 0`" and than "some unassembled
branch is nonzero" (`EFF.T4.11`): a shadow coordinate may be nonzero while its height-`Θ_j`
digit cancels. FR-M3 at `j = 0` is the committed separator — the self-shadow has pin `12`, but
`Θ₀ = 10` and `ω₀ = 0` — executed at the D.66 gate. -/
def CertFrame.Touched {Dv Slot K : Type*} [AddCommGroup Dv] [Field K]
    (F : CertFrame Dv Slot K) (j : ℕ) : Prop := F.omega j ≠ 0

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.CertFrame.omega
#print axioms Uniformity.Density.Gauge.CertFrame.Touched

end AxCheck
