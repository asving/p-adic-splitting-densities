/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H01

/-!
# Uniformity.ChapH.H02 — the derived stage data of a genre datum

**Chapter H, NODE H.02** (`blueprint/CHAP-H_general_induction.md` §3). Four derived quantities of
a genre datum `G = (Q; e₁, f₁, μ; h)` (H.01):

* `keyDeg  G = e₁ f₁`   — the key degree `D′` (the corpus's `a = e·γ` with `γ = deg ψ = f₁`);
* `stageCard G = Q ^ f₁` — the stage residue cardinality `|K|`;
* `sideLen G = e₁ μ f₁` — the abscissa length `L` the composite block occupies;
* `nodeHeight G j = (μ − j) · D′ · h + 1` — the stage-initial node floor at coordinate `j < μ`.

Definitional, no proof obligation. DEPENDS: H.01.

SOURCE: `EFF.GENHN.07` (clause (i): key degree `D′ = e₁f₁`, stage residue field `K = F_{Q^{f₁}}`,
stage value normalization `dv := e₁·v`, stage multiplicity `μ`); `EFF.GENHN.08` (`GENHN.A`(i)'s
node **with** the `[r1]` correction); `EFF.GENIND.197` (`γ = deg ψ`, `a = eγ`, `L = eμγ`).

**⚠ TRANSCRIPTION FIDELITY** (blueprint, mandatory). `nodeHeight` uses `D′h = keyDeg * h`, **not**
the sealed `S = e₁ h`: `EFF.GENHN.23`(b) records the `S`-node as replaced and `EFF.GENHN.12`(b) the
settlement *"the `(2,K)`-cluster read at the `S`-node" is read count-side as "at the `B = D′h`-node"*.
The two agree exactly at `f₁ = 1` — every battery row — which is the coincidence-regime trap; the
`f₁ = 1` specialization is a *theorem* (H.08), not the definition.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `D′ = e₁ f₁`, the entry key's degree. -/
def GenreDatum.keyDeg (G : GenreDatum) : ℕ := G.e₁ * G.f₁

/-- `|K| = Q ^ f₁`, the stage residue cardinality. -/
def GenreDatum.stageCard (G : GenreDatum) : ℕ := G.Q ^ G.f₁

/-- `L = e₁ μ f₁`, the abscissa length the composite block occupies. -/
def GenreDatum.sideLen (G : GenreDatum) : ℕ := G.e₁ * G.μ * G.f₁

/-- The stage-initial node floor at coordinate `j`, in `dv`-units:
`dv(A_j) ≥ (μ − j) · D′ h + 1`.  This is the `[r1]`-CORRECTED floor of `GENHN.A`(i); the sealed
`(μ − j) · e₁ h + 1` is the `f₁ = 1` specialization (H.08). -/
def GenreDatum.nodeHeight (G : GenreDatum) (j : ℕ) : ℕ := (G.μ - j) * G.keyDeg * G.h + 1

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum.keyDeg
#print axioms Uniformity.Density.Induction.GenreDatum.stageCard
#print axioms Uniformity.Density.Induction.GenreDatum.sideLen
#print axioms Uniformity.Density.Induction.GenreDatum.nodeHeight

end AxCheck
