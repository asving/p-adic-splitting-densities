/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapE.E26 — the (twisted) seam sum

**Chapter E, NODE E.26** [def] (`blueprint/CHAP-E_sigma_ladder.md` §5, the slot-seam
evaluation layer), ENV-E3 (the stage-field arena: `F ⊆ K` fields, `η : K`; no `O`, no polygon
object — the finiteness hypotheses of ENV-E3 are *not* in the signed binders and are not needed
for the definitions, so they are omitted rather than assumed).

The residue assembly at a seam. Fixing the stage extension `F → K` and the stage generator
`η : K`, the seam sum of a coefficient vector `γ : Fin g → F` is

`seamSum γ η = Σ_{t < g} algebraMap F K (γ t) * η ^ t`,

the `(GAMMA)`/`(SLOT₂)` display's assembly of the `g` normalized coefficient residues into one
element of the stage field. The **twisted** form carries R1-b's per-slot unit `ϑ_t`:

`seamSumT γ ϑ η = Σ_{t < g} algebraMap F K (γ t * ϑ t) * η ^ t`.

Two modelling choices, both forced by the sources and both visible in the signature:

* The twist lives in the BASE field. `EFF.HE7.110` puts `ϑ_t ∈ K_i^×` — the *previous* level's
  field — so the twist enters `K` only through `algebraMap`, and `ϑ : Fin g → F` with a
  nonvanishing hypothesis at the use site (E.27's `hϑ : ∀ t, ϑ t ≠ 0`) is the faithful shape;
  a `Fin g → Kˣ` field would be strictly weaker bookkeeping and strictly stronger a type.
* The twist is multiplied in BEFORE the transport (`algebraMap F K (γ t * ϑ t)`, not
  `algebraMap F K (γ t) * algebraMap F K (ϑ t)`). These agree (`map_mul`), and the chosen form
  is the one the kill lemma E.27 consumes: it presents the twisted family as a single
  `F`-coefficient family `t ↦ γ t * ϑ t`, which is exactly what H.53 (`eta_independent`) takes.

`(SLOT₂)` of `EFF.HE7.11` is the `ϑ ≡ 1` instance of the twisted form; no separate declaration
is introduced for it (one public name per signed row — the relation is a use-site `simp`).

DEPENDS: none (ENV-E3 primitives; mathlib `algebraMap`, `Finset.sum`).

**PROOF.** Definitional. Both bodies are the stage-0e gate-verified ones from
`leanspec/Leanspec/ChapE.lean`, reused verbatim.

**Flagged for human review as new definitions** (parent CLAUDE.md trust boundary): the two
bodies are the whole content of this node, and the reading above (twist in `F`, multiplied
before transport, sum over `Fin g` with `g` the seam length) is the load-bearing part.

SOURCE: `EFF.T2.06` (the boxed `(GAMMA)`); `EFF.HE7.11` ((SLOT₂)(b): "`res(C(ξ)/n₂(k)(ξ)) =
ι_ξ^{(2)}(Σ_{t<d_r} γ_t·β^t)`"); `EFF.HE7.110` (R1-b: "`ι_ξ^{(i+1)}(Σ_{t<g_i} γ_t·ϑ_t·β_i^t)`",
"`ϑ_t ∈ K_i^×` … depending on `(k, t)` and the s-bookkeeping only").

## Status

Sorry-free, axiom-free (Lean core only). The kill (`seamSumT ≠ 0`) is E.27, not here.
-/

namespace Uniformity.Density.Ladder

/-- **E.26 (a)** The seam sum `Σ_t γ_t η^t` (the `(GAMMA)`/`(SLOT₂)` residue assembly). -/
def seamSum {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t) * η ^ (t : ℕ)

/-- **E.26 (b)** The twisted seam sum `Σ_t γ_t·ϑ_t·η^t` (R1-b's display); `ϑ` in the base
field. -/
def seamSumT {F K : Type*} [Field F] [Field K] [Algebra F K]
    {g : ℕ} (γ ϑ : Fin g → F) (η : K) : K :=
  ∑ t : Fin g, algebraMap F K (γ t * ϑ t) * η ^ (t : ℕ)

section AxCheck
#print axioms Uniformity.Density.Ladder.seamSum
#print axioms Uniformity.Density.Ladder.seamSumT
end AxCheck

end Uniformity.Density.Ladder
