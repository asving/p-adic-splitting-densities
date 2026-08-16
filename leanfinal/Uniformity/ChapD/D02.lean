/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D01

/-!
# Uniformity.ChapD.D02 — `NormSection.tau`, the normalizer cocycle and its endpoints

**Chapter D, NODE D.02** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — this node's signature is unamended).
ENV-D2. Three public declarations (the signed `def` and the two signed endpoint lemmas, same
file — the STATEMENT displays both endpoints, and the stub gate signs all three).

*The normalizer cocycle `τ` and its endpoints.* For a normalizer section `N` (D.01),

  `τ(a,b) := n(a)·n(b)·n(a+b)⁻¹`,  with  `τ(0,a) = τ(a,0) = 1`.

The corpus writes the quotient `n̂_i(a)n̂_i(b)/n̂_i(a+b)` (`EFF.T1.08`'s first display);
division is `·⁻¹` in the commutative group `G`, so the Lean body is that display verbatim.

This node stops at the ENDPOINTS. The boxed `(C2-cocycle)` associativity law
`τ(a,b)·τ(a+b,c) = τ(b,c)·τ(a,b+c)` of the same source unit is node D.03, deliberately
separate: `EFF.T1.08`'s own derivation splits the two ("Associativity compares the two
parenthesizations of three normalizers. `n̂_i(0) = 1` gives both endpoints"), and only the
endpoint half consumes `n_zero`.

## Faithfulness

**⚠ Trust-boundary transcription.** Three points, flagged for the chapter cross-read:

* *`τ` is the ONLY τ of the chapter.* T3 §8.1 check (3) is the "no competing frame" obligation:
  every τ below — D.03's cocycle law, D.05's telescope recursion, D.08's `tau_mem_ker` residue
  leg — is THIS `NormSection.tau`, and no consumer may introduce a second two-argument cocycle.
  The near-miss name is T3's `χ` (ONE argument, the pointwise section ratio, D.39's `chi`),
  which the spec itself renamed to avoid exactly this collision (`EFF.T3.12`); the two Lean
  names are `chi` and `tau` and neither aliases the other (blueprint §0.3(ii)).
* *both endpoints are public.* The blueprint's SIGNATURE comment calls `tau_zero_right` "a
  private corollary in the same file"; the node's STATEMENT displays `τ(0,a) = τ(a,0) = 1`, and
  the gate-verified stub (`leanspec/Leanspec/ChapD.lean`) signs it as a public row — the same
  reading the blueprint spells out at D.05 ("the endpoints are its two `simp` corollaries,
  public per the STATEMENT — the stub signs all three"). Landed public, so that a consumer of
  the mirror endpoint cites a name rather than re-deriving it.
* *no valuation, no residue, no tower.* ENV-D2 is a bare `CommGroup`: `EFF.T1.08`'s
  CONDITIONALITY ("all displayed heights and sums must be defined") is discharged by typing
  heights as `ℤ`, on which every sum is total. The residue layer enters only at D.07/D.08, and
  `tau a b`'s value-zero membership is D.08's `tau_mem_ker`, not a fact of this node.

DEPENDS: D.01 (`NormSection`, landed at `Uniformity.ChapD.D01`; the `n_zero` field is what the
two endpoint lemmas consume). No other landed node; mathlib group lemmas only, all reached
through `simp`.

**PROOF.** The blueprint's, executed. 1. Unfold: `τ(0,a) = n 0 * n a * (n (0+a))⁻¹`.
2. `N.n_zero` + `zero_add` + `mul_inv_cancel`-shape closes it
(`simp [NormSection.tau, N.n_zero]`). 3. Mirror by `add_comm`/`mul_comm` — in Lean the very
same `simp` call discharges it (`add_zero`/`mul_one` in place of `zero_add`), so the mirror
costs one line and no commutativity rewrite is written by hand.

SOURCE: `EFF.T1.08` (the definition display `τ_i(a,b) = n̂_i(a)n̂_i(b)/n̂_i(a+b)` and the
endpoint display `τ_i(0,a) = τ_i(a,0) = 1`; DERIVATION "…`n̂_i(0) = 1` gives both endpoints",
RESOLUTION TRACE "R1-2 supplies the height-zero normalization and endpoint derivation");
`EFF.T3.02` (the imported `(T1-C2)` display).

**TEETH.** T3 §8.1(3) (no competing frame — the τ used everywhere below is THIS τ) →
executable regression retained (§12); the endpoint half → Lean theorem (this node). T1's
"misindexed telescope tooth" is scored at D.03/D.67, not here.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule —
this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only). Both lemmas are PROVED theorems here, not the leanspec
`axiom` stubs.
-/

namespace Uniformity.Density.Gauge

/-- The T1 normalizer two-cocycle `τ_N(a,b) = N(a)N(b)/N(a+b)` (`EFF.T1.08`, `EFF.T3.02`). -/
def NormSection.tau {G : Type*} [CommGroup G] (N : NormSection G) (a b : ℤ) : G :=
  N.n a * N.n b * (N.n (a + b))⁻¹

/-- Endpoint `τ(0,a) = 1` (`EFF.T1.08`; from `(C2-zero-normalizer)`, D.01's `n_zero`). -/
theorem NormSection.tau_zero_left {G : Type*} [CommGroup G] (N : NormSection G) (a : ℤ) :
    N.tau 0 a = 1 := by
  simp [NormSection.tau, N.n_zero]

/-- Endpoint `τ(a,0) = 1` (`EFF.T1.08`; the mirror of `tau_zero_left`, by commutativity of `G`
and `add_zero`). -/
theorem NormSection.tau_zero_right {G : Type*} [CommGroup G] (N : NormSection G) (a : ℤ) :
    N.tau a 0 = 1 := by
  simp [NormSection.tau, N.n_zero]

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.tau
#print axioms Uniformity.Density.Gauge.NormSection.tau_zero_left
#print axioms Uniformity.Density.Gauge.NormSection.tau_zero_right

end AxCheck
