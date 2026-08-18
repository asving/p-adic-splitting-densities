/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B77a
import Uniformity.ChapB.B77b
import Uniformity.ChapC.C11
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C117

/-!
# Uniformity.ChapC.C118 — visible reads are window functions (level 2)

**Chapter C, NODE C.118** [lemma] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §12).  B.77's window-congruence, one level up: two
members of the same level-`N` window class have equal level-2 heights (`dv2Pin`), side
data, and residual polynomials (`dv2ResPoly`) at every consulted datum, under the
`Visible₂` guard.  Two signed clauses: `dv2_read_congr` (heights) and
`dv2_read_congr_res` (residuals) — B.77's own split executed.

## Route (recorded at skeleton time; B77a/B77b are the template)

The level-2 reads unfold to level-1 reads of development blocks:
`dv2Pin L Ψ f j = dvSupp F (dev Ψ f j) L.u L.ℓ`, `dvHgt F A i = F.stageHeight (dev F.key A i)`,
and `stageHeight F A = suppVal X A F.h F.e₁` (C.02's GC-2 reuse) — so every consulted
datum bottoms out in `suppVal`-at-key-`X` reads of DOUBLE developments
`dev F.key (dev Ψ f j) i`.  Congruence propagates through both `dev` layers by B.10's
`dev_congr`; the reads then agree by the B.77 capped-min dichotomy — NOT by
`suppVal_congr` as stated (its `hdeg` binder fails for blocks, whose degrees are not
window-stable): the chain needs the dichotomy form (each capped read `min (·) (window)`
agrees, and `Visible₂` pins the consulted reads strictly below the window
`(F.e₁ * L.ℓ) * N`, whence the caps are invisible).  The residual clause additionally
threads B77b's `resMk`-level congruence through C.38a's `dv2Res` (the coherent read is a
`dvResPoly` pushed through `AdjoinRoot.mk L.r`; its consulted heights sit below the
window by the same guard).

## Status

**BLOCKED — the frozen clause 1 is MACHINE-REFUTED** (2026-08-18;
`C118_REFUTATION.lean.txt`, `c118_clause1_refuted`, compiles clean at the pin): a ⊤ pin of
the member `a` is unguarded by `Visible₂` (`≠ ⊤ →` escape) and REAL at level 2 (blocks can
vanish below the top), while a `π^N`-perturbed member of the same window class has a
FINITE pin at the same abscissa — the FOURTH A-C.1 vacuous-⊤ instance (C.111, C.94,
C.113, now C.118).  Clause 2 is SUSPECT by the same mechanism (its `hne'`/side data
consult the unguarded member).  The sorried clauses below are the FROZEN (refuted) forms,
retained verbatim for the record; do NOT attempt to prove clause 1 — it is false.
Amendment A-C.7 (blueprint) drafts the re-signs: the unconditional CAPPED law
`min (dv2Pin ·) W = min (dv2Pin ·) W` (`W = (F.e₁ * L.ℓ) * N`, the honest "window
function" reading) plus the guarded raw form (`dv2Pin ≠ ⊤` binder), with clause 2
re-signed at B77b's level-1 shape; per the A-C.5 certify-BEFORE-sign standard the
leanspec re-sign lands only WITH the repair proofs.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.118, clause 1 — the level-2 height reads are window functions.** -/
theorem dv2_read_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N) {j : ℕ} (hj : j ≤ n / L.keyDeg₂) :
    dv2Pin L Ψ (monicPoly a) j = dv2Pin L Ψ (monicPoly a') j := by
  sorry

/-- **C.118, clause 2 — the level-2 residual reads are window functions.** -/
theorem dv2_read_congr_res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂).Nonempty) :
    dv2ResPoly L Ψ (monicPoly a) u₂ ℓ₂ hne = dv2ResPoly L Ψ (monicPoly a') u₂ ℓ₂ hne' := by
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2_read_congr
#print axioms Uniformity.Density.Tower.dv2_read_congr_res

end AxCheck
