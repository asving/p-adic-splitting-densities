/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.LevelDrop
import LeanUrat.OM.ChildResidualExt

/-!
# `LevelDropResidue` — the residue reader is stable under the level-drop hom (below the cutoff)

Additive leaf over `LeanUrat.OM.LevelDrop` and `LeanUrat.OM.ChildResidualExt` (which transitively
imports `UnramifiedBase`). Nothing imports this file, so it cannot break `master`.

This is the CITE-FREE half (Goal 2a) of the reduce-stability `hcompat` that
`ChildResidualExt.childResidualExt_transport` abstracts as a hypothesis: the extension analogue of
the order-≤1 `PadicLift.zmodUnitResidue_reduce_stable`, now over the unramified base ring.

## What this file lands (core-only, no `sorry`/`axiom`/`native_decide`)

* `resUnitResidue_levelDrop` — for `x : Oring(p, N+1, g')` with `p`-adic valuation strictly below the
  drop cutoff `N` (`pval x < N`), the residue reader commutes with the level drop:
  `resUnitResidue N g (levelDropHom x) = levelDropResHom (resUnitResidue (N+1) g' x)`.

The proof follows the standard "divide out `p^v`, reduce mod `p`" argument:
1. `x ≠ 0` (since `pval x < N`, and `pval x = N+1 ↔ x = 0` at level `N+1`).
2. A witness `u` at level `N+1` with `u · p^v = x` (`pvalWitness_spec`); `u ∉ (p)` because otherwise
   `x ∈ (p^{v+1})` would force `v+1 ≤ pval x = v`.
3. `θ := levelDropHom` is a ring hom sending `p ↦ p`, so `θ x = θ u · p^v`.
4. **Crux — `pval (θ x) = v`:** `θ u ∉ (p)` at level `N` (via `resHom_natural_levelDrop`: `resHom (θ u)
   = φ (resHom u)`, both sides nonzero since `resHom u ≠ 0` and `φ = levelDropResHom` is a hom of
   FIELDS, hence injective), so `pval (θ x) = v` (bounds from both directions via `le_pval_iff`).
5. `θ u` is then a witness for `θ x` at valuation `v`; `resUnitResidue_eq_of_witness` finishes.

Discipline: no `sorry`/`axiom`/`native_decide`; `Mathlib` + `LevelDrop` + `ChildResidualExt`.
NEVER edits any existing file.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.LevelDropResidue

open Polynomial LeanUrat.OM LeanUrat.OM.UnramifiedBase LeanUrat.OM.LevelDrop
open LeanUrat.OM.ChildResidualExt

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime]

/-- **Residue reader is stable under the level drop below the cutoff.**

For `x : Oring(p, N+1, g')` with `pval x < N`, the residue reader commutes with the level-drop hom:
`resUnitResidue N g (levelDropHom x) = levelDropResHom (resUnitResidue (N+1) g' x)`.

The abstract-`Oring` hypotheses `hm` (positive degree), `hgirr` (irreducible reduced key at level
`N+1`) and the two `IsLocalRing` instances are the standing data the reader machinery
(`resUnitResidue_eq_of_witness`, `p_pow_ne_zero_of_lt`, `mem_span_p_of_mul_p_pow_eq_zero`) requires;
the target statement is meaningless without them. Irreducibility at level `N` is derived from level
`N+1` via `gbar_levelDrop`. -/
theorem resUnitResidue_levelDrop (g' : (ZMod (p ^ (N + 1)))[X]) (g : (ZMod (p ^ N))[X])
    (hgm' : g'.Monic) (hgm : g.Monic) (h1 : 0 < N + 1) (h2 : 0 < N)
    (hm' : 0 < g'.natDegree) (hgirr : Irreducible (gbar p (N + 1) g' h1))
    [IsLocalRing (Oring p (N + 1) g')] [IsLocalRing (Oring p N g)]
    (hgg : g'.map (levelDropCoeff p N) = g)
    (x : Oring p (N + 1) g')
    (hcut : pval_Oring p (N + 1) g' x < N) :
    resUnitResidue p N g hgm h2 (levelDropHom p N g' g hgg x)
      = levelDropResHom p N g' g h1 h2 hgg
          (resUnitResidue p (N + 1) g' hgm' h1 x) := by
  -- Notation.
  set θ := levelDropHom p N g' g hgg with hθ
  set φ := levelDropResHom p N g' g h1 h2 hgg with hφ
  set v := pval_Oring p (N + 1) g' x with hv
  -- Degree agreement `g.natDegree = g'.natDegree` (monic ⟹ natDegree preserved under `map`).
  haveI : Nontrivial (ZMod (p ^ N)) := nontrivial_base p N h2
  have hdeg : g.natDegree = g'.natDegree := by
    rw [← hgg]; exact hgm'.natDegree_map _
  have hm : 0 < g.natDegree := by rw [hdeg]; exact hm'
  -- Irreducibility at level `N` (transported from level `N+1` via `gbar_levelDrop`).
  have hgirrN : Irreducible (gbar p N g h2) := by
    rw [← gbar_levelDrop p N g' g h1 h2 hgg]; exact hgirr
  -- Step 1: `v ≤ N` (junk bound) and `x ≠ 0`.
  have hvle : v ≤ N := le_of_lt hcut
  have hx : x ≠ 0 := by
    intro h0
    rw [hv, h0, pval_zero p (N + 1) g'] at hcut
    omega
  -- Step 2: the witness `u` at level `N+1` with `u · p^v = x`.
  set u := pvalWitness p (N + 1) g' hgm' h1 x with hu
  have huspec : u * (((p : ℕ) : Oring p (N + 1) g') ^ v) = x :=
    pvalWitness_spec p (N + 1) g' hgm' h1 x
  -- `resUnitResidue (N+1) x = resHom (N+1) u` by definition of `resUnitResidue`/`pvalWitness`.
  have hres_def : resUnitResidue p (N + 1) g' hgm' h1 x
      = resHom p (N + 1) g' hgm' h1 u := rfl
  -- `u ∉ (p)`: else `x ∈ (p^{v+1})`, forcing `v+1 ≤ pval x = v`.
  have hu_notmem : u ∉ Ideal.span {((p : ℕ) : Oring p (N + 1) g')} := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    -- `x = u · p^v = w · p · p^v = w · p^{v+1}`
    have hxmem : x ∈ Ideal.span {((p : ℕ) : Oring p (N + 1) g') ^ (v + 1)} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨w, ?_⟩
      have hpc : ((p : ℕ) : Oring p (N + 1) g') ^ (v + 1)
          = ((p : ℕ) : Oring p (N + 1) g') ^ v * ((p : ℕ) : Oring p (N + 1) g') := pow_succ _ _
      rw [← huspec, hw, hpc]; ring
    have hle : v + 1 ≤ v := by
      have := (le_pval_iff p (N + 1) g' (by omega : v + 1 ≤ N + 1)).mpr hxmem
      rwa [← hv] at this
    omega
  -- `resHom (N+1) u ≠ 0` (`u ∉ (p) = ker resHom`).
  have hresu_ne : resHom p (N + 1) g' hgm' h1 u ≠ 0 := by
    intro h0
    apply hu_notmem
    rw [← ker_resHom_eq_span_p p (N + 1) g' hgm' h1, RingHom.mem_ker]
    exact h0
  -- Step 3: `θ x = θ u · p^v` (θ ring hom, `θ p = p`).
  have hθx : θ x = θ u * (((p : ℕ) : Oring p N g) ^ v) := by
    rw [hθ, ← huspec, map_mul, map_pow, map_natCast]
  -- Naturality: `resHom N (θ u) = φ (resHom (N+1) u)`.
  have hnat : resHom p N g hgm h2 (θ u) = φ (resHom p (N + 1) g' hgm' h1 u) := by
    have := resHom_natural_levelDrop p N g' g h1 h2 hgm' hgm hgg
    have := congrArg (fun (F : Oring p (N + 1) g' →+* resField p N g h2) => F u) this
    simpa [RingHom.comp_apply, hθ, hφ] using this
  -- `φ` is injective (nonzero ring hom of fields).
  have hφ_inj : Function.Injective φ := by
    haveI : Fact (Irreducible (gbar p (N + 1) g' h1)) := ⟨hgirr⟩
    haveI : Fact (Irreducible (gbar p N g h2)) := ⟨hgirrN⟩
    exact RingHom.injective φ
  -- `resHom N (θ u) ≠ 0` (φ injective, `resHom (N+1) u ≠ 0`).
  have hresθu_ne : resHom p N g hgm h2 (θ u) ≠ 0 := by
    rw [hnat]
    intro h0
    apply hresu_ne
    apply hφ_inj
    rw [h0, map_zero]
  -- `θ u ∉ (p)` at level `N` (ker resHom).
  have hθu_notmem : θ u ∉ Ideal.span {((p : ℕ) : Oring p N g)} := by
    intro hmem
    apply hresθu_ne
    rw [← RingHom.mem_ker, ker_resHom_eq_span_p p N g hgm h2]
    exact hmem
  -- Step 4 (crux): `pval N (θ x) = v`.
  have hpval_θx : pval_Oring p N g (θ x) = v := by
    apply le_antisymm
    · -- `pval (θ x) ≤ v`: else `v + 1 ≤ pval`, i.e. `θ x ∈ (p^{v+1})`, giving `θ u ∈ (p)`.
      by_contra hlt
      push_neg at hlt  -- `v < pval (θ x)`
      have hmem : θ x ∈ Ideal.span {((p : ℕ) : Oring p N g) ^ (v + 1)} :=
        (le_pval_iff p N g (by omega : v + 1 ≤ N)).mp hlt
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨w, hw⟩ := hmem
      -- `θ u · p^v = θ x = w · p^{v+1} = w · p · p^v`, so `(θ u - w·p)·p^v = 0`.
      have hzero : (θ u - w * ((p : ℕ) : Oring p N g)) * (((p : ℕ) : Oring p N g) ^ v) = 0 := by
        have hpc : ((p : ℕ) : Oring p N g) ^ (v + 1)
            = ((p : ℕ) : Oring p N g) ^ v * ((p : ℕ) : Oring p N g) := pow_succ _ _
        rw [sub_mul, ← hθx, hw, hpc]
        ring
      -- `v < N`, so `θ u - w·p ∈ (p)`, hence `θ u ∈ (p)`, contradiction.
      have hdiffmem : (θ u - w * ((p : ℕ) : Oring p N g)) ∈ Ideal.span {((p : ℕ) : Oring p N g)} :=
        mem_span_p_of_mul_p_pow_eq_zero p N g hgm h2 hm hgirrN hcut hzero
      apply hθu_notmem
      have : θ u = (θ u - w * ((p : ℕ) : Oring p N g)) + w * ((p : ℕ) : Oring p N g) := by ring
      rw [this]
      exact Ideal.add_mem _ hdiffmem
        (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    · -- `v ≤ pval (θ x)`: `θ x = θ u · p^v ∈ (p^v)`.
      apply (le_pval_iff p N g hvle).mpr
      rw [Ideal.mem_span_singleton, hθx]
      exact ⟨θ u, mul_comm _ _⟩
  -- Step 5: `θ x ≠ 0` (from `pval (θ x) = v < N` and `pval = N ↔ = 0`).
  have hθx_ne : θ x ≠ 0 := by
    intro h0
    have : pval_Oring p N g (θ x) = N := by rw [h0, pval_zero p N g]
    rw [hpval_θx] at this
    omega
  -- `θ u` is a witness for `θ x` at valuation `pval (θ x) = v`.
  have hwit : θ u * (((p : ℕ) : Oring p N g) ^ (pval_Oring p N g (θ x))) = θ x := by
    rw [hpval_θx, ← hθx]
  -- Step 6: `resUnitResidue N (θ x) = resHom N (θ u)` (witness independence), then naturality.
  rw [resUnitResidue_eq_of_witness p N g hgm h2 hm hgirrN hθx_ne hwit, hnat, ← hres_def]

end

end LeanUrat.OM.LevelDropResidue

/-! ## Axiom audit — must be ⊆ [propext, Classical.choice, Quot.sound]. -/

#print axioms LeanUrat.OM.LevelDropResidue.resUnitResidue_levelDrop
