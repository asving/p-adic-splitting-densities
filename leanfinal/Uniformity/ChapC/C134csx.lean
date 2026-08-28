/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh9

/-!
# Uniformity.ChapC.C134csx — `[CSX 2026-08-28]`: the exported context-split theorem
(UNIT CSX — the F1.2–F1.8 unblocker)

`runs/wave-c/verdict_CFS.md` identified the head-blocker for the whole F1.2–F1.8 family:
`C133mh14.blockFrontier_of_context_of_theoremA`'s proof (§8 steps 3-6) *constructs* the
full context split `f = g₁ * g₂ * Wf` — `g₁` the labelled pure block (= `blockFactor L f`
once matched against C.35's selector), `g₂` its complement with a NON-`r`-divisible
residual, `Wf` the point-sided below/other-slope product — but the exported theorem
(`BlockFrontier L f`) drops `g₂` and `Wf` at the door: only existence + maximality + the
`D′` rider survive. F1.2 `block_complement_notdvd` and its F1.3–F1.8 descendants all need
exactly this dropped internal data. This file re-exports it as a standalone public
theorem, `context_split`.

## What this file lands

`context_split` — Route 1 (RE-DERIVE) of the charge: replays `C133mh14`'s §8 steps 1-6
verbatim (STEP 3 via the already-PUBLIC `C133mh14.residual_transport` +
`C133mh14.dvSideDeg_mul_prod_eq_zero`; STEP 4 via H0 = `C133mh10.dvResidualBezout` on the
M-monic residual `C133mh4.dvResPoly_monic_of_isDvPure`; STEP 5 via the now-UNCONDITIONAL
`C133mh9.theoremA`), but instead of packaging the witness into `BlockFrontier` and
discarding `(g₂, Wf)`, it identifies the witness `g₁` with C.35's `blockFactor L f` (via
`blockFactor_eq_of_frontier`, the same identification `C134cfs.lean`'s
`keyDeg₁_dvd_blockFactor_natDegree` uses) and returns `(g₂, Wf)` together with the
clauses F1.2–F1.8 need: monicity of both, `Wf` point-sided at `(L.u, L.ℓ)`, and the
∀-pin non-divisibility of `g₂`'s residual by `L.r`.

The five private plumbing lemmas from `C133mh14` Part 0 that STEP 2/4 need
(`isKey_X`, `localFieldStageField`, `floor_assoc`, `dvOnSide_of_mem'`, `exists_pin`) are
private there and hence unreachable across files; they are re-declared here
byte-identical in mechanism, credited per declaration (`C133mh14.lean` never edited).
`C133mh14.residual_transport` and `C133mh14.dvSideDeg_mul_prod_eq_zero` themselves are
PUBLIC in `C133mh14` and are consumed directly, not re-derived.

## Cite discipline

The only non-Lean-core name in the footprint is the allowlisted C.33 dissection cite
`exists_dvDissection` (`C33Cite.lean:76`), consumed exactly once (STEP 2), inherited
through `C133mh14.residual_transport`'s dependencies exactly as in `blockFrontier_of_context_of_theoremA`.
`C133mh9.theoremA` consumes no cite (Lean-core). Sorry-free; no statement/definition in
any landed file touched.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Tower.C134csx

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-! ## Part 0 — private plumbing, re-declared from `C133mh14` Part 0 (credited; that file
untouched). None of this is new mathematics. -/

/-- Local D9 reconstruction (source: `C133mh14.lean`'s private `isKey_X`). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- The strict floor `ℓ·D′·h < u`, re-associated from `LevelDatum.hκ`'s `ℓ·D′·h < u`
(source: `C133mh14.lean`'s private `floor_assoc`). -/
private theorem floor_assoc {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  have h := L.hκ; rw [mul_assoc] at h; exact h

/-- Membership in `dvSideSet` unpacks `DvOnSide` (source: `C133mh14.lean`'s private
`dvOnSide_of_mem'`). -/
private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

/-- Pin existence: the side-min abscissa of a nonempty side has FINITE level height
(source: `C133mh14.lean`'s private `exists_pin`). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 (dvOnSide_of_mem' (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-! ## Part 1 — the exported context split -/

set_option maxHeartbeats 1600000 in
/-- ★ **`context_split` (UNIT CSX, the F1.2–F1.8 unblocker).** Under `BlockContext L f`,
`f` splits as `blockFactor L f * g₂ * Wf` with `g₂` and `Wf` monic, `Wf` point-sided at
`(L.u, L.ℓ)`, and `g₂`'s residual NOT divisible by `L.r` at every pin — exactly the
internal data `C133mh14.blockFrontier_of_context_of_theoremA`'s proof constructs
(§8 steps 3-6) and drops at the `BlockFrontier` export. This re-export is the head
unblocker the corpus sweep (`runs/wave-c/verdict_CFS.md`) named for F1.2
`block_complement_notdvd` and its F1.3–F1.8 descendants. -/
theorem context_split {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    ∃ g₂ Wf : Polynomial O,
      f = blockFactor L f * g₂ * Wf ∧
      g₂.Monic ∧ Wf.Monic ∧
      (∀ hneW : (dvSideSet F Wf L.u L.ℓ).Nonempty, dvSideDeg F Wf L.u L.ℓ hneW = 0) ∧
      ∀ (hne₂ : (dvSideSet F g₂ L.u L.ℓ).Nonempty) (M₂ : ℕ)
        (hp₂ : dvHgt F g₂ (dvSideMin F g₂ L.u L.ℓ hne₂) = (M₂ : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g₂ L.u L.ℓ hne₂ M₂ hp₂ := by
  classical
  -- STEP 1: unpack the context (verbatim as `C133mh14`'s STEP 1)
  obtain ⟨hfmon, hsq, hkey, hne, M₀, hp, hpos, hrdvd⟩ := hctx
  -- STEP 2: the C.33 dissection (the ONE cite consumption) + `hsides` at `(L.u, L.ℓ)`
  obtain ⟨D⟩ := exists_dvDissection F hπ hfmon hkey
  have hmem : (L.u, L.ℓ) ∈ D.slopes :=
    (D.hsides L.u L.ℓ L.hℓ L.hcop (floor_assoc L)).2 ⟨hne, hpos⟩
  have hGmon : (D.factor (L.u, L.ℓ)).Monic := D.hmonic _ hmem
  have hGpure : IsDvPure F (D.factor (L.u, L.ℓ)) L.u L.ℓ := D.hpure _ hmem
  have hGdeg : (D.factor (L.u, L.ℓ)).natDegree
      = (F.e₁ * F.f₁) * (L.ℓ * dvSideDeg F f L.u L.ℓ hne) := D.hdeg _ hmem hne
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hGpos : 0 < (D.factor (L.u, L.ℓ)).natDegree := by
    rw [hGdeg]; exact Nat.mul_pos hDpos (Nat.mul_pos L.hℓ hpos)
  have hGfd : (F.e₁ * F.f₁) ∣ (D.factor (L.u, L.ℓ)).natDegree := ⟨_, hGdeg⟩
  -- STEP 3: the residual transport (MH.14, PUBLIC — consumed, not re-derived)
  obtain ⟨hfGW, hWmon, hWpt, htrans⟩ :=
    C133mh14.residual_transport hπ hh L D hmem hne hp hrdvd
  have hneG : (dvSideSet F (D.factor (L.u, L.ℓ)) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hGmon.ne_zero L.u L.hℓ
  obtain ⟨MG, hpG⟩ := exists_pin F hneG
  have hrG : L.r ∣ dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG :=
    htrans hneG MG hpG
  -- STEP 4: Theorem H0 on the MONIC `R(G)` (M-monic)
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hRGmon : (dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG).Monic :=
    C133mh4.dvResPoly_monic_of_isDvPure F hπ hh H₀ hpin hGmon hGpos L.hℓ L.hcop hGpure
      hGfd hneG hpG
  have hRG0 : (dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG).coeff 0 ≠ 0 :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hneG hpG).2
  obtain ⟨m, s, hRGeq, hnrs, hmpos, hs0, hcoprm, hmonics⟩ :=
    C133mh10.dvResidualBezout hRGmon.ne_zero hRG0 L.hrmonic L.hrirr L.hr0 L.hrdeg hrG
  obtain ⟨hrmmon, hsmon⟩ := hmonics hRGmon
  have hrm0 : (L.r ^ m).coeff 0 ≠ 0 := by
    have hpow : (L.r ^ m).coeff 0 = L.r.coeff 0 ^ m := by
      rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply]
    rw [hpow]; exact pow_ne_zero m L.hr0
  -- STEP 5: Theorem A — now UNCONDITIONAL (`C133mh9.theoremA`), splits `G = g₁ * g₂`
  obtain ⟨g₁, g₂, hG12, hg₁mon, hg₂mon, hdeg₁, hdeg₂, hpure₁, hpure₂, hhgt₁, hhgt₂,
      hres₁, hres₂⟩ :=
    C133mh9.theoremA π F hπ hh H₀ hpin L.u L.ℓ L.hℓ L.hcop (floor_assoc L)
      (D.factor (L.u, L.ℓ)) hGmon hGpos hGfd hGpure hneG MG hpG (L.r ^ m) s hrmmon hsmon
      hcoprm hrm0 hs0 hRGeq
  -- STEP 6: assemble the split, then identify the witness `g₁` with `blockFactor L f`
  have hsplit : f = g₁ * g₂ * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) :=
    hfGW.trans (by rw [hG12])
  have hdr : (L.r ^ m).natDegree = m * L.r.natDegree := L.hrmonic.natDegree_pow m
  have hg₁pos : 0 < g₁.natDegree := by
    rw [hdeg₁, hdr]
    exact Nat.mul_pos (Nat.mul_pos L.hℓ hDpos) (Nat.mul_pos hmpos L.hrdeg)
  have hfd₁ : (F.e₁ * F.f₁) ∣ g₁.natDegree := by
    rw [hdeg₁]; exact ⟨L.ℓ * (L.r ^ m).natDegree, by ring⟩
  have hfd₂ : (F.e₁ * F.f₁) ∣ g₂.natDegree := by
    rw [hdeg₂]; exact ⟨L.ℓ * s.natDegree, by ring⟩
  have hneP : (dvSideSet F g₁ L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hg₁mon.ne_zero L.u L.hℓ
  obtain ⟨MP, hpP⟩ := exists_pin F hneP
  have hlab : HasLabel L g₁ :=
    ⟨hg₁mon, hg₁pos, hpure₁, hneP, MP, hpP, m, hmpos, hres₁ hneP MP hpP⟩
  have hneQ : (dvSideSet F g₂ L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hg₂mon.ne_zero L.u L.hℓ
  obtain ⟨MQ, hpQ⟩ := exists_pin F hneQ
  have hQres : ¬ L.r ∣ dvResPoly F H₀ hpin g₂ L.u L.ℓ hneQ MQ hpQ := by
    rw [hres₂ hneQ MQ hpQ]; exact hnrs
  have hnW : (dvSideSet F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hWmon.ne_zero L.u L.hℓ
  have hg₁dvd : g₁ ∣ f :=
    ⟨g₂ * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p),
      hsplit.trans (mul_assoc g₁ g₂ _)⟩
  have hmax : ∀ fS' : Polynomial O,
      (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ g₁ := by
    rintro fS' ⟨hlab', hpin'⟩ hdvd'
    exact C133mh13.theoremC_placement hπ hh L hfmon hsq hsplit hg₁mon hpure₁ hfd₁ hneP hpP
      hmpos (hres₁ hneP MP hpP) hg₂mon hpure₂ hfd₂ hneQ hpQ hQres hWmon hnW (hWpt hnW)
      hlab' hpin' hdvd'
  have hbf : blockFactor L f = g₁ := blockFactor_eq_of_frontier L hlab hfd₁ hg₁dvd hmax
  -- assemble the export: `g₂` and `Wf := D.below * ∏_{p ≠ (L.u,L.ℓ)} D.factor p`
  refine ⟨g₂, D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p, by rw [hbf]; exact hsplit,
    hg₂mon, hWmon, hWpt, ?_⟩
  intro hne₂ M₂ hp₂
  rw [hres₂ hne₂ M₂ hp₂]
  exact hnrs

end Uniformity.Density.Tower.C134csx

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134csx.context_split

end AxCheck
