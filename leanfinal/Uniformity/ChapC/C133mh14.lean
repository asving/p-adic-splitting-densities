/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C33Cite
import Uniformity.ChapC.C133mh4
import Uniformity.ChapC.C133mh8
import Uniformity.ChapC.C133mh10
import Uniformity.ChapC.C133mh13

/-!
# Uniformity.ChapC.C133mh14 — `[MH14T 2026-08-28]`: §8 assembly — `BlockFrontier` from `BlockContext`, carrying Theorem A

**Nodes MH.14-transport + MH.15-shape** (source of truth:
`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §8 "Proposed F1.H3 after A-C.20: current
`BlockFrontier` from `BlockContext`", ~line 966; Theorem A's statement §2 ~line 250).

## What this file lands

1. **MH.14-transport** (`residual_transport` + the product point-side law
   `dvSideDeg_mul_prod_eq_zero`): for a dissection `D` of `f` with `(L.u, L.ℓ) ∈ D.slopes`,
   the complement `Wf := D.below * ∏_{p ≠ (L.u, L.ℓ)} D.factor p` is monic with POINT
   `(L.u, L.ℓ)`-side — each other-slope factor is point-sided by X1
   (`C133mh8.otherSlope_pointSide`, fed by `D.hdistinct`), `D.below` by `D.hbelow`, and
   the product by Theorem M clause 2 (`C133mh3.dvSideDeg_mul`).  Then M clause 3
   (`C133mh3.dvResPoly_mul_gen`, τ = 1) gives `R(f) = R(G)·R(Wf)` with `R(Wf)` a NONZERO
   CONSTANT (degree = side degree = 0, constant coefficient ≠ 0 by
   `natDegree_dvResPoly`), hence a unit of `K[Z]`; so `L.r ∣ R(f) → L.r ∣ R(G)`.

2. **MH.15-shape** (`blockFrontier_of_context_of_theoremA`): `BlockContext L f` plus
   **Theorem A carried as the ONE explicit hypothesis** `hA : TheoremAStatement O`
   implies the signed `BlockFrontier L f` (`C35.lean:278-282`, consumed BYTE-AS-IS).
   §8's six steps: `hctx` unpacking → the C.33 cite `exists_dvDissection` + `hsides` at
   `(L.u, L.ℓ)` → the transport (1) → Theorem H0 (`C133mh10.dvResidualBezout`) on the
   MONIC `R(G)` (M-monic, `C133mh4.dvResPoly_monic_of_isDvPure`) → `hA` splits
   `G = g₁ * g₂` with exact residuals `L.r ^ m` / `s` → `g₁` is the frontier witness;
   maximality via `C133mh13.theoremC_placement` at `f = g₁ * g₂ * Wf`.

## Theorem A pinning record (the carried hypothesis, NOT proved here)

`TheoremAStatement` is transcribed from doc §2 "Theorem A" via its machine-checked
statement-shape elaboration `MHENS.EngineExistenceStatement`
(`scratch/MHENS_probe.lean:71-94`, byte-identical body; scratch is not importable, so the
shape is re-declared here under the MH.15 name).  Pinned choices, all from the probe:
* the strict floor `ℓ * ((F.e₁ * F.f₁) * F.h) < u` (the [MHDISP 2026-08-27] corrected
  form; all engine consumers carry it);
* `hpin : F.Pin H₀` (definitionally the raw `npHgt` equation, `C14a.lean:214` — the
  same pin `LevelDatum` carries);
* clause 2's degree associativity `ℓ * (F.e₁ * F.f₁) * G.natDegree`;
* clause 4's left-height pins as `ℕ∞`-casts of `u * natDegree`;
* clause 5's exact residual identities in ∀-PIN form (any side/pin witness reads the
  same residual — C.25's junk-total design, as in the signed Theorem B clause).

## Associativity/commutation bookkeeping (§8 step 6 vs `theoremC_placement`)

`theoremC_placement` takes `hsplit : f = P * Q * W`, i.e. `(P * Q) * W`.  The §8
factorization arrives as `f = G * Wf` (transport) with `G = g₁ * g₂` (Theorem A), so
`f = (g₁ * g₂) * Wf` is DEFINITIONALLY the `P * Q * W` shape at `P := g₁`, `Q := g₂`,
`W := Wf` — one `rw` chain, no `mul_comm` needed.  The witness divisibility
`g₁ ∣ f` re-associates once (`mul_assoc`).

## Cite discipline

`exists_dvDissection` (`C33Cite.lean:76`, allowlisted axiom, GN15 Thm 2.3 + FGMN
arXiv-v3 Thm 6.6) is consumed ONLY by `blockFrontier_of_context_of_theoremA` — it is the
single non-Lean-core name in that theorem's footprint.  The transport theorems are
Lean-core (AxCheck footer).

Sorry-free.  This closes the engine's F1.H3 shape MODULO Theorem A: when MH.5/7/9 land,
one application discharges `hA`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Tower.C133mh14

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — private plumbing (standing D9 convention, as in C133mh13) -/

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

private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

/-- Pin existence: the side-min abscissa of a nonempty side has FINITE level height
(`DvOnSide`'s second conjunct is exactly the finiteness guard, C.07). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 (dvOnSide_of_mem' (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-- The strict floor `ℓ·(D′·h) < u`, re-associated from `LevelDatum.hκ`'s `ℓ·D′·h < u`. -/
private theorem floor_assoc {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  have h := L.hκ; rw [mul_assoc] at h; exact h

/-- Point-sidedness (in ∀-pin form) transports across an equality of polynomials —
`subst` avoids the dependent-motive failure of rewriting under the `hne` binder. -/
private theorem dvSideDeg_eq_zero_congr {F : KeyFrame O π} {u ℓ : ℕ} {x y : Polynomial O}
    (hxy : x = y)
    (h : ∀ hne : (dvSideSet F y u ℓ).Nonempty, dvSideDeg F y u ℓ hne = 0) :
    ∀ hne : (dvSideSet F x u ℓ).Nonempty, dvSideDeg F x u ℓ hne = 0 := by
  subst hxy; exact h

/-- `dvResPoly` transports across an equality of polynomials: the two pins agree by
`ℕ∞`-cast injectivity, and the side/pin witnesses by proof irrelevance. -/
private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx = dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

/-! ## Part 1 — MH.14-transport: the complement is point-sided, the residual transports -/

/-- **Point sides are stable under `below · ∏` products** (Theorem M clause 2, iterated).
A monic `w` with point `(u,ℓ)`-side times a finite product of monic point-sided factors
is point-sided: side-degree additivity (`C133mh3.dvSideDeg_mul`) plus `Finset` induction
anchored at `w` (so the empty product never needs a side law for `1`). -/
theorem dvSideDeg_mul_prod_eq_zero
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {w : Polynomial O} (hw : w.Monic)
    (hwpt : ∀ hne : (dvSideSet F w u ℓ).Nonempty, dvSideDeg F w u ℓ hne = 0)
    (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → Polynomial O)
    (hmon : ∀ p ∈ s, (g p).Monic)
    (hpt : ∀ p ∈ s, ∀ hne : (dvSideSet F (g p) u ℓ).Nonempty,
      dvSideDeg F (g p) u ℓ hne = 0) :
    ∀ hne : (dvSideSet F (w * ∏ p ∈ s, g p) u ℓ).Nonempty,
      dvSideDeg F (w * ∏ p ∈ s, g p) u ℓ hne = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact dvSideDeg_eq_zero_congr (by simp) hwpt
  | @insert a s' ha ih =>
      have hga : (g a).Monic := hmon a (Finset.mem_insert_self a s')
      have hmon' : ∀ p ∈ s', (g p).Monic := fun p hp => hmon p (Finset.mem_insert_of_mem hp)
      have hpt' : ∀ p ∈ s', ∀ hne : (dvSideSet F (g p) u ℓ).Nonempty,
          dvSideDeg F (g p) u ℓ hne = 0 := fun p hp => hpt p (Finset.mem_insert_of_mem hp)
      have hws' : (w * ∏ p ∈ s', g p).Monic :=
        hw.mul (Polynomial.monic_prod_of_monic _ _ hmon')
      have hrest := ih hmon' hpt'
      refine dvSideDeg_eq_zero_congr (y := g a * (w * ∏ p ∈ s', g p)) ?_ ?_
      · rw [Finset.prod_insert ha]; ring
      · intro hne
        have hng := dvSideSet_nonempty F hga.ne_zero u hℓ
        have hnz := dvSideSet_nonempty F hws'.ne_zero u hℓ
        rw [C133mh3.dvSideDeg_mul hπ hh H₀ hpin hℓ hcop hfloor hga.ne_zero hws'.ne_zero
          hng hnz hne, hpt a (Finset.mem_insert_self a s') hng, hrest hnz]

/-- ★ **MH.14-transport (§8 step 3).**  For a dissection `D` of `f` with
`(L.u, L.ℓ) ∈ D.slopes`, writing `G := D.factor (L.u, L.ℓ)` and
`Wf := D.below * ∏_{p ∈ D.slopes.erase (L.u, L.ℓ)} D.factor p`:
`f = G * Wf`, `Wf` is monic with POINT `(L.u, L.ℓ)`-side, and `L.r`-divisibility of the
level residual transports from `f` to `G` (τ = 1 law + `R(Wf)` a unit). -/
theorem residual_transport
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {f : Polynomial O} (D : DvDissection F f)
    (hmem : (L.u, L.ℓ) ∈ D.slopes)
    (hne : (dvSideSet F f L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hrf : L.r ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp) :
    f = D.factor (L.u, L.ℓ) * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) ∧
    (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p).Monic ∧
    (∀ hneW : (dvSideSet F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ).Nonempty,
      dvSideDeg F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hneW = 0) ∧
    ∀ (hneG : (dvSideSet F (D.factor (L.u, L.ℓ)) L.u L.ℓ).Nonempty) (MG : ℕ)
      (hpG : dvHgt F (D.factor (L.u, L.ℓ)) (dvSideMin F (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG) = (MG : ℕ∞)),
      L.r ∣ dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG := by
  classical
  -- the factorization `f = G * Wf` (commute `below` past the slope factor)
  have hfGW : f = D.factor (L.u, L.ℓ)
      * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) := by
    calc f = D.below * ∏ p ∈ D.slopes, D.factor p := D.hprod
      _ = D.below * (D.factor (L.u, L.ℓ) * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) := by
          rw [Finset.mul_prod_erase D.slopes D.factor hmem]
      _ = D.factor (L.u, L.ℓ)
          * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) := by ring
  -- `Wf` is monic
  have hWmon : (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p).Monic :=
    D.hbelow_monic.mul (Polynomial.monic_prod_of_monic _ _
      (fun p hp => D.hmonic p (Finset.mem_of_mem_erase hp)))
  -- `Wf` is point-sided: X1 on each other-slope factor + `D.hbelow` + M clause 2
  have hWpt : ∀ hneW : (dvSideSet F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ).Nonempty,
      dvSideDeg F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hneW = 0 :=
    dvSideDeg_mul_prod_eq_zero hπ hh H₀ hpin L.hℓ L.hcop (floor_assoc L) D.hbelow_monic
      (D.hbelow L.u L.ℓ L.hℓ L.hcop (floor_assoc L))
      (D.slopes.erase (L.u, L.ℓ)) D.factor
      (fun p hp => D.hmonic p (Finset.mem_of_mem_erase hp))
      (fun p hp hne' => C133mh8.otherSlope_pointSide F
        (D.hpure p (Finset.mem_of_mem_erase hp))
        (D.hdistinct p (Finset.mem_of_mem_erase hp) (L.u, L.ℓ) hmem (Finset.ne_of_mem_erase hp))
        hne')
  refine ⟨hfGW, hWmon, hWpt, ?_⟩
  intro hneG MG hpG
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hGmon : (D.factor (L.u, L.ℓ)).Monic := D.hmonic _ hmem
  -- side data + pins for `Wf` and `G * Wf`
  have hnW : (dvSideSet F (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hWmon.ne_zero L.u L.hℓ
  obtain ⟨MW, hpW⟩ := exists_pin F hnW
  have hnGW : (dvSideSet F (D.factor (L.u, L.ℓ) * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p)) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F (hGmon.mul hWmon).ne_zero L.u L.hℓ
  obtain ⟨MGW, hpGW⟩ := exists_pin F hnGW
  -- Theorem M clause 3 (τ = 1): `R(G·Wf) = R(G)·R(Wf)`
  have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop (floor_assoc L)
    hGmon.ne_zero hWmon.ne_zero hneG hnW hnGW hpG hpW hpGW
  -- transport `R(f)` to `R(G·Wf)` across `hfGW`
  have hcongr := dvResPoly_congr F H₀ hpin hfGW hne hnGW hp hpGW
  -- `R(Wf)` is a nonzero constant, hence a unit of `K[Z]`
  have hWnd := natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hnW hpW
  have hW0 : (dvResPoly F H₀ hpin (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hnW MW hpW).natDegree = 0 := by
    rw [hWnd.1, hWpt hnW]
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hW0
  have hc0 : c ≠ 0 := fun h0 => hWnd.2 (by rw [← hc, h0, Polynomial.C_0, Polynomial.coeff_zero])
  obtain ⟨uw, huw⟩ : IsUnit (dvResPoly F H₀ hpin (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hnW MW hpW) := by
    rw [← hc]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  -- divisibility transfer: `L.r ∣ R(f) = R(G)·R(Wf)` and `R(Wf)` is a unit
  have hrGW : L.r ∣ dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG
      * dvResPoly F H₀ hpin (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hnW MW hpW := by
    rw [← hmul, ← hcongr]; exact hrf
  have hGid : dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG
      = dvResPoly F H₀ hpin (D.factor (L.u, L.ℓ)) L.u L.ℓ hneG MG hpG
        * dvResPoly F H₀ hpin (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p) L.u L.ℓ hnW MW hpW
        * (↑uw⁻¹ : Polynomial (F.stageField H₀ hpin)) := by
    rw [← huw, mul_assoc, Units.mul_inv, mul_one]
  rw [hGid]
  exact hrGW.mul_right _

/-! ## Part 2 — MH.15-shape: Theorem A's statement (the carried hypothesis) -/

/-- **Theorem A's exact §2 statement** (doc §2 ~line 250; the dv-graded one-slope Hensel
existence, B.41-shaped conclusion with exact residual identities in ∀-pin form).
Byte-identical to the machine-checked shape elaboration
`MHENS.EngineExistenceStatement` (`scratch/MHENS_probe.lean:71`); see the module header
for the pinning record.  Carried as a HYPOTHESIS by the assembly below — NOT proved
here; MH.5–MH.9 are its discharge path. -/
def TheoremAStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g : Polynomial O, g.Monic → 0 < g.natDegree → (F.e₁ * F.f₁) ∣ g.natDegree →
    IsDvPure F g u ℓ →
  ∀ (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)),
  ∀ G H : Polynomial (F.stageField H₀ hpin), G.Monic → H.Monic → IsCoprime G H →
    G.coeff 0 ≠ 0 → H.coeff 0 ≠ 0 →
    dvResPoly F H₀ hpin g u ℓ hne M₀ hp = G * H →
  ∃ g₁ g₂ : Polynomial O, g = g₁ * g₂ ∧ g₁.Monic ∧ g₂.Monic ∧
    g₁.natDegree = ℓ * (F.e₁ * F.f₁) * G.natDegree ∧
    g₂.natDegree = ℓ * (F.e₁ * F.f₁) * H.natDegree ∧
    IsDvPure F g₁ u ℓ ∧ IsDvPure F g₂ u ℓ ∧
    dvHgt F g₁ 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
    dvHgt F g₂ 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
    (∀ (hne₁ : (dvSideSet F g₁ u ℓ).Nonempty) (M₁ : ℕ)
      (hp₁ : dvHgt F g₁ (dvSideMin F g₁ u ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin g₁ u ℓ hne₁ M₁ hp₁ = G) ∧
    (∀ (hne₂ : (dvSideSet F g₂ u ℓ).Nonempty) (M₂ : ℕ)
      (hp₂ : dvHgt F g₂ (dvSideMin F g₂ u ℓ hne₂) = (M₂ : ℕ∞)),
      dvResPoly F H₀ hpin g₂ u ℓ hne₂ M₂ hp₂ = H)

/-! ## Part 3 — ★ MH.15: the §8 assembly -/

/-- ★ **MH.15 (§8 steps 1–6): `BlockContext` + Theorem A ⟹ `BlockFrontier`.**
The signed shapes (`BlockContext`, `BlockFrontier`, `C35.lean`) are consumed byte-as-is;
`hA` is Theorem A's exact §2 statement (one explicit hypothesis, see
`TheoremAStatement`); the C.33 cite `exists_dvDissection` is the ONLY non-Lean-core
name in the footprint.  This closes F1.H3 MODULO Theorem A. -/
theorem blockFrontier_of_context_of_theoremA
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {H₀ hpin} (L : LevelDatum F H₀ hpin) {f : Polynomial O}
    (hctx : BlockContext L f)
    (hA : TheoremAStatement O) :
    BlockFrontier L f := by
  classical
  -- STEP 1: unpack the context
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
  -- STEP 3: the residual transport (MH.14)
  obtain ⟨hfGW, hWmon, hWpt, htrans⟩ := residual_transport hπ hh L D hmem hne hp hrdvd
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
  -- STEP 5: Theorem A (the carried hypothesis) splits `G = g₁ * g₂`
  obtain ⟨g₁, g₂, hG12, hg₁mon, hg₂mon, hdeg₁, hdeg₂, hpure₁, hpure₂, hhgt₁, hhgt₂,
      hres₁, hres₂⟩ :=
    hA π F hπ hh H₀ hpin L.u L.ℓ L.hℓ L.hcop (floor_assoc L) (D.factor (L.u, L.ℓ))
      hGmon hGpos hGfd hGpure hneG MG hpG (L.r ^ m) s hrmmon hsmon hcoprm hrm0 hs0 hRGeq
  -- STEP 6: assemble the frontier witness `g₁` and its clauses
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
  -- the frontier: witness `g₁`, maximality via Theorem C at `f = g₁ * g₂ * Wf`
  refine ⟨g₁, hlab, ⟨g₂ * (D.below * ∏ p ∈ D.slopes.erase (L.u, L.ℓ), D.factor p),
    hsplit.trans (mul_assoc g₁ g₂ _)⟩, hfd₁, ?_⟩
  rintro fS' ⟨hlab', hpin'⟩ hdvd'
  exact C133mh13.theoremC_placement hπ hh L hfmon hsq hsplit hg₁mon hpure₁ hfd₁ hneP hpP
    hmpos (hres₁ hneP MP hpP) hg₂mon hpure₂ hfd₂ hneQ hpQ hQres hWmon hnW (hWpt hnW)
    hlab' hpin' hdvd'

end Uniformity.Density.Tower.C133mh14

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh14.dvSideDeg_mul_prod_eq_zero
#print axioms Uniformity.Density.Tower.C133mh14.residual_transport
#print axioms Uniformity.Density.Tower.C133mh14.TheoremAStatement
#print axioms Uniformity.Density.Tower.C133mh14.blockFrontier_of_context_of_theoremA

end AxCheck
