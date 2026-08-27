/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C129
import Uniformity.ChapC.C130s6
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapC.C133mh8 — `[MH.8+X1, 2026-08-27]`: the Hensel-engine bounded-window
graded limit and the other-slope point-side lemma, promoted

**Nodes MH.8 and X1** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md`, the
`[MHG 2026-08-27]` amendment closing MHDISP gates 2–3; regrade
`runs/wave-b/verdict_MHG.md`; source `leanfinal/scratch/MHG_probe.lean`, green,
orchestrator-verified, zero `sorry`, zero declared `axiom`). Promotes the probe's GENERIC
content — every PROVED theorem — byte-identical apart from plumbing (namespace, opens,
import path, docstrings).

## What lands here

**MH.8, the bounded-window forward/reverse comparison and the assembled graded limit.**
Fix a frame `F`, a direction `(u, ℓ)` with `0 < ℓ`, and a degree window `a.natDegree < d`.
Write `D′ := F.e₁ * F.f₁` for the inner digit window, `A := ℓ * F.e₁` for the positive
scale, and `C_d := ℓ * F.h * (D′ - 1) + u * (d - 1)` for the fixed finite loss. Then:

* `inf_devGauss_le_gaussVal` — the least Gauss valuation of the key-development digits
  is at most that of the assembled polynomial (the public replacement for B.40's private
  helper).
* `stageHeight_le_gaussVal_add_loss` — on a single digit of degree `< D`, the stage
  height is at most the scaled Gauss valuation plus the finite loss `F.h * (D - 1)`.
* `dvSupp_le_scaled_gaussVal_add_window` (**MH8-U**) — the bounded-window upper
  comparison `W(a) ≤ ℓ • (F.e₁ • gaussVal a) + C_d`.
* `gaussVal_of_shifted_dvSupp` (**MH8-F**) — the forward conversion:
  `A * N + C_d ≤ W(a) ⟹ N ≤ gaussVal a`, with the `gaussVal a = ⊤` case split off so no
  subtraction at `⊤` is used.
* `reverseTransport` (**MH8-R**) — the reverse conversion `N ≤ gaussVal a ⟹ A * N ≤ W(a)`,
  built from the public `C118a.dvSupp_min_congr` against zero and public
  `C130s6.dvSupp_zero_eq_top`; it consumes no private B.40 helper.
* `exists_dvGradedLimit` — **MH.8, fully assembled**: a degree-bounded `W`-Cauchy
  sequence has a limit `P` in the same degree window with the same unshifted `dvSupp`
  tail estimate, via the subtraction-free subsequence `q(j) := p(A * j + C_d)`, public
  `Uniformity.Hensel.exists_adicLimit_of_degree_lt`, and one further telescope.

**X1 (OPEN-4), the other-slope point-side lemma.** `otherSlope_pointSide`: if `g` is
`(u', ℓ')`-pure and `u' * ℓ ≠ u * ℓ'`, then the `(u, ℓ)`-side of `g` is a single point
(`dvSideDeg = 0`) — in the stronger singleton-side form: every attaining abscissa at the
`(u, ℓ)` direction is the same endpoint (`0` or `n := g.natDegree / D′`), read off the
supporting-line convexity argument against the old direction's purity. The private
helpers `dvOnSide_weight_eq` and `onSide_weight_le_slot` are the equal-weight and
supporting-line inequalities this argument runs on.

## Honest scope: what does NOT land here

Theorem A (the dv-graded one-slope Hensel lift) and the rest of the engine assembly
remain open pending the separate MH.1 transcription (the corrected mixed residual product
law, node `C133mh1`) and the initialization/solve/perturbation nodes; MH.8's closure
repairs only the limit leg. No consumer of MH.8/X1 is transcribed here.

## Plumbing and DEPENDS

Import chain (`C35`, `C129`, `C130s6`, `Uniformity.HenselFactorization`) is the probe's,
reused verbatim; every cited public lemma (`C118a.dvSupp_min_congr`,
`C118a.smul_top_pos`, `C130s6.dvSupp_zero_eq_top`, `C130s6.min_dvSupp_le_dvSupp_add`,
`Uniformity.Hensel.coeffIdeal`/`mem_coeffIdeal`/`maximalIdeal_pow_eq_span`/
`exists_adicLimit_of_degree_lt`, `C35.dvOnSide_of_mem_dvSideSet`,
`C35.le_natDegree_div_of_mem_dvSideSet`) resolves through this import chain alone.
**Status:** sorry-free, zero new axiom, footprint Lean-core only — see the AxCheck
footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh8

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {pi : O}

/-! ## X1 — the other-slope point-side lemma (PROVED) -/

/-- Two finite points on the same `dv`-side have equal natural-number weights. -/
theorem dvOnSide_weight_eq {F : KeyFrame O pi} {f : Polynomial O} {u ell j k Hj Hk : Nat}
    (hj : DvOnSide F f u ell j) (hk : DvOnSide F f u ell k)
    (hHj : dvHgt F f j = (Hj : ENat)) (hHk : dvHgt F f k = (Hk : ENat)) :
    ell * Hj + u * j = ell * Hk + u * k := by
  have h := hj.1.symm.trans hk.1
  rw [hHj, hHk] at h
  simp only [nsmul_eq_mul] at h
  exact_mod_cast h

/-- Every finite slot lies weakly above the supporting line through an on-side base point. -/
theorem onSide_weight_le_slot {F : KeyFrame O pi} {f : Polynomial O}
    {u ell b j Hb Hj : Nat} (hbase : DvOnSide F f u ell b)
    (hjle : j <= f.natDegree) (hHb : dvHgt F f b = (Hb : ENat))
    (hHj : dvHgt F f j = (Hj : ENat)) :
    ell * Hb + u * b <= ell * Hj + u * j := by
  have hinf : dvSupp F f u ell <= ell • dvHgt F f j + (u * j : ENat) := by
    rw [dvSupp]
    exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hjle))
  rw [hbase.1, hHb, hHj] at hinf
  simp only [nsmul_eq_mul] at hinf
  exact_mod_cast hinf

/-- ★ **PROVED — X1 (OPEN-4).** A polynomial pure at one direction has a point side at
every distinct direction. The conclusion is stronger than `dvSideDeg = 0`: every
attaining abscissa at the second direction is the same endpoint (`0` or `n`). -/
theorem otherSlope_pointSide (F : KeyFrame O pi) {g : Polynomial O}
    {u ell u' ell' : Nat} (hpure : IsDvPure F g u' ell')
    (hslope : u' * ell ≠ u * ell')
    (hne : (dvSideSet F g u ell).Nonempty) :
    dvSideDeg F g u ell hne = 0 := by
  let n := g.natDegree / (F.e₁ * F.f₁)
  have hzero' : DvOnSide F g u' ell' 0 := dvOnSide_of_mem_dvSideSet hpure.1
  have hn' : DvOnSide F g u' ell' n := dvOnSide_of_mem_dvSideSet hpure.2
  obtain ⟨H0, hH0⟩ := ENat.ne_top_iff_exists.mp hzero'.2
  obtain ⟨Hn, hHn⟩ := ENat.ne_top_iff_exists.mp hn'.2
  have hH0' := hH0.symm
  have hHn' := hHn.symm
  have holdEnds : ell' * H0 = ell' * Hn + u' * n := by
    simpa only [Nat.mul_zero, Nat.add_zero] using
      dvOnSide_weight_eq hzero' hn' hH0' hHn'
  have hall : forall j, j ∈ dvSideSet F g u ell ->
      (u' * ell < u * ell' -> j = 0) ∧ (u * ell' < u' * ell -> j = n) := by
    intro j hj
    have hjcur := dvOnSide_of_mem_dvSideSet hj
    obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.mp hjcur.2
    have hHj' := hHj.symm
    have hjn : j <= n := le_natDegree_div_of_mem_dvSideSet F hj
    have hjdeg : j <= g.natDegree := le_trans hjn (Nat.div_le_self _ _)
    have hold0 : ell' * H0 <= ell' * Hj + u' * j :=
      onSide_weight_le_slot hzero' hjdeg hH0' hHj'
    have hcur0 : ell * Hj + u * j <= ell * H0 := by
      have h := onSide_weight_le_slot hjcur (Nat.zero_le _) hHj' hH0'
      simpa only [Nat.mul_zero, Nat.add_zero] using h
    have holdn : ell' * Hn + u' * n <= ell' * Hj + u' * j := by
      rw [← holdEnds]
      exact hold0
    have hcurn : ell * Hj + u * j <= ell * Hn + u * n := by
      have hnledeg : n <= g.natDegree := Nat.div_le_self _ _
      exact onSide_weight_le_slot hjcur hnledeg hHj' hHn'
    constructor
    · intro hs
      by_contra hj0
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      nlinarith
    · intro hs
      by_contra hjne
      have hjlt : j < n := lt_of_le_of_ne hjn hjne
      nlinarith
  have hsidesingle : forall j, j ∈ dvSideSet F g u ell ->
      j = dvSideMin F g u ell hne := by
    rcases lt_or_gt_of_ne hslope with hs | hs
    · intro j hj
      exact ((hall j hj).1 hs).trans ((hall _ (Finset.min'_mem _ _)).1 hs).symm
    · intro j hj
      exact ((hall j hj).2 hs).trans ((hall _ (Finset.min'_mem _ _)).2 hs).symm
  have hmaxmin : dvSideMax F g u ell hne = dvSideMin F g u ell hne :=
    hsidesingle _ (Finset.max'_mem _ _)
  simp [dvSideDeg, hmaxmin]

/-! ## MH.8: the bounded-window forward comparison (PROVED) -/

/-- The Gauss valuation of a monic polynomial is zero. -/
private theorem gaussVal_eq_zero_of_monic {p : Polynomial O} (hp : p.Monic) :
    gaussVal p = 0 := by
  refine le_antisymm ?_ (by simp)
  have h := gaussVal_le_addVal_coeff p p.natDegree
  rwa [hp.coeff_natDegree, addVal_one] at h

/-- Gauss valuation is ultrametric on a finite sum. -/
private theorem inf_gaussVal_le_gaussVal_sum (A : Nat -> Polynomial O) (K : Nat) :
    (Finset.range K).inf (fun t => gaussVal (A t)) <=
      gaussVal (∑ t ∈ Finset.range K, A t) := by
  induction K with
  | zero =>
      simp only [Finset.range_zero, Finset.inf_empty, Finset.sum_empty]
      exact le_of_eq (gaussVal_eq_top_iff.mpr rfl).symm
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.range_add_one, Finset.inf_insert]
      refine le_trans ?_ (min_gaussVal_le_gaussVal_add (∑ t ∈ Finset.range K, A t) (A K))
      rw [min_comm]
      exact min_le_min ih le_rfl

/-- ★ **PROVED.** The least Gauss valuation of the key-development digits is at most that
of the assembled polynomial. This is the public-proof replacement for B.40's private
helper. -/
theorem inf_devGauss_le_gaussVal (hpi : Irreducible pi) (F : KeyFrame O pi)
    (a : Polynomial O) {K : Nat} (hK : a.natDegree < K * F.key.natDegree) :
    (Finset.range K).inf (fun j => gaussVal (dev F.key a j)) <= gaussVal a := by
  have hterm : forall j,
      gaussVal (dev F.key a j) = gaussVal (dev F.key a j * F.key ^ j) := by
    intro j
    rw [gaussVal_mul hpi, gaussVal_eq_zero_of_monic (F.hmonic.pow j), add_zero]
  calc
    (Finset.range K).inf (fun j => gaussVal (dev F.key a j)) =
        (Finset.range K).inf (fun j => gaussVal (dev F.key a j * F.key ^ j)) := by
          simp only [hterm]
    _ <= gaussVal (∑ j ∈ Finset.range K, dev F.key a j * F.key ^ j) :=
      inf_gaussVal_le_gaussVal_sum _ K
    _ = gaussVal a := by
      have hkeypos : 0 < F.key.natDegree := by
        rw [F.hdeg]
        exact Nat.mul_pos F.he₁ F.hf₁
      rw [sum_dev_eq F.hmonic hkeypos a hK]

/-- ★ **PROVED.** The inner finite loss: on digits of degree `< D`, stage height is at
most scaled Gauss valuation plus `h*(D-1)`. -/
theorem stageHeight_le_gaussVal_add_loss (F : KeyFrame O pi) {A : Polynomial O} {D : Nat}
    (hD : 0 < D) (hdeg : A.natDegree < D) :
    F.stageHeight A <= F.e₁ • gaussVal A + ((F.h * (D - 1) : Nat) : ENat) := by
  classical
  rw [F.stageHeight_eq_inf, gaussVal]
  obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf (Finset.range (A.natDegree + 1))
    (by simp) (fun i => addVal O (A.coeff i))
  refine le_trans (Finset.inf_le hi) ?_
  have hCi : gaussVal (Polynomial.C (A.coeff i)) = addVal O (A.coeff i) := by
    simp [gaussVal]
  rw [hCi, hmin]
  gcongr
  have hiA : i <= A.natDegree := by
    have hi' := Finset.mem_range.mp hi
    omega
  have hiD : i <= D - 1 := by omega
  exact_mod_cast Nat.mul_le_mul_left F.h hiD

/-- ★ **PROVED — MH8-U, the bounded-window forward upper comparison.** On
`natDegree < d`, the exact fixed loss is `ell*h*(D'-1) + u*(d-1)`, where `D'=deg(key)=e1*f1`
controls the inner digit window and `d` controls the outer development window. -/
theorem dvSupp_le_scaled_gaussVal_add_window (hpi : Irreducible pi) (F : KeyFrame O pi)
    {u ell d : Nat} (hell : 0 < ell) {a : Polynomial O} (hdeg : a.natDegree < d) :
    dvSupp F a u ell <= ell • (F.e₁ • gaussVal a) +
      (((ell * F.h * (F.e₁ * F.f₁ - 1)) + u * (d - 1) : Nat) : ENat) := by
  classical
  by_cases ha : a = 0
  · subst a
    rw [gaussVal_eq_top_iff.mpr rfl, C118a.smul_top_pos F.he₁,
      C118a.smul_top_pos hell, top_add]
    exact le_top
  · let K := a.natDegree + 1
    have hKpos : 0 < K := Nat.succ_pos _
    have hkeypos : 0 < F.key.natDegree := by
      rw [F.hdeg]
      exact Nat.mul_pos F.he₁ F.hf₁
    have hKdeg : a.natDegree < K * F.key.natDegree := by
      calc a.natDegree < K := Nat.lt_succ_self _
        _ <= K * F.key.natDegree := Nat.le_mul_of_pos_right _ hkeypos
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_mem_eq_inf (Finset.range K)
      (by simp [K]) (fun j => gaussVal (dev F.key a j))
    have hjgauss : gaussVal (dev F.key a j) <= gaussVal a := by
      rw [← hjmin]
      exact inf_devGauss_le_gaussVal hpi F a hKdeg
    have hjA : j <= a.natDegree := by simpa [K] using Finset.mem_range.mp hj
    have hjd : j <= d - 1 := by omega
    have hdevdeg : (dev F.key a j).natDegree < F.e₁ * F.f₁ := by
      by_cases hzero : dev F.key a j = 0
      · rw [hzero, Polynomial.natDegree_zero]
        exact Nat.mul_pos F.he₁ F.hf₁
      · have h := degree_dev_lt F.hmonic hkeypos a j
        have hn := Polynomial.natDegree_lt_natDegree hzero h
        simpa [F.hdeg] using hn
    have hWterm : dvSupp F a u ell <= ell • dvHgt F a j + (u * j : ENat) := by
      rw [dvSupp]
      exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hjA))
    refine le_trans hWterm ?_
    rw [dvHgt]
    calc
      ell • F.stageHeight (dev F.key a j) + (u * j : ENat) <=
          ell • (F.e₁ • gaussVal (dev F.key a j) +
            ((F.h * (F.e₁ * F.f₁ - 1) : Nat) : ENat)) + (u * j : ENat) := by
              gcongr
              exact stageHeight_le_gaussVal_add_loss F
                (Nat.mul_pos F.he₁ F.hf₁) hdevdeg
      _ <= ell • (F.e₁ • gaussVal a) +
          (((ell * F.h * (F.e₁ * F.f₁ - 1)) + u * (d - 1) : Nat) : ENat) := by
            rw [nsmul_add]
            have hmain : ell • (F.e₁ • gaussVal (dev F.key a j)) <=
                ell • (F.e₁ • gaussVal a) := by gcongr
            calc
              ell • (F.e₁ • gaussVal (dev F.key a j)) +
                    ell • ((F.h * (F.e₁ * F.f₁ - 1) : Nat) : ENat) + (u * j : ENat) <=
                  ell • (F.e₁ • gaussVal a) +
                    ell • ((F.h * (F.e₁ * F.f₁ - 1) : Nat) : ENat) + (u * j : ENat) := by
                      gcongr
              _ <= ell • (F.e₁ • gaussVal a) +
                  (((ell * F.h * (F.e₁ * F.f₁ - 1)) + u * (d - 1) : Nat) : ENat) := by
                    have hloss :
                        ell • ((F.h * (F.e₁ * F.f₁ - 1) : Nat) : ENat) + (u * j : ENat) <=
                          (((ell * F.h * (F.e₁ * F.f₁ - 1)) +
                            u * (d - 1) : Nat) : ENat) := by
                      push_cast [nsmul_eq_mul]
                      have hnat := Nat.add_le_add_left (Nat.mul_le_mul_left u hjd)
                        (ell * F.h * (F.e₁ * F.f₁ - 1))
                      exact_mod_cast (by simpa [Nat.mul_assoc] using hnat)
                    rw [add_assoc]
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_left hloss (ell • (F.e₁ • gaussVal a))

/-- ★ **PROVED — MH8-F, the forward conversion.** The bounded-window upper comparison
cancels the fixed loss and turns a sufficiently shifted `dvSupp` floor into a Gauss
floor. -/
theorem gaussVal_of_shifted_dvSupp (hpi : Irreducible pi) (F : KeyFrame O pi)
    {u ell d N : Nat} (hell : 0 < ell) {a : Polynomial O} (hdeg : a.natDegree < d)
    (hW : (((ell * F.e₁ * N + ell * F.h * (F.e₁ * F.f₁ - 1) +
      u * (d - 1) : Nat) : ENat) <= dvSupp F a u ell)) :
    (N : ENat) <= gaussVal a := by
  have hupp := dvSupp_le_scaled_gaussVal_add_window hpi F (u := u) hell hdeg
  by_cases htop : gaussVal a = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hv] at hupp
    have hcast :
        ell • (F.e₁ • (v : ENat)) +
          (((ell * F.h * (F.e₁ * F.f₁ - 1)) + u * (d - 1) : Nat) : ENat) =
        ((ell * F.e₁ * v + ell * F.h * (F.e₁ * F.f₁ - 1) +
          u * (d - 1) : Nat) : ENat) := by
      push_cast [nsmul_eq_mul]
      ring
    rw [hcast] at hupp
    have hnat :
        ell * F.e₁ * N + ell * F.h * (F.e₁ * F.f₁ - 1) + u * (d - 1) <=
        ell * F.e₁ * v + ell * F.h * (F.e₁ * F.f₁ - 1) + u * (d - 1) := by
      exact_mod_cast hW.trans hupp
    have hNv : N <= v := by
      have hscale : 0 < ell * F.e₁ := Nat.mul_pos hell F.he₁
      nlinarith
    rw [← hv]
    exact_mod_cast hNv

/-- MH.8 forward comparison, exact public statement shape: the loss is fixed on the
degree window. `C` will be instantiated by `ell * F.h * (D' - 1) + u * d`. -/
def BoundedWindowUpperComparisonStatement : Prop :=
  forall (_hpi : Irreducible pi) (F : KeyFrame O pi) (u ell d N : Nat) (a : Polynomial O),
    0 < ell -> a.natDegree < d ->
    ((((ell * F.e₁ * N + ell * F.h * (F.e₁ * F.f₁ - 1) +
      u * (d - 1) : Nat) : ENat) <= dvSupp F a u ell) ->
      (N : ENat) <= gaussVal a)

/-- MH.8 reverse comparison, exact public statement shape. -/
def ReverseTransportStatement : Prop :=
  forall (_hpi : Irreducible pi) (F : KeyFrame O pi) (u ell N : Nat) (a : Polynomial O),
    0 < ell -> (N : ENat) <= gaussVal a ->
    (((F.e₁ * ell) * N : Nat) : ENat) <= dvSupp F a u ell

/-- ★ **PROVED — MH8-R, the reverse transport, from public API.** Coefficientwise `pi^N`
divisibility pushes back to the level-two support with scale `e1*ell`. -/
theorem reverseTransport (hpi : Irreducible pi) (F : KeyFrame O pi) (u : Nat)
    {ell N : Nat} (hell : 0 < ell) {a : Polynomial O}
    (hgauss : (N : ENat) <= gaussVal a) :
    (((F.e₁ * ell) * N : Nat) : ENat) <= dvSupp F a u ell := by
  have hdiv : forall i, pi ^ N ∣ a.coeff i := (le_gaussVal_iff hpi).mp hgauss
  have hcong := C118a.dvSupp_min_congr hpi F (A := a) (A' := 0)
    (N := N) (fun i => by simpa using hdiv i) u ell hell
  rw [C130s6.dvSupp_zero_eq_top F u hell, min_eq_right le_top] at hcong
  exact min_eq_right_iff.mp hcong

/-! ## MH.8 assembled limit (PROVED) -/

/-- Telescoping preserves the floor at the first index. -/
private theorem le_dvSupp_sub (F : KeyFrame O pi) {u ell : Nat} (hell : 0 < ell)
    (p : Nat -> Polynomial O)
    (hstep : forall k : Nat, (k : ENat) <= dvSupp F (p (k + 1) - p k) u ell)
    (a c : Nat) : (a : ENat) <= dvSupp F (p (a + c) - p a) u ell := by
  induction c with
  | zero =>
      simp only [Nat.add_zero, sub_self]
      rw [C130s6.dvSupp_zero_eq_top F u hell]
      exact le_top
  | succ c ih =>
      have hsplit : p (a + (c + 1)) - p a =
          (p (a + c + 1) - p (a + c)) + (p (a + c) - p a) := by
        rw [show a + (c + 1) = a + c + 1 from rfl]
        ring
      rw [hsplit]
      refine le_trans ?_ (C130s6.min_dvSupp_le_dvSupp_add F hell _ _)
      refine le_min ?_ ih
      have hac : (a : ENat) <= ((a + c : Nat) : ENat) := by
        exact_mod_cast Nat.le_add_right a c
      exact hac.trans (hstep (a + c))

section Complete

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- ★ **PROVED — MH.8, fully assembled.** A degree-bounded sequence Cauchy for `dvSupp`
has a limit in the same window, with the same unshifted `dvSupp` tail estimate. -/
theorem exists_dvGradedLimit (hpi : Irreducible pi) (F : KeyFrame O pi)
    {u ell : Nat} (hell : 0 < ell) (d : Nat) (p : Nat -> Polynomial O)
    (hdeg : forall k : Nat, (p k).natDegree < d)
    (hstep : forall k : Nat, (k : ENat) <= dvSupp F (p (k + 1) - p k) u ell) :
    exists P : Polynomial O, P.natDegree < d ∧
      forall k : Nat, (k : ENat) <= dvSupp F (P - p k) u ell := by
  classical
  let A := ell * F.e₁
  let C := ell * F.h * (F.e₁ * F.f₁ - 1) + u * (d - 1)
  have hApos : 0 < A := Nat.mul_pos hell F.he₁
  have hAge1 : 1 <= A := hApos
  have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (hdeg 0)
  have hqdeg : forall j : Nat, (p (A * j + C)).degree < (d : WithBot Nat) := by
    intro j
    by_cases hp : p (A * j + C) = 0
    · rw [hp]
      simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mp (hdeg _)
  have hqstep : forall j : Nat,
      p (A * (j + 1) + C) - p (A * j + C) ∈
        Uniformity.Hensel.coeffIdeal (IsLocalRing.maximalIdeal O ^ j) := by
    intro j
    have hidx : A * (j + 1) + C = (A * j + C) + A := by ring
    have hW : ((A * j + C : Nat) : ENat) <=
        dvSupp F (p (A * (j + 1) + C) - p (A * j + C)) u ell := by
      rw [hidx]
      exact le_dvSupp_sub F hell p hstep (A * j + C) A
    have hdiffdeg : (p (A * (j + 1) + C) - p (A * j + C)).natDegree < d :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (hdeg _) (hdeg _))
    have hGauss : (j : ENat) <=
        gaussVal (p (A * (j + 1) + C) - p (A * j + C)) := by
      apply gaussVal_of_shifted_dvSupp hpi F (u := u) hell hdiffdeg
      have heq : A * j + C =
          ell * F.e₁ * j + ell * F.h * (F.e₁ * F.f₁ - 1) + u * (d - 1) := by
        simp only [A, C]
        ring
      rw [← heq]
      exact hW
    rw [Uniformity.Hensel.mem_coeffIdeal]
    intro i
    rw [Uniformity.Hensel.maximalIdeal_pow_eq_span hpi, Ideal.mem_span_singleton]
    exact (le_gaussVal_iff hpi).mp hGauss i
  obtain ⟨P, hPdeg, hPlim⟩ :=
    Uniformity.Hensel.exists_adicLimit_of_degree_lt d (fun j => p (A * j + C)) hqdeg hqstep
  refine ⟨P, ?_, ?_⟩
  · by_cases hP : P = 0
    · rw [hP]
      simpa using hdpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hPdeg
  · intro k
    have hg : (k : ENat) <= gaussVal (P - p (A * k + C)) := by
      refine (le_gaussVal_iff hpi).mpr fun i => ?_
      have hmem := Uniformity.Hensel.mem_coeffIdeal.mp (hPlim k) i
      rwa [Uniformity.Hensel.maximalIdeal_pow_eq_span hpi, Ideal.mem_span_singleton] at hmem
    have hPqStrong : ((A * k : Nat) : ENat) <= dvSupp F (P - p (A * k + C)) u ell := by
      have hr := reverseTransport hpi F u hell hg
      simpa [A, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hr
    have hPq : (k : ENat) <= dvSupp F (P - p (A * k + C)) u ell :=
      le_trans (by exact_mod_cast Nat.le_mul_of_pos_left k hApos) hPqStrong
    have hkle : k <= A * k + C :=
      le_trans (Nat.le_mul_of_pos_left k hApos) (Nat.le_add_right _ _)
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hkle
    have hqk : (k : ENat) <= dvSupp F (p (A * k + C) - p k) u ell := by
      rw [hc]
      exact le_dvSupp_sub F hell p hstep k c
    have hdecomp : P - p k = (P - p (A * k + C)) + (p (A * k + C) - p k) := by ring
    rw [hdecomp]
    exact le_trans (le_min hPq hqk) (C130s6.min_dvSupp_le_dvSupp_add F hell _ _)

end Complete

end Uniformity.Density.Tower.C133mh8

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh8.dvOnSide_weight_eq
#print axioms Uniformity.Density.Tower.C133mh8.onSide_weight_le_slot
#print axioms Uniformity.Density.Tower.C133mh8.otherSlope_pointSide
#print axioms Uniformity.Density.Tower.C133mh8.inf_devGauss_le_gaussVal
#print axioms Uniformity.Density.Tower.C133mh8.stageHeight_le_gaussVal_add_loss
#print axioms Uniformity.Density.Tower.C133mh8.dvSupp_le_scaled_gaussVal_add_window
#print axioms Uniformity.Density.Tower.C133mh8.gaussVal_of_shifted_dvSupp
#print axioms Uniformity.Density.Tower.C133mh8.reverseTransport
#print axioms Uniformity.Density.Tower.C133mh8.exists_dvGradedLimit

end AxCheck
