/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C109
import Uniformity.ChapC.C118a

/-!
# Uniformity.ChapC.C118b — the A-C.7 repair, clause 2: the guarded residual transport

**Amendment A-C.7's repair unit for NODE C.118, clause 2** (the frozen `dv2_read_congr_res`
is machine-refuted — `C118_REFUTATION.lean.txt` section 2, the degree-jump counterexample).
One public theorem, `dv2_read_congr_res_guarded`: the frozen binder list PLUS the two guards
that make the statement true.

## ⚠ Guard design — a CORRECTION to the drafted A-C.7 addendum (recorded for certification)

The addendum drafts the re-sign with the single guard `hsupp : dv2Supp < ℓ₂·W`
(`W = (F.e₁ * L.ℓ) * N`).  **That single guard is NOT sufficient**, by the same ⊤-slot
mechanism one layer down: `dv2ResPoly` consults every slot `min + t·ℓ₂`, `t ≤ deg` —
including INTERIOR slots that are off-side — and `dv2Res` reads each consulted block at the
block's OWN level-1 side data, not at the level-2 side line.  An interior slot whose block
is `0` in the member `a` (read `0`, the junk branch) can carry a `π^N`-perturbation block in
`a'` whose own pin is finite (`≥ W`, unseen by `hsupp`) and whose read is NONZERO — C.26's
`natDegree_dvResPoly` forces every pinned block's residual constant term to be nonzero, so
the perturbed read cannot vanish.  Designed instance (same carrier as the refutation file):
`a = X³ + X² + π^M·X` vs `a' = a + π^N` at `(u₂, ℓ₂)` with `u₂ < e₁ℓN`... interior slot 1;
the polynomials differ at coefficient 1 (`0` vs a nonzero read).  Hence the second guard
`hslots`, bounding the pin of EVERY consulted slot of the visible member strictly below `W`:
it excludes both the `⊤`-hole and the above-window reads.  At the section-2 counterexample
`hslots` fails at `t = 0` (the slot-`0` pin of `X²` is `⊤`), and at the interior-slot
instance it fails at `t = 1`; both exclusions are sharp.

`hvis` and `hseam` of the frozen list are RETAINED for binder compatibility but are not
consumed by the proof (B77a's unused-`hd` precedent); the honest minimal form is the
orchestrator's re-sign decision.

## Route

1. `dv2Supp` capped congruence at `(u₂, ℓ₂)` (the C118a capped-pin law rides up the second
   `inf`-layer), then raw equality under `hsupp`.
2. Side-set transfer: per abscissa, an on-side term sits at the support (`< ℓ₂·W`, so its
   pin is `< W` and transports raw); an off-side term either transports raw or both sides
   sit `≥ ℓ₂·W > supp`.  Hence `dv2SideSet`, `dv2SideMin`, `dv2SideMax`, `dv2SideDeg` all
   transfer.
3. Per-slot read transfer under `hslots`: each consulted block has pin `< W = L.ℓ·(e₁N)`,
   i.e. its own level-1 support sits below the level-1 cap; the C118a capped chain gives its
   side set / `M₀` / degree transfer, and the reads bottom out in `digAt` digits at
   positions `< N` (C109's class-level digit calculus `digAt_congr`), so `twistRead`,
   `dvResPoly`, and `dv2Res` all transport.
4. Assemble `dv2ResPoly` coefficientwise.

## Status

Sorry-free, axiom-free (Lean core only): `#print axioms dv2_read_congr_res_guarded` prints
`[propext, Classical.choice, Quot.sound]`.  The leanspec A-C.7 clause-2 re-sign is the
orchestrator's separate step, gated on this module AND on the section-2 refutation record
(certify-BEFORE-sign).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C118b

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. capped-min plumbing (B77a's private extraction lemmas, at a general cap) -/

/-- below the cap the truncated congruence is an honest equality. -/
theorem eq_of_min_eq_of_lt {a b W : ℕ∞} (h : min a W = min b W) (ha : a < W) : b = a := by
  rw [min_eq_left ha.le] at h
  rcases min_cases b W with ⟨hb, _⟩ | ⟨hb, _⟩
  · rw [hb] at h
    exact h.symm
  · rw [hb] at h
    exact absurd ha (by simp [h])

/-- at or above the cap the truncated congruence transports the bound. -/
theorem le_of_min_eq_of_le {a b W : ℕ∞} (h : min a W = min b W) (ha : W ≤ a) : W ≤ b := by
  rw [min_eq_right ha] at h
  exact h.trans_le (min_le_left b W)

/-- a cleared term below a cleared cap has its height below the cap. -/
theorem lt_of_smul_le_of_lt {x S W : ℕ∞} {ℓ : ℕ} (h1 : ℓ • x ≤ S) (h2 : S < ℓ • W) :
    x < W := by
  by_contra hcon
  push_neg at hcon
  exact absurd (lt_of_le_of_lt (le_trans (nsmul_le_nsmul_right hcon ℓ) h1) h2) (lt_irrefl _)

/-- the per-term capped congruence: a cleared-and-offset term reads its height only through
the cap. -/
theorem smul_add_min_congr {W x x' : ℕ∞} (hcap : min x W = min x' W) (ℓ : ℕ) (c : ℕ∞) :
    min (ℓ • x + c) (ℓ • W) = min (ℓ • x' + c) (ℓ • W) := by
  rcases lt_or_ge x W with hx | hx
  · rw [eq_of_min_eq_of_lt hcap hx]
  · have hx' : W ≤ x' := le_of_min_eq_of_le hcap hx
    have h1 : ℓ • W ≤ ℓ • x + c :=
      le_trans (nsmul_le_nsmul_right hx ℓ) (le_add_of_nonneg_right zero_le)
    have h2 : ℓ • W ≤ ℓ • x' + c :=
      le_trans (nsmul_le_nsmul_right hx' ℓ) (le_add_of_nonneg_right zero_le)
    rw [min_eq_right h1, min_eq_right h2]

/-- the capped congruence rides up an `inf` of cleared-and-offset terms. -/
theorem inf_min_congr {M : ℕ} {W : ℕ∞} {h h' : ℕ → ℕ∞}
    (hcap : ∀ j, min (h j) W = min (h' j) W) (u ℓ : ℕ) :
    min ((Finset.range (M + 1)).inf fun j => ℓ • h j + (u * j : ℕ∞)) (ℓ • W)
      = min ((Finset.range (M + 1)).inf fun j => ℓ • h' j + (u * j : ℕ∞)) (ℓ • W) := by
  rw [C118a.min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩,
    C118a.min_inf_eq ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩]
  exact Finset.inf_congr rfl fun j _ => smul_add_min_congr (hcap j) ℓ _

/-- transporting a `min'` along a proved set equality. -/
theorem min'_congr {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst hst
  rfl

/-- transporting a `max'` along a proved set equality. -/
theorem max'_congr {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by
  subst hst
  rfl

/-! ### 2. the level-2 side transfer under the support guard -/

/-- the cast bridge `↑(ℓ₂·W) = ℓ₂ • ↑W`. -/
theorem cast_mul_smul (ℓ₂ w : ℕ) : ((ℓ₂ * w : ℕ) : ℕ∞) = ℓ₂ • ((w : ℕ) : ℕ∞) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- the capped `dv2Supp` congruence at an arbitrary side `(u₂, ℓ₂)`: the C118a capped-pin
law rides up the second `inf` layer. -/
theorem dv2Supp_min_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') (u₂ ℓ₂ : ℕ) :
    min (dv2Supp L Ψ (monicPoly a) u₂ ℓ₂) ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)
      = min (dv2Supp L Ψ (monicPoly a') u₂ ℓ₂) ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞) := by
  have hcap : ∀ j, min (dv2Pin L Ψ (monicPoly a) j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)
      = min (dv2Pin L Ψ (monicPoly a') j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) :=
    fun j => dv2_read_congr_min L hπ hc j
  rw [dv2Supp, dv2Supp, monicPoly_natDegree a, monicPoly_natDegree a', cast_mul_smul]
  exact inf_min_congr hcap u₂ ℓ₂

/-- raw `dv2Supp` equality under the support guard. -/
theorem dv2Supp_congr_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') {u₂ ℓ₂ : ℕ}
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)) :
    dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ = dv2Supp L Ψ (monicPoly a') u₂ ℓ₂ := by
  have hmin := dv2Supp_min_congr L hπ (Ψ := Ψ) hc u₂ ℓ₂
  rw [min_eq_left hsupp.le] at hmin
  rcases min_cases (dv2Supp L Ψ (monicPoly a') u₂ ℓ₂) ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)
    with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at hmin
    exact hmin
  · rw [h1] at hmin
    exact absurd (hmin ▸ hsupp) (lt_irrefl _)

/-- side-set transfer under the support guard. -/
theorem dv2SideSet_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a') {u₂ ℓ₂ : ℕ}
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞)) :
    dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂ = dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂ := by
  classical
  have hS := dv2Supp_congr_of_lt L hπ (Ψ := Ψ) hc hsupp
  have hcap : ∀ j, min (dv2Pin L Ψ (monicPoly a) j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)
      = min (dv2Pin L Ψ (monicPoly a') j) (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) :=
    fun j => dv2_read_congr_min L hπ hc j
  have hsupp' : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂
      < ℓ₂ • (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) := by
    rw [← cast_mul_smul]
    exact hsupp
  ext j
  simp only [dv2SideSet, Dv2OnSide, Finset.mem_filter, Finset.mem_range,
    monicPoly_natDegree a, monicPoly_natDegree a']
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hon, hnetop⟩
    have hle : ℓ₂ • dv2Pin L Ψ (monicPoly a) j ≤ dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ := by
      rw [hon]
      exact le_add_of_nonneg_right zero_le
    have hpj : dv2Pin L Ψ (monicPoly a) j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) :=
      lt_of_smul_le_of_lt hle hsupp'
    have hpe : dv2Pin L Ψ (monicPoly a') j = dv2Pin L Ψ (monicPoly a) j :=
      eq_of_min_eq_of_lt (hcap j) hpj
    refine ⟨?_, ?_⟩
    · rw [← hS, hpe]
      exact hon
    · rw [hpe]
      exact hnetop
  · rintro ⟨hon', hnetop'⟩
    have hle' : ℓ₂ • dv2Pin L Ψ (monicPoly a') j ≤ dv2Supp L Ψ (monicPoly a') u₂ ℓ₂ := by
      rw [hon']
      exact le_add_of_nonneg_right zero_le
    have hpj' : dv2Pin L Ψ (monicPoly a') j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) := by
      refine lt_of_smul_le_of_lt hle' ?_
      rw [← hS]
      exact hsupp'
    have hpe : dv2Pin L Ψ (monicPoly a) j = dv2Pin L Ψ (monicPoly a') j :=
      eq_of_min_eq_of_lt (hcap j).symm hpj'
    refine ⟨?_, ?_⟩
    · rw [hS, hpe]
      exact hon'
    · rw [hpe]
      exact hnetop'

/-! ### 3. the level-1 block transfer below the window -/

/-- `dvSideSet` seen over any extended range (added abscissae are never on-side: their
heights are `⊤`). -/
theorem dvSideSet_ext_range (F : KeyFrame O π) (A : Polynomial O) (u ℓ : ℕ)
    {M : ℕ} (hM : A.natDegree ≤ M) :
    dvSideSet F A u ℓ
      = open Classical in (Finset.range (M + 1)).filter (fun j => DvOnSide F A u ℓ j) := by
  classical
  ext j
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hon⟩
    exact ⟨by omega, hon⟩
  · rintro ⟨hj, hon⟩
    refine ⟨?_, hon⟩
    by_contra hcon
    push_neg at hcon
    exact hon.2 (C118a.dvHgt_top_of_gt F A (by omega))

/-- raw level-1 `dvSupp` equality below the window. -/
theorem dvSupp_congr_of_lt (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (hcg : ∀ i, π ^ N ∣ (A - A').coeff i) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hlt : dvSupp F A u ℓ < (((F.e₁ * ℓ) * N : ℕ) : ℕ∞)) :
    dvSupp F A u ℓ = dvSupp F A' u ℓ := by
  have hmin := C118a.dvSupp_min_congr hπ F hcg u ℓ hℓ
  rw [min_eq_left hlt.le] at hmin
  rcases min_cases (dvSupp F A' u ℓ) (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at hmin
    exact hmin
  · rw [h1] at hmin
    exact absurd (hmin ▸ hlt) (lt_irrefl _)

/-- level-1 side-set transfer below the window. -/
theorem dvSideSet_congr_of_lt (hπ : Irreducible π) (F : KeyFrame O π) {N : ℕ}
    {A A' : Polynomial O} (hcg : ∀ i, π ^ N ∣ (A - A').coeff i) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hlt : dvSupp F A u ℓ < (((F.e₁ * ℓ) * N : ℕ) : ℕ∞)) :
    dvSideSet F A u ℓ = dvSideSet F A' u ℓ := by
  classical
  have hS := dvSupp_congr_of_lt hπ F hcg hℓ hlt
  have hcap : ∀ j, min (dvHgt F A j) ((F.e₁ * N : ℕ) : ℕ∞)
      = min (dvHgt F A' j) ((F.e₁ * N : ℕ) : ℕ∞) := C118a.dvHgt_min_congr hπ F hcg
  have hsm : (((F.e₁ * ℓ) * N : ℕ) : ℕ∞) = ℓ • ((F.e₁ * N : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hlt' : dvSupp F A u ℓ < ℓ • ((F.e₁ * N : ℕ) : ℕ∞) := by
    rw [← hsm]
    exact hlt
  set M := max A.natDegree A'.natDegree with hM
  rw [dvSideSet_ext_range F A u ℓ (le_max_left _ _),
    dvSideSet_ext_range F A' u ℓ (le_max_right _ _)]
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, DvOnSide]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hon, hnetop⟩
    have hle : ℓ • dvHgt F A j ≤ dvSupp F A u ℓ := by
      rw [hon]
      exact le_add_of_nonneg_right zero_le
    have hpj : dvHgt F A j < ((F.e₁ * N : ℕ) : ℕ∞) := lt_of_smul_le_of_lt hle hlt'
    have hpe : dvHgt F A' j = dvHgt F A j := eq_of_min_eq_of_lt (hcap j) hpj
    refine ⟨?_, ?_⟩
    · rw [← hS, hpe]
      exact hon
    · rw [hpe]
      exact hnetop
  · rintro ⟨hon', hnetop'⟩
    have hle' : ℓ • dvHgt F A' j ≤ dvSupp F A' u ℓ := by
      rw [hon']
      exact le_add_of_nonneg_right zero_le
    have hpj' : dvHgt F A' j < ((F.e₁ * N : ℕ) : ℕ∞) := by
      refine lt_of_smul_le_of_lt hle' ?_
      rw [← hS]
      exact hlt'
    have hpe : dvHgt F A j = dvHgt F A' j := eq_of_min_eq_of_lt (hcap j).symm hpj'
    refine ⟨?_, ?_⟩
    · rw [hS, hpe]
      exact hon'
    · rw [hpe]
      exact hnetop'

/-- the ϖ-read transports below the window: `twistRead` at a height `k < e₁N` only reads
the class mod `π^N` (C109's `digAt_congr` at every window digit). -/
theorem twistRead_congr (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {N : ℕ} {B B' : Polynomial O} (hcg : ∀ i, π ^ N ∣ (B - B').coeff i)
    {k : ℕ} (hk : k < F.e₁ * N) :
    F.twistRead H₀ hpin k B = F.twistRead H₀ hpin k B' := by
  have hslot : F.slotRes H₀ hpin k B = F.slotRes H₀ hpin k B' := by
    rw [KeyFrame.slotRes, KeyFrame.slotRes]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hm : (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ < N := by
      have h1 : (k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁ ≤ k / F.e₁ :=
        Nat.div_le_div_right (Nat.sub_le _ _)
      have h2 : k / F.e₁ < N := Nat.div_lt_of_lt_mul hk
      omega
    have hdig : digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
          (B.coeff (F.slotIdx k + F.e₁ * t))
        = digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
          (B'.coeff (F.slotIdx k + F.e₁ * t)) := by
      have hN : (π : O) ^ N ∣ (B'.coeff (F.slotIdx k + F.e₁ * t)
          - B.coeff (F.slotIdx k + F.e₁ * t)) := by
        have := hcg (F.slotIdx k + F.e₁ * t)
        rw [Polynomial.coeff_sub] at this
        simpa using this.neg_right
      exact C109asm.digAt_congr hπ (dvd_trans (pow_dvd_pow π (Nat.succ_le_of_lt hm)) hN)
    rw [hdig]
  rw [KeyFrame.twistRead, KeyFrame.twistRead, hslot]

/-- the level residual polynomial transports below the window (same `M₀`, both side reads
pinned). -/
theorem dvResPoly_congr (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {N : ℕ} {A A' : Polynomial O} (hcg : ∀ i, π ^ N ∣ (A - A').coeff i) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) (hlt : dvSupp F A u ℓ < (((F.e₁ * ℓ) * N : ℕ) : ℕ∞))
    (hne₂ : (dvSideSet F A u ℓ).Nonempty) (hne₂' : (dvSideSet F A' u ℓ).Nonempty)
    {M₀ M₀' : ℕ} (hM : M₀ = M₀') (hMlt : M₀ < F.e₁ * N)
    (hpin₂ : dvHgt F A (dvSideMin F A u ℓ hne₂) = (M₀ : ℕ∞))
    (hpin₂' : dvHgt F A' (dvSideMin F A' u ℓ hne₂') = (M₀' : ℕ∞)) :
    dvResPoly F H₀ hpin A u ℓ hne₂ M₀ hpin₂ = dvResPoly F H₀ hpin A' u ℓ hne₂' M₀' hpin₂' := by
  subst hM
  have hset := dvSideSet_congr_of_lt hπ F hcg hℓ hlt
  have hmin : dvSideMin F A u ℓ hne₂ = dvSideMin F A' u ℓ hne₂' := min'_congr hset _ _
  have hmax : dvSideMax F A u ℓ hne₂ = dvSideMax F A' u ℓ hne₂' := max'_congr hset _ _
  have hdeg : dvSideDeg F A u ℓ hne₂ = dvSideDeg F A' u ℓ hne₂' := by
    rw [dvSideDeg, dvSideDeg, hmin, hmax]
  rw [dvResPoly, dvResPoly, ← hdeg, ← hmin]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hread : F.twistRead H₀ hpin (M₀ - t * u) (dev F.key A (dvSideMin F A u ℓ hne₂ + t * ℓ))
      = F.twistRead H₀ hpin (M₀ - t * u) (dev F.key A' (dvSideMin F A u ℓ hne₂ + t * ℓ)) := by
    refine twistRead_congr F hπ H₀ hpin (dev_congr hπ F.hmonic hcg _) ?_
    omega
  rw [hread]

set_option maxHeartbeats 1000000 in
/-- **block-level read transfer**: a consulted block whose own level pin sits below the
window has the same coherent `dv2Res` read on both members. -/
theorem dv2Res_congr_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π)
    {N : ℕ} {A A' : Polynomial O} (hcg : ∀ i, π ^ N ∣ (A - A').coeff i)
    (hlt : dvSupp F A L.u L.ℓ < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)) :
    dv2Res L A = dv2Res L A' := by
  classical
  have hS := dvSupp_congr_of_lt hπ F hcg L.hℓ hlt
  have hset := dvSideSet_congr_of_lt hπ F hcg L.hℓ hlt
  have hsm : (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞) = L.ℓ • ((F.e₁ * N : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hlt' : dvSupp F A L.u L.ℓ < L.ℓ • ((F.e₁ * N : ℕ) : ℕ∞) := by
    rw [← hsm]
    exact hlt
  -- the A-side existence data
  have hneA : (dvSideSet F A L.u L.ℓ).Nonempty := by
    obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_inf (Finset.range (A.natDegree + 1))
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
      (fun j => L.ℓ • dvHgt F A j + (L.u * j : ℕ∞))
    have hsupp_eq : dvSupp F A L.u L.ℓ = L.ℓ • dvHgt F A j₀ + (L.u * j₀ : ℕ∞) := by
      rw [dvSupp]
      exact hj₀
    have htop : dvHgt F A j₀ ≠ ⊤ := by
      intro hcon
      rw [hcon, C118a.smul_top_pos L.hℓ, top_add] at hsupp_eq
      rw [hsupp_eq] at hlt
      exact absurd hlt (by simp)
    exact ⟨j₀, by
      simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨Finset.mem_range.1 hj₀mem, hsupp_eq, htop⟩⟩
  have hminmem : dvSideMin F A L.u L.ℓ hneA ∈ dvSideSet F A L.u L.ℓ := Finset.min'_mem _ _
  have hminon : DvOnSide F A L.u L.ℓ (dvSideMin F A L.u L.ℓ hneA) := by
    have := hminmem
    simp only [dvSideSet, Finset.mem_filter] at this
    exact this.2
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, dvHgt F A (dvSideMin F A L.u L.ℓ hneA) = (M₀ : ℕ∞) := by
    rcases (WithTop.ne_top_iff_exists).1 hminon.2 with ⟨m, hm⟩
    exact ⟨m, hm.symm⟩
  -- M₀ sits below the window
  have hMlt : M₀ < F.e₁ * N := by
    have hle : L.ℓ • dvHgt F A (dvSideMin F A L.u L.ℓ hneA) ≤ dvSupp F A L.u L.ℓ := by
      rw [hminon.1]
      exact le_add_of_nonneg_right zero_le
    have := lt_of_smul_le_of_lt hle hlt'
    rw [hM₀] at this
    exact_mod_cast this
  -- the A'-side data
  have hneA' : (dvSideSet F A' L.u L.ℓ).Nonempty := hset ▸ hneA
  have hminA' : dvSideMin F A' L.u L.ℓ hneA' = dvSideMin F A L.u L.ℓ hneA :=
    (min'_congr hset hneA hneA').symm
  have hM₀' : dvHgt F A' (dvSideMin F A' L.u L.ℓ hneA') = (M₀ : ℕ∞) := by
    rw [hminA']
    have hcap := C118a.dvHgt_min_congr hπ F hcg (dvSideMin F A L.u L.ℓ hneA)
    have hlow : dvHgt F A (dvSideMin F A L.u L.ℓ hneA) < ((F.e₁ * N : ℕ) : ℕ∞) := by
      rw [hM₀]
      exact_mod_cast hMlt
    rw [← hM₀]
    exact eq_of_min_eq_of_lt hcap hlow
  have hexA : ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M₀ : ℕ∞) := ⟨hneA, M₀, hM₀⟩
  have hexA' : ∃ (hne : (dvSideSet F A' L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F A' (dvSideMin F A' L.u L.ℓ hne) = (M₀ : ℕ∞) := ⟨hneA', M₀, hM₀'⟩
  rw [dv2Res, dv2Res, dif_pos hexA, dif_pos hexA']
  -- the two chosen `M₀`s are the pins' unique numerals
  have hMA : hexA.choose_spec.choose = M₀ := by
    have h1 : dvHgt F A (dvSideMin F A L.u L.ℓ hexA.choose)
        = (hexA.choose_spec.choose : ℕ∞) := hexA.choose_spec.choose_spec
    have h2 : dvHgt F A (dvSideMin F A L.u L.ℓ hexA.choose) = (M₀ : ℕ∞) := hM₀
    exact_mod_cast (h1.symm.trans h2)
  have hMA' : hexA'.choose_spec.choose = M₀ := by
    have h1 : dvHgt F A' (dvSideMin F A' L.u L.ℓ hexA'.choose)
        = (hexA'.choose_spec.choose : ℕ∞) := hexA'.choose_spec.choose_spec
    have h2 : dvHgt F A' (dvSideMin F A' L.u L.ℓ hexA'.choose) = (M₀ : ℕ∞) := hM₀'
    exact_mod_cast (h1.symm.trans h2)
  congr 1
  refine dvResPoly_congr F hπ H₀ hpin hcg L.hℓ hlt _ _ (hMA.trans hMA'.symm) ?_ _ _
  rw [hMA]
  exact hMlt

end Uniformity.Density.Tower.C118b

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **A-C.7, clause 2′ — the guarded residual transport.**  The frozen clause-2 binders,
PLUS the support guard `hsupp` (side sets transfer) and the consulted-slot guard `hslots`
(every read the residual polynomial consults sits below the window).  Both guards are
sharp at the two machine/designed counterexamples — see the module docstring. -/
theorem dv2_read_congr_res_guarded {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂).Nonempty)
    (hsupp : dv2Supp L Ψ (monicPoly a) u₂ ℓ₂ < ((ℓ₂ * ((F.e₁ * L.ℓ) * N) : ℕ) : ℕ∞))
    (hslots : ∀ t, t ≤ dv2SideDeg L Ψ (monicPoly a) u₂ ℓ₂ hne →
      dv2Pin L Ψ (monicPoly a) (dv2SideMin L Ψ (monicPoly a) u₂ ℓ₂ hne + t * ℓ₂)
        < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)) :
    dv2ResPoly L Ψ (monicPoly a) u₂ ℓ₂ hne = dv2ResPoly L Ψ (monicPoly a') u₂ ℓ₂ hne' := by
  classical
  have hcg : ∀ i, π ^ N ∣ (monicPoly a - monicPoly a').coeff i :=
    C118a.monicPoly_coeff_congr hπ hc
  have hset := C118b.dv2SideSet_congr L hπ hc hsupp
  have hmin : dv2SideMin L Ψ (monicPoly a) u₂ ℓ₂ hne
      = dv2SideMin L Ψ (monicPoly a') u₂ ℓ₂ hne' := C118b.min'_congr hset _ _
  have hmax : dv2SideMax L Ψ (monicPoly a) u₂ ℓ₂ hne
      = dv2SideMax L Ψ (monicPoly a') u₂ ℓ₂ hne' := C118b.max'_congr hset _ _
  have hdeg : dv2SideDeg L Ψ (monicPoly a) u₂ ℓ₂ hne
      = dv2SideDeg L Ψ (monicPoly a') u₂ ℓ₂ hne' := by
    rw [dv2SideDeg, dv2SideDeg, hmin, hmax]
  rw [dv2ResPoly, dv2ResPoly, ← hdeg, ← hmin]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hts : t ≤ dv2SideDeg L Ψ (monicPoly a) u₂ ℓ₂ hne := by
    rw [Finset.mem_range] at ht
    omega
  have hres : dv2Res L (dev Ψ (monicPoly a) (dv2SideMin L Ψ (monicPoly a) u₂ ℓ₂ hne + t * ℓ₂))
      = dv2Res L (dev Ψ (monicPoly a') (dv2SideMin L Ψ (monicPoly a) u₂ ℓ₂ hne + t * ℓ₂)) := by
    refine C118b.dv2Res_congr_of_lt L hπ (C118a.dev_blocks_congr hπ hcg Ψ _) ?_
    exact hslots t hts
  rw [hres]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2_read_congr_res_guarded

end AxCheck
