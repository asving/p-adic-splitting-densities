/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Development
import LeanUrat.OM.RphiRingGenH
import LeanUrat.OM.RphiGenHCount
import LeanUrat.OM.RestartEquiv

/-!
# RestartEquivGenH — wave W6b-h: THE GENERAL-`h` single-block RESTART EQUIVALENCE

**Provenance.** `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §1 (the unified fresh
cluster pattern), §2 (refuted naive forms — guardrails), §6 (W6b-h bullet). The MATH is fully
gate-verified (0-mismatch): `/workspace-vast/asving/tmp/phaseb_w6h/`. This is the direct analogue
of the (referee-gap) `h = 1` `RestartEquiv.restartEquiv`, ported to GENERAL `h ≥ 1`
(`gcd(e,h) = 1`).

**Setting** (order 1, `f = 1`, general `h`, W6a's banked `RphiRingGenH` layer): `c : (ZMod (p^N))ˣ`
the lift of the residual root `c̄`, `φ = X^e − c·p^h` (`RphiRing.phi`, general `h`), the single
sloped side of vphi-slope `−h/e`, width `s = e·μ`, left vertex height `H = h·μ`, residual
`(y − c̄)^μ`: path `[(0, h·μ), (μ·e, 0)]`, shape `[(1, μ)]`. The child ring is the GAPPED general-`h`
`Rphi` (W6a); the fresh pattern uses `filtIdeal` (NOT `θ`-powers — §2 guardrail) and is
RESIDUE-FREE (§1/§2).

**Deliverables.**
1. `FreshClusterPatternGenH β := ∀ j, β_j ∈ filtIdeal(e·h·(μ−j)+1)` + `card_freshPatternGenH`
   (the per-digit product `∏_j ∏_i p^(N − min N ⌈(w−ih)/e⌉⁺)` via `RphiGenHCount.card_filtIdeal`).
2. `restartDigitsGenH` — `developEquiv` (φ = X^e − c·p^h, `k = μ, m = e`) ∘ `digitEquiv` per digit.
3. **THE DICTIONARY** `inCellAtGenH_iff_pattern`: `InCellAtGenH f ↔ FreshClusterPatternGenH
   (restartDigitsGenH' f)`. The cap `φ^μ` carries vertex-exactness + binomial residues
   `C(μ,t)(−c·p^h)^(μ−t)` (the `p^h` cap); the digits carry only the strict `dexp` floors. The
   `⟹` crux (`slotPattern_of_coeffCondGenH`, the triangular converse) CLOSES; `gcd(e,h)=1` enters
   only via the diagonal identity `dexp_pattern_pos`.
4. `restartEquivGenH : {f // InCellAtGenH f} ≃ {β // FreshClusterPatternGenH β}` +
   `card_restartGenH_fiber` (Deliverable 1 transported).
5. **MARGIN + collapse**: every fiber lemma carries `h·μ < N` (blueprint §1 emptiness, the
   h-scaled F1 left-endpoint-readability); `card_restartGenH_fiber_h_one_collapse` reduces the
   `h = 1` case to `RestartEquiv.card_restart_fiber`'s closed form (`gate_S_h_one_matches_banked`).

**Gates** (phaseb_w6h, 0-mismatch): `gate_G1` (3,2,2) N=5 fiber 4096; `gate_H` (2,3,2) N=7 fiber
1024; `gate_S_h_one` (2,1,2) N=3 fiber 16 collapsing to the banked value.

**Box size spelling.** `μ * e` (not `e * μ`): `developEquiv` produces `monicBox p N (k * m)` at
`k = μ, m = e`, so `μ * e` avoids a propositional cast; the sloped path endpoint is `(μ*e, 0)`.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprint
`[propext, Classical.choice, Quot.sound]` (checked with `#print axioms`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.RestartEquivGenH

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.CellCard
open LeanUrat.OM.RphiRing
open LeanUrat.OM.RphiRingGenH
open LeanUrat.OM.RphiGenHCount
open LeanUrat.OM.Development

variable (p N e h μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## Deliverable 1: `FreshClusterPatternGenH` and its cardinality -/

section Pattern

/-- **Deliverable 1 — the gate-verified general-`h` fresh cluster pattern** (blueprint §1):
PURE `filtIdeal` membership, e·h-SCALED, STRICT (`+1`), RESIDUE-FREE. The floor scales by the
full `vL`-slope `e·h` (the `vL`-avatar of the parent vphi-slope `−h/e`). No exactness/residue
condition at any slot; the parent's endpoint pins are carried by the cap `φ^μ`, not the digits.
Uses `filtIdeal` (gapped for `h ≥ 2`), NOT `θ`-powers (blueprint §2 guardrail). -/
def FreshClusterPatternGenH (β : Fin μ → Rphi p N e h c) : Prop :=
  ∀ j : Fin μ, β j ∈ filtIdeal p N e h c (e * h * (μ - j.1) + 1)

/-- **Deliverable 1, per-slot product form** (banked FIRST, per the spec): the pattern space is
the product of the per-slot filtration ideals, each counted by `card_filtIdeal`. -/
theorem card_freshPatternGenH (hN : 0 < N) (he : 0 < e) :
    Nat.card {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β}
      = ∏ j : Fin μ, ∏ i : Fin e,
          p ^ (N - min N (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ))) := by
  haveI := finite_Rphi p N e h c hN he
  have e1 : {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β}
      ≃ ∀ j : Fin μ,
        {x : Rphi p N e h c // x ∈ filtIdeal p N e h c (e * h * (μ - j.1) + 1)} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e1, Nat.card_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact card_filtIdeal p N e h c hN he (e * h * (μ - j.1) + 1)

end Pattern

/-! ## The general-`h` restart cell and root-refined membership `InCellAtGenH` -/

section Cell

open LeanUrat.OM.OMCountV2 (NodeConfig)

/-- The residual root: the residue of the lift `c` (h-independent — same as the h=1 template). -/
def cbar : ZMod p := RestartEquiv.cbar p N c

/-- The single sloped side of vphi-slope `−h/e`, width `e·μ`, left vertex height `h·μ`:
`[(0, h·μ), (e·μ, 0)]`. -/
def restartPathGenH : List (ℕ × ℕ) := [(0, h * μ), (μ * e, 0)]

/-- The general-`h` restart menu cell: single side of slope `−h/e`, residual shape `{(1, μ)}`. -/
def restartCellGenH : NodeConfig := mkCell (μ * e) (restartPathGenH e h μ) [[(1, μ)]]

theorem sideDeg_restartGenH (hcop : Nat.Coprime e h) :
    sideDeg ((0, h * μ), (μ * e, 0)) = μ := by
  show Nat.gcd (h * μ - 0) (μ * e - 0) = μ
  rw [Nat.sub_zero, Nat.sub_zero, Nat.mul_comm h μ, Nat.gcd_mul_left,
    (Nat.coprime_comm.mp hcop), Nat.mul_one]

theorem sideE_restartGenH (hμ : 0 < μ) (hcop : Nat.Coprime e h) :
    CellCard.sideE ((0, h * μ), (μ * e, 0)) = e := by
  show (μ * e - 0) / sideDeg ((0, h * μ), (μ * e, 0)) = e
  rw [sideDeg_restartGenH e h μ hcop, Nat.sub_zero]
  exact Nat.mul_div_cancel_left e hμ

/-- The column ceiling of the sloped restart path: `ceilAt i = h·μ − ⌊h·i/e⌋`. -/
theorem ceilAt_restartGenH (hμ : 0 < μ) (i : ℕ) (hi : i ≤ μ * e) :
    ceilAt (restartPathGenH e h μ) i = h * μ - h * i / e := by
  show (if i ≤ 0 then h * μ
      else if i ≤ μ * e then h * μ - (h * μ - 0) * (i - 0) / (μ * e - 0)
      else ceilAt [(μ * e, 0)] i) = h * μ - h * i / e
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos (le_refl 0), Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
  · rw [if_neg (by omega), if_pos hi]
    congr 1
    simp only [Nat.sub_zero]
    -- (h*μ)*i / (μ*e) = (h*i)/e
    rw [show h * μ * i = μ * (h * i) by ring]
    exact Nat.mul_div_mul_left (h * i) e hμ

theorem restartPath_menuPathGenH (hμ : 0 < μ) (hhμN : h * μ < N) (he : 0 < e) (hh : 0 < h) :
    MenuPath (μ * e) N (restartPathGenH e h μ) :=
  have hpos : 0 < h * μ := Nat.mul_pos hh hμ
  ⟨h * μ, (μ * e, 0), [], rfl, by omega, by omega, Nat.mul_pos hμ he, by omega,
    ChainOK.nil rfl rfl⟩

theorem restartShapesGenH (hμ : 0 < μ) (hcop : Nat.Coprime e h) :
    ShapesFor (restartPathGenH e h μ) [[(1, μ)]] := by
  show List.Forall₂ _ [[(1, μ)]] (sidePairs (restartPathGenH e h μ))
  rw [show sidePairs (restartPathGenH e h μ) = [((0, h * μ), (μ * e, 0))] from rfl]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [sideDeg_restartGenH e h μ hcop, mem_shapesOfDegree_iff]
  refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨le_refl 1, hμ⟩
  · simp

/-- **The root-refined general-`h` cell membership**: `f` matches the general-`h` menu cell AND
its side residual is exactly `(X − c̄)^μ` (the root pin genuinely refines at `p ≥ 3`). -/
def InCellAtGenH (f : QuotientBox.monicBox p N (μ * e)) : Prop :=
  InCell p f (restartCellGenH e h μ) ∧
    residualOf p f ((0, h * μ), (μ * e, 0)) = (X - C (RestartEquiv.cbar p N c)) ^ μ

/-- The side polynomial of a digit vector on the restart side is the pinned target iff every
vertex read is the matching binomial residue (h-independent structure). -/
theorem sidePolyR_eq_target_iff (hμ : 0 < μ) (hcop : Nat.Coprime e h)
    (rr : Fin (μ * e) → ZMod p) :
    sidePolyR p rr ((0, h * μ), (μ * e, 0)) = (X - C (RestartEquiv.cbar p N c)) ^ μ
      ↔ ∀ k : ℕ, k < μ → rho p rr (k * e) = RestartEquiv.bres p N μ c k := by
  have hIdx : ∀ k : ℕ,
      ((0, h * μ), (μ * e, 0)).1.1 + k * CellCard.sideE ((0, h * μ), (μ * e, 0)) = k * e := fun k => by
    rw [sideE_restartGenH e h μ hμ hcop]
    show 0 + k * e = k * e
    exact Nat.zero_add _
  constructor
  · intro hsp k hk
    have h2 : (sidePolyR p rr ((0, h * μ), (μ * e, 0))).coeff k
        = ((X - C (RestartEquiv.cbar p N c)) ^ μ).coeff k := by rw [hsp]
    rw [sidePolyR_coeff, sideDeg_restartGenH e h μ hcop, hIdx k,
      RestartEquiv.target_coeff p N μ c k, if_pos (by omega)] at h2
    exact h2
  · intro hfun
    ext k
    rw [sidePolyR_coeff, sideDeg_restartGenH e h μ hcop, hIdx k, RestartEquiv.target_coeff p N μ c k]
    by_cases hk : k < μ
    · rw [if_pos (by omega)]
      exact hfun k hk
    · by_cases hkμ : k = μ
      · subst hkμ
        rw [if_pos (le_refl k), rho_ge p rr (by rw [Nat.mul_comm]; omega)]
        unfold RestartEquiv.bres
        rw [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero]
      · rw [if_neg (by omega)]
        unfold RestartEquiv.bres
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- The vertex reads of the ceiling-digit vector are the level-`(h(μ−k))` digits. -/
theorem rho_restart_readGenH (he : 0 < e) (hμ : 0 < μ) (f : QuotientBox.monicBox p N (μ * e))
    (k : ℕ) (hk : k < μ) :
    rho p (fun i : Fin (μ * e) =>
        digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) (k * e)
      = digit p N (h * (μ - k)) ((f.1).coeff (k * e)) := by
  have hke : k * e < μ * e := (Nat.mul_lt_mul_right he).mpr hk
  rw [rho_lt p _ hke]
  show digit p N (ceilAt (restartPathGenH e h μ) (k * e)) ((f.1).coeff (k * e)) = _
  rw [ceilAt_restartGenH e h μ hμ (k * e) (le_of_lt hke)]
  congr 1
  -- h*μ − h*(k*e)/e = h*(μ−k)
  rw [show h * (k * e) = h * k * e by ring, Nat.mul_div_cancel _ he, Nat.mul_sub]

end Cell

/-! ## The x-adic coefficient formula of the φ-adic assembly (general `h`)

`f = φ^μ + Σ_j b_j φ^j` with `φ = X^e − c·p^h`: the x-adic coefficient at `k·e+r` (`r<e`) is the
`p`-weighted triangular combination plus the cap `C(μ,k)·(−c·p^h)^(μ−k)·[r=0]`. The twist power
`wnegH^t = (−c)^t·p^(h·t)` carries a `p^(h·t)` factor (the h-scaled version of the h=1 `p^t`). -/

section CoeffFormula

/-- `−c·p^h`, the twist constant of `φ = X^e + C(wnegH)`. -/
def wnegH : ZMod (p ^ N) := -((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h)

/-- `φ = X^e + C(−c·p^h)`. -/
theorem phi_eq_H : phi p N e h c = X ^ e + C (wnegH p N h c) := by
  rw [phi_eq]
  unfold wnegH
  rw [map_neg, sub_eq_add_neg]

/-- The cap coefficient splits as `p`-power `p^(h·(μ−k))` times the (h-independent) unit part
`capU`. -/
theorem cap_splitH (k : ℕ) :
    (μ.choose k : ZMod (p ^ N)) * wnegH p N h c ^ (μ - k)
      = (p : ZMod (p ^ N)) ^ (h * (μ - k)) * RestartEquiv.capU p N μ c k := by
  unfold wnegH RestartEquiv.capU
  rw [show -((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h)
        = (-(c : ZMod (p ^ N))) * (p : ZMod (p ^ N)) ^ h by ring,
    mul_pow, ← pow_mul, mul_comm h (μ - k)]
  ring

/-- `wnegH^t = (−c)^t · p^(h·t)` — the unit/`p`-power split of the twist powers. -/
theorem wnegH_pow_split (t : ℕ) :
    wnegH p N h c ^ t = (-(c : ZMod (p ^ N))) ^ t * (p : ZMod (p ^ N)) ^ (h * t) := by
  unfold wnegH
  rw [show -((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h)
        = (-(c : ZMod (p ^ N))) * (p : ZMod (p ^ N)) ^ h by ring,
    mul_pow, ← pow_mul, mul_comm h t]

/-- **The triangular coefficient extraction** (general `h`): for `b` of degree `< e` and `r < e`,
`(b·φ^j).coeff (k·e+r) = b.coeff r · C(j,k) · (−c·p^h)^(j−k)`. -/
theorem coeff_mul_phi_powH (b : (ZMod (p ^ N))[X])
    (hb : b.degree < (e : WithBot ℕ)) (j k r : ℕ) (hr : r < e) :
    (b * phi p N e h c ^ j).coeff (k * e + r)
      = b.coeff r * (j.choose k : ZMod (p ^ N)) * wnegH p N h c ^ (j - k) := by
  rw [phi_eq_H, add_pow, Finset.mul_sum, finsetSum_coeff]
  have hterm : ∀ m : ℕ, b * ((X ^ e) ^ m * C (wnegH p N h c) ^ (j - m)
        * ((j.choose m : ℕ) : (ZMod (p ^ N))[X]))
      = (b * X ^ (e * m)) * C (wnegH p N h c ^ (j - m) * (j.choose m : ZMod (p ^ N))) := by
    intro m
    rw [← pow_mul, ← C_pow, ← C_eq_natCast, C_mul]
    ring
  rw [Finset.sum_congr rfl fun m _ => by rw [hterm m, coeff_mul_C, coeff_mul_X_pow']]
  have hvanish : ∀ m : ℕ, m < k →
      (if e * m ≤ k * e + r then b.coeff (k * e + r - e * m) else 0)
        * (wnegH p N h c ^ (j - m) * (j.choose m : ZMod (p ^ N))) = 0 := by
    intro m hlt
    have hcond : e * m ≤ k * e + r := by
      have h2 : e * m ≤ e * k := Nat.mul_le_mul_left e hlt.le
      have hek : e * k = k * e := Nat.mul_comm e k
      omega
    have hidx : e ≤ k * e + r - e * m := by
      have h2 : e * (m + 1) ≤ e * k := Nat.mul_le_mul_left e hlt
      have h3 : e * (m + 1) = e * m + e := Nat.mul_succ e m
      have hek : e * k = k * e := Nat.mul_comm e k
      omega
    rw [if_pos hcond,
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hb (Nat.cast_le.mpr hidx)), zero_mul]
  by_cases hkj : k ≤ j
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]
    · have hcond : e * k ≤ k * e + r := by
        have hek : e * k = k * e := Nat.mul_comm e k
        omega
      rw [if_pos hcond, show k * e + r - e * k = r by
        have hek : e * k = k * e := Nat.mul_comm e k
        omega]
      ring
    · intro m hm hmk
      rw [Finset.mem_range] at hm
      rcases Nat.lt_or_ge m k with hlt | hge
      · exact hvanish m hlt
      · have hmk' : k < m := by omega
        have hcond : ¬ e * m ≤ k * e + r := by
          have h2 : e * (k + 1) ≤ e * m := Nat.mul_le_mul_left e hmk'
          have h3 : e * (k + 1) = e * k + e := Nat.mul_succ e k
          have hek : e * k = k * e := Nat.mul_comm e k
          omega
        rw [if_neg hcond, zero_mul]
  · have hrhs : (j.choose k : ZMod (p ^ N)) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.cast_zero
    rw [hrhs, mul_zero, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    exact hvanish m (by omega)

/-- The reassembled development `φ^μ + Σ_j b_j φ^j` — the underlying polynomial of
`developEquiv.symm`. -/
def assembleH (b : Fin μ → degreeLT (ZMod (p ^ N)) e) : (ZMod (p ^ N))[X] :=
  phi p N e h c ^ μ + ∑ j : Fin μ, (b j : (ZMod (p ^ N))[X]) * phi p N e h c ^ (j : ℕ)

/-- **Cap coefficient** (general `h`): the cap `φ^μ` alone carries the exact on-side values — its
`(k·e+r)` coefficient is `C(μ,k)·(−c·p^h)^(μ−k)` at `r = 0`, and `0` off-pattern. -/
theorem phi_pow_coeffH (hN : 0 < N) (he : 0 < e) (k r : ℕ) (hr : r < e) :
    (phi p N e h c ^ μ).coeff (k * e + r)
      = if r = 0 then (μ.choose k : ZMod (p ^ N)) * wnegH p N h c ^ (μ - k) else 0 := by
  haveI := nontrivial_base p N hN
  have hdeg1 : (1 : (ZMod (p ^ N))[X]).degree < (e : WithBot ℕ) := by
    rw [degree_one]
    exact_mod_cast he
  conv_lhs => rw [← one_mul (phi p N e h c ^ μ)]
  rw [coeff_mul_phi_powH p N e h c 1 hdeg1 μ k r hr, coeff_one]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos h0, one_mul]
  · rw [if_neg h0, if_neg h0, zero_mul, zero_mul]

/-- **The x-adic coefficient formula** of the assembly: cap term + triangular perturbation. -/
theorem assemble_coeffH (hN : 0 < N) (he : 0 < e) (b : Fin μ → degreeLT (ZMod (p ^ N)) e)
    (k r : ℕ) (hr : r < e) :
    (assembleH p N e h μ c b).coeff (k * e + r)
      = (if r = 0 then (μ.choose k : ZMod (p ^ N)) * wnegH p N h c ^ (μ - k) else 0)
        + ∑ j : Fin μ, (b j : (ZMod (p ^ N))[X]).coeff r * ((j : ℕ).choose k : ZMod (p ^ N))
            * wnegH p N h c ^ ((j : ℕ) - k) := by
  unfold assembleH
  rw [coeff_add, finsetSum_coeff, phi_pow_coeffH p N e h μ c hN he k r hr]
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    coeff_mul_phi_powH p N e h c _ (mem_degreeLT.mp (b j).2) (j : ℕ) k r hr

end CoeffFormula

/-! ## The per-coordinate floor closed forms (`dexp` at the pattern weights) -/

section Dexp

/-- The constant-coordinate floor is STRICT: `dexp e h (e·h·q+1) 0 = h·q + 1` (coprime-free). -/
theorem dexp_pattern_zero (he : 0 < e) (q : ℕ) :
    dexp e h (e * h * q + 1) 0 = h * q + 1 := by
  refine le_antisymm ?_ ?_
  · rw [dexp_le_iff e h he]; ring_nf; omega
  · by_contra hcon
    have hle : dexp e h (e * h * q + 1) 0 ≤ h * q := by omega
    have := (dexp_le_iff e h he (e * h * q + 1) 0 (h * q)).mp hle
    -- e*h*q+1 ≤ 0*h + e*(h*q) = e*h*q, false
    simp only [Nat.zero_mul, Nat.zero_add] at this
    have hle2 : e * (h * q) = e * h * q := by ring
    omega

/-- `e ∤ h·r` for `0 < r < e` and `gcd(e,h)=1` (so `h·r % e ≥ 1`). -/
theorem not_e_dvd_hr (hcop : Nat.Coprime e h) {r : ℕ} (hr0 : 0 < r) (hre : r < e) :
    ¬ (e ∣ h * r) := by
  intro hdvd
  -- e ∣ h*r, Coprime e h ⟹ e ∣ r
  have hdvd' : e ∣ r * h := by rwa [Nat.mul_comm] at hdvd
  have hdr : e ∣ r := hcop.dvd_of_dvd_mul_right hdvd'
  have := Nat.le_of_dvd hr0 hdr
  omega

/-- The off-vertex diagonal floor (`1 ≤ r < e`, `gcd(e,h)=1`):
`dexp e h (e·h·q+1) r = h·q − ⌊h·r/e⌋`. THE crux identity (carries the coprimality). -/
theorem dexp_pattern_pos (he : 0 < e) (hcop : Nat.Coprime e h) (q : ℕ) {r : ℕ}
    (hr0 : 0 < r) (hre : r < e) :
    dexp e h (e * h * q + 1) r = h * q - h * r / e := by
  -- key modular facts: h*r = e*f + m with f = h*r/e, m = h*r%e, 1 ≤ m < e
  set f := h * r / e with hf
  set m := h * r % e with hm
  have hmod : e * f + m = h * r := by
    rw [hf, hm]; exact Nat.div_add_mod (h * r) e
  have hmod1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact absurd (Nat.dvd_of_mod_eq_zero (by rw [hm] at h0; exact h0))
        (not_e_dvd_hr e h hcop hr0 hre)
    · exact hpos
  have hmode : m < e := hm ▸ Nat.mod_lt _ he
  -- goal: dexp = h*q - f. Antisymmetry via dexp_le_iff.
  refine le_antisymm ?_ ?_
  · -- dexp ≤ h*q - f : need e*h*q+1 ≤ r*h + e*(h*q - f)
    rw [dexp_le_iff e h he]
    by_cases hqf : f ≤ h * q
    · -- e*(h*q-f) = e*(h*q) - e*f
      have hexp : e * (h * q - f) = e * (h * q) - e * f := by rw [Nat.mul_sub]
      have hehq : e * (h * q) = e * h * q := by ring
      have hrh : r * h = h * r := by ring
      omega
    · -- h*q < f ⟹ h*q - f = 0
      have h0 : h * q - f = 0 := by omega
      rw [h0, Nat.mul_zero, Nat.add_zero]
      -- need e*h*q+1 ≤ r*h = e*f+m ; e*h*q ≤ e*(f-1) ... since h*q < f
      have hrh : r * h = h * r := by ring
      have hlt : e * h * q < e * f := by
        have : e * (h * q) < e * f := (Nat.mul_lt_mul_left he).mpr (by omega)
        have hehq : e * (h * q) = e * h * q := by ring
        omega
      omega
  · -- h*q - f ≤ dexp : suppose not (dexp < h*q-f), contradiction
    by_contra hcon
    -- set D' = h*q - f - 1 (the alleged dexp bound); f + 1 + D' = h*q
    set D' := h * q - f - 1 with hD'
    have hd1 : dexp e h (e * h * q + 1) r ≤ D' := by omega
    have hqf : f + 1 + D' = h * q := by omega
    have := (dexp_le_iff e h he (e * h * q + 1) r D').mp hd1
    -- e*h*q+1 ≤ r*h + e*D' ; but e*(f+1+D') = e*h*q so e*D' = e*h*q - e*f - e = e*h*q - (e*f) - e
    have hED : e * (f + 1 + D') = e * h * q := by
      rw [hqf]; ring
    have hExpand : e * (f + 1 + D') = e * f + e + e * D' := by ring
    have hrh : r * h = h * r := by ring
    -- from hmod: e*f + m = h*r; so r*h + e*D' = e*f + m + e*D' = (e*h*q - e - e*f) ... let omega finish
    omega

end Dexp

/-! ## The per-slot dictionary: `filtIdeal`-membership ⟺ per-coefficient `p`-floors

Via `RphiGenHCount.filtIdeal_eq_phiIdeal` + `mem_phiIdeal`: membership `digitEquiv b ∈ filtIdeal w`
unfolds directly to the per-coordinate divisibilities `p^(dexp w i) ∣ b.coeff i`. No cardinality
sandwich is needed (that machinery is already banked in `RphiGenHCount`). -/

section Slot

/-- **The bridge**: the `digitCoeff` of `digitEquiv b` is the coefficient vector of `b`. -/
theorem digitCoeff_digitEquiv (hN : 0 < N) (he : 0 < e) (b : degreeLT (ZMod (p ^ N)) e)
    (i : Fin e) :
    digitCoeff p N e h c hN he (digitEquiv p N e h c hN he b) i
      = (b : (ZMod (p ^ N))[X]).coeff (i : ℕ) := by
  rw [digitCoeff, digitEquivFull, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The strict per-coefficient floor at depth `q` — the coefficient avatar of
`digitEquiv b ∈ filtIdeal(e·h·q+1)`, spelled directly by `dexp`. -/
def SlotCondGenH (q : ℕ) (b : degreeLT (ZMod (p ^ N)) e) : Prop :=
  ∀ i : Fin e, (p : ZMod (p ^ N)) ^ (dexp e h (e * h * q + 1) (i : ℕ))
    ∣ (b : (ZMod (p ^ N))[X]).coeff (i : ℕ)

/-- **The one-slot dictionary** (general `h`): `digitEquiv b ∈ filtIdeal(e·h·q+1) ⟺ SlotCondGenH q b`.
Immediate from `filtIdeal_eq_phiIdeal` + `mem_phiIdeal` + the `digitCoeff`/`coeff` bridge. -/
theorem digitEquiv_mem_filtIdeal_iff (hN : 0 < N) (he : 0 < e) (q : ℕ)
    (b : degreeLT (ZMod (p ^ N)) e) :
    digitEquiv p N e h c hN he b ∈ filtIdeal p N e h c (e * h * q + 1)
      ↔ SlotCondGenH p N e h q b := by
  rw [filtIdeal_eq_phiIdeal p N e h c hN he, mem_phiIdeal]
  unfold Phi SlotCondGenH
  refine forall_congr' fun i => ?_
  rw [digitCoeff_digitEquiv p N e h c hN he b i]

end Slot

/-! ## THE DICTIONARY at coefficient level: cell conditions ⟺ digit pattern (general `h`)

The cell floor at column `k·e+r` is `p^(h(μ−k) − ⌊h·r/e⌋)` (`= p^ceilAt`), with an exact digit
pin `digit(h(μ−k))(coeff(k·e)) = bres k` at the vertex reads (`r = 0`). The per-digit pattern is
the strict `SlotCondGenH (μ−j)`: coefficient `i` of digit `j` divisible by `p^(dexp e h
(e·h·(μ−j)+1) i)`. -/

section Dictionary

/-- The cell floor exponent at column `k·e+r`: `h·(μ−k) − ⌊h·r/e⌋` (`= ceilAt (k·e+r)`). -/
def cellFloor (k r : ℕ) : ℕ := h * (μ - k) - h * r / e

/-- The unpacked (root-refined) general-`h` cell conditions on the x-adic coefficients. -/
def CoeffCondGenH (a : ℕ → ZMod (p ^ N)) : Prop :=
  (∀ k r : ℕ, k < μ → r < e →
      (p : ZMod (p ^ N)) ^ (cellFloor e h μ k r) ∣ a (k * e + r)) ∧
    (∀ k : ℕ, k < μ → digit p N (h * (μ - k)) (a (k * e)) = RestartEquiv.bres p N μ c k)

/-- The per-digit strict pattern: digit `j` obeys `SlotCondGenH` at depth `μ − j`. -/
def SlotPatternGenH (b : Fin μ → degreeLT (ZMod (p ^ N)) e) : Prop :=
  ∀ j : Fin μ, SlotCondGenH p N e h (μ - (j : ℕ)) (b j)

/-- **Divisibility transfer through the twist** (general `h`): a `p^d`-floor on `x`, tensored with
the `p^(h·t)`-factor from `wnegH^t`, lands `x·y·wnegH^t` in the `p^D`-floor (`d + h·t = D`). -/
private theorem dvd_mul_wnegH_pow {d t D : ℕ} (hD : d + h * t = D) {x : ZMod (p ^ N)}
    (hx : (p : ZMod (p ^ N)) ^ d ∣ x) (y : ZMod (p ^ N)) :
    (p : ZMod (p ^ N)) ^ D ∣ x * y * wnegH p N h c ^ t := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u * y * (-(c : ZMod (p ^ N))) ^ t, ?_⟩
  rw [hu, wnegH_pow_split p N h c t, ← hD, pow_add]
  ring

/-- The `SlotCondGenH q b` per-coordinate floors, extracted at `r < e`. -/
theorem SlotCondGenH.dvd_coeff {q : ℕ} {b : degreeLT (ZMod (p ^ N)) e}
    (hb : SlotCondGenH p N e h q b) {r : ℕ} (hr : r < e) :
    (p : ZMod (p ^ N)) ^ (dexp e h (e * h * q + 1) r) ∣ (b : (ZMod (p ^ N))[X]).coeff r :=
  hb ⟨r, hr⟩

/-- The cell floor is dominated by the slot-`j` (`k ≤ j < μ`) perturbation valuation:
`cellFloor k r ≤ dexp e h (e·h·(μ−j)+1) r + h·(j−k)` (equality at `r ≥ 1`, one below at `r = 0`). -/
theorem cellFloor_le_dexp_add (he : 0 < e) (hcop : Nat.Coprime e h) {j k r : ℕ}
    (hkj : k ≤ j) (hjμ : j < μ) (hr : r < e) :
    cellFloor e h μ k r ≤ dexp e h (e * h * (μ - j) + 1) r + h * (j - k) := by
  unfold cellFloor
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · -- r = 0: dexp = h*(μ-j)+1 ; cellFloor = h*(μ-k) ; LHS ≤ h(μ-j)+1 + h(j-k)
    rw [dexp_pattern_zero e h he (μ - j), Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
    -- h*(μ-k) ≤ h*(μ-j)+1 + h*(j-k) : since (μ-j)+(j-k) = μ-k
    have hmul : h * (μ - j) + h * (j - k) = h * (μ - k) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  · rw [dexp_pattern_pos e h he hcop (μ - j) hr0 hr]
    -- h*(μ-k) - h*r/e ≤ (h*(μ-j) - h*r/e) + h*(j-k) : (μ-j)+(j-k)=μ-k
    have hmul : h * (μ - j) + h * (j - k) = h * (μ - k) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega

/-- The **strict** vertex domination for `k ≤ j`: `cellFloor k 0 + 1 ≤ dexp e h (e·h·(μ−j)+1) 0
+ h·(j−k)` (`= h(μ−k)+1`). -/
theorem cellFloor_zero_lt_dexp_add (he : 0 < e) {j k : ℕ}
    (hkj : k ≤ j) (hjμ : j < μ) :
    cellFloor e h μ k 0 + 1 ≤ dexp e h (e * h * (μ - j) + 1) 0 + h * (j - k) := by
  unfold cellFloor
  rw [dexp_pattern_zero e h he (μ - j), Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
  have hmul : h * (μ - j) + h * (j - k) = h * (μ - k) := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-- **The shift equality** for the ⟹ higher-slot bookkeeping: for `q ≤ q'`,
`dexp e h (e·h·q+1) r = dexp e h (e·h·q'+1) r + h·(q'−q)`... stated as `≤` in the form used:
for `j ≤ j' < μ`, `dexp e h (e·h·(μ−j)+1) r ≤ dexp e h (e·h·(μ−j')+1) r + h·(j'−j)`. -/
theorem dexp_target_le (he : 0 < e) (hcop : Nat.Coprime e h) {j j' r : ℕ}
    (hjj' : j ≤ j') (hj'μ : j' < μ) (hr : r < e) :
    dexp e h (e * h * (μ - j) + 1) r ≤ dexp e h (e * h * (μ - j') + 1) r + h * (j' - j) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [dexp_pattern_zero e h he (μ - j), dexp_pattern_zero e h he (μ - j')]
    have hmul : h * (μ - j') + h * (j' - j) = h * (μ - j) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  · rw [dexp_pattern_pos e h he hcop (μ - j) hr0 hr, dexp_pattern_pos e h he hcop (μ - j') hr0 hr]
    have hmul : h * (μ - j') + h * (j' - j) = h * (μ - j) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega

/-- **⟸ direction**: the strict digit floors imply the cell's coefficient conditions — every
perturbation term sits at or below the on-side reads (equal at `r ≥ 1`, strictly below at `r = 0`,
so the cap's exact vertex value survives). -/
theorem coeffCond_of_slotPatternGenH (hN : 0 < N) (he : 0 < e) (_hh : 0 < h)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) (hb : SlotPatternGenH p N e h μ b) :
    CoeffCondGenH p N e h μ c (fun i => (assembleH p N e h μ c b).coeff i) := by
  -- weak floor at column k*e+r for the perturbation term of slot j (dominates cellFloor)
  have hweak : ∀ (j : Fin μ) (k r : ℕ), k < μ → r < e →
      (p : ZMod (p ^ N)) ^ (cellFloor e h μ k r)
        ∣ (b j : (ZMod (p ^ N))[X]).coeff r * (((j : ℕ)).choose k : ZMod (p ^ N))
            * wnegH p N h c ^ ((j : ℕ) - k) := by
    intro j k r hk hr
    by_cases hkj : k ≤ (j : ℕ)
    · have hjμ : (j : ℕ) < μ := j.2
      have hfloor := SlotCondGenH.dvd_coeff p N e h (hb j) hr
      have hle := cellFloor_le_dexp_add e h μ he hcop hkj hjμ hr
      exact dvd_trans (pow_dvd_pow _ hle)
        (dvd_mul_wnegH_pow p N h c (rfl :
          dexp e h (e * h * (μ - (j:ℕ)) + 1) r + h * ((j:ℕ) - k)
            = dexp e h (e * h * (μ - (j:ℕ)) + 1) r + h * ((j:ℕ) - k)) hfloor _)
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
      exact dvd_zero _
  -- strict floor at the vertex (r=0): perturbation valuation ≥ cellFloor+1
  have hstrict : ∀ (j : Fin μ) (k : ℕ), k < μ →
      (p : ZMod (p ^ N)) ^ (cellFloor e h μ k 0 + 1)
        ∣ (b j : (ZMod (p ^ N))[X]).coeff 0 * (((j : ℕ)).choose k : ZMod (p ^ N))
            * wnegH p N h c ^ ((j : ℕ) - k) := by
    intro j k hk
    by_cases hkj : k ≤ (j : ℕ)
    · have hjμ : (j : ℕ) < μ := j.2
      have hfloor := SlotCondGenH.dvd_coeff p N e h (hb j) he
      have hle := cellFloor_zero_lt_dexp_add e h μ he hkj hjμ
      exact dvd_trans (pow_dvd_pow _ hle)
        (dvd_mul_wnegH_pow p N h c (rfl :
          dexp e h (e * h * (μ - (j:ℕ)) + 1) 0 + h * ((j:ℕ) - k)
            = dexp e h (e * h * (μ - (j:ℕ)) + 1) 0 + h * ((j:ℕ) - k)) hfloor _)
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_mul]
      exact dvd_zero _
  constructor
  · intro k r hk hr
    show (p : ZMod (p ^ N)) ^ (cellFloor e h μ k r) ∣ (assembleH p N e h μ c b).coeff (k * e + r)
    rw [assemble_coeffH p N e h μ c hN he b k r hr]
    refine dvd_add ?_ (Finset.dvd_sum fun j _ => hweak j k r hk hr)
    by_cases h0 : r = 0
    · rw [if_pos h0, cap_splitH p N h μ c k]
      -- cellFloor k 0 = h*(μ-k) = cap valuation; cellFloor k r = h*(μ-k) at r=0
      have hcf : cellFloor e h μ k r = h * (μ - k) := by
        rw [h0]; unfold cellFloor; rw [Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
      rw [hcf]
      exact Dvd.intro _ rfl
    · rw [if_neg h0]
      exact dvd_zero _
  · intro k hk
    show digit p N (h * (μ - k)) ((assembleH p N e h μ c b).coeff (k * e))
      = RestartEquiv.bres p N μ c k
    have hco := assemble_coeffH p N e h μ c hN he b k 0 he
    rw [Nat.add_zero, if_pos rfl] at hco
    obtain ⟨t, ht⟩ := Finset.dvd_sum fun (j : Fin μ) (_ : j ∈ Finset.univ) => hstrict j k hk
    have hcf0 : cellFloor e h μ k 0 = h * (μ - k) := by
      unfold cellFloor; rw [Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
    rw [hcf0] at ht
    rw [hco, cap_splitH p N h μ c k, ht,
      show (p : ZMod (p ^ N)) ^ (h * (μ - k) + 1)
          = (p : ZMod (p ^ N)) ^ (h * (μ - k)) * (p : ZMod (p ^ N)) from pow_succ _ _,
      show (p : ZMod (p ^ N)) ^ (h * (μ - k)) * RestartEquiv.capU p N μ c k
            + (p : ZMod (p ^ N)) ^ (h * (μ - k)) * (p : ZMod (p ^ N)) * t
          = (p : ZMod (p ^ N)) ^ (h * (μ - k))
              * (RestartEquiv.capU p N μ c k + (p : ZMod (p ^ N)) * t) by ring,
      RestartEquiv.digit_pow_mul p N (by
        have : h * (μ - k) ≤ h * μ := Nat.mul_le_mul_left h (Nat.sub_le _ _)
        omega : h * (μ - k) < N),
      RestartEquiv.resp_add p N hN, RestartEquiv.resp_capU p N μ c hN k,
      RestartEquiv.resp_mul p N hN, RestartEquiv.resp_p p N hN, zero_mul, add_zero]

/-- **⟹ direction, the triangular converse**: the cell's coefficient conditions force every
digit's strict floor — downward induction from the cap: the LOWEST failing slot would win the
coefficient valuation at its own column, contradicting the floor/pin there. The vertex reads are
at level `h(μ−k)` (h-scaled); every perturbation sits `≥ +1` above at `r = 0` and `≥` at `r ≥ 1`
(via `dexp_target_le`, the coprimality entering only through `dexp_pattern_pos`). -/
theorem slotPattern_of_coeffCondGenH (hN : 0 < N) (he : 0 < e) (_hh : 0 < h)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e)
    (hcc : CoeffCondGenH p N e h μ c (fun i => (assembleH p N e h μ c b).coeff i)) :
    SlotPatternGenH p N e h μ b := by
  have hfloor : ∀ k r : ℕ, k < μ → r < e →
      (p : ZMod (p ^ N)) ^ (cellFloor e h μ k r) ∣ (assembleH p N e h μ c b).coeff (k * e + r) :=
    fun k r hk hr => hcc.1 k r hk hr
  have hpin : ∀ k : ℕ, k < μ →
      digit p N (h * (μ - k)) ((assembleH p N e h μ c b).coeff (k * e)) = RestartEquiv.bres p N μ c k :=
    fun k hk => hcc.2 k hk
  have hlow : ∀ (j' : Fin μ) (k r : ℕ), (j' : ℕ) < k →
      (b j' : (ZMod (p ^ N))[X]).coeff r * (((j' : ℕ)).choose k : ZMod (p ^ N))
          * wnegH p N h c ^ ((j' : ℕ) - k) = 0 := by
    intro j' k r hlt
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, zero_mul]
  have main : ∀ t : ℕ, ∀ j : Fin μ, μ - (j : ℕ) ≤ t → SlotCondGenH p N e h (μ - (j : ℕ)) (b j) := by
    intro t
    induction t with
    | zero =>
        intro j hj
        exfalso
        have := j.2
        omega
    | succ t ih =>
        intro j hj
        have hjμ : (j : ℕ) < μ := j.2
        -- higher-slot (j' > j) perturbations at column j*e+r dominate the target floor at r
        have hup_weak : ∀ r : ℕ, r < e → ∀ j' ∈ Finset.univ.erase j,
            (p : ZMod (p ^ N)) ^ (dexp e h (e * h * (μ - (j : ℕ)) + 1) r) ∣
              (b j' : (ZMod (p ^ N))[X]).coeff r
                * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                * wnegH p N h c ^ ((j' : ℕ) - (j : ℕ)) := by
          intro r hr j' hj'
          rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with hlt | hge
          · rw [hlow j' (j : ℕ) r hlt]
            exact dvd_zero _
          · have hj'μ : (j' : ℕ) < μ := j'.2
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun hEq => (Finset.mem_erase.mp hj').1 (Fin.ext hEq)
            have hfl := SlotCondGenH.dvd_coeff p N e h (ih j' (by omega)) hr
            have hle := dexp_target_le e h μ he hcop hge hj'μ hr
            exact dvd_trans (pow_dvd_pow _ hle) (dvd_mul_wnegH_pow p N h c rfl hfl _)
        have hup_strict : ∀ j' ∈ Finset.univ.erase j,
            (p : ZMod (p ^ N)) ^ (dexp e h (e * h * (μ - (j : ℕ)) + 1) 0) ∣
              (b j' : (ZMod (p ^ N))[X]).coeff 0
                * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                * wnegH p N h c ^ ((j' : ℕ) - (j : ℕ)) := by
          intro j' hj'
          rcases Nat.lt_or_ge (j' : ℕ) (j : ℕ) with hlt | hge
          · rw [hlow j' (j : ℕ) 0 hlt]
            exact dvd_zero _
          · have hj'μ : (j' : ℕ) < μ := j'.2
            have hne : (j' : ℕ) ≠ (j : ℕ) := fun hEq => (Finset.mem_erase.mp hj').1 (Fin.ext hEq)
            have hfl := SlotCondGenH.dvd_coeff p N e h (ih j' (by omega)) he
            have hle := dexp_target_le e h μ he hcop hge hj'μ he
            exact dvd_trans (pow_dvd_pow _ hle) (dvd_mul_wnegH_pow p N h c rfl hfl _)
        have hextract : ∀ r : ℕ, r < e →
            (assembleH p N e h μ c b).coeff ((j : ℕ) * e + r)
              = (if r = 0 then (μ.choose (j : ℕ) : ZMod (p ^ N))
                    * wnegH p N h c ^ (μ - (j : ℕ)) else 0)
                + ((b j : (ZMod (p ^ N))[X]).coeff r
                  + ∑ j' ∈ Finset.univ.erase j,
                      (b j' : (ZMod (p ^ N))[X]).coeff r
                        * (((j' : ℕ)).choose (j : ℕ) : ZMod (p ^ N))
                        * wnegH p N h c ^ ((j' : ℕ) - (j : ℕ))) := by
          intro r hr
          rw [assemble_coeffH p N e h μ c hN he b (j : ℕ) r hr]
          congr 1
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
          congr 1
          rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, mul_one]
        -- prove SlotCondGenH (μ-j) (b j) : per-coordinate
        intro i
        by_cases hi0 : (i : ℕ) = 0
        · -- constant coeff: floor dexp(...) 0 = h(μ-j)+1, via the vertex pin
          rw [hi0]
          have hid := hextract 0 he
          rw [Nat.add_zero, if_pos rfl] at hid
          -- cell floor at r=0 is cellFloor j 0 = h*(μ-j); the pin gives digit(h(μ-j)) = bres j
          have hfl := hfloor (j : ℕ) 0 hjμ he
          rw [Nat.add_zero] at hfl
          have hcf0 : cellFloor e h μ (j : ℕ) 0 = h * (μ - (j : ℕ)) := by
            unfold cellFloor; rw [Nat.mul_zero, Nat.zero_div, Nat.sub_zero]
          rw [hcf0] at hfl
          obtain ⟨u, hu⟩ := hfl
          have hp1 := hpin (j : ℕ) hjμ
          rw [hu, RestartEquiv.digit_pow_mul p N (by
            have : h * (μ - (j:ℕ)) ≤ h * μ := Nat.mul_le_mul_left h (Nat.sub_le _ _)
            omega : h * (μ - (j : ℕ)) < N)] at hp1
          have hdiff : RestartEquiv.resp p N (u - RestartEquiv.capU p N μ c (j : ℕ)) = 0 := by
            rw [RestartEquiv.resp_sub p N hN, hp1, RestartEquiv.resp_capU p N μ c hN (j : ℕ), sub_self]
          obtain ⟨w1, hw1⟩ := (RestartEquiv.resp_eq_zero_iff p N hN _).mp hdiff
          obtain ⟨T, hT⟩ := Finset.dvd_sum (hup_strict)
          -- dexp(...) 0 = h(μ-j)+1
          rw [dexp_pattern_zero e h he (μ - (j : ℕ))]
          refine ⟨w1 - T, ?_⟩
          have hcapsplit := cap_splitH p N h μ c (j : ℕ)
          rw [dexp_pattern_zero e h he (μ - (j : ℕ))] at hT
          linear_combination -hid + hu - hcapsplit - hT
            + (p : ZMod (p ^ N)) ^ (h * (μ - (j : ℕ))) * hw1
        · -- higher coeff r ≥ 1: floor dexp(...) r via the cell floor at column j*e+r
          have hr1 : 1 ≤ (i : ℕ) := by omega
          have hre : (i : ℕ) < e := i.2
          have hid := hextract (i : ℕ) hre
          rw [if_neg (by omega), zero_add] at hid
          obtain ⟨T, hT⟩ := Finset.dvd_sum (hup_weak (i : ℕ) hre)
          -- cell floor at column j*e+i is cellFloor j i = dexp(...) i (r≥1, coprime)
          have hcf : cellFloor e h μ (j : ℕ) (i : ℕ) = dexp e h (e * h * (μ - (j : ℕ)) + 1) (i : ℕ) := by
            unfold cellFloor
            rw [dexp_pattern_pos e h he hcop (μ - (j : ℕ)) hr1 hre]
          have hfl := hfloor (j : ℕ) (i : ℕ) hjμ hre
          rw [hcf] at hfl
          obtain ⟨u, hu⟩ := hfl
          show (p : ZMod (p ^ N)) ^ (dexp e h (e * h * (μ - (j : ℕ)) + 1) (i : ℕ))
            ∣ (b j : (ZMod (p ^ N))[X]).coeff (i : ℕ)
          exact ⟨u - T, by rw [mul_sub, ← hu, ← hT]; linear_combination -hid⟩
  exact fun j => main μ j (by omega)

/-- `cellFloor k r ≤ h·μ` always (`h(μ−k) ≤ hμ`, minus a floor). -/
theorem cellFloor_le_hmu (k r : ℕ) : cellFloor e h μ k r ≤ h * μ := by
  unfold cellFloor
  exact le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_left h (Nat.sub_le _ _))

/-- `ceilAt (k·e+r) = cellFloor k r` for `k < μ`, `r < e` (the cell floor matches the def). -/
theorem ceilAt_eq_cellFloor (he : 0 < e) {k r : ℕ} (hk : k < μ) (hr : r < e) :
    ceilAt (restartPathGenH e h μ) (k * e + r) = cellFloor e h μ k r := by
  have hle : k * e + r ≤ μ * e := by
    have h1 : (k + 1) * e ≤ μ * e := Nat.mul_le_mul_right e (by omega)
    have h2 : (k + 1) * e = k * e + e := Nat.succ_mul k e
    omega
  rw [ceilAt_restartGenH e h μ (by omega) (k * e + r) hle]
  unfold cellFloor
  -- h*μ − h*(k*e+r)/e = h*(μ-k) − h*r/e
  have hdiv : h * (k * e + r) / e = h * k + h * r / e := by
    rw [show h * (k * e + r) = h * r + h * k * e by ring, Nat.add_mul_div_right _ _ he,
      Nat.add_comm]
  rw [hdiv]
  have hmul : h * (μ - k) = h * μ - h * k := by rw [Nat.mul_sub]
  have hkμ : h * k ≤ h * μ := Nat.mul_le_mul_left h (by omega)
  omega

/-! ## The membership unpacking (`matches_iff`, e-reindexed and root-refined) -/

set_option maxHeartbeats 1600000 in
theorem inCellAtGenH_iff_coeffCondGenH (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAtGenH p N e h μ c f ↔ CoeffCondGenH p N e h μ c (fun i => (f.1).coeff i) := by
  have hμ : 0 < μ := by omega
  have hP := restartPath_menuPathGenH N e h μ hμ hhμN he hh
  have hsh := restartShapesGenH e h μ hμ hcop
  have hM := matches_iff p hN hP hsh f
  have hprMem : ((0, h * μ), (μ * e, 0)) ∈ sidePairs (restartPathGenH e h μ) :=
    List.mem_singleton_self _
  -- floors reindexing, both ways
  have hfloors : (∀ i : Fin (μ * e),
        (p : ℕ) ^ ceilAt (restartPathGenH e h μ) i.1 ∣ (((f.1)).coeff i.1).val)
      ↔ (∀ k r : ℕ, k < μ → r < e →
          (p : ZMod (p ^ N)) ^ (cellFloor e h μ k r) ∣ (f.1).coeff (k * e + r)) := by
    constructor
    · intro hall k r hk hr
      have hi : k * e + r < μ * e := by
        have h1 : (k + 1) * e ≤ μ * e := Nat.mul_le_mul_right e (by omega)
        have h2 : (k + 1) * e = k * e + e := Nat.succ_mul k e
        omega
      have h3 := hall ⟨k * e + r, hi⟩
      rw [ceilAt_eq_cellFloor e h μ he hk hr] at h3
      exact (RestartEquiv.pow_dvd_iff_dvd_val p N
        (by have := cellFloor_le_hmu e h μ k r; omega) _).mpr h3
    · intro hall i
      have hk : i.1 / e < μ := by
        rw [Nat.div_lt_iff_lt_mul he]
        exact i.2
      have hr : i.1 % e < e := Nat.mod_lt _ he
      have hidx : i.1 / e * e + i.1 % e = i.1 := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod i.1 e
      have h3 := hall (i.1 / e) (i.1 % e) hk hr
      rw [hidx] at h3
      -- goal: p^(ceilAt i.1) ∣ (coeff i.1).val ; ceilAt i.1 = cellFloor (i.1/e) (i.1%e)
      have hce : ceilAt (restartPathGenH e h μ) i.1 = cellFloor e h μ (i.1 / e) (i.1 % e) := by
        conv_lhs => rw [← hidx]
        exact ceilAt_eq_cellFloor e h μ he hk hr
      rw [hce]
      exact (RestartEquiv.pow_dvd_iff_dvd_val p N
        (by have := cellFloor_le_hmu e h μ (i.1 / e) (i.1 % e); omega) _).mp h3
  constructor
  · rintro ⟨hin, hres⟩
    obtain ⟨hdvd, _⟩ := hM.mp ((inCell_mkCell_iff p hP hsh).mp hin)
    have hsp : sidePolyR p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) ((0, h * μ), (μ * e, 0))
        = (X - C (RestartEquiv.cbar p N c)) ^ μ := by
      rw [← residualOf_eq_sidePolyR p hN hP hprMem f hdvd]
      exact hres
    refine ⟨hfloors.mp hdvd, ?_⟩
    intro k hk
    have h5 := (sidePolyR_eq_target_iff p N e h μ c hμ hcop _).mp hsp k hk
    rw [rho_restart_readGenH p N e h μ he hμ f k hk] at h5
    exact h5
  · rintro ⟨hflo, hpins⟩
    have hdvd := hfloors.mpr hflo
    have hsp : sidePolyR p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) ((0, h * μ), (μ * e, 0))
        = (X - C (RestartEquiv.cbar p N c)) ^ μ := by
      refine (sidePolyR_eq_target_iff p N e h μ c hμ hcop _).mpr ?_
      intro k hk
      rw [rho_restart_readGenH p N e h μ he hμ f k hk]
      exact hpins k hk
    have hside : SideCond p (fun i : Fin (μ * e) =>
          digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) [(1, μ)]
        ((0, h * μ), (μ * e, 0)) := by
      constructor
      · rw [hsp, RestartEquiv.target_shape p N μ c (by omega)]
      · show rho p (fun i : Fin (μ * e) =>
            digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) 0 ≠ 0
        rw [show (0 : ℕ) = 0 * e from (Nat.zero_mul e).symm,
          rho_restart_readGenH p N e h μ he hμ f 0 hμ]
        rw [Nat.zero_mul]
        have h6 := hpins 0 hμ
        rw [Nat.zero_mul] at h6
        simp only [] at h6
        intro h0
        rw [h0] at h6
        exact RestartEquiv.bres_zero_ne p N μ c hN hμ h6.symm
    have hdig : DigCond p (restartPathGenH e h μ) [[(1, μ)]] (fun i : Fin (μ * e) =>
        digit p N (ceilAt (restartPathGenH e h μ) i.1) ((f.1).coeff i.1)) := by
      show List.Forall₂ _ [[(1, μ)]] (sidePairs (restartPathGenH e h μ))
      rw [show sidePairs (restartPathGenH e h μ) = [((0, h * μ), (μ * e, 0))] from rfl]
      exact List.Forall₂.cons hside List.Forall₂.nil
    refine ⟨(inCell_mkCell_iff p hP hsh).mpr (hM.mpr ⟨hdvd, hdig⟩), ?_⟩
    rw [residualOf_eq_sidePolyR p hN hP hprMem f hdvd]
    exact hsp

end Dictionary

/-! ## Deliverables 2–5: `restartDigitsGenH`, THE DICTIONARY, `restartEquivGenH`, the fiber card -/

section Main

/-- The develop equivalence specialized to the general-`h` restart key `φ = X^e − c·p^h`
(`k = μ`, `m = e`). -/
def developPhiGenH (hN : 0 < N) (he : 0 < e) :
    QuotientBox.monicBox p N (μ * e) ≃ (Fin μ → degreeLT (ZMod (p ^ N)) e) :=
  developEquiv p N e μ hN (phi p N e h c) (monic_phi p N e h c he)
    (natDegree_phi p N e h c hN) he

theorem developPhiGenH_symm_val (hN : 0 < N) (he : 0 < e)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) :
    ((developPhiGenH p N e h μ c hN he).symm b).1 = assembleH p N e h μ c b := rfl

/-- **Deliverable 2 (unbundled)**: the digit avatars of `f` — the φ-adic development
(`developEquiv`, φ = X^e − c·p^h) composed with the digit identification (`digitEquiv`),
per digit. -/
def restartDigitsGenH' (hN : 0 < N) (he : 0 < e) (f : QuotientBox.monicBox p N (μ * e)) :
    Fin μ → Rphi p N e h c :=
  fun j => digitEquiv p N e h c hN he (developPhiGenH p N e h μ c hN he f j)

/-- **Deliverable 2**: the digit avatars of a cell-fiber element. -/
def restartDigitsGenH (hN : 0 < N) (he : 0 < e)
    (f : {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}) :
    Fin μ → Rphi p N e h c :=
  restartDigitsGenH' p N e h μ c hN he f.1

/-- The dictionary at develop level: `InCellAtGenH f ⟺ SlotPatternGenH (developPhiGenH f)`. -/
theorem inCellAtGenH_iff_slotPattern (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAtGenH p N e h μ c f
      ↔ SlotPatternGenH p N e h μ (developPhiGenH p N e h μ c hN he f) := by
  rw [inCellAtGenH_iff_coeffCondGenH p N e h μ c hN he hh hμ2 hcop hhμN f]
  have hval : assembleH p N e h μ c (developPhiGenH p N e h μ c hN he f) = f.1 := by
    rw [← developPhiGenH_symm_val p N e h μ c hN he (developPhiGenH p N e h μ c hN he f),
      Equiv.symm_apply_apply]
  constructor
  · intro hcc
    refine slotPattern_of_coeffCondGenH p N e h μ c hN he hh hcop hhμN _ ?_
    rw [hval]; exact hcc
  · intro hsp
    have h2 := coeffCond_of_slotPatternGenH p N e h μ c hN he hh hcop hhμN _ hsp
    rw [hval] at h2; exact h2

/-- The per-slot dictionary summed: `SlotPatternGenH b ⟺ FreshClusterPatternGenH (digitEquiv ∘ b)`. -/
theorem slotPattern_iff_pattern (hN : 0 < N) (he : 0 < e)
    (b : Fin μ → degreeLT (ZMod (p ^ N)) e) :
    SlotPatternGenH p N e h μ b
      ↔ FreshClusterPatternGenH p N e h μ c (fun j => digitEquiv p N e h c hN he (b j)) := by
  unfold SlotPatternGenH FreshClusterPatternGenH
  refine forall_congr' fun j => ?_
  exact (digitEquiv_mem_filtIdeal_iff p N e h c hN he (μ - (j : ℕ)) (b j)).symm

/-- **Deliverable 3 — THE DICTIONARY**: root-refined general-`h` cell membership ⟺ the
gate-verified fresh cluster pattern of the digit avatars. -/
theorem inCellAtGenH_iff_pattern (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (f : QuotientBox.monicBox p N (μ * e)) :
    InCellAtGenH p N e h μ c f
      ↔ FreshClusterPatternGenH p N e h μ c (restartDigitsGenH' p N e h μ c hN he f) := by
  rw [inCellAtGenH_iff_slotPattern p N e h μ c hN he hh hμ2 hcop hhμN f,
    slotPattern_iff_pattern p N e h μ c hN he _]
  exact Iff.rfl

/-- **Deliverable 4 — THE GENERAL-`h` RESTART EQUIVALENCE at level `N`**: the root-refined cell
fiber is in bijection with the fresh-cluster-pattern coset. Forward: `restartDigitsGenH`;
inverse: the explicit reassembly `β ↦ φ^μ + Σ_j lift(β_j)·φ^j`. -/
def restartEquivGenH (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N) :
    {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}
      ≃ {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β} :=
  ((developPhiGenH p N e h μ c hN he).subtypeEquiv fun f =>
      inCellAtGenH_iff_slotPattern p N e h μ c hN he hh hμ2 hcop hhμN f).trans
    ((Equiv.piCongrRight fun _ => (digitEquiv p N e h c hN he).toEquiv).subtypeEquiv fun b =>
      slotPattern_iff_pattern p N e h μ c hN he b)

/-- The forward map of `restartEquivGenH` IS `restartDigitsGenH`. -/
theorem restartEquivGenH_apply_val (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (f : {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}) :
    (restartEquivGenH p N e h μ c hN he hh hμ2 hcop hhμN f).1
      = restartDigitsGenH p N e h μ c hN he f := rfl

/-- The inverse of `restartEquivGenH` is the explicit reassembly `φ^μ + Σ_j lift(β_j)·φ^j`. -/
theorem restartEquivGenH_symm_apply_val (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N)
    (β : {β : Fin μ → Rphi p N e h c // FreshClusterPatternGenH p N e h μ c β}) :
    (((restartEquivGenH p N e h μ c hN he hh hμ2 hcop hhμN).symm β).1).1
      = phi p N e h c ^ μ
        + ∑ j : Fin μ, ((digitEquiv p N e h c hN he).symm (β.1 j) : (ZMod (p ^ N))[X])
            * phi p N e h c ^ (j : ℕ) := rfl

/-- **Deliverable 5**: the root-refined general-`h` restart fiber card — Deliverable 1 transported
through Deliverables 2–4 (the per-digit product count). -/
theorem card_restartGenH_fiber (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (hμ2 : 2 ≤ μ)
    (hcop : Nat.Coprime e h) (hhμN : h * μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e h μ c f}
      = ∏ j : Fin μ, ∏ i : Fin e,
          p ^ (N - min N (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ))) := by
  rw [Nat.card_congr (restartEquivGenH p N e h μ c hN he hh hμ2 hcop hhμN),
    card_freshPatternGenH p N e h μ c hN he]

end Main

/-! ## The `h = 1` collapse (compat with the banked `RestartEquiv`) -/

section Collapse

/-- **`h = 1` collapse of the per-slot pattern card**: at `h = 1` each slot's per-digit product
collapses to the ungapped W1 count `p^(N·e − (e(μ−j)+1))` (via `RphiGenHCount.prod_dexp_h_one`,
the `⟨e,1⟩ = ℕ` no-gap case). -/
theorem card_freshPatternGenH_h_one_collapse (hN : 0 < N) (he : 0 < e) (hμN : μ < N) :
    Nat.card {β : Fin μ → Rphi p N e 1 c // FreshClusterPatternGenH p N e 1 μ c β}
      = ∏ j : Fin μ, p ^ (N * e - (e * (μ - j.1) + 1)) := by
  rw [card_freshPatternGenH p N e 1 μ c hN he]
  refine Finset.prod_congr rfl fun j _ => ?_
  -- e*1*(μ-j)+1 = e*(μ-j)+1 ≤ N*e (from μ < N), so prod_dexp_h_one applies
  have hw : e * 1 * (μ - j.1) + 1 ≤ N * e := by
    have h1 : e * (μ - j.1) + 1 ≤ N * e := RestartEquiv.slot_exponent_le N e μ he hμN j.1
    have h2 : e * 1 * (μ - j.1) = e * (μ - j.1) := by ring
    omega
  rw [prod_dexp_h_one p N e hN he hw]
  congr 1
  have : e * 1 * (μ - j.1) = e * (μ - j.1) := by ring
  omega

/-- **`h = 1` collapse to the banked closed form**: the general-`h` restart fiber card at `h = 1`
equals `RestartEquiv.card_restart_fiber`'s `p^(μ(Ne−1) − eμ(μ+1)/2)`. -/
theorem card_restartGenH_fiber_h_one_collapse (hN : 0 < N) (he : 0 < e) (hμ2 : 2 ≤ μ)
    (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * e) // InCellAtGenH p N e 1 μ c f}
      = p ^ (μ * (N * e - 1) - e * μ * (μ + 1) / 2) := by
  have hcop : Nat.Coprime e 1 := Nat.coprime_one_right e
  rw [card_restartGenH_fiber p N e 1 μ c hN he (by norm_num) hμ2 hcop (by omega),
    ← card_freshPatternGenH p N e 1 μ c hN he,
    card_freshPatternGenH_h_one_collapse p N e μ c hN he hμN,
    Finset.prod_pow_eq_pow_sum, RestartEquiv.freshExp_sum N e μ he hμN]

end Collapse

/-! ## MANDATORY GATES (phaseb_w6h fiber cards, 0-mismatch) -/

section Gates

/-- **Gate G1** (e,h,μ)=(3,2,2), p=2, N=5, c̃'=1: the genuine wild ramified restart. Fiber `4096`.
(phaseb_w6h `case_G1_5`; floors [13,7], per-slot exps [3,9].) -/
theorem gate_G1 :
    Nat.card {f : QuotientBox.monicBox 2 5 (2 * 3) // InCellAtGenH 2 5 3 2 2 1 f} = 4096 := by
  rw [card_restartGenH_fiber 2 5 3 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  decide

/-- **Gate H** (e,h,μ)=(2,3,2), p=2, N=7, c̃'=1: the wild gapped ⟨2,3⟩ readable case. Fiber `1024`.
(phaseb_w6h `case_H_7`; floors [13,7], per-slot exps [2,8]; nonempty first at N=7 = hμ+1.) -/
theorem gate_H :
    Nat.card {f : QuotientBox.monicBox 2 7 (2 * 2) // InCellAtGenH 2 7 2 3 2 1 f} = 1024 := by
  rw [card_restartGenH_fiber 2 7 2 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  decide

/-- **Gate S (h = 1 sanity)** (e,h,μ)=(2,1,2), p=2, N=3, c̃'=1: fiber `16`, collapsing to the
banked `RestartEquiv.card_restart_fiber` value (phaseb_w6h `case_S_e2mu2`; floors [5,3]). -/
theorem gate_S_h_one :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAtGenH 2 3 2 1 2 1 f} = 16 := by
  rw [card_restartGenH_fiber_h_one_collapse 2 3 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- The `h = 1` sanity gate value agrees with the banked `RestartEquiv.card_restart_fiber`
(both `16`) — the general-`h` collapse is consistent with the referee-gap `h = 1` bijection.
(At `p = 2` the box is `μ*e`; `RestartEquiv` uses the same `μ*e` box, so the cardinalities are
compared on the same fiber type.) -/
theorem gate_S_h_one_matches_banked :
    Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // InCellAtGenH 2 3 2 1 2 1 f}
      = Nat.card {f : QuotientBox.monicBox 2 3 (2 * 2) // RestartEquiv.InCellAt 2 3 2 2 1 f} := by
  rw [gate_S_h_one,
    RestartEquiv.card_restart_fiber 2 3 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end Gates

end

end LeanUrat.OM.RestartEquivGenH
