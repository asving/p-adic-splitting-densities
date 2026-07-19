/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.TowerBase
import LeanUrat.OM.TowerRestartAbstract
import LeanUrat.OM.Development
import LeanUrat.OM.RestartEquivGenH
import LeanUrat.OM.UnramifiedBase

/-!
# DevelopTower — the LAST ≃-piece: the order-`r` restart EQUIVALENCE recursion (D4d)

**Provenance.** `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §4 + §7 (deliverable 5).
The named residual D4d of `TowerRestartAbstract`: the `developPhiGenH`-analogue over the tower
coefficient ring, upgrading the CLOSED count recursion (`towerBallProduct` :313) to a genuine `≃`
at all orders. Purely additive on the FROZEN concrete layer and the banked `TowerBase` /
`TowerRestartAbstract` abstractions.

**THE KEY REALIZATION (verified).** `Development.developEquiv` is NOT literally base-general — its
DOMAIN `QuotientBox.monicBox p N (k*m)` is `ZMod`-specific (`Fact p.Prime`, `ZMod (p^N)`). BUT the
underlying φ-adic digit machinery it is built from (`develop`, `develop_reassemble_degree`,
`develop_unique`, `monic_pow_add_digit_sum`, `develop_digit_degree`) is ALREADY fully base-general
over an arbitrary `[CommRing R]`. So the development bijection over the tower ring needs NO new
mathematical content — only a re-statement of `developEquiv` over a general monic box (`Nontrivial
CommRing`), reusing those base-general lemmas verbatim (`developEquivGen`). This is the sense in
which "developEquiv may need no new proof, just instantiation."

**Deliverables.**
1. `developEquivGen` (base-general `developEquiv`) + `developTower`: the φ-adic development of a
   `monicBoxGen (μ*e)` over an arbitrary `[TowerBase R]` (φ = `phiGen R e h c = X^e − c·ϖ^h`) into
   digit avatars in `Fin μ → degreeLT R e` — the `developPhiGenH`-analogue over the tower ring.
2. `restartEquivTower` / `r_level_census_equiv`: the full order-`r` restart `≃` by `Nat`-recursion
   on tower height (`towerLevel`), each level a `TowerBase` over the last via
   `instTowerBase_RphiGenH`, composing `developTower` with the banked base-agnostic
   `restartEquivAbstract`. The CARD side is `towerBallProduct` (banked); `card_restartTower_fiber`
   is the per-digit product, and `towerLevel_ballCount` unfolds the level-`r` ball-count into the
   nested per-level product (= the order-2 `card_freshPatternAbstract_child`).
3. Gates: reduction to concrete (fibers 4096/1024/16 via the abstract `≃` at `R = ZMod`), order-2
   recovery (matching `card_freshPatternAbstract_child` / `card_two_level_genH_perslot`), and the
   O''-instance (`restartEquivTower` at `R = Oring` = the f≥2 restart, via `instTowerBase_Oring`).

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprint
(`[propext, Classical.choice, Quot.sound]`, `#print axioms`-checked); mathlib-only beyond the
frozen concrete + `TowerBase`/`TowerRestartAbstract` layers.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.DevelopTower

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.Development
open LeanUrat.OM.TowerBase
open LeanUrat.OM.TowerRestartAbstract
open LeanUrat.OM.RphiGenHCount

noncomputable section

/-! ## Deliverable 1a: the base-general φ-adic development bijection (ZMod-free `developEquiv`) -/

section DevelopGen

variable {R : Type*} [CommRing R]

/-- The general monic box: monic polynomials of degree `n` over an arbitrary `CommRing R` (the
`ZMod`-free avatar of `QuotientBox.monicBox p N n`). -/
def monicBoxGen (n : ℕ) : Type _ := {f : R[X] // f.Monic ∧ f.natDegree = n}

/-- **Deliverable 1a — the base-general φ-adic development bijection** (the `ZMod`-free
`Development.developEquiv`). For a monic `φ` of degree `m` over any `Nontrivial CommRing R`, the
monic box of degree `k·m` is in bijection with `k`-tuples of digits of degree `< m`. The proof is
`Development.developEquiv`'s, with `ZMod (p^N)` replaced by `R`; it reuses ONLY the base-general
`Development` digit lemmas (`develop_digit_degree`, `monic_pow_add_digit_sum`,
`develop_reassemble_degree`, `develop_unique`) — no `Fact p.Prime`, no `ZMod`, no `Fact (1 < p^N)`.
This is the precise sense in which `developEquiv` needed "no new proof, just instantiation": the
mathematical content was already base-general in `Development`. -/
def developEquivGen [Nontrivial R] (m k : ℕ) (φ : R[X]) (hφ : φ.Monic) (hm : φ.natDegree = m) :
    monicBoxGen (R := R) (k * m) ≃ (Fin k → degreeLT R m) where
  toFun := fun g j =>
    ⟨develop φ k (g.1 - φ ^ k) j,
      mem_degreeLT.2 (by
        have h := develop_digit_degree hφ k (g.1 - φ ^ k) j
        rwa [degree_eq_natDegree hφ.ne_zero, hm] at h)⟩
  invFun := fun b =>
    ⟨φ ^ k + ∑ j : Fin k, (b j : R[X]) * φ ^ (j : ℕ),
      monic_pow_add_digit_sum hφ hm k (fun j => (b j : R[X]))
        (fun j => mem_degreeLT.1 (b j).2)⟩
  left_inv := fun g => by
    obtain ⟨f, hfm, hfd⟩ := g
    apply Subtype.ext
    show φ ^ k + ∑ j : Fin k, develop φ k (f - φ ^ k) j * φ ^ (j : ℕ) = f
    have h1 : f.degree = (φ ^ k).degree := by
      rw [degree_eq_natDegree hfm.ne_zero, degree_eq_natDegree (hφ.pow k).ne_zero, hfd,
        hφ.natDegree_pow, hm]
    have hsub : (f - φ ^ k).degree < ((k * m : ℕ) : WithBot ℕ) := by
      have h2 := degree_sub_lt h1 hfm.ne_zero
        (by rw [hfm.leadingCoeff, (hφ.pow k).leadingCoeff])
      rwa [degree_eq_natDegree hfm.ne_zero, hfd] at h2
    rw [develop_reassemble_degree hφ k (f - φ ^ k) (by rw [hm]; exact hsub)]
    ring
  right_inv := fun b => by
    funext j
    apply Subtype.ext
    show develop φ k
        ((φ ^ k + ∑ i : Fin k, (b i : R[X]) * φ ^ (i : ℕ)) - φ ^ k) j
      = (b j : R[X])
    rw [add_sub_cancel_left]
    have h := develop_unique hφ k (∑ i : Fin k, (b i : R[X]) * φ ^ (i : ℕ))
      (fun i => (b i : R[X]))
      (fun i => by rw [hm]; exact mem_degreeLT.1 (b i).2) rfl
    exact (congrFun h j).symm

/-- The inverse of `developEquivGen` is the explicit reassembly `φ^k + Σ_j b_j·φ^j`. -/
theorem developEquivGen_symm_val [Nontrivial R] (m k : ℕ) (φ : R[X]) (hφ : φ.Monic)
    (hm : φ.natDegree = m) (b : Fin k → degreeLT R m) :
    ((developEquivGen m k φ hφ hm).symm b).1 = φ ^ k + ∑ j : Fin k, (b j : R[X]) * φ ^ (j : ℕ) :=
  rfl

end DevelopGen

/-! ## Deliverable 1b: `developTower` — the development over the tower coefficient ring -/

section DevelopTowerDef

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- **Deliverable 1b — `developTower`.** The φ-adic development of a `monicBoxGen (μ*e)` over an
arbitrary `[TowerBase R]` coefficient ring (φ = `phiGen R e h c = X^e − c·ϖ^h`) into digit avatars
in `Fin μ → degreeLT R e`. This is `developEquivGen` instantiated at the tower key `phiGen R e h c`
(`k = μ`, `m = e`) — the `developPhiGenH`-analogue over the tower ring. Because the `Development`
digit machinery is base-general, this is a pure instantiation, no new proof. -/
def developTower {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    monicBoxGen (R := R) (μ * e) ≃ (Fin μ → degreeLT R e) :=
  developEquivGen e μ (phiGen R e h c) (monic_phiGen he h c) (natDegree_phiGen he h c)

/-- The inverse of `developTower` is the reassembly `φ^μ + Σ_j b_j·φ^j` (φ = `phiGen R e h c`) —
the abstract avatar of `RestartEquivGenH.restartEquivGenH_symm_apply_val`'s reassembly. -/
theorem developTower_symm_val {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (b : Fin μ → degreeLT R e) :
    ((developTower he h μ c).symm b).1
      = phiGen R e h c ^ μ + ∑ j : Fin μ, (b j : R[X]) * phiGen R e h c ^ (j : ℕ) := rfl

end DevelopTowerDef

/-! ## Deliverable 2a: the abstract restart cell `InCellTower` and `restartEquivTower` -/

section RestartTower

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- Abstract order-`r`-level cell membership on the tower monic box: the develop-avatars obey the
fresh slot pattern `SlotPatternAbstract`. This is the abstract avatar of
`RestartEquivGenH.InCellAtGenH`, spelled THROUGH `developTower` — there is no abstract
`residualOf`/`InCell` over a general `[TowerBase R]` (that Newton-menu reader is `ZMod`-specific and
stays FROZEN); the `developPhiGenH`-analogue development IS the cell reader here. -/
def InCellTower {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (f : monicBoxGen (R := R) (μ * e)) : Prop :=
  SlotPatternAbstract he h μ c (developTower he h μ c f)

/-- **Deliverable 2a — the order-`r` restart EQUIVALENCE over `[TowerBase R]`.** Compose the
base-general development `developTower` (as a `subtypeEquiv` over the develop-pullback of the slot
pattern — `Iff.rfl` by construction of `InCellTower`) with the banked base-agnostic
`restartEquivAbstract`. This is `restartEquivGenH`'s two-factor shape (`developPhiGenH ∘
piCongrRight digitEquiv`) transported to the tower base: the FIRST factor is now the base-general
`developTower`, the SECOND is the banked `restartEquivAbstract`. At `R = ZMod (p^N)` it recovers
`restartEquivGenH`'s card; over a tower ring (via `instTowerBase_RphiGenH`) it is the order-`r`
restart. -/
def restartEquivTower {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    {f : monicBoxGen (R := R) (μ * e) // InCellTower he h μ c f}
      ≃ {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β} :=
  ((developTower he h μ c).subtypeEquiv fun _ => Iff.rfl).trans
    (restartEquivAbstract he h μ c)

/-- The forward map of `restartEquivTower` is the per-digit `digitEquivG` of the develop-avatars —
the abstract avatar of `restartEquivGenH_apply_val` (`restartDigitsGenH`). -/
theorem restartEquivTower_apply_val {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (f : {f : monicBoxGen (R := R) (μ * e) // InCellTower he h μ c f}) :
    (restartEquivTower he h μ c f).1
      = fun j => digitEquivG R he h c (developTower he h μ c f.1 j) := rfl

/-- The inverse of `restartEquivTower` is the explicit reassembly `φ^μ + Σ_j lift(β_j)·φ^j`
(φ = `phiGen R e h c`, `lift = digitEquivG.symm`) — the abstract avatar of
`restartEquivGenH_symm_apply_val`. -/
theorem restartEquivTower_symm_val {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (β : {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β}) :
    (((restartEquivTower he h μ c).symm β).1).1
      = phiGen R e h c ^ μ
        + ∑ j : Fin μ, ((digitEquivG R he h c).symm (β.1 j) : R[X]) * phiGen R e h c ^ (j : ℕ) :=
  rfl

/-- **The order-`r` restart fiber CARD** = `card_restartAbstract_fiber` transported through the
development bijection: the per-digit product count, general base. -/
theorem card_restartTower_fiber {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    Nat.card {f : monicBoxGen (R := R) (μ * e) // InCellTower he h μ c f}
      = ∏ j : Fin μ, ∏ i : Fin e,
          ballCount (R := R) (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ)) := by
  have hcong : {f : monicBoxGen (R := R) (μ * e) // InCellTower he h μ c f}
      ≃ {b : Fin μ → degreeLT R e // SlotPatternAbstract he h μ c b} :=
    (developTower he h μ c).subtypeEquiv fun _ => Iff.rfl
  rw [Nat.card_congr hcong, card_restartAbstract_fiber he h μ c]

/-- **The order-`r` restart CARD in `towerBallProduct` form** (one-step): the tower fiber card is
`∏_j towerBallProduct e h (R.ballCount) 1 (top floor j)` — the banked `towerBallProduct` at `r = 1`
per slot. Anchors `restartEquivTower`'s card to the banked `Nat`-recursion CARD skeleton. -/
theorem card_restartTower_fiber_towerBallProduct {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    Nat.card {f : monicBoxGen (R := R) (μ * e) // InCellTower he h μ c f}
      = ∏ j : Fin μ, towerBallProduct e h (ballCount R) 1 (e * h * (μ - j.1) + 1) := by
  rw [card_restartTower_fiber he h μ c]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [towerBallProduct_one]

end RestartTower

/-! ## Deliverable 2b: the homogeneous tower and `r_level_census_equiv` (the deep recursion) -/

section Recursion

/-- Bundled tower level: a finite nontrivial commutative ring with a `TowerBase` instance. Packages
the four instances the abstract layer needs, so the `Nat`-recursion on tower height produces a
single term. -/
structure TowerLevel where
  carrier : Type
  [commRing : CommRing carrier]
  [finite : Finite carrier]
  [nontrivial : Nontrivial carrier]
  [tower : TowerBase carrier]

attribute [instance] TowerLevel.commRing TowerLevel.finite TowerLevel.nontrivial TowerLevel.tower

/-- The homogeneous `(e,h)`-tower over a base level, by `Nat`-recursion on tower height. Level `0`
is the base `L0`; level `r+1` is `RphiGenH (level r) e h 1`, itself a `TowerBase` via
`instTowerBase_RphiGenH` (each level a `TowerBase` over the last — THE inductive crux). The unit is
`1 : Rˣ` at every level. This IS the `Nat`-iterated `RphiGenH` from any `[TowerBase R]` of the
blueprint §7 deliverable 4. -/
noncomputable def towerLevel {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h)
    (L0 : TowerLevel) : ℕ → TowerLevel
  | 0 => L0
  | r + 1 =>
    let L := towerLevel he h hh L0 r
    haveI : Finite (RphiGenH L.carrier e h 1) := finite_RphiGenH he h 1
    haveI : Nontrivial (RphiGenH L.carrier e h 1) := nontrivial_RphiGenH he h 1
    haveI : TowerBase (RphiGenH L.carrier e h 1) := instTowerBase_RphiGenH he h hh 1
    { carrier := RphiGenH L.carrier e h 1 }

/-- **Deliverable 2b — `r_level_census_equiv` (the deep recursion).** The order-`r` restart
EQUIVALENCE (not just the card): a `restartEquivTower` over the level-`r` tower ring
`towerLevel … r` — each level built as a `TowerBase` over the last via `instTowerBase_RphiGenH`, by
`Nat`-recursion on tower height. Its domain is the tower cell fiber `InCellTower` (the develop-
pullback of the fresh slot pattern, the `developPhiGenH`-analogue at the top level), its codomain
the fresh-cluster-pattern coset over the level-`(r+1)` ring. This CLOSES the count-native restart
at ALL orders as a genuine `≃`: the residual D4d named in `TowerRestartAbstract` (Deliverable 4d)
is discharged by `developTower` (`developEquivGen` instantiated at each level). -/
noncomputable def r_level_census_equiv {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (μ : ℕ)
    (L0 : TowerLevel) (r : ℕ) :
    letI L := towerLevel he h hh L0 r
    {f : monicBoxGen (R := L.carrier) (μ * e) // InCellTower he h μ 1 f}
      ≃ {β : Fin μ → RphiGenH L.carrier e h 1 // FreshClusterPatternAbstract he h μ 1 β} :=
  restartEquivTower he h μ (1 : (towerLevel he h hh L0 r).carrier ˣ)

/-- The level-`r` tower ring's own `ballCount` is the compounded per-level product: the recursion of
`instTowerBase_RphiGenH`'s ball-count unfolds definitionally into the nested `dexp`-composed base
ball-count. NB the tower's per-level slope is the fixed `h` (each child `ϖ = θ` has `vUnif = h` in
the child's OWN ball), so this is the HOMOGENEOUS-`h` nested product — matching
`card_freshPatternAbstract_child`'s order-2 shape (per-slot `∏_i ∏_{i'} R.ballCount(dexp e h (dexp
e h · i) i')`), NOT the level-0-collapsed cumulative `towerBallProduct` (`dexp e (e^r·h)`). Both
count the same fiber in different valuation frames. -/
theorem towerLevel_ballCount {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h)
    (L0 : TowerLevel) (r : ℕ) (w : ℕ) :
    TowerBase.ballCount (R := (towerLevel he h hh L0 r).carrier) w
      = Nat.rec (motive := fun _ => ℕ → ℕ)
          (TowerBase.ballCount (R := L0.carrier))
          (fun _ prev w => ∏ i : Fin e, prev (dexp e h w (i : ℕ))) r w := by
  induction r generalizing w with
  | zero => rfl
  | succ n ih =>
    show (∏ i : Fin e, TowerBase.ballCount (R := (towerLevel he h hh L0 n).carrier)
            (dexp e h w (i : ℕ)))
        = ∏ i : Fin e, _
    refine Finset.prod_congr rfl fun i _ => ?_
    exact ih (dexp e h w (i : ℕ))

/-- **The `r`-level census CARD** (the deep recursion payoff, `≃` side now proved): the order-`r`
census card is the fresh-pattern card over the level-`r` tower ring — the nested per-level product
(`towerLevel_ballCount`). This is `card_restartTower_fiber` at `R = towerLevel … r`, i.e. the CARD
of `r_level_census_equiv`, matching the banked `towerBallProduct` recursion. -/
theorem card_r_level_census {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (μ : ℕ)
    (L0 : TowerLevel) (r : ℕ) :
    letI L := towerLevel he h hh L0 r
    Nat.card {f : monicBoxGen (R := L.carrier) (μ * e) // InCellTower he h μ 1 f}
      = ∏ j : Fin μ, ∏ i : Fin e,
          TowerBase.ballCount (R := (towerLevel he h hh L0 r).carrier)
            (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ)) :=
  card_restartTower_fiber he h μ (1 : (towerLevel he h hh L0 r).carrier ˣ)

end Recursion

/-! ## Deliverable 3a: reduction to concrete at `R = ZMod (p^N)` (fibers 4096/1024/16) -/

section GateConcrete

/-- **Gate — the abstract tower fiber CARD at `R = ZMod` reproduces the banked wild ramified fiber
`4096`** (`(e,h,μ)=(3,2,2)`, `p=2`, `N=5`), matching `RestartEquivGenH.gate_G1` /
`TowerRestartAbstract.gate_reduce_G1`. This certifies the reduction to the concrete `restartEquivGenH`
numerically via `restartEquivTower` at the level-0 `instTowerBase_ZMod`. -/
theorem gate_tower_reduce_G1 :
    letI := instTowerBase_ZMod 2 5 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 5)) := RphiRing.nontrivial_base 2 5 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 5)) 3 2 1) := finite_RphiGenH (by norm_num) 2 1
    Nat.card {f : monicBoxGen (R := ZMod (2 ^ 5)) (2 * 3) //
        InCellTower (by norm_num) 2 2 1 f} = 4096 := by
  letI := instTowerBase_ZMod 2 5 (by norm_num)
  haveI : Nontrivial (ZMod (2 ^ 5)) := RphiRing.nontrivial_base 2 5 (by norm_num)
  rw [card_restartTower_fiber (by norm_num) 2 2 1]
  decide

/-- **Gate — the abstract tower fiber CARD at `R = ZMod` reproduces the banked wild gapped ⟨2,3⟩
fiber `1024`** (`(e,h,μ)=(2,3,2)`, `p=2`, `N=7`), matching `RestartEquivGenH.gate_H` /
`TowerRestartAbstract.gate_reduce_H`. -/
theorem gate_tower_reduce_H :
    letI := instTowerBase_ZMod 2 7 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 7)) := RphiRing.nontrivial_base 2 7 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 7)) 2 3 1) := finite_RphiGenH (by norm_num) 3 1
    Nat.card {f : monicBoxGen (R := ZMod (2 ^ 7)) (2 * 2) //
        InCellTower (by norm_num) 3 2 1 f} = 1024 := by
  letI := instTowerBase_ZMod 2 7 (by norm_num)
  haveI : Nontrivial (ZMod (2 ^ 7)) := RphiRing.nontrivial_base 2 7 (by norm_num)
  rw [card_restartTower_fiber (by norm_num) 3 2 1]
  decide

/-- **Gate (h = 1 collapse) — the abstract tower fiber CARD at `R = ZMod` reproduces the banked
`h = 1` sanity fiber `16`** (`(e,h,μ)=(2,1,2)`, `p=2`, `N=3`), matching
`RestartEquivGenH.gate_S_h_one` / `TowerRestartAbstract.gate_reduce_S_h_one`. -/
theorem gate_tower_reduce_S_h_one :
    letI := instTowerBase_ZMod 2 3 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 3)) := RphiRing.nontrivial_base 2 3 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 3)) 2 1 1) := finite_RphiGenH (by norm_num) 1 1
    Nat.card {f : monicBoxGen (R := ZMod (2 ^ 3)) (2 * 2) //
        InCellTower (by norm_num) 1 2 1 f} = 16 := by
  letI := instTowerBase_ZMod 2 3 (by norm_num)
  haveI : Nontrivial (ZMod (2 ^ 3)) := RphiRing.nontrivial_base 2 3 (by norm_num)
  rw [card_restartTower_fiber (by norm_num) 1 2 1]
  decide

end GateConcrete

/-! ## Deliverable 3b: order-2 recovery — the tower fiber card = the banked compounded product -/

section GateOrder2

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- **Gate — order-2 recovery.** The order-2 tower census card (the tower fiber over the level-1
child ring `RphiGenH R e h c`, itself a `TowerBase` via `instTowerBase_RphiGenH`) equals the banked
compounded per-level product `card_freshPatternAbstract_child` — the W6c "compounds cleanly" number.
The order-2 `restartEquivTower` card IS `TowerRestartGenH.two_level_census_genH`'s per-slot count
(both the doubly-nested `∏_j ∏_i ∏_{i'} R.ballCount(dexp e h (dexp e h · i) i')`). This is the CARD
half of "order-2 must reproduce `two_level_census_genH`". -/
theorem gate_order2_tower_matches_child {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (c : Rˣ)
    [Finite (RphiGenH R e h c)] {μ2 : ℕ} (c2 : (RphiGenH R e h c)ˣ) :
    letI := instTowerBase_RphiGenH he h hh c
    haveI : Nontrivial (RphiGenH R e h c) := nontrivial_RphiGenH he h c
    Nat.card {f : monicBoxGen (R := RphiGenH R e h c) (μ2 * e) //
        InCellTower he h μ2 c2 f}
      = ∏ j : Fin μ2, ∏ i : Fin e,
          (∏ i' : Fin e, ballCount (R := R)
            (dexp e h (dexp e h (e * h * (μ2 - j.1) + 1) (i : ℕ)) (i' : ℕ))) := by
  letI := instTowerBase_RphiGenH he h hh c
  haveI : Nontrivial (RphiGenH R e h c) := nontrivial_RphiGenH he h c
  rw [card_restartTower_fiber he h μ2 c2]
  rfl

end GateOrder2

/-! ## Deliverable 3c: the O''-instance — `restartEquivTower` over `Oring` (the f≥2 restart) -/

section GateOring

open UnramifiedBase
open LeanUrat.OM.TowerRestartAbstract (instTowerBase_Oring)

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-- **Deliverable 3c — the O''-instance (`restartEquivTower` at `R = Oring`).** The unramified ring
`O'' = Oring p N g` is a `TowerBase` (`instTowerBase_Oring`, banked in `TowerRestartAbstract`), so
`restartEquivTower`/`card_restartTower_fiber` instantiate at `R = Oring` — the child ring
`RphiGenH O'' e h c` is the ramified Eisenstein extension of the two-step `f≥2` descent (blueprint
§3), and the fresh-cluster count is the general-base per-digit product with `ballCount k =
(p^m)^(N−min N k)` (`Q = p^m`) in place of the level-0 `p`. This SUBSUMES the W6b-f2 restart into
this ONE abstraction: the f≥2 order-`r` restart is `r_level_census_equiv` with `L0 = O''`. -/
theorem gate_Oring_restart_card (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) {e : ℕ} (he : 0 < e) (h μ : ℕ)
    (c : (Oring p N g)ˣ) :
    letI := instTowerBase_Oring p N g hgm hN hm hgirr
    haveI := finite_Oring p N g hgm hN
    haveI : Nontrivial (Oring p N g) := nontrivial_Oring p N g hgm hN hm
    Nat.card {f : monicBoxGen (R := Oring p N g) (μ * e) // InCellTower he h μ c f}
      = ∏ j : Fin μ, ∏ i : Fin e,
          (p ^ g.natDegree) ^ (N - min N (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ))) := by
  letI := instTowerBase_Oring p N g hgm hN hm hgirr
  haveI := finite_Oring p N g hgm hN
  haveI : Nontrivial (Oring p N g) := nontrivial_Oring p N g hgm hN hm
  rw [card_restartTower_fiber he h μ c]
  rfl

end GateOring

end

end LeanUrat.OM.DevelopTower
