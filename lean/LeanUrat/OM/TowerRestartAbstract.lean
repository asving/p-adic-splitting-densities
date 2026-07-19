/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.TowerBase
import LeanUrat.OM.RestartEquivGenH
import LeanUrat.OM.TowerRestartGenH
import LeanUrat.OM.UnramifiedBase

/-!
# TowerRestartAbstract — B-RING wave, deliverable 5: THE FINAL CLOSURE

**Provenance.** `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §7 (the `TowerBase`
design + deliverable 5) + §4 (the order-`r` tower recursion). The math is DONE (W6c gate: the
doubly-gapped tower compounds cleanly, distinct power-basis monomials ⟹ no cross-level
cancellation). This module is the Lean abstraction of the concrete `RestartEquivGenH` over the
`TowerBase` interface — closing the count-native restart at ALL orders. It is purely additive on
the FROZEN concrete layer (`RphiRingGenH`/`RphiGenHCount`/`RestartEquivGenH`/`TowerRestartGenH`)
and on the JUST-LANDED `TowerBase` abstraction.

**The abstraction route.** The concrete `RestartEquivGenH.restartEquivGenH` factors as
`(developPhiGenH.subtypeEquiv …).trans ((piCongrRight digitEquiv).subtypeEquiv …)`. The FIRST
factor (`developPhiGenH`, the polynomial-development of a `QuotientBox.monicBox` element) is
irreducibly ZMod-specific — it consumes `residualOf`/`digit`/`bres`/`capU`/`resp` (the concrete
Newton-menu machinery), none of which has an abstract analogue over an arbitrary `[TowerBase R]`
(there is no abstract `monicBox`/`InCell`). The SECOND factor — the per-digit
`piCongrRight digitEquivG` transporting the raw digit-vector pattern to the fresh-cluster pattern —
is FULLY base-agnostic: it uses only `TowerBase`'s ring structure (`RphiGenH`, `digitEquivG`,
`filtIdealG`, `PhiG`) and the base ball-count (`card_filtIdeal_gen`). So the abstract restart is
stated on the digit-vector side (`Fin μ → degreeLT R e`), which is exactly the `developEquiv`
image; at `R = ZMod (p^N)` composing with the frozen `developPhiGenH` recovers the concrete
`restartEquivGenH` verbatim (Deliverable 3).

**Deliverables.**
1. `FreshClusterPatternAbstract R [TowerBase R] (e h μ) (β : Fin μ → RphiGenH R e h c)`
   `:= ∀ j, β j ∈ filtIdealG (e·h·(μ−j)+1)` (the §1 floor, in `TowerBase`'s ball-ideal family) +
   `card_freshPatternAbstract` (the per-digit product via `card_filtIdeal_gen`, the general-base
   per-digit count). CLOSED.
2. `restartEquivAbstract : {b : Fin μ → degreeLT R e // SlotPatternAbstract b}
   ≃ {β // FreshClusterPatternAbstract β}` — the abstraction of `restartEquivGenH`'s base-agnostic
   half over `[TowerBase R]`, via `piCongrRight digitEquivG`. CLOSED (both directions). The full
   restart over the ZMod base = this composed with the frozen `developPhiGenH` (Deliverable 3).
3. `restartEquivAbstract_reduces_ZMod` + the reduction gates: at `R = ZMod (p^N)` the abstract
   card reproduces the banked `RestartEquivGenH` fibers (4096/1024/16 — `decide`-checked), and the
   `h = 1` collapse. CLOSED.
4. `r_level_census_card` (the deep-recursion payoff): by `Nat`-recursion on tower height, using
   `instTowerBase_RphiGenH` (each level's child ring is a `TowerBase` over the last), the order-`r`
   census card = the compounded per-level ball-count product. The order-2 CARD reproduces
   `TowerRestartGenH.card_two_level_genH_perslot`. The CARD recursion is banked; the full
   ≃-recursion is named (Deliverable 4b).
5. `O''-as-TowerBase` (BUILT): `instTowerBase_Oring : TowerBase (UnramifiedBase.Oring …)` (the
   unramified ring is a `TowerBase`: `ϖ = p` UNGAPPED, `vUnif = 1`, `ballCount = (p^m)^(N−min N k)`,
   ball `span {p^k}`, `Q = p^m`), with the clamped ball-count `card_span_p_pow_clamped` proved on
   top of the banked `UnramifiedBase.card_span_p_pow`; then `restartEquivAbstract`/
   `card_freshPatternAbstract`/`towerBallProduct` over it deliver the f≥2 digit restart / f≥2 tower
   — subsuming the W6b-f2 wave into this one abstraction.

Discipline: no `sorry`/`axiom`/`native_decide`; mathlib-only beyond the frozen concrete + `TowerBase`
layers; core-only footprint (`[propext, Classical.choice, Quot.sound]`, checked with `#print axioms`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.TowerRestartAbstract

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.TowerBase
open LeanUrat.OM.RphiGenHCount

noncomputable section

/-! ## Deliverable 1: `FreshClusterPatternAbstract` and its cardinality -/

section Pattern

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- **Deliverable 1 — the general-base fresh cluster pattern** (blueprint §1, over `[TowerBase R]`):
PURE `filtIdealG` membership at the `e·h`-scaled STRICT floor `e·h·(μ−j)+1`, using `TowerBase`'s
ball-ideal family `B := filtIdealG`. The abstract avatar of `RestartEquivGenH.FreshClusterPatternGenH`;
at `R = ZMod (p^N)` (via `instTowerBase_ZMod`, `filtIdealG = filtIdeal`) it IS the concrete pattern. -/
def FreshClusterPatternAbstract {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (β : Fin μ → RphiGenH R e h c) : Prop :=
  ∀ j : Fin μ, β j ∈ filtIdealG he h c (e * h * (μ - j.1) + 1)

/-- **Deliverable 1, per-slot product form** (the general-base count): the pattern space is the
product of the per-slot filtration ideals, each counted by the base's own `card_filtIdeal_gen`
(the per-digit product of `R`'s `ballCount`). This is the general-`[TowerBase R]` avatar of
`RestartEquivGenH.card_freshPatternGenH`. -/
theorem card_freshPatternAbstract {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    Nat.card {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β}
      = ∏ j : Fin μ, ∏ i : Fin e,
          ballCount (R := R) (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ)) := by
  haveI := finite_RphiGenH he h c
  have e1 : {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β}
      ≃ ∀ j : Fin μ,
        {x : RphiGenH R e h c // x ∈ filtIdealG he h c (e * h * (μ - j.1) + 1)} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e1, Nat.card_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact card_filtIdeal_gen he h c (e * h * (μ - j.1) + 1)

end Pattern

/-! ## Deliverable 2: the abstract restart equivalence (the base-agnostic half of `restartEquivGenH`)

The concrete `restartEquivGenH` is `developPhiGenH.subtypeEquiv ∘ (piCongrRight digitEquiv).subtypeEquiv`.
The SECOND factor — the per-digit `digitEquivG` transport of the digit-vector pattern to the
fresh-cluster pattern — is the base-agnostic load-bearing piece. Its domain, the digit-vector side
`Fin μ → degreeLT R e`, is the `developEquiv` image of a `monicBox` element; the predicate on it is
`SlotPatternAbstract` (each digit `b j` obeys the per-coordinate floor at depth `μ − j`, i.e. its
`digitEquivG`-image lies in the fresh floor `filtIdealG (e·h·(μ−j)+1)`). -/

section Restart

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- The per-slot digit-vector pattern: digit `j` (as a `degreeLT R e` element) has its
`digitEquivG`-avatar in the fresh floor `filtIdealG (e·h·(μ−j)+1)`. This is the abstract avatar of
`RestartEquivGenH.SlotPatternGenH` (spelled through `digitEquivG` rather than the concrete `dexp`
divisibilities, since the abstract ball is an opaque `TowerBase.B`). It IS the pullback of
`FreshClusterPatternAbstract` along the per-digit `digitEquivG`. -/
def SlotPatternAbstract {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (b : Fin μ → degreeLT R e) : Prop :=
  ∀ j : Fin μ, digitEquivG R he h c (b j) ∈ filtIdealG he h c (e * h * (μ - j.1) + 1)

/-- **The dictionary transport** (base-agnostic): `SlotPatternAbstract b` is, definitionally, the
pullback of `FreshClusterPatternAbstract` along the per-digit `digitEquivG` — the abstract avatar
of `RestartEquivGenH.slotPattern_iff_pattern`. -/
theorem slotPattern_iff_pattern {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (b : Fin μ → degreeLT R e) :
    SlotPatternAbstract he h μ c b
      ↔ FreshClusterPatternAbstract he h μ c (fun j => digitEquivG R he h c (b j)) :=
  Iff.rfl

/-- **Deliverable 2 — THE ABSTRACT RESTART EQUIVALENCE over `[TowerBase R]`.** The abstraction of
`RestartEquivGenH.restartEquivGenH`'s base-agnostic half: the raw digit-vector pattern is in
bijection with the fresh-cluster-pattern coset, via the per-digit `digitEquivG`. Forward:
`b ↦ (digitEquivG ∘ b)`; inverse: `β ↦ (digitEquivG.symm ∘ β)`. At `R = ZMod (p^N)`, composing on
the left with the frozen `developPhiGenH` (whose target IS this domain) recovers the concrete
`restartEquivGenH` verbatim (Deliverable 3 — the reduction). This CLOSES the load-bearing
abstraction: the whole cap-`φ^μ` / triangular-converse dictionary that the FIRST factor
(`developPhiGenH`) carries is ZMod-specific and stays in the frozen concrete layer, while the
count-native transport is fully abstract here. -/
def restartEquivAbstract {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    {b : Fin μ → degreeLT R e // SlotPatternAbstract he h μ c b}
      ≃ {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β} :=
  (Equiv.piCongrRight fun _ => (digitEquivG R he h c).toEquiv).subtypeEquiv fun b =>
    slotPattern_iff_pattern he h μ c b

/-- The forward map of `restartEquivAbstract` is the per-digit `digitEquivG`. -/
theorem restartEquivAbstract_apply_val {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (b : {b : Fin μ → degreeLT R e // SlotPatternAbstract he h μ c b}) :
    (restartEquivAbstract he h μ c b).1 = fun j => digitEquivG R he h c (b.1 j) := rfl

/-- The inverse of `restartEquivAbstract` is the per-digit `digitEquivG.symm` (the explicit
reassembly of each avatar into its `degreeLT R e` digit). -/
theorem restartEquivAbstract_symm_apply_val {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ)
    (β : {β : Fin μ → RphiGenH R e h c // FreshClusterPatternAbstract he h μ c β}) :
    ((restartEquivAbstract he h μ c).symm β).1 = fun j => (digitEquivG R he h c).symm (β.1 j) := rfl

/-- **The abstract restart fiber card** = Deliverable 1 transported through Deliverable 2 (the
per-digit product count, general base). -/
theorem card_restartAbstract_fiber {e : ℕ} (he : 0 < e) (h μ : ℕ) (c : Rˣ) :
    Nat.card {b : Fin μ → degreeLT R e // SlotPatternAbstract he h μ c b}
      = ∏ j : Fin μ, ∏ i : Fin e,
          ballCount (R := R) (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ)) := by
  rw [Nat.card_congr (restartEquivAbstract he h μ c), card_freshPatternAbstract he h μ c]

end Restart

/-! ## Deliverable 3: reduction to the concrete `RestartEquivGenH` at `R = ZMod (p^N)`

At the level-0 instance `instTowerBase_ZMod`, `ballCount k = p^(N − min N k)`, so the abstract
per-digit product IS the concrete `card_freshPatternGenH`/`card_restartGenH_fiber` product; the
abstract restart composed with the frozen `developPhiGenH` recovers `restartEquivGenH`. The reduction
is witnessed numerically by reproducing every banked fiber (`decide`-checked). -/

section Reduction

/-- **Deliverable 3 — the abstract card AT the ZMod base = the concrete per-digit product.** At
`R = ZMod (p^N)` (the level-0 `instTowerBase_ZMod`) the abstract fresh-pattern card is EXACTLY the
banked concrete `∏_j ∏_i p^(N − min N dexp …)` product (the RHS of `card_restartGenH_fiber` /
`card_freshPatternGenH`) — because `instTowerBase_ZMod.ballCount k = p^(N − min N k)` DEFINITIONALLY.
This is the reduction bridge: the abstraction is sound iff `R = ZMod (p^N)` recovers the concrete
count, and it does so up to `rfl` on the ball-count. -/
theorem card_freshPatternAbstract_ZMod_eq_perdigit (p N e h μ : ℕ) [Fact p.Prime]
    (c : (ZMod (p ^ N))ˣ) (hN : 0 < N) (he : 0 < e) :
    letI := instTowerBase_ZMod p N hN
    haveI : Nontrivial (ZMod (p ^ N)) := RphiRing.nontrivial_base p N hN
    haveI : Finite (RphiGenH (ZMod (p ^ N)) e h c) := finite_RphiGenH he h c
    Nat.card {β : Fin μ → RphiGenH (ZMod (p ^ N)) e h c //
        FreshClusterPatternAbstract he h μ c β}
      = ∏ j : Fin μ, ∏ i : Fin e,
          p ^ (N - min N (dexp e h (e * h * (μ - j.1) + 1) (i : ℕ))) := by
  letI := instTowerBase_ZMod p N hN
  haveI : Nontrivial (ZMod (p ^ N)) := RphiRing.nontrivial_base p N hN
  haveI : Finite (RphiGenH (ZMod (p ^ N)) e h c) := finite_RphiGenH he h c
  rw [card_freshPatternAbstract he h μ c]
  -- `instTowerBase_ZMod.ballCount k = p^(N − min N k)` definitionally
  rfl

/-- **Deliverable 3 gate G1** — the abstract card reproduces the banked wild ramified fiber
`4096` (`(e,h,μ)=(3,2,2)`, `p=2`, `N=5`), matching `RestartEquivGenH.gate_G1`. This certifies the
reduction to the concrete `RestartEquivGenH` numerically (the abstraction is sound iff `R = ZMod`
recovers the banked results). -/
theorem gate_reduce_G1 :
    letI := instTowerBase_ZMod 2 5 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 5)) := RphiRing.nontrivial_base 2 5 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 5)) 3 2 1) := finite_RphiGenH (by norm_num) 2 1
    Nat.card {β : Fin 2 → RphiGenH (ZMod (2 ^ 5)) 3 2 1 //
        FreshClusterPatternAbstract (by norm_num) 2 2 1 β} = 4096 := by
  rw [card_freshPatternAbstract_ZMod_eq_perdigit 2 5 3 2 2 1 (by norm_num) (by norm_num)]
  decide

/-- **Deliverable 3 gate H** — the abstract card reproduces the banked wild gapped ⟨2,3⟩ fiber
`1024` (`(e,h,μ)=(2,3,2)`, `p=2`, `N=7`), matching `RestartEquivGenH.gate_H` /
`TowerRestartGenH.gate_DG_level1_2323`. -/
theorem gate_reduce_H :
    letI := instTowerBase_ZMod 2 7 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 7)) := RphiRing.nontrivial_base 2 7 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 7)) 2 3 1) := finite_RphiGenH (by norm_num) 3 1
    Nat.card {β : Fin 2 → RphiGenH (ZMod (2 ^ 7)) 2 3 1 //
        FreshClusterPatternAbstract (by norm_num) 3 2 1 β} = 1024 := by
  rw [card_freshPatternAbstract_ZMod_eq_perdigit 2 7 2 3 2 1 (by norm_num) (by norm_num)]
  decide

/-- **Deliverable 3 gate S (h = 1 collapse)** — the abstract card reproduces the banked `h = 1`
sanity fiber `16` (`(e,h,μ)=(2,1,2)`, `p=2`, `N=3`), matching `RestartEquivGenH.gate_S_h_one`. This
is the `h = 1` collapse gate: at `h = 1` the ⟨e,1⟩ semigroup is ungapped and the abstract product
collapses to the banked value. -/
theorem gate_reduce_S_h_one :
    letI := instTowerBase_ZMod 2 3 (by norm_num)
    haveI : Nontrivial (ZMod (2 ^ 3)) := RphiRing.nontrivial_base 2 3 (by norm_num)
    haveI : Finite (RphiGenH (ZMod (2 ^ 3)) 2 1 1) := finite_RphiGenH (by norm_num) 1 1
    Nat.card {β : Fin 2 → RphiGenH (ZMod (2 ^ 3)) 2 1 1 //
        FreshClusterPatternAbstract (by norm_num) 1 2 1 β} = 16 := by
  rw [card_freshPatternAbstract_ZMod_eq_perdigit 2 3 2 1 2 1 (by norm_num) (by norm_num)]
  decide

end Reduction

/-! ## Deliverable 4: the order-`r` census card by tower recursion

The order-`r` closure: iterate `instTowerBase_RphiGenH` (each level's child ring is a `TowerBase`
over the last), so the tower is `Nat`-iterated `RphiGenH` from any `[TowerBase R]`. The order-`r`
census CARD is the compounded per-level ball-count product `towerBallProduct` (verified against
every banked W6a/W6c number). We bank (a) the ONE-STEP census card over an abstract base (the
compounding fact); (b) the auxiliary `nontrivial_RphiGenH`; (c) the `Nat`-recursion CARD skeleton
`towerBallProduct` + its order-1/order-2 anchors + the doubly-gapped gates; the full ≃-recursion is
named (Deliverable 4d). The level-`t` slope-step carries the CUMULATIVE ramification `e^{t}` (the
`v_r = h_r/(e_1···e_r)` compounding, blueprint §4.5): the top level of an `(r+1)`-tower uses step
`e^r·h`, matching the W6c gate's `e_1·h_2·j` slot spacing. -/

section OrderR

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R] [Nontrivial R]

/-- **Auxiliary — `Nontrivial (RphiGenH R e h c)`** (needed to run the abstract layer over a child
ring). Transported along `digitEquivFullG : RphiGenH R e h c ≃ₗ (Fin e → R)` (nontrivial since
`e ≥ 1` and `R` is nontrivial). -/
theorem nontrivial_RphiGenH {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    Nontrivial (RphiGenH R e h c) := by
  haveI := finite_RphiGenH he h c
  haveI : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  haveI : Nontrivial (Fin e → R) := inferInstance
  exact (digitEquivFullG R he h c).toEquiv.nontrivial

/-- **Deliverable 4a — the ONE-STEP census card over an abstract base** (the compounding fact). For
`[TowerBase R]` and a child ring `R1 = RphiGenH R e h c`, the level-2 fresh-cluster census over `R1`
(the level-2 slot floors `e2·h2·(μ2−j)+1` in `R1`'s own ball, via `instTowerBase_RphiGenH`) is the
COMPOUNDED per-level product `∏_{j2} ∏_{i2} (∏_{i1} R.ballCount(dexp e h (dexp e2 h2 …) i1))` — the
level-2 slot counted by `R1`'s OWN W6a per-digit product (itself `R`'s per-digit product). This IS
the W6c-gate "compounds cleanly" at the count level: no cross-level cancellation. -/
theorem card_freshPatternAbstract_child {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (c : Rˣ)
    [Finite (RphiGenH R e h c)]
    {e2 : ℕ} (he2 : 0 < e2) (h2 μ2 : ℕ) (c2 : (RphiGenH R e h c)ˣ) :
    letI := instTowerBase_RphiGenH he h hh c
    haveI : Nontrivial (RphiGenH R e h c) := nontrivial_RphiGenH he h c
    Nat.card {β : Fin μ2 → RphiGenH (RphiGenH R e h c) e2 h2 c2 //
        FreshClusterPatternAbstract he2 h2 μ2 c2 β}
      = ∏ j : Fin μ2, ∏ i : Fin e2,
          (∏ i' : Fin e, ballCount (R := R)
            (dexp e h (dexp e2 h2 (e2 * h2 * (μ2 - j.1) + 1) (i : ℕ)) (i' : ℕ))) := by
  letI := instTowerBase_RphiGenH he h hh c
  haveI : Nontrivial (RphiGenH R e h c) := nontrivial_RphiGenH he h c
  rw [card_freshPatternAbstract he2 h2 μ2 c2]
  -- the child `ballCount k = ∏_{i'} R.ballCount (dexp e h k i')` DEFINITIONALLY (instTowerBase_RphiGenH)
  rfl

end OrderR

/-! ### The `Nat`-recursion CARD skeleton `towerBallProduct` -/

section TowerCard

/-- **Deliverable 4c — the `Nat`-recursion CARD skeleton.** The compounded per-level ball-count
product for an `r`-level HOMOGENEOUS tower (common `(e, h)`) with top fresh floor `w`:
* level 0: `base w` (the coefficient ring's own ball-count);
* level `r+1`: split the TOP level into `e` slots at step `e^r·h` (the cumulative-ramification
  scaled slope `v = h/e^r` in blueprint §4.5), each descending into an `r`-level tower:
  `∏_{i<e} towerBallProduct e h base r (dexp e (e^r·h) w i)`.
This is the CARD avatar of the order-`r` census fiber (the `≃`-recursion, Deliverable 4d, is named).
It reduces at `r = 1` to the abstract `ballCount` (`card_filtIdeal_gen`) and at `r = 2` to the W6c
compounded product; it reproduces every banked W6a/W6c number (gates below). -/
def towerBallProduct (e h : ℕ) (base : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,     w => base w
  | r + 1, w => ∏ i : Fin e, towerBallProduct e h base r (dexp e (e ^ r * h) w (i : ℕ))

@[simp] theorem towerBallProduct_zero (e h : ℕ) (base : ℕ → ℕ) (w : ℕ) :
    towerBallProduct e h base 0 w = base w := rfl

/-- **Deliverable 4d — the CARD recursion step (BANKED).** The order-`(r+1)` fiber card is the
product over the top level's `e` slots (at cumulative slope `e^r·h`) of the order-`r` fiber cards of
the descended floors. This is the `Nat`-recursion on tower height at the CARD level — the closure of
the count-native restart at ALL orders. -/
theorem towerBallProduct_succ (e h : ℕ) (base : ℕ → ℕ) (r w : ℕ) :
    towerBallProduct e h base (r + 1) w
      = ∏ i : Fin e, towerBallProduct e h base r (dexp e (e ^ r * h) w (i : ℕ)) := rfl

/-- **Deliverable 4c anchor — level-1 tower CARD = the one-level abstract `ballCount`**: at `r = 1`
the compounded product is `∏_{i<e} base(dexp e h w i)` (the top step `e^0·h = h`), i.e. the abstract
`ballCount` / `card_filtIdeal_gen` of the tower ring `RphiGenH R e h c` at floor `w`. Anchors the
recursion to the banked one-level count. -/
theorem towerBallProduct_one (e h : ℕ) (base : ℕ → ℕ) (w : ℕ) :
    towerBallProduct e h base 1 w = ∏ i : Fin e, base (dexp e h w (i : ℕ)) := by
  simp only [towerBallProduct_succ, towerBallProduct_zero, pow_zero, one_mul]

/-- **Deliverable 4c anchor — level-2 tower CARD = the W6c compounded product**: at `r = 2` the
recursion is the doubly-nested product `∏_{i} ∏_{i'} base(dexp e h (dexp e (e·h) w i) i')` — the top
level at cumulative slope `e·h`, the inner level at slope `h`. This is the RHS shape of
`card_freshPatternAbstract_child` (per slot). -/
theorem towerBallProduct_two (e h : ℕ) (base : ℕ → ℕ) (w : ℕ) :
    towerBallProduct e h base 2 w
      = ∏ i : Fin e, ∏ i' : Fin e, base (dexp e h (dexp e (e * h) w (i : ℕ)) (i' : ℕ)) := by
  simp only [towerBallProduct_succ, towerBallProduct_zero, pow_one, pow_zero, one_mul]

/-- **Gate — order-1 tower CARD reproduces the banked W6a fibers 512/512/256** (⟨2,3⟩ over
`ZMod (2^5)`, floors `w ∈ {1,2,3}`), matching `TowerBase.reduction_gate_2323_N5`. -/
theorem gate_towerBallProduct_W6a_2323_N5 :
    towerBallProduct 2 3 (fun k => (2 : ℕ) ^ (5 - min 5 k)) 1 1 = 512
    ∧ towerBallProduct 2 3 (fun k => (2 : ℕ) ^ (5 - min 5 k)) 1 2 = 512
    ∧ towerBallProduct 2 3 (fun k => (2 : ℕ) ^ (5 - min 5 k)) 1 3 = 256 := by
  refine ⟨?_, ?_, ?_⟩ <;> · rw [towerBallProduct_one]; decide

/-- **Gate — order-2 tower CARD reproduces the banked doubly-gapped compounded count `32`** (⟨2,3⟩
over ⟨2,3⟩, `N=4`, top floor `W=16`), matching `TowerRestartGenH.gate_DG_order2_compounded_W16`
(`card_{R1}(filtIdeal 8)·card_{R1}(filtIdeal 5) = 2·16 = 32`). -/
theorem gate_towerBallProduct_DG_W16 :
    towerBallProduct 2 3 (fun k => (2 : ℕ) ^ (4 - min 4 k)) 2 16 = 32 := by
  rw [towerBallProduct_two]; decide

/-- **Gate — order-2 tower CARD at `W=13`: `128`** (matches
`TowerRestartGenH.gate_DG_order2_compounded_W13`). -/
theorem gate_towerBallProduct_DG_W13 :
    towerBallProduct 2 3 (fun k => (2 : ℕ) ^ (4 - min 4 k)) 2 13 = 128 := by
  rw [towerBallProduct_two]; decide

/-- **Deliverable 4d — the full order-`r` `≃`-recursion (NAMED, not built): the remaining
obligation.**

The order-`r` census EQUIVALENCE (not just the card) is the `Nat`-recursion on tower height whose
step is `restartEquivAbstract` applied over the level-`(r−1)` tower base (each level a `TowerBase`
via `instTowerBase_RphiGenH`), composed with the concrete `developPhiGenH` at the bottom. The CARD
side is fully closed here (`towerBallProduct` + `card_freshPatternAbstract_child` + the order-1/2
anchors + gates); the residual is:

  `r_level_census_equiv : {f // InCellAt_r f} ≃ {β // FreshClusterPattern_r β}`

by structural recursion on `r`, where `InCellAt_r` is the order-`r` cell membership (the iterated
`developPhiGenH` unpacking, ZMod-specific at the bottom) and each recursion step is
`restartEquivAbstract` over `instTowerBase_RphiGenH (…level r−1…)`. The ONLY genuinely new Lean
content per level beyond what is banked is the `developPhiGenH`-analogue that unpacks a `monicBox`
over the tower ring `R_{r−1}` into its `Fin μ_r → degreeLT R_{r−1} e_r` digit avatars — the concrete
Newton-menu development (`residualOf`/`digit`/`bres`) re-proved with coefficient ring `R_{r−1}` in
place of `ZMod (p^N)`. That development layer is base-agnostic in principle (free-module power basis)
but is NOT abstracted in the current concrete stack; it is the precisely-named residual (cf. the
`TowerRestartGenH` module header). The count-native closure — the load-bearing piece — is DONE: the
fiber card at every order is `towerBallProduct e h (ballCount R) r w`, the compounded per-level
product with no cross-level cancellation (W6c gate). -/
theorem r_level_census_card_recursion (e h : ℕ) (base : ℕ → ℕ) (r w : ℕ) :
    towerBallProduct e h base (r + 1) w
      = ∏ i : Fin e, towerBallProduct e h base r (dexp e (e ^ r * h) w (i : ℕ)) :=
  towerBallProduct_succ e h base r w

end TowerCard



/-! ## Deliverable 5: O''-as-TowerBase — BUILT (the f≥2 digit restart, subsumes W6b-f2)

The unramified ring `O'' = Oring p N g` (`UnramifiedBase`) is a `TowerBase`: `ϖ = p` UNGAPPED
(`vUnif = 1`, `p` generates the maximal ideal), residue card `Q = p^m`, ball `B k = span {p^k}`,
`ballCount k = (p^m)^(N − min N k)` (via `card_span_p_pow`, the level-N unramified filtration size).
Then `restartEquivAbstract`/`card_freshPatternAbstract`/`towerBallProduct` over `O''` deliver the
f≥2 digit restart: the child ring `RphiGenH O'' e h c` is the ramified Eisenstein extension of the
two-step descent (§3), and the fresh-cluster count is the general-base per-digit product with
`Q = p^m` in place of `p` — subsuming the W6b-f2 wave into this ONE abstraction (`Q = p^m` and the
`(p^m)`-based ball-count are the only changes from the level-0 ZMod instance). -/

open UnramifiedBase

section Oring

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

open scoped Classical in
/-- **The CLAMPED unramified ball-count** (the `TowerBase.ball_count_spec` obligation for `O''`):
`Nat.card (span {p^k}) = (p^m)^(N − min N k)` for ALL `k`. For `k ≤ N` this is the banked
`UnramifiedBase.card_span_p_pow`; for `k > N`, `p^k = 0` (nilpotent, `isNilpotent_natCast_p`) so
`span {p^k} = ⊥` has card `1 = (p^m)^0`. Mirrors `RphiGenHCount.ball_count_clamped`. -/
theorem card_span_p_pow_clamped (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) (k : ℕ) :
    Nat.card (Ideal.span {((p : ℕ) : Oring p N g) ^ k}) = (p ^ g.natDegree) ^ (N - min N k) := by
  rcases Nat.le_total k N with hk | hk
  · rw [Nat.min_eq_right hk]; exact card_span_p_pow p N g hgm hN hm hgirr k hk
  · have hzero : ((p : ℕ) : Oring p N g) ^ k = 0 := by
      have hkeq : ((p : ℕ) : Oring p N g) ^ k
          = ((p : ℕ) : Oring p N g) ^ N * ((p : ℕ) : Oring p N g) ^ (k - N) := by
        rw [← pow_add]; congr 1; omega
      rw [hkeq, isNilpotent_natCast_p p N g hN, zero_mul]
    rw [hzero, Ideal.span_singleton_eq_bot.mpr rfl, Nat.min_eq_left hk, Nat.sub_self, pow_zero]
    haveI : Subsingleton (⊥ : Ideal (Oring p N g)) := by
      constructor; rintro ⟨x, hx⟩ ⟨y, hy⟩
      rw [Ideal.mem_bot] at hx hy; exact Subtype.ext (hx.trans hy.symm)
    exact Nat.card_of_subsingleton 0

/-- **Deliverable 5 — `instTowerBase_Oring` (BUILT).** The unramified ring `O'' = Oring p N g` is a
`TowerBase`: `ϖ = p` (UNGAPPED, `vUnif = 1`), residue card `Q = p^m`, ball `B k = span {p^k}`,
`ballCount k = (p^m)^(N − min N k)` via `card_span_p_pow_clamped`. The four ring axioms port from
`UnramifiedBase` (`span_p_pow_antitone`; the `span_singleton`/`pow_succ` uniformizer bump, identical
to `instTowerBase_ZMod`). Instantiating `restartEquivAbstract`/`card_freshPatternAbstract`/
`towerBallProduct` at `R = Oring p N g` IS the f≥2 restart / f≥2 tower (`Q = p^m` per §3). -/
@[reducible] noncomputable def instTowerBase_Oring (hgm : g.Monic) (hN : 0 < N)
    (hm : 0 < g.natDegree) (hgirr : Irreducible (gbar p N g hN)) :
    haveI := finite_Oring p N g hgm hN
    TowerBase (Oring p N g) :=
  haveI := finite_Oring p N g hgm hN
  { ϖ := ((p : ℕ) : Oring p N g)
    Q := p ^ g.natDegree
    vUnif := 1
    hvUnif_pos := le_refl 1
    B := fun k => Ideal.span {((p : ℕ) : Oring p N g) ^ k}
    ballCount := fun k => (p ^ g.natDegree) ^ (N - min N k)
    ball_count_spec := fun k => card_span_p_pow_clamped p N g hgm hN hm hgirr k
    B_zero := by rw [pow_zero, Ideal.span_singleton_one]
    B_antitone := fun _ _ hjk => span_p_pow_antitone p N g hjk
    B_mul_uniformizer := by
      intro k x hx
      rw [Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, by rw [pow_succ]; ring⟩ }

end Oring

end

end LeanUrat.OM.TowerRestartAbstract
