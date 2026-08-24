/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130a

/-!
# Uniformity.ChapC.C130tr — the canonical terminal receiver (chain-carrier node CC-3)

**Chain-carrier node CC-3** (`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md`, §4 and the
§10 node table: *"Construct the recursive `TerminalReceiver` with `Kt = W.fld r`; prove every
step square and injectivity"*).  This file constructs, for a C.83 `DeepTower`, the canonical
`TerminalReceiver` instance re-homed at C.130a: the terminal equivalence is `RingEquiv.refl`
at the top, the level homomorphisms are the telescope's recursively composed step embeddings
into level `r`, every step square is PROVED (`towerHom_step`, and the receiver's own
`levelHom_step` field), and every level map is injective (`TerminalReceiver.levelHom_injective`
— a ring hom out of a field).

## The construction

* `DeepTower.stepEmb W j` — the one-rung embedding `K_j →+* K_{j+1}`: adjoin the letter
  (`AdjoinRoot.of (ψ j)`), then pull back along the `step j` iterate witness.  This composite
  is BYTE-IDENTICAL to the inner map of `TerminalReceiver.levelHom_step`, so the receiver's
  step square holds for it definitionally once the level maps are the step composites.
* `DeepTower.climbTo W d j` — the step composite `K_j →+* K_r`, by structural recursion on the
  remaining fuel `d` with `j + d = r` (base: the identity at the terminal level; step: one
  `stepEmb` then climb from `j + 1`).  Keeping the CODOMAIN pinned at `r` makes every
  recursive composite typecheck with no index cast; the single cast lives in the base case,
  where it reduces definitionally by proof irrelevance.
* `DeepTower.towerHom W j` — `climbTo` at fuel `r - j`: the canonical level map on the live
  range, with `towerHom_terminal` (identity at `j = r`) and `towerHom_step` (the step square).
* `DeepTower.terminalReceiver W junk` — the receiver itself, with `Kt := W.fld r` and
  `topEquiv := RingEquiv.refl`.

## ⚠ The honest junk-level finding (why `junk` is an argument)

`TerminalReceiver.levelHom` is TOTAL over `j : ℕ` (freeze v2's D-TIF-3 discipline), but C.83's
telescope pins `fld j` only on the live range: `fld 0` (when `0 < r`) and `fld j` for `j > r`
are arbitrary fields, and the hom type `W.fld j →+* W.fld r` can be EMPTY off the live range
(e.g. junk `fld j = ℚ` against a positive-characteristic `fld r` — ring homs of fields are
injective and preserve characteristic).  So the canonical receiver CANNOT be constructed from
the bare telescope alone; the exact missing datum is a family of junk-level fillers

```
junk : ∀ j, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)
```

carried as an explicit argument (the `j ≠ r` guard exempts the degenerate `r = 0` terminal,
which the identity fills).  `terminalReceiver_nonempty_iff` PROVES this is exactly the
obstruction — receiver existence at `Kt = W.fld r` is equivalent to junk-level fillability —
so nothing was weakened: the live-range content is unconditional
(`terminalReceiver_levelHom_live` shows the receiver never reads `junk` on the live range).
At the campaign's first full instance the argument is trivial: C.97's `s2Witness` sets
`fld := fun _ => stageField …` (constant), so `RingHom.id` fills every junk level (CC-17's
job, not taken here).

## Status

Zero `sorry`; no new axiom; axiom footprint Lean-core only (AxCheck footer).  New structure
fields: none (the receiver is C.130a's, unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

/-- `StageLive` is a decidable range condition (it unfolds to `1 ≤ j ∧ j ≤ r`); registered so
the canonical receiver's level-map family can branch on liveness with `dite`.  (The branch is
decidable; the receiver defs below are `noncomputable` only through `AdjoinRoot`'s ring
instance.) -/
-- [orchestrator 2026-08-24] private: C130k declares the public instance of the same name;
-- co-importing both files collided at import (CC-9's SUPPLY finding).
private instance instDecidableStageLive (r j : ℕ) : Decidable (StageLive r j) :=
  inferInstanceAs (Decidable (1 ≤ j ∧ j ≤ r))

section Telescope

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

namespace DeepTower

/-- CC-3: the telescope's one-rung ring embedding `K_j →+* K_{j+1}` (live `1 ≤ j < r`):
adjoin the level-`(j+1)` letter, then pull back along the `step` iterate witness.  This is
byte-identical to the inner composite of `TerminalReceiver.levelHom_step`. -/
noncomputable def stepEmb (W : DeepTower F H₀ hpin r) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    W.fld j →+* W.fld (j + 1) :=
  (W.step j hj1 hjr).symm.toRingHom.comp (AdjoinRoot.of (W.ψ j))

/-- CC-3 injectivity, one rung: a ring hom out of a field is injective. -/
theorem stepEmb_injective (W : DeepTower F H₀ hpin r) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    Function.Injective (W.stepEmb j hj1 hjr) :=
  RingHom.injective _

/-- CC-3: the recursive step composite `K_j →+* K_r`, by structural recursion on the fuel `d`
with `j + d = r`.  The codomain is pinned at `r` throughout, so the recursive case needs no
index cast; the base case's cast is by `subst` and reduces definitionally (proof
irrelevance). -/
noncomputable def climbTo (W : DeepTower F H₀ hpin r) :
    (d : ℕ) → (j : ℕ) → 1 ≤ j → j + d = r → (W.fld j →+* W.fld r)
  | 0, j, _, h => by
      have hj : j = r := h
      subst hj
      exact RingHom.id _
  | d + 1, j, hj1, h =>
      (W.climbTo d (j + 1) (by omega) (by omega)).comp (W.stepEmb j hj1 (by omega))

/-- The fuel argument of `climbTo` is proof-irrelevant bookkeeping: equal fuels give equal
composites. -/
theorem climbTo_congr (W : DeepTower F H₀ hpin r) {d d' : ℕ} (hd : d = d')
    {j : ℕ} (hj1 : 1 ≤ j) (h : j + d = r) :
    W.climbTo d j hj1 h = W.climbTo d' j hj1 (hd ▸ h) := by
  subst hd; rfl

/-- CC-3 injectivity, composite: every `climbTo` is a ring hom out of a field. -/
theorem climbTo_injective (W : DeepTower F H₀ hpin r) (d j : ℕ)
    (hj1 : 1 ≤ j) (h : j + d = r) :
    Function.Injective (W.climbTo d j hj1 h) :=
  RingHom.injective _

/-- CC-3: the canonical level map `K_j →+* K_r` on the live range — the telescope's step
composite from level `j` into the terminal level. -/
noncomputable def towerHom (W : DeepTower F H₀ hpin r) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    W.fld j →+* W.fld r :=
  W.climbTo (r - j) j hj1 (Nat.add_sub_cancel' hjr)

/-- CC-3: at the terminal level the canonical map is the identity. -/
theorem towerHom_terminal (W : DeepTower F H₀ hpin r) (h1 : 1 ≤ r) :
    W.towerHom r h1 le_rfl = RingHom.id (W.fld r) := by
  unfold towerHom
  rw [W.climbTo_congr (Nat.sub_self r)]
  rfl

/-- ★ CC-3, **the step square**: on the live range the canonical level map factors through
one rung — `K_j → K_{j+1} → K_r` commutes with `K_j → K_r`.  This is the content of the
receiver's `levelHom_step` field. -/
theorem towerHom_step (W : DeepTower F H₀ hpin r) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r) :
    W.towerHom j hj1 hjr.le =
      (W.towerHom (j + 1) (Nat.le_add_left 1 j) hjr).comp (W.stepEmb j hj1 hjr) := by
  unfold towerHom
  rw [W.climbTo_congr (show r - j = (r - (j + 1)) + 1 by omega)]
  rfl

/-- CC-3 injectivity, live level map. -/
theorem towerHom_injective (W : DeepTower F H₀ hpin r) (j : ℕ) (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    Function.Injective (W.towerHom j hj1 hjr) :=
  RingHom.injective _

end DeepTower

end Telescope

section Receiver

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

namespace DeepTower

/-- CC-3: the total level-map family of the canonical receiver — the step composite on the
live range, the identity at a degenerate (`r = 0`) terminal, and the supplied junk-level
filler elsewhere (see the module docstring: off the live range the hom type can be empty, so
the filler is a genuine extra datum, not a derivable default). -/
noncomputable def receiverLevelHom (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)) (j : ℕ) :
    W.fld j →+* W.fld r :=
  if h : StageLive r j then W.towerHom j h.1 h.2
  else if hr : j = r then by subst hr; exact RingHom.id _
  else junk j h hr

/-- On the live range the receiver's level map is the canonical step composite — in
particular it does NOT read `junk` (the non-swallowing audit for this node). -/
theorem receiverLevelHom_live (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r))
    {j : ℕ} (hj : StageLive r j) :
    receiverLevelHom W junk j = W.towerHom j hj.1 hj.2 :=
  dif_pos hj

/-- ★ **NODE CC-3 — the canonical terminal receiver at `Kt = W.fld r`**: terminal equivalence
`RingEquiv.refl`, level maps the telescope's step composites, step squares proved
(`towerHom_step` discharges the `levelHom_step` field).  The `junk` argument is the exact
missing telescope datum off the live range (`terminalReceiver_nonempty_iff`); it is never
read on the live range (`receiverLevelHom_live`). -/
noncomputable def terminalReceiver (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)) :
    TerminalReceiver F H₀ hpin r W (W.fld r) where
  topEquiv := RingEquiv.refl (W.fld r)
  levelHom := receiverLevelHom W junk
  levelHom_terminal := by
    rcases Nat.eq_zero_or_pos r with h0 | h1
    · subst h0
      have hns : ¬ StageLive 0 0 := fun h => by
        have h1 : (1 : ℕ) ≤ 0 := h.1
        omega
      unfold receiverLevelHom
      rw [dif_neg hns, dif_pos rfl]
      rfl
    · rw [receiverLevelHom_live W junk ⟨h1, le_rfl⟩, W.towerHom_terminal h1,
        RingEquiv.toRingHom_refl]
  levelHom_step := by
    intro j hj1 hjr
    rw [receiverLevelHom_live W junk ⟨hj1, hjr.le⟩,
      receiverLevelHom_live W junk ⟨Nat.le_add_left 1 j, hjr⟩]
    exact W.towerHom_step j hj1 hjr

/-- The canonical receiver's terminal equivalence is definitionally the identity. -/
theorem terminalReceiver_topEquiv (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)) :
    (W.terminalReceiver junk).topEquiv = RingEquiv.refl (W.fld r) :=
  rfl

/-- On the live range the canonical receiver's level map is the step composite (the
junk-independence audit, restated at the receiver). -/
theorem terminalReceiver_levelHom_live (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r))
    {j : ℕ} (hj : StageLive r j) :
    (W.terminalReceiver junk).levelHom j = W.towerHom j hj.1 hj.2 :=
  receiverLevelHom_live W junk hj

/-- ★ CC-3 exactness certificate: a receiver at `Kt = W.fld r` exists IFF every junk level
admits a ring hom into the terminal field.  Forward: the receiver's own level maps.
Backward: the canonical construction.  So the `junk` argument of `terminalReceiver` is
exactly the missing telescope datum — no weakening, no swallowing. -/
theorem terminalReceiver_nonempty_iff (W : DeepTower.{0, uKt} F H₀ hpin r) :
    Nonempty (TerminalReceiver F H₀ hpin r W (W.fld r)) ↔
      ∀ j : ℕ, ¬ StageLive r j → j ≠ r → Nonempty (W.fld j →+* W.fld r) := by
  constructor
  · rintro ⟨R⟩ j _ _
    exact ⟨R.levelHom j⟩
  · intro h
    exact ⟨W.terminalReceiver fun j hj hjr => (h j hj hjr).some⟩

end DeepTower

/-- ★ CC-3 injectivity, in full generality: EVERY level map of ANY terminal receiver is
injective — each level is a field, and ring homs out of a field are injective.  This covers
junk levels too, with no liveness hypothesis. -/
theorem TerminalReceiver.levelHom_injective {W : DeepTower.{0, uKt} F H₀ hpin r}
    {Kt : Type uKt} [Field Kt] (R : TerminalReceiver F H₀ hpin r W Kt) (j : ℕ) :
    Function.Injective (R.levelHom j) :=
  RingHom.injective _

/-- CC-3 injectivity, specialized to the canonical receiver (the node's exit condition). -/
theorem DeepTower.terminalReceiver_levelHom_injective (W : DeepTower.{0, uKt} F H₀ hpin r)
    (junk : ∀ j : ℕ, ¬ StageLive r j → j ≠ r → (W.fld j →+* W.fld r)) (j : ℕ) :
    Function.Injective ((W.terminalReceiver junk).levelHom j) :=
  TerminalReceiver.levelHom_injective _ j

end Receiver

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.stepEmb
#print axioms Uniformity.Density.Tower.DeepTower.stepEmb_injective
#print axioms Uniformity.Density.Tower.DeepTower.climbTo
#print axioms Uniformity.Density.Tower.DeepTower.climbTo_congr
#print axioms Uniformity.Density.Tower.DeepTower.climbTo_injective
#print axioms Uniformity.Density.Tower.DeepTower.towerHom
#print axioms Uniformity.Density.Tower.DeepTower.towerHom_terminal
#print axioms Uniformity.Density.Tower.DeepTower.towerHom_step
#print axioms Uniformity.Density.Tower.DeepTower.towerHom_injective
#print axioms Uniformity.Density.Tower.DeepTower.receiverLevelHom
#print axioms Uniformity.Density.Tower.DeepTower.receiverLevelHom_live
#print axioms Uniformity.Density.Tower.DeepTower.terminalReceiver
#print axioms Uniformity.Density.Tower.DeepTower.terminalReceiver_topEquiv
#print axioms Uniformity.Density.Tower.DeepTower.terminalReceiver_levelHom_live
#print axioms Uniformity.Density.Tower.DeepTower.terminalReceiver_nonempty_iff
#print axioms Uniformity.Density.Tower.TerminalReceiver.levelHom_injective
#print axioms Uniformity.Density.Tower.DeepTower.terminalReceiver_levelHom_injective

end AxCheck
