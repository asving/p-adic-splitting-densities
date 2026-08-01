/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.Census

/-!
# Scaffold/HDischarge/H2/Carriers — census-keyed counting carriers [HDISCHARGE_H2 unit U1]

Structures VERBATIM from `lean/blueprints/HDISCHARGE_H2.md` §6 (H2-U1; revised
at review pass 1 — findings 9/10/12/13/14: `hn2`/`hmono`/`honLine_box`/`hks_top`
carrier laws added; `slotDigits` field added).

Design notes (blueprint ratification points): (i) `ParentShape.g` shape-only-ness
is enforced BY TYPE (no ρ argument); (ii) `boxSlots` carries the monic-top
erasure (K_D = {0..ℓ−1} at m | n) verbatim, and `hks_top` pins the monic-top
junction to the erased top slot; (iii) carriers are SKELETAL by the corpus's
own precedent (`Stratum1`/`StratumR` C4a provenance) — the engine's constructed
strata instantiate them at the BP_IV wave-4 seam, where the residual
conformance duties live (polygon-ledger tie, realization positivity, the
q = p^δ prime-power semantics).
-/

namespace LeanUrat.Scaffold.HDischarge.H2

open LeanUrat.Scaffold

/-- H2-U1a `WindowDatum`: the order-(r+1) window counting skeleton over census
    datum `D` (O-9 rev-5 §2 stratum datum reduced to the (FRESH)-quantified
    data: box slots, per-slot thresholds, on-line slots, junction slot).
    `onLine` = the on-line lattice slots OF THE BOX K_D (the monic top, though
    on the line, is excluded with K_D — O-9 §2). -/
structure WindowDatum (D : CensusData) where
  ℓ : ℕ
  hℓ : 1 ≤ ℓ
  /-- the polynomial degree n; hn/hn2 pin ℓ = ⌊n/m⌋, m = period·d. -/
  n : ℕ
  hn : ℓ * (D.period * D.d) ≤ n
  hn2 : n < (ℓ + 1) * (D.period * D.d)
  beta : Fin (ℓ + 1) → ℕ
  onLine : Finset (Fin (ℓ + 1))
  ks : Fin (ℓ + 1)
  monicTop : Bool
  hmono : monicTop = true ↔ (D.period * D.d) ∣ n
  boxSlots : Finset (Fin (ℓ + 1))
  hbox : boxSlots = if monicTop then Finset.univ.erase (Fin.last ℓ) else Finset.univ
  honLine_box : onLine ⊆ boxSlots
  hks_line : monicTop = false → ks ∈ onLine
  hks_top : monicTop = true → ks = Fin.last ℓ

/-- H2-U1b `ParentShape`: the discrete parent shape — level `N0` and the
    transported floors `g` (shape-only by TYPE: `g` sees no realization ρ). -/
structure ParentShape (D : CensusData) (W : WindowDatum D) where
  N0 : ℕ
  hN0 : 1 ≤ N0
  g : Fin (W.ℓ + 1) → ℕ

/-- H2-U1c `JointStratum`: the level-N joint (parent, window) stratum presented
    fiberwise — skeletal counting carrier (`Stratum1`/`StratumR` discipline).
    NON-VACUITY is NOT a carrier law: it is delivered by the de-vacuifier unit
    H2-U6 (the canonical r = 0 instance, rhoCount = 1) and owed by the engine
    seam at instantiation — the corpus's Stratum1/StratumR pattern. -/
structure JointStratum (D : CensusData) (W : WindowDatum D) (P : ParentShape D W) where
  N : ℕ
  hN : P.N0 ≤ N
  /-- number of parent realizations ρ at alphabet size q (level N0). -/
  rhoCount : ℕ → ℕ
  /-- per-realization per-slot HEIGHT-condition count at alphabet size q
      (absolute count; O-9's RELATIVE (E″) charge is this against the
      parent's q^{mN − s(g_k)} baseline). -/
  slotCount : ℕ → Fin (W.ℓ + 1) → ℕ → ℕ
  /-- per-realization per-on-line-slot per-digit-value count at size q. -/
  slotDigits : ℕ → ↥W.onLine → ℕ → ℕ → ℕ
  /-- per-realization fiber count (heights only), at alphabet size q. -/
  fiber : ℕ → ℕ → ℕ
  /-- per-realization count of boxes with prescribed on-line digit vector z. -/
  fiberDigits : ℕ → (↥W.onLine → ℕ) → ℕ → ℕ

end LeanUrat.Scaffold.HDischarge.H2
