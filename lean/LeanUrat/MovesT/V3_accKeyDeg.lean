/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V3 `accEF_keyDeg` — the E·F = key-degree leg (MOVES 7078–7080), SPECIES
vocabulary. DOCSTRING DUTY: the cluster-degree·μ leg lives at T-V9 (node side); this
unit claims nothing beyond the E·F = D′ telescope. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Front-peeling telescope: for any chain along `StageLaws`, with per-step multiplier
`f` satisfying `a.D * f a = b.D` on adjacent pairs, the head's `D` times `∏ f`
equals `f last * last.D`. (With a root head `D = 1` this is the `∏(e·g)` telescope.)
No coherence/budget needed — pure `D`-bookkeeping. -/
private theorem accEF_telescope {f : MovesSp.Species → ℕ}
    (hstep : ∀ a b : MovesSp.Species, MovesSp.StageLaws a b → a.D * f a = b.D) :
    ∀ (l : List MovesSp.Species), l.Chain' MovesSp.StageLaws →
      ∀ h : MovesSp.Species, l.head? = some h →
      ∀ s : MovesSp.Species, l.getLast? = some s →
      h.D * (l.map f).prod = f s * s.D := by
  intro l
  induction l with
  | nil => intro _ h hh; simp at hh
  | cons a t ih =>
    intro hchain h hh s hs
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hs
      subst hs
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    | cons b t' =>
      obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp hchain
      rw [List.getLast?_cons_cons] at hs
      have IH := ih htail b rfl s hs
      have hkey : a.D * f a = b.D := hstep a b hab
      rw [List.map_cons, List.prod_cons]
      calc a.D * (f a * ((b :: t').map f).prod)
          = (a.D * f a) * ((b :: t').map f).prod := by ring
        _ = b.D * ((b :: t').map f).prod := by rw [hkey]
        _ = f s * s.D := IH

/-- E·F = the CHILD key degree D′ = e·g·D: list induction along `Chain' StageLaws`
(D_{r+1} = e_r·g_r·D_r with D₀ = 1 telescopes to ∏e·∏g = D′). -/
theorem accEF_keyDeg {n : ℕ} (l : List MovesSp.Species) (sels : List (ℕ × ℕ))
    (hzip : l.length = sels.length ∧
      ∀ (r : ℕ) (s : MovesSp.Species) (gm : ℕ × ℕ),
        l[r]? = some s → sels[r]? = some gm → s.sel = some gm)
    (hne : l ≠ []) (hroot : ∀ s, l.head? = some s → MovesSp.RootStage n s)
    (hchain : l.Chain' MovesSp.StageLaws)
    (s : MovesSp.Species) (hlast : l.getLast? = some s)
    (g μ : ℕ) (hsel : sels.getLast? = some (g, μ) ∧ s.sel = some (g, μ)) :
    (l.map fun t => t.e).prod * (sels.map Prod.fst).prod = s.e * g * s.D := by
  obtain ⟨hlen, hpair⟩ := hzip
  obtain ⟨hgμ, hssel⟩ := hsel
  -- The per-step multiplier: e·g, reading g from the (present) selection.
  -- (`sels[r]` is exactly `l[r].sel`, so `(t.sel.getD (0,0)).1` recovers each `g`.)
  -- Head has D = 1 by RootStage.
  have hhead : l.head? = some (l.head hne) := List.head?_eq_head hne
  have hrootD : (l.head hne).D = 1 := (hroot _ hhead).2.1
  -- Adjacent-pair compatibility for the multiplier.
  have hstep : ∀ a b : MovesSp.Species, MovesSp.StageLaws a b →
      a.D * (a.e * (a.sel.getD (0, 0)).1) = b.D := by
    intro a b hab
    rcases hae : a.sel with _ | ⟨ga, μa⟩
    · simp only [MovesSp.StageLaws, hae] at hab
    · simp only [MovesSp.StageLaws, hae] at hab
      obtain ⟨hbD, -⟩ := hab
      show a.D * (a.e * ga) = b.D
      rw [hbD]; ring
  -- Telescope, then collapse the root D = 1.
  have htel := accEF_telescope (f := fun t : MovesSp.Species => t.e * (t.sel.getD (0, 0)).1)
    hstep l hchain (l.head hne) hhead s hlast
  rw [hrootD, one_mul] at htel
  -- `sels`'s first components equal `l`'s recovered `g`'s, pointwise.
  have hsg : sels.map Prod.fst = l.map (fun t => (t.sel.getD (0, 0)).1) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, hlen]
    · intro k h₁ _
      rw [List.length_map] at h₁
      have hkl : k < l.length := hlen ▸ h₁
      have e1 : l[k]? = some l[k] := List.getElem?_eq_getElem hkl
      have e2 : sels[k]? = some sels[k] := List.getElem?_eq_getElem h₁
      have hpk : (l[k]).sel = some (sels[k]) := hpair k _ _ e1 e2
      simp only [List.getElem_map, hpk, Option.getD_some]
  calc (l.map fun t => t.e).prod * (sels.map Prod.fst).prod
      = (l.map fun t => t.e).prod * (l.map fun t => (t.sel.getD (0, 0)).1).prod := by rw [hsg]
    _ = (l.map fun t => t.e * (t.sel.getD (0, 0)).1).prod := (List.prod_map_mul).symm
    _ = s.e * (s.sel.getD (0, 0)).1 * s.D := htel
    _ = s.e * g * s.D := by simp [hssel]

end LeanUrat.MovesT
