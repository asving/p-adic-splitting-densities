/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeB4_legRosterFintype

/-!
# IB-B5 — `card_legRoster`: the leg-count pin's cardinality law (bridge BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (†4d,
leg case) / §4 group B (IB-B5):

    Fintype.card (LegRoster T e) = Σ τ, Σ o ∈ splitOuts T e τ, Outcome.c

— the count of abstract leg labels equals the roster's own continuing-member
population, which is EXACTLY `RegPin.leg_pin`'s RHS (DefsLedger.lean:529) at
the tautological roster, so IB-B8's `legIdx_card` field IS this lemma.

TRANSCRIPTION RESOLUTION (recorded, same as IB-B4): stated at a bare
`T : MovesS.TableShape n`; the `Fintype.card` is taken at IB-B4's named
instance `legRosterFintype` (the one IB-B8 wires into `instL`), so the record
field consumes this statement without `Subsingleton (Fintype _)` transport.

DEPS: IB-B4.  CONSUMERS: IB-B8 (`legIdx_card`), IB-B10 (`leg_pin`).

PROOF SKETCH (H, ~40): `Fintype.card_sigma` twice (states, then split
outcomes through the Finset-coe carrier); per (τ, o) the continuing-positions
count `Fintype.card {i : Fin mem.length // (mem.get i).continuing}` equals the
filter length `(mem.filter (fun μ => μ.status.isRight)).length = Outcome.c`:
`Fintype.card_subtype` + the countP/filter-length dictionary
(`List.countP_eq_length_filter`-style, with the `Member.continuing μ ↔
μ.status.isRight = true` Prop/Bool coercion minded) — expect Mathlib
archaeology on the `List.count`/`countP`/`Fin`-subtype-card lemma names.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open scoped Classical in
/-- IB-B5 helper (the countP/filter-length dictionary, Fin-indexed face): the
    count of positions of `l` whose entry passes the Bool test `p` equals the
    filtered length.  Mirrors Mathlib's
    `Fin.card_filter_univ_eq_vector_get_eq_count` induction
    (`Fin.card_filter_univ_succ'` at the cons step). -/
private theorem card_filter_get_eq_length_filter {α : Type*} (p : α → Bool) :
    ∀ l : List α,
      (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card
        = (l.filter p).length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    show (Finset.univ.filter fun i : Fin (t.length + 1) =>
        p ((a :: t).get i) = true).card = ((a :: t).filter p).length
    rw [Fin.card_filter_univ_succ']
    simp only [List.get_eq_getElem] at ih
    simp only [List.get_eq_getElem, Fin.val_succ, Fin.val_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, List.filter_cons, ih]
    by_cases h : p a
    · simp only [h, if_true, List.length_cons]
      omega
    · simp [h]

/-- IB-B5: the leg-roster cardinality law (†4d, leg case) — the abstract label
    count at IB-B4's Fintype equals the per-block continuing-member population
    `Σ τ, Σ o ∈ splitOuts, Outcome.c`. -/
theorem card_legRoster {n : ℕ} (T : MovesS.TableShape n) (e : ℕ) :
    @Fintype.card (LegRoster T e) (legRosterFintype T e)
      = ∑ τ : T.State e, ∑ o ∈ MovesS.splitOuts T e τ, (T.odata e τ o).c := by
  classical
  have h : @Fintype.card (LegRoster T e) (legRosterFintype T e)
      = Fintype.card (Σ (τ : T.State e)
          (o : {o : T.Out e τ // o ∈ MovesS.splitOuts T e τ}),
          {i : Fin (T.odata e τ o.1).mem.length //
            ((T.odata e τ o.1).mem.get i).continuing}) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.card_sigma]
  rw [Finset.sum_coe_sort (MovesS.splitOuts T e τ)
    (fun o => Fintype.card {i : Fin (T.odata e τ o).mem.length //
      ((T.odata e τ o).mem.get i).continuing})]
  refine Finset.sum_congr rfl fun o _ => ?_
  calc Fintype.card {i : Fin (T.odata e τ o).mem.length //
        ((T.odata e τ o).mem.get i).continuing}
      = (Finset.univ.filter fun i : Fin (T.odata e τ o).mem.length =>
          ((T.odata e τ o).mem.get i).continuing).card :=
        Fintype.card_subtype _
    _ = (Finset.univ.filter fun i : Fin (T.odata e τ o).mem.length =>
          ((T.odata e τ o).mem.get i).status.isRight = true).card :=
        congrArg Finset.card (Finset.filter_congr fun i _ => Iff.rfl)
    _ = ((T.odata e τ o).mem.filter fun μ => μ.status.isRight).length :=
        card_filter_get_eq_length_filter (fun μ => μ.status.isRight)
          (T.odata e τ o).mem
    _ = (T.odata e τ o).c := rfl

end LeanUrat.MovesU
