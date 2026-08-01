/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/HDischarge/H2/ProdBoxUniform — the (b-RED) product-box engine
  [HDISCHARGE_H2 unit U4; wave 1, MED, corpus-free]

Statement VERBATIM from `lean/blueprints/HDISCHARGE_H2.md` §6 (H2-U4;
alphabet-bounded `B` form per review pass 1, finding 9).

Proof route (per blueprint): the filtered pi-set is the pi of per-slot
filtered fibers (`filter_pi_read_eq`), then `Finset.card_pi` +
`Finset.prod_congr` with the per-slot uniformity hypothesis `huni`.

Falsifier gate (`#eval`, blueprint-mandated): ι = Fin 2, Ω = Fin 3, B = 2 —
uniform read gives equal joint counts (1, 1); non-uniform read (hypothesis
violated) gives unequal joint counts (4, 1), so the counting is non-vacuous.
-/

namespace LeanUrat.Scaffold.HDischarge.H2

/-- Helper: filtering a product box by a per-slot read condition is the
    product of the per-slot filtered fibers. -/
lemma filter_pi_read_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ k, Fintype (Ω k)] [∀ k, DecidableEq (Ω k)]
    (A : ∀ k, Finset (Ω k)) (read : ∀ k, Ω k → ℕ) (z : ι → ℕ) :
    ((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = z k)
      = Finset.univ.pi (fun k => (A k).filter fun ω => read k ω = z k) := by
  ext ω
  simp only [Finset.mem_filter, Finset.mem_pi, forall_and]

/-- (b-RED) engine: per-slot uniform independent counts multiply — the joint
    count over a product box with per-slot fiber-uniform reads is digit-vector
    independent on the alphabet.  Abstract Finset/counting form. -/
theorem prodBox_jointUniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ k, Fintype (Ω k)] [∀ k, DecidableEq (Ω k)]
    (A : ∀ k, Finset (Ω k)) (read : ∀ k, Ω k → ℕ) (B : ℕ)
    (huni : ∀ k, ∀ z < B, ∀ z' < B,
      ((A k).filter fun ω => read k ω = z).card
        = ((A k).filter fun ω => read k ω = z').card)
    (z z' : ι → ℕ) (hz : ∀ k, z k < B) (hz' : ∀ k, z' k < B) :
    ((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = z k).card
      = ((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = z' k).card := by
  rw [filter_pi_read_eq, filter_pi_read_eq, Finset.card_pi, Finset.card_pi]
  exact Finset.prod_congr rfl fun k _ => huni k (z k) (hz k) (z' k) (hz' k)

/-! ## Falsifier gate (blueprint H2-U4): ι = Fin 2, Ω = Fin 3, B = 2

Uniform read (`read k ω = ω.val` on the box `A k = {0, 1}`): every fiber
`z < 2` has one point per slot, so all joint counts agree (1, 1). -/

/-- info: (1, 1) -/
#guard_msgs in
#eval
  let A : ∀ _ : Fin 2, Finset (Fin 3) := fun _ => {0, 1}
  let read : ∀ _ : Fin 2, Fin 3 → ℕ := fun _ ω => ω.val
  (((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = (fun _ => 0) k).card,
   ((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = (fun k : Fin 2 => k.val) k).card)

/-! Non-uniform read (`read k ω = ω.val % 2` on the full box `Fin 3`): the
`0`-fiber has 2 points per slot and the `1`-fiber has 1, violating `huni` —
and the joint counts indeed split as (4, 1), so the conclusion genuinely
depends on the hypothesis. -/

/-- info: (4, 1) -/
#guard_msgs in
#eval
  let A : ∀ _ : Fin 2, Finset (Fin 3) := fun _ => Finset.univ
  let read : ∀ _ : Fin 2, Fin 3 → ℕ := fun _ ω => ω.val % 2
  (((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = (fun _ => 0) k).card,
   ((Finset.univ.pi A).filter fun ω => ∀ k h, read k (ω k h) = (fun _ => 1) k).card)

end LeanUrat.Scaffold.HDischarge.H2
