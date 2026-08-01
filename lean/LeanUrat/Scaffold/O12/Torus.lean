/-
BP_II §1.8 — the torus telescope (`Scaffold/O12/Torus.lean`), unit II-T2.
Units in this file: II-T2 (`chain_telescope`) — the abstract fibered telescope
over shared-vertex chains, anchor V_{k+1} := 1 at index k (L6d Step 2).
-/
import Mathlib

/-!
# The fibered telescope, abstract form [unit II-T2]

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.8 (unit II-T2; row table §2, MED).
* Math source of record: L6d Step 2.
* Deps: none. Later torus units (II-T1, II-T3, II-T4) extend this file.

Proof: induction on k, left to right — sum the first vertex via the
c-independent row sums `hrow`, pull out `P 0`, recurse on the tail chain.

Transcription note: the blueprint binder `λ` in `hrow` is Lean 4's reserved
lambda token; it is transcribed as the escaped identifier `«λ»` (the same
binder name, alpha-identical statement). The classical instances (`Fintype Fˣ`
and decidability of the anchor condition over an abstract finite field) enter
via `open Classical in`, as elaboration context only — the displayed statement
is otherwise byte-verbatim from BP_II §1.8.
-/

namespace LeanUrat.Scaffold

open Finset

open Classical in
/-- Helper for unit II-T2 (not a blueprint statement): the telescope with the
`Fin` bookkeeping in `castSucc`/`succ`/`last` normal form — definitionally the
blueprint display. Induction on `k`: split off the first vertex `v₀` by
`Fin.consEquiv`, sum it via the c-independent row sum `hrow 0`, pull out `P 0`,
recurse on the tail chain `j ↦ n j.succ`. -/
private theorem chain_telescope_aux {F : Type*} [Field F] [Fintype F] :
    ∀ (k : ℕ) (n : Fin k → Fˣ → Fˣ → ℕ) (P : Fin k → ℕ),
      (∀ j c, ∑ l : Fˣ, n j l c = P j) →
      (∑ V : Fin (k + 1) → Fˣ,
        if V (Fin.last k) = 1 then
          ∏ j : Fin k, n j (V j.castSucc) (V j.succ)
        else 0) =
      ∏ j, P j := by
  intro k
  induction k with
  | zero =>
    intro n P hrow
    rw [← ((Equiv.funUnique (Fin 1) Fˣ).symm).sum_comp]
    simp
  | succ k ih =>
    intro n P hrow
    -- Split off the first vertex: V = Fin.cons v₀ W.
    have hsplit :
        (∑ V : Fin (k + 1 + 1) → Fˣ,
          if V (Fin.last (k + 1)) = 1 then
            ∏ j : Fin (k + 1), n j (V j.castSucc) (V j.succ)
          else 0)
        = ∑ W : Fin (k + 1) → Fˣ, ∑ v₀ : Fˣ,
            if (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = 1 then
              ∏ j : Fin (k + 1),
                n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ)
            else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (k + 1 + 1) => Fˣ).sum_comp,
        Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    -- The inner sum over v₀: the anchor condition and the tail product do not
    -- see v₀, so `hrow 0` collapses it to `P 0`.
    have key : ∀ W : Fin (k + 1) → Fˣ,
        (∑ v₀ : Fˣ,
          if (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = 1 then
            ∏ j : Fin (k + 1),
              n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ)
          else 0)
        = P 0 *
          (if W (Fin.last k) = 1 then
            ∏ j : Fin k, n j.succ (W j.castSucc) (W j.succ)
          else 0) := by
      intro W
      have hanchor : ∀ v₀ : Fˣ,
          (Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) (Fin.last (k + 1)) = W (Fin.last k) := by
        intro v₀
        rw [← Fin.succ_last, Fin.cons_succ]
      have hprod : ∀ v₀ : Fˣ,
          (∏ j : Fin (k + 1),
            n j ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.castSucc)
                  ((Fin.cons v₀ W : Fin (k + 1 + 1) → Fˣ) j.succ))
          = n 0 v₀ (W 0) * ∏ j : Fin k, n j.succ (W j.castSucc) (W j.succ) := by
        intro v₀
        rw [Fin.prod_univ_succ]
        rfl
      by_cases hW : W (Fin.last k) = 1
      · simp only [hanchor, hprod, hW, if_true, ← Finset.sum_mul, hrow 0]
      · simp only [hanchor, hW, if_false, Finset.sum_const_zero, mul_zero]
    -- Recurse on the tail chain.
    rw [hsplit, Finset.sum_congr rfl fun W _ => key W, ← Finset.mul_sum,
      ih (fun j => n j.succ) (fun j => P j.succ) (fun j c => hrow j.succ c),
      ← Fin.prod_univ_succ]

open Classical in
/-- **The fibered telescope** (L6d Step 2), abstract form: counting functions
n_j : Fˣ × Fˣ → ℕ whose torus row-sums Σ_λ n_j(λ, c) = P_j are c-independent
telescope over shared-vertex chains: Σ_{V ∈ (Fˣ)^k} ∏_j n_j(V_j, V_{j+1}) = ∏_j P_j
(V_{k+1} := 1, the anchor). Induction on k, left to right. -/
theorem chain_telescope {F : Type*} [Field F] [Fintype F] {k : ℕ}
    (n : Fin k → Fˣ → Fˣ → ℕ) (P : Fin k → ℕ)
    (hrow : ∀ j c, ∑ «λ» : Fˣ, n j «λ» c = P j) :
    (∑ V : Fin (k + 1) → Fˣ,
      if V ⟨k, Nat.lt_succ_self k⟩ = 1 then
        ∏ j : Fin k, n j
          (V ⟨j, Nat.lt.step j.isLt⟩)
          (V ⟨j + 1, Nat.succ_lt_succ j.isLt⟩)
      else 0) =
    ∏ j, P j :=
  chain_telescope_aux k n P hrow

end LeanUrat.Scaffold
