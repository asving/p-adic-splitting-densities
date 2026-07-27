/-
Unit U-16a3 `consumedDeltas_def` (medium) — the closure spec lemma for the
multiplicative δ-closure (R17, DELTA-ABS; the def `consumedDeltas` lives in
Defs.lean, filled at E-phase).  moves_ref: "δ ranging over 1 AND every base-change
index a β_{e_j,τ_j}(q^{δ_j}) leg of b_e^split or RS.1-SH consumes ([2r] BASE-INDEX
CONVENTION + (e2), δ ABSOLUTE)".  For any nesting chain of split/shape legs
(length ≤ n by U-2), the chain's PRODUCT — the semantic index rel. the base prime —
lies in `consumedDeltas`; hence `RegP`/`legs_reg` carry E0 over every EFFECTIVE
pool p^(δ₁·…·δ_k), and `pools_closed` keeps each in `Pools`.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowSubstMul

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- The one-step multiplicative-closure operator `s ↦ s ∪ (D * s)` is INFLATIONARY
under iteration: any starting set is contained in every iterate. -/
private lemma infl_iterate {α : Type*} [Mul α] [DecidableEq α] (D : Finset α)
    (s : Finset α) (k : ℕ) :
    s ⊆ (fun t : Finset α => t ∪ Finset.image₂ (· * ·) D t)^[k] s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans Finset.subset_union_left

/-- The KEY closure fact: a list `l` of factors, each drawn from `D`, has its product
land in the `l.length`-th iterate of the closure operator started at `{1}`.  Proved by
induction on `l`: the empty product `1` seeds `{1}`, and prepending a factor `a ∈ D`
multiplies into the previous iterate via `D * (·)`, one more application of the
operator. -/
private lemma prod_mem_iterate {α : Type*} [CommMonoid α] [DecidableEq α]
    (D : Finset α) :
    ∀ (l : List α), (∀ δ ∈ l, δ ∈ D) →
      l.prod ∈ (fun t : Finset α => t ∪ Finset.image₂ (· * ·) D t)^[l.length] {1} := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l' ih =>
    intro hfac
    have ha : a ∈ D := hfac a (by simp)
    have hl' : ∀ δ ∈ l', δ ∈ D := fun δ hδ => hfac δ (List.mem_cons_of_mem _ hδ)
    have hprev := ih hl'
    rw [List.prod_cons, List.length_cons, Function.iterate_succ_apply']
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image₂_of_mem ha hprev))

theorem nested_delta_mem (T : TableShape n) (F : ShapeFam T) (l : List ℕ+)
    (hlen : l.length ≤ n) (hfac : ∀ δ ∈ l, δ ∈ deltaFactors T F) :
    l.prod ∈ consumedDeltas T F := by
  unfold consumedDeltas
  set D := deltaFactors T F with hD
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlen
  rw [hd, Nat.add_comm, Function.iterate_add_apply]
  exact infl_iterate D _ d (prod_mem_iterate D l hfac)

end LeanUrat.MovesS
