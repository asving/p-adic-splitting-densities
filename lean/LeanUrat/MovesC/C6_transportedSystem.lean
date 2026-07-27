/-
Unit C6.transportedSystem — moves_ref: §C.2 the state cylinder IS the joint transported fresh
system (statement unchanged; ROUND 3: proved through recursion + inh_implied)

Induction on `k`. Base: `Sigma 0` pins nothing (`J.init`), and `∀ i < 0` is vacuous — both
sides trivially hold. Step: `J.recursion` unfolds `Sigma (k+1)` into
`Sigma k (Θ_k x) ∧ stratum k (Θ_k x)`; on the `Σ_k`-solution branch `J.inh_implied` converts
`stratum` to `(fresh k).sat`; the IH rebinds the earlier reads through `seg` (the segment
composite equations `seg i (k+1) x = seg i k (Θ_k x)` for `i ≤ k`, and `seg i i = id`).
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The empty segment composite is the identity: `seg i i = id`. -/
private lemma seg_self {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) :
    J.seg i i = id := by
  cases i with
  | zero => rfl
  | succ j =>
    have : ¬ (j + 1 ≤ j) := by omega
    simp [JetSetup.seg, this]

theorem C6_transportedSystem {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (k : ℕ) (hk : k ≤ H.nodes.length) (x : Fin m → ZMod p) : (J.Sigma k).IsSolution x ↔ ∀ (i : ℕ) (hi : i < k), (J.fresh i).sat (J.seg i k x) := by
  have main : ∀ k, k ≤ H.nodes.length → ∀ (x : Fin m → ZMod p),
      ((J.Sigma k).IsSolution x ↔ ∀ (i : ℕ) (hi : i < k), (J.fresh i).sat (J.seg i k x)) := by
    intro k
    induction k with
    | zero =>
      intro _ x
      constructor
      · intro _ i hi
        exact absurd hi (Nat.not_lt_zero i)
      · intro _ c hc
        simp [J.init c] at hc
    | succ k ih =>
      intro hk x
      have hklen : k < H.nodes.length := hk
      have hkle : k ≤ H.nodes.length := le_of_lt hklen
      have segstep : ∀ i, i ≤ k → J.seg i (k + 1) x = J.seg i k (J.Theta k x) := by
        intro i hi
        simp [JetSetup.seg, hi]
      have segk : J.seg k (k + 1) x = J.Theta k x := by
        rw [segstep k (le_refl k), seg_self J k, Function.id_def]
      rw [J.recursion k hklen x]
      constructor
      · rintro ⟨hsol, hstr⟩
        have hfreshk : (J.fresh k).sat (J.Theta k x) :=
          (J.inh_implied k hklen (J.Theta k x) hsol).mp hstr
        have hIH := (ih hkle (J.Theta k x)).mp hsol
        intro i hi
        rcases Nat.lt_or_ge i k with hlt | hge
        · rw [segstep i (le_of_lt hlt)]
          exact hIH i hlt
        · have heq : i = k := by omega
          subst heq
          rw [segk]
          exact hfreshk
      · intro hall
        have hfreshk : (J.fresh k).sat (J.Theta k x) := by
          have h := hall k (by omega)
          rwa [segk] at h
        have hIHrhs : ∀ i (hi : i < k), (J.fresh i).sat (J.seg i k (J.Theta k x)) := by
          intro i hi
          have h := hall i (by omega)
          rwa [segstep i (le_of_lt hi)] at h
        have hsol : (J.Sigma k).IsSolution (J.Theta k x) := (ih hkle (J.Theta k x)).mpr hIHrhs
        have hstr : J.stratum k (J.Theta k x) :=
          (J.inh_implied k hklen (J.Theta k x) hsol).mpr hfreshk
        exact ⟨hsol, hstr⟩
  exact main k hk x

end LeanUrat.MovesC
